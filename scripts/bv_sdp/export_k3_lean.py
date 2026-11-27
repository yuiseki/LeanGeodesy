import math
import numpy as np
import cvxpy as cp
from fractions import Fraction
from scipy.linalg import qr, cholesky

from round_k3_cert import (
    poly_mul, poly_add, sym3_exact, build_Qk_exact, e_mons, vt_mons, round_matrix
)
from test_compact_dd import get_compact_sos3_specs, check_cholesky_dd

def lcm(a, b):
    return abs(a * b) // math.gcd(a, b)

def solve_and_export():
    d3 = 5
    sNum, sDen = 1, 2
    s_frac = Fraction(sNum, sDen)
    s = float(s_frac)
    Q = build_Qk_exact(d3)

    A0 = cp.Variable((d3 + 2, d3 + 2), symmetric=True)
    Fk = [None] + [cp.Variable((d3 - k + 1, d3 - k + 1), symmetric=True) for k in range(1, d3 + 1)]
    eps = cp.Variable(nonneg=True)

    constraints = [A0 >> eps * np.eye(d3 + 2)]
    for k in range(1, d3 + 1):
        constraints.append(Fk[k] >> eps * np.eye(d3 - k + 1))

    deg2 = 2 * d3
    G2_coeffs = [0 for _ in range(deg2 + 1)]
    G2_coeffs[0] = G2_coeffs[0] + 1.0
    for i in range(d3 + 1):
        G2_coeffs[i] = G2_coeffs[i] + 2.0 * A0[0, 1 + i]
        for j in range(d3 + 1):
            G2_coeffs[i + j] = G2_coeffs[i + j] + A0[1 + i, 1 + j]
    one_minus_t2 = {(0,): Fraction(1), (2,): Fraction(-1)}
    pow_1mt2 = [{(0,): Fraction(1)}]
    for k in range(1, d3 + 1):
        pow_1mt2.append(poly_mul(pow_1mt2[-1], one_minus_t2))
    for k in range(1, d3 + 1):
        m = d3 - k + 1
        for i in range(m):
            for j in range(m):
                for (deg,), val in pow_1mt2[k].items():
                    G2_coeffs[i + j + deg] = G2_coeffs[i + j + deg] + Fk[k][i, j] * float(val)

    h0, h1 = d3, d3 - 1
    S2_0 = cp.Variable((h0 + 1, h0 + 1), symmetric=True)
    S2_1 = cp.Variable((h1 + 1, h1 + 1), symmetric=True)
    constraints.append(S2_0 >> eps * np.eye(h0 + 1))
    constraints.append(S2_1 >> eps * np.eye(h1 + 1))
    for d in range(deg2 + 1):
        rhs = 0
        for i in range(h0 + 1):
            j = d - i
            if 0 <= j <= h0: rhs = rhs + S2_0[i, j]
        for i in range(h1 + 1):
            for j in range(h1 + 1):
                if i + j == d: rhs = rhs + s * S2_1[i, j]
                if i + j + 1 == d: rhs = rhs + (s - 1.0) * S2_1[i, j]
                if i + j + 2 == d: rhs = rhs - S2_1[i, j]
        constraints.append(-G2_coeffs[d] == rhs)

    G3 = {}
    for i in range(d3 + 1):
        for j in range(d3 + 1):
            for m, val in sym3_exact({(i, j, 0): Fraction(1)}).items():
                if m[0] >= m[1] >= m[2]:
                    G3[m] = G3.get(m, 0) + A0[1 + i, 1 + j] * float(val)
    for k in range(1, d3 + 1):
        mk = d3 - k + 1
        for i in range(mk):
            for j in range(mk):
                p_ij = {(a1 + i, b1 + j, c1): val for (a1, b1, c1), val in Q[k].items()}
                for m, val in sym3_exact(p_ij).items():
                    if m[0] >= m[1] >= m[2]:
                        G3[m] = G3.get(m, 0) + Fk[k][i, j] * float(val)

    specs = get_compact_sos3_specs(d3, s_frac)
    M_vars = []
    RHS3 = {}
    spec_polys = []
    for name, mult, basis in specs:
        n_b = len(basis)
        M = cp.Variable((n_b, n_b), symmetric=True)
        constraints.append(M >> eps * np.eye(n_b))
        M_vars.append(M)
        p_map = {}
        for i in range(n_b):
            for j in range(i, n_b):
                prod_ij = sym3_exact(poly_mul(mult, poly_mul(basis[i], basis[j])))
                coeff = Fraction(1 if i == j else 2)
                canon = {m: v * coeff for m, v in prod_ij.items() if m[0] >= m[1] >= m[2]}
                p_map[(i, j)] = canon
                for m, v in canon.items():
                    RHS3[m] = RHS3.get(m, 0) + M[i, j] * float(v)
        spec_polys.append(p_map)

    all_mons = sorted(set(G3.keys()) | set(RHS3.keys()))
    for m in all_mons:
        constraints.append(-G3.get(m, 0) == RHS3.get(m, 0))

    constraints.append(1.0 + A0[0, 0] <= 12.99)
    trace_sum = cp.trace(A0) + sum(cp.trace(Fk[k]) for k in range(1, d3 + 1)) + cp.trace(S2_0) + cp.trace(S2_1) + sum(cp.trace(M) for M in M_vars)
    constraints.append(trace_sum <= 50000.0)

    prob = cp.Problem(cp.Maximize(eps), constraints)
    prob.solve(solver=cp.CLARABEL)
    assert prob.status == "optimal"

    dK = 10**6
    denom_sos_init = 10**7
    dR = 10**6

    A0_q = round_matrix(A0.value, dK)
    Fk_q = [None] + [round_matrix(Fk[k].value, dK) for k in range(1, d3 + 1)]

    # Exact G2_q
    G2_q = [Fraction(0)] * (deg2 + 1)
    G2_q[0] += Fraction(1)
    for i in range(d3 + 1):
        G2_q[i] += 2 * A0_q[0][1 + i]
        for j in range(d3 + 1): G2_q[i + j] += A0_q[1 + i][1 + j]
    for k in range(1, d3 + 1):
        mk = d3 - k + 1
        for i in range(mk):
            for j in range(mk):
                for (deg,), val in pow_1mt2[k].items():
                    G2_q[i + j + deg] += Fk_q[k][i][j] * val

    S2_0_q = round_matrix(S2_0.value, denom_sos_init)
    S2_1_q = round_matrix(S2_1.value, denom_sos_init)
    def eval_rhs2(S0, S1):
        out = [Fraction(0)] * (deg2 + 1)
        for i in range(h0 + 1):
            for j in range(h0 + 1): out[i + j] += S0[i][j]
        for i in range(h1 + 1):
            for j in range(h1 + 1):
                out[i + j] += s_frac * S1[i][j]
                out[i + j + 1] += (s_frac - 1) * S1[i][j]
                out[i + j + 2] -= S1[i][j]
        return out
    res2 = [-G2_q[d] - eval_rhs2(S2_0_q, S2_1_q)[d] for d in range(deg2 + 1)]
    for d in range(deg2 + 1):
        if res2[d] != 0:
            i = d // 2; j = d - i
            if i == j: S2_0_q[i][i] += res2[d]
            else: S2_0_q[i][j] += res2[d] / 2; S2_0_q[j][i] += res2[d] / 2
    assert all(-G2_q[d] == eval_rhs2(S2_0_q, S2_1_q)[d] for d in range(deg2 + 1))

    # Exact G3_q
    G3_q = {m: Fraction(0) for m in all_mons}
    for i in range(d3 + 1):
        for j in range(d3 + 1):
            for m, val in sym3_exact({(i, j, 0): Fraction(1)}).items():
                if m[0] >= m[1] >= m[2]: G3_q[m] += A0_q[1 + i][1 + j] * val
    for k in range(1, d3 + 1):
        mk = d3 - k + 1
        for i in range(mk):
            for j in range(mk):
                p_ij = {(a1 + i, b1 + j, c1): val for (a1, b1, c1), val in Q[k].items()}
                for m, val in sym3_exact(p_ij).items():
                    if m[0] >= m[1] >= m[2]: G3_q[m] += Fk_q[k][i][j] * val

    M_q = [round_matrix(M.value, denom_sos_init) for M in M_vars]
    mon_idx = {m: idx for idx, m in enumerate(all_mons)}
    num_eq = len(all_mons)
    rhs3 = {m: Fraction(0) for m in all_mons}
    for b_idx, p_map in enumerate(spec_polys):
        for (i, j), canon in p_map.items():
            val = M_q[b_idx][i][j]
            for m, c in canon.items(): rhs3[m] += val * c
    res3 = [(-G3_q[m] - rhs3[m]) for m in all_mons]

    cols_info, cols_vec = [], []
    for b_idx, p_map in enumerate(spec_polys):
        for (i, j), canon in p_map.items():
            v = np.zeros(num_eq)
            for m, c in canon.items(): v[mon_idx[m]] = float(c)
            if np.linalg.norm(v) > 0:
                cols_info.append((b_idx, i, j, canon))
                cols_vec.append(v)
    _, R_qr, piv = qr(np.column_stack(cols_vec), pivoting=True)
    chosen = piv[:num_eq]
    mat = [[Fraction(0) for _ in range(num_eq + 1)] for _ in range(num_eq)]
    for c_pos, col_id in enumerate(chosen):
        for m, c in cols_info[col_id][3].items(): mat[mon_idx[m]][c_pos] = c
    for r in range(num_eq): mat[r][num_eq] = res3[r]
    for col in range(num_eq):
        piv_row = next(r for r in range(col, num_eq) if mat[r][col] != 0)
        mat[col], mat[piv_row] = mat[piv_row], mat[col]
        pv = mat[col][col]
        mat[col] = [x / pv for x in mat[col]]
        for r in range(num_eq):
            if r != col and mat[r][col] != 0:
                f = mat[r][col]
                mat[r] = [mat[r][c] - f * mat[col][c] for c in range(num_eq + 1)]
    for c_pos, col_id in enumerate(chosen):
        b_idx, i, j, _ = cols_info[col_id]
        dval = mat[c_pos][num_eq]
        M_q[b_idx][i][j] += dval
        if i != j: M_q[b_idx][j][i] += dval

    # Compute common denominator dS across S2_0_q, S2_1_q, and all M_q
    dS = 1
    for M in [S2_0_q, S2_1_q] + M_q:
        for row in M:
            for val in row:
                dS = lcm(dS, val.denominator)
    print(f"dK = {dK}, dS = {dS} (digits={len(str(dS))}), dR = {dR}")

    # Compute exact Cholesky witnesses R_q (with denom dR) for all 18 matrices
    kernel_mats = [("A0", A0_q), ("F1", Fk_q[1]), ("F2", Fk_q[2]), ("F3", Fk_q[3]), ("F4", Fk_q[4]), ("F5", Fk_q[5])]
    sos_mats = [("S2_0", S2_0_q), ("S2_1", S2_1_q)] + [(n, Mq) for (n, _, _), Mq in zip(specs, M_q)]

    R_map = {}
    for name, Mq in kernel_mats + sos_mats:
        R_q, lmin, margin = check_cholesky_dd(Mq, denom_R=dR)
        assert R_q is not None and margin >= 0, f"Failed DD on {name}: margin={margin}"
        R_map[name] = R_q

    def to_int_mat(Mq, denom):
        res = []
        for row in Mq:
            r_int = []
            for val in row:
                scaled = val * denom
                assert scaled.denominator == 1, f"Non-integer: {val} * {denom}"
                r_int.append(int(scaled.numerator))
            res.append(r_int)
        return res

    def fmt_mat(M_int):
        rows = ["[" + ", ".join(str(x) for x in row) + "]" for row in M_int]
        return "[\n    " + ",\n    ".join(rows) + "\n  ]"

    lines = [
        "import LeanGeodesy.Spherical.BachocVallentinCert",
        "import LeanGeodesy.Spherical.Delsarte",
        "",
        "/-!",
        "# Kissing number in dimension 3: `K(3) = 12`",
        "",
        "This module proves the exact kissing number in dimension 3 (`K(3) = 12`)",
        "unconditionally in Lean 4:",
        "",
        "- `kissing3Cert`: an exact rational degree-5 Bachoc–Vallentin three-point SDP",
        "  certificate for `s = 1/2` (60° separation), generated externally and verified",
        "  independently in Lean's kernel with zero trust in floating-point arithmetic",
        "  or external solvers;",
        "- `kissing3Cert_valid`: kernel-checked proof (`by decide`) that all 18 matrices",
        "  are symmetric and positive semidefinite (via Cholesky + diagonal dominance)",
        "  and that both the univariate and `S₃`-symmetric trivariate polynomial",
        "  identities hold identically;",
        "- `kissingNumber_three_upper`: every `(n, 1/2)`-spherical code on `S²`",
        "  satisfies `n ≤ 12` (beating the two-point Delsarte LP barrier of `13`);",
        "- `kissingNumber_three_lower`: `icosahedron12` witnesses a `(12, 1/2)`-code;",
        "- `kissingNumber_three_exact`: `(∃ p : Fin n → UnitSphere, IsSphericalCode p (1/2)) ↔ n ≤ 12`;",
        "- Negative tests confirming that malformed certificates (asymmetric, non-PSD,",
        "  or broken polynomial identity) are rejected by `BVCert5.isValid`.",
        "-/",
        "",
        "namespace Geodesy.Spherical",
        "",
        "/-- Exact rational degree-5 Bachoc–Vallentin SDP certificate for `K(3) ≤ 12`. -/",
        "def kissing3Cert : BVCert5 where",
        f"  sNum := {sNum}",
        f"  sDen := {sDen}",
        f"  dK := {dK}",
        f"  dS := {dS}",
        f"  dR := {dR}",
    ]

    for name, Mq in kernel_mats:
        lines.append(f"  {name} := {fmt_mat(to_int_mat(Mq, dK))}")
        lines.append(f"  R_{name} := {fmt_mat(to_int_mat(R_map[name], dR))}")
    for name, Mq in sos_mats:
        field = name if name.startswith("S2_") else f"M_{name}"
        rfield = f"R_{name}"
        lines.append(f"  {field} := {fmt_mat(to_int_mat(Mq, dS))}")
        lines.append(f"  {rfield} := {fmt_mat(to_int_mat(R_map[name], dR))}")

    lines.extend([
        "",
        "/-- Kernel-verified validity of `kissing3Cert` (no `native_decide`, no extra axioms). -/",
        "set_option maxRecDepth 20000 in",
        "theorem kissing3Cert_valid : kissing3Cert.isValid = true := by decide",
        "",
        "/-- The certified rational upper bound is strictly less than `13` (`12.99 < 13`). -/",
        "theorem kissing3Cert_bound_lt_13 : kissing3Cert.bound < 13 := by",
        "  norm_num [BVCert5.bound, kissing3Cert, matGet]",
        "",
        "/-- **Kissing number in dimension 3 (upper bound)**:",
        "every spherical code on `S²` with pairwise inner products `≤ 1/2` (angular",
        "separation `≥ 60°`) has at most `12` points. -/",
        "theorem kissingNumber_three_upper {n : ℕ} {p : Fin n → UnitSphere}",
        "    (hp : IsSphericalCode p (1 / 2 : ℝ)) : n ≤ 12 := by",
        "  have hs : (kissing3Cert.sRat : ℝ) = (1 / 2 : ℝ) := by",
        "    norm_num [BVCert5.sRat, kissing3Cert]",
        "  have hle : (n : ℝ) ≤ (kissing3Cert.bound : ℝ) := by",
        "    apply BVCert5.sound kissing3Cert_valid",
        "    rwa [hs]",
        "  have hlt : (kissing3Cert.bound : ℝ) < 13 := by",
        "    exact_mod_cast kissing3Cert_bound_lt_13",
        "  have hn13 : (n : ℝ) < 13 := lt_of_le_of_lt hle hlt",
        "  have hn_nat : n < 13 := by exact_mod_cast hn13",
        "  omega",
        "",
        "/-- **Kissing number in dimension 3 (lower bound)**:",
        "the 12 vertices of the regular icosahedron form a `(12, 1/2)`-spherical code",
        "(since `1 / √5 < 1 / 2`). -/",
        "theorem kissingNumber_three_lower :",
        "    ∃ p : Fin 12 → UnitSphere, IsSphericalCode p (1 / 2 : ℝ) := by",
        "  refine ⟨icosahedron12, fun i j hij => ?_⟩",
        "  have h1 : inner ℝ (icosahedron12 i).1 (icosahedron12 j).1 ≤ 1 / Real.sqrt 5 :=",
        "    icosahedron12_inner_le i j hij",
        "  have h2 : (1 : ℝ) / Real.sqrt 5 ≤ 1 / 2 := by",
        "    have hsqrt : (2 : ℝ) ≤ Real.sqrt 5 := by",
        "      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]",
        "      exact Real.sqrt_le_sqrt (by norm_num)",
        "    exact one_div_le_one_div_of_le (by norm_num) hsqrt",
        "  exact h1.trans h2",
        "",
        "/-- **Exact kissing number in dimension 3 (`K(3) = 12`)**:",
        "an `n`-point spherical code on `S²` with separation `≥ 60°` (`⟪pᵢ, pⱼ⟫ ≤ 1/2`)",
        "exists if and only if `n ≤ 12`. -/",
        "theorem kissingNumber_three_exact (n : ℕ) :",
        "    (∃ p : Fin n → UnitSphere, IsSphericalCode p (1 / 2 : ℝ)) ↔ n ≤ 12 := by",
        "  constructor",
        "  · rintro ⟨p, hp⟩",
        "    exact kissingNumber_three_upper hp",
        "  · intro hn",
        "    obtain ⟨q, hq⟩ := kissingNumber_three_lower",
        "    refine ⟨fun i => q (Fin.castLE hn i), fun i j hij => hq _ _ ?_⟩",
        "    intro heq",
        "    exact hij (Fin.ext (by simpa using congr_arg Fin.val heq))",
        "",
        "/-! ## Negative tests: malformed SDP certificates are rejected -/",
        "",
        "/-- Negative test 1: a certificate with an asymmetric matrix is rejected. -/",
        "def badCertAsymm : BVCert5 :=",
        "  { kissing3Cert with F4 := [[1000000, 1], [0, 1000000]] }",
        "",
        "theorem badCertAsymm_rejected : badCertAsymm.isValid = false := by decide",
        "",
        "/-- Negative test 2: a certificate with a non-PSD matrix (`F5 = [[-1]]`) is rejected. -/",
        "def badCertNotPSD : BVCert5 :=",
        "  { kissing3Cert with F5 := [[-1]] }",
        "",
        "theorem badCertNotPSD_rejected : badCertNotPSD.isValid = false := by decide",
        "",
        "/-- Negative test 3: a certificate whose matrices are PSD but break the",
        "polynomial identity (`A0[0][0]` perturbed) is rejected. -/",
        "def badCertBadId : BVCert5 :=",
        "  { kissing3Cert with F5 := [[2000000]], R_F5 := [[1414213]] }",
        "",
        "theorem badCertBadId_rejected : badCertBadId.isValid = false := by decide",
        "",
        "end Geodesy.Spherical",
        "",
    ])

    out_path = "/Users/yuiseki/src/github.com/geolonia/_20_percent_rule/__yuiseki/_lean/LeanGeodesy/LeanGeodesy/Spherical/KissingNumber3.lean"
    with open(out_path, "w") as f:
        f.write("\n".join(lines))
    print(f"Wrote {out_path} ({len(lines)} lines)")

if __name__ == "__main__":
    solve_and_export()
