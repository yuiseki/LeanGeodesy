"""
Generate LeanGeodesy/LeanGeodesy/Spherical/Tammes18BV8.lean from the verified
exact rational BV(8, 16) certificate JSON (scratch/bv8_18_cert.json).

Certifies unconditionally in the Lean 4 kernel:
  A(3, 317/500) <= 17
  T(18) < arccos(317/500) ≈ 50.65415° < 50.655° < 50.68095° (Robinson 1961)
including a direct formal proof that a = arccos(317/500) strictly satisfies
Robinson (1961, Theorem Ba) LHS < 12π.
"""
import json
import math
import time
from fractions import Fraction
from pathlib import Path
import sys

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))
from round_bv8_18 import build_sos_specs, poly_mul, sym3_canon_exact

def fmt_mat(M):
    return "[" + ", ".join("[" + ", ".join(str(int(x)) for x in row) + "]" for row in M) + "]"

def fmt_poly3(p):
    # Sorted by (a, b, c) lexicographically, matching mergePoly3 / sym3Canon order
    items = sorted(p.items())
    return "[" + ", ".join(f"({a}, {b}, {c}, {int(v)})" for (a, b, c), v in items if v != 0) + "]"

def fmt_basis(basis_list):
    return "[" + ", ".join(fmt_poly3(p) for p in basis_list) + "]"

def sym3_canon_int(p):
    """Exact match to Lean's `sym3Canon`: maps each term (a,b,c,v) to (max, mid, min, v) and sums."""
    res = {}
    for (a, b, c), v in p.items():
        if v == 0:
            continue
        m = tuple(sorted((a, b, c), reverse=True))
        res[m] = res.get(m, 0) + int(v)
    return {m: v for m, v in res.items() if v != 0}

def quad_poly3_int(M, basis):
    """Exact integer expansion of quadPoly3 m M basis."""
    m = len(basis)
    res = {}
    for i in range(m):
        bi = basis[i]
        # qi = sum_j M[i][j] * basis[j]
        qi = {}
        for j in range(m):
            mij = int(M[i][j])
            if mij == 0:
                continue
            for mon, coeff in basis[j].items():
                qi[mon] = qi.get(mon, 0) + mij * int(coeff)
        qi = {mon: v for mon, v in qi.items() if v != 0}
        for m1, c1 in bi.items():
            for m2, c2 in qi.items():
                mon = (m1[0] + m2[0], m1[1] + m2[1], m1[2] + m2[2])
                res[mon] = res.get(mon, 0) + int(c1) * c2
    return {mon: v for mon, v in res.items() if v != 0}

def mul_poly3_int(p, q):
    res = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            mon = (m1[0] + m2[0], m1[1] + m2[1], m1[2] + m2[2])
            res[mon] = res.get(mon, 0) + int(c1) * int(c2)
    return {mon: v for mon, v in res.items() if v != 0}

def right_assoc_append(parts):
    if len(parts) == 1:
        return parts[0]
    return f"{parts[0]} ++ ({right_assoc_append(parts[1:])})"

def quad_poly3_chunk_int(M_rows, b_rows, all_basis):
    """Exact integer expansion of quadPoly3FastAux M_rows b_rows all_basis."""
    res = {}
    for row, bi in zip(M_rows, b_rows):
        qi = {}
        for j, mij in enumerate(row):
            mij = int(mij)
            if mij == 0:
                continue
            for mon, coeff in all_basis[j].items():
                qi[mon] = qi.get(mon, 0) + mij * int(coeff)
        qi = {mon: v for mon, v in qi.items() if v != 0}
        for m1, c1 in bi.items():
            for m2, c2 in qi.items():
                mon = (m1[0] + m2[0], m1[1] + m2[1], m1[2] + m2[2])
                res[mon] = res.get(mon, 0) + int(c1) * c2
    return {mon: v for mon, v in res.items() if v != 0}

def main():
    t0 = time.time()
    in_json = Path(sys.argv[1]) if len(sys.argv) > 1 else SCRIPT_DIR / "bv8_18_cert.json"
    with open(in_json) as f:
        cert = json.load(f)

    sNum = cert["sNum"]
    sDen = cert["sDen"]
    dK = cert["dK"]
    dS0 = int(cert["dS0"])
    dR = cert["dR"]
    dM = [int(x) for x in cert["dM"]]
    dS = math.lcm(*dM)
    sc = [dS // dm for dm in dM]
    for dm, s_i in zip(dM, sc):
        assert dm * s_i == dS

    specs = build_sos_specs()
    Delta_int = {(0,0,0): 1, (1,1,1): 2, (2,0,0): -1, (0,2,0): -1, (0,0,2): -1}
    g1_int = {(0,0,0): sNum, (1,0,0): sNum - sDen, (2,0,0): -sDen}

    # Precompute exact canonicalized poly3 for each of the 7 SOS blocks AND each 10-row chunk
    q_canon_vals = []
    q_chunk_vals = []
    basis_ints = []
    chunk_rows = 10
    for idx in range(7):
        b_int = [{m: int(v) for m, v in p.items()} for p in specs[idx][2]]
        basis_ints.append(b_int)
        M_int = [[int(x) for x in row] for row in cert["M"][idx]]
        chunks_i = []
        total_canon = {}
        for start in range(0, len(b_int), chunk_rows):
            qp = quad_poly3_chunk_int(M_int[start:start+chunk_rows], b_int[start:start+chunk_rows], b_int)
            if idx < 3:
                mp = qp
            elif idx < 6:
                mp = mul_poly3_int(Delta_int, qp)
            else:
                mp = mul_poly3_int(g1_int, qp)
            sc_chunk = sym3_canon_int(mp)
            chunks_i.append(sc_chunk)
            for mon, val in sc_chunk.items():
                total_canon[mon] = total_canon.get(mon, 0) + val
        total_canon = {mon: v for mon, v in total_canon.items() if v != 0}
        q_chunk_vals.append(chunks_i)
        q_canon_vals.append(total_canon)
        print(f"Block {idx} ({specs[idx][0]}, dim {len(b_int)}, {len(chunks_i)} chunks): {len(total_canon)} canonical terms", flush=True)

    sph_dir = SCRIPT_DIR.parent.parent / "LeanGeodesy" / "Spherical"

    # =========================================================================
    # 1. Tammes18BV8Data.lean — certificate data only
    # =========================================================================
    data_lines = ["""import LeanGeodesy.Spherical.BachocVallentinCert8

/-!
# Certificate Data for Tammes `N = 18` Degree-8 Three-Point SDP (`BV(8, 16)`)

Stores the exact integer matrices, trimmed lower-triangular Cholesky factors,
and trivariate SOS bases for `tammes18BV8Cert`, chunked in 10-row pieces so
kernel verification proceeds in bounded-memory steps.
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 1600000
"""]

    def emit_mat_data(name, M):
        if len(M) <= chunk_rows:
            data_lines.append(f"def {name} : List (List ℤ) := {fmt_mat(M)}")
            return 1
        parts = []
        for p_idx in range(0, len(M), chunk_rows):
            pname = f"{name}_p{p_idx // chunk_rows}"
            parts.append(pname)
            data_lines.append(f"def {pname} : List (List ℤ) := {fmt_mat(M[p_idx:p_idx+chunk_rows])}")
        data_lines.append(f"def {name} : List (List ℤ) := {right_assoc_append(parts)}")
        return len(parts)

    def emit_basis_data(name, B):
        if len(B) <= chunk_rows:
            data_lines.append(f"def {name} : List Poly3 := {fmt_basis(B)}")
            return 1
        parts = []
        for p_idx in range(0, len(B), chunk_rows):
            pname = f"{name}_p{p_idx // chunk_rows}"
            parts.append(pname)
            data_lines.append(f"def {pname} : List Poly3 := {fmt_basis(B[p_idx:p_idx+chunk_rows])}")
        data_lines.append(f"def {name} : List Poly3 := {right_assoc_append(parts)}")
        return len(parts)

    for k in range(9):
        emit_mat_data(f"t18b8_F{k}", cert['F'][k])
        emit_mat_data(f"t18b8_RF{k}", cert['R_F'][k])
    emit_mat_data("t18b8_S0", cert['S0'])
    emit_mat_data("t18b8_RS0", cert['R_S0'])
    emit_mat_data("t18b8_S1", cert['S1'])
    emit_mat_data("t18b8_RS1", cert['R_S1'])
    n_chunks = []
    for idx in range(7):
        nc = emit_mat_data(f"t18b8_M{idx}", cert['M'][idx])
        R_orig = cert['R_M'][idx]
        m_dim = len(R_orig)
        L_trim = [[R_orig[k][i] for k in range(i + 1)] for i in range(m_dim)]
        emit_mat_data(f"t18b8_RM{idx}", L_trim)
        emit_basis_data(f"t18b8_b{idx}", basis_ints[idx])
        n_chunks.append(nc)

    data_lines.append(f"""
/-- Certified rational degree-8 + Legendre `P₁..P₁₆` Bachoc–Vallentin SDP certificate
at `s = 317 / 500` (`50.65414°`), giving upper bound `{cert['bound_num']} / 10⁹ < 18`. -/
def tammes18BV8Cert : BVCert8 where
  sNum := {sNum}
  sDen := {sDen}
  dK := {dK}
  dS0 := {dS0}
  dS := {dS}
  dR := {dR}""")
    for k in range(9):
        data_lines.append(f"  F{k} := t18b8_F{k}")
        data_lines.append(f"  R_F{k} := t18b8_RF{k}")
    data_lines.append(f"  c2 := [{', '.join(str(x) for x in cert['c2'])}]")
    data_lines.append("  S0 := t18b8_S0")
    data_lines.append("  R_S0 := t18b8_RS0")
    data_lines.append("  S1 := t18b8_S1")
    data_lines.append("  R_S1 := t18b8_RS1")
    for idx in range(7):
        data_lines.append(f"  m{idx} := {len(basis_ints[idx])}")
        data_lines.append(f"  dM{idx} := {dM[idx]}")
        data_lines.append(f"  sc{idx} := {sc[idx]}")
        data_lines.append(f"  M{idx} := t18b8_M{idx}")
        data_lines.append(f"  R{idx} := t18b8_RM{idx}")
        data_lines.append(f"  b{idx} := t18b8_b{idx}")
    data_lines.append("\nend Geodesy.Spherical\n")

    data_path = sph_dir / "Tammes18BV8Data.lean"
    with open(data_path, "w") as f:
        f.write("\n".join(data_lines))
    print(f"Wrote {data_path} ({len(data_lines)} lines)")

    # =========================================================================
    # 2. Tammes18BV8Check.lean — all Cholesky PSD checks (10-row chunked)
    # =========================================================================
    chk_lines = ["""import LeanGeodesy.Spherical.Tammes18BV8Data

/-!
# Cholesky + Diagonal Dominance Verification for `tammes18BV8Cert`

Verifies all 18 positive-semidefinite certificate matrices (`F0..F8`, `S0`, `S1`,
and `M0..M6`) in the Lean 4 kernel using 10-row chunks via `choleskyCheckRows_append`.
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 1600000

theorem t18b8_basic :
    decide (0 < tammes18BV8Cert.sDen) = true ∧
    decide (0 < tammes18BV8Cert.dK) = true ∧
    decide (0 < tammes18BV8Cert.dS0) = true ∧
    decide (0 < tammes18BV8Cert.dS) = true ∧
    decide (0 < tammes18BV8Cert.dR) = true ∧
    decide (-(tammes18BV8Cert.sDen : ℤ) < tammes18BV8Cert.sNum) = true ∧
    (List.range 16).all (fun k => decide (0 ≤ tammes18BV8Cert.c2.getD k 0)) = true ∧
    decide (tammes18BV8Cert.dM0 * tammes18BV8Cert.sc0 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.dM1 * tammes18BV8Cert.sc1 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.dM2 * tammes18BV8Cert.sc2 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.dM3 * tammes18BV8Cert.sc3 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.dM4 * tammes18BV8Cert.sc4 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.dM5 * tammes18BV8Cert.sc5 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.dM6 * tammes18BV8Cert.sc6 = tammes18BV8Cert.dS) = true ∧
    decide (tammes18BV8Cert.b0.length = tammes18BV8Cert.m0) = true ∧
    decide (tammes18BV8Cert.b1.length = tammes18BV8Cert.m1) = true ∧
    decide (tammes18BV8Cert.b2.length = tammes18BV8Cert.m2) = true ∧
    decide (tammes18BV8Cert.b3.length = tammes18BV8Cert.m3) = true ∧
    decide (tammes18BV8Cert.b4.length = tammes18BV8Cert.m4) = true ∧
    decide (tammes18BV8Cert.b5.length = tammes18BV8Cert.m5) = true ∧
    decide (tammes18BV8Cert.b6.length = tammes18BV8Cert.m6) = true := by
  decide
"""]
    for k in range(9):
        chk_lines.append(f"theorem t18b8_cF{k} : isCholeskyDDValid {9 - k} tammes18BV8Cert.dK tammes18BV8Cert.dR tammes18BV8Cert.F{k} tammes18BV8Cert.R_F{k} = true := by decide")
    chk_lines.append("theorem t18b8_cS0 : isCholeskyDDValid 9 tammes18BV8Cert.dS0 tammes18BV8Cert.dR tammes18BV8Cert.S0 tammes18BV8Cert.R_S0 = true := by decide")
    chk_lines.append("theorem t18b8_cS1 : isCholeskyDDValid 8 tammes18BV8Cert.dK tammes18BV8Cert.dR tammes18BV8Cert.S1 tammes18BV8Cert.R_S1 = true := by decide")

    for idx in range(7):
        nc = n_chunks[idx]
        m_dim = len(basis_ints[idx])
        if nc == 1:
            chk_lines.append(f"theorem t18b8_cM{idx} : isCholeskyDDLower tammes18BV8Cert.m{idx} tammes18BV8Cert.dM{idx} tammes18BV8Cert.dR tammes18BV8Cert.M{idx} tammes18BV8Cert.R{idx} = true := by decide")
        else:
            dR2_expr = "((tammes18BV8Cert.dR : ℤ) * (tammes18BV8Cert.dR : ℤ))"
            chk_lines.append(f"""
private theorem t18b8_cM{idx}_hdr :
    (decide (0 < tammes18BV8Cert.dM{idx}) &&
     decide (0 < tammes18BV8Cert.dR) &&
     decide (tammes18BV8Cert.R{idx}.length = tammes18BV8Cert.m{idx}) &&
     tammes18BV8Cert.R{idx}.all (fun row => decide (row.length ≤ tammes18BV8Cert.m{idx})) &&
     isSymmInt tammes18BV8Cert.m{idx} tammes18BV8Cert.M{idx} &&
     decide (tammes18BV8Cert.M{idx}.length = tammes18BV8Cert.m{idx})) = true := by decide""")
            for c in range(nc):
                start = c * chunk_rows
                chk_lines.append(
                    f"private theorem t18b8_cM{idx}_r{c} : "
                    f"choleskyCheckRows {m_dim} {dR2_expr} (tammes18BV8Cert.dM{idx} : ℤ) t18b8_RM{idx} {start} t18b8_M{idx}_p{c} t18b8_RM{idx}_p{c} = true := by decide"
                )
            chk_lines.append(f"""theorem t18b8_cM{idx} : isCholeskyDDLower tammes18BV8Cert.m{idx} tammes18BV8Cert.dM{idx} tammes18BV8Cert.dR tammes18BV8Cert.M{idx} tammes18BV8Cert.R{idx} = true := by
  unfold isCholeskyDDLower
  rw [t18b8_cM{idx}_hdr, Bool.true_and]
  change choleskyCheckRows {m_dim} {dR2_expr} (tammes18BV8Cert.dM{idx} : ℤ) t18b8_RM{idx} 0 ({right_assoc_append([f't18b8_M{idx}_p{c}' for c in range(nc)])}) ({right_assoc_append([f't18b8_RM{idx}_p{c}' for c in range(nc)])}) = true""")
            for c in range(nc - 1):
                chk_lines.append(f"  refine choleskyCheckRows_append {m_dim} {dR2_expr} (tammes18BV8Cert.dM{idx} : ℤ) t18b8_RM{idx} {c * chunk_rows} _ _ _ _ rfl t18b8_cM{idx}_r{c} ?_")
            chk_lines.append(f"  exact t18b8_cM{idx}_r{nc - 1}")

    chk_lines.append("\nend Geodesy.Spherical\n")
    chk_path = sph_dir / "Tammes18BV8Check.lean"
    with open(chk_path, "w") as f:
        f.write("\n".join(chk_lines))
    print(f"Wrote {chk_path} ({len(chk_lines)} lines)")

    def emit_q_chunks(target_lines, idx, chunk_range, public=False):
        vis = "" if public else "private "
        if idx < 3:
            wrap = lambda inner: f"sym3Canon ({inner})"
        elif idx < 6:
            wrap = lambda inner: f"sym3Canon (mulPoly3Sorted BVCert8.polyDelta8 ({inner}))"
        else:
            wrap = lambda inner: f"sym3Canon (mulPoly3Sorted (BVCert8.polyG1_8 tammes18BV8Cert.sNum tammes18BV8Cert.sDen) ({inner}))"
        for c in chunk_range:
            c_lit = fmt_poly3(q_chunk_vals[idx][c])
            target_lines.append(f"""
{vis}theorem t18b8_q{idx}_c{c} :
    {wrap(f'quadPoly3FastAux t18b8_M{idx}_p{c} t18b8_b{idx}_p{c} t18b8_b{idx}')} =
    {c_lit} := by decide""")

    def emit_q_combine(target_lines, idx):
        nc = n_chunks[idx]
        q_lit = fmt_poly3(q_canon_vals[idx])
        if idx < 3:
            mul_opt = "none"
        elif idx < 6:
            mul_opt = "(some BVCert8.polyDelta8)"
        else:
            mul_opt = "(some (BVCert8.polyG1_8 tammes18BV8Cert.sNum tammes18BV8Cert.sDen))"
        if nc == 1:
            target_lines.append(f"""
theorem t18b8_q{idx} :
    quadPoly3Sym10 {mul_opt} tammes18BV8Cert.M{idx} tammes18BV8Cert.b{idx} =
    {q_lit} := by decide""")
            return
        m_rhs = right_assoc_append([f"t18b8_M{idx}_p{c}" for c in range(nc)])
        b_rhs = right_assoc_append([f"t18b8_b{idx}_p{c}" for c in range(nc)])
        target_lines.append(f"""
theorem t18b8_q{idx} :
    quadPoly3Sym10 {mul_opt} tammes18BV8Cert.M{idx} tammes18BV8Cert.b{idx} =
    {q_lit} := by
  have hlen : (tammes18BV8Cert.M{idx}.length + 9) / 10 = {nc} := by decide
  unfold quadPoly3Sym10
  rw [hlen]
  change sym3Canon (quadPoly3Sym10Aux {nc} {mul_opt} ({m_rhs}) ({b_rhs}) t18b8_b{idx}) = _""")
        for c in range(nc - 1):
            target_lines.append(f"  rw [quadPoly3Sym10Aux_step {nc - 1 - c} {mul_opt} t18b8_M{idx}_p{c} _ t18b8_b{idx}_p{c} _ t18b8_b{idx} rfl rfl]")
        target_lines.append(f"  rw [quadPoly3Sym10Aux_last {mul_opt} t18b8_M{idx}_p{nc-1} t18b8_b{idx}_p{nc-1} t18b8_b{idx} (by decide) (by decide) (by decide) (by decide)]")
        target_lines.append("  dsimp only")
        target_lines.append(f"  rw [{', '.join(f't18b8_q{idx}_c{c}' for c in range(nc))}]")
        target_lines.append("  decide")

    def emit_q_block(target_lines, idx):
        nc = n_chunks[idx]
        if nc > 1:
            emit_q_chunks(target_lines, idx, range(nc), public=False)
        emit_q_combine(target_lines, idx)

    # =========================================================================
    # 3a. Tammes18BV8Q6a.lean — first 4 chunks of M6 (rows 0..39)
    # =========================================================================
    q6a_lines = ["""import LeanGeodesy.Spherical.Tammes18BV8Check

/-!
# Chunked Trivariate Quadratic-Form Verification for `M6` (Rows 0–39)
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 2400000
"""]
    emit_q_chunks(q6a_lines, 6, range(0, 4), public=True)
    q6a_lines.append("\nend Geodesy.Spherical\n")
    q6a_path = sph_dir / "Tammes18BV8Q6a.lean"
    with open(q6a_path, "w") as f:
        f.write("\n".join(q6a_lines))
    print(f"Wrote {q6a_path} ({len(q6a_lines)} lines)")

    # =========================================================================
    # 3b. Tammes18BV8Q6b.lean — last 3 chunks of M6 (rows 40..69) + t18b8_q6
    # =========================================================================
    q6b_lines = ["""import LeanGeodesy.Spherical.Tammes18BV8Q6a

/-!
# Chunked Trivariate Quadratic-Form Verification for `M6` (Rows 40–69)
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 2400000
"""]
    emit_q_chunks(q6b_lines, 6, range(4, 7), public=False)
    emit_q_combine(q6b_lines, 6)
    q6b_lines.append("\nend Geodesy.Spherical\n")
    q6b_path = sph_dir / "Tammes18BV8Q6b.lean"
    with open(q6b_path, "w") as f:
        f.write("\n".join(q6b_lines))
    print(f"Wrote {q6b_path} ({len(q6b_lines)} lines)")

    # =========================================================================
    # 3c..3e. Tammes18BV8Q1a/b/c.lean — M1 (54x54, 2 chunks per file)
    # =========================================================================
    q1a_lines = ["""import LeanGeodesy.Spherical.Tammes18BV8Q6b

/-!
# Chunked Trivariate Quadratic-Form Verification for `M1` (Rows 0–19)
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 2400000
"""]
    emit_q_chunks(q1a_lines, 1, range(0, 2), public=True)
    q1a_lines.append("\nend Geodesy.Spherical\n")
    with open(sph_dir / "Tammes18BV8Q1a.lean", "w") as f:
        f.write("\n".join(q1a_lines))

    q1b_lines = ["""import LeanGeodesy.Spherical.Tammes18BV8Q1a

/-!
# Chunked Trivariate Quadratic-Form Verification for `M1` (Rows 20–39)
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 2400000
"""]
    emit_q_chunks(q1b_lines, 1, range(2, 4), public=True)
    q1b_lines.append("\nend Geodesy.Spherical\n")
    with open(sph_dir / "Tammes18BV8Q1b.lean", "w") as f:
        f.write("\n".join(q1b_lines))

    q1c_lines = ["""import LeanGeodesy.Spherical.Tammes18BV8Q1b

/-!
# Chunked Trivariate Quadratic-Form Verification for `M1` (Rows 40–53)
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 2400000
"""]
    emit_q_chunks(q1c_lines, 1, range(4, 6), public=False)
    emit_q_combine(q1c_lines, 1)
    q1c_lines.append("\nend Geodesy.Spherical\n")
    with open(sph_dir / "Tammes18BV8Q1c.lean", "w") as f:
        f.write("\n".join(q1c_lines))

    # =========================================================================
    # 3f..3h. Tammes18BV8Q0a/Q0b/Q34.lean — M0, M2, M3, M4, M5
    # =========================================================================
    q0a_lines = ["""import LeanGeodesy.Spherical.Tammes18BV8Q1c

/-!
# Chunked Trivariate Quadratic-Form Verification for `M0` (Rows 0–29)
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 2400000
"""]
    emit_q_chunks(q0a_lines, 0, range(0, 3), public=True)
    q0a_lines.append("\nend Geodesy.Spherical\n")
    with open(sph_dir / "Tammes18BV8Q0a.lean", "w") as f:
        f.write("\n".join(q0a_lines))

    q0b_lines = ["""import LeanGeodesy.Spherical.Tammes18BV8Q0a

/-!
# Chunked Trivariate Quadratic-Form Verification for `M0` (Rows 30–40) and `M2`
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 2400000
"""]
    emit_q_chunks(q0b_lines, 0, range(3, 5), public=False)
    emit_q_combine(q0b_lines, 0)
    emit_q_block(q0b_lines, 2)
    q0b_lines.append("\nend Geodesy.Spherical\n")
    with open(sph_dir / "Tammes18BV8Q0b.lean", "w") as f:
        f.write("\n".join(q0b_lines))

    q34_lines = ["""import LeanGeodesy.Spherical.Tammes18BV8Q0b

/-!
# Chunked Trivariate Quadratic-Form Verification for `M3`, `M4`, and `M5`
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 2400000
"""]
    for idx in [3, 4, 5]:
        emit_q_block(q34_lines, idx)
    q34_lines.append("\nend Geodesy.Spherical\n")
    with open(sph_dir / "Tammes18BV8Q34.lean", "w") as f:
        f.write("\n".join(q34_lines))

    # =========================================================================
    # 4. Tammes18BV8.lean — eq2, eq3, validity, and main theorems
    # =========================================================================
    out_path = sph_dir / "Tammes18BV8.lean"
    lines = []
    lines.append("""import LeanGeodesy.Spherical.Tammes18BV8Q34
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Certified Degree-8 Three-Point SDP Upper Bound for Tammes `N = 18` on `S²`

We prove unconditionally in the Lean 4 kernel that no spherical code of size `18`
on `S²` can have maximum pairwise inner product `≤ 317 / 500 = 0.634`, i.e.,

```
A(3, 317/500) ≤ 17
```

Equivalently, every `18`-point configuration on `S²` has minimum geodesic separation
strictly less than `arccos (317 / 500) ≈ 50.65414° < 50.655°`.

This strictly improves the best previously known upper bound due to R. M. Robinson
(1961, Theorem Ba, Section 9.1), which gives `T(18) ≤ 50.68095°`. We also prove
directly in Lean that `a = arccos (317 / 500)` strictly satisfies Robinson's
Theorem Ba inequality `4 · 18 · Δ(a) + (2 · 18 - 12) · Δ*(a) < 12π`.

The proof uses a Chebyshev-basis degree-8 Bachoc–Vallentin three-point SDP certificate
with two-point Legendre terms `P₁..P₁₆` and 7 reduced `S₃`-symmetric SOS blocks,
checked purely by `decide` in the Lean 4 kernel (no `native_decide`, no custom axioms).
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 2400000

private theorem t18b8_eq2 : tammes18BV8Cert.checkEq2 = true := by decide
""")

    lines.append("""
set_option maxHeartbeats 2400000 in
private theorem t18b8_eq3 :
    (sym3Canon (poly3Scale (-((tammes18BV8Cert.sDen : ℤ) * (tammes18BV8Cert.dS : ℤ))) tammes18BV8Cert.polyG3) ==
      sym3Canon (poly3Scale (tammes18BV8Cert.dK : ℤ) tammes18BV8Cert.polyRHS3Canon)) = true := by
  unfold BVCert8.polyRHS3Canon
  dsimp only
  rw [t18b8_q0, t18b8_q1, t18b8_q2, t18b8_q3, t18b8_q4, t18b8_q5, t18b8_q6]
  decide

/-- Kernel-verified validity of `tammes18BV8Cert` (no `native_decide`, no extra axioms). -/
theorem tammes18BV8Cert_valid : tammes18BV8Cert.isValid = true := by
  unfold BVCert8.isValid
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hb0, hb1, hb2, hb3, hb4, hb5, hb6⟩ := t18b8_basic
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
    t18b8_cF0, t18b8_cF1, t18b8_cF2, t18b8_cF3, t18b8_cF4, t18b8_cF5, t18b8_cF6, t18b8_cF7, t18b8_cF8,
    t18b8_cS0, t18b8_cS1,
    t18b8_cM0, t18b8_cM1, t18b8_cM2, t18b8_cM3, t18b8_cM4, t18b8_cM5, t18b8_cM6,
    t18b8_eq2, t18b8_eq3]
  rfl

private theorem tammes18BV8Cert_bound_lt_18 : tammes18BV8Cert.bound < 18 := by
  have hnum : tammes18BV8Cert.boundNum < 18 * (tammes18BV8Cert.dK : ℤ) := by decide
  have hdK : (0 : ℝ) < (tammes18BV8Cert.dK : ℝ) := by norm_num [tammes18BV8Cert]
  rw [BVCert8.bound, div_lt_iff₀ hdK]
  have hnumR : (tammes18BV8Cert.boundNum : ℝ) < 18 * (tammes18BV8Cert.dK : ℝ) := by exact_mod_cast hnum
  linarith

/-- **Certified spherical-code upper bound on `S²`**:
every `(n, 317 / 500)`-spherical code on `S²` has at most `17` points (`A(3, 317/500) ≤ 17`). -/
theorem sphericalCode_three_upper_317_500 {n : ℕ} {p : Fin n → UnitSphere}
    (hp : IsSphericalCode p (317 / 500 : ℝ)) : n ≤ 17 := by
  have hs : tammes18BV8Cert.s = (317 / 500 : ℝ) := by norm_num [BVCert8.s, tammes18BV8Cert]
  have hle : (n : ℝ) ≤ tammes18BV8Cert.bound := tammes18BV8Cert.sound tammes18BV8Cert_valid (hs ▸ hp)
  have hlt : (n : ℝ) < 18 := lt_of_le_of_lt hle tammes18BV8Cert_bound_lt_18
  have hnat : n < 18 := by exact_mod_cast hlt
  omega

/-- **Certified Tammes `N = 18` strict upper bound**:
every `18`-point configuration on `S²` with minimum separation `θ` satisfies
`θ < arccos (317 / 500) ≈ 50.65414°`. -/
theorem tammes_18_strict_upper_317_500 {p : Fin 18 → UnitSphere} {θ : ℝ}
    (hp : IsSeparated p θ) : θ < Real.arccos (317 / 500 : ℝ) := by
  by_contra h
  push Not at h
  have hsep : IsSeparated p (Real.arccos (317 / 500 : ℝ)) := fun i j hij => le_trans h (hp i j hij)
  have hcode : IsSphericalCode p (317 / 500 : ℝ) := by
    have h0 : (0 : ℝ) ≤ Real.arccos (317 / 500 : ℝ) := Real.arccos_nonneg _
    have hpi : Real.arccos (317 / 500 : ℝ) ≤ Real.pi := Real.arccos_le_pi _
    have hc : Real.cos (Real.arccos (317 / 500 : ℝ)) = (317 / 500 : ℝ) :=
      Real.cos_arccos (by norm_num) (by norm_num)
    rw [← hc]
    exact (isSeparated_iff_isSphericalCode p h0 hpi).mp hsep
  have hle := sphericalCode_three_upper_317_500 hcode
  omega

/-! ## Certified angle bounds & rigorous comparison with Robinson (1961) -/

private theorem trig_taylor_bounds {x : ℝ} (hx : 0 ≤ x) :
    (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x) ∧
    (Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) ∧
    (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x) := by
  have hmono : ∀ (f f' : ℝ → ℝ),
      (∀ t, HasDerivAt f (f' t) t) → (∀ t, 0 ≤ t → 0 ≤ f' t) → f 0 = 0 →
      ∀ t, 0 ≤ t → 0 ≤ f t := by
    intro f f' hderiv hf' hf0 t ht
    have hcont : ContinuousOn f (Set.Icc 0 t) := fun y _ => (hderiv y).continuousAt.continuousWithinAt
    have hdiff : ∀ y ∈ Set.Ioo 0 t, 0 ≤ deriv f y := fun y hy => by
      rw [(hderiv y).deriv]; exact hf' y hy.1.le
    have hmono' := monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hcont
      (fun y _ => (hderiv y).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [interior_Icc] at hy; exact hdiff y hy)
    have hle := hmono' (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
    linarith
  have h0 : ∀ t, 0 ≤ t → 0 ≤ 1 - Real.cos t := fun t _ => by linarith [Real.cos_le_one t]
  have h1 : ∀ t, 0 ≤ t → 0 ≤ t - Real.sin t :=
    hmono (fun t => t - Real.sin t) (fun t => 1 - Real.cos t)
      (fun t => (hasDerivAt_id' t).sub (Real.hasDerivAt_sin t)) h0 (by simp)
  have h2 : ∀ t, 0 ≤ t → 0 ≤ Real.cos t - 1 + t ^ 2 / 2 :=
    hmono (fun t => Real.cos t - 1 + t ^ 2 / 2) (fun t => t - Real.sin t)
      (fun t => by
        have hd := ((Real.hasDerivAt_cos t).sub (hasDerivAt_const t (1 : ℝ))).add
          ((hasDerivAt_pow 2 t).div_const 2)
        have heq : -Real.sin t - 0 + (2 : ℝ) * t ^ (2 - 1) / 2 = t - Real.sin t := by norm_num; ring
        rw [← heq]; exact hd)
      h1 (by simp)
  have h3 : ∀ t, 0 ≤ t → 0 ≤ Real.sin t - t + t ^ 3 / 6 :=
    hmono (fun t => Real.sin t - t + t ^ 3 / 6) (fun t => Real.cos t - 1 + t ^ 2 / 2)
      (fun t => by
        have hd := ((Real.hasDerivAt_sin t).sub (hasDerivAt_id' t)).add
          ((hasDerivAt_pow 3 t).div_const 6)
        have heq : Real.cos t - 1 + (3 : ℝ) * t ^ (3 - 1) / 6 = Real.cos t - 1 + t ^ 2 / 2 := by norm_num; ring
        rw [← heq]; exact hd)
      h2 (by simp)
  have h4 : ∀ t, 0 ≤ t → 0 ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t :=
    hmono (fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t) (fun t => Real.sin t - t + t ^ 3 / 6)
      (fun t => by
        have hd := (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24)).sub (Real.hasDerivAt_cos t)
        have heq : 0 - (2 : ℝ) * t ^ (2 - 1) / 2 + (4 : ℝ) * t ^ (4 - 1) / 24 - (-Real.sin t) =
            Real.sin t - t + t ^ 3 / 6 := by norm_num; ring
        rw [← heq]; exact hd)
      h3 (by simp)
  have h5 : ∀ t, 0 ≤ t → 0 ≤ t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t :=
    hmono (fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
      (fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
      (fun t => by
        have hd := (((hasDerivAt_id' t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
          ((hasDerivAt_pow 5 t).div_const 120)).sub (Real.hasDerivAt_sin t)
        have heq : 1 - (3 : ℝ) * t ^ (3 - 1) / 6 + (5 : ℝ) * t ^ (5 - 1) / 120 - Real.cos t =
            1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by norm_num; ring
        rw [← heq]; exact hd)
      h4 (by simp)
  have h6 : ∀ t, 0 ≤ t → 0 ≤ Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) :=
    hmono (fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
      (fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
      (fun t => by
        have hd := (Real.hasDerivAt_cos t).sub
          ((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
            ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720))
        have heq : -Real.sin t - (0 - (2 : ℝ) * t ^ (2 - 1) / 2 + (4 : ℝ) * t ^ (4 - 1) / 24 -
            (6 : ℝ) * t ^ (6 - 1) / 720) = t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t := by norm_num; ring
        rw [← heq]; exact hd)
      h5 (by simp)
  have h7 : ∀ t, 0 ≤ t → 0 ≤ Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040) :=
    hmono (fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040))
      (fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
      (fun t => by
        have hd := (Real.hasDerivAt_sin t).sub
          ((((hasDerivAt_id' t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
            ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040))
        have heq : Real.cos t - (1 - (3 : ℝ) * t ^ (3 - 1) / 6 + (5 : ℝ) * t ^ (5 - 1) / 120 -
            (7 : ℝ) * t ^ (7 - 1) / 5040) =
            Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) := by norm_num; ring
        rw [← heq]; exact hd)
      h6 (by simp)
  have h8 : ∀ t, 0 ≤ t → 0 ≤ (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320) - Real.cos t :=
    hmono (fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320) - Real.cos t)
      (fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040))
      (fun t => by
        have hd := (((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add
          ((hasDerivAt_pow 8 t).div_const 40320)).sub (Real.hasDerivAt_cos t)
        have heq : 0 - (2 : ℝ) * t ^ (2 - 1) / 2 + (4 : ℝ) * t ^ (4 - 1) / 24 -
            (6 : ℝ) * t ^ (6 - 1) / 720 + (8 : ℝ) * t ^ (8 - 1) / 40320 - (-Real.sin t) =
            Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040) := by norm_num; ring
        rw [← heq]; exact hd)
      h7 (by simp)
  exact ⟨by linarith [h6 x hx], by linarith [h8 x hx], by linarith [h7 x hx]⟩

/-- Rigorous degree bound: `arccos (317 / 500) < 50.655°` (strictly below Robinson 1961's `50.68095°`). -/
theorem arccos_317_500_lt_deg :
    Real.arccos (317 / 500 : ℝ) < (50.655 : ℝ) * (Real.pi / 180) := by
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  set x : ℝ := (50.655 : ℝ) * (Real.pi / 180)
  have hx_lo : (0.884096 : ℝ) < x := by dsimp only [x]; linarith
  have hx_hi : x < (0.884097 : ℝ) := by dsimp only [x]; linarith
  have hx_nonneg : 0 ≤ x := by linarith
  have hx_le_pi : x ≤ Real.pi := by linarith
  have hcos_lt : Real.cos x < (317 / 500 : ℝ) := by
    have ht := (trig_taylor_bounds hx_nonneg).2.1
    have hx2_lo : (0.884096 : ℝ) ^ 2 < x ^ 2 := pow_lt_pow_left₀ hx_lo (by norm_num) (by norm_num)
    have hx4_hi : x ^ 4 < (0.884097 : ℝ) ^ 4 := pow_lt_pow_left₀ hx_hi hx_nonneg (by norm_num)
    have hx6_lo : (0.884096 : ℝ) ^ 6 < x ^ 6 := pow_lt_pow_left₀ hx_lo (by norm_num) (by norm_num)
    have hx8_hi : x ^ 8 < (0.884097 : ℝ) ^ 8 := pow_lt_pow_left₀ hx_hi hx_nonneg (by norm_num)
    linarith
  have hcos_arccos : Real.cos (Real.arccos (317 / 500 : ℝ)) = (317 / 500 : ℝ) :=
    Real.cos_arccos (by norm_num) (by norm_num)
  by_contra h
  push Not at h
  have hanti : Real.cos (Real.arccos (317 / 500 : ℝ)) ≤ Real.cos x :=
    Real.strictAntiOn_cos.antitoneOn
      ⟨hx_nonneg, hx_le_pi⟩ ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩ h
  linarith

/-- Combined Tammes `N = 18` degree bound: every `18`-point configuration on `S²` has
minimum geodesic separation strictly less than `50.655°`. -/
theorem tammes_18_lt_50_655_deg {p : Fin 18 → UnitSphere} {θ : ℝ}
    (hp : IsSeparated p θ) : θ < (50.655 : ℝ) * (Real.pi / 180) :=
  lt_trans (tammes_18_strict_upper_317_500 hp) arccos_317_500_lt_deg

/-- Left-hand side of Robinson (1961, Theorem Ba, Section 9.1) for `N = 18` at angular
separation `a`: `4 · 18 · Δ(a) + (2 · 18 - 12) · Δ*(a)`, where `Δ(a) = 3α - π` is the area
of an equilateral spherical triangle of side `a` (`cos α = cos a / (1 + cos a)`) and
`Δ*(a) = γ + 2φ - π` is the area of an isosceles spherical triangle with two sides `a`
enclosing angle `γ = 2π - 4α` and base angle `φ = arctan(1 / (cos a · tan(γ / 2)))`. -/
noncomputable def robinson18LHS (a : ℝ) : ℝ :=
  let α := Real.arccos (Real.cos a / (1 + Real.cos a))
  let Δ := 3 * α - Real.pi
  let γ := 2 * Real.pi - 4 * α
  let φ := Real.arctan (1 / (Real.cos a * Real.tan (γ / 2)))
  let Δstar := γ + 2 * φ - Real.pi
  4 * 18 * Δ + (2 * 18 - 12) * Δstar

/-- **Rigorous strict improvement over Robinson (1961, Theorem Ba)**:
at `a = arccos (317 / 500)`, Robinson's Theorem Ba area functional is strictly below `12π`,
proving that our certified bound `arccos (317 / 500)` is strictly sharper than Robinson's
upper bound `T(18) ≤ 50.68094488°`. -/
theorem robinson18_strict_improvement :
    robinson18LHS (Real.arccos (317 / 500 : ℝ)) < 12 * Real.pi := by
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  unfold robinson18LHS
  have hcos_a : Real.cos (Real.arccos (317 / 500 : ℝ)) = (317 / 500 : ℝ) :=
    Real.cos_arccos (by norm_num) (by norm_num)
  rw [hcos_a]
  have hratio : (317 / 500 : ℝ) / (1 + 317 / 500) = (317 / 817 : ℝ) := by norm_num
  rw [hratio]
  set α := Real.arccos (317 / 817 : ℝ)
  -- Step 1: α < 1.17235
  have hα_lt : α < (1.17235 : ℝ) := by
    have hcos_lt : Real.cos (1.17235 : ℝ) < (317 / 817 : ℝ) := by
      have ht := (trig_taylor_bounds (by norm_num : (0 : ℝ) ≤ 1.17235)).2.1
      linarith
    have hcos_α : Real.cos α = (317 / 817 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
    by_contra h
    push Not at h
    have hanti : Real.cos α ≤ Real.cos (1.17235 : ℝ) :=
      Real.strictAntiOn_cos.antitoneOn
        ⟨by norm_num, by linarith⟩ ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩ h
    linarith
  -- Step 2: 0 < α, so γ / 2 = π - 2α ∈ (0.7968, π/2)
  have hα_pos : (1 : ℝ) < α := by
    have hcos_gt : (317 / 817 : ℝ) < Real.cos (1 : ℝ) := by
      have ht := (trig_taylor_bounds (by norm_num : (0 : ℝ) ≤ 1)).1
      linarith
    have hcos_α : Real.cos α = (317 / 817 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
    by_contra h
    push Not at h
    have hanti : Real.cos (1 : ℝ) ≤ Real.cos α :=
      Real.strictAntiOn_cos.antitoneOn
        ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩ ⟨by norm_num, by linarith⟩ h
    linarith
  set g := (2 * Real.pi - 4 * α) / 2
  have hg_lo : (0.7968 : ℝ) < g := by dsimp only [g]; linarith
  have hg_hi : g < Real.pi / 2 := by dsimp only [g]; linarith
  -- Step 3: tan(0.7968) > 1.023, so tan g > 1.023
  have htan_g_gt : (1.023 : ℝ) < Real.tan g := by
    have htb := trig_taylor_bounds (by norm_num : (0 : ℝ) ≤ 0.7968)
    have hsin_lo : (0.71512 : ℝ) < Real.sin (0.7968 : ℝ) := by linarith [htb.2.2]
    have hcos_hi : Real.cos (0.7968 : ℝ) < (0.69900 : ℝ) := by linarith [htb.2.1]
    have hcos_pos : 0 < Real.cos (0.7968 : ℝ) := by linarith [htb.1]
    have htan0 : (1.023 : ℝ) < Real.tan (0.7968 : ℝ) := by
      rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos_pos]
      linarith
    have hmono : Real.tan (0.7968 : ℝ) < Real.tan g :=
      Real.strictMonoOn_tan ⟨by linarith, by linarith⟩ ⟨by linarith, hg_hi⟩ hg_lo
    linarith
  -- Step 4: 1 / ((317 / 500) * tan g) < 1.542 < tan(0.9955), so arctan(...) < 0.9955
  have harg_lt : 1 / ((317 / 500 : ℝ) * Real.tan g) < (1.542 : ℝ) := by
    have hden_pos : (0 : ℝ) < (317 / 500 : ℝ) * Real.tan g := by linarith
    rw [div_lt_iff₀ hden_pos]
    linarith
  have htan_9955 : (1.542 : ℝ) < Real.tan (0.9955 : ℝ) := by
    have htb := trig_taylor_bounds (by norm_num : (0 : ℝ) ≤ 0.9955)
    have hsin_lo : (0.83902 : ℝ) < Real.sin (0.9955 : ℝ) := by linarith [htb.2.2]
    have hcos_hi : Real.cos (0.9955 : ℝ) < (0.54410 : ℝ) := by linarith [htb.2.1]
    have hcos_pos : 0 < Real.cos (0.9955 : ℝ) := by linarith [htb.1]
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos_pos]
    linarith
  have hφ_lt : Real.arctan (1 / ((317 / 500 : ℝ) * Real.tan g)) < (0.9955 : ℝ) := by
    rw [← Real.arctan_tan (by linarith : -(Real.pi / 2) < (0.9955 : ℝ)) (by linarith : (0.9955 : ℝ) < Real.pi / 2)]
    exact Real.arctan_strictMono (lt_trans harg_lt htan_9955)
  -- Step 5: 4*18*(3α - π) + 24*(2π - 4α + 2φ - π) = 24*(5α + 2φ - 2π) < 12π
  linarith

/-! ## Negative test: corrupted certificate is rejected by the kernel verifier -/

private def tammes18BV8BadCert : BVCert8 :=
  { tammes18BV8Cert with F8 := [[-1]] }

theorem tammes18BV8BadCert_rejected : tammes18BV8BadCert.isValid = false := by
  decide

end Geodesy.Spherical
""")

    with open(out_path, "w") as f:
        f.write("\n".join(lines))
    print(f"Wrote {out_path} ({len(lines)} lines) in {time.time()-t0:.1f}s")

if __name__ == "__main__":
    main()
