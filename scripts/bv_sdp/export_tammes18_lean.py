"""
Generate LeanGeodesy/LeanGeodesy/Spherical/Tammes18.lean:
Certified degree-6 + Legendre P_1..P_12 Bachoc-Vallentin 3-point SDP bound
proving A(3, 313/500) <= 17 (Tammes T(18) < arccos(313/500) < 51.25 deg).
"""
import math
import time
from fractions import Fraction
import numpy as np
import cvxpy as cp
from scipy.linalg import qr

S_NUM = 313
S_DEN = 500
S_FRAC = Fraction(S_NUM, S_DEN)
S_FLOAT = S_NUM / S_DEN
D3 = 6
D2 = 12
DK = 10**9
DR = 10**9

def poly_mul(p, q):
    res = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(a + b for a, b in zip(m1, m2))
            res[m] = res.get(m, 0) + c1 * c2
    return {m: c for m, c in res.items() if c != 0}

def poly_add(p, q, scale=1):
    res = dict(p)
    for m, c in q.items():
        res[m] = res.get(m, 0) + scale * c
    return {m: c for m, c in res.items() if c != 0}

def canon(m):
    return tuple(sorted(m, reverse=True))

def sym3_exact(p):
    perms = [(0,1,2), (0,2,1), (1,0,2), (1,2,0), (2,0,1), (2,1,0)]
    res = {}
    for (a, b, c), val in p.items():
        for i, j, k in perms:
            m = ([a, b, c][i], [a, b, c][j], [a, b, c][k])
            res[m] = res.get(m, Fraction(0)) + val / 6
    return {m: c for m, c in res.items() if c != 0}

def sym3_canon_exact(p):
    sp = sym3_exact(p)
    return {m: c for m, c in sp.items() if m == canon(m)}

def build_Qk_exact(max_k):
    Q = [{(0, 0, 0): Fraction(1)}]
    if max_k >= 1:
        Q.append({(0, 0, 1): Fraction(1), (1, 1, 0): Fraction(-1)})
    two_t_uv = {(0, 0, 1): Fraction(2), (1, 1, 0): Fraction(-2)}
    prod_uv = {(0, 0, 0): Fraction(1), (2, 0, 0): Fraction(-1), (0, 2, 0): Fraction(-1), (2, 2, 0): Fraction(1)}
    for k in range(2, max_k + 1):
        p1 = poly_mul(two_t_uv, Q[k - 1])
        p2 = poly_mul(prod_uv, Q[k - 2])
        Q.append(poly_add(p1, p2, Fraction(-1)))
    return Q

def legendre_P_exact(max_k):
    P = [{(0,): Fraction(1)}]
    if max_k >= 1:
        P.append({(1,): Fraction(1)})
    for k in range(2, max_k + 1):
        p1 = poly_mul({(1,): Fraction(2*k - 1, k)}, P[k - 1])
        p2 = {m: Fraction(-(k - 1), k) * c for m, c in P[k - 2].items()}
        P.append(poly_add(p1, p2))
    return P

e1 = {(1,0,0): Fraction(1), (0,1,0): Fraction(1), (0,0,1): Fraction(1)}
e2 = {(1,1,0): Fraction(1), (1,0,1): Fraction(1), (0,1,1): Fraction(1)}
e3 = {(1,1,1): Fraction(1)}

def e_mon(a, b, c):
    res = {(0,0,0): Fraction(1)}
    for _ in range(a): res = poly_mul(res, e1)
    for _ in range(b): res = poly_mul(res, e2)
    for _ in range(c): res = poly_mul(res, e3)
    return res

def e_mons(max_deg):
    out = []
    for a in range(max_deg + 1):
        for b in range((max_deg - a) // 2 + 1):
            for c in range((max_deg - a - 2*b) // 3 + 1):
                out.append(e_mon(a, b, c))
    return out

def vt_mons(r):
    v_p_t = {(0,1,0): Fraction(1), (0,0,1): Fraction(1)}
    v_t = {(0,1,1): Fraction(1)}
    out = []
    for a in range(r + 1):
        for b in range(r - a + 1):
            for c in range((r - a - b) // 2 + 1):
                p = {(a, 0, 0): Fraction(1)}
                for _ in range(b): p = poly_mul(p, v_p_t)
                for _ in range(c): p = poly_mul(p, v_t)
                out.append(p)
    return out

def get_sos3_specs(d3, s_frac):
    u_m_v = {(1,0,0): Fraction(1), (0,1,0): Fraction(-1)}
    u2_m_v2 = {(2,0,0): Fraction(1), (0,2,0): Fraction(-1)}
    v_m_t = {(0,1,0): Fraction(1), (0,0,1): Fraction(-1)}
    disc = poly_mul(poly_mul(u_m_v, {(0,1,0): Fraction(1), (0,0,1): Fraction(-1)}), {(0,0,1): Fraction(1), (1,0,0): Fraction(-1)})

    Delta_poly = {(0,0,0): Fraction(1), (1,1,1): Fraction(2), (2,0,0): Fraction(-1), (0,2,0): Fraction(-1), (0,0,2): Fraction(-1)}
    g1_poly = {(0,0,0): s_frac, (1,0,0): s_frac - 1, (2,0,0): Fraction(-1)}
    g2_poly = {(0,0,0): s_frac**2, (0,1,0): -s_frac, (0,0,1): -s_frac, (0,1,1): Fraction(1)}

    specs = []
    for name, r, mult, is_sym in [
        ("one", d3, {(0,0,0): Fraction(1)}, True),
        ("delta", d3 - 2, Delta_poly, True),
        ("g1", d3 - 1, g1_poly, False),
        ("g2", d3 - 1, g2_poly, False),
    ]:
        if is_sym:
            b_triv = e_mons(r)
            b_std = [poly_mul(u_m_v, p) for p in e_mons(r - 1)] if r >= 1 else []
            b_std += [poly_mul(u2_m_v2, p) for p in e_mons(r - 2)] if r >= 2 else []
            b_sign = [poly_mul(disc, p) for p in e_mons(r - 3)] if r >= 3 else []
            for sub, b in [("triv", b_triv), ("std", b_std), ("sign", b_sign)]:
                if b:
                    specs.append((f"{name}_{sub}", mult, b))
        else:
            b_even = vt_mons(r)
            b_odd = [poly_mul(v_m_t, p) for p in vt_mons(r - 1)] if r >= 1 else []
            for sub, b in [("even", b_even), ("odd", b_odd)]:
                if b:
                    specs.append((f"{name}_{sub}", mult, b))
    return specs

def check_cholesky_dd(M_int, dM, dR=DR):
    """Find integer upper-triangular R such that dR^2 * M_int - dM * R^T R is diagonally dominant."""
    n = len(M_int)
    # Real matrix is M_int / dM
    M_f = np.array([[float(x) / float(dM) for x in row] for row in M_int], dtype=np.float64)
    eigs = np.linalg.eigvalsh(M_f)
    min_e = float(eigs[0])
    assert min_e > 0, f"Not PD: min_eig={min_e}"
    shift = min_e * 0.5
    L = np.linalg.cholesky(M_f - shift * np.eye(n))
    R_int = [[int(round(L.T[i, j] * dR)) for j in range(n)] for i in range(n)]
    # Exact integer DD check matching isCholeskyDDValid:
    # diag = dR^2 * M_int[i][i] - dM * sum_k R[k][i]^2
    dR2 = dR * dR
    for i in range(n):
        diag = dR2 * int(M_int[i][i]) - dM * sum(R_int[k][i] * R_int[k][i] for k in range(n))
        off = 0
        for j in range(n):
            if i == j: continue
            eij = dR2 * int(M_int[i][j]) - dM * sum(R_int[k][i] * R_int[k][j] for k in range(n))
            off += abs(eij)
        assert off <= diag, f"DD failed at row {i}: off={off} > diag={diag}"
    return R_int

def fmt_mat(M):
    return "[" + ", ".join("[" + ", ".join(str(int(x)) for x in row) + "]" for row in M) + "]"

def fmt_poly3(p_dict):
    # Sort lexicographically ascending by (a, b, c) matching tripleLt!
    items = sorted(((a, b, c, int(v)) for (a, b, c), v in p_dict.items() if v != 0), key=lambda x: (x[0], x[1], x[2]))
    return "[" + ", ".join(f"({a}, {b}, {c}, {v})" for a, b, c, v in items) + "]"

def fmt_basis(basis):
    return "[" + ",\n  ".join(fmt_poly3(p) for p in basis) + "]"

def sym3_canon_int(p_int_dict):
    """Exact integer sym3Canon matching Lean's sym3Canon (sums coeffs for sorted triple, no /6!)."""
    res = {}
    for (a, b, c), v in p_int_dict.items():
        if v == 0: continue
        cm = tuple(sorted((a, b, c), reverse=True))
        res[cm] = res.get(cm, 0) + int(v)
    return {m: v for m, v in res.items() if v != 0}

def main():
    t0 = time.time()
    Q = build_Qk_exact(D3)
    P = legendre_P_exact(D2)
    specs = get_sos3_specs(D3, S_FRAC)

    # 1. Solve interiority-maximized SDP
    F = [cp.Variable((D3 - k + 1, D3 - k + 1), PSD=True) for k in range(D3 + 1)]
    c2 = cp.Variable(D2, nonneg=True)
    deg1 = 2 * D3
    m0 = deg1 // 2 + 1
    m1 = (deg1 - 2) // 2 + 1
    S0 = cp.Variable((m0, m0), PSD=True)
    S1 = cp.Variable((m1, m1), PSD=True)
    M_sos = [cp.Variable((len(b), len(b)), PSD=True) for (_, _, b) in specs]
    eps = cp.Variable()

    constraints = [eps >= 0]
    for M in F + [S0, S1] + M_sos:
        constraints.append(M - eps * np.eye(M.shape[0]) >> 0)
    constraints.append(1.0 + cp.sum(F[0]) + cp.sum(c2) <= 17.99)

    G2_coeffs = [0] * (deg1 + 1)
    for i in range(D3 + 1):
        for j in range(D3 + 1):
            G2_coeffs[i] = G2_coeffs[i] + 2.0 * F[0][i, j]
    one_m_t2 = {(0,): Fraction(1), (2,): Fraction(-1)}
    pows = [{(0,): Fraction(1)}]
    for k in range(1, D3 + 1):
        pows.append(poly_mul(pows[-1], one_m_t2))
    for k in range(D3 + 1):
        sz = D3 - k + 1
        for i in range(sz):
            for j in range(sz):
                for (deg,), val in pows[k].items():
                    G2_coeffs[i + j + deg] = G2_coeffs[i + j + deg] + float(val) * F[k][i, j]
    for k in range(1, D2 + 1):
        for (deg,), val in P[k].items():
            G2_coeffs[deg] = G2_coeffs[deg] + float(val) * c2[k - 1]

    rhs2 = [0] * (deg1 + 1)
    for i in range(m0):
        for j in range(m0):
            rhs2[i + j] = rhs2[i + j] + S0[i, j]
    for i in range(m1):
        for j in range(m1):
            d = i + j
            rhs2[d] = rhs2[d] + S_FLOAT * S1[i, j]
            rhs2[d + 1] = rhs2[d + 1] + (S_FLOAT - 1.0) * S1[i, j]
            rhs2[d + 2] = rhs2[d + 2] - S1[i, j]
    for d in range(deg1 + 1):
        lhs = -1.0 - G2_coeffs[d] if d == 0 else -G2_coeffs[d]
        constraints.append(lhs == rhs2[d])

    G3_canon = {}
    for k in range(D3 + 1):
        sz = D3 - k + 1
        for i in range(sz):
            for j in range(i, sz):
                p = poly_mul({(i, j, 0): Fraction(1)}, Q[k])
                sc = sym3_canon_exact(p)
                mult = 1.0 if i == j else 2.0
                for cm, val in sc.items():
                    G3_canon[cm] = G3_canon.get(cm, 0) + F[k][i, j] * (mult * float(val))

    rhs3_canon = {}
    for (name, mult_poly, basis), M in zip(specs, M_sos):
        for i in range(len(basis)):
            for j in range(i, len(basis)):
                p = poly_mul(mult_poly, poly_mul(basis[i], basis[j]))
                sc = sym3_canon_exact(p)
                coeff = 1.0 if i == j else 2.0
                for cm, val in sc.items():
                    rhs3_canon[cm] = rhs3_canon.get(cm, 0) + M[i, j] * (coeff * float(val))

    all_mons = sorted(set(G3_canon.keys()) | set(rhs3_canon.keys()))
    for m in all_mons:
        constraints.append(-G3_canon.get(m, 0) == rhs3_canon.get(m, 0))

    prob = cp.Problem(cp.Maximize(eps), constraints)
    prob.solve(solver=cp.CLARABEL, verbose=False)
    print(f"Solved SDP in {time.time()-t0:.1f}s: status={prob.status}, eps={eps.value:.3e}")

    # 2. Round F, c2, S1 to DK
    F_int = []
    F_frac = []
    for k in range(D3 + 1):
        sz = D3 - k + 1
        Mi = [[int(round(F[k].value[i, j] * DK)) for j in range(sz)] for i in range(sz)]
        for i in range(sz):
            for j in range(i + 1, sz):
                Mi[j][i] = Mi[i][j]
        F_int.append(Mi)
        F_frac.append([[Fraction(x, DK) for x in row] for row in Mi])

    c2_int = [max(0, int(round(c2.value[k] * DK))) for k in range(D2)]
    c2_frac = [Fraction(x, DK) for x in c2_int]

    S1_int = [[int(round(S1.value[i, j] * DK)) for j in range(m1)] for i in range(m1)]
    for i in range(m1):
        for j in range(i + 1, m1):
            S1_int[j][i] = S1_int[i][j]
    S1_frac = [[Fraction(x, DK) for x in row] for row in S1_int]

    # Exact S0 adjustment
    G2_ex = [Fraction(0)] * (deg1 + 1)
    for i in range(D3 + 1):
        for j in range(D3 + 1):
            G2_ex[i] += 2 * F_frac[0][i][j]
    for k in range(D3 + 1):
        sz = D3 - k + 1
        for i in range(sz):
            for j in range(sz):
                for (deg,), val in pows[k].items():
                    G2_ex[i + j + deg] += val * F_frac[k][i][j]
    for k in range(1, D2 + 1):
        for (deg,), val in P[k].items():
            G2_ex[deg] += val * c2_frac[k - 1]

    S0_target = [(-Fraction(1) - G2_ex[0]) if d == 0 else -G2_ex[d] for d in range(deg1 + 1)]
    for i in range(m1):
        for j in range(m1):
            d = i + j
            S0_target[d] -= S_FRAC * S1_frac[i][j]
            S0_target[d + 1] -= (S_FRAC - 1) * S1_frac[i][j]
            S0_target[d + 2] += S1_frac[i][j]

    S0_frac = [[Fraction(int(round(S0.value[i, j] * DK)), DK) for j in range(m0)] for i in range(m0)]
    for i in range(m0):
        for j in range(i + 1, m0):
            S0_frac[j][i] = S0_frac[i][j]
    for d in range(deg1 + 1):
        cur = sum(S0_frac[i][d - i] for i in range(m0) if 0 <= d - i < m0)
        diff = S0_target[d] - cur
        pairs = [(i, d - i) for i in range(m0) if 0 <= d - i < m0]
        delta = diff / len(pairs)
        for (i, j) in pairs:
            S0_frac[i][j] += delta
    dS0 = math.lcm(*(x.denominator for row in S0_frac for x in row))
    S0_int = [[int(x * dS0) for x in row] for row in S0_frac]

    # 3. Exact 3D residual elimination
    G3_ex = {}
    for k in range(D3 + 1):
        sz = D3 - k + 1
        for i in range(sz):
            for j in range(sz):
                if F_frac[k][i][j] == 0: continue
                p = poly_mul({(i, j, 0): Fraction(1)}, Q[k])
                sc = sym3_canon_exact(p)
                for cm, val in sc.items():
                    G3_ex[cm] = G3_ex.get(cm, Fraction(0)) + F_frac[k][i][j] * val

    M_frac = []
    for (_, _, b), M in zip(specs, M_sos):
        sz = len(b)
        Mf = [[Fraction(int(round(M.value[i, j] * DK)), DK) for j in range(sz)] for i in range(sz)]
        for i in range(sz):
            for j in range(i + 1, sz):
                Mf[j][i] = Mf[i][j]
        M_frac.append(Mf)

    rhs3_ex = {}
    for (name, mult_poly, basis), Mf in zip(specs, M_frac):
        sz = len(basis)
        for i in range(sz):
            for j in range(i, sz):
                if Mf[i][j] == 0: continue
                p = poly_mul(mult_poly, poly_mul(basis[i], basis[j]))
                sc = sym3_canon_exact(p)
                mult = 1 if i == j else 2
                for cm, val in sc.items():
                    rhs3_ex[cm] = rhs3_ex.get(cm, Fraction(0)) + Mf[i][j] * mult * val

    res_vec = [-G3_ex.get(m, Fraction(0)) - rhs3_ex.get(m, Fraction(0)) for m in all_mons]
    mon_idx = {m: idx for idx, m in enumerate(all_mons)}
    cols = []
    col_info = []
    for b_idx, (name, mult_poly, basis) in enumerate(specs):
        sz = len(basis)
        for i in range(sz):
            for j in range(i, sz):
                p = poly_mul(mult_poly, poly_mul(basis[i], basis[j]))
                sc = sym3_canon_exact(p)
                mult = Fraction(1 if i == j else 2)
                col = {mon_idx[cm]: val * mult for cm, val in sc.items() if cm in mon_idx}
                if col:
                    cols.append(col)
                    col_info.append((b_idx, i, j))

    n_rows = len(all_mons)
    A_f = np.zeros((n_rows, len(cols)), dtype=np.float64)
    for c_idx, col in enumerate(cols):
        for r_idx, val in col.items():
            A_f[r_idx, c_idx] = float(val)
    _, R_qr, piv = qr(A_f, pivoting=True)
    piv_cols = list(piv[:n_rows])
    Aug = [[cols[c].get(r, Fraction(0)) for c in piv_cols] + [res_vec[r]] for r in range(n_rows)]
    for col_i in range(n_rows):
        piv_r = next(r for r in range(col_i, n_rows) if Aug[r][col_i] != 0)
        Aug[col_i], Aug[piv_r] = Aug[piv_r], Aug[col_i]
        pv = Aug[col_i][col_i]
        for j in range(col_i, n_rows + 1):
            Aug[col_i][j] /= pv
        for r in range(n_rows):
            if r != col_i and Aug[r][col_i] != 0:
                fac = Aug[r][col_i]
                for j in range(col_i, n_rows + 1):
                    Aug[r][j] -= fac * Aug[col_i][j]
    for k_i, c_idx in enumerate(piv_cols):
        b_idx, i, j = col_info[c_idx]
        M_frac[b_idx][i][j] += Aug[k_i][n_rows]
        if i != j:
            M_frac[b_idx][j][i] += Aug[k_i][n_rows]

    dS = math.lcm(*(x.denominator for Mf in M_frac for row in Mf for x in row))
    M_int = [[[int(x * dS) for x in row] for row in Mf] for Mf in M_frac]

    # 4. Compute and verify all 19 exact Cholesky+DD witnesses
    R_F = [check_cholesky_dd(F_int[k], DK, DR) for k in range(D3 + 1)]
    R_S0 = check_cholesky_dd(S0_int, dS0, DR)
    R_S1 = check_cholesky_dd(S1_int, DK, DR)
    R_M = [check_cholesky_dd(M_int[idx], dS, DR) for idx in range(10)]
    print(f"All 19 exact Cholesky+DD witnesses verified! dS0={dS0}, dS digits={len(str(dS))}")

    # 5. Precompute exact sym3Canon outputs for each of the 10 SOS blocks (matching Lean's polyRHS3Canon)
    polyDelta_int = {(0,0,0): 1, (0,0,2): -1, (0,2,0): -1, (1,1,1): 2, (2,0,0): -1}
    polyG1_int = {(0,0,0): S_NUM, (1,0,0): S_NUM - S_DEN, (2,0,0): -S_DEN}
    polyG2_int = {(0,0,0): S_NUM*S_NUM, (0,0,1): -S_NUM*S_DEN, (0,1,0): -S_NUM*S_DEN, (0,1,1): S_DEN*S_DEN}
    block_mults = [None, None, None, polyDelta_int, polyDelta_int, polyDelta_int, polyG1_int, polyG1_int, polyG2_int, polyG2_int]

    q_canon_vals = []
    for idx, ((name, _, basis), Mi, mult_int) in enumerate(zip(specs, M_int, block_mults)):
        sz = len(basis)
        b_int = [{m: int(v) for m, v in p.items()} for p in basis]
        q_poly = {}
        for i in range(sz):
            qi = {}
            for j in range(sz):
                val = Mi[i][j]
                if val == 0: continue
                for m, c in b_int[j].items():
                    qi[m] = qi.get(m, 0) + val * c
            qi = {m: c for m, c in qi.items() if c != 0}
            prod = poly_mul(b_int[i], qi)
            for m, c in prod.items():
                q_poly[m] = q_poly.get(m, 0) + c
        q_poly = {m: c for m, c in q_poly.items() if c != 0}
        if mult_int is not None:
            q_poly = poly_mul(mult_int, q_poly)
        q_canon_vals.append(sym3_canon_int(q_poly))

    # Sanity check: compare total sym3Canon RHS vs LHS in exact integers
    sD2 = S_DEN * S_DEN
    total_rhs = {}
    scales = [sD2, sD2, sD2, sD2, sD2, sD2, S_DEN, S_DEN, 1, 1]
    for sc, qc in zip(scales, q_canon_vals):
        for m, v in qc.items():
            total_rhs[m] = total_rhs.get(m, 0) + DK * sc * v
    total_rhs = {m: v for m, v in total_rhs.items() if v != 0}

    total_lhs = {}
    for k in range(D3 + 1):
        sz = D3 - k + 1
        qk_int = {m: int(v) for m, v in Q[k].items()}
        for i in range(sz):
            for j in range(sz):
                v = F_int[k][i][j]
                if v == 0: continue
                for (a, b, d), w in qk_int.items():
                    cm = tuple(sorted((a + i, b + j, d), reverse=True))
                    total_lhs[cm] = total_lhs.get(cm, 0) - sD2 * dS * v * w
    total_lhs = {m: v for m, v in total_lhs.items() if v != 0}
    assert total_lhs == total_rhs, "Exact integer LHS != RHS!"
    print("EXACT INTEGER LEAN IDENTITY MATCH VERIFIED!")

    # 6. Write LeanGeodesy/LeanGeodesy/Spherical/Tammes18.lean
    out_path = "LeanGeodesy/LeanGeodesy/Spherical/Tammes18.lean"
    lines = []
    lines.append("""import LeanGeodesy.Spherical.BachocVallentinCert6
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Certified New Upper Bound for Tammes `N = 18` on `S²`

We prove unconditionally in the Lean 4 kernel that no spherical code of size `18`
on `S²` can have maximum pairwise inner product `≤ 313 / 500 = 0.626`, i.e.,

```
A(3, 313/500) ≤ 17
```

Equivalently, every `18`-point configuration on `S²` has minimum geodesic separation
strictly less than `arccos (313 / 500) ≈ 51.24438° < 51.25°`.

This strictly improves:
- L. Fejes Tóth (1943): `≤ 51.69012°` (currently listed on `leapsinbounds.org/constants/tammes-18/`),
- Monotonicity from Bachoc–Vallentin (2008) Table 5.3 (`T(17) ≤ 51.69°`), and
- The infinite-degree Delsarte two-point LP limit (`≈ 51.2827°`, where `LP(∞)` at
  `s = 313 / 500` is `≈ 18.0269 > 18`).

The proof uses a degree-6 Bachoc–Vallentin three-point SDP certificate combined with
two-point Legendre terms `P₁..P₁₂`, checked purely by `decide` in the Lean 4 kernel
(no `native_decide`, no `sorry`, no custom axioms).
-/

namespace Geodesy.Spherical

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
""")
    # Emit matrices and bases as separate typed defs for instant elaboration
    for k in range(7):
        lines.append(f"private def t18_F{k}_val : List (List ℤ) := {fmt_mat(F_int[k])}")
        lines.append(f"private def t18_RF{k}_val : List (List ℤ) := {fmt_mat(R_F[k])}")
    lines.append(f"private def t18_S0_val : List (List ℤ) := {fmt_mat(S0_int)}")
    lines.append(f"private def t18_RS0_val : List (List ℤ) := {fmt_mat(R_S0)}")
    lines.append(f"private def t18_S1_val : List (List ℤ) := {fmt_mat(S1_int)}")
    lines.append(f"private def t18_RS1_val : List (List ℤ) := {fmt_mat(R_S1)}")
    for idx in range(10):
        basis_int = [{m: int(v) for m, v in p.items()} for p in specs[idx][2]]
        lines.append(f"private def t18_M{idx}_val : List (List ℤ) := {fmt_mat(M_int[idx])}")
        lines.append(f"private def t18_RM{idx}_val : List (List ℤ) := {fmt_mat(R_M[idx])}")
        lines.append(f"private def t18_b{idx}_val : List Poly3 := {fmt_basis(basis_int)}")

    lines.append("""
/-- Certified rational degree-6 + Legendre `P₁..P₁₂` Bachoc–Vallentin SDP certificate
at `s = 313 / 500` (`51.24438°`), giving upper bound `17989990959 / 10⁹ < 18`. -/
def tammes18Cert : BVCert6 where
  sNum := 313
  sDen := 500""")
    lines.append(f"  dK := {DK}")
    lines.append(f"  dS0 := {dS0}")
    lines.append(f"  dS := {dS}")
    lines.append(f"  dR := {DR}")
    for k in range(7):
        lines.append(f"  F{k} := t18_F{k}_val")
        lines.append(f"  R_F{k} := t18_RF{k}_val")
    lines.append(f"  c2 := [{', '.join(str(x) for x in c2_int)}]")
    lines.append("  S0 := t18_S0_val")
    lines.append("  R_S0 := t18_RS0_val")
    lines.append("  S1 := t18_S1_val")
    lines.append("  R_S1 := t18_RS1_val")
    for idx in range(10):
        lines.append(f"  m{idx} := {len(specs[idx][2])}")
        lines.append(f"  M{idx} := t18_M{idx}_val")
        lines.append(f"  R{idx} := t18_RM{idx}_val")
        lines.append(f"  b{idx} := t18_b{idx}_val")

    lines.append("")
    # 19 independent PSD checks + basic checks
    lines.append("private theorem t18_basic : decide (0 < tammes18Cert.sDen) = true ∧ decide (0 < tammes18Cert.dK) = true ∧")
    lines.append("    decide (0 < tammes18Cert.dS0) = true ∧ decide (0 < tammes18Cert.dS) = true ∧")
    lines.append("    decide (0 < tammes18Cert.dR) = true ∧ decide (-(tammes18Cert.sDen : ℤ) < tammes18Cert.sNum) = true ∧")
    lines.append("    ((List.range 12).all fun k => decide (0 ≤ tammes18Cert.c2.getD k 0)) = true := by decide")
    for k in range(7):
        lines.append(f"private theorem t18_F{k} : isCholeskyDDValid {7-k} tammes18Cert.dK tammes18Cert.dR tammes18Cert.F{k} tammes18Cert.R_F{k} = true := by decide")
    lines.append("private theorem t18_S0 : isCholeskyDDValid 7 tammes18Cert.dS0 tammes18Cert.dR tammes18Cert.S0 tammes18Cert.R_S0 = true := by decide")
    lines.append("private theorem t18_S1 : isCholeskyDDValid 6 tammes18Cert.dK tammes18Cert.dR tammes18Cert.S1 tammes18Cert.R_S1 = true := by decide")
    for idx in range(10):
        lines.append(f"private theorem t18_M{idx} : isCholeskyDDValid tammes18Cert.m{idx} tammes18Cert.dS tammes18Cert.dR tammes18Cert.M{idx} tammes18Cert.R{idx} = true := by decide")
    lines.append("private theorem t18_eq2 : tammes18Cert.checkEq2 = true := by decide")

    # 10 split trivariate block canonicalization theorems!
    for idx in range(10):
        q_lit = fmt_poly3(q_canon_vals[idx])
        if idx < 3:
            lhs_expr = f"sym3Canon (quadPoly3 tammes18Cert.m{idx} tammes18Cert.M{idx} tammes18Cert.b{idx})"
        elif idx < 6:
            lhs_expr = f"sym3Canon (mulPoly3Sorted BVCert6.polyDelta6 (quadPoly3 tammes18Cert.m{idx} tammes18Cert.M{idx} tammes18Cert.b{idx}))"
        elif idx < 8:
            lhs_expr = f"sym3Canon (mulPoly3Sorted (BVCert6.polyG1_6 tammes18Cert.sNum tammes18Cert.sDen) (quadPoly3 tammes18Cert.m{idx} tammes18Cert.M{idx} tammes18Cert.b{idx}))"
        else:
            lhs_expr = f"sym3Canon (mulPoly3Sorted (BVCert6.polyG2_6 tammes18Cert.sNum tammes18Cert.sDen) (quadPoly3 tammes18Cert.m{idx} tammes18Cert.M{idx} tammes18Cert.b{idx}))"
        lines.append(f"\nset_option maxHeartbeats 800000 in\nprivate theorem t18_q{idx} :\n    {lhs_expr} =\n    {q_lit} := by decide")

    lines.append("""
private theorem t18_eq3 :
    (sym3Canon (poly3Scale (-((tammes18Cert.sDen : ℤ) * (tammes18Cert.sDen : ℤ) * (tammes18Cert.dS : ℤ))) tammes18Cert.polyG3) ==
      sym3Canon (poly3Scale (tammes18Cert.dK : ℤ) tammes18Cert.polyRHS3Canon)) = true := by
  unfold BVCert6.polyRHS3Canon
  dsimp only
  rw [t18_q0, t18_q1, t18_q2, t18_q3, t18_q4, t18_q5, t18_q6, t18_q7, t18_q8, t18_q9]
  decide

/-- Kernel-verified validity of `tammes18Cert` (no `native_decide`, no extra axioms). -/
theorem tammes18Cert_valid : tammes18Cert.isValid = true := by
  unfold BVCert6.isValid
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := t18_basic
  rw [h1, h2, h3, h4, h5, h6, h7,
    t18_F0, t18_F1, t18_F2, t18_F3, t18_F4, t18_F5, t18_F6,
    t18_S0, t18_S1,
    t18_M0, t18_M1, t18_M2, t18_M3, t18_M4, t18_M5, t18_M6, t18_M7, t18_M8, t18_M9,
    t18_eq2, t18_eq3]
  rfl

private theorem tammes18Cert_bound_lt_18 : tammes18Cert.bound < 18 := by
  have hnum : tammes18Cert.boundNum < 18 * (tammes18Cert.dK : ℤ) := by decide
  have hdK : (0 : ℝ) < (tammes18Cert.dK : ℝ) := by norm_num [tammes18Cert]
  rw [BVCert6.bound, div_lt_iff₀ hdK]
  have hnumR : (tammes18Cert.boundNum : ℝ) < 18 * (tammes18Cert.dK : ℝ) := by exact_mod_cast hnum
  linarith

/-- **New certified spherical-code upper bound on `S²`**:
every `(n, 313 / 500)`-spherical code on `S²` has at most `17` points (`A(3, 313/500) ≤ 17`). -/
theorem sphericalCode_three_upper_313_500 {n : ℕ} {p : Fin n → UnitSphere}
    (hp : IsSphericalCode p (313 / 500 : ℝ)) : n ≤ 17 := by
  have hs : tammes18Cert.s = (313 / 500 : ℝ) := by norm_num [BVCert6.s, tammes18Cert]
  have hle : (n : ℝ) ≤ tammes18Cert.bound := tammes18Cert.sound tammes18Cert_valid (hs ▸ hp)
  have hlt : (n : ℝ) < 18 := lt_of_le_of_lt hle tammes18Cert_bound_lt_18
  have hnat : n < 18 := by exact_mod_cast hlt
  omega

/-- **New certified Tammes `N = 18` strict upper bound**:
every `18`-point configuration on `S²` with minimum separation `θ` satisfies
`θ < arccos (313 / 500) ≈ 51.24438°`. -/
theorem tammes_18_strict_upper {p : Fin 18 → UnitSphere} {θ : ℝ}
    (hp : IsSeparated p θ) : θ < Real.arccos (313 / 500 : ℝ) := by
  by_contra h
  push Not at h
  have hsep : IsSeparated p (Real.arccos (313 / 500 : ℝ)) := fun i j hij => le_trans h (hp i j hij)
  have hcode : IsSphericalCode p (313 / 500 : ℝ) := by
    have h0 : (0 : ℝ) ≤ Real.arccos (313 / 500 : ℝ) := Real.arccos_nonneg _
    have hpi : Real.arccos (313 / 500 : ℝ) ≤ Real.pi := Real.arccos_le_pi _
    have hc : Real.cos (Real.arccos (313 / 500 : ℝ)) = (313 / 500 : ℝ) :=
      Real.cos_arccos (by norm_num) (by norm_num)
    rw [← hc]
    exact (isSeparated_iff_isSphericalCode p h0 hpi).mp hsep
  have hle := sphericalCode_three_upper_313_500 hcode
  omega

/-- Equivalent non-existence statement: no `18`-point configuration on `S²` is
`θ`-separated for `θ ≥ arccos (313 / 500)`. -/
theorem tammes_18_not_isSeparated {p : Fin 18 → UnitSphere} {θ : ℝ}
    (hθ : Real.arccos (313 / 500 : ℝ) ≤ θ) : ¬ IsSeparated p θ :=
  fun hp => not_lt_of_ge hθ (tammes_18_strict_upper hp)

/-! ## Certified angle comparison: `arccos (313 / 500) < 51.25°` -/

private theorem cos_taylor8_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  -- Elementary repeated integration of `cos t ≤ 1` on `[0, x]` via MVT:
  -- f_0(t) = 1 - cos t ≥ 0
  -- f_1(t) = t - sin t ≥ 0
  -- f_2(t) = cos t - 1 + t^2/2 ≥ 0
  -- f_3(t) = sin t - t + t^3/6 ≥ 0
  -- f_4(t) = 1 - t^2/2 + t^4/24 - cos t ≥ 0
  -- f_5(t) = t - t^3/6 + t^5/120 - sin t ≥ 0
  -- f_6(t) = cos t - (1 - t^2/2 + t^4/24 - t^6/720) ≥ 0
  -- f_7(t) = sin t - (t - t^3/6 + t^5/120 - t^7/5040) ≥ 0
  -- f_8(t) = (1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320) - cos t ≥ 0
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
        have heq : Real.cos t - 1 + (3 : ℝ) * t ^ (3 - 1) / 6 = Real.cos t - 1 + t ^ 2 / 2 := by
          norm_num; ring
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
            (6 : ℝ) * t ^ (6 - 1) / 720) = t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t := by
          norm_num; ring
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
  linarith [h8 x hx]

/-- Rigorous degree bound: `arccos (313 / 500) < 51.25°` (strictly below Fejes Tóth 1943's
`51.69012°`, Bachoc–Vallentin 2008's `T(17) ≤ 51.69°`, and Delsarte 2-point LP's `51.2827°`). -/
theorem arccos_313_500_lt_deg :
    Real.arccos (313 / 500 : ℝ) < (51.25 : ℝ) * (Real.pi / 180) := by
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  set x : ℝ := (51.25 : ℝ) * (Real.pi / 180)
  have hx_lo : (0.894481 : ℝ) < x := by
    dsimp only [x]; linarith
  have hx_hi : x < (0.894482 : ℝ) := by
    dsimp only [x]; linarith
  have hx_nonneg : 0 ≤ x := by linarith
  have hx_le_pi : x ≤ Real.pi := by linarith
  have hcos_lt : Real.cos x < (313 / 500 : ℝ) := by
    have ht := cos_taylor8_upper hx_nonneg
    have hx2_lo : (0.894481 : ℝ) ^ 2 < x ^ 2 := pow_lt_pow_left₀ hx_lo (by norm_num) (by norm_num)
    have hx4_hi : x ^ 4 < (0.894482 : ℝ) ^ 4 := pow_lt_pow_left₀ hx_hi hx_nonneg (by norm_num)
    have hx6_lo : (0.894481 : ℝ) ^ 6 < x ^ 6 := pow_lt_pow_left₀ hx_lo (by norm_num) (by norm_num)
    have hx8_hi : x ^ 8 < (0.894482 : ℝ) ^ 8 := pow_lt_pow_left₀ hx_hi hx_nonneg (by norm_num)
    linarith
  have hcos_arccos : Real.cos (Real.arccos (313 / 500 : ℝ)) = (313 / 500 : ℝ) :=
    Real.cos_arccos (by norm_num) (by norm_num)
  by_contra h
  push Not at h
  have hanti : Real.cos (Real.arccos (313 / 500 : ℝ)) ≤ Real.cos x :=
    Real.strictAntiOn_cos.antitoneOn
      ⟨hx_nonneg, hx_le_pi⟩ ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩ h
  linarith

/-- Combined Tammes `N = 18` degree bound: every `18`-point configuration on `S²` has
minimum geodesic separation strictly less than `51.25°`. -/
theorem tammes_18_lt_51_25_deg {p : Fin 18 → UnitSphere} {θ : ℝ}
    (hp : IsSeparated p θ) : θ < (51.25 : ℝ) * (Real.pi / 180) :=
  lt_trans (tammes_18_strict_upper hp) arccos_313_500_lt_deg

/-! ## Negative test: corrupted certificate is rejected by the kernel verifier -/

private def tammes18BadCert : BVCert6 :=
  { tammes18Cert with F6 := [[-1]] }

theorem tammes18BadCert_rejected : tammes18BadCert.isValid = false := by
  decide

end Geodesy.Spherical
""")

    with open(out_path, "w") as f:
        f.write("\n".join(lines))
    print(f"Wrote {out_path} ({len(lines)} lines) in {time.time()-t0:.1f}s")

if __name__ == "__main__":
    main()
