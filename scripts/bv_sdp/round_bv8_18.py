"""
Exact rational BV(8, 16) certificate builder & verifier in Python for:
  N = 18, s = 317/500 = 0.634 (arccos(317/500) ≈ 50.65415 deg < Robinson 50.68095 deg)

Uses the mathematically reduced 7-block trivariate SOS structure:
  one_triv(41), one_std(54), one_sign(16),
  delta_triv(23), delta_std(27), delta_sign(7),
  g1_even(70)
(All of g2 and g1_odd eliminated: 10 blocks -> 7 blocks, sum_sq 20960 -> 11060,
 no s^2 = 500^2 denominator in trivariate SOS!)

Verifies in EXACT arbitrary-precision Python integer/Fraction arithmetic:
  1. Exact univariate degree-16 identity: zero residual
  2. Exact trivariate S3-canonicalized degree-16 identity (204 monomials): zero residual
  3. Exact Cholesky + symmetric diagonal dominance (dR^2 * M - dM * R^T R SDD) for ALL 18 matrices
  4. Exact rational objective bound < 18
"""
import math
import time
from fractions import Fraction
import numpy as np
import cvxpy as cp
from scipy.linalg import qr

S_NUM = 317
S_DEN = 500
S_FRAC = Fraction(S_NUM, S_DEN)
S_FLOAT = S_NUM / S_DEN
D3 = 8
D2 = 16

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

def chebyshev_T_exact(max_k):
    T = [{(0,): Fraction(1)}]
    if max_k >= 1:
        T.append({(1,): Fraction(1)})
    for k in range(2, max_k + 1):
        p1 = poly_mul({(1,): Fraction(2)}, T[k - 1])
        p2 = {m: -c for m, c in T[k - 2].items()}
        T.append(poly_add(p1, p2))
    return T

def embed_var(p1, axis):
    out = {}
    for (d,), c in p1.items():
        m = [0, 0, 0]
        m[axis] = d
        out[tuple(m)] = c
    return out

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

def build_sos_specs():
    u_m_v = {(1,0,0): Fraction(1), (0,1,0): Fraction(-1)}
    u2_m_v2 = {(2,0,0): Fraction(1), (0,2,0): Fraction(-1)}
    disc = poly_mul(poly_mul(u_m_v, {(0,1,0): Fraction(1), (0,0,1): Fraction(-1)}),
                    {(0,0,1): Fraction(1), (1,0,0): Fraction(-1)})
    Delta = {(0,0,0): Fraction(1), (1,1,1): Fraction(2), (2,0,0): Fraction(-1),
             (0,2,0): Fraction(-1), (0,0,2): Fraction(-1)}
    g1 = {(0,0,0): S_FRAC, (1,0,0): S_FRAC - 1, (2,0,0): Fraction(-1)}

    specs = [
        ("one_triv", {(0,0,0): Fraction(1)}, e_mons(8)),
        ("one_std", {(0,0,0): Fraction(1)},
         [poly_mul(u_m_v, p) for p in e_mons(7)] + [poly_mul(u2_m_v2, p) for p in e_mons(6)]),
        ("one_sign", {(0,0,0): Fraction(1)}, [poly_mul(disc, p) for p in e_mons(5)]),
        ("delta_triv", Delta, e_mons(6)),
        ("delta_std", Delta,
         [poly_mul(u_m_v, p) for p in e_mons(5)] + [poly_mul(u2_m_v2, p) for p in e_mons(4)]),
        ("delta_sign", Delta, [poly_mul(disc, p) for p in e_mons(3)]),
        ("g1_even", g1, vt_mons(7)),
    ]
    return specs

def exact_cholesky_dd(M_int, dM, dR):
    """Find integer upper-triangular R such that dR^2 * M_int - dM * R^T R is symmetric diagonally dominant."""
    m = len(M_int)
    M_flt = np.array([[float(x) / float(dM) for x in row] for row in M_int], dtype=np.float64)
    ev = np.linalg.eigvalsh(M_flt)
    if ev[0] <= 0:
        return None, ev[0], -1.0
    # Subtract tiny margin from diagonal so R^T R < M, leaving strictly positive diagonal in E = M - R^T R
    # Actually Cholesky of (M - delta * I) where delta = 0.5 * ev[0]
    delta = 0.5 * ev[0]
    try:
        L = np.linalg.cholesky(M_flt - delta * np.eye(m))
    except np.linalg.LinAlgError:
        return None, ev[0], -1.0
    R_flt = L.T
    R_int = [[0] * m for _ in range(m)]
    for i in range(m):
        for j in range(i, m):
            R_int[i][j] = int(round(R_flt[i, j] * dR))
    # Exact integer check of E = dR^2 * M_int - dM * R^T R
    dR2 = dR * dR
    min_margin = None
    for i in range(m):
        diag_val = dR2 * M_int[i][i] - dM * sum(R_int[k][i] * R_int[k][i] for k in range(i + 1))
        off_sum = 0
        for j in range(m):
            if i == j:
                continue
            lim = min(i, j) + 1
            e_ij = dR2 * M_int[i][j] - dM * sum(R_int[k][i] * R_int[k][j] for k in range(lim))
            off_sum += abs(e_ij)
        margin = diag_val - off_sum
        if min_margin is None or margin < min_margin:
            min_margin = margin
    return R_int, ev[0], min_margin

def solve_exact_fraction_system(A_frac, b_frac):
    """Gaussian elimination over Fraction for n x n invertible system."""
    n = len(b_frac)
    M = [list(A_frac[i]) + [b_frac[i]] for i in range(n)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if M[r][col] != 0:
                piv = r
                break
        if piv is None:
            raise ValueError(f"Singular pivot at col {col}")
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        row_c = M[col]
        for j in range(col, n + 1):
            row_c[j] /= pv
        for r in range(n):
            if r == col:
                continue
            f = M[r][col]
            if f != 0:
                row_r = M[r]
                for j in range(col, n + 1):
                    row_r[j] -= f * row_c[j]
    return [M[i][n] for i in range(n)]

def main():
    t0 = time.time()
    print("=== Phase 1: Solve interiority-maximized reduced 7-block BV(8, 16) ===", flush=True)
    Q = build_Qk_exact(D3)
    P = legendre_P_exact(D2)
    T = chebyshev_T_exact(D3 + 1)
    specs = build_sos_specs()

    F = [cp.Variable((D3 - k + 1, D3 - k + 1), PSD=True) for k in range(D3 + 1)]
    c2 = cp.Variable(D2, nonneg=True)

    G3_canon = {}
    def add_G3(p, expr):
        for m, v in sym3_canon_exact(p).items():
            G3_canon[m] = G3_canon.get(m, 0) + expr * float(v)

    for k in range(D3 + 1):
        sz = D3 - k + 1
        for i in range(sz):
            Ti_u = embed_var(T[i], 0)
            for j in range(i, sz):
                Tj_v = embed_var(T[j], 1)
                p = poly_mul(poly_mul(Ti_u, Tj_v), Q[k])
                coeff = 1.0 if i == j else 2.0
                add_G3(p, F[k][i, j] * coeff)

    deg1 = 2 * D3
    G2_coeffs = [0] * (deg1 + 1)
    for i in range(D3 + 1):
        for j in range(D3 + 1):
            for (d,), val in T[i].items():
                G2_coeffs[d] = G2_coeffs[d] + 2.0 * float(val) * F[0][i, j]
    one_m_t2 = {(0,): Fraction(1), (2,): Fraction(-1)}
    pows = [{(0,): Fraction(1)}]
    for k in range(1, D3 + 1):
        pows.append(poly_mul(pows[-1], one_m_t2))
    for k in range(D3 + 1):
        sz = D3 - k + 1
        for i in range(sz):
            for j in range(sz):
                prod_ij = poly_mul(poly_mul(T[i], T[j]), pows[k])
                for (d,), val in prod_ij.items():
                    G2_coeffs[d] = G2_coeffs[d] + float(val) * F[k][i, j]
    for k in range(1, D2 + 1):
        for (d,), val in P[k].items():
            G2_coeffs[d] = G2_coeffs[d] + float(val) * c2[k - 1]

    m0 = D3 + 1  # 9
    m1 = D3      # 8
    S0 = cp.Variable((m0, m0), PSD=True)
    S1 = cp.Variable((m1, m1), PSD=True)
    rhs2 = [0] * (deg1 + 1)
    for i in range(m0):
        for j in range(m0):
            for (d,), val in poly_mul(T[i], T[j]).items():
                rhs2[d] = rhs2[d] + float(val) * S0[i, j]
    mult_s = {(0,): S_FRAC, (1,): S_FRAC - 1, (2,): Fraction(-1)}
    for i in range(m1):
        for j in range(m1):
            for (d,), val in poly_mul(mult_s, poly_mul(T[i], T[j])).items():
                rhs2[d] = rhs2[d] + float(val) * S1[i, j]

    constraints = []
    for d in range(deg1 + 1):
        lhs = -1.0 - G2_coeffs[d] if d == 0 else -G2_coeffs[d]
        constraints.append(lhs == rhs2[d])

    rhs3_canon = {}
    M_vars = []
    # Precompute exact sym3_canon for every (block, i, j)
    print("  Precomputing exact trivariate basis products...", flush=True)
    spec_prods = []
    for bname, mult, basis in specs:
        d = len(basis)
        M = cp.Variable((d, d), PSD=True)
        M_vars.append(M)
        prods = {}
        for i in range(d):
            for j in range(i, d):
                sc = sym3_canon_exact(poly_mul(mult, poly_mul(basis[i], basis[j])))
                coeff = 1 if i == j else 2
                sc_scaled = {m: v * coeff for m, v in sc.items()}
                prods[(i, j)] = sc_scaled
                for m, v in sc_scaled.items():
                    rhs3_canon[m] = rhs3_canon.get(m, 0) + M[i, j] * float(v)
        spec_prods.append(prods)

    all_mons = sorted(set(G3_canon.keys()) | set(rhs3_canon.keys()))
    print(f"  Trivariate canonical monomials: {len(all_mons)}, SOS dims: {[len(s[2]) for s in specs]}", flush=True)
    for m in all_mons:
        constraints.append(-G3_canon.get(m, 0) == rhs3_canon.get(m, 0))

    obj_expr = 1.0 + cp.sum(F[0]) + cp.sum(c2)
    eps = cp.Variable()
    constraints.append(obj_expr <= 17.98)
    constraints.append(eps >= 0)
    all_psd = F + [S0, S1] + M_vars
    for M in all_psd:
        constraints.append(M - eps * np.eye(M.shape[0]) >> 0)
    constraints.append(c2 >= eps)

    prob = cp.Problem(cp.Maximize(eps), constraints)
    prob.solve(solver=cp.CLARABEL, verbose=False, max_iter=500, tol_feas=1e-10, tol_gap_abs=1e-10, tol_gap_rel=1e-10)
    print(f"  Clarabel done in {time.time()-t0:.1f}s: status={prob.status}, bound={float(obj_expr.value):.6f}, eps={float(eps.value):.3e}", flush=True)
    for idx, M in enumerate(all_psd):
        ev = np.linalg.eigvalsh(M.value)
        print(f"    block {idx:2d} (dim {M.shape[0]:2d}): min_eig={ev[0]:+.3e}, max_eig={ev[-1]:.3e}", flush=True)

    # === Phase 2: Exact rational rounding ===
    print("\n=== Phase 2: Exact rational rounding ===", flush=True)
    dK = 10**9
    F_int = []
    for k in range(D3 + 1):
        Fk = F[k].value
        sz = D3 - k + 1
        Fi = [[0] * sz for _ in range(sz)]
        for i in range(sz):
            for j in range(i, sz):
                v = int(round(0.5 * (Fk[i, j] + Fk[j, i]) * dK))
                Fi[i][j] = v
                Fi[j][i] = v
        F_int.append(Fi)
    c2_int = [max(0, int(round(float(c2.value[k]) * dK))) for k in range(D2)]
    S1_val = S1.value
    S1_int = [[0] * m1 for _ in range(m1)]
    for i in range(m1):
        for j in range(i, m1):
            v = int(round(0.5 * (S1_val[i, j] + S1_val[j, i]) * dK))
            S1_int[i][j] = v
            S1_int[j][i] = v

    bound_num = dK + sum(sum(row) for row in F_int[0]) + sum(c2_int)
    print(f"  Exact rational bound = {bound_num} / {dK} = {bound_num / dK:.9f} (< 18: {bound_num < 18 * dK})", flush=True)

    # Exact univariate RHS for S0: -1 - G2(F_int, c2_int) - (s-t)(t+1)*S1_int
    uni_target = [Fraction(0)] * (deg1 + 1)
    uni_target[0] -= Fraction(1)
    for i in range(D3 + 1):
        for j in range(D3 + 1):
            fij = Fraction(F_int[0][i][j], dK)
            for (d,), val in T[i].items():
                uni_target[d] -= 2 * val * fij
    for k in range(D3 + 1):
        sz = D3 - k + 1
        for i in range(sz):
            for j in range(sz):
                fij = Fraction(F_int[k][i][j], dK)
                for (d,), val in poly_mul(poly_mul(T[i], T[j]), pows[k]).items():
                    uni_target[d] -= val * fij
    for k in range(1, D2 + 1):
        ck = Fraction(c2_int[k - 1], dK)
        for (d,), val in P[k].items():
            uni_target[d] -= val * ck
    for i in range(m1):
        for j in range(m1):
            sij = Fraction(S1_int[i][j], dK)
            for (d,), val in poly_mul(mult_s, poly_mul(T[i], T[j])).items():
                uni_target[d] -= val * sij

    # Round S0 to dK, then fix 17 univariate eqs using 17 diagonal/superdiagonal entries of S0!
    S0_val = S0.value
    S0_frac = [[Fraction(0)] * m0 for _ in range(m0)]
    for i in range(m0):
        for j in range(i, m0):
            v = Fraction(int(round(0.5 * (S0_val[i, j] + S0_val[j, i]) * dK)), dK)
            S0_frac[i][j] = v
            S0_frac[j][i] = v

    # Residual of univariate eqs
    uni_res = list(uni_target)
    for i in range(m0):
        for j in range(m0):
            for (d,), val in poly_mul(T[i], T[j]).items():
                uni_res[d] -= val * S0_frac[i][j]

    # Pick 17 pivot pairs (i, j) with i+j = d (i=d//2, j=(d+1)//2) for d=0..16!
    uni_pivots = [(d // 2, (d + 1) // 2) for d in range(deg1 + 1)]
    A_uni = [[Fraction(0)] * (deg1 + 1) for _ in range(deg1 + 1)]
    for col, (i, j) in enumerate(uni_pivots):
        coeff = 1 if i == j else 2
        for (d,), val in poly_mul(T[i], T[j]).items():
            A_uni[d][col] = coeff * val
    delta_uni = solve_exact_fraction_system(A_uni, uni_res)
    for col, (i, j) in enumerate(uni_pivots):
        S0_frac[i][j] += delta_uni[col]
        if i != j:
            S0_frac[j][i] += delta_uni[col]

    # Verify exact univariate identity = 0
    uni_check = list(uni_target)
    for i in range(m0):
        for j in range(m0):
            for (d,), val in poly_mul(T[i], T[j]).items():
                uni_check[d] -= val * S0_frac[i][j]
    assert all(v == 0 for v in uni_check), f"Univariate check failed: {uni_check}"
    dS0 = math.lcm(*(x.denominator for row in S0_frac for x in row))
    S0_int = [[int(x * dS0) for x in row] for row in S0_frac]
    print(f"  Univariate S0 exact! dS0={dS0} ({len(str(dS0))} digits), max |delta_uni|={max(abs(float(x)) for x in delta_uni):.3e}", flush=True)

    # === Phase 3: Exact trivariate SOS projection ===
    print("\n=== Phase 3: Exact trivariate SOS rounding & projection ===", flush=True)
    mon_idx = {m: idx for idx, m in enumerate(all_mons)}
    n_eq = len(all_mons)

    # Exact target RHS = -G3_canon(F_int)
    tri_target = [Fraction(0)] * n_eq
    for k in range(D3 + 1):
        sz = D3 - k + 1
        for i in range(sz):
            Ti_u = embed_var(T[i], 0)
            for j in range(i, sz):
                Tj_v = embed_var(T[j], 1)
                sc = sym3_canon_exact(poly_mul(poly_mul(Ti_u, Tj_v), Q[k]))
                coeff = 1 if i == j else 2
                fij = Fraction(F_int[k][i][j], dK) * coeff
                for m, v in sc.items():
                    tri_target[mon_idx[m]] -= fij * v

    # Round all M_vars to dM_init = 10^9, then do float minimum-norm projection to reduce residual by 10^4x,
    # round that float adjustment to 10^10, and THEN do exact Fraction pivot solve on the tiny residual!
    dM_init = 10**10
    M_frac = []
    for b_idx, Mv in enumerate(M_vars):
        d = Mv.shape[0]
        arr = Mv.value
        Mf = [[Fraction(0)] * d for _ in range(d)]
        for i in range(d):
            for j in range(i, d):
                v = Fraction(int(round(0.5 * (arr[i, j] + arr[j, i]) * dM_init)), dM_init)
                Mf[i][j] = v
                Mf[j][i] = v
        M_frac.append(Mf)

    # Build float constraint matrix A_flt and variable list
    var_list = []
    cols_flt = []
    for b_idx, prods in enumerate(spec_prods):
        d = len(specs[b_idx][2])
        for i in range(d):
            for j in range(i, d):
                var_list.append((b_idx, i, j))
                col = np.zeros(n_eq)
                for m, v in prods[(i, j)].items():
                    col[mon_idx[m]] = float(v)
                cols_flt.append(col)
    A_flt = np.column_stack(cols_flt)

    # Compute exact residual after initial rounding
    def compute_tri_res(Mf_list):
        res = list(tri_target)
        for b_idx, prods in enumerate(spec_prods):
            Mf = Mf_list[b_idx]
            for (i, j), sc in prods.items():
                val = Mf[i][j]
                if val != 0:
                    for m, v in sc.items():
                        res[mon_idx[m]] -= val * v
        return res

    res0 = compute_tri_res(M_frac)
    print(f"  Initial trivariate exact residual max = {max(abs(float(x)) for x in res0):.3e}", flush=True)

    # Step 3a: Float minimum-norm adjustment rounded to 10^12 to crush residual to ~1e-12
    res0_flt = np.array([float(x) for x in res0])
    dx_flt, _, rk, _ = np.linalg.lstsq(A_flt, res0_flt, rcond=None)
    dM_adj = 10**12
    for idx_v, (b_idx, i, j) in enumerate(var_list):
        adj = Fraction(int(round(dx_flt[idx_v] * dM_adj)), dM_adj)
        M_frac[b_idx][i][j] += adj
        if i != j:
            M_frac[b_idx][j][i] += adj

    res1 = compute_tri_res(M_frac)
    print(f"  After float-lstsq rounded adjustment: residual max = {max(abs(float(x)) for x in res1):.3e} (rank={rk})", flush=True)

    # Step 3b: Choose 204 pivot columns preferring INTEGER-multiplier blocks (blocks 0..5) first!
    # Wait: let's check if blocks 0..5 alone have rank 204, or how many from block 6 are needed.
    int_col_indices = [idx_v for idx_v, (b_idx, _, _) in enumerate(var_list) if b_idx < 6]
    A_int_only = A_flt[:, int_col_indices]
    rk_int = np.linalg.matrix_rank(A_int_only)
    print(f"  Rank of integer-multiplier blocks (0..5) alone: {rk_int} / {n_eq}", flush=True)

    if rk_int == n_eq:
        # Pure integer-multiplier pivots! No factor of 500 in pivot matrix!
        _, R_qr, piv = qr(A_int_only, pivoting=True)
        piv_cols = [int_col_indices[p] for p in piv[:n_eq]]
    else:
        _, R_qr, piv = qr(A_flt, pivoting=True)
        piv_cols = list(piv[:n_eq])

    # Exact Fraction solve for the 204 pivots
    t_piv = time.time()
    A_piv = [[Fraction(0)] * n_eq for _ in range(n_eq)]
    for col_k, v_idx in enumerate(piv_cols):
        b_idx, i, j = var_list[v_idx]
        for m, v in spec_prods[b_idx][(i, j)].items():
            A_piv[mon_idx[m]][col_k] = v
    delta_piv = solve_exact_fraction_system(A_piv, res1)
    print(f"  Exact 204x204 Fraction solve done in {time.time()-t_piv:.1f}s! max |delta_piv| = {max(abs(float(x)) for x in delta_piv):.3e}", flush=True)

    for col_k, v_idx in enumerate(piv_cols):
        b_idx, i, j = var_list[v_idx]
        M_frac[b_idx][i][j] += delta_piv[col_k]
        if i != j:
            M_frac[b_idx][j][i] += delta_piv[col_k]

    res2 = compute_tri_res(M_frac)
    assert all(v == 0 for v in res2), "EXACT TRIVARIATE RESIDUAL NOT ZERO!"
    print("  >>> EXACT TRIVARIATE RESIDUAL = 0 FOR ALL 204 CANONICAL MONOMIALS! <<<", flush=True)

    # Check denominators and exact Cholesky + DD for ALL 18 matrices!
    dS = math.lcm(*(x.denominator for Mf in M_frac for row in Mf for x in row))
    print(f"  Common trivariate denominator dS has {len(str(dS))} digits", flush=True)
    for b_idx, Mf in enumerate(M_frac):
        db = math.lcm(*(x.denominator for row in Mf for x in row))
        print(f"    {specs[b_idx][0]:12s} (dim {len(Mf):2d}): local denom = {len(str(db))} digits", flush=True)

    print("\n=== Phase 4: Exact integer Cholesky + Diagonal Dominance verification ===", flush=True)
    dR = 10**10
    all_ok = True
    R_F_all = []
    for k in range(D3 + 1):
        R_int, ev0, marg = exact_cholesky_dd(F_int[k], dK, dR)
        ok = (R_int is not None and marg >= 0)
        all_ok = all_ok and ok
        R_F_all.append(R_int)
        print(f"  F{k}  (dim {len(F_int[k]):2d}): min_eig={ev0:+.3e} | DD_ok={ok}", flush=True)
    R_S0, ev0, marg = exact_cholesky_dd(S0_int, dS0, dR)
    ok = (R_S0 is not None and marg >= 0)
    all_ok = all_ok and ok
    print(f"  S0  (dim {len(S0_int):2d}): min_eig={ev0:+.3e} | DD_ok={ok}", flush=True)
    R_S1, ev0, marg = exact_cholesky_dd(S1_int, dK, dR)
    ok = (R_S1 is not None and marg >= 0)
    all_ok = all_ok and ok
    print(f"  S1  (dim {len(S1_int):2d}): min_eig={ev0:+.3e} | DD_ok={ok}", flush=True)
    M_int_all = []
    dM_all = []
    R_M_all = []
    for b_idx, Mf in enumerate(M_frac):
        db = math.lcm(*(x.denominator for row in Mf for x in row))
        Mint = [[int(x * db) for x in row] for row in Mf]
        R_int, ev0, marg = exact_cholesky_dd(Mint, db, dR)
        ok = (R_int is not None and marg >= 0)
        all_ok = all_ok and ok
        M_int_all.append(Mint)
        dM_all.append(db)
        R_M_all.append(R_int)
        print(f"  M{b_idx} {specs[b_idx][0]:10s} (dim {len(Mint):2d}): min_eig={ev0:+.3e} | DD_ok={ok} | denom_digits={len(str(db))}", flush=True)

    print(f"\n>>> ALL 18 MATRICES EXACTLY VERIFIED SPD + ZERO RESIDUAL + BOUND < 18: {all_ok} (total {time.time()-t0:.1f}s) <<<", flush=True)
    if all_ok:
        import json, sys
        from pathlib import Path
        cert_data = {
            "sNum": S_NUM, "sDen": S_DEN, "dK": dK, "dS0": str(dS0), "dR": dR,
            "bound_num": bound_num,
            "F": F_int, "R_F": R_F_all,
            "c2": c2_int,
            "S0": [[str(x) for x in row] for row in S0_int], "R_S0": R_S0,
            "S1": S1_int, "R_S1": R_S1,
            "dM": [str(db) for db in dM_all],
            "M": [[[str(x) for x in row] for row in Mint] for Mint in M_int_all],
            "R_M": R_M_all,
            "block_names": [s[0] for s in specs],
            "block_dims": [len(s[2]) for s in specs],
        }
        out_json = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent / "bv8_18_cert.json"
        with open(out_json, "w") as f:
            json.dump(cert_data, f)
        print(f"Saved exact verified certificate to {out_json}", flush=True)

if __name__ == "__main__":
    main()
