import numpy as np
import cvxpy as cp

def poly_mul(p, q):
    res = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(a + b for a, b in zip(m1, m2))
            res[m] = res.get(m, 0.0) + c1 * c2
    return {m: c for m, c in res.items() if abs(c) > 1e-14}

def poly_add(p, q, scale=1.0):
    res = dict(p)
    for m, c in q.items():
        res[m] = res.get(m, 0.0) + scale * c
    return res

def sym3(p):
    perms = [(0,1,2), (0,2,1), (1,0,2), (1,2,0), (2,0,1), (2,1,0)]
    res = {}
    for (a, b, c), val in p.items():
        for i, j, k in perms:
            m = ([a, b, c][i], [a, b, c][j], [a, b, c][k])
            res[m] = res.get(m, 0.0) + val / 6.0
    return res

def build_Qk(max_k):
    Q = [{(0, 0, 0): 1.0}]
    if max_k >= 1:
        Q.append({(0, 0, 1): 1.0, (1, 1, 0): -1.0})
    two_t_uv = {(0, 0, 1): 2.0, (1, 1, 0): -2.0}
    prod_uv = {(0, 0, 0): 1.0, (2, 0, 0): -1.0, (0, 2, 0): -1.0, (2, 2, 0): 1.0}
    for k in range(2, max_k + 1):
        p1 = poly_mul(two_t_uv, Q[k - 1])
        p2 = poly_mul(prod_uv, Q[k - 2])
        Q.append(poly_add(p1, p2, -1.0))
    return Q

def legendre_P(max_k):
    P = [{(0,): 1.0}]
    if max_k >= 1:
        P.append({(1,): 1.0})
    for k in range(2, max_k + 1):
        p1 = poly_mul({(1,): (2*k - 1) / k}, P[k - 1])
        p2 = {m: -(k - 1) / k * c for m, c in P[k - 2].items()}
        P.append(poly_add(p1, p2))
    return P

# Build S3-invariant SOS basis using elementary symmetric polynomials e1, e2, e3:
# Any S3-invariant polynomial is a polynomial in e1, e2, e3.
# And an S3-invariant SOS in (u,v,t) decomposes into 3 isotypic components (Gatermann-Parrilo):
#   1. Trivial rep:  f(e1,e2,e3)^2  (basis: monomials in e1,e2,e3 of weighted deg <= r)
#   2. Sign rep:     ((u-v)(v-t)(t-u))^2 * f(e1,e2,e3)^2  (discriminant = D_3, deg 6)
#   3. Standard rep (2D):
#      For any vector of pairs (p_i(e), q_i(e)) with weighted deg(p_i) <= r-1, deg(q_i) <= r-2:
#      span of { (u-v) p(e) + (u^2-v^2) q(e) } symmetrized ->
#      Actually, in standard rep: let b1 = u - v, b2 = u + v - 2t (orthogonal under S3),
#      and c1 = u^2 - v^2, c2 = u^2 + v^2 - 2t^2.
#      Better yet: for a symmetric matrix M on basis {p_i(e)*b1 + q_j(e)*c1}, averaging over S3 gives
#      sum_cyc ((u-v) P + (u^2-v^2) Q)^2 !
#      Even simpler: take basis vectors of the form:
#        - trivial: e1^a e2^b e3^c (deg <= r)
#        - std:     e1^a e2^b e3^c * (u - v) (deg <= r-1) and e1^a e2^b e3^c * (u^2 - v^2) (deg <= r-2)
#                   symmetrized by sym3(v_i * v_j)!
#        - sign:    e1^a e2^b e3^c * (u-v)(v-t)(t-u) (deg <= r-3)

e1 = {(1,0,0): 1.0, (0,1,0): 1.0, (0,0,1): 1.0}
e2 = {(1,1,0): 1.0, (1,0,1): 1.0, (0,1,1): 1.0}
e3 = {(1,1,1): 1.0}

def e_mon(a, b, c):
    res = {(0,0,0): 1.0}
    for _ in range(a): res = poly_mul(res, e1)
    for _ in range(b): res = poly_mul(res, e2)
    for _ in range(c): res = poly_mul(res, e3)
    return res

def e_mons(max_deg):
    out = []
    for a in range(max_deg + 1):
        for b in range((max_deg - a) // 2 + 1):
            for c in range((max_deg - a - 2*b) // 3 + 1):
                out.append((a, b, c, e_mon(a, b, c)))
    return out

def s3_sos_blocks(max_half_deg, mult_poly, sym_mult=True):
    """
    Create S3-reduced PSD blocks for mult_poly * SOS of total degree <= 2*max_half_deg + deg(mult).
    If sym_mult=True, mult_poly is S3-symmetric (e.g., 1, Delta, (s-u)(s-v)(s-t)).
    Returns (list of cp.Variable, dict {monomial: cp.Expression}) representing sym3(mult * SOS).
    """
    vars_list = []
    exprs = {}
    def add_e(m, ex):
        exprs[m] = exprs.get(m, 0) + ex

    if sym_mult:
        # 1. Trivial rep
        b_triv = [p for (_, _, _, p) in e_mons(max_half_deg)]
        # 2. Standard rep: (u-v)*e_mon and (u^2-v^2)*e_mon
        u_m_v = {(1,0,0): 1.0, (0,1,0): -1.0}
        u2_m_v2 = {(2,0,0): 1.0, (0,2,0): -1.0}
        b_std = [poly_mul(u_m_v, p) for (_, _, _, p) in e_mons(max_half_deg - 1)] if max_half_deg >= 1 else []
        b_std += [poly_mul(u2_m_v2, p) for (_, _, _, p) in e_mons(max_half_deg - 2)] if max_half_deg >= 2 else []
        # 3. Sign rep: (u-v)(v-t)(t-u)*e_mon
        disc = poly_mul(poly_mul(u_m_v, {(0,1,0): 1.0, (0,0,1): -1.0}), {(0,0,1): 1.0, (1,0,0): -1.0})
        b_sign = [poly_mul(disc, p) for (_, _, _, p) in e_mons(max_half_deg - 3)] if max_half_deg >= 3 else []

        for basis in [b_triv, b_std, b_sign]:
            if not basis:
                continue
            M = cp.Variable((len(basis), len(basis)), PSD=True)
            vars_list.append(M)
            for i in range(len(basis)):
                for j in range(i, len(basis)):
                    prod_ij = sym3(poly_mul(mult_poly, poly_mul(basis[i], basis[j])))
                    coeff = 1.0 if i == j else 2.0
                    for m, v in prod_ij.items():
                        if abs(v) > 1e-14:
                            add_e(m, M[i, j] * (coeff * v))
    else:
        # mult_poly is invariant under v <-> t (e.g., (s - u)(u + 1) or (s - u))
        # Basis in (u, v+t, vt) [even in v-t] and (v-t)*(u, v+t, vt) [odd in v-t]
        v_p_t = {(0,1,0): 1.0, (0,0,1): 1.0}
        v_t = {(0,1,1): 1.0}
        v_m_t = {(0,1,0): 1.0, (0,0,1): -1.0}
        def vt_mons(r):
            out = []
            for a in range(r + 1):
                for b in range(r - a + 1):
                    for c in range((r - a - b) // 2 + 1):
                        p = {(a, 0, 0): 1.0}
                        for _ in range(b): p = poly_mul(p, v_p_t)
                        for _ in range(c): p = poly_mul(p, v_t)
                        out.append(p)
            return out
        b_even = vt_mons(max_half_deg)
        b_odd = [poly_mul(v_m_t, p) for p in vt_mons(max_half_deg - 1)] if max_half_deg >= 1 else []
        for basis in [b_even, b_odd]:
            if not basis:
                continue
            M = cp.Variable((len(basis), len(basis)), PSD=True)
            vars_list.append(M)
            for i in range(len(basis)):
                for j in range(i, len(basis)):
                    prod_ij = sym3(poly_mul(mult_poly, poly_mul(basis[i], basis[j])))
                    coeff = 1.0 if i == j else 2.0
                    for m, v in prod_ij.items():
                        if abs(v) > 1e-14:
                            add_e(m, M[i, j] * (coeff * v))
    return vars_list, exprs

def solve_k3_s3(d3, d2, s=0.5, use_linear_u=True):
    Q = build_Qk(d3)
    P = legendre_P(d2)

    a = cp.Variable(d2, nonneg=True) if d2 > 0 else None
    A0 = cp.Variable((d3 + 2, d3 + 2), PSD=True)
    Fk = [None] + [cp.Variable((d3 - k + 1, d3 - k + 1), PSD=True) for k in range(1, d3 + 1)]

    deg2 = max(d2, 2 * d3)
    G2_coeffs = [0 for _ in range(deg2 + 1)]
    G2_coeffs[0] = G2_coeffs[0] + 1.0
    if d2 > 0:
        for k in range(1, d2 + 1):
            for (deg,), val in P[k].items():
                G2_coeffs[deg] = G2_coeffs[deg] + a[k - 1] * val
    for i in range(d3 + 1):
        G2_coeffs[i] = G2_coeffs[i] + 2.0 * A0[0, 1 + i]
        for j in range(d3 + 1):
            G2_coeffs[i + j] = G2_coeffs[i + j] + A0[1 + i, 1 + j]
    one_minus_t2 = {(0,): 1.0, (2,): -1.0}
    pow_1mt2 = [{(0,): 1.0}]
    for k in range(1, d3 + 1):
        pow_1mt2.append(poly_mul(pow_1mt2[-1], one_minus_t2))
    for k in range(1, d3 + 1):
        m = d3 - k + 1
        for i in range(m):
            for j in range(m):
                for (deg,), val in pow_1mt2[k].items():
                    G2_coeffs[i + j + deg] = G2_coeffs[i + j + deg] + Fk[k][i, j] * val

    h0 = (deg2 + 1) // 2
    h1 = (deg2 - 1) // 2
    S2_0 = cp.Variable((h0 + 1, h0 + 1), PSD=True)
    S2_1 = cp.Variable((h1 + 1, h1 + 1), PSD=True)
    constraints = []
    for d in range(max(deg2, 2 * h0, 2 * h1 + 2) + 1):
        rhs = 0
        for i in range(h0 + 1):
            j = d - i
            if 0 <= j <= h0:
                rhs = rhs + S2_0[i, j]
        for i in range(h1 + 1):
            for j in range(h1 + 1):
                if i + j == d: rhs = rhs + s * S2_1[i, j]
                if i + j + 1 == d: rhs = rhs + (s - 1.0) * S2_1[i, j]
                if i + j + 2 == d: rhs = rhs - S2_1[i, j]
        lhs = -G2_coeffs[d] if d <= deg2 else 0
        constraints.append(lhs == rhs)

    # 3-point polynomial G3 (only keep canonical sorted monomials a >= b >= c!)
    G3 = {}
    def add_G3(poly_dict, var_expr):
        sp = sym3(poly_dict)
        for m, val in sp.items():
            if m[0] >= m[1] >= m[2] and abs(val) > 1e-14:
                G3[m] = G3.get(m, 0) + var_expr * val

    for i in range(d3 + 1):
        for j in range(d3 + 1):
            add_G3({(i, j, 0): 1.0}, A0[1 + i, 1 + j])
    for k in range(1, d3 + 1):
        m = d3 - k + 1
        for i in range(m):
            for j in range(m):
                p_ij = {(a1 + i, b1 + j, c1): val for (a1, b1, c1), val in Q[k].items()}
                add_G3(p_ij, Fk[k][i, j])

    # S3-reduced SOS on Delta(s)
    Delta_poly = {(0,0,0): 1.0, (1,1,1): 2.0, (2,0,0): -1.0, (0,2,0): -1.0, (0,0,2): -1.0}
    g1_poly = {(0,0,0): s, (1,0,0): s - 1.0, (2,0,0): -1.0}  # (s - u)(u + 1), v<->t invariant
    g2_poly = {(0,0,0): s*s, (0,1,0): -s, (0,0,1): -s, (0,1,1): 1.0}  # (s - v)(s - t), v<->t invariant
    glin_poly = {(0,0,0): s, (1,0,0): -1.0}  # (s - u), v<->t invariant

    all_blocks = [
        s3_sos_blocks(d3, {(0,0,0): 1.0}, sym_mult=True),
        s3_sos_blocks(d3 - 2, Delta_poly, sym_mult=True),
        s3_sos_blocks(d3 - 1, g1_poly, sym_mult=False),
        s3_sos_blocks(d3 - 1, g2_poly, sym_mult=False),
    ]
    if use_linear_u:
        all_blocks.append(s3_sos_blocks(d3 - 1, glin_poly, sym_mult=False))

    RHS3 = {}
    block_sizes = []
    for vlist, exprs in all_blocks:
        block_sizes.extend([v.shape[0] for v in vlist])
        for m, ex in exprs.items():
            if m[0] >= m[1] >= m[2]:
                RHS3[m] = RHS3.get(m, 0) + ex

    all_mons = set(G3.keys()) | set(RHS3.keys())
    for m in sorted(all_mons):
        constraints.append(-G3.get(m, 0) == RHS3.get(m, 0))

    obj = 1.0 + (cp.sum(a) if d2 > 0 else 0.0) + A0[0, 0]
    prob = cp.Problem(cp.Minimize(obj), constraints)
    prob.solve(solver=cp.CLARABEL)
    print(f"d3={d3}, d2={d2}, lin={use_linear_u}: status={prob.status}, bound={prob.value:.6f}, max_block={max(block_sizes)}, n_blocks={len(block_sizes)}")

for d3, d2 in [(4, 0), (4, 4), (4, 8), (5, 0), (5, 4), (5, 6), (5, 10)]:
    solve_k3_s3(d3, d2, use_linear_u=True)
