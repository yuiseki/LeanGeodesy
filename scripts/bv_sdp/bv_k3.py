import numpy as np
import cvxpy as cp
from itertools import product

# Monomial basis for 1 variable t of degree <= D
# and 3 variables (u, v, t) of total degree <= D

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
    """Symmetrize a 3-variable polynomial over all 6 permutations of (u, v, t)."""
    perms = [(0,1,2), (0,2,1), (1,0,2), (1,2,0), (2,0,1), (2,1,0)]
    res = {}
    for (a, b, c), val in p.items():
        for i, j, k in perms:
            m = ([a, b, c][i], [a, b, c][j], [a, b, c][k])
            res[m] = res.get(m, 0.0) + val / 6.0
    return res

def build_Qk(max_k):
    """Build Q_k(u, v, t) as dicts {(a,b,c): coeff}."""
    Q = []
    Q.append({(0, 0, 0): 1.0})
    if max_k >= 1:
        Q.append({(0, 0, 1): 1.0, (1, 1, 0): -1.0})
    two_t_uv = {(0, 0, 1): 2.0, (1, 1, 0): -2.0}
    # (1 - u^2)(1 - v^2) = 1 - u^2 - v^2 + u^2 v^2
    prod_uv = {(0, 0, 0): 1.0, (2, 0, 0): -1.0, (0, 2, 0): -1.0, (2, 2, 0): 1.0}
    for k in range(2, max_k + 1):
        p1 = poly_mul(two_t_uv, Q[k - 1])
        p2 = poly_mul(prod_uv, Q[k - 2])
        Q.append(poly_add(p1, p2, -1.0))
    return Q

def legendre_P(max_k):
    """Legendre polynomials P_k(t) as dicts {(d,): coeff}."""
    P = [{(0,): 1.0}]
    if max_k >= 1:
        P.append({(1,): 1.0})
    for k in range(2, max_k + 1):
        # k P_k = (2k-1) t P_{k-1} - (k-1) P_{k-2}
        p1 = poly_mul({(1,): (2*k - 1) / k}, P[k - 1])
        p2 = {m: -(k - 1) / k * c for m, c in P[k - 2].items()}
        P.append(poly_add(p1, p2))
    return P

def solve_k3(d3, d2, s=0.5, sos_deg_3=None):
    """
    Solve Bachoc-Vallentin 3-point SDP on S^2 for inner product <= s.
    d3: max degree for 3-point kernel Y_k (0 <= k <= d3, size d3-k+1)
    d2: max degree for 2-point Legendre P_k (1 <= k <= d2)
    """
    if sos_deg_3 is None:
        sos_deg_3 = d3  # half-degree of SOS basis for 3-point polynomial (total degree 2*d3)

    Q = build_Qk(d3)
    P = legendre_P(d2)

    # Variables:
    # c0 = 1 (normalized)
    # a_k >= 0 for k = 1..d2 (2-point Legendre)
    a = cp.Variable(d2, nonneg=True)
    # A0 PSD of size (d3 + 2) x (d3 + 2) for k = 0 (index 0 is constant 1, index 1+i is u^i)
    A0 = cp.Variable((d3 + 2, d3 + 2), PSD=True)
    # F_k PSD of size (d3 - k + 1) x (d3 - k + 1) for k = 1..d3
    Fk = [None] + [cp.Variable((d3 - k + 1, d3 - k + 1), PSD=True) for k in range(1, d3 + 1)]

    # Objective: 1 + sum_{k=1}^{d2} a_k + A0[0, 0]
    # Wait: let's check the identity!
    # 1) sum_{i,j} (1 + sum_{k=1}^{d2} a_k P_k(<pi,pj>)) >= N^2
    #    LHS = N * (1 + sum a_k) + sum_{i!=j} (1 + sum a_k P_k(t))
    # 2) sum_x v0(x)^T A0 v0(x) >= 0, where v0(x) = (1, sum_{y!=x} 1, sum_{y!=x} u, ..., sum_{y!=x} u^{d3})
    #    = N * A0[0,0]
    #      + sum_{x!=y} (2 * sum_{i=0}^{d3} A0[0, 1+i] t^i + sum_{i,j=0}^{d3} A0[1+i, 1+j] t^{i+j})
    #      + sum_{x,y,z dist} sum_{i,j=0}^{d3} A0[1+i, 1+j] u^i v^j
    # 3) sum_{k=1}^{d3} sum_x sum_{y,z != x} <Fk, Y_k(u,v,t)> >= 0
    #    = sum_{x!=y} sum_{k=1}^{d3} sum_{i,j} Fk[i,j] t^{i+j} (1 - t^2)^k
    #      + sum_{x,y,z dist} sum_{k=1}^{d3} sum_{i,j} Fk[i,j] u^i v^j Q_k(u,v,t)
    # Summing (1)+(2)+(3):
    #   N^2 <= N * (1 + sum a_k + A0[0,0]) + sum_{x!=y} G2(t) + sum_{x,y,z dist} G3(u,v,t)
    # Requiring G2(t) <= 0 on [-1, s] and G3_sym(u,v,t) <= 0 on Delta(s) gives:
    #   N <= 1 + sum a_k + A0[0,0] !

    # Build 2-point polynomial G2(t) of degree <= max(d2, 2*d3)
    deg2 = max(d2, 2 * d3)
    G2_coeffs = [0 for _ in range(deg2 + 1)]
    G2_coeffs[0] = G2_coeffs[0] + 1.0
    for k in range(1, d2 + 1):
        for (deg,), val in P[k].items():
            G2_coeffs[deg] = G2_coeffs[deg] + a[k - 1] * val
    for i in range(d3 + 1):
        G2_coeffs[i] = G2_coeffs[i] + 2.0 * A0[0, 1 + i]
        for j in range(d3 + 1):
            G2_coeffs[i + j] = G2_coeffs[i + j] + A0[1 + i, 1 + j]
    # (1 - t^2)^k expansion
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

    # SOS constraint for -G2(t) >= 0 on [-1, s]:
    # -G2(t) = sigma0(t) + (t + 1)(s - t) sigma1(t)
    # where deg(sigma0) <= 2*h0, deg(sigma1) <= 2*h1
    h0 = (deg2 + 1) // 2
    h1 = (deg2 - 1) // 2
    S2_0 = cp.Variable((h0 + 1, h0 + 1), PSD=True)
    S2_1 = cp.Variable((h1 + 1, h1 + 1), PSD=True)
    # (t + 1)(s - t) = s + (s - 1) t - t^2
    constraints = []
    for d in range(max(deg2, 2 * h0, 2 * h1 + 2) + 1):
        rhs = 0
        for i in range(h0 + 1):
            j = d - i
            if 0 <= j <= h0:
                rhs = rhs + S2_0[i, j]
        # (s + (s-1)t - t^2) * sum S2_1[i,j] t^{i+j}
        for i in range(h1 + 1):
            for j in range(h1 + 1):
                if i + j == d:
                    rhs = rhs + s * S2_1[i, j]
                if i + j + 1 == d:
                    rhs = rhs + (s - 1.0) * S2_1[i, j]
                if i + j + 2 == d:
                    rhs = rhs - S2_1[i, j]
        lhs = -G2_coeffs[d] if d <= deg2 else 0
        constraints.append(lhs == rhs)

    # Build 3-point symmetrized polynomial G3(u, v, t) of total degree <= 2*d3
    G3 = {}
    def add_G3(poly_dict, var_expr):
        sp = sym3(poly_dict)
        for m, val in sp.items():
            if abs(val) > 1e-14:
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

    # SOS constraint for -G3(u, v, t) >= 0 on Delta(s):
    # Monomials of total degree <= r
    def mons(r):
        return [(a1, b1, c1) for a1 in range(r + 1) for b1 in range(r + 1 - a1) for c1 in range(r + 1 - a1 - b1)]

    # Multipliers on Delta(s):
    # 1 (deg 0), Delta = 1 + 2uvt - u^2 - v^2 - t^2 (deg 3),
    # (s - u)(u + 1) (deg 2, symmetrized by cyclic sum),
    # (s - u)(s - v) (deg 2, symmetrized by cyclic sum)
    r0 = sos_deg_3
    rD = max(0, sos_deg_3 - 2)  # since deg(Delta) = 3, 2*rD + 3 <= 2*sos_deg_3 => rD = sos_deg_3 - 2 (or -1 if we allow deg 2*sos_deg_3+1)
    r1 = max(0, sos_deg_3 - 1)  # deg((s-u)(u+1)) = 2

    m0 = mons(r0)
    mD = mons(rD) if sos_deg_3 >= 2 else []
    m1 = mons(r1) if sos_deg_3 >= 1 else []

    M0 = cp.Variable((len(m0), len(m0)), PSD=True)
    MD = cp.Variable((len(mD), len(mD)), PSD=True) if mD else None
    M1 = cp.Variable((len(m1), len(m1)), PSD=True) if m1 else None
    M2 = cp.Variable((len(m1), len(m1)), PSD=True) if m1 else None

    RHS3 = {}
    def add_RHS3(m_key, expr):
        RHS3[m_key] = RHS3.get(m_key, 0) + expr

    # M0 * 1
    for idx1, e1 in enumerate(m0):
        for idx2, e2 in enumerate(m0):
            m = (e1[0]+e2[0], e1[1]+e2[1], e1[2]+e2[2])
            add_RHS3(m, M0[idx1, idx2])

    # MD * (1 + 2uvt - u^2 - v^2 - t^2)
    Delta_poly = {(0,0,0): 1.0, (1,1,1): 2.0, (2,0,0): -1.0, (0,2,0): -1.0, (0,0,2): -1.0}
    if MD is not None:
        for idx1, e1 in enumerate(mD):
            for idx2, e2 in enumerate(mD):
                base = (e1[0]+e2[0], e1[1]+e2[1], e1[2]+e2[2])
                for dm, dv in Delta_poly.items():
                    m = (base[0]+dm[0], base[1]+dm[1], base[2]+dm[2])
                    add_RHS3(m, MD[idx1, idx2] * dv)

    # Symmetrized M1 * (s - u)(u + 1) = (s + (s-1)u - u^2)
    g1_poly = {(0,0,0): s, (1,0,0): s - 1.0, (2,0,0): -1.0}
    if M1 is not None:
        for idx1, e1 in enumerate(m1):
            for idx2, e2 in enumerate(m1):
                base = (e1[0]+e2[0], e1[1]+e2[1], e1[2]+e2[2])
                prod_p = {(base[0]+dm[0], base[1]+dm[1], base[2]+dm[2]): dv for dm, dv in g1_poly.items()}
                for m, dv in sym3(prod_p).items():
                    if abs(dv) > 1e-14:
                        add_RHS3(m, M1[idx1, idx2] * dv)

    # Symmetrized M2 * (s - u)(s - v) = s^2 - s*u - s*v + u*v
    g2_poly = {(0,0,0): s*s, (1,0,0): -s, (0,1,0): -s, (1,1,0): 1.0}
    if M2 is not None:
        for idx1, e1 in enumerate(m1):
            for idx2, e2 in enumerate(m1):
                base = (e1[0]+e2[0], e1[1]+e2[1], e1[2]+e2[2])
                prod_p = {(base[0]+dm[0], base[1]+dm[1], base[2]+dm[2]): dv for dm, dv in g2_poly.items()}
                for m, dv in sym3(prod_p).items():
                    if abs(dv) > 1e-14:
                        add_RHS3(m, M2[idx1, idx2] * dv)

    all_mons = set(G3.keys()) | set(RHS3.keys())
    for m in sorted(all_mons):
        lhs = -G3.get(m, 0)
        rhs = RHS3.get(m, 0)
        constraints.append(lhs == rhs)

    obj = 1.0 + cp.sum(a) + A0[0, 0]
    prob = cp.Problem(cp.Minimize(obj), constraints)
    prob.solve(solver=cp.CLARABEL)
    print(f"d3={d3}, d2={d2}, sos_deg={sos_deg_3}: status={prob.status}, bound={prob.value}")
    return prob.value

for d3, d2 in [(2, 4), (3, 6), (4, 8), (5, 10)]:
    solve_k3(d3, d2)
