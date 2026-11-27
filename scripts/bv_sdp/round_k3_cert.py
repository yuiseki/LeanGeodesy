import numpy as np
import cvxpy as cp
from fractions import Fraction

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

def sym3_exact(p):
    """Symmetrize a 3-var exact Fraction polynomial over S3 (sum of 6 perms / 6)."""
    perms = [(0,1,2), (0,2,1), (1,0,2), (1,2,0), (2,0,1), (2,1,0)]
    res = {}
    for (a, b, c), val in p.items():
        for i, j, k in perms:
            m = ([a, b, c][i], [a, b, c][j], [a, b, c][k])
            res[m] = res.get(m, Fraction(0)) + val / 6
    return {m: c for m, c in res.items() if c != 0}

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

# Exact S3-reduced bases (over Fraction)
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
    """Return list of (name, mult_poly, basis_list) for S3-reduced SOS."""
    u_m_v = {(1,0,0): Fraction(1), (0,1,0): Fraction(-1)}
    u2_m_v2 = {(2,0,0): Fraction(1), (0,2,0): Fraction(-1)}
    v_m_t = {(0,1,0): Fraction(1), (0,0,1): Fraction(-1)}
    disc = poly_mul(poly_mul(u_m_v, {(0,1,0): Fraction(1), (0,0,1): Fraction(-1)}), {(0,0,1): Fraction(1), (1,0,0): Fraction(-1)})

    Delta_poly = {(0,0,0): Fraction(1), (1,1,1): Fraction(2), (2,0,0): Fraction(-1), (0,2,0): Fraction(-1), (0,0,2): Fraction(-1)}
    g1_poly = {(0,0,0): s_frac, (1,0,0): s_frac - 1, (2,0,0): Fraction(-1)}  # (s-u)(u+1)
    g2_poly = {(0,0,0): s_frac**2, (0,1,0): -s_frac, (0,0,1): -s_frac, (0,1,1): Fraction(1)}  # (s-v)(s-t)
    glin_poly = {(0,0,0): s_frac, (1,0,0): Fraction(-1)}  # (s-u)

    specs = []
    for name, r, mult, is_sym in [
        ("one", d3, {(0,0,0): Fraction(1)}, True),
        ("delta", d3 - 2, Delta_poly, True),
        ("g1", d3 - 1, g1_poly, False),
        ("g2", d3 - 1, g2_poly, False),
        ("glin", d3 - 1, glin_poly, False),
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

def exact_ldlt(M_frac):
    """Compute exact rational LDL^T for symmetric matrix M_frac. Returns (L, D) or None if not PD."""
    n = len(M_frac)
    L = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
    D = [Fraction(0)] * n
    for j in range(n):
        s = M_frac[j][j] - sum(L[j][k] * L[j][k] * D[k] for k in range(j))
        if s <= 0:
            return None, s
        D[j] = s
        for i in range(j + 1, n):
            L[i][j] = (M_frac[i][j] - sum(L[i][k] * L[j][k] * D[k] for k in range(j))) / D[j]
    return (L, D), min(D)

def round_matrix(M_np, denom):
    n = M_np.shape[0]
    M_sym = 0.5 * (M_np + M_np.T)
    return [[Fraction(int(round(M_sym[i, j] * denom)), denom) for j in range(n)] for i in range(n)]

d3 = 5
s_frac = Fraction(1, 2)
s = float(s_frac)
Q = build_Qk_exact(d3)

# Solve SDP maximizing minimum eigenvalue margin `eps` subject to bound <= 12.95!
# That gives a strictly interior point where ALL matrices are strictly PD!
A0 = cp.Variable((d3 + 2, d3 + 2), symmetric=True)
Fk = [None] + [cp.Variable((d3 - k + 1, d3 - k + 1), symmetric=True) for k in range(1, d3 + 1)]
eps = cp.Variable(nonneg=True)

constraints = [A0 >> eps * np.eye(d3 + 2)]
for k in range(1, d3 + 1):
    constraints.append(Fk[k] >> eps * np.eye(d3 - k + 1))

# 2-point G2(t) of degree 10
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
        if 0 <= j <= h0:
            rhs = rhs + S2_0[i, j]
    for i in range(h1 + 1):
        for j in range(h1 + 1):
            if i + j == d: rhs = rhs + s * S2_1[i, j]
            if i + j + 1 == d: rhs = rhs + (s - 1.0) * S2_1[i, j]
            if i + j + 2 == d: rhs = rhs - S2_1[i, j]
    constraints.append(-G2_coeffs[d] == rhs)

# 3-point G3 (canonical sorted monomials a >= b >= c)
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

specs = get_sos3_specs(d3, s_frac)
M_vars = []
RHS3 = {}
# Also precompute exact linear map from SOS matrices to canonical monomials for exact projection!
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
print(f"Canonical 3-var monomials: {len(all_mons)}, SOS blocks: {[(n, len(b)) for n, _, b in specs]}")
for m in all_mons:
    constraints.append(-G3.get(m, 0) == RHS3.get(m, 0))

# Bound <= 12.95, maximize interiority eps (with mild trace cap so numbers stay small!)
constraints.append(1.0 + A0[0, 0] <= 12.95)
trace_sum = cp.trace(A0) + sum(cp.trace(Fk[k]) for k in range(1, d3 + 1)) + cp.trace(S2_0) + cp.trace(S2_1) + sum(cp.trace(M) for M in M_vars)
constraints.append(trace_sum <= 5000.0)

prob = cp.Problem(cp.Maximize(eps), constraints)
prob.solve(solver=cp.CLARABEL)
print(f"Interiority solve: status={prob.status}, eps={eps.value:.6e}, bound={1.0 + A0.value[0,0]:.6f}")

# Check exact rounding!
denom_kernel = 1000
A0_q = round_matrix(A0.value, denom_kernel)
Fk_q = [None] + [round_matrix(Fk[k].value, denom_kernel) for k in range(1, d3 + 1)]
print("Exact bound:", 1 + A0_q[0][0], "=", float(1 + A0_q[0][0]))

for name, Mq in [("A0", A0_q)] + [(f"F{k}", Fk_q[k]) for k in range(1, d3 + 1)]:
    res, mind = exact_ldlt(Mq)
    print(f"  {name} ({len(Mq)}x{len(Mq)}): PD={res is not None}, min_D={float(mind):.6e}")

# Compute exact G2_q
G2_q = [Fraction(0)] * (deg2 + 1)
G2_q[0] += Fraction(1)
for i in range(d3 + 1):
    G2_q[i] += 2 * A0_q[0][1 + i]
    for j in range(d3 + 1):
        G2_q[i + j] += A0_q[1 + i][1 + j]
for k in range(1, d3 + 1):
    mk = d3 - k + 1
    for i in range(mk):
        for j in range(mk):
            for (deg,), val in pow_1mt2[k].items():
                G2_q[i + j + deg] += Fk_q[k][i][j] * val

# Round S2_0, S2_1 and project exact residual onto S2_0, S2_1 using minimum-norm rational projection
denom_sos = 10000
S2_0_q = round_matrix(S2_0.value, denom_sos)
S2_1_q = round_matrix(S2_1.value, denom_sos)

# Residual of -G2_q - RHS2_q
def eval_rhs2(S0, S1):
    out = [Fraction(0)] * (deg2 + 1)
    for i in range(h0 + 1):
        for j in range(h0 + 1):
            out[i + j] += S0[i][j]
    for i in range(h1 + 1):
        for j in range(h1 + 1):
            out[i + j] += s_frac * S1[i][j]
            out[i + j + 1] += (s_frac - 1) * S1[i][j]
            out[i + j + 2] -= S1[i][j]
    return out

rhs2 = eval_rhs2(S2_0_q, S2_1_q)
res2 = [-G2_q[d] - rhs2[d] for d in range(deg2 + 1)]
# Absorb res2[d] directly into S2_0_q[i][j] with i+j=d!
for d in range(deg2 + 1):
    if res2[d] != 0:
        i = d // 2
        j = d - i
        if i == j:
            S2_0_q[i][i] += res2[d]
        else:
            S2_0_q[i][j] += res2[d] / 2
            S2_0_q[j][i] += res2[d] / 2

rhs2_new = eval_rhs2(S2_0_q, S2_1_q)
assert all(-G2_q[d] == rhs2_new[d] for d in range(deg2 + 1)), "G2 mismatch!"
for name, Mq in [("S2_0", S2_0_q), ("S2_1", S2_1_q)]:
    res, mind = exact_ldlt(Mq)
    print(f"  {name} ({len(Mq)}x{len(Mq)}): PD={res is not None}, min_D={float(mind):.6e}")

# Exact G3_q
G3_q = {m: Fraction(0) for m in all_mons}
for i in range(d3 + 1):
    for j in range(d3 + 1):
        for m, val in sym3_exact({(i, j, 0): Fraction(1)}).items():
            if m[0] >= m[1] >= m[2]:
                G3_q[m] += A0_q[1 + i][1 + j] * val
for k in range(1, d3 + 1):
    mk = d3 - k + 1
    for i in range(mk):
        for j in range(mk):
            p_ij = {(a1 + i, b1 + j, c1): val for (a1, b1, c1), val in Q[k].items()}
            for m, val in sym3_exact(p_ij).items():
                if m[0] >= m[1] >= m[2]:
                    G3_q[m] += Fk_q[k][i][j] * val

# Round M_vars and project exact 3-var residual!
M_q = [round_matrix(M.value, denom_sos) for M in M_vars]
# Build exact linear system A * delta = residual over numpy, solve least-squares, or exact rational Gaussian elimination!
# Wait: there are only 61 equations (all_mons) and ~800 symmetric matrix entries!
# Pick 61 linearly independent matrix entries and solve the 61x61 system EXACTLY over Fraction!
mon_idx = {m: idx for idx, m in enumerate(all_mons)}
num_eq = len(all_mons)

# Compute current exact residual
rhs3 = {m: Fraction(0) for m in all_mons}
for b_idx, p_map in enumerate(spec_polys):
    for (i, j), canon in p_map.items():
        val = M_q[b_idx][i][j]
        for m, c in canon.items():
            rhs3[m] += val * c
res3 = [(-G3_q[m] - rhs3[m]) for m in all_mons]
print(f"Max 3-var residual before exact projection: {max(abs(float(x)) for x in res3):.3e}")

# Collect columns (b_idx, i, j) -> float vector of length num_eq
cols_info = []
cols_vec = []
for b_idx, p_map in enumerate(spec_polys):
    for (i, j), canon in p_map.items():
        v = np.zeros(num_eq)
        for m, c in canon.items():
            v[mon_idx[m]] = float(c)
        if np.linalg.norm(v) > 0:
            cols_info.append((b_idx, i, j, canon))
            cols_vec.append(v)

A_mat = np.column_stack(cols_vec)
# Minimum-norm float solution first, then exact rational projection on a full-rank subset!
# Even better: use QR with column pivoting to pick 61 well-conditioned columns, then solve 61x61 EXACTLY over Fraction!
from scipy.linalg import qr
_, R_qr, piv = qr(A_mat, pivoting=True)
rank = np.sum(np.abs(np.diag(R_qr)) > 1e-10)
print(f"Linear map rank: {rank} / {num_eq}")
assert rank == num_eq, "Not full rank!"

chosen = piv[:num_eq]
# Exact rational Gaussian elimination on chosen columns
mat = [[Fraction(0) for _ in range(num_eq + 1)] for _ in range(num_eq)]
for c_pos, col_id in enumerate(chosen):
    _, _, _, canon = cols_info[col_id]
    for m, c in canon.items():
        mat[mon_idx[m]][c_pos] = c
for r in range(num_eq):
    mat[r][num_eq] = res3[r]

# Gauss-Jordan over Fraction
for col in range(num_eq):
    piv_row = next(r for r in range(col, num_eq) if mat[r][col] != 0)
    mat[col], mat[piv_row] = mat[piv_row], mat[col]
    pv = mat[col][col]
    mat[col] = [x / pv for x in mat[col]]
    for r in range(num_eq):
        if r != col and mat[r][col] != 0:
            f = mat[r][col]
            mat[r] = [mat[r][c] - f * mat[col][c] for c in range(num_eq + 1)]

deltas = [mat[r][num_eq] for r in range(num_eq)]
print(f"Max exact rational adjustment: {max(abs(float(x)) for x in deltas):.3e}")
for c_pos, col_id in enumerate(chosen):
    b_idx, i, j, _ = cols_info[col_id]
    dval = deltas[c_pos]
    M_q[b_idx][i][j] += dval
    if i != j:
        M_q[b_idx][j][i] += dval

# Re-verify exact polynomial identity AND exact rational PD of ALL 12 SOS blocks!
rhs3_new = {m: Fraction(0) for m in all_mons}
for b_idx, p_map in enumerate(spec_polys):
    for (i, j), canon in p_map.items():
        val = M_q[b_idx][i][j]
        for m, c in canon.items():
            rhs3_new[m] += val * c
assert all(-G3_q[m] == rhs3_new[m] for m in all_mons), "G3 mismatch!"
print("EXACT RATIONAL 3-VAR POLYNOMIAL IDENTITY VERIFIED (0 residual)!")

all_pd = True
for (name, _, _), Mq in zip(specs, M_q):
    res, mind = exact_ldlt(Mq)
    ok = res is not None
    all_pd = all_pd and ok
    print(f"  SOS {name:12s} ({len(Mq):2d}x{len(Mq):2d}): PD={ok}, min_D={float(mind):.6e}")

print("ALL MATRICES EXACTLY RATIONAL PD:", all_pd)
