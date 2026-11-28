#!/usr/bin/env python3
"""Exact second-order analysis of Jucovic's nine-point covering, without symmetry.

This script is a verification outside Lean. It proves, by exact arithmetic in the number
field K = Q(sqrt3, t*, h*) and by exact rational interval arithmetic (no floating point in
any conclusion), the following facts about the configuration P* of
LeanGeodesy/Spherical/Jucovic9.lean (t* the root in (2/3, 1) of 4t^4 - 4t^3 + 3t^2 + 4t - 4,
h* = sqrt(1 - t*^2)):

  1. the 8 active faces (two triangles, six sides) have distance h*; the 6 slopes more;
  2. the KKT multipliers of max min_f d_f are unique and positive:
       lambda_T (each triangle) = r / (2r + 6), lambda_V (each side) = 1 / (2r + 6),
     with r given exactly below; the tangential gradient of sum lambda_f d_f vanishes at
     every point (exact identity in K);
  3. the 8 x 18 tangent Jacobian of the active distances has rank 7 (a nonzero 7 x 7 minor);
  4. with F = - sum lambda_f / d_f, the Hessian of the Lagrangian F - sum mu_i (|p_i|^2 - 1)
     restricted to a 15-dimensional complement of the rotation orbit is negative definite
     (certified Cholesky decomposition in exact rational interval arithmetic).

From 4, by the second-order sufficient condition on the manifold (S^2)^9 and the slice
argument for the rotation group, P* is a strict local maximum of F modulo rotations. Near
P* every face plane stays a supporting plane, so for P near P* and not a rotation of P*,
min_f d_f(P) <= (sum lambda_f / d_f(P))^-1 < h*, hence coveringRadius P > arccos h*:
strict local optimality of P* without any symmetry assumption. The classical second-order
sufficient condition and slice theorem are used, not re-proved; Lean does not check this
file.

usage: python3 jucovic9_local.py
"""
from fractions import Fraction as Fr
import sympy as sp

t, h, s = sp.symbols('t h s')
QUART = 4 * t**4 - 4 * t**3 + 3 * t**2 + 4 * t - 4

# ---------------------------------------------------------------- exact normal forms in K
def nf_poly(e):
    """Normal form of a polynomial in s, h, t modulo s^2 = 3, h^2 = 1 - t^2, QUART(t) = 0."""
    e = sp.expand(e)
    if e == 0:
        return sp.Integer(0)
    poly = sp.Poly(e, s, h, t)
    out = 0
    for (ps, ph, pt), c in poly.terms():
        out += c * 3**(ps // 2) * s**(ps % 2) * (1 - t**2)**(ph // 2) * h**(ph % 2) * t**pt
    out = sp.expand(out)
    if out == 0:
        return sp.Integer(0)
    poly = sp.Poly(out, s, h, t)
    res = 0
    for a in (0, 1):
        for b in (0, 1):
            coeff = sum(c * t**pt for (ps, ph, pt), c in poly.terms() if ps == a and ph == b)
            if coeff != 0:
                r = sp.rem(sp.Poly(coeff, t), sp.Poly(QUART, t)).as_expr()
                res += s**a * h**b * r
    return sp.expand(res)


def is_zero(e):
    num, den = sp.fraction(sp.together(e))
    return nf_poly(num) == 0


# ------------------------------------------------- certified enclosures of t*, h*, sqrt3
def bisect_root(fun, lo, hi, iters):
    """fun increasing on [lo, hi] with fun(lo) < 0 < fun(hi), exact rationals."""
    assert fun(lo) < 0 < fun(hi)
    for _ in range(iters):
        mid = (lo + hi) / 2
        if fun(mid) < 0:
            lo = mid
        else:
            hi = mid
    return lo, hi


ITERS = 200
QUARTF = lambda x: 4 * x**4 - 4 * x**3 + 3 * x**2 + 4 * x - 4  # increasing on [0, oo)
T_LO, T_HI = bisect_root(QUARTF, Fr(2, 3), Fr(1), ITERS)
S_LO, S_HI = bisect_root(lambda x: x * x - 3, Fr(1), Fr(2), ITERS)
# h = sqrt(1 - t^2) is decreasing in t: enclose sqrt(1 - T_HI^2) .. sqrt(1 - T_LO^2)
H_LO, _ = bisect_root(lambda x: x * x - (1 - T_HI**2), Fr(0), Fr(1), ITERS)
_, H_HI = bisect_root(lambda x: x * x - (1 - T_LO**2), Fr(0), Fr(1), ITERS)


ROUND_BITS = 320   # endpoints are rounded outward to multiples of 2^-ROUND_BITS


def _floor(x):
    return Fr((x.numerator << ROUND_BITS) // x.denominator, 1 << ROUND_BITS)


def _ceil(x):
    return Fr(-((-x.numerator << ROUND_BITS) // x.denominator), 1 << ROUND_BITS)


class I:
    """Closed interval [lo, hi] with rational endpoints. Every operation is exact and the
    result is rounded outward to a dyadic grid, so the true value always stays inside."""
    def __init__(self, lo, hi=None):
        lo = Fr(lo)
        hi = lo if hi is None else Fr(hi)
        assert lo <= hi
        self.lo = lo if lo.denominator == 1 else _floor(lo)
        self.hi = hi if hi.denominator == 1 else _ceil(hi)

    def __add__(a, b):
        b = b if isinstance(b, I) else I(b)
        return I(a.lo + b.lo, a.hi + b.hi)
    __radd__ = __add__

    def __neg__(a):
        return I(-a.hi, -a.lo)

    def __sub__(a, b):
        return a + (-(b if isinstance(b, I) else I(b)))

    def __rsub__(a, b):
        return I(b) - a

    def __mul__(a, b):
        b = b if isinstance(b, I) else I(b)
        ps = [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
        return I(min(ps), max(ps))
    __rmul__ = __mul__

    def inv(a):
        assert a.lo > 0 or a.hi < 0, "division by an interval containing 0"
        return I(1 / a.hi, 1 / a.lo)

    def __truediv__(a, b):
        b = b if isinstance(b, I) else I(b)
        return a * b.inv()

    def pos(self):
        return self.lo > 0

    def width(self):
        return self.hi - self.lo


ENV = {t: I(T_LO, T_HI), h: I(H_LO, H_HI), s: I(S_LO, S_HI)}


def ev(e):
    """Evaluate a sympy expression in t, h, s (and the coordinates x_j) over rational intervals."""
    if e.is_Rational:
        return I(Fr(int(e.p), int(e.q)))
    if e.is_Symbol:
        return ENV[e]
    if e.is_Add:
        acc = I(0)
        for a in e.args:
            acc = acc + ev(a)
        return acc
    if e.is_Mul:
        acc = I(1)
        for a in e.args:
            acc = acc * ev(a)
        return acc
    if e.is_Pow:
        base, ex = e.args
        assert ex.is_Integer
        b = ev(base)
        n = int(ex)
        r = I(1)
        for _ in range(abs(n)):
            r = r * b
        return r if n >= 0 else r.inv()
    raise ValueError(e)


# ------------------------------------------------------------------- the configuration
X = sp.symbols('x0:27')
P = [sp.Matrix(X[3 * i:3 * i + 3]) for i in range(9)]
FACES = [(3, 4, 5), (6, 7, 8), (0, 5, 3), (1, 3, 4), (2, 4, 5), (0, 8, 6), (1, 6, 7), (2, 7, 8),
         (0, 3, 6), (1, 4, 7), (2, 5, 8), (1, 3, 6), (2, 4, 7), (0, 5, 8)]
NAMES = ["T", "Bot", "U0", "U1", "U2", "L0", "L1", "L2", "V0", "V1", "V2", "W0", "W1", "W2"]
ACT = [0, 1, 8, 9, 10, 11, 12, 13]
half = sp.Rational(1, 2)
COS = {0: (1, 0), 1: (-half, s / 2), 2: (-half, -s / 2)}            # A_k angles
BCS = {0: (half, s / 2), 1: (-1, 0), 2: (half, -s / 2)}               # B_k, C_k angles
PSTAR = [(1, 0, 0), (-half, s / 2, 0), (-half, -s / 2, 0)] + \
        [(t * BCS[k][0], t * BCS[k][1], h) for k in range(3)] + \
        [(t * BCS[k][0], t * BCS[k][1], -h) for k in range(3)]
SUB = {X[3 * i + j]: PSTAR[i][j] for i in range(9) for j in range(3)}


def face_DQ(f):
    a, b, c = [P[i] for i in f]
    n = (b - a).cross(c - a)
    return n.dot(a), n.dot(n)


def main():
    import functools, builtins
    global print
    print = functools.partial(builtins.print, flush=True)
    print("enclosure widths: t", float(T_HI - T_LO), "h", float(H_HI - H_LO))
    # orientation: D > 0 at P*
    D_at, Q_at, SIGN = {}, {}, {}
    for k, f in enumerate(FACES):
        D, Q = face_DQ(f)
        Ds = sp.expand(D.subs(SUB))
        sg = 1 if ev(Ds).pos() else -1
        assert (ev(sg * Ds)).pos()
        SIGN[k] = sg
        D_at[k], Q_at[k] = nf_poly(sg * Ds), nf_poly(Q.subs(SUB))

    # 1. distances: d^2 = D^2 / Q; active iff D^2 - h^2 Q = 0 (exact), else D^2 - h^2 Q > 0
    for k in range(14):
        gap = nf_poly(D_at[k]**2 - h**2 * Q_at[k])
        if k in ACT:
            assert gap == 0, NAMES[k]
        else:
            assert ev(gap).pos(), NAMES[k]
    print("1. active faces (d = h* exactly):", [NAMES[k] for k in ACT],
          "; slopes have d > h* (certified)")

    # gradient of d_f at P*: h grad D / D - h^3 grad Q / (2 D^2)   (using sqrt Q = D / h)
    def grad_d(k):
        D, Q = face_DQ(FACES[k])
        D = SIGN[k] * D
        gD = [sp.diff(D, v).subs(SUB) for v in X]
        gQ = [sp.diff(Q, v).subs(SUB) for v in X]
        Dk = D_at[k]
        return [h * a / Dk - h**3 * b / (2 * Dk**2) for a, b in zip(gD, gQ)]

    GD = {k: grad_d(k) for k in ACT}

    # tangent basis (27 x 18) and the gauge-fixing columns
    def tb(i):
        if i < 3:
            c, sn = COS[i]
            return [(-sn, c, 0), (0, 0, 1)]
        k = (i - 3) % 3
        c, sn = BCS[k]
        z = 1 if i < 6 else -1
        return [(-sn, c, 0), (-z * h * c, -z * h * sn, t)]
    TB = []
    for i in range(9):
        for vec in tb(i):
            col = [0] * 27
            for j in range(3):
                col[3 * i + j] = vec[j]
            TB.append(col)
    dot = lambda u, v: sum(a * b for a, b in zip(u, v))

    # 2. KKT multipliers: tangential components of lam_T sum_T grad + lam_V sum_V grad
    gT = [sum(GD[k][j] for k in (0, 1)) for j in range(27)]
    gV = [sum(GD[k][j] for k in ACT[2:]) for j in range(27)]
    # meridian tangent at B0 (column index 2*3+1)
    col = TB[2 * 3 + 1]
    aT, aV = dot(gT, col), dot(gV, col)
    r = sp.together(-aV / aT)          # r = lam_T / lam_V
    lamT, lamV = r / (2 * r + 6), 1 / (2 * r + 6)
    for c_ in TB:
        assert is_zero(lamT * dot(gT, c_) + lamV * dot(gV, c_))
    print("2. KKT: lam_T / lam_V = r, r =", sp.simplify(r))
    print("   lam_T ~", sp.N(lamT.subs({t: sp.Rational(str(float(T_LO))), h: sp.sqrt(1 - sp.Rational(str(float(T_LO)))**2), s: sp.sqrt(3)}), 12),
          "; r certified positive:", ev(sp.together(r)).pos())
    assert ev(sp.together(r)).pos()

    # 3. rank of the 8 x 18 tangent Jacobian: a nonzero 7 x 7 minor (certified)
    J = sp.Matrix([[dot(GD[k], c_) for c_ in TB] for k in ACT])
    # columns to use for the minor are found numerically, the minor is certified exactly
    import itertools
    Jn = sp.matrix2numpy(J.subs({t: 0.71786982122624549, h: 0.69617736229541271, s: 3**0.5}), dtype=float)
    import numpy as np
    rows = list(range(7))
    best = None
    for cols in itertools.combinations(range(18), 7):
        m = abs(np.linalg.det(Jn[np.ix_(rows, cols)]))
        if best is None or m > best[0]:
            best = (m, cols)
        if m > 1e-3:
            break
    minor = sp.Matrix([[J[i, j] for j in best[1]] for i in rows])
    md = ev(sp.together(minor.det(method='berkowitz')))
    assert md.pos() or (-md).pos()
    print("3. rank 7: the 7 x 7 minor on columns", best[1], "is certified nonzero;",
          "rank <= 7 by the KKT relation of 2.")

    # 4. Hessian of the Lagrangian of F = - sum lam_f sqrt(Q_f) / D_f, evaluated in exact
    #    rational interval arithmetic (polynomial derivatives are symbolic, values are intervals)
    for i_ in range(9):
        for j_ in range(3):
            ENV[X[3 * i_ + j_]] = ev(sp.sympify(PSTAR[i_][j_]))
    lamI = {k: ev(sp.together(lamT if k in (0, 1) else lamV)) for k in ACT}
    hI = ENV[h]
    H = [[I(0) for _ in range(27)] for _ in range(27)]
    gradF = [I(0) for _ in range(27)]
    for k in ACT:
        D, Q = face_DQ(FACES[k])
        D = sp.expand(SIGN[k] * D)
        Q = sp.expand(Q)
        gD = [ev(sp.diff(D, v)) for v in X]
        gQ = [ev(sp.diff(Q, v)) for v in X]
        Dk = ev(D)                                  # D at P* (interval)
        sq = Dk / hI                                # sqrt(Q) at P*, since d_f = h*
        Qk = sq * sq
        for a in range(27):
            gradF[a] = gradF[a] - lamI[k] * (gQ[a] / (2 * sq * Dk) - sq * gD[a] / (Dk * Dk))
        for a in range(27):
            for b in range(a, 27):
                hd = sp.diff(D, X[a], X[b])
                hq = sp.diff(Q, X[a], X[b])
                HDab = ev(hd) if hd != 0 else I(0)
                HQab = ev(hq) if hq != 0 else I(0)
                val = (HQab / (2 * sq * Dk) - gQ[a] * gQ[b] / (4 * Qk * sq * Dk)
                       - (gQ[a] * gD[b] + gD[a] * gQ[b]) / (2 * sq * Dk * Dk)
                       - sq * HDab / (Dk * Dk) + 2 * sq * gD[a] * gD[b] / (Dk * Dk * Dk))
                H[a][b] = H[a][b] - lamI[k] * val
                if b != a:
                    H[b][a] = H[a][b]
    print("   Hessian entries evaluated")
    # sphere multipliers mu_i = <grad_i F, p_i> / 2 (the tangential part of grad F is zero by 2.)
    for i_ in range(9):
        pi = [ENV[X[3 * i_ + j_]] for j_ in range(3)]
        m_ = (gradF[3 * i_] * pi[0] + gradF[3 * i_ + 1] * pi[1] + gradF[3 * i_ + 2] * pi[2]) / 2
        for j_ in range(3):
            H[3 * i_ + j_][3 * i_ + j_] = H[3 * i_ + j_][3 * i_ + j_] - 2 * m_
    keep = [c for idx, c in enumerate(TB) if idx not in (0, 1, 3)]   # drop A0 (2), A1 vertical
    Bc = [[ev(sp.sympify(c[r_])) for r_ in range(27)] for c in keep]   # 15 columns
    n = 15
    HB = [[sum((H[a][b] * Bc[j][b] for b in range(27) if Bc[j][b].lo != 0 or Bc[j][b].hi != 0),
               I(0)) for j in range(n)] for a in range(27)]
    M = [[sum((Bc[i][a] * HB[a][j] for a in range(27) if Bc[i][a].lo != 0 or Bc[i][a].hi != 0),
              I(0)) for j in range(n)] for i in range(n)]
    # certified Cholesky of -M in rational interval arithmetic
    A = [[-M[i][j] for j in range(n)] for i in range(n)]
    pivots = []
    for k in range(n):
        piv = A[k][k]
        assert piv.pos(), f"pivot {k} not certified positive"
        pivots.append(piv)
        for i in range(k + 1, n):
            f = A[i][k] / piv
            for j in range(k + 1, n):
                A[i][j] = A[i][j] - f * A[k][j]
    print("4. -Hessian on the 15-dim slice: 15 Cholesky pivots certified positive;",
          "smallest pivot >=", float(min(p.lo for p in pivots)),
          "; max interval width", float(max(p.width() for p in pivots)))
    print("Conclusion: P* is a strict local maximum of -sum lam_f / d_f modulo rotations,",
          "hence a strict local minimum of the covering radius modulo rotations.")


if __name__ == "__main__":
    main()
