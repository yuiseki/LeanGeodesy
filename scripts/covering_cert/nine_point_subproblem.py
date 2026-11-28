#!/usr/bin/env python3
"""Numerical study of the subproblems of `NinePointElim.lean` (numerical only).

For fixed B, C (and hence fixed triangle planes) the k-th subproblem minimizes
`sideVal k = 1/d(A_k B_k C_k) + 1/d(A_k B_{k-1} C_{k-1})` over A_k on the
sphere, subject to `SubFeasible k`: the planes of the four faces through A_k
(computed from their vertices) have the origin and the B, C off the face
strictly inside, and A_k is strictly inside both triangle planes.

Two questions:
1. At Jucovic's B, C, is Jucovic's A_k the global minimizer
   (`JucovicSubMinimal`)? A grid over the sphere, then local refinement.
2. For other B, C, is the minimizer interior (all slacks positive), where the
   Lagrange condition gives tangency (Gram determinant 0), or on the boundary
   of the support conditions, where tangency need not hold?

Usage: nine_point_subproblem.py SAMPLES SEED
"""
import sys
import numpy as np
from scipy.optimize import minimize
from nine_point_search import FACES, P_STAR, H_STAR, planes, slacks

SIDES = {0: (8, 13), 1: (9, 11), 2: (10, 12)}


def faces_of(k):
    return [f for f, vs in enumerate(FACES) if k in vs]


def sub_slacks(P, k):
    """Slacks of SubFeasible k (strict conditions are slack > 0)."""
    n, d, nn = planes(P)
    out = []
    for f in faces_of(k):
        out.append(d[f])
        out.append(nn[f])
        for i in range(3, 9):
            if i not in FACES[f]:
                out.append(d[f] - n[f] @ P[i])
    for f in (0, 1):
        out.append(d[f] - n[f] @ P[k])
    return np.array(out)


def side_val(P, k):
    _, d, _ = planes(P)
    a, b = SIDES[k]
    if d[a] <= 1e-12 or d[b] <= 1e-12:
        return 1e6
    return 1 / d[a] + 1 / d[b]


def gram(P, k):
    n, d, _ = planes(P)
    a, b = SIDES[k]
    c = n[a] @ n[b]
    return 1 + 2 * d[a] * d[b] * c - d[a]**2 - d[b]**2 - c**2


def with_A(P, k, A):
    Q = P.copy()
    Q[k] = A / np.linalg.norm(A)
    return Q


def minimize_sub(P, k, A0, eps=1e-9):
    cons = [{"type": "ineq", "fun": lambda a: sub_slacks(with_A(P, k, a), k) - eps}]
    r = minimize(lambda a: side_val(with_A(P, k, a), k), A0, method="SLSQP", constraints=cons,
                 options={"maxiter": 1000, "ftol": 1e-15})
    Q = with_A(P, k, r.x)
    return side_val(Q, k), Q, sub_slacks(Q, k).min()


def grid_min(P, k, m=400):
    best = (np.inf, None)
    for th in np.linspace(0, np.pi, m):
        for ph in np.linspace(0, 2 * np.pi, 2 * m, endpoint=False):
            A = np.array([np.sin(th) * np.cos(ph), np.sin(th) * np.sin(ph), np.cos(th)])
            Q = with_A(P, k, A)
            if sub_slacks(Q, k).min() > 0:
                v = side_val(Q, k)
                if v < best[0]:
                    best = (v, A)
    return best


def main():
    samples = int(sys.argv[1])
    rng = np.random.default_rng(int(sys.argv[2]))
    print(f"2/h* = {2 / H_STAR:.13f}")
    # 1. Jucovic's B, C
    for k in range(3):
        v, A = grid_min(P_STAR, k)
        vr, Q, sl = minimize_sub(P_STAR, k, A)
        print(f"Jucovic B,C, k={k}: grid min {v:.10f}, refined {vr:.13f} (diff to 2/h* "
              f"{vr - 2 / H_STAR:+.2e}), |A - A*| {np.linalg.norm(Q[k] - P_STAR[k]):.2e}, "
              f"min slack {sl:.3e}, gram {gram(Q, k):+.2e}")
    # 2. perturbed B, C
    interior = boundary = 0
    tight_interior = 0
    worst_interior_gram = 0.0
    for _ in range(samples):
        P = P_STAR + rng.choice([0.05, 0.15, 0.3]) * rng.normal(size=(9, 3))
        P = P / np.linalg.norm(P, axis=1)[:, None]
        if slacks(P, "relaxed").min() <= 1e-6:
            continue
        k = int(rng.integers(3))
        best = None
        for _ in range(12):
            A0 = P[k] + 0.3 * rng.normal(size=3)
            if sub_slacks(with_A(P, k, A0), k).min() <= 0:
                continue
            res = minimize_sub(P, k, A0)
            if res[2] > -1e-12 and (best is None or res[0] < best[0]):
                best = res
        if best is None:
            continue
        v, Q, sl = best
        g = gram(Q, k)
        if sl > 1e-6:
            interior += 1
            worst_interior_gram = max(worst_interior_gram, abs(g))
            tight_interior += abs(g) < 1e-7
        else:
            boundary += 1
    print(f"perturbed B,C: minimizer interior {interior} (Gram |.| < 1e-7 in {tight_interior}, "
          f"max |Gram| {worst_interior_gram:.2e}), on the support boundary {boundary}")


if __name__ == "__main__":
    main()
