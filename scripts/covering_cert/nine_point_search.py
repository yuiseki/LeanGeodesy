#!/usr/bin/env python3
"""Numerical counterexample search for the repaired nine-point inequalities.

Numerical only (floating point, local optimization): nothing here is a proof,
and finding no counterexample is not evidence of truth beyond the starts
tried. The definitions follow `LeanGeodesy/Spherical/NinePoint.lean` and
`NinePointElim.lean`:

* strict (`TTPHarmonic`): for each of the 14 labelled faces, the plane through
  its three vertices has the origin strictly inside (`d_f > 0`) and the six
  other points strictly inside;
* relaxed (`RelaxedHarmonic`): the same without the cross-A conditions
  (an equatorial point A_j against a plane through another A_k).

Strict inequalities are imposed with a margin `eps` (slack >= eps); smaller
`eps` lets the search approach the boundary of the open feasible set. The
plane of a face is computed from its vertices, so it is the unique plane of
the definition (positive scaling does not change `1/d`).

The objective is the active sum `sum_f w_f / d_f` with the KKT weights
`lambda_T`, `lambda_V` (`2 lambda_T + 6 lambda_V = 1`). The script reports
the smallest feasible value found per start family, to be compared with
`1/h*`.

Usage: nine_point_search.py STARTS_PER_FAMILY SEED [WORKERS]
"""
import sys
import multiprocessing as mp
import numpy as np
from scipy.optimize import minimize, brentq

FACES = [(3, 4, 5), (6, 7, 8), (0, 5, 3), (1, 3, 4), (2, 4, 5), (0, 8, 6), (1, 6, 7), (2, 7, 8),
         (0, 3, 6), (1, 4, 7), (2, 5, 8), (1, 3, 6), (2, 4, 7), (0, 5, 8)]
ACTIVE = [0, 1, 8, 9, 10, 11, 12, 13]

T_STAR = brentq(lambda t: 4 * t**4 - 4 * t**3 + 3 * t**2 + 4 * t - 4, 0.5, 1.0)
H_STAR = np.sqrt(1 - T_STAR**2)
_r = 9 / 4 + 15 * T_STAR / 8 - 3 * T_STAR**2 / 2 - 3 * T_STAR**3 / 2
LAM_T, LAM_V = _r / (2 * _r + 6), 1 / (2 * _r + 6)
W = np.array([LAM_T, LAM_T] + [LAM_V] * 6)


def jucovic(t):
    h = np.sqrt(1 - t * t)
    s3 = np.sqrt(3)
    return np.array([[1, 0, 0], [-.5, s3 / 2, 0], [-.5, -s3 / 2, 0],
                     [t / 2, s3 / 2 * t, h], [-t, 0, h], [t / 2, -s3 / 2 * t, h],
                     [t / 2, s3 / 2 * t, -h], [-t, 0, -h], [t / 2, -s3 / 2 * t, -h]])


P_STAR = jucovic(T_STAR)


def pairs(mode):
    """The (face, point) pairs that must be strictly inside."""
    out = []
    for f, vs in enumerate(FACES):
        for i in range(9):
            if i in vs:
                continue
            if mode == "relaxed" and f >= 2 and i < 3:
                continue
            out.append((f, i))
    return out


PAIRS = {m: pairs(m) for m in ("strict", "relaxed")}


def unpack(x):
    P = x.reshape(9, 3)
    return P / np.linalg.norm(P, axis=1)[:, None]


def planes(P):
    """Unit normals oriented so that the offset is >= 0, and offsets."""
    a, b, c = (P[[f[j] for f in FACES]] for j in range(3))
    n = np.cross(b - a, c - a)
    nn = np.linalg.norm(n, axis=1)
    n = n / np.maximum(nn, 1e-300)[:, None]
    d = np.einsum("ij,ij->i", n, a)
    sgn = np.where(d < 0, -1.0, 1.0)
    return n * sgn[:, None], d * sgn, nn


def slacks(P, mode):
    n, d, nn = planes(P)
    pr = PAIRS[mode]
    s = [d[f] - n[f] @ P[i] for f, i in pr]
    return np.concatenate([d, np.array(s), nn])  # offsets, inside slacks, face areas


def objective(P):
    _, d, _ = planes(P)
    da = d[ACTIVE]
    if (da <= 1e-12).any():
        return 1e6
    return float(W @ (1 / da))


def solve(P0, mode, eps, pin=None):
    """Minimize the active sum; `pin = (j, value)` also forces slack `j` to equal
    `value`, which keeps the search on one stratum near the boundary."""
    cons = [{"type": "ineq", "fun": lambda x: slacks(unpack(x), mode) - eps}]
    if pin is not None:
        j, val = pin
        cons.append({"type": "eq", "fun": lambda x: slacks(unpack(x), mode)[j] - val})
    r = minimize(lambda x: objective(unpack(x)), P0.ravel(), method="SLSQP",
                 constraints=cons, options={"maxiter": 2000, "ftol": 1e-15})
    P = unpack(r.x)
    sl = slacks(P, mode)
    feasible = sl.min() >= eps * (1 - 1e-6) - 1e-12
    if pin is not None:
        feasible = feasible and abs(sl[pin[0]] - pin[1]) < 1e-9
    return objective(P), P, feasible, sl


def gram_dist(P):
    """Distance from Jucovic's configuration up to rotation, for this labelling."""
    return float(np.abs(P @ P.T - P_STAR @ P_STAR.T).max())


def start(family, rng):
    s3 = np.sqrt(3)
    if family == "near_coincident":
        P = P_STAR + 0.05 * rng.normal(size=(9, 3))
        i, j = rng.choice(9, 2, replace=False)
        P[i] = P[j] + rng.uniform(0.02, 0.15) * rng.normal(size=3)
    elif family == "thin_face":
        P = P_STAR + 0.05 * rng.normal(size=(9, 3))
        f = FACES[rng.integers(14)]
        m = P[list(f)].mean(axis=0)
        k = rng.uniform(0.1, 0.5)
        for v in f:
            P[v] = m + k * (P[v] - m)
    elif family == "origin_near_boundary":
        P = P_STAR + 0.1 * rng.normal(size=(9, 3))
        u = rng.normal(size=3)
        P = P + rng.uniform(0.3, 0.8) * u / np.linalg.norm(u)
    elif family == "asymmetric_triangles":
        t1, t2 = rng.uniform(0.3, 0.98, 2)
        P = jucovic(t1)
        P[6:] = jucovic(t2)[6:]
        P = P + 0.1 * rng.normal(size=(9, 3))
    elif family == "near_coplanar_faces":
        P = P_STAR + 0.05 * rng.normal(size=(9, 3))
        # flatten towards one face plane: move the points of a neighbouring face onto it
        f = rng.integers(14)
        n, d, _ = planes(P_STAR)
        for i in range(9):
            if rng.random() < 0.3:
                P[i] = P[i] - rng.uniform(0.5, 1.0) * (n[f] @ P[i] - d[f]) * n[f]
    else:  # far_random: random positions with the rough layout of the type
        az = rng.uniform(0, 2 * np.pi, 3)
        az.sort()
        A = np.c_[np.cos(az), np.sin(az), rng.uniform(-0.5, 0.5, 3)]
        tb = rng.uniform(0.2, 0.95, 3)
        tc = rng.uniform(0.2, 0.95, 3)
        bz = rng.uniform(0.2, 1, 3)
        cz = -rng.uniform(0.2, 1, 3)
        mid = az + np.diff(np.r_[az, az[0] + 2 * np.pi]) / 2
        B = np.c_[tb * np.cos(mid), tb * np.sin(mid), bz]
        C = np.c_[tc * np.cos(mid + rng.normal(0, .3, 3)), tc * np.sin(mid + rng.normal(0, .3, 3)), cz]
        P = np.r_[A, B, C]
    return P / np.linalg.norm(P, axis=1)[:, None]


FAMILIES = ["near_coincident", "thin_face", "origin_near_boundary", "asymmetric_triangles",
            "near_coplanar_faces", "far_random"]


def run(args):
    family, seed, n = args
    rng = np.random.default_rng(seed)
    res = []
    for _ in range(n):
        P0 = start(family, rng)
        for mode in ("strict", "relaxed"):
            for eps in (1e-3, 1e-6):
                v, P, ok, sl = solve(P0, mode, eps)
                if ok:
                    res.append((family, mode, eps, v, gram_dist(P), float(sl.min()),
                                gram_dist(P0)))
            # boundary strata: pin one slack (an offset, an inside condition, or a
            # face area) to a small value
            m = len(slacks(P0, mode))
            j = int(rng.integers(m))
            val = float(rng.choice([1e-2, 1e-3]))
            v, P, ok, sl = solve(P0, mode, val / 10, pin=(j, val))
            if ok:
                kind = "offset" if j < 14 else ("area" if j >= m - 14 else "inside")
                res.append((family, mode, "pin-" + kind, v, gram_dist(P), float(sl.min()),
                            gram_dist(P0)))
    return res


def main():
    n = int(sys.argv[1])
    seed = int(sys.argv[2])
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    jobs = [(fam, seed * 1000 + 17 * k + j, max(1, n // 4)) for k, fam in enumerate(FAMILIES)
            for j in range(4)]
    with mp.Pool(workers) as pool:
        out = [r for rs in pool.map(run, jobs) for r in rs]
    print(f"1/h* = {1 / H_STAR:.13f}; lambda_T = {LAM_T:.12f}, lambda_V = {LAM_V:.12f}")
    print("family mode eps: feasible ends, starts far (Gram > 0.3), min value, "
          "min - 1/h*, Gram distance of argmin, ends with value < 1/h* - 1e-9")
    for fam in FAMILIES:
        for mode in ("strict", "relaxed"):
            for eps in (1e-3, 1e-6, "pin-offset", "pin-inside", "pin-area"):
                rs = [r for r in out if r[0] == fam and r[1] == mode and r[2] == eps]
                if not rs:
                    print(f"{fam} {mode} {eps}: no feasible end")
                    continue
                best = min(rs, key=lambda r: r[3])
                far = sum(r[6] > 0.3 for r in rs)
                bad = sum(r[3] < 1 / H_STAR - 1e-9 for r in rs)
                print(f"{fam} {mode} {eps}: {len(rs)} ends, {far} far starts, "
                      f"min {best[3]:.13f}, diff {best[3] - 1 / H_STAR:+.2e}, "
                      f"gram {best[4]:.2e}, below {bad}")
    allv = [r for r in out]
    worst = min(allv, key=lambda r: r[3])
    print(f"overall: {len(allv)} feasible ends; min {worst[3]:.13f} "
          f"({worst[0]}, {worst[1]}, {worst[2]}); 1/h* {1 / H_STAR:.13f}")
    pinned = [r for r in out if isinstance(r[2], str)]
    if pinned:
        wp = min(pinned, key=lambda r: r[3])
        print(f"pinned strata: {len(pinned)} feasible ends; min {wp[3]:.13f} "
              f"({wp[0]}, {wp[1]}, {wp[2]}); margin above 1/h*: {wp[3] - 1 / H_STAR:.3e}")


if __name__ == "__main__":
    main()
