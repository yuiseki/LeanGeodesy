#!/usr/bin/env python3
"""Generate covering certificates (CoverTree literals) for rational configurations.

The output is data for LeanGeodesy.Spherical.CoveringCert.checkCover. Nothing here is
trusted: Lean re-checks every leaf in exact rational arithmetic. The search uses the same
leaf test as the checker (fractions only, no floating point), but any other method would do.

usage: gen_cert.py NAME R   (NAME in tetra, octa, ...)  prints a Lean term for the tree
       function `fun a b => ...` over (Fin 3) x Bool.
"""
import sys
from fractions import Fraction as F

CONFIGS = {
    "tetra": [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)],
    "octa": [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)],
}


def rot(a, q):
    return [q, (q[1], q[2], q[0]), (q[2], q[0], q[1])][a]


def leaf_ok(R, q, t, u0, u1, v0, v1):
    L = q[0] * t + min(q[1] * u0, q[1] * u1) + min(q[2] * v0, q[2] * v1)
    M = t * t + max(u0 * u0, u1 * u1) + max(v0 * v0, v1 * v1)
    n2 = q[0] ** 2 + q[1] ** 2 + q[2] ** 2
    return L >= 0 and R * n2 * M <= L * L


def lit(x):
    x = F(x)
    s = f"{x.numerator}" if x.denominator == 1 else f"{x.numerator}/{x.denominator}"
    return f"({s} : ℚ)"


def build(R, qs, a, t, u0, u1, v0, v1, depth=0):
    for i, q in enumerate(qs):
        if leaf_ok(R, rot(a, q), t, u0, u1, v0, v1):
            return ("leaf", i)
    if depth > 60:
        raise SystemExit("no certificate found: R too close to the true value")
    if u1 - u0 >= v1 - v0:
        m = (u0 + u1) / 2
        return ("cutU", m, build(R, qs, a, t, u0, m, v0, v1, depth + 1),
                build(R, qs, a, t, m, u1, v0, v1, depth + 1))
    m = (v0 + v1) / 2
    return ("cutV", m, build(R, qs, a, t, u0, u1, v0, m, depth + 1),
            build(R, qs, a, t, u0, u1, m, v1, depth + 1))


def render(t):
    if t[0] == "leaf":
        return f".leaf {t[1]}"
    return f".{t[0]} {lit(t[1])} ({render(t[2])}) ({render(t[3])})"


def leaves(t):
    return 1 if t[0] == "leaf" else leaves(t[2]) + leaves(t[3])


def main():
    name, R = sys.argv[1], F(sys.argv[2])
    qs = [tuple(F(c) for c in q) for q in CONFIGS[name]]
    trees = {}
    for a in range(3):
        for b in (True, False):
            trees[(a, b)] = build(R, qs, a, F(1 if b else -1), F(-1), F(1), F(-1), F(1))
    total = sum(leaves(t) for t in trees.values())
    print(f"-- {name}: R = {R}, {total} leaves", file=sys.stderr)
    lines = ["fun a b => match a.val, b with"]
    for a in range(3):
        for b in (True, False):
            lines.append(f"  | {a}, {'true' if b else 'false'} => {render(trees[(a, b)])}")
    lines.append("  | _, _ => .leaf 0")
    print("\n".join(lines))


main()
