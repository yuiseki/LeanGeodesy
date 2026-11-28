# Global optimality of spherical coverings: what is done, what is missing

Written 2026-11-28. "Proved" below means proved in this repository and checked
by Lean (`docs/COVERING.md`); literature claims carry the labels of the surveys
in this folder (`COVERING_LITERATURE.md`, `COVERING_N9_WIMMER_NACO.md`).

## 1. Proved here

| `N` | Statement | Theorem | Method |
| --- | --- | --- | --- |
| 2, 3 | `(∃ p, IsCovering p r) ↔ π/2 ≤ r` | `covering_2_optimal`, `covering_3_optimal` | three points lie in a plane, hence in a closed hemisphere; points summing to zero cover at `π/2` |
| 4 | `(∃ p, IsCovering p r) ↔ arccos (1/3) ≤ r` | `covering_4_optimal` | balanced face normals of the tetrahedron spanned by the four points (Euler's `R ≥ 3r`), with the exact tetrahedron radius from the octahedron |

The reusable piece is `cos_mul_sum_norm_le_of_halfSpaces`: supporting
half-spaces `⟪V k, p i⟫ ≤ c k` give `cos r Σ ‖V k‖ ≤ Σ c k` for every covering.
For four points the normals are the gradients of the oriented volume, which sum
to zero for every configuration, so no case analysis on the combinatorics is
needed. That is what fails beyond four points.

## 2. L. Fejes Tóth's bound, and what it needs

The bound (L. Fejes Tóth 1943, as quoted by Musin, arXiv:1604.02776, Thm 1.1):
every covering of `S²` by `N` caps of radius `r` has
`cos r ≤ cot(ω_N)/√3` with `ω_N = Nπ/(6N − 12)`. It is tight for `N = 4, 6, 12`
(at `N = 4`, `ω = π/3` and `cot(π/3)/√3 = 1/3`, the value proved above).

The classical proof, step by step, with what Lean and Mathlib have:

| Step | Content | Status |
| --- | --- | --- |
| 1 | Holes bound the radius: the circumcentre direction of each hull facet is a hole, so `r ≥` its angular circumradius | have it (`cos_le_of_supportPlane`) |
| 2 | Hull facets of `N` points in convex position, containing the origin in the interior, project radially to a triangulation of `S²` (non-triangular facets triangulated) | missing: no facet structure of 3-dimensional convex hulls in Mathlib (only exposed faces in general, `Analysis/Convex/Exposed.lean`) |
| 3 | The triangulation has `2N − 4` triangles | missing: Euler's formula for polytopes or sphere triangulations (Mathlib's Euler characteristics are homological) |
| 4 | Areas of the triangles sum to `4π` | missing: spherical triangle area and Girard's theorem (area = excess), or the measure of cones over facets (Mathlib has the sphere measure `Measure.toSphere`, but no cap or triangle area formula) |
| 5 | A spherical triangle of circumradius `≤ r` has area `≤` that of the equilateral one of circumradius `r`, which is increasing in `r` | missing: a trigonometric inequality; elementary once areas exist |
| 6 | Degenerate configurations: points in a hemisphere (radius `≥ π/2`, done: `pi_div_two_le_of_hemisphere`), coincident points (done: `isCovering_comp_of_range_eq`), non-triangular facets (step 2) | partly done |

Steps 3 and 4 can be traded for each other: the angle sum at every vertex is
`2π` and the excess of a triangle is its area, so `Σ area = Σ (angles) − Fπ =
2πN − Fπ`, which is `4π` exactly when `F = 2N − 4`. A route that avoids measure
theory: define the area of a spherical triangle as its excess, prove the vertex
angle sums (a local fact about the fan of facets at a vertex), and prove
`F = 2N − 4` combinatorially. A route that avoids Euler's formula: prove
`Σ area = 4π` by measure (the cones over the facets partition space up to null
sets) and read off `F` from it. Either is a substantial library, comparable to
or larger than everything in `Spherical/` so far.

The cheapest next increments:

1. Step 5 alone, with area defined as excess, as a self-contained trigonometric
   theorem (no triangulation needed).
2. The `N = 6` case through a different reduction, if one exists, in the style
   of `N = 4`: a balanced family of normals whose weighted facet distances can
   be computed from the points. For six points the face structure varies (an
   octahedron-like or other simplicial type, or a non-simplicial hull), so a
   case split on the combinatorial type looks unavoidable. Not attempted.
3. `N = 12` needs everything in the table.

## 3. N = 9

### 3.1 Proved here, unconditionally (`Spherical/Jucovic9.lean`)

Jucovič's configuration (Mat.-fyz. časopis 10 (1960), §2, read in the original
Slovak and checked against its figures): an equilateral triangle `A₀A₁A₂` on
the equator and the apexes `Bₖ`, `Cₖ` of congruent isosceles triangles over its
sides, legs `68°58'`, radius `45°53'`; the graph has two edge lengths, `45°53'`
and `42°38'`, and 12 congruent parts. In coordinates `Aₖ = (cos θₖ, sin θₖ, 0)`,
`Bₖ = (t cos(θₖ + π/3), t sin(θₖ + π/3), h)`, `Cₖ` mirrored, `t² + h² = 1`.

| Statement | Theorem |
| --- | --- |
| `4t⁴ - 4t³ + 3t² + 4t - 4` is strictly increasing on `[0, ∞)`; its only nonnegative root `t⋆` lies in `(2/3, 1)`, in fact in `(0.7178, 0.7179)` | `jucovicQuartic_strictMonoOn`, `tStar_mem`, `eq_tStar_of_jucovicQuartic`, `tStar_bracket` |
| `h⋆ = √(1 - t⋆²)` is a root of `16x⁸ - 72x⁶ + 129x⁴ - 66x² + 9` (Rathbun's numerically identified polynomial, now proved for this configuration: it is `f(t⋆) f(-t⋆)` in `h⋆²`) | `hStar_octic` |
| the nine points lie on `S²` and are distinct | `norm_jucovicVec`, `jucovic_injective` |
| the 14 faces (two triangles, six slopes, six sides) are supporting planes with the listed vertices, for `1/2 ≤ t ≤ 1` | `jucovic_face_on`, `jucovic_face_supporting` |
| the covering radius is exactly `arccos h⋆` (`≈ 45.8789°`, a number not used in any proof) | `coveringRadius_jucovicStar` |
| the ball of radius `h⋆` lies in the hull | `closedBall_subset_hullOf_jucovicStar` |
| within the family `jucovic t`, `0 < t < 1`, no member does better | `coveringRadius_jucovicStar_le` |

How the radius is proved: the north pole is a hole (lower bound); for the upper
bound every direction is mapped by `D₃h` into the sector `0 ≤ y ≤ √3 x`, `z ≥ 0`,
which is covered by the cones over three faces (`B₀B₁B₂`, `A₀B₀C₀`, `A₀B₂B₀`),
chosen by two linear tests; a direction over a face whose plane is at distance
`≥ h⋆` sees a vertex of that face at inner product `≥ h⋆` (`face_support`). The
face distances at `t⋆` are `h⋆` (triangles and sides, equal by the quartic) and
more than `h⋆` (slopes, since `t⋆ > 2/3`). The family statement uses the top
face for `t ≥ t⋆`, the side face (a supporting plane for `t ≥ 1/2`, its distance
increasing in `t`) for `1/2 ≤ t < t⋆`, and the equatorial hole of depth `60°`
for `t < 1/2`.

Cross-check (NUMERICAL, not used): the archived Hardin–Sloane–Smith coordinates
for `N = 9` (`cover.3.9.txt`, "putatively optimal", radius `45.8788878°`) have the
same sorted multiset of 36 inner products as `jucovicStar` to six decimals.

### 3.2 Conditional (`coveringRadius_jucovicStar_le_of_reduction`)

`NinePointReduction` (an ordinary hypothesis, not an axiom): every 9-point
configuration is matched or beaten by some member of the family `jucovic t`.
Under it, Jucovič's configuration is optimal among all 9-point configurations.
The hypothesis is not Wimmer's theorem. It combines

1. an optimal configuration has the combinatorial type of the triaugmented
   triangular prism (what the abstract of Wimmer 2017 reports; the statement's
   exact hypotheses and the proof are unread), and
2. within that type, the optimum lies in the `D₃h`-symmetric family.

A combinatorial type does not fix the symmetry, so (2) does not follow from (1).

### 3.3 What is still open, and how it might be attacked

* Step (2), optimality within the combinatorial type without assuming symmetry.
  Hoehner and Ledford (arXiv:2608.04392, v2) do the analogous thing for the
  maximum-volume 9-vertex polytope: within the same combinatorial type, they
  derive the symmetry from equality cases instead of assuming it, by hand,
  without computer assistance (`HOEHNER_LEDFORD_WIMMER_THESIS.md`). Their
  volume-specific reductions do not transfer; the pattern does. For covering,
  the type fixes which 14 triangles are faces, and the radius is the largest of
  their 14 circumradii; the task is to show that minimizing that maximum over
  the 15 remaining parameters forces `D₃h` symmetry.
* Step (1), re-proving the combinatorial type. Wimmer's dissertation (Salzburg
  1998, author-hosted) is about maximum volume, not covering; the covering
  classification is in Wimmer 2017, whose body is unread.
* The lower bound side: L. Fejes Tóth's bound gives `ρ₉ ≥ arccos(tan(2π/7)/√3)
  ≈ 43.61°`, about `2.27°` below `45.879°`; not formalized (section 2).

Research plan, in order: (a) formalize step (2) for configurations of the
triaugmented-prism type, starting with local optimality (second-order
conditions at `jucovicStar`, exact in `ℚ(√3, t⋆)`); (b) global optimality within
the type, choosing between an equality-case argument in the style of
Hoehner–Ledford and interval arithmetic once (a) shows the structure; (c) read
Wimmer 2017 to state step (1) exactly, then decide whether to formalize it or
keep it a hypothesis. NACO 2025 (moment hierarchy) remains a possible source of
non-sharp lower bounds, not of `N = 9` optimality.
