# Certified spherical covering

What LeanGeodesy proves about covering `S²` by `n` closed caps, what a covering
certificate is, and what it does not show. All of it is checked by Lean from
Mathlib and the three standard axioms; nothing is assumed.

Files: `Spherical/Topology.lean` (existing: `coveringRadius`,
`exists_optimal_covering`), `Spherical/Covering.lean` (equivalences),
`Spherical/CoveringCert.lean` (checker and its soundness),
`Spherical/CoveringBenchmarks.lean` (octahedron and tetrahedron),
`Spherical/CoveringLowerBound.lean` (bounds for every configuration, global
optimality for `N = 2, 3, 4`), `Spherical/Jucovic9.lean` (Jucovič's 9-point
configuration, exact radius, optimality within its symmetric family),
`Spherical/NinePoint.lean` (the 9-point problem decomposed, the harmonic-mean
reduction),
`scripts/covering_cert/gen_cert.py` (certificate generator).

All six Lean files belong to the routine target `LeanGeodesy`, not to
`LeanGeodesyResearch` (ADR-001): the first two are foundations and a reusable
verifier, and the benchmark certificates are small (they build in seconds).
A large certificate for a research configuration should go to
`LeanGeodesyResearch` instead.

## 1. Exact reformulations (`Covering.lean`)

For a configuration `p : Fin n → UnitSphere` and `0 ≤ r ≤ π`:

| Statement | Theorem |
| --- | --- |
| `x ∈ closedCap c r ↔ cos r ≤ ⟪c, x⟫` | `mem_closedCap_iff` |
| `IsCovering p r ↔ ∀ u, ∃ i, cos r ≤ ⟪p i, u⟫` (the support function of the hull, `max_i ⟪p i, u⟫`, is at least `cos r` in every direction) | `isCovering_iff_inner_support`, `hullOf_subset_halfSpace` |
| for `r ≤ π/2`: `IsCovering p r ↔ closedBall 0 (cos r) ⊆ convexHull (range p)` | `isCovering_iff_closedBall_subset_hullOf`, `coveringRadius_le_iff_closedBall_subset_hullOf` |
| a supporting plane `⟪p i, u⟫ ≤ c` for all `i` forces `cos r ≤ c` (a hole of depth `arccos c`) | `cos_le_of_supportPlane`, `arccos_le_coveringRadius_of_hole` |
| the Voronoi cell of `p i` is the sphere cut by `⟪p j - p i, x⟫ ≤ 0`; covering holds iff every cell lies in its own cap | `mem_voronoiCell_iff`, `isCovering_iff_voronoiCell_subset` |
| repeated points change nothing | `isCovering_comp_of_range_eq`, `hullOf_congr` |
| origin not interior to the hull, or all points in a closed hemisphere, forces radius `≥ π/2` | `not_isCovering_of_zero_not_mem_interior`, `pi_div_two_le_of_hemisphere` |

The ball-in-hull equivalence uses Hahn–Banach separation (hence
`Classical.choice`); it is a statement about all configurations, including
degenerate ones. For `r > π/2` the ball radius `cos r` is negative and the
equivalence is not claimed.

## 2. The certificate (`CoveringCert.lean`)

Data: `n` nonzero rational vectors `q i : ℚ × ℚ × ℚ` (the point is
`q i / ‖q i‖`, which is why irrational coordinates such as `1/√3` are not
needed), a rational `R ∈ [0,1]`, and for each of the six faces of the cube
`[-1,1]³` a guillotine subdivision of the face square (`CoverTree`) whose
leaves name a point. On each leaf box the checker bounds `⟪q i, x⟫` below and
`‖x‖²` above in exact rational arithmetic and requires
`0 ≤ L` and `R ‖q i‖² M ≤ L²`.

`checkCover_sound`: if `checkCover q R T = true` and `p` realizes `q`
(`Realizes`), then every unit direction `u` has a point with `√R ≤ ⟪p i, u⟫`;
`isCovering_of_checkCover` and `coveringRadius_le_of_checkCover` give
`IsCovering p (arccos √R)` and `coveringRadius ≤ arccos √R`.

* No convex hull, facet list or completeness of a face set is needed: the
  boxes cover the cube surface by construction (a cut sends `u ≤ m` left and
  `u ≥ m` right), and every unit vector is a positive multiple of a cube-surface
  point (`exists_face`). This is the completeness-free route.
* Trusted: Lean's kernel, this file, and the realization hypothesis tying `p`
  to `q`. Not trusted: the generator, any convex-hull solver, any floating
  point. The tree is only data.
* Strict limit: the leaf test is zero-slack only where a deep hole lies on a
  box corner it shares with its neighbours. In general `R` must sit a little
  below the true `cos² r`, and the leaf count grows as the slack shrinks.

### The vertex test (`checkCoverV`)

For fixed `Q` and `k ≥ 0` the set `{x | k ‖x‖ ≤ ⟪Q, x⟫}` is a convex cone
(`cone_convex`), and a box is the convex hull of its corners, so checking the
squared inequality `R ‖q‖² ‖x‖² ≤ ⟪q, x⟫², 0 ≤ ⟪q, x⟫` at the four corners proves
it on the box (`leafOKv`, `chkV_sound`). It accepts every box the original test
accepts. Measured with `gen_cert.py` and `lake env lean` on the tetrahedron:

| `R` | `leafOK` leaves | `leafOKv` leaves |
| --- | --- | --- |
| 1/10 | 192 | 132 |
| 11/100 | 360 | 276 |
| 111/1000 | 504 | 372 |
| 1111/10000 | 672 | 492 |
| 1/9 (exact) | none (depth > 34) | none (depth > 34) |

Both grow by about 150 leaves per decimal digit of slack. At `R = 11/100` the
kernel check takes about 1.6 s (`leafOK`) and 1.8 s (`leafOKv`) beyond a
2.2 s baseline: fewer leaves, four corners each. Neither reaches an exact
boundary unless the deep holes sit on box corners and each box lies in one cap
(the octahedron passes at `R = 1/3` with six leaves under both tests); at the
tetrahedron's holes three Voronoi cells meet, and axis-parallel boxes cannot
follow their edges. Exact values come from structure instead (section 3).

### Zero direction vectors and `Realizes`

A zero vector passes every leaf of `checkCover` (its lower bound is `0` and its
norm is `0`), so `checkCover` accepts a "covering" by one zero vector (an
`example` in the benchmarks). This is not unsound: `checkCover_sound` assumes
`Realizes q p`, and no configuration realizes a zero vector
(`not_realizes_of_zero`). `Realizes` is otherwise exactly what it says: each
point is its direction normalized, so it can only describe configurations
whose points have rational directions. `checkCoverV` checks `nrm2 (q i) ≠ 0`
itself, and `ratConfig` builds the points from the directions, so
`isCovering_ratConfig_of_checkCoverV` has no realization hypothesis left.

Not proved: that a configuration covering with strict margin always has a
finite accepted certificate. The argument would be compactness (a uniform
margin `δ`), then a uniform grid fine enough that each box's corners stay
within `δ` of the centre's best point; it is written down nowhere in Lean.

## 3. Benchmarks (`CoveringBenchmarks.lean`)

| Configuration | Result |
| --- | --- |
| Regular octahedron | `coveringRadius_octahedron6 : coveringRadius = arccos (1/√3)`, exact. Upper bound from a 6-leaf certificate at `R = 1/3`, lower bound from the hole `(1,1,1)/√3`. |
| Regular tetrahedron | `coveringRadius_tetrahedron4 : coveringRadius = arccos (1/3)`, exact, with no certificate: the six edge midpoints are the octahedron scaled by `1/√3`, so the hull of the tetrahedron contains `1/√3` times the hull of the octahedron, hence the ball of radius `1/3` (`closedBall_subset_hullOf_tetrahedron4`). The 360-leaf certificate (`coveringRadius_tetrahedron4_bounds`, `≤ arccos √(11/100)`) is kept as a test of the checker. |
| Both | `octaCert_rejects_above`, `tetraCert_rejects_above`: no tree whatsoever is accepted for `R` above the true `cos² r` (soundness plus the hole). Concrete mutation tests (`example : checkCover … = false`): `R` too large, wrong or out-of-range leaf, a vertex removed, negative `R`, a tampered cut. |

Not done: the regular icosahedron. Its vertices are irrational (`φ`), so the
rational checker does not apply directly; it needs arithmetic in `ℚ(√5)` or a
rational near-icosahedron (which would not be the icosahedron).

## 4. Bounds for every configuration (`CoveringLowerBound.lean`)

* `cos_mul_norm_le_of_halfSpace`: if all points satisfy `⟪V, p i⟫ ≤ c`, every
  covering radius has `cos r ‖V‖ ≤ c`; summed over several half-spaces,
  `cos r Σ ‖V k‖ ≤ Σ c k`. With balanced normals (`Σ V k = 0`) the right-hand
  side can be computed from the points.
* Four points: the face normals of the tetrahedron they span (the gradients of
  its oriented volume) sum to zero, which gives `cos r ≤ 1/3` for every
  configuration (Euler's `R ≥ 3r` in vector form); collinear configurations lie
  in a hemisphere. `covering_4_optimal`: four caps of radius `r` cover exactly
  when `arccos (1/3) ≤ r`; `coveringRadius_tetrahedron4_le`: the regular
  tetrahedron is optimal.
* Two and three points: they lie in a closed hemisphere, and points summing to
  zero cover at `π/2`. `covering_2_optimal`, `covering_3_optimal`: the threshold
  is `π/2`.

These are global optimality theorems, statements about all configurations;
`coveringRadius_octahedron6` and `coveringRadius_tetrahedron4` are exact values
for one configuration each. The two are different claims, and only `N = 2, 3, 4`
have the first kind here. For `N = 6, 12` see `research/COVERING_GLOBAL_PLAN.md`.

## 5. Nine points (`Jucovic9.lean`)

Jucovič's 1960 configuration is formalized exactly: the parameter `t⋆` is the
root in `(2/3, 1)` of `4t⁴ - 4t³ + 3t² + 4t - 4`, the 14 hull faces are
certified by supporting planes, and `coveringRadius_jucovicStar` proves the
covering radius `arccos √(1 - t⋆²)` with no certificate (symmetry, three face
cones, and a hole). `coveringRadius_jucovicStar_le` proves optimality within the
one-parameter `D₃h` family only. Optimality among all 9-point configurations is
stated as `coveringRadius_jucovicStar_le_of_reduction`, conditional on an
explicit hypothesis that is not Wimmer's theorem; see
`research/COVERING_GLOBAL_PLAN.md`, section 3. `NinePoint.lean` sharpens this:
`TTPOptimal` (optimality within the combinatorial type) and `OptimalIsTTP`
(optimal configurations have the type) are separate hypotheses, and
`TTPOptimal` follows from the harmonic-mean inequality `TTPHarmonic`, which
`NinePointElim.lean` reduces, after one relaxation, to an equivalent inequality
`ReducedHarmonic` in the six non-equatorial points (both open; the first,
non-strict version of `TTPHarmonic` was false, see `NinePointAudit.lean`). Strict
local optimality without symmetry is verified exactly outside Lean
(`research/NINE_POINT_LOCAL.md`).

## 6. What this does not prove

* Optimality of Jucovič's 9-point configuration among all configurations: only
  conditional (section 5).
* A certificate is an upper bound for one configuration. It says nothing about
  other configurations, so it never proves global optimality of a configuration.
* Optimality for `N = 6, 12` (L. Fejes Tóth) is not formalized; `N = 4` is.
  The general bound needs the face structure of the hull, spherical triangle
  areas and Euler's formula (`research/COVERING_GLOBAL_PLAN.md`);
  `research/COVERING_LITERATURE.md` has the status of every `N`.
* `exists_optimal_covering` (existence of a minimizer) is old; nothing here
  locates or characterizes minimizers.
