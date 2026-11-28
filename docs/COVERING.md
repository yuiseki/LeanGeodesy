# Certified spherical covering

What LeanGeodesy proves about covering `S²` by `n` closed caps, what a covering
certificate is, and what it does not show. All of it is checked by Lean from
Mathlib and the three standard axioms; nothing is assumed.

Files: `Spherical/Topology.lean` (existing: `coveringRadius`,
`exists_optimal_covering`), `Spherical/Covering.lean` (equivalences),
`Spherical/CoveringCert.lean` (checker and its soundness),
`Spherical/CoveringBenchmarks.lean` (octahedron and tetrahedron),
`scripts/covering_cert/gen_cert.py` (certificate generator).

All three Lean files belong to the routine target `LeanGeodesy`, not to
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

## 3. Benchmarks (`CoveringBenchmarks.lean`)

| Configuration | Result |
| --- | --- |
| Regular octahedron | `coveringRadius_octahedron6 : coveringRadius = arccos (1/√3)`, exact. Upper bound from a 6-leaf certificate at `R = 1/3`, lower bound from the hole `(1,1,1)/√3`. |
| Regular tetrahedron | `coveringRadius_tetrahedron4_bounds`: `arccos (1/3) ≤ coveringRadius ≤ arccos √(11/100)`, i.e. `70.5288° ≤ · ≤ 70.63°` (360-leaf certificate). The exact value `arccos (1/3)` is not proved. |
| Both | `octaCert_rejects_above`, `tetraCert_rejects_above`: no tree whatsoever is accepted for `R` above the true `cos² r` (soundness plus the hole). Concrete mutation tests (`example : checkCover … = false`): `R` too large, wrong or out-of-range leaf, a vertex removed, negative `R`, a tampered cut. |

Not done: the regular icosahedron. Its vertices are irrational (`φ`), so the
rational checker does not apply directly; it needs arithmetic in `ℚ(√5)` or a
rational near-icosahedron (which would not be the icosahedron).

## 4. What this does not prove

* A certificate is an upper bound for one configuration. It says nothing about
  other configurations, so it never proves global optimality of a configuration.
* Optimality of `N = 4, 6, 12` (L. Fejes Tóth) is not formalized. It needs a
  lower bound valid for every configuration (Delaunay triangulation, area of
  spherical triangles of bounded circumradius); see
  `research/COVERING_LITERATURE.md` for the status of every `N`.
* `exists_optimal_covering` (existence of a minimizer) is old; nothing here
  locates or characterizes minimizers.
