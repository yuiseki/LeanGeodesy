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

## 3. N = 9: the problem, reduced

What is proved (literature):

* Wimmer 2017 (DCG 57, 763–781): the combinatorial type of the optimal
  covering for `N = 9` is determined, and `N = 8` is solved (the optimum is
  Schütte's 1955 arrangement, per the zbMATH review). THEOREM by the refereed
  abstract; the body could not be read (paywalled), so the type itself, the
  method and any computer part are UNVERIFIED. An undated note on the author's
  web page claims more (both 8 and 9 solved) from a preprint that could not be
  found; the refereed abstract claims only the type for 9.
* Lower bound: L. Fejes Tóth's bound gives `ρ₉ ≥ arccos(tan(2π/7)/√3) ≈ 43.61°`
  (closed form THEOREM; the number is a hand evaluation).

Best known configuration (NUMERICAL): Rathbun 2020 (arXiv:2008.04441), `D3h`,
three coplanar equilateral triples, radius `45.8788878287°`, `cos ρ` a root of
`16x⁸ − 72x⁶ + 129x⁴ − 66x² + 9` (a numerical identification, not proved). The
gap between the proved lower bound and the best known radius is about `2.27°`.

What is not proved: that the `D3h` configuration is optimal within Wimmer's
type (or at all); uniqueness; the exact algebraic value.

Reduction to finitely many constraints (assessment, not literature): once the
combinatorial type is fixed (9 vertices, 14 triangles), the covering radius of
a configuration of that type is the largest angular circumradius of its 14
triangles, as long as the type stays a Delaunay triangulation. Optimality
within the type is then a min-max over `(S²)⁹ / SO(3)`, 15 real parameters,
with 14 circumradius constraints and the Delaunay (empty-circle) conditions,
all polynomial in the coordinates after squaring.

What could verify it, and what each needs:

* Upper bound: the checker here can certify `ρ₉ ≤` any rational bound above
  `45.8788878…°` for a rational approximation of the `D3h` configuration
  (moderate size, by the tetrahedron numbers). Exact `ρ₉` for that
  configuration needs algebraic arithmetic (the degree-8 polynomial), not more
  boxes.
* Local optimality of `D3h` within the type: exact second-order (KKT)
  conditions at an algebraic point, checkable with exact algebraic numbers.
* Global optimality within the type: interval branch-and-bound over the 15
  parameters, or an SOS/Positivstellensatz certificate, both large. This is
  where the work is.
* Exhaustiveness: that no other combinatorial type does better. This is
  Wimmer's result, which would have to be read and re-proved (possibly with a
  verified enumeration of triangulations, e.g. by plantri, which his
  references cite).
* The NACO moment hierarchy (Riener, Rolfes, Vallentin, NACO 16 (2026) 157–170;
  arXiv:2312.11267) gives lower bounds on the covering number; level 1 equals
  the volume bound on `S²` (weaker than Fejes Tóth), level 2 is set up but not
  computed, and finite convergence needs an a priori separation `ε`. The exact
  rational PSD checking here would carry over, but certificates would have to
  hold for every radius below the target and over orbits of 4-point sets. At
  best a new non-sharp lower bound; not a route to `N = 9` optimality.

Research plan for `N = 9`, in order, each step useful on its own:

1. Obtain and read Wimmer 2017 (needs institutional access). Without the
   combinatorial type the rest cannot be stated.
2. Certified upper bound for a rational near-`D3h` configuration with the
   existing checker (a research-size certificate goes to
   `LeanGeodesyResearch`, not the routine target).
3. Exact radius of the `D3h` configuration: prove that the claimed degree-8
   polynomial vanishes at `cos ρ` for that configuration (algebraic identity),
   and that the deep holes are the claimed triangles.
4. Local optimality within the type by exact second-order conditions.
5. Global optimality within the type: decide between interval arithmetic and
   SOS after step 4 shows how much slack there is away from the optimum.
6. Exhaustiveness over types: re-prove Wimmer's reduction.

The smallest unproved piece is step 4 (or step 3 if the polynomial is wrong);
the hardest is step 5 together with step 6. Nothing here starts a numerical
search.
