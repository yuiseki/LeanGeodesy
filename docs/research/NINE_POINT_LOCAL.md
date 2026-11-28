# Nine caps beyond symmetry: local optimality and a reduction

Written 2026-11-28. Every statement is labelled by how it is known:

* **Lean**: an unconditional theorem checked by Lean (`Spherical/NinePoint.lean`,
  `Spherical/Jucovic9.lean`), standard axioms only.
* **Lean, conditional**: a Lean theorem whose hypothesis is an explicit
  proposition, not an axiom.
* **Verified (exact)**: proved by `scripts/covering_cert/jucovic9_local.py` in
  exact arithmetic (the number field `K = ℚ(√3, t⋆, h⋆)` and rational interval
  arithmetic with outward rounding; no floating point in any conclusion), not
  checked by Lean.
* **Numerical**: floating-point observation, used for exploration only.

`P⋆` is Jucovič's configuration, `t⋆` the root in `(2/3, 1)` of
`4t⁴ - 4t³ + 3t² + 4t - 4`, `h⋆ = √(1 - t⋆²)`, `ρ⋆ = arccos h⋆ ≈ 45.8789°`.

## 1. The decomposition (Lean)

`IsTTP p`: under some labelling, each of the 14 triangles of the triaugmented
triangular prism lies in a supporting plane of the nine points with the origin
strictly inside (supporting-plane definition; the equivalence with the
face-lattice definition is not proved).

| Proposition | Status |
| --- | --- |
| `isTTP_jucovicStar`: `P⋆` has the type | Lean |
| `TTPOptimal`: every configuration of the type has covering radius `≥ ρ⋆` | open |
| `OptimalIsTTP`: every optimal 9-point configuration has the type | open here; the abstract of Wimmer 2017 reports a classification of this kind, whose exact statement and proof are unread |
| `coveringRadius_jucovicStar_le_of_TTP`: `TTPOptimal → OptimalIsTTP → P⋆` is globally optimal | Lean, conditional |

`TTPOptimal` is strictly weaker than global optimality, so this splits the old
`NinePointReduction` (which with the family theorem was equivalent to global
optimality) into a statement about one combinatorial type and a statement
about which type is optimal.

## 2. Active and inactive faces (Lean)

At `P⋆`, `jucovic_active_dist`: the two triangles and the six sides are at
distance exactly `h⋆`; `jucovic_slope_dist`: the six slopes are farther. So the
covering radius near `P⋆` is governed by eight constraints.

## 3. Local optimality without symmetry (Verified, exact)

The problem: maximize `min_f d_f(P)` over the eight active faces, on
`(S²)⁹ / SO(3)` (15 dimensions); `d_f` is the distance of the plane of face `f`.

1. **Gradients.** The active distances are smooth near `P⋆`; their tangent
   Jacobian is an `8 × 18` matrix with entries in `K`.
2. **Rank and null space.** The Jacobian has rank 7 (a `7 × 7` minor is
   certified nonzero; rank `≤ 7` by the relation in 3). Its null space has
   dimension 11, containing the 3 rotation directions, so the critical subspace
   modulo rotations has dimension 8.
3. **KKT multipliers.** Unique up to scale and positive: each triangle
   `λ_T = r/(2r + 6)`, each side `λ_V = 1/(2r + 6)`, with
   `r = λ_T/λ_V = 9/4 + 15t⋆/8 - 3t⋆²/2 - 3t⋆³/2 ≈ 2.26808`, a root of
   `4y⁴ - 72y³ + 405y² - 702y + 243`; the tangential part of
   `Σ λ_f ∇d_f` vanishes at every point (exact identity in `K`).
4. **Symmetry-breaking directions (Numerical).** The 8-dimensional critical
   subspace has no `D₃h`-invariant component: every first-order direction that
   keeps all eight distances is a symmetry-breaking perturbation (the only
   symmetric degree of freedom, the family parameter `t`, changes them).
5. **Second variation.** Not done in max-min form; instead, the stronger smooth
   statement below. (Numerically, the Lagrangian Hessian of the max-min problem
   on the critical subspace has eigenvalues `-0.161, -0.161, -0.111, -0.091,
   -0.091, -0.035, -0.035, -0.026`, all negative.)
6. **Strict local optimality.** Let `F(P) = -Σ λ_f / d_f(P)`. At `P⋆` its
   gradient vanishes (from 3, since all active `d_f = h⋆`), and the Hessian of
   its Lagrangian on a 15-dimensional complement of the rotation orbit is
   negative definite (15 Cholesky pivots of its negative certified positive in
   exact rational interval arithmetic: smallest pivot `≥ 0.0417`, interval
   widths `≤ 7.5·10⁻⁵⁷`; an independent finite-difference computation, Numerical,
   gives eigenvalues between `-0.716` and `-0.036`). By the second-order sufficient
   condition on `(S²)⁹` and the slice argument for `SO(3)` (classical, not
   re-proved), `P⋆` is a strict local maximum of `F` modulo rotations. Near `P⋆`
   the slopes stay inactive and every face plane stays supporting, so for `P`
   near `P⋆` and not a rotation of `P⋆`,
   `min_f d_f(P) ≤ (Σ λ_f / d_f(P))⁻¹ < h⋆` and the covering radius of `P` is
   larger than `ρ⋆`.

   Why `F` and not `Σ λ_f d_f`: the Hessian of `Σ λ_f d_f` (Numerical) has a
   positive eigenvalue `+0.0099` (twice) outside the critical subspace, so the
   arithmetic mean is not maximal at `P⋆`; composing with an increasing
   function `φ` adds `φ''/φ'·Σ λ_f ∇d_f ∇d_fᵀ`, and `φ''(h⋆)/φ'(h⋆) < -0.887` is
   enough. `φ = log` (`-1/h⋆ ≈ -1.44`) and `φ = -1/d` (`-2/h⋆ ≈ -2.87`) both
   work locally.

Not in Lean: Mathlib has no multivariate second-derivative test on manifolds
modulo a group action, and formalizing it is a library of its own. What Lean
does prove is the reduction of section 4, which needs no calculus.

## 4. A global inequality (Lean reduction, open inequality)

`arccos_le_coveringRadius_of_harmonic` (Lean): if supporting half-spaces and
weights `w ≥ 0`, `Σ w = 1`, have weighted harmonic mean of distances `≤ ρ`, the
covering radius is `≥ arccos ρ`. It is `cos_mul_sum_norm_le_of_halfSpaces` with
the weights `w_f / κ_f`.

`TTPHarmonic wT wV`: for every configuration of the type and every choice of
supporting planes through its faces (each plane contains the three vertices of
its face), `Σ_f w_f / d_f ≥ 1/h⋆` over the eight faces active at `P⋆`
(triangles `wT`, sides `wV`). (Correction, 2026-11-28: the first version of this
definition, in commit `504e62a`, omitted the condition that the planes pass
through the vertices; with it omitted, far-away supporting planes make the
statement false, so the implication `TTPOptimal_of_harmonic` was true but
empty. The definition now includes the condition; the proof of the
implication was unaffected.) (Second correction, 2026-11-28: the definition
of commit `bf906c0` is still false. With non-strict support, all fourteen
planes may coincide: nine points at the north pole with every plane `z = 1`,
or nine distinct points on the circle `z = 12/13` with every plane `z = 12/13`,
give the weighted sums `1` and `13/12`, both below `1/h⋆` when
`2wT + 6wV = 1`. Lean: `not_TTPHarmonic_allEqual`,
`not_TTPHarmonic_smallCircle` in `Spherical/NinePointAudit.lean`. See
section 7 for the repaired definitions.) `TTPOptimal_of_harmonic` (Lean): for any
`wT, wV ≥ 0` with `2wT + 6wV = 1`, `TTPHarmonic wT wV → TTPOptimal`.

Only the KKT weights `wT = λ_T`, `wV = λ_V` can work (equality at `P⋆` and local
maximality force them). With them:

* **Numerical (old definition, kept for the record; not evidence for the
  repaired statements of section 7):** in multi-start local maximization of the weighted harmonic
  mean over configurations of the type (SLSQP, the 14 supporting-plane
  conditions as constraints), 94 starts near `P⋆` and 77 starts far from it
  (Gram matrices differing by more than `0.3`) all ended at a value `≤ h⋆`
  (within `10⁻¹²`), at `P⋆`. The same holds for the weighted power means
  `(Σ λ_f d_f^{-k})^{-1/k}` with `k = 3, 10, 30`, and for `min_f d_f` itself
  (165 starts).
* **Numerical, negative:** the weighted geometric mean (`k = 0`) exceeds `h⋆`
  somewhere in the type (`Σ λ_f log d_f` up to `-0.301 > log h⋆ = -0.362`), and
  so does the arithmetic mean. So no fixed-weight inequality with `k ≤ 0` can
  prove `TTPOptimal`; `k = 1` is the first that is numerically true.

## 5. The obstacle

`TTPHarmonic λ_T λ_V` is a single smooth inequality in 15 variables, with
equality exactly on the orbit of `P⋆` (numerically), and it implies
optimality within the type. What blocks a proof:

* It is not convex in any coordinates tried, and its maximum is interior to
  the type, so no boundary or monotonicity argument applies directly.
* The `D₃h` symmetry cannot be assumed: the point of the statement is to
  derive it, as Hoehner and Ledford do for volume (where the objective
  decouples after a Cauchy–Schwarz step; here no such step is known).
* Partial elimination is available: each `Aₖ` appears in exactly two active
  faces (`AₖBₖCₖ`, `AₖBₖ₋₁Cₖ₋₁`), so for fixed `B`, `C` the inequality splits
  into three independent two-dimensional problems in `A₀, A₁, A₂`. If their
  minima have a closed form, what remains is a 9-dimensional inequality in the
  six points `B`, `C`, with the two triangle terms. This is the next step to
  try, before any interval branch-and-bound.
* A branch-and-bound over 15 dimensions would need, near `P⋆`, the local
  result of section 3 to close the neighbourhood (the margin vanishes there);
  away from it, the numerical margin is what an interval method would have to
  certify.

## 6. Eliminating `A₀, A₁, A₂` (2026-11-28, continued)

**Independence.** In the weighted harmonic sum each `Aₖ` appears in exactly two
active faces, `Vₖ = AₖBₖCₖ` (edge `eₖ = BₖCₖ`) and `Wₖ₋₁ = AₖBₖ₋₁Cₖ₋₁` (edge
`eₖ₋₁`). The constraints of the type that involve `Aₖ` are of three kinds: the
planes of the faces through `Aₖ` support the other points; the planes of other
faces have `Aₖ` on their inner side; and planes through `Aₖ` must have `Aⱼ`
(`j ≠ k`) on their inner side. Only the last kind couples two different `A`s.
Dropping it (and only it) is a relaxation: every configuration of the type
satisfies the remaining constraints, so a lower bound for the relaxed minimum
is a lower bound for the original one, and the relaxed inequality is a
sufficient condition for `TTPHarmonic`. For fixed `B`, `C` the relaxed problem
splits into three independent problems, one per `Aₖ`.

Numerical (searches made before the audit of section 7, with margins
`10⁻⁷` and sign-fixed planes; superseded by section 7.4), the relaxation that is used: minimizing the weighted harmonic sum
with only the cross-`A` constraints dropped, from 524 starts (518 far from
Jucovič's configuration, including fully random points), always ended at
`1/h⋆` (within `3·10⁻¹²`). So, as far as the search shows, the decoupling
loses nothing.

Numerical, a relaxation that is too strong: dropping every supporting-plane
constraint and keeping only positive distances lets the minimum fall to
about `1.000` (`< 1/h⋆ ≈ 1.436`, 1119 starts) at configurations where all
points cluster and every face is small; so the type constraints on `B`, `C`
cannot be dropped.

**The subproblem.** Fix the edges `e = eₖ`, `e' = eₖ₋₁` and minimize
`g(A) = 1/d(A, e) + 1/d(A, e')` over `A ∈ S²` (with the constraints above).

* *Algebraic form.* For a line `L` at distance `δ` from the origin (foot point
  `m`, direction `u`, `w = u × m/δ`) and `A = αu + β m/δ + γ w`,
  `d(A, L) = δ |γ| / √((β - δ)² + γ²)`: the distance of the plane through `L`
  and `A` depends only on the projection of `A` to the plane normal to `L`, and
  equals `δ cos θ`, `θ` the angle of that plane from the plane through `L`
  orthogonal to `m`. So `1/d(A, L) = sec θ / δ`.
* *Elimination.* With unit normals `n₁`, `n₂` of the two planes and
  `c = ⟨n₁, n₂⟩`, a common point `A` on the sphere exists exactly when
  `gramDet3 d₁ d₂ c ≥ 0` (Gram determinant of `A, n₁, n₂`; Lean:
  `gram_two_planes`, from the existing `gramDet3_nonneg`). Eliminating `A`
  turns the subproblem into: minimize `1/(δ₁ cos θ₁) + 1/(δ₂ cos θ₂)` over the
  two rotation angles `θ₁, θ₂` of the planes about their edges, subject to that
  one inequality. Two parameters instead of a point plus constraints.
* *Existence of a minimum.* `g → ∞` when a distance tends to `0` (the plane
  through the edge approaches the origin), and the admissible set in `(θ₁, θ₂)`
  is closed in `(-π/2, π/2)²` (Gram condition and the kept supporting
  conditions are closed), so sublevel sets are compact and a minimum exists
  whenever the set is nonempty. (Not in Lean.) (Correction, section 7.5: with
  the strict conditions of the repaired definition the set is open, so this
  gives a minimum of the closure only; `NinePointElim.lean` therefore uses the
  infimum and never assumes a minimum.)
* *Stationarity and boundary.* The unconstrained minimum `θ₁ = θ₂ = 0` (both
  planes orthogonal to their foot points) is admissible only if the two
  smallest circles through the edges meet; at Jucovič's configuration they do
  not (they would meet at `x = 2t⋆ > 1`). Otherwise a minimizer at which no
  supporting condition is active lies on the boundary `gramDet3 = 0`, which
  means the line of intersection of the two planes is tangent to the sphere:
  the two circumcircles through `A` are tangent at `A`. (Lagrange condition;
  not in Lean.) (Correction, section 7.5: this needs the extra hypothesis that
  no supporting condition is active at the minimizer; a minimizer on the
  boundary of the supporting conditions need not be tangent, and the
  infimum over the open feasible set need not be attained.)
* *Closed-form lower bound.* Under the Gram condition, `1/d₁ + 1/d₂ ≥ 2 √(2/(1 + c))`
  (Lean: `inv_add_inv_sq_ge_of_gram`), with equality exactly when `d₁ = d₂` and
  `2d₁² = 1 + c` (Lean: `eq_of_inv_add_inv_sq_eq`): tangent circles and equal
  distances.
* *Equality at Jucovič's configuration.* At each `Aₖ` the two sides have
  distance `h⋆` and normals with cosine `1 - 2t⋆² = 2h⋆² - 1`, which is the
  quartic equation for `t⋆` (Lean: `jucovic_side_normals_inner`,
  `jucovic_pair_equality`). So the bound is attained, and (Numerical) for the
  `B`, `C` of Jucovič's configuration the minimum over each `Aₖ` is attained at
  Jucovič's `Aₖ` (distance `< 2·10⁻⁸`, the optimizer's tolerance).
* *Convexity and closed form of the minimum.* Not established. `sec` is convex,
  but the admissible set in `(θ₁, θ₂)` is not known to be convex, and the
  tangency condition gives an algebraic equation of high degree, so no closed
  form for the minimum itself is claimed. The closed-form bound above depends
  on `c`, which still depends on the planes; it eliminates `A` but not the
  plane orientations.

**The reduced inequality.** Let `m(e, e')` be the minimum of the subproblem.
Then `TTPHarmonic` follows from

`R(B, C) = λ_T (1/d_T + 1/d_Bot) + λ_V (m(e₀, e₂) + m(e₁, e₀) + m(e₂, e₁)) ≥ 1/h⋆`

over the six points `B`, `C` satisfying the constraints of the type that do not
involve `A` (9 parameters modulo rotations). Numerical: `R = 1/h⋆` at Jucovič's
`B`, `C` (to `3·10⁻¹²`), and 21 multi-start minimizations of `R` from perturbed
configurations of the type all ended at `1/h⋆`.

**Further reduction (open, directions).** The six remaining points carry the
two triangles and the three vertical edges. Candidates, none carried out:
replace each `m(eₖ, eₖ₋₁)` by the closed-form bound `2√(2/(1+cₖ))` and keep
the plane orientations as variables (this makes the inequality polynomial
after squaring); use the Gram matrix of the six points to remove rotations;
compare the two triangles through their normals (the triangle terms are
`1/d_T`, `1/d_Bot` and depend only on each triangle's circumradius); and look
for the equality analysis (`d₁ = d₂` and tangency at each `Aₖ`, all eight
distances equal) to force the mirror symmetry `z ↦ -z` and the threefold
rotation, in the manner of Hoehner–Ledford.

## 7. Semantic audit and the sound reduction (2026-11-28, continued)

### 7.1 Counterexamples to the non-strict definition (Lean)

The definition of commits `504e62a`–`705f459` asked, for each face, a plane
through its three vertices with `κ > 0` and `⟪N, q i⟫ ≤ κ` for all nine
points. All fourteen planes may then be one plane:

| Configuration | Planes | Weighted sum (`2wT + 6wV = 1`) | Rejected by the repaired type |
| --- | --- | --- | --- |
| `allEqual`: nine points at `(0, 0, 1)` (degenerate triangles) | all `z = 1` | `1` | `not_isTTP_allEqual` |
| `smallCircle`: nine distinct points on `z = 12/13` (non-degenerate triangles, all faces in one plane, origin outside the hull) | all `z = 12/13` | `13/12` | `not_isTTP_smallCircle` |

Both sums are below `1/h⋆ ≈ 1.4364`, so the old statement (kept as
`TTPHarmonicWeak`) is false (Lean: `not_TTPHarmonic_allEqual`,
`not_TTPHarmonic_smallCircle`), and the old `TTPOptimal_of_harmonic` was an
empty implication. The two configurations stay in
`Spherical/NinePointAudit.lean` as regression tests: the repaired type
rejects them under every labelling.

### 7.2 The repaired definitions and what each condition costs

`FaceSupport q f N κ`: `κ > 0`, the three vertices of `f` on the plane, the
six other points strictly inside. `IsTTPSupported`, `IsTTP`, `TTPHarmonic`
use it; `TTPOptimal` and `OptimalIsTTP` keep their form (with the stricter
`IsTTP`, `OptimalIsTTP` is a stronger hypothesis: optimal configurations have
a simplicial hull of this type, which is what "has the combinatorial type"
means). The nine candidate conditions of the audit:

| Condition | Status in the repaired definition |
| --- | --- |
| 1. the nine points distinct | derived (Lean, `IsTTPSupported.injective`: some face contains one point and not the other) |
| 2. the origin in the interior of the hull | assumed as `κ > 0` for every face; together with 8–9 it is the interior condition |
| 3. non-degenerate triangles | derived: the vertices are distinct by 1, and three distinct points of the sphere are not collinear (Lean, `unit_collinear`) |
| 4. vertices on the plane | assumed |
| 5. the six other points strictly inside | assumed; this is the condition that was missing |
| 6. nonzero normal | derived (Lean, `FaceSupport.norm_pos`); also `0 < κ/‖N‖ ≤ 1` (`FaceSupport.dist_mem`) |
| 7. the fourteen faces distinct | derived (Lean, `FaceSupport.separated`: a vertex of one face is strictly inside the other) |
| 8. completeness of the face set | derived, not in Lean: 14 distinct triangular facets on at most 9 vertices are all the facets (`F ≤ 2V - 4`) |
| 9. the face lattice is the TTP with this labelling | derived from 5, 7, 8, not in Lean |

So the definition has three assumptions per face (4, 5 and `κ > 0`), all
necessary for a configuration whose hull is the labelled TTP containing the
origin (facets of a polytope have strict supporting planes), and none
excludes such a configuration. The three sets to keep apart:

* the true TTP type: hull simplicial with exactly these faces, origin
  interior. Equal to `IsTTPSupported` by the argument of rows 8–9 (not in
  Lean; the equivalence with a face-lattice definition is not claimed as a
  Lean theorem);
* a relaxed set containing it: `RelaxedFaceSupport` (section 7.3), which
  drops the cross-`A` conditions; it is not the TTP type;
* sets sufficient for the global inequality: any set containing the TTP
  type on which the inequality holds; `RelaxedHarmonic` is one candidate.

Validation (Lean): Jucovič's configuration has the repaired type
(`jucovic_faceSupport`, `isTTP_jucovicStar`; the 84 strict inequalities hold
for every `1/2 < t < 1`, `jucovic_face_strict`); the active sum there is
exactly `1/h⋆` (`activeSum_jucovicStar`), so `TTPHarmonic` would be sharp;
invariance under positive scaling of a plane (`faceSupport_smul`,
`norm_smul_div_mul`), under maps preserving inner products
(`faceSupport_map`, `norm_map_of_inner`) and under relabelling
(`isTTP_comp_perm`). `OptimalIsTTP` remains a hypothesis: Wimmer 2017 is
still unread.

### 7.3 The reduction, formally (Lean, `Spherical/NinePointElim.lean`)

```
ReducedHarmonic  ⟺  RelaxedHarmonic  ⟹  TTPHarmonic  ⟹  TTPOptimal
   (reduced_iff_relaxed)   (TTPHarmonic_of_relaxed)  (TTPOptimal_of_harmonic)
```

for weights `wT, wV ≥ 0`, `2wT + 6wV = 1` (`TTPOptimal_of_reduced`).

* *Original admissible set*: `(q, N, κ)` with `FaceSupport` for all 14 faces.
* *Relaxed set*: `RelaxedFaceSupport`, the same without the conditions
  "`Aⱼ` strictly inside a plane through `Aₖ`" (`CrossA`). This is the only
  step that is not an equivalence; it can only make the inequality harder.
* *Split*: `relaxed_iff` proves that the relaxed conditions are exactly
  `OuterFeasible` (the two triangle planes with `B`, `C`) and three
  `SubFeasible k` (the four faces through `Aₖ` with `Aₖ`, `B`, `C`, and `Aₖ`
  strictly inside both triangle planes). `sub_congr` and `outer_congr` show
  which data each part depends on, so the three subproblems are independent
  given `B`, `C` and the triangle planes.
* *Subproblem*: the objective `sideVal k` (the two sides through `Aₖ`), the
  feasible set `subValues k` (values over all `Aₖ` and all planes through
  `Aₖ`). Bounded below by `0` (`subValues_nonneg`); its infimum is used, no
  minimum is assumed.
* *Reduced objective*: `R = wT (1/d_T + 1/d_Bot) + wV Σₖ inf subValues k`,
  a function of `B`, `C` and the two triangle planes
  (`reducedObjective_congr`).
* *Reduced inequality* `ReducedHarmonic`: `R ≥ 1/h⋆` whenever the outer
  conditions hold and all three subproblems are feasible. An empty
  subproblem means the outer datum belongs to no configuration, so nothing
  is asked; this also keeps `sInf ∅ = 0` out of the statement. The
  direction `RelaxedHarmonic → ReducedHarmonic` takes near-optimal feasible
  points of the three subproblems and glues them into one relaxed
  configuration, which is where independence is used.
* *What is and is not eliminated*: `Aₖ` and the four planes through it are
  eliminated (they range inside the infimum). The two triangle planes are
  still arguments; for distinct `B`'s they are unique up to positive
  scaling, so `R` is a function of the six points, but that uniqueness is
  not proved in Lean. So this is a reduction to the six points `B`, `C`
  plus the two triangle planes, not yet an algebraic reduction to 9
  parameters.
* *The two-plane bound* survives as a bound on every feasible point
  (`sideVal_bound`: `(1 + cₖ) sideVal² ≥ 8`), but `cₖ` depends on the planes
  through `Aₖ`, so it does not eliminate them; it is not used in the chain.

### 7.4 Sharpness and counterexample search

Lean: `reducedObjective ≤ 1/h⋆` at Jucovič's `B`, `C`
(`reducedObjective_jucovicStar_le`). Equality there is equivalent to the
three subproblem statements `JucovicSubMinimal` (Jucovič's `Aₖ` minimizes
subproblem `k` for Jucovič's `B`, `C`): `JucovicSubMinimal → R = 1/h⋆`
(`reducedObjective_jucovicStar_eq`), and for `wV > 0`,
`ReducedHarmonic → JucovicSubMinimal` (`jucovicSubMinimal_of_reduced`).
Four different things, kept apart:

| Statement | Status |
| --- | --- |
| covering radius of Jucovič's configuration is `arccos h⋆` | Lean (`coveringRadius_jucovicStar`) |
| Jucovič's `Aₖ` minimizes its subproblem (`JucovicSubMinimal`) | open; numerical, 7.5 |
| equality `R = 1/h⋆` at Jucovič's `B`, `C` | Lean, conditional on `JucovicSubMinimal`; `≤` unconditional |
| `R ≥ 1/h⋆` for all `B`, `C` (`ReducedHarmonic`) | open |

Numerical (new search, `scripts/covering_cert/nine_point_search.py 40 2 16`;
planes computed from the vertices, strict conditions as slack `≥ ε`,
SLSQP): six start families aimed at the boundary (two points nearly
coincident, a face shrunk towards its centroid, the origin pushed towards the
hull boundary, top and bottom triangles of different sizes, points pushed
onto a face plane, random far configurations), each for the strict and the
relaxed set and `ε = 10⁻³, 10⁻⁶`: 977 feasible ends, smallest value
`1.4364155661466 = 1/h⋆` (to `10⁻¹⁴`), all at Jucovič's configuration. On
boundary strata (one slack, an offset, an inside condition or a face area,
pinned to `10⁻²` or `10⁻³`): 240 feasible ends, smallest value
`1.43891 = 1/h⋆ + 2.5·10⁻³`. No value below `1/h⋆`. Not a proof, and the
earlier counts (524, 21) are not reused as evidence.

### 7.5 Audit of the two-plane reduction

* `gram_two_planes` is a necessary condition only (Gram determinant of three
  unit vectors). The converse (for `|c| < 1`, the condition gives a common
  point of the two planes on the sphere) is true but neither proved in Lean
  nor used; every bound is applied to an actual common point.
* Degenerate cases (Lean): parallel normals, `c = 1` (the two planes
  coincide): the condition forces `d₁ = d₂` (`gram_parallel`), and the bound
  reads `8/d² ≥ 8`, with equality only for the tangent plane `d = 1`.
  Antiparallel normals, `c = -1`: the condition forces `d₁ + d₂ = 0`
  (`gram_antiparallel`), impossible for two positive distances, so the
  hypotheses of `inv_add_inv_sq_ge_of_gram` exclude it. The bound needs
  `0 < dᵢ ≤ 1` and `-1 ≤ c ≤ 1`, which hold for planes `⟪N, ·⟫ = κ > 0`
  through a point of the sphere (`face_pair_bound`).
* The inequality `d₁² + d₂² - 2c d₁ d₂ ≤ 1 - c²` is `gramDet3 ≥ 0`; the bound
  `1/d₁ + 1/d₂ ≥ 2√(2/(1 + c))` and its equality case (`d₁ = d₂`,
  `2d₁² = 1 + c`) are as stated (Lean).
* "The minimum of a subproblem has tangent circles" needs two hypotheses:
  the minimum is attained (with strict conditions the feasible set is open),
  and no supporting condition is active there; and it fails when the
  unconstrained optimum is feasible. Numerical
  (`scripts/covering_cert/nine_point_subproblem.py 150 3`): at Jucovič's
  `B`, `C` each subproblem is minimized at Jucovič's `Aₖ` (grid of
  `400 × 800` directions and local refinement; value `2/h⋆` to `3·10⁻¹⁴`,
  smallest slack `0.696`, Gram determinant `10⁻¹⁵`). For 122 perturbed
  `B`, `C`, the best of 12 local minimizations was interior every time (no
  supporting condition active); 118 were tangent (`|gramDet3| < 10⁻⁷`), and
  the other 4 were exactly the unconstrained case, with value
  `1/δ₁ + 1/δ₂` (`δᵢ` the distance from the origin to the edge `BₖCₖ`), as the
  Lagrange analysis predicts.
* A closed-form bound in `B`, `C` alone follows: a plane through a line at
  distance `δ` from the origin is at distance at most `δ`, so
  `sideVal k ≥ 1/δ₁ + 1/δ₂`. It is valid but loses at Jucovič's
  configuration (`2/t⋆ ≈ 2.786 < 2/h⋆ ≈ 2.873`), so replacing the infimum by
  it gives a false inequality; not used.

### 7.6 What is open, exactly

* `ReducedHarmonic λ_T λ_V` (equivalently `RelaxedHarmonic λ_T λ_V`): an
  inequality in the six points `B`, `C` (and the triangle planes they
  determine), with three two-parameter infima inside. It implies
  `TTPHarmonic`, hence `TTPOptimal`, in Lean.
* `JucovicSubMinimal`: three two-dimensional statements, necessary for
  `ReducedHarmonic` and sufficient for its equality at Jucovič's `B`, `C`.
  The natural first target.
* Not proved in Lean: uniqueness of the triangle planes, the equivalence of
  `IsTTPSupported` with the face-lattice definition, the converse of the
  Gram condition, the existence of subproblem minima.
