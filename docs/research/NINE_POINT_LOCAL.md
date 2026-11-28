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
implication was unaffected.) `TTPOptimal_of_harmonic` (Lean): for any
`wT, wV ≥ 0` with `2wT + 6wV = 1`, `TTPHarmonic wT wV → TTPOptimal`.

Only the KKT weights `wT = λ_T`, `wV = λ_V` can work (equality at `P⋆` and local
maximality force them). With them:

* **Numerical:** in multi-start local maximization of the weighted harmonic
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

Numerical, the relaxation that is used: minimizing the weighted harmonic sum
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
  whenever the set is nonempty. (Not in Lean.)
* *Stationarity and boundary.* The unconstrained minimum `θ₁ = θ₂ = 0` (both
  planes orthogonal to their foot points) is admissible only if the two
  smallest circles through the edges meet; at Jucovič's configuration they do
  not (they would meet at `x = 2t⋆ > 1`). Otherwise the minimum lies on the
  boundary `gramDet3 = 0`, which means the line of intersection of the two
  planes is tangent to the sphere: the two circumcircles through `A` are
  tangent at `A`. (Lagrange condition; not in Lean.)
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
