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
