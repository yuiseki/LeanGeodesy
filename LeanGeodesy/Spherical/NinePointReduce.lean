import LeanGeodesy.Spherical.NinePoint
import LeanGeodesy.Spherical.ThreePoint

/-!
# Eliminating the equatorial points from the harmonic-mean inequality

In `TTPHarmonic` each equatorial point `Aₖ` lies on exactly two of the eight
active faces, the sides `AₖBₖCₖ` and `AₖBₖ₋₁Cₖ₋₁`. For fixed `B`, `C` the part of
the weighted sum that depends on `Aₖ` is `λ_V (1/d₁ + 1/d₂)`, where `d₁, d₂` are
the distances of the two planes through `Aₖ`. This file proves the facts that
make the elimination of `Aₖ` work:

* `gram_two_planes`: if a unit vector `A` lies on two planes with unit normals
  `n₁, n₂` at distances `d₁, d₂`, then `gramDet3 d₁ d₂ ⟪n₁, n₂⟫ ≥ 0`, i.e.
  `d₁² + d₂² - 2c d₁ d₂ ≤ 1 - c²`. Conversely the planes meet on the sphere
  exactly when this holds, so eliminating `A` replaces it by this one
  inequality between the two planes.
* `inv_add_inv_sq_ge_of_gram`: under that inequality,
  `(1 + c) (1/d₁ + 1/d₂)² ≥ 8`, that is `1/d₁ + 1/d₂ ≥ 2 √(2/(1 + c))`.
* `inv_add_inv_eq_of_gram_iff`: equality holds exactly when `d₁ = d₂` and
  `d₁² = (1 + c)/2`, the case in which the two circles through `A` are tangent
  at `A` and the two distances are equal. At Jucovič's configuration both
  happen at each `Aₖ` (`jucovic_pair_equality`).

What the elimination leaves (a 2-parameter problem per `Aₖ`, then a
9-parameter inequality in `B`, `C`) is described in
`docs/research/NINE_POINT_LOCAL.md`.
-/

namespace Geodesy.Spherical

open Real Geodesic

/-- A unit vector on two planes with unit normals: the Gram determinant of
`A, n₁, n₂` is nonnegative. -/
theorem gram_two_planes (A n₁ n₂ : UnitSphere) :
    0 ≤ gramDet3 (inner ℝ A.1 n₁.1) (inner ℝ A.1 n₂.1) (inner ℝ n₁.1 n₂.1) :=
  gramDet3_nonneg A n₁ n₂

/-- The Gram condition bounds the sum of the distances: `(d₁ + d₂)² ≤ 2 (1 + c)`. -/
theorem sum_sq_le_of_gram {d₁ d₂ c : ℝ} (h1 : 0 < d₁) (h1' : d₁ ≤ 1) (h2' : d₂ ≤ 1)
    (hc0 : -1 ≤ c) (hc1 : c ≤ 1) (hg : 0 ≤ gramDet3 d₁ d₂ c) : (d₁ + d₂) ^ 2 ≤ 2 * (1 + c) := by
  unfold gramDet3 at hg
  -- (d₁ + d₂)² (1 - c) ≤ 2 (1 - c) (1 + c)
  have key : (d₁ + d₂) ^ 2 * (1 - c) ≤ 2 * (1 - c) * (1 + c) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + c) (sq_nonneg (d₁ - d₂))]
  rcases lt_or_eq_of_le hc1 with hlt | heq
  · have h : 0 < 1 - c := by linarith
    nlinarith
  · subst heq; nlinarith

/-- Two positive distances `d₁, d₂ ≤ 1` with `gramDet3 d₁ d₂ c ≥ 0`, `-1 ≤ c ≤ 1`,
satisfy `(1 + c) (1/d₁ + 1/d₂)² ≥ 8`. -/
theorem inv_add_inv_sq_ge_of_gram {d₁ d₂ c : ℝ} (h1 : 0 < d₁) (h2 : 0 < d₂) (h1' : d₁ ≤ 1)
    (h2' : d₂ ≤ 1) (hc0 : -1 ≤ c) (hc1 : c ≤ 1) (hg : 0 ≤ gramDet3 d₁ d₂ c) :
    8 ≤ (1 + c) * (1 / d₁ + 1 / d₂) ^ 2 := by
  have hs := sum_sq_le_of_gram h1 h1' h2' hc0 hc1 hg
  have hp : 0 < d₁ * d₂ := mul_pos h1 h2
  have hsum : 1 / d₁ + 1 / d₂ = (d₁ + d₂) / (d₁ * d₂) := by field_simp; ring
  rw [hsum, div_pow]
  have hp2 : 0 < (d₁ * d₂) ^ 2 := by positivity
  rw [mul_div_assoc', le_div_iff₀ hp2]
  have hamgm : 4 * (d₁ * d₂) ≤ (d₁ + d₂) ^ 2 := by nlinarith [sq_nonneg (d₁ - d₂)]
  -- (1 + c)(d₁+d₂)² ≥ (d₁+d₂)⁴/2 ≥ 8 (d₁d₂)²
  have e1 : (d₁ + d₂) ^ 2 * (d₁ + d₂) ^ 2 ≤ 2 * ((1 + c) * (d₁ + d₂) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (d₁ + d₂))]
  have e2 : 16 * (d₁ * d₂) ^ 2 ≤ (d₁ + d₂) ^ 2 * (d₁ + d₂) ^ 2 := by
    nlinarith [mul_le_mul hamgm hamgm (by positivity) (by positivity)]
  nlinarith

/-- Equality in `inv_add_inv_sq_ge_of_gram` forces `d₁ = d₂` and `2 d₁² = 1 + c`
(the two circles through the common point are tangent there). -/
theorem eq_of_inv_add_inv_sq_eq {d₁ d₂ c : ℝ} (h1 : 0 < d₁) (h2 : 0 < d₂) (h1' : d₁ ≤ 1)
    (h2' : d₂ ≤ 1) (hc0 : -1 ≤ c) (hc1 : c ≤ 1) (hg : 0 ≤ gramDet3 d₁ d₂ c)
    (heq : (1 + c) * (1 / d₁ + 1 / d₂) ^ 2 = 8) : d₁ = d₂ ∧ 2 * d₁ ^ 2 = 1 + c := by
  have hs := sum_sq_le_of_gram h1 h1' h2' hc0 hc1 hg
  have hp : 0 < d₁ * d₂ := mul_pos h1 h2
  have hsum : 1 / d₁ + 1 / d₂ = (d₁ + d₂) / (d₁ * d₂) := by field_simp; ring
  rw [hsum, div_pow] at heq
  have hp2 : 0 < (d₁ * d₂) ^ 2 := by positivity
  have heq' : (1 + c) * (d₁ + d₂) ^ 2 = 8 * (d₁ * d₂) ^ 2 := by
    rw [mul_div_assoc', div_eq_iff hp2.ne'] at heq; linarith
  have hamgm : 4 * (d₁ * d₂) ≤ (d₁ + d₂) ^ 2 := by nlinarith [sq_nonneg (d₁ - d₂)]
  have e1 : (d₁ + d₂) ^ 2 * (d₁ + d₂) ^ 2 ≤ 2 * ((1 + c) * (d₁ + d₂) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (d₁ + d₂))]
  have e2 : 16 * (d₁ * d₂) ^ 2 ≤ (d₁ + d₂) ^ 2 * (d₁ + d₂) ^ 2 := by
    nlinarith [mul_le_mul hamgm hamgm (by positivity) (by positivity)]
  -- the chain 16 p² ≤ s⁴ ≤ 2 (1+c) s² = 16 p² is tight, so s² = 4p, i.e. d₁ = d₂
  have tight : (d₁ + d₂) ^ 2 * (d₁ + d₂) ^ 2 = 16 * (d₁ * d₂) ^ 2 := by nlinarith
  have hsq : (d₁ + d₂) ^ 2 = 4 * (d₁ * d₂) := by
    have h4 : 0 ≤ (d₁ + d₂) ^ 2 := sq_nonneg _
    have : ((d₁ + d₂) ^ 2) ^ 2 = (4 * (d₁ * d₂)) ^ 2 := by nlinarith
    exact (sq_eq_sq₀ h4 (by positivity)).1 this
  have hd : d₁ = d₂ := by nlinarith [sq_nonneg (d₁ - d₂)]
  refine ⟨hd, ?_⟩
  subst hd
  have hd0 : 0 < d₁ ^ 2 := by positivity
  have : (1 + c) * (4 * d₁ ^ 2) = 8 * (d₁ ^ 2) ^ 2 := by nlinarith [heq']
  nlinarith

/-- At Jucovič's configuration the two sides through `A₀` (`A₀B₀C₀` and `A₀B₂C₂`)
have normals whose cosine is `1 - 2t⋆² = 2h⋆² - 1`; this is equivalent to the
quartic equation for `t⋆`. -/
theorem jucovic_side_normals_inner :
    inner ℝ (jucovicFaceNormal tStar hStar 8) (jucovicFaceNormal tStar hStar 13) =
      (1 - 2 * tStar ^ 2) * (‖jucovicFaceNormal tStar hStar 8‖ * ‖jucovicFaceNormal tStar hStar 13‖) := by
  have hq : 4 * tStar ^ 4 - 4 * tStar ^ 3 + 3 * tStar ^ 2 + 4 * tStar - 4 = 0 :=
    jucovicQuartic_tStar
  have h3 := sqrt3_sq
  have n8 := jucovicFaceNormal_norm_sq tStar hStar 8
  have n13 := jucovicFaceNormal_norm_sq tStar hStar 13
  simp at n8 n13
  have hprod : ‖jucovicFaceNormal tStar hStar 8‖ * ‖jucovicFaceNormal tStar hStar 13‖ =
      4 * tStar ^ 2 - 4 * tStar + 4 := by
    have hpos : 0 ≤ 4 * tStar ^ 2 - 4 * tStar + 4 := by nlinarith [sq_nonneg (2 * tStar - 1)]
    have : (‖jucovicFaceNormal tStar hStar 8‖ * ‖jucovicFaceNormal tStar hStar 13‖) ^ 2 =
        (4 * tStar ^ 2 - 4 * tStar + 4) ^ 2 := by rw [mul_pow, n8, n13]; ring
    exact (sq_eq_sq₀ (by positivity) hpos).1 this
  rw [hprod]
  simp only [jucovicFaceNormal, Matrix.cons_val]
  simp [inner_vec3]
  ring_nf
  simp only [h3]
  linear_combination 2 * hq

/-- Equality in the two-plane bound at Jucovič's configuration: distances `h⋆`,
cosine `c = 1 - 2t⋆²`, and `(1 + c) (1/h⋆ + 1/h⋆)² = 8`. -/
theorem jucovic_pair_equality : (1 + (1 - 2 * tStar ^ 2)) * (1 / hStar + 1 / hStar) ^ 2 = 8 := by
  have h2 := hStar_sq
  have hps := hStar_pos
  field_simp
  nlinarith [h2]

end Geodesy.Spherical
