import LeanGeodesy.ECEFInverse
import LeanGeodesy.Geodesic.Ellipsoid
import LeanGeodesy.Projection.FirstForm

/-!
# Uniqueness of the ellipsoidal ECEF inverse and curve length

`ECEFInverse` proved that `GeodeticCoordinate.toECEF` is surjective: every point
of space has geodetic coordinates. Inside the evolute near the Earth's centre,
normals from opposite sides cross, so the inverse is not globally unique across
all negative heights. On and outside the ellipsoid (`0 ≤ height`, and more
generally whenever `0 ≤ c₁.height + c₂.height`), no two normals cross:

- `lat_height_unique_of_meridian`: if two latitudes in `[-π/2, π/2]` and two
  heights with `0 ≤ h₁ + h₂` give the same axial distance `(N + h) cos φ` and
  vertical coordinate `(N (1 - e²) + h) sin φ`, then both the latitudes and the
  heights are equal;
- `lat_height_eq_of_toECEF`: if `toECEF E c₁ = toECEF E c₂` with
  `0 ≤ c₁.height` and `0 ≤ c₂.height`, then `c₁.lat = c₂.lat` and
  `c₁.height = c₂.height` everywhere, including at the poles;
- `toECEF_injective_off_poles`: off the poles (`0 < cos c₁.lat.1`), equality of
  `toECEF` on `0 ≤ height` forces `c₁ = c₂`.

This file also records the general smooth-curve arc-length theorem on the
ellipsoid (`EllipsoidCurve.curveLength_eq_integral_firstForm`), extending
`meridianArc_eq_curveLength` from meridians to arbitrary curves: the integral of
spatial speed `curveLength γ.position a b` equals `∫ t in a..b, √(I(φ', λ'))`.
-/

namespace Geodesy

open Real

namespace ReferenceEllipsoid

variable (E : ReferenceEllipsoid)

/-! ## Strict Cauchy-Schwarz on the meridian ellipse -/

private theorem W2_eq_cos_sq_add (φ : ℝ) :
    E.W2 φ = cos φ ^ 2 + (1 - E.e2) * sin φ ^ 2 := by
  unfold W2
  linear_combination -sin_sq_add_cos_sq φ

private theorem primeVerticalRadius_mul_sqrt_W2 (φ : ℝ) :
    E.primeVerticalRadius φ * √(E.W2 φ) = E.a := by
  have hs : 0 < √(E.W2 φ) := sqrt_pos.mpr (E.W2_pos φ)
  simp only [primeVerticalRadius]
  rw [show 1 - E.e2 * sin φ ^ 2 = E.W2 φ from rfl]
  field_simp

/-- Strict Cauchy-Schwarz inequality on the meridian ellipse: for distinct
geodetic latitudes `φ₁ ≠ φ₂`,
`cos φ₁ cos φ₂ + (1 - e²) sin φ₁ sin φ₂ < √(W²(φ₁)) √(W²(φ₂))`. -/
theorem meridianDot_lt_sqrt_W2_mul {φ₁ φ₂ : GeodeticLatitude} (hne : φ₁ ≠ φ₂) :
    cos φ₁.1 * cos φ₂.1 + (1 - E.e2) * sin φ₁.1 * sin φ₂.1 <
      √(E.W2 φ₁.1) * √(E.W2 φ₂.1) := by
  set c₁ := cos φ₁.1
  set s₁ := sin φ₁.1
  set c₂ := cos φ₂.1
  set s₂ := sin φ₂.1
  set A := c₁ * c₂ + (1 - E.e2) * s₁ * s₂
  have hW1 := E.W2_pos φ₁.1
  have hW2 := E.W2_pos φ₂.1
  have hprod_pos : 0 < √(E.W2 φ₁.1) * √(E.W2 φ₂.1) :=
    mul_pos (sqrt_pos.mpr hW1) (sqrt_pos.mpr hW2)
  rcases le_or_gt A 0 with hAle | hApos
  · linarith
  · have hsin_ne : s₁ ≠ s₂ := by
      intro hs_eq
      apply hne
      have h1 : arcsin s₁ = φ₁.1 := arcsin_sin φ₁.2.1 φ₁.2.2
      have h2 : arcsin s₂ = φ₂.1 := arcsin_sin φ₂.2.1 φ₂.2.2
      exact Subtype.ext (by rw [← h1, ← h2, hs_eq])
    have hcross_ne : c₁ * s₂ - s₁ * c₂ ≠ 0 := by
      intro hcross
      have hp1 := sin_sq_add_cos_sq φ₁.1
      have hp2 := sin_sq_add_cos_sq φ₂.1
      have hsq : s₂ ^ 2 = s₁ ^ 2 := by
        linear_combination (c₁ * s₂ + s₁ * c₂) * hcross - s₂ ^ 2 * hp1 + s₁ ^ 2 * hp2
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hpos | hneg
      · exact hsin_ne hpos.symm
      · by_cases hs10 : s₁ = 0
        · exact hsin_ne (by linarith)
        · have hcsum : (c₁ + c₂) * s₁ = 0 := by
            linear_combination -hcross + c₁ * hneg
          have hc0 : c₁ + c₂ = 0 := (mul_eq_zero.mp hcsum).resolve_right hs10
          have hc1_nn : 0 ≤ c₁ := GeodeticLatitude.cos_nonneg φ₁
          have hc2_nn : 0 ≤ c₂ := GeodeticLatitude.cos_nonneg φ₂
          have hc1_z : c₁ = 0 := by linarith
          have hc2_z : c₂ = 0 := by linarith
          have hA_neg : A ≤ 0 := by
            have he := E.one_sub_e2_pos
            have : A = -(1 - E.e2) * s₁ ^ 2 := by
              simp only [A, hc1_z, hc2_z, hneg]
              ring
            rw [this]
            nlinarith [sq_nonneg s₁]
          linarith
    have hdiff : (√(E.W2 φ₁.1) * √(E.W2 φ₂.1)) ^ 2 - A ^ 2 =
        (1 - E.e2) * (c₁ * s₂ - s₁ * c₂) ^ 2 := by
      rw [mul_pow, sq_sqrt hW1.le, sq_sqrt hW2.le, E.W2_eq_cos_sq_add, E.W2_eq_cos_sq_add]
      simp only [A]
      ring
    have hdiff_pos : 0 < (√(E.W2 φ₁.1) * √(E.W2 φ₂.1)) ^ 2 - A ^ 2 := by
      rw [hdiff]
      exact mul_pos E.one_sub_e2_pos (sq_pos_of_ne_zero hcross_ne)
    nlinarith

/-! ## Uniqueness in the meridian plane and in ECEF -/

/-- Uniqueness in the meridian plane: if two geodetic latitudes and two heights
with `0 ≤ h₁ + h₂` determine the same `(p, z)` point, then the latitudes and
heights coincide. -/
theorem lat_height_unique_of_meridian {φ₁ φ₂ : GeodeticLatitude} {h₁ h₂ : ℝ}
    (hh : 0 ≤ h₁ + h₂)
    (hp : (E.primeVerticalRadius φ₁.1 + h₁) * cos φ₁.1 =
          (E.primeVerticalRadius φ₂.1 + h₂) * cos φ₂.1)
    (hz : (E.primeVerticalRadius φ₁.1 * (1 - E.e2) + h₁) * sin φ₁.1 =
          (E.primeVerticalRadius φ₂.1 * (1 - E.e2) + h₂) * sin φ₂.1) :
    φ₁ = φ₂ ∧ h₁ = h₂ := by
  have hφ : φ₁ = φ₂ := by
    by_contra hne
    set c₁ := cos φ₁.1
    set s₁ := sin φ₁.1
    set c₂ := cos φ₂.1
    set s₂ := sin φ₂.1
    set N₁ := E.primeVerticalRadius φ₁.1
    set N₂ := E.primeVerticalRadius φ₂.1
    set A := c₁ * c₂ + (1 - E.e2) * s₁ * s₂
    have hdot := E.meridianDot_lt_sqrt_W2_mul hne
    have hN1A : N₁ * A < N₂ * E.W2 φ₂.1 := by
      calc N₁ * A < N₁ * (√(E.W2 φ₁.1) * √(E.W2 φ₂.1)) :=
            mul_lt_mul_of_pos_left hdot (E.primeVerticalRadius_pos φ₁.1)
        _ = E.a * √(E.W2 φ₂.1) := by rw [← mul_assoc, E.primeVerticalRadius_mul_sqrt_W2]
        _ = N₂ * E.W2 φ₂.1 := E.a_mul_sqrt_W2 φ₂.1
    have hN2A : N₂ * A < N₁ * E.W2 φ₁.1 := by
      calc N₂ * A < N₂ * (√(E.W2 φ₁.1) * √(E.W2 φ₂.1)) :=
            mul_lt_mul_of_pos_left hdot (E.primeVerticalRadius_pos φ₂.1)
        _ = (N₂ * √(E.W2 φ₂.1)) * √(E.W2 φ₁.1) := by ring
        _ = E.a * √(E.W2 φ₁.1) := by rw [E.primeVerticalRadius_mul_sqrt_W2]
        _ = N₁ * E.W2 φ₁.1 := E.a_mul_sqrt_W2 φ₁.1
    have hh_term : 0 ≤ (h₁ + h₂) * ((c₁ - c₂) ^ 2 + (s₁ - s₂) ^ 2) :=
      mul_nonneg hh (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hzero : 2 * (N₁ * (E.W2 φ₁.1 - A) + N₂ * (E.W2 φ₂.1 - A)) +
        (h₁ + h₂) * ((c₁ - c₂) ^ 2 + (s₁ - s₂) ^ 2) = 0 := by
      rw [E.W2_eq_cos_sq_add, E.W2_eq_cos_sq_add]
      simp only [A]
      linear_combination
        2 * (c₁ - c₂) * hp + 2 * (s₁ - s₂) * hz
          - h₁ * (sin_sq_add_cos_sq φ₁.1 - sin_sq_add_cos_sq φ₂.1)
          + h₂ * (sin_sq_add_cos_sq φ₁.1 - sin_sq_add_cos_sq φ₂.1)
    linarith
  subst hφ
  refine ⟨rfl, ?_⟩
  have hdiff_c : (h₁ - h₂) * cos φ₁.1 = 0 := by linear_combination hp
  have hdiff_s : (h₁ - h₂) * sin φ₁.1 = 0 := by linear_combination hz
  have hsq : (h₁ - h₂) ^ 2 = 0 := by
    linear_combination
      (h₁ - h₂) * cos φ₁.1 * hdiff_c + (h₁ - h₂) * sin φ₁.1 * hdiff_s
        - (h₁ - h₂) ^ 2 * sin_sq_add_cos_sq φ₁.1
  nlinarith

end ReferenceEllipsoid

namespace GeodeticCoordinate

/-- On and outside the ellipsoid (`0 ≤ height`), `toECEF` uniquely determines
both geodetic latitude and ellipsoidal height everywhere, poles included. -/
theorem lat_height_eq_of_toECEF (E : ReferenceEllipsoid) {c₁ c₂ : GeodeticCoordinate}
    (hh₁ : 0 ≤ c₁.height) (hh₂ : 0 ≤ c₂.height)
    (heq : toECEF E c₁ = toECEF E c₂) :
    c₁.lat = c₂.lat ∧ c₁.height = c₂.height := by
  have hN1 : 0 ≤ E.primeVerticalRadius c₁.lat.1 + c₁.height :=
    add_nonneg (E.primeVerticalRadius_pos c₁.lat.1).le hh₁
  have hN2 : 0 ≤ E.primeVerticalRadius c₂.lat.1 + c₂.height :=
    add_nonneg (E.primeVerticalRadius_pos c₂.lat.1).le hh₂
  have hp1 := toECEF_p E c₁ hN1
  have hp2 := toECEF_p E c₂ hN2
  rw [heq] at hp1
  have hp : (E.primeVerticalRadius c₁.lat.1 + c₁.height) * cos c₁.lat.1 =
      (E.primeVerticalRadius c₂.lat.1 + c₂.height) * cos c₂.lat.1 := hp1.symm.trans hp2
  have hz : (E.primeVerticalRadius c₁.lat.1 * (1 - E.e2) + c₁.height) * sin c₁.lat.1 =
      (E.primeVerticalRadius c₂.lat.1 * (1 - E.e2) + c₂.height) * sin c₂.lat.1 := by
    have hz' := congrArg (fun v : E3 => v 2) heq
    simpa [toECEF] using hz'
  exact E.lat_height_unique_of_meridian (add_nonneg hh₁ hh₂) hp hz

/-- Off the poles (`0 < cos c₁.lat.1`), `toECEF` is injective on coordinates
with nonnegative height. -/
theorem toECEF_injective_off_poles (E : ReferenceEllipsoid) {c₁ c₂ : GeodeticCoordinate}
    (hh₁ : 0 ≤ c₁.height) (hh₂ : 0 ≤ c₂.height) (hc : 0 < cos c₁.lat.1)
    (heq : toECEF E c₁ = toECEF E c₂) :
    c₁ = c₂ := by
  obtain ⟨hlat, hht⟩ := lat_height_eq_of_toECEF E hh₁ hh₂ heq
  have hN1 : 0 < E.primeVerticalRadius c₁.lat.1 + c₁.height :=
    add_pos_of_pos_of_nonneg (E.primeVerticalRadius_pos c₁.lat.1) hh₁
  have hc2 : 0 < cos c₂.lat.1 := hlat ▸ hc
  have hN2 : 0 < E.primeVerticalRadius c₂.lat.1 + c₂.height :=
    add_pos_of_pos_of_nonneg (E.primeVerticalRadius_pos c₂.lat.1) hh₂
  have hlon1 := ecefLongitude_toECEF E c₁ hc hN1
  have hlon2 := ecefLongitude_toECEF E c₂ hc2 hN2
  rw [heq] at hlon1
  have hlon : c₁.lon = c₂.lon := hlon1.symm.trans hlon2
  cases c₁
  cases c₂
  simp only [mk.injEq] at *
  exact ⟨hlat, hlon, hht⟩

end GeodeticCoordinate

/-! ## Arc length of smooth curves on the ellipsoid -/

namespace ReferenceEllipsoid.EllipsoidCurve

/-- The spatial curve length `∫ t in a..b, ‖r'(t)‖` of any smooth curve on the
ellipsoid agrees with the integral of its first-fundamental-form speed
`√(I(φ'(t), λ'(t)))`. -/
theorem curveLength_eq_integral_firstForm {E : ReferenceEllipsoid} (γ : EllipsoidCurve E)
    (a b : ℝ) :
    Projection.curveLength γ.position a b =
      ∫ t in a..b, √(E.firstForm (γ.lat t) (γ.lat' t, γ.lon' t)) := by
  unfold Projection.curveLength
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [(γ.hasDerivAt_position t).deriv, EllipsoidCurve.vel, E.norm_dr]

end ReferenceEllipsoid.EllipsoidCurve

end Geodesy
