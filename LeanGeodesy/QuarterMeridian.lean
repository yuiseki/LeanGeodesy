import LeanGeodesy.MeridianArc
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Real.Pi.Bounds

/-!
# The quarter meridian of WGS 84

In 1791 the metre was defined as one ten-millionth of the distance from the
equator to the pole along the meridian through Paris. On WGS 84 that
distance, the quarter meridian `m(π/2)`, is

```
10001960 m < m(π/2) < 10001975 m          (wgs84_quarterMeridian_bounds)
```

so the Earth came out about 0.02 % larger than the definition intended.

The integral has no closed form, so the proof bounds its integrand. With
`s = √(1 - e² sin² ψ)`, `M = a (1 - e²) / s³`, and `1 / s³` is squeezed
between polynomials in `x = 1 - s² = e² sin² ψ`:

```
1 + 3/2 x + 15/8 x²  ≤  1 / s³  ≤  1 + 3/2 x + 15/8 x² + 3 x³
```

(`inv_cube_bounds`, the first terms of the binomial series of
`(1 - x)^(-3/2)`). The polynomials integrate exactly, since
`∫₀^{π/2} sin² = π/4` and `∫₀^{π/2} sin⁴ = 3π/16` (`integral_poly_sin`).
-/

namespace Geodesy

open Real

/-- The binomial series of `(1 - x)^(-3/2)` to second order, with `x = 1 - s²`,
bounds `1 / s³` below, and adding `3 x³` bounds it above, for `0.99 ≤ s ≤ 1`. -/
theorem inv_cube_bounds {s : ℝ} (h0 : 0.99 ≤ s) (h1 : s ≤ 1) :
    1 + 3 / 2 * (1 - s ^ 2) + 15 / 8 * (1 - s ^ 2) ^ 2 ≤ 1 / s ^ 3 ∧
      1 / s ^ 3 ≤ 1 + 3 / 2 * (1 - s ^ 2) + 15 / 8 * (1 - s ^ 2) ^ 2 + 3 * (1 - s ^ 2) ^ 3 := by
  have hs : 0 < s := by linarith
  have hs3 : 0 < s ^ 3 := by positivity
  have ht : 0 ≤ (1 - s) ^ 3 := pow_nonneg (by linarith) 3
  constructor
  · rw [le_div_iff₀ hs3]
    have hq : 0 ≤ 15 * s ^ 4 + 45 * s ^ 3 + 48 * s ^ 2 + 24 * s + 8 := by positivity
    have key : 1 - (1 + 3 / 2 * (1 - s ^ 2) + 15 / 8 * (1 - s ^ 2) ^ 2) * s ^ 3 =
        (1 - s) ^ 3 * (15 * s ^ 4 + 45 * s ^ 3 + 48 * s ^ 2 + 24 * s + 8) / 8 := by ring
    nlinarith [mul_nonneg ht hq]
  · rw [div_le_iff₀ hs3]
    have p2 : (0.99 : ℝ) ^ 2 ≤ s ^ 2 := by gcongr
    have p4 : (0.99 : ℝ) ^ 4 ≤ s ^ 4 := by gcongr
    have p5 : (0.99 : ℝ) ^ 5 ≤ s ^ 5 := by gcongr
    have p6 : (0.99 : ℝ) ^ 6 ≤ s ^ 6 := by gcongr
    have q2 : s ^ 2 ≤ 1 := by nlinarith
    have q3 : s ^ 3 ≤ 1 := by nlinarith
    have hq : 0 ≤ 24 * s ^ 6 + 72 * s ^ 5 + 57 * s ^ 4 - 21 * s ^ 3 - 48 * s ^ 2 - 24 * s - 8 := by
      nlinarith
    have key : (1 + 3 / 2 * (1 - s ^ 2) + 15 / 8 * (1 - s ^ 2) ^ 2 + 3 * (1 - s ^ 2) ^ 3) * s ^ 3 - 1 =
        (1 - s) ^ 3 *
          (24 * s ^ 6 + 72 * s ^ 5 + 57 * s ^ 4 - 21 * s ^ 3 - 48 * s ^ 2 - 24 * s - 8) / 8 := by
      ring
    nlinarith [mul_nonneg ht hq]

theorem integral_sin_sq_quarter : ∫ x in (0 : ℝ)..π / 2, sin x ^ 2 = π / 4 := by
  rw [integral_sin_sq]
  simp only [sin_zero, cos_pi_div_two, mul_zero, zero_mul, sub_zero]
  ring

theorem integral_sin_four_quarter : ∫ x in (0 : ℝ)..π / 2, sin x ^ 4 = 3 * π / 16 := by
  have h := integral_sin_pow (a := 0) (b := π / 2) 2
  simp only [sin_zero, cos_pi_div_two] at h
  norm_num at h
  rw [h]
  ring

/-- Integrating a polynomial in `sin²` over a quarter turn. -/
theorem integral_poly_sin (c₀ c₁ c₂ : ℝ) :
    ∫ x in (0 : ℝ)..π / 2, (c₀ + c₁ * sin x ^ 2 + c₂ * sin x ^ 4) =
      c₀ * (π / 2) + c₁ * (π / 4) + c₂ * (3 * π / 16) := by
  have i0 : IntervalIntegrable (fun _ : ℝ => c₀) MeasureTheory.volume 0 (π / 2) :=
    intervalIntegrable_const
  have i1 : IntervalIntegrable (fun x => c₁ * sin x ^ 2) MeasureTheory.volume 0 (π / 2) :=
    (by fun_prop : Continuous fun x => c₁ * sin x ^ 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => c₂ * sin x ^ 4) MeasureTheory.volume 0 (π / 2) :=
    (by fun_prop : Continuous fun x => c₂ * sin x ^ 4).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (i0.add i1) i2, intervalIntegral.integral_add i0 i1,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_sin_sq_quarter, integral_sin_four_quarter,
    smul_eq_mul]
  ring

namespace ReferenceEllipsoid

variable (E : ReferenceEllipsoid)

/-- The meridian radius squeezed between polynomials in `sin² ψ`, when
`e² ≤ 0.0199`. -/
theorem meridianRadius_poly_bounds (he : E.e2 ≤ 0.0199) (ψ : ℝ) :
    E.a * (1 - E.e2) * (1 + 3 / 2 * E.e2 * sin ψ ^ 2 + 15 / 8 * E.e2 ^ 2 * sin ψ ^ 4) ≤
        E.meridianRadius ψ ∧
      E.meridianRadius ψ ≤ E.a * (1 - E.e2) *
        (1 + 3 / 2 * E.e2 * sin ψ ^ 2 + 15 / 8 * E.e2 ^ 2 * sin ψ ^ 4 + 3 * E.e2 ^ 3) := by
  have hW := E.W2_pos ψ
  have he0 := E.e2_nonneg
  have hsin := sin_sq_le_one ψ
  have hW1 : E.W2 ψ ≤ 1 := by unfold W2; nlinarith [sq_nonneg (sin ψ)]
  have hW0 : 0.9801 ≤ E.W2 ψ := by unfold W2; nlinarith
  set s := √(E.W2 ψ) with hs
  have hss : s ^ 2 = E.W2 ψ := sq_sqrt hW.le
  have hs0 : 0.99 ≤ s := by
    rw [hs, show (0.99 : ℝ) = √(0.99 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num; linarith)
  have hs1 : s ≤ 1 := by rw [hs]; exact sqrt_le_one.mpr hW1
  have hx : 1 - s ^ 2 = E.e2 * sin ψ ^ 2 := by rw [hss, W2]; ring
  have hM : E.meridianRadius ψ = E.a * (1 - E.e2) * (1 / s ^ 3) := by
    rw [meridianRadius, ← hs, ← hss]
    ring
  obtain ⟨hlo, hhi⟩ := inv_cube_bounds hs0 hs1
  rw [hx] at hlo hhi
  have hA : 0 < E.a * (1 - E.e2) := mul_pos E.a_pos E.one_sub_e2_pos
  have hx3 : (E.e2 * sin ψ ^ 2) ^ 3 ≤ E.e2 ^ 3 := by
    rw [mul_pow]
    exact mul_le_of_le_one_right (pow_nonneg he0 3) (by
      exact pow_le_one₀ (sq_nonneg _) hsin)
  rw [hM]
  constructor
  · refine mul_le_mul_of_nonneg_left ?_ hA.le
    nlinarith
  · refine mul_le_mul_of_nonneg_left ?_ hA.le
    nlinarith

/-- So the quarter meridian lies between the integrals of the two polynomials. -/
theorem quarterMeridian_bounds (he : E.e2 ≤ 0.0199) :
    E.a * (1 - E.e2) * (π / 2 + 3 / 8 * E.e2 * π + 45 / 128 * E.e2 ^ 2 * π) ≤
        E.meridianArc (π / 2) ∧
      E.meridianArc (π / 2) ≤ E.a * (1 - E.e2) *
        (π / 2 + 3 / 8 * E.e2 * π + 45 / 128 * E.e2 ^ 2 * π + 3 * E.e2 ^ 3 * (π / 2)) := by
  have hpi := pi_pos
  have hM := E.continuous_meridianRadius.intervalIntegrable (μ := MeasureTheory.volume) 0 (π / 2)
  set A := E.a * (1 - E.e2)
  have hlo := integral_poly_sin A (A * (3 / 2 * E.e2)) (A * (15 / 8 * E.e2 ^ 2))
  have hhi := integral_poly_sin (A * (1 + 3 * E.e2 ^ 3)) (A * (3 / 2 * E.e2)) (A * (15 / 8 * E.e2 ^ 2))
  have cont : ∀ c₀ c₁ c₂ : ℝ, IntervalIntegrable (fun x => c₀ + c₁ * sin x ^ 2 + c₂ * sin x ^ 4)
      MeasureTheory.volume 0 (π / 2) := fun c₀ c₁ c₂ =>
    (by fun_prop : Continuous fun x => c₀ + c₁ * sin x ^ 2 + c₂ * sin x ^ 4).intervalIntegrable _ _
  constructor
  · have := intervalIntegral.integral_mono_on (by linarith) (cont _ _ _) hM fun ψ _ => by
      have h := (E.meridianRadius_poly_bounds he ψ).1
      calc A + A * (3 / 2 * E.e2) * sin ψ ^ 2 + A * (15 / 8 * E.e2 ^ 2) * sin ψ ^ 4 =
          A * (1 + 3 / 2 * E.e2 * sin ψ ^ 2 + 15 / 8 * E.e2 ^ 2 * sin ψ ^ 4) := by ring
        _ ≤ E.meridianRadius ψ := h
    rw [hlo] at this
    rw [meridianArc]
    linarith
  · have := intervalIntegral.integral_mono_on (by linarith) hM (cont _ _ _) fun ψ _ => by
      have h := (E.meridianRadius_poly_bounds he ψ).2
      calc E.meridianRadius ψ ≤ A *
            (1 + 3 / 2 * E.e2 * sin ψ ^ 2 + 15 / 8 * E.e2 ^ 2 * sin ψ ^ 4 + 3 * E.e2 ^ 3) := h
        _ = A * (1 + 3 * E.e2 ^ 3) + A * (3 / 2 * E.e2) * sin ψ ^ 2 +
            A * (15 / 8 * E.e2 ^ 2) * sin ψ ^ 4 := by ring
    rw [hhi] at this
    rw [meridianArc]
    linarith

end ReferenceEllipsoid

/-- The WGS 84 quarter meridian is 10001960 m to 10001975 m, about 0.02 %
longer than the ten thousand kilometres the metre was meant to make it. -/
theorem wgs84_quarterMeridian_bounds :
    10001960 < wgs84.meridianArc (π / 2) ∧ wgs84.meridianArc (π / 2) < 10001975 := by
  have he : wgs84.e2 ≤ 0.0199 := by
    simp only [ReferenceEllipsoid.e2, wgs84_f]; norm_num
  obtain ⟨hlo, hhi⟩ := wgs84.quarterMeridian_bounds he
  simp only [ReferenceEllipsoid.e2, wgs84_a, wgs84_f] at hlo hhi
  norm_num at hlo hhi
  constructor <;> nlinarith [pi_gt_d20, pi_lt_d20]

end Geodesy
