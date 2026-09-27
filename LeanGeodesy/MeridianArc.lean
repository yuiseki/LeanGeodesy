import LeanGeodesy.Curvature
import LeanGeodesy.WGS84
import LeanGeodesy.Angle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Meridian arc length

The distance along the meridian from the equator to geodetic latitude `φ` is

```
m(φ) = ∫₀^φ M(ψ) dψ,
```

the integral of the meridian radius of curvature `M` (`Curvature`). It has
no closed form on an ellipsoid; geodetic software evaluates it by series.
This file proves what the integral itself says:

- `m` changes at rate `M` (`hasDerivAt_meridianArc`), so it is strictly
  increasing (`meridianArc_strictMono`), and it is odd
  (`meridianArc_neg`): south of the equator is the mirror image;
- on a sphere of radius `a` it is `a φ` (`meridianArc_of_sphere`);
- on an ellipsoid it lies between `(b² / a) φ` and `(a² / b) φ` for
  `0 ≤ φ` (`meridianArc_bounds`), because `M` runs from `b² / a` at the
  equator to `a² / b` at the pole (`meridianRadius_zero`,
  `meridianRadius_pi_div_two`, `meridianRadius_mem`). A degree of latitude is
  therefore shorter near the equator than near the poles
  (`meridianArc_band_lt`, `wgs84_first_degree_lt_last_degree`), the
  measurement that showed in the eighteenth century that the Earth is
  flattened. This follows from `M` growing strictly from equator to pole on
  any flattened ellipsoid (`meridianRadius_strictMonoOn`).
-/

namespace Geodesy

open Real

namespace ReferenceEllipsoid

variable (E : ReferenceEllipsoid)

theorem continuous_W2 : Continuous E.W2 := by
  unfold W2
  fun_prop

theorem continuous_meridianRadius : Continuous E.meridianRadius := by
  have hW := E.continuous_W2
  unfold meridianRadius
  refine continuous_const.div (hW.mul hW.sqrt) fun φ => ?_
  have := E.W2_pos φ
  positivity

/-- `M` is the same at `φ` and `-φ`. -/
theorem meridianRadius_neg (φ : ℝ) : E.meridianRadius (-φ) = E.meridianRadius φ := by
  simp [meridianRadius, W2, sin_neg]

/-- At the equator `M = b² / a`, its smallest value. -/
theorem meridianRadius_zero : E.meridianRadius 0 = E.b ^ 2 / E.a := by
  have ha := E.a_pos.ne'
  simp only [meridianRadius, W2, sin_zero]
  rw [E.b_sq]
  norm_num
  field_simp

/-- At the poles `M = a² / b`, its largest value. -/
theorem meridianRadius_pi_div_two : E.meridianRadius (π / 2) = E.a ^ 2 / E.b := by
  have ha := E.a_pos
  have hb := E.b_pos
  have he := E.one_sub_e2_pos
  simp only [meridianRadius, W2, sin_pi_div_two, one_pow, mul_one]
  rw [E.one_sub_e2_eq, sqrt_div' _ (sq_nonneg _), sqrt_sq hb.le, sqrt_sq ha.le]
  field_simp

/-- `M` always lies between its equatorial and polar values. -/
theorem meridianRadius_mem (φ : ℝ) :
    E.b ^ 2 / E.a ≤ E.meridianRadius φ ∧ E.meridianRadius φ ≤ E.a ^ 2 / E.b := by
  have ha := E.a_pos
  have hb := E.b_pos
  have he := E.one_sub_e2_pos
  have hW := E.W2_pos φ
  have hW1 : E.W2 φ ≤ 1 := by
    unfold W2
    nlinarith [E.e2_nonneg, sq_nonneg (sin φ)]
  have hWe : 1 - E.e2 ≤ E.W2 φ := by
    unfold W2
    nlinarith [E.e2_nonneg, sin_sq_le_one φ]
  have hs : 0 < √(E.W2 φ) := sqrt_pos.mpr hW
  have hs1 : √(E.W2 φ) ≤ 1 := sqrt_le_one.mpr hW1
  have hse : √(1 - E.e2) ≤ √(E.W2 φ) := sqrt_le_sqrt hWe
  have hse0 : 0 < √(1 - E.e2) := sqrt_pos.mpr he
  have hbsq : E.b ^ 2 / E.a = E.a * (1 - E.e2) := by
    rw [E.b_sq]; field_simp
  have hasq : E.a ^ 2 / E.b = E.a * (1 - E.e2) / ((1 - E.e2) * √(1 - E.e2)) := by
    rw [E.one_sub_e2_eq, sqrt_div' _ (sq_nonneg _), sqrt_sq hb.le, sqrt_sq ha.le]
    field_simp
  rw [hbsq, hasq, meridianRadius]
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have : E.W2 φ * √(E.W2 φ) ≤ 1 := by nlinarith
    nlinarith [mul_pos ha he]
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul hWe hse hse0.le hW.le)

/-- The meridian arc from the equator to latitude `φ`. -/
noncomputable def meridianArc (φ : ℝ) : ℝ := ∫ ψ in (0 : ℝ)..φ, E.meridianRadius ψ

@[simp] theorem meridianArc_zero : E.meridianArc 0 = 0 := by simp [meridianArc]

/-- The arc grows at the rate `M`. -/
theorem hasDerivAt_meridianArc (φ : ℝ) : HasDerivAt E.meridianArc (E.meridianRadius φ) φ :=
  (E.continuous_meridianRadius.integral_hasStrictDerivAt 0 φ).hasDerivAt

/-- Further north is further along the meridian. -/
theorem meridianArc_strictMono : StrictMono E.meridianArc :=
  strictMono_of_deriv_pos fun φ => by
    rw [(E.hasDerivAt_meridianArc φ).deriv]
    exact E.meridianRadius_pos φ

/-- South of the equator is the mirror image of the north. -/
theorem meridianArc_neg (φ : ℝ) : E.meridianArc (-φ) = -E.meridianArc φ := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := φ) E.meridianRadius
  simp only [E.meridianRadius_neg, neg_zero] at h
  rw [meridianArc, meridianArc, h, intervalIntegral.integral_symm]

/-- On a sphere the meridian arc is `a φ`. -/
theorem meridianArc_of_sphere (hf : E.f = 0) (φ : ℝ) : E.meridianArc φ = E.a * φ := by
  have he : E.e2 = 0 := (E.isSphere_tfae.out 1 3).mp hf
  have hM : ∀ ψ, E.meridianRadius ψ = E.a := fun ψ => by
    simp [meridianRadius, W2, he]
  simp only [meridianArc, hM, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

/-- On an ellipsoid the arc lies between `(b² / a) φ` and `(a² / b) φ`. -/
theorem meridianArc_bounds {φ : ℝ} (hφ : 0 ≤ φ) :
    E.b ^ 2 / E.a * φ ≤ E.meridianArc φ ∧ E.meridianArc φ ≤ E.a ^ 2 / E.b * φ := by
  have hi := E.continuous_meridianRadius.intervalIntegrable (μ := MeasureTheory.volume) 0 φ
  have hc : ∀ c : ℝ, ∫ _ in (0 : ℝ)..φ, c = c * φ := fun c => by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
  constructor
  · rw [← hc]
    exact intervalIntegral.integral_mono_on hφ intervalIntegrable_const hi
      fun ψ _ => (E.meridianRadius_mem ψ).1
  · rw [← hc]
    exact intervalIntegral.integral_mono_on hφ hi intervalIntegrable_const
      fun ψ _ => (E.meridianRadius_mem ψ).2

/-- On a flattened ellipsoid `M` grows strictly from the equator to the pole. -/
theorem meridianRadius_strictMonoOn (hf : 0 < E.f) :
    StrictMonoOn E.meridianRadius (Set.Icc 0 (π / 2)) := by
  intro x hx y hy hxy
  have he : 0 < E.e2 := mul_pos hf (by linarith [E.f_lt_one])
  have hpi := pi_pos
  have hsx : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2])
  have hsxy : sin x < sin y :=
    strictMonoOn_sin ⟨by linarith [hx.1], hx.2⟩ ⟨by linarith [hy.1], hy.2⟩ hxy
  have hW : E.W2 y < E.W2 x := by
    unfold W2
    nlinarith [mul_lt_mul_of_pos_left (mul_self_lt_mul_self hsx hsxy) he]
  have hWy := E.W2_pos y
  have hsy : 0 < √(E.W2 y) := sqrt_pos.mpr hWy
  have hsq : √(E.W2 y) < √(E.W2 x) := sqrt_lt_sqrt hWy.le hW
  have hden : E.W2 y * √(E.W2 y) < E.W2 x * √(E.W2 x) := mul_lt_mul hW hsq.le hsy (E.W2_pos x).le
  unfold meridianRadius
  exact div_lt_div_of_pos_left (mul_pos E.a_pos E.one_sub_e2_pos) (by positivity) hden

/-- The arc between two latitudes is the integral of `M` between them. -/
theorem meridianArc_sub (φ₁ φ₂ : ℝ) :
    E.meridianArc φ₂ - E.meridianArc φ₁ = ∫ ψ in φ₁..φ₂, E.meridianRadius ψ := by
  have hi := fun a b => E.continuous_meridianRadius.intervalIntegrable (μ := MeasureTheory.volume) a b
  rw [meridianArc, meridianArc, intervalIntegral.integral_interval_sub_left (hi 0 φ₂) (hi 0 φ₁)]

/-- On a flattened ellipsoid a band of latitude of the same width is longer
along the meridian the further it is from the equator: a degree of
latitude is shortest at the equator and longest at the poles. -/
theorem meridianArc_band_lt (hf : 0 < E.f) {φ₁ φ₂ δ : ℝ} (hδ : 0 < δ) (h₁ : 0 ≤ φ₁)
    (h₁₂ : φ₁ < φ₂) (h₂ : φ₂ + δ ≤ π / 2) :
    E.meridianArc (φ₁ + δ) - E.meridianArc φ₁ < E.meridianArc (φ₂ + δ) - E.meridianArc φ₂ := by
  have hc := E.continuous_meridianRadius
  rw [E.meridianArc_sub, E.meridianArc_sub]
  have hshift := intervalIntegral.integral_comp_add_right (a := φ₁) (b := φ₁ + δ)
    E.meridianRadius (φ₂ - φ₁)
  rw [show φ₁ + (φ₂ - φ₁) = φ₂ by ring, show φ₁ + δ + (φ₂ - φ₁) = φ₂ + δ by ring] at hshift
  rw [← hshift]
  have hlt : ∀ x ∈ Set.Icc φ₁ (φ₁ + δ), E.meridianRadius x < E.meridianRadius (x + (φ₂ - φ₁)) :=
    fun x hx => E.meridianRadius_strictMonoOn hf ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hx.1], by linarith [hx.2]⟩ (by linarith)
  exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by linarith)
    hc.continuousOn (hc.comp (continuous_add_const _)).continuousOn
    (fun x hx => (hlt x ⟨hx.1.le, hx.2⟩).le) ⟨φ₁, ⟨le_rfl, by linarith⟩, hlt φ₁ ⟨le_rfl, by linarith⟩⟩

end ReferenceEllipsoid

/-- On WGS 84 the first degree of latitude north of the equator is shorter
along the meridian than the last degree before the pole. -/
theorem wgs84_first_degree_lt_last_degree :
    wgs84.meridianArc (degToRad 1) - wgs84.meridianArc 0 <
      wgs84.meridianArc (degToRad 89 + degToRad 1) - wgs84.meridianArc (degToRad 89) := by
  have hpi := pi_pos
  have h := wgs84.meridianArc_band_lt (by simp; norm_num) (φ₁ := 0) (φ₂ := degToRad 89)
    (δ := degToRad 1) (by unfold degToRad; positivity) le_rfl (by unfold degToRad; positivity)
    (by unfold degToRad; linarith)
  simpa using h


end Geodesy
