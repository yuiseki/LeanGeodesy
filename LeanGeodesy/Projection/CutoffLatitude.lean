import LeanGeodesy.Projection.WebMercator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Web Mercator stops at 85.05°

Web maps end a little short of the poles, at the latitude `maxLatitude`
where the northing reaches `π a` and the world becomes a square
(`y_maxLatitude`). This file pins that latitude down in degrees:

```
85.05° < maxLatitude < 85.06°        (maxLatitude_deg_bounds)
```

The value often quoted is 85.0511°. The proof shows where it comes from.
Since `tan (maxLatitude) = sinh π`, its cosine is `1 / cosh π`
(`cos_maxLatitude`), so the question is about `e^π`, which is between
23.14 and 23.15 (`exp_pi_bounds`, from `e^π = e³ e^(π - 3)` and the
Taylor series of `e^(π - 3)`). Comparing `1 / cosh π` with
`cos 85.05° = sin 4.95°` and `cos 85.06° = sin 4.94°`, bounded by the Taylor
series of `sin`, gives the result.
-/

namespace Geodesy.Projection

open Real

/-- `cos (maxLatitude) = 1 / cosh π`. -/
theorem cos_maxLatitude : cos maxLatitude = 1 / cosh π := by
  rw [maxLatitude, gd, cos_arctan, add_comm, ← cosh_sq, sqrt_sq (cosh_pos π).le]

/-- `e^(π - 3)`, from the first four terms of its Taylor series. -/
theorem exp_pi_sub_three_bounds : 1.152089 < exp (π - 3) ∧ exp (π - 3) < 1.152112 := by
  have hlo : (0.141592 : ℝ) < π - 3 := by linarith [pi_gt_d6]
  have hhi : π - 3 < (0.141593 : ℝ) := by linarith [pi_lt_d6]
  constructor
  · have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.141592) 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    calc (1.152089 : ℝ) < exp 0.141592 := by linarith
      _ < exp (π - 3) := exp_lt_exp.mpr hlo
  · have h := exp_bound' (by norm_num : (0 : ℝ) ≤ 0.141593) (by norm_num) (n := 4) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    calc exp (π - 3) < exp 0.141593 := exp_lt_exp.mpr hhi
      _ < 1.152112 := by linarith

/-- `e^π` is between 23.14 and 23.15. -/
theorem exp_pi_bounds : 23.14 < exp π ∧ exp π < 23.15 := by
  have he : exp π = exp 1 ^ 3 * exp (π - 3) := by
    rw [← exp_nat_mul, ← exp_add]
    congr 1
    push_cast
    ring
  have h1 := exp_one_gt_d9
  have h2 := exp_one_lt_d9
  have h3 := exp_pi_sub_three_bounds
  have e3lo : (2.7182818283 : ℝ) ^ 3 < exp 1 ^ 3 := by gcongr
  have e3hi : exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 := by gcongr
  have hpos : 0 < exp (π - 3) := exp_pos _
  rw [he]
  constructor <;> nlinarith

/-- So `1 / cosh π` is between 0.086225 and 0.086275. -/
theorem inv_cosh_pi_bounds : 0.086225 < 1 / cosh π ∧ 1 / cosh π < 0.086275 := by
  obtain ⟨hlo, hhi⟩ := exp_pi_bounds
  have hpos : 0 < exp π := exp_pos π
  have hneg : exp (-π) = 1 / exp π := by rw [exp_neg, one_div]
  -- `e^π + e^(-π)` is between 23.183 and 23.1933.
  have hsum_lo : 23.183 < exp π + exp (-π) := by
    rw [hneg]
    have : 1 / 23.15 < 1 / exp π := by
      rw [div_lt_div_iff₀ (by norm_num) hpos]; linarith
    linarith [show (1 : ℝ) / 23.15 > 0.0431 by norm_num]
  have hsum_hi : exp π + exp (-π) < 23.1933 := by
    rw [hneg]
    have : 1 / exp π < 1 / 23.14 := by
      rw [div_lt_div_iff₀ hpos (by norm_num)]; linarith
    linarith [show (1 : ℝ) / 23.14 < 0.043216 by norm_num]
  rw [cosh_eq]
  have hc : 0 < (exp π + exp (-π)) / 2 := by positivity
  constructor
  · rw [lt_div_iff₀ hc]; linarith
  · rw [div_lt_iff₀ hc]; linarith

/-- `sin 4.95°` is more than 0.086275. -/
theorem sin_degToRad_495_gt : 0.086275 < sin (degToRad 4.95) := by
  set x := degToRad 4.95 with hx
  have hxlo : 0.086393 < x := by rw [hx, degToRad]; nlinarith [pi_gt_d6]
  have hxhi : x < 0.086394 := by rw [hx, degToRad]; nlinarith [pi_lt_d6]
  have hx0 : 0 ≤ x := by linarith
  have hb := sin_bound (x := x) (by rw [abs_of_nonneg hx0]; linarith)
  rw [abs_of_nonneg hx0] at hb
  have h3 : x ^ 3 ≤ (0.086394 : ℝ) ^ 3 := by gcongr
  have h4 : x ^ 4 ≤ (0.086394 : ℝ) ^ 4 := by gcongr
  have := neg_le_of_abs_le hb
  nlinarith

/-- `sin 4.94°` is less than 0.086225. -/
theorem sin_degToRad_494_lt : sin (degToRad 4.94) < 0.086225 := by
  have hx : 0 < degToRad 4.94 := by rw [degToRad]; positivity
  have hxhi : degToRad 4.94 < 0.08622 := by rw [degToRad]; nlinarith [pi_lt_d6]
  linarith [sin_lt hx]

theorem cos_degToRad_eq_sin (d : ℝ) : cos (degToRad d) = sin (degToRad (90 - d)) := by
  rw [← sin_pi_div_two_sub]
  congr 1
  unfold degToRad
  ring

/-- Web Mercator's cut-off latitude is between 85.05° and 85.06°. -/
theorem maxLatitude_deg_bounds : 85.05 < radToDeg maxLatitude ∧ radToDeg maxLatitude < 85.06 := by
  have hm := maxLatitude_mem
  have hm0 := maxLatitude_pos
  have hpi := pi_pos
  have mem : ∀ d : ℝ, 0 ≤ d → d ≤ 90 → degToRad d ∈ Set.Icc 0 π := fun d h0 h1 => by
    unfold degToRad
    constructor
    · positivity
    · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 180)]; nlinarith
  have hmI : maxLatitude ∈ Set.Icc 0 π := ⟨hm0.le, by linarith [hm.2]⟩
  have hiff : ∀ d : ℝ, d < radToDeg maxLatitude ↔ degToRad d < maxLatitude := fun d => by
    rw [← degToRad_strictMono.lt_iff_lt, degToRad_radToDeg]
  have hiff' : ∀ d : ℝ, radToDeg maxLatitude < d ↔ maxLatitude < degToRad d := fun d => by
    rw [← degToRad_strictMono.lt_iff_lt, degToRad_radToDeg]
  obtain ⟨hclo, hchi⟩ := inv_cosh_pi_bounds
  constructor
  · rw [hiff, ← strictAntiOn_cos.lt_iff_lt hmI (mem 85.05 (by norm_num) (by norm_num)),
      cos_maxLatitude, cos_degToRad_eq_sin, show (90 : ℝ) - 85.05 = 4.95 by norm_num]
    linarith [sin_degToRad_495_gt]
  · rw [hiff', ← strictAntiOn_cos.lt_iff_lt (mem 85.06 (by norm_num) (by norm_num)) hmI,
      cos_maxLatitude, cos_degToRad_eq_sin, show (90 : ℝ) - 85.06 = 4.94 by norm_num]
    linarith [sin_degToRad_494_lt]

end Geodesy.Projection
