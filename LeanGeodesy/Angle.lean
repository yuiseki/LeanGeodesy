import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Angles: degrees, radians, degrees-minutes-seconds

Coordinates are published in degrees, often as degrees, minutes and seconds,
while trigonometry works in radians. Everything in this library is in
radians; these conversions connect the two.

A full turn is 360 degrees or `2π` radians, so one degree is `π / 180`
radians. A minute is a sixtieth of a degree and a second a sixtieth of a
minute.
-/

namespace Geodesy

open Real

/-- Degrees to radians. -/
noncomputable def degToRad (d : ℝ) : ℝ := d * π / 180

/-- Radians to degrees. -/
noncomputable def radToDeg (r : ℝ) : ℝ := r * 180 / π

theorem radToDeg_degToRad (d : ℝ) : radToDeg (degToRad d) = d := by
  unfold radToDeg degToRad
  field_simp

theorem degToRad_radToDeg (r : ℝ) : degToRad (radToDeg r) = r := by
  unfold radToDeg degToRad
  field_simp

@[simp] theorem degToRad_zero : degToRad 0 = 0 := by simp [degToRad]

theorem degToRad_90 : degToRad 90 = π / 2 := by unfold degToRad; ring

theorem degToRad_180 : degToRad 180 = π := by unfold degToRad; ring

theorem degToRad_360 : degToRad 360 = 2 * π := by unfold degToRad; ring

theorem degToRad_neg (d : ℝ) : degToRad (-d) = -degToRad d := by unfold degToRad; ring

theorem degToRad_add (d e : ℝ) : degToRad (d + e) = degToRad d + degToRad e := by
  unfold degToRad; ring

/-- More degrees is more radians. -/
theorem degToRad_strictMono : StrictMono degToRad := by
  intro d e h
  unfold degToRad
  have := pi_pos
  apply div_lt_div_of_pos_right _ (by norm_num)
  exact mul_lt_mul_of_pos_right h this

theorem degToRad_le_iff {d e : ℝ} : degToRad d ≤ degToRad e ↔ d ≤ e :=
  degToRad_strictMono.le_iff_le

/-- Degrees, minutes and seconds as decimal degrees. For a negative angle the
sign applies to the whole value, so pass nonnegative parts and negate the
result. -/
noncomputable def dms (d m s : ℝ) : ℝ := d + m / 60 + s / 3600

theorem dms_one_minute : dms 0 1 0 = 1 / 60 := by norm_num [dms]

theorem dms_one_second : dms 0 0 1 = 1 / 3600 := by norm_num [dms]

/-- Sixty minutes make a degree, sixty seconds a minute. -/
theorem dms_carry (d m s : ℝ) : dms d (m + 60) s = dms (d + 1) m s ∧
    dms d m (s + 60) = dms d (m + 1) s := by
  constructor <;> (unfold dms; ring)

end Geodesy
