import LeanGeodesy.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Geodetic longitude

Longitude is the angle east of the prime meridian, measured around the
Earth's axis. Going once around brings you back: 190° east is 170° west.
So a longitude is not a real number but an angle modulo a full turn, which
is exactly Mathlib's `Real.Angle`, the reals modulo `2π`.

Published coordinates pick one representative, in `(-180°, 180°]`.
`Real.Angle.toReal` picks the representative in `(-π, π]`, which is the same
convention in radians (`toDegrees_mem`). The antimeridian shows the choice:
180° east and 180° west are one longitude (`antimeridian`), written 180.
-/

namespace Geodesy

open Real

/-- A geodetic longitude: an angle modulo a full turn. -/
abbrev GeodeticLongitude := Real.Angle

namespace GeodeticLongitude

/-- The longitude with this many degrees east. -/
noncomputable def ofDegrees (d : ℝ) : GeodeticLongitude := (degToRad d : Real.Angle)

/-- The longitude in degrees, in `(-180, 180]`. -/
noncomputable def toDegrees (lon : GeodeticLongitude) : ℝ := radToDeg lon.toReal

/-- The published representative lies in `(-180°, 180°]`. -/
theorem toDegrees_mem (lon : GeodeticLongitude) :
    -180 < toDegrees lon ∧ toDegrees lon ≤ 180 := by
  have h₁ := Real.Angle.neg_pi_lt_toReal lon
  have h₂ := Real.Angle.toReal_le_pi lon
  have hpi := pi_pos
  unfold toDegrees radToDeg
  constructor
  · rw [lt_div_iff₀ hpi]; nlinarith
  · rw [div_le_iff₀ hpi]; nlinarith

/-- Adding a full turn does not change a longitude. -/
theorem ofDegrees_add_360 (d : ℝ) : ofDegrees (d + 360) = ofDegrees d := by
  rw [ofDegrees, ofDegrees, degToRad_add, degToRad_360, Real.Angle.coe_add,
    Real.Angle.coe_two_pi, add_zero]

/-- 180° east and 180° west are the same longitude. -/
theorem antimeridian : ofDegrees 180 = ofDegrees (-180) := by
  rw [← ofDegrees_add_360 (-180)]
  norm_num

/-- A longitude given in `(-180°, 180°]` is read back unchanged. -/
theorem toDegrees_ofDegrees {d : ℝ} (h : -180 < d ∧ d ≤ 180) :
    toDegrees (ofDegrees d) = d := by
  have hpi := pi_pos
  have hr : (degToRad d : Real.Angle).toReal = degToRad d := by
    rw [Real.Angle.toReal_coe_eq_self_iff]
    unfold degToRad
    constructor
    · rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 180)]; nlinarith
    · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 180)]; nlinarith
  rw [toDegrees, ofDegrees, hr, radToDeg_degToRad]

/-- 180° west is published as 180. -/
theorem toDegrees_ofDegrees_neg180 : toDegrees (ofDegrees (-180)) = 180 := by
  rw [← antimeridian, toDegrees_ofDegrees (by norm_num)]

/-- Cosine and sine of a longitude, computed from any representative. -/
theorem cos_ofDegrees (d : ℝ) : Real.Angle.cos (ofDegrees d) = Real.cos (degToRad d) :=
  Real.Angle.cos_coe _

theorem sin_ofDegrees (d : ℝ) : Real.Angle.sin (ofDegrees d) = Real.sin (degToRad d) :=
  Real.Angle.sin_coe _

end GeodeticLongitude

end Geodesy
