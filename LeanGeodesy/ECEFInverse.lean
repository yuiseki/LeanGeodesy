import LeanGeodesy.GeodeticCoordinate
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# From ECEF back to geodetic coordinates

`GeodeticCoordinate.toECEF` turns latitude, longitude and height into a
point of space. This file goes the other way.

- The longitude is the direction of the point's shadow on the equatorial
  plane: the argument of `x + y i` (`ecefLongitude_toECEF`).
-/

namespace Geodesy

open Real

/-- The longitude of the ECEF point with coordinates `x, y`: the argument of
`x + y i`. -/
noncomputable def ecefLongitude (x y : ℝ) : GeodeticLongitude := (Complex.arg ⟨x, y⟩ : Real.Angle)

namespace GeodeticCoordinate

variable (E : ReferenceEllipsoid) (c : GeodeticCoordinate)

/-- The `x` and `y` coordinates of the ECEF position: `(N + h) cos φ` times the
cosine and sine of the longitude. -/
theorem toECEF_horizontal :
    (toECEF E c) 0 = (E.primeVerticalRadius c.lat.1 + c.height) * cos c.lat.1 * cos c.lon.toReal ∧
      (toECEF E c) 1 =
        (E.primeVerticalRadius c.lat.1 + c.height) * cos c.lat.1 * sin c.lon.toReal := by
  simp [toECEF, Real.Angle.cos_toReal, Real.Angle.sin_toReal]

/-- The longitude is recovered from the ECEF position, as long as the point
is not on the axis and is on the same side of it as its surface point. -/
theorem ecefLongitude_toECEF (hc : 0 < cos c.lat.1)
    (hN : 0 < E.primeVerticalRadius c.lat.1 + c.height) :
    ecefLongitude ((toECEF E c) 0) ((toECEF E c) 1) = c.lon := by
  obtain ⟨hx, hy⟩ := toECEF_horizontal E c
  set r := (E.primeVerticalRadius c.lat.1 + c.height) * cos c.lat.1 with hr
  set θ := c.lon.toReal
  have hr0 : 0 < r := mul_pos hN hc
  have hz : (⟨(toECEF E c) 0, (toECEF E c) 1⟩ : ℂ) =
      (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    apply Complex.ext <;>
      simp [hx, hy, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im]
  rw [ecefLongitude, hz, Complex.arg_real_mul _ hr0,
    Complex.arg_cos_add_sin_mul_I ⟨Real.Angle.neg_pi_lt_toReal _, Real.Angle.toReal_le_pi _⟩,
    Real.Angle.coe_toReal]

end GeodeticCoordinate

end Geodesy
