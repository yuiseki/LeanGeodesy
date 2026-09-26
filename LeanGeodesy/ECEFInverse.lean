import LeanGeodesy.GeodeticCoordinate
import LeanGeodesy.Curvature
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# From ECEF back to geodetic coordinates

`GeodeticCoordinate.toECEF` turns latitude, longitude and height into a
point of space. This file goes the other way.

- The longitude is the direction of the point's shadow on the equatorial
  plane: the argument of `x + y i` (`ecefLongitude_toECEF`).
- With `p = √(x² + y²)` the distance from the axis (`toECEF_p`), the
  geodetic latitude `φ` is a root of
  `p sin φ - z cos φ - e² N(φ) sin φ cos φ` (`latitudeResidual_toECEF`),
  the equation that iterative ECEF-to-geodetic methods solve, and once `φ`
  is known the height is
  `h = p cos φ + z sin φ - a √(1 - e² sin² φ)` (`height_eq`), with no
  division by `cos φ`, so it stays accurate near the poles.
-/

namespace Geodesy

open Real

/-- The longitude of the ECEF point with coordinates `x, y`: the argument of
`x + y i`. -/
noncomputable def ecefLongitude (x y : ℝ) : GeodeticLongitude := (Complex.arg ⟨x, y⟩ : Real.Angle)

namespace ReferenceEllipsoid

variable (E : ReferenceEllipsoid)

/-- The residual of the latitude equation for a point at distance `p` from the
axis and height `z` above the equatorial plane. -/
noncomputable def latitudeResidual (p z φ : ℝ) : ℝ :=
  p * sin φ - z * cos φ - E.e2 * E.primeVerticalRadius φ * sin φ * cos φ

/-- `a √(1 - e² sin² φ) = N (1 - e² sin² φ)`. -/
theorem a_mul_sqrt_W2 (φ : ℝ) : E.a * √(E.W2 φ) = E.primeVerticalRadius φ * E.W2 φ := by
  have hW := E.W2_pos φ
  have hs : 0 < √(E.W2 φ) := sqrt_pos.mpr hW
  rw [primeVerticalRadius, show 1 - E.e2 * sin φ ^ 2 = E.W2 φ from rfl]
  field_simp
  rw [mul_assoc, ← sq, sq_sqrt hW.le]

end ReferenceEllipsoid

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

/-- The distance of the ECEF position from the axis is `(N + h) cos φ`, when
`N + h ≥ 0`. -/
theorem toECEF_p (hN : 0 ≤ E.primeVerticalRadius c.lat.1 + c.height) :
    √((toECEF E c) 0 ^ 2 + (toECEF E c) 1 ^ 2) =
      (E.primeVerticalRadius c.lat.1 + c.height) * cos c.lat.1 := by
  obtain ⟨hx, hy⟩ := toECEF_horizontal E c
  have hc := GeodeticLatitude.cos_nonneg c.lat
  rw [hx, hy, show ∀ A B C : ℝ, (A * B * C) ^ 2 + (A * B * sin c.lon.toReal) ^ 2 =
      (A * B) ^ 2 * (C ^ 2 + sin c.lon.toReal ^ 2) from fun A B C => by ring,
    cos_sq_add_sin_sq, mul_one, sqrt_sq (mul_nonneg hN hc)]

/-- The geodetic latitude solves the latitude equation. -/
theorem latitudeResidual_toECEF :
    E.latitudeResidual ((E.primeVerticalRadius c.lat.1 + c.height) * cos c.lat.1)
      ((toECEF E c) 2) c.lat.1 = 0 := by
  simp only [ReferenceEllipsoid.latitudeResidual, toECEF, vec3_2]
  ring

/-- The height from the distance to the axis, the height above the equator and
the latitude. -/
theorem height_eq :
    c.height = (E.primeVerticalRadius c.lat.1 + c.height) * cos c.lat.1 * cos c.lat.1 +
      (toECEF E c) 2 * sin c.lat.1 - E.a * √(E.W2 c.lat.1) := by
  rw [E.a_mul_sqrt_W2]
  simp only [toECEF, vec3_2, ReferenceEllipsoid.W2]
  have hp := sin_sq_add_cos_sq c.lat.1
  linear_combination (-(E.primeVerticalRadius c.lat.1 + c.height)) * hp

end GeodeticCoordinate

end Geodesy
