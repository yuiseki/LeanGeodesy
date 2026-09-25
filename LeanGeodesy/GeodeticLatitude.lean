import LeanGeodesy.Angle
import LeanGeodesy.ReferenceEllipsoid
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Geodetic latitude

On a sphere the latitude of a point is the angle, seen from the centre,
between the point and the equatorial plane. On an ellipsoid that angle has
its own name, the *geocentric* latitude `ψ`, and it is not the latitude on
maps. The *geodetic* latitude `φ` is the angle between the equatorial plane
and the ellipsoid's normal at the point: the direction a plumb line would
hang if gravity were perpendicular to the ellipsoid.

In a meridian plane, with `p` the distance from the axis and `z` the height
above the equator, the point at geodetic latitude `φ` is

```
p = N cos φ,   z = N (1 - e²) sin φ,   N = a / √(1 - e² sin² φ)
```

where `N` is the radius of curvature in the prime vertical. This file proves
that this point lies on the ellipse (`meridianPoint_mem`), that the normal
there points at angle `φ` (`meridianNormal_eq`), and that its geocentric
latitude satisfies `tan ψ = (1 - e²) tan φ` (`geocentric_tan`), so the two
latitudes agree exactly on a sphere and differ on the Earth.

Latitude runs from the south pole to the north pole and does not wrap
around, so it is a real number in `[-π/2, π/2]`, unlike longitude.
-/

namespace Geodesy

open Real

/-- A geodetic latitude, in radians, from the south pole to the north pole. -/
def GeodeticLatitude := {φ : ℝ // -(π / 2) ≤ φ ∧ φ ≤ π / 2}

namespace GeodeticLatitude

/-- The latitude with this many degrees north, which must be in `[-90, 90]`. -/
noncomputable def ofDegrees (d : ℝ) (h : -90 ≤ d ∧ d ≤ 90) : GeodeticLatitude :=
  ⟨degToRad d, by
    have := pi_pos
    unfold degToRad
    constructor <;> nlinarith [h.1, h.2]⟩

noncomputable def equator : GeodeticLatitude := ⟨0, by constructor <;> linarith [pi_pos]⟩
noncomputable def northPole : GeodeticLatitude := ⟨π / 2, by constructor <;> linarith [pi_pos]⟩
noncomputable def southPole : GeodeticLatitude := ⟨-(π / 2), by constructor <;> linarith [pi_pos]⟩

/-- The cosine of a latitude is never negative. -/
theorem cos_nonneg (φ : GeodeticLatitude) : 0 ≤ cos φ.1 :=
  Real.cos_nonneg_of_neg_pi_div_two_le_of_le φ.2.1 φ.2.2

end GeodeticLatitude

/-! ## The meridian ellipse -/

namespace ReferenceEllipsoid

variable (E : ReferenceEllipsoid)

/-- `1 - e² sin² φ`, always positive. -/
theorem one_sub_e2_sin_sq_pos (φ : ℝ) : 0 < 1 - E.e2 * sin φ ^ 2 := by
  have h1 := sin_sq_le_one φ
  have h2 := E.e2_nonneg
  have h3 := E.e2_lt_one
  nlinarith

/-- The radius of curvature in the prime vertical at latitude `φ`. -/
noncomputable def primeVerticalRadius (φ : ℝ) : ℝ := E.a / √(1 - E.e2 * sin φ ^ 2)

theorem primeVerticalRadius_pos (φ : ℝ) : 0 < E.primeVerticalRadius φ :=
  div_pos E.a_pos (sqrt_pos.mpr (E.one_sub_e2_sin_sq_pos φ))

theorem primeVerticalRadius_sq (φ : ℝ) :
    E.primeVerticalRadius φ ^ 2 = E.a ^ 2 / (1 - E.e2 * sin φ ^ 2) := by
  rw [primeVerticalRadius, div_pow, sq_sqrt (E.one_sub_e2_sin_sq_pos φ).le]

/-- At the equator `N = a`. -/
theorem primeVerticalRadius_zero : E.primeVerticalRadius 0 = E.a := by
  simp [primeVerticalRadius]

/-- At the poles `N = a² / b`, the largest value. -/
theorem primeVerticalRadius_pi_div_two : E.primeVerticalRadius (π / 2) = E.a ^ 2 / E.b := by
  rw [primeVerticalRadius, sin_pi_div_two, one_pow, mul_one, one_sub_e2_eq,
    sqrt_div' _ (sq_nonneg _), sqrt_sq E.b_pos.le, sqrt_sq E.a_pos.le]
  field_simp [E.a_pos.ne', E.b_pos.ne']
  ring

/-- The point of the meridian ellipse at geodetic latitude `φ`: its distance
from the axis and its height above the equatorial plane. -/
noncomputable def meridianPoint (φ : ℝ) : ℝ × ℝ :=
  (E.primeVerticalRadius φ * cos φ, E.primeVerticalRadius φ * (1 - E.e2) * sin φ)

/-- The point lies on the meridian ellipse `p² / a² + z² / b² = 1`. -/
theorem meridianPoint_mem (φ : ℝ) :
    (E.meridianPoint φ).1 ^ 2 / E.a ^ 2 + (E.meridianPoint φ).2 ^ 2 / E.b ^ 2 = 1 := by
  have hD := E.one_sub_e2_sin_sq_pos φ
  have he := E.one_sub_e2_pos
  have ha := E.a_pos.ne'
  simp only [meridianPoint]
  rw [E.b_sq, mul_pow, mul_pow, mul_pow, E.primeVerticalRadius_sq, cos_sq' φ]
  field_simp
  ring

/-- The direction of the ellipse's normal at `(p, z)`: the gradient of
`p² / a² + z² / b²`, up to a factor of two. -/
noncomputable def meridianNormal (φ : ℝ) : ℝ × ℝ :=
  ((E.meridianPoint φ).1 / E.a ^ 2, (E.meridianPoint φ).2 / E.b ^ 2)

/-- The normal at the point points in direction `(cos φ, sin φ)`: its angle
above the equatorial plane is the geodetic latitude `φ`. -/
theorem meridianNormal_eq (φ : ℝ) :
    E.meridianNormal φ = (E.primeVerticalRadius φ / E.a ^ 2) • (cos φ, sin φ) := by
  have he := E.one_sub_e2_pos.ne'
  have ha := E.a_pos.ne'
  simp only [meridianNormal, meridianPoint, E.b_sq, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
  constructor
  · ring
  · field_simp
    ring

/-- The geocentric latitude `ψ` of the point, seen from the centre, has
`tan ψ = z / p = (1 - e²) tan φ`. -/
theorem geocentric_tan {φ : ℝ} (hc : cos φ ≠ 0) :
    (E.meridianPoint φ).2 / (E.meridianPoint φ).1 = (1 - E.e2) * tan φ := by
  have hN := (E.primeVerticalRadius_pos φ).ne'
  simp only [meridianPoint]
  rw [tan_eq_sin_div_cos]
  field_simp
  ring

/-- On a sphere, geodetic and geocentric latitude agree. -/
theorem geocentric_tan_of_sphere (hf : E.f = 0) {φ : ℝ} (hc : cos φ ≠ 0) :
    (E.meridianPoint φ).2 / (E.meridianPoint φ).1 = tan φ := by
  have he : E.e2 = 0 := (E.isSphere_tfae.out 0 2).mp hf
  rw [E.geocentric_tan hc, he, sub_zero, one_mul]

/-- On a flattened ellipsoid the geocentric latitude is never further from
the equator than the geodetic one: `|tan ψ| ≤ |tan φ|`. -/
theorem abs_geocentric_tan_le {φ : ℝ} (hc : cos φ ≠ 0) :
    |(E.meridianPoint φ).2 / (E.meridianPoint φ).1| ≤ |tan φ| := by
  rw [E.geocentric_tan hc, abs_mul, abs_of_pos E.one_sub_e2_pos]
  have := E.e2_nonneg
  have := abs_nonneg (tan φ)
  nlinarith

end ReferenceEllipsoid

end Geodesy
