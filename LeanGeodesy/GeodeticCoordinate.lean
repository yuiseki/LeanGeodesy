import LeanGeodesy.GeodeticLatitude
import LeanGeodesy.GeodeticLongitude

/-!
# Geodetic coordinates

A geodetic coordinate is a latitude `φ`, a longitude `λ` and an ellipsoidal
height `h`, all relative to a reference ellipsoid. It names a point of space
in Earth-centred, Earth-fixed (ECEF) coordinates:

```
x = (N + h) cos φ cos λ
y = (N + h) cos φ sin λ
z = (N (1 - e²) + h) sin φ
```

with `N` the prime vertical radius of curvature at `φ`. This file proves what
makes these coordinates geodetic:

- at `h = 0` the point lies on the ellipsoid (`surfacePoint_mem`);
- the ellipsoid's normal there is the unit vector `n` with elevation `φ` and
  azimuth `λ` (`gradient_eq`);
- the point at height `h` is `h` metres from the surface point along that
  normal (`toECEF_eq`), so the height is measured along the normal, not
  towards the centre;
- on a sphere all of this reduces to the point at distance `R + h` from the
  centre in direction `n` (`toECEF_of_sphere`).
-/

namespace Geodesy

open Real

/-- Latitude, longitude and ellipsoidal height. -/
structure GeodeticCoordinate where
  /-- Geodetic latitude, in `[-π/2, π/2]`. -/
  lat : GeodeticLatitude
  /-- Longitude, an angle modulo a full turn. -/
  lon : GeodeticLongitude
  /-- Height above the ellipsoid, along its normal, in metres. -/
  height : ℝ

namespace GeodeticCoordinate

variable (E : ReferenceEllipsoid) (c : GeodeticCoordinate)

/-- The unit vector with elevation `φ` and azimuth `λ`: the ellipsoid's outward
normal at this latitude and longitude. -/
noncomputable def normal : E3 :=
  vec3 (cos c.lat.1 * Real.Angle.cos c.lon) (cos c.lat.1 * Real.Angle.sin c.lon) (sin c.lat.1)

theorem norm_normal : ‖c.normal‖ = 1 := by
  have hl := Real.Angle.cos_sq_add_sin_sq c.lon
  have hp := sin_sq_add_cos_sq c.lat.1
  have : ‖c.normal‖ ^ 2 = 1 := by
    rw [norm_sq_eq]
    simp only [normal, vec3_0, vec3_1, vec3_2]
    nlinarith [hl, hp]
  nlinarith [norm_nonneg c.normal]

/-- The point on the ellipsoid at this latitude and longitude. -/
noncomputable def surfacePoint : E3 :=
  vec3 (E.primeVerticalRadius c.lat.1 * cos c.lat.1 * Real.Angle.cos c.lon)
    (E.primeVerticalRadius c.lat.1 * cos c.lat.1 * Real.Angle.sin c.lon)
    (E.primeVerticalRadius c.lat.1 * (1 - E.e2) * sin c.lat.1)

/-- The Earth-centred, Earth-fixed position. -/
noncomputable def toECEF : E3 :=
  vec3 ((E.primeVerticalRadius c.lat.1 + c.height) * cos c.lat.1 * Real.Angle.cos c.lon)
    ((E.primeVerticalRadius c.lat.1 + c.height) * cos c.lat.1 * Real.Angle.sin c.lon)
    ((E.primeVerticalRadius c.lat.1 * (1 - E.e2) + c.height) * sin c.lat.1)

/-- The surface point lies on the ellipsoid. -/
theorem surfacePoint_mem : surfacePoint E c ∈ E.toSet := by
  have hm := E.meridianPoint_mem c.lat.1
  simp only [ReferenceEllipsoid.meridianPoint] at hm
  rw [ReferenceEllipsoid.toSet, mem_ellipsoid]
  simp only [surfacePoint, vec3_0, vec3_1, vec3_2]
  have hl := Real.Angle.cos_sq_add_sin_sq c.lon
  have hxy : (E.primeVerticalRadius c.lat.1 * cos c.lat.1 * Real.Angle.cos c.lon) ^ 2 +
      (E.primeVerticalRadius c.lat.1 * cos c.lat.1 * Real.Angle.sin c.lon) ^ 2 =
      (E.primeVerticalRadius c.lat.1 * cos c.lat.1) ^ 2 := by
    rw [show ∀ A : ℝ, (A * Real.Angle.cos c.lon) ^ 2 + (A * Real.Angle.sin c.lon) ^ 2 =
      A ^ 2 * (Real.Angle.cos c.lon ^ 2 + Real.Angle.sin c.lon ^ 2) from fun A => by ring,
      hl, mul_one]
  rw [hxy]
  exact hm

/-- The gradient of `(x² + y²) / a² + z² / b²` at the surface point, up to a
factor of two, is a positive multiple of `normal`: `normal` is the surface
normal. -/
theorem gradient_eq :
    vec3 ((surfacePoint E c) 0 / E.a ^ 2) ((surfacePoint E c) 1 / E.a ^ 2)
        ((surfacePoint E c) 2 / E.b ^ 2) =
      (E.primeVerticalRadius c.lat.1 / E.a ^ 2) • c.normal := by
  have he := E.one_sub_e2_pos.ne'
  have ha := E.a_pos.ne'
  simp only [surfacePoint, normal, vec3_0, vec3_1, vec3_2, vec3_smul, E.b_sq]
  refine vec3_congr ?_ ?_ ?_
  · ring
  · ring
  · field_simp

/-- The position at height `h` is `h` along the normal from the surface
point. -/
theorem toECEF_eq : toECEF E c = surfacePoint E c + c.height • c.normal := by
  simp only [toECEF, surfacePoint, normal, vec3_smul, vec3_add]
  refine vec3_congr ?_ ?_ ?_ <;> ring

/-- On a sphere of radius `R`, the position is `R + h` along the normal. -/
theorem toECEF_of_sphere (hf : E.f = 0) : toECEF E c = (E.a + c.height) • c.normal := by
  have he : E.e2 = 0 := (E.isSphere_tfae.out 1 3).mp hf
  have hN : E.primeVerticalRadius c.lat.1 = E.a := by
    simp [ReferenceEllipsoid.primeVerticalRadius, he]
  simp only [toECEF, normal, vec3_smul, hN, he, sub_zero, mul_one]
  refine vec3_congr ?_ ?_ ?_ <;> ring

/-- So on a sphere the distance from the centre is `R + h`. -/
theorem norm_toECEF_of_sphere (hf : E.f = 0) (hh : -E.a ≤ c.height) :
    ‖toECEF E c‖ = E.a + c.height := by
  rw [toECEF_of_sphere E c hf, norm_smul, c.norm_normal, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

end GeodeticCoordinate

end Geodesy
