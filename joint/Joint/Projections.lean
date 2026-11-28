import Joint.Basic

/-!
# Map projections across the three libraries

Which projection, centred where, onto which plane, at which scale:

| map | library | domain | centre / projection point | target plane, scale |
| --- | --- | --- | --- | --- |
| `Geodesy.Projection.stereographic R φ lam` | LeanGeodesy | latitude/longitude, `φ ≠ -π/2` | projects from the south pole | plane tangent at the north pole, radius `R` |
| `Geospatial.Spaces.stereoProj` | LeanGeospatial | `S² \ {N}` | projects from the north pole | equatorial plane `z = 0`, unit sphere |
| `ComputationalGeometry.stereoS2` | LeanComputationalGeometry | `S² \ {v}` | Mathlib's `stereographic'` | the orthogonal complement of `v`, in an orthonormal basis |
| `ComputationalGeometry.gnomonic` | LeanComputationalGeometry | `z ≠ 0` (meaningful on `z > 0`) | projects from the centre | plane `z = 1`, read as `(x / z, y / z)` |
| `ComputationalGeometry.radial`, `Geospatial.Spaces.radialProj` | both | `ℝ³ \ {0}` | from the centre | onto the unit sphere |
| `Geodesy.Projection.mercator`, `webMercator` | LeanGeodesy | latitude/longitude | cylindrical | the plane, radius `R` / WGS 84 `a` |

Proved here:

* **the two stereographic projections agree after a reflection and a scaling**: LeanGeodesy's
  north-polar projection of the unit sphere is twice LeanGeospatial's projection of the point
  reflected in the equator (`stereographic_eq_two_smul_stereoProj`): the projection points are
  opposite poles and the target planes are the tangent plane at the north pole (distance 2 from
  the south pole) and the equatorial plane (distance 1 from the north pole);
* **the gnomonic projection in geodetic coordinates** is the polar gnomonic map
  `(cot φ cos lam, cot φ sin lam)`, independent of the radius (`gnomonic_spherePoint`);
* **radial projection takes the sphere of radius `R` to the unit sphere** point by point in
  latitude and longitude (`radial_spherePoint`).

Not proved here: the identification of Mathlib's `stereographic'` with either explicit formula
(it uses an abstract orthonormal basis of the complement).
-/

namespace Joint

open Real Geodesy Geodesy.Projection

/-- **The two stereographic projections.** LeanGeodesy's north-polar stereographic projection of
the unit sphere at `(φ, lam)` is twice LeanGeospatial's projection from the north pole of the
point reflected in the equator. -/
theorem stereographic_eq_two_smul_stereoProj (φ lam : ℝ) (p : Geospatial.Spaces.PuncturedS2)
    (hp : (p.1 : Geodesy.E3) = vec3 (cos φ * cos lam) (cos φ * sin lam) (-sin φ)) :
    Projection.stereographic 1 φ lam = (2 : ℝ) • Geospatial.Spaces.stereoProj p := by
  apply ComputationalGeometry.Point2D.ext <;>
    simp [ComputationalGeometry.Point2D.x, ComputationalGeometry.Point2D.y,
      Projection.stereographic, stereographicFactor, vec2, Geospatial.Spaces.stereoProj, hp, Geospatial.Point2D.mk] <;> ring

/-- **The gnomonic projection in geodetic coordinates**: the polar gnomonic map, the same for
every radius. -/
theorem gnomonic_spherePoint {R : ℝ} (hR : R ≠ 0) (φ lam : ℝ) :
    ComputationalGeometry.gnomonic (spherePoint R φ lam) =
      ComputationalGeometry.Point2D.mk (cos φ * cos lam / sin φ) (cos φ * sin lam / sin φ) := by
  apply ComputationalGeometry.Point2D.ext <;>
    simp only [ComputationalGeometry.gnomonic, ComputationalGeometry.Point2D.x_mk,
      ComputationalGeometry.Point2D.y_mk, ComputationalGeometry.Point3D.x,
      ComputationalGeometry.Point3D.y, ComputationalGeometry.Point3D.z, spherePoint, vec3_0, vec3_1,
      vec3_2] <;>
    rw [mul_assoc R, mul_div_mul_left _ _ hR]

theorem spherePoint_eq_smul (R φ lam : ℝ) : spherePoint R φ lam = R • spherePoint 1 φ lam := by
  simp only [spherePoint, vec3_smul, one_mul, mul_assoc]

theorem norm_spherePoint_one (φ lam : ℝ) : ‖spherePoint 1 φ lam‖ = 1 := by
  have h : ‖spherePoint 1 φ lam‖ ^ 2 = 1 := by
    rw [Geodesy.norm_sq_eq]
    simp only [spherePoint, vec3_0, vec3_1, vec3_2, one_mul]
    nlinarith [sin_sq_add_cos_sq φ, sin_sq_add_cos_sq lam]
  nlinarith [norm_nonneg (spherePoint 1 φ lam)]

/-- **Radial projection** takes the sphere of radius `R > 0` to the unit sphere, keeping latitude
and longitude. -/
theorem radial_spherePoint {R : ℝ} (hR : 0 < R) (φ lam : ℝ) :
    ComputationalGeometry.radial (spherePoint R φ lam) = spherePoint 1 φ lam := by
  rw [ComputationalGeometry.radial, spherePoint_eq_smul R, norm_smul, norm_spherePoint_one,
    Real.norm_eq_abs, abs_of_pos hR, mul_one, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]

end Joint
