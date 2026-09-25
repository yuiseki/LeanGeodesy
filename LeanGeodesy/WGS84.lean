import LeanGeodesy.ReferenceEllipsoid

/-!
# WGS 84 and GRS 80

WGS 84, the datum of GPS, defines its ellipsoid by

- semi-major axis `a = 6378137 m`,
- inverse flattening `1 / f = 298.257223563`

(NGA.STND.0036, "Department of Defense World Geodetic System 1984",
Table 3.1). The polar radius and the eccentricity are derived from these,
and the theorems below bound them with exact rational arithmetic:
`b ≈ 6356752.3142 m`, `e² ≈ 0.00669437999014`.

GRS 80, the ellipsoid of ITRF-based datums such as Japan's JGD2011, has the
same `a` and `1 / f = 298.257222101`. The two ellipsoids differ by about a
tenth of a millimetre in polar radius (`wgs84_b_sub_grs80_b`), which is why
they are interchangeable for mapping.
-/

namespace Geodesy

/-- The WGS 84 ellipsoid. -/
noncomputable def wgs84 : ReferenceEllipsoid :=
  ⟨6378137, 1 / 298.257223563, by norm_num, by norm_num, by norm_num⟩

/-- The GRS 80 ellipsoid. -/
noncomputable def grs80 : ReferenceEllipsoid :=
  ⟨6378137, 1 / 298.257222101, by norm_num, by norm_num, by norm_num⟩

@[simp] theorem wgs84_a : wgs84.a = 6378137 := rfl
@[simp] theorem wgs84_f : wgs84.f = 1 / 298.257223563 := rfl
@[simp] theorem grs80_a : grs80.a = 6378137 := rfl
@[simp] theorem grs80_f : grs80.f = 1 / 298.257222101 := rfl

/-- The WGS 84 polar radius is 6356752.3142 m to the tenth of a millimetre. -/
theorem wgs84_b_bounds : 6356752.3142 < wgs84.b ∧ wgs84.b < 6356752.3143 := by
  simp only [ReferenceEllipsoid.b, wgs84_a, wgs84_f]
  norm_num

/-- The WGS 84 first eccentricity squared is 0.00669437999014 to 14 decimal
places. -/
theorem wgs84_e2_bounds : 0.00669437999014 < wgs84.e2 ∧ wgs84.e2 < 0.00669437999015 := by
  simp only [ReferenceEllipsoid.e2, wgs84_f]
  norm_num

theorem grs80_b_bounds : 6356752.3141 < grs80.b ∧ grs80.b < 6356752.3142 := by
  simp only [ReferenceEllipsoid.b, grs80_a, grs80_f]
  norm_num

/-- The Earth is flattened by about 21.4 km at the poles. -/
theorem wgs84_a_sub_b : 21384 < wgs84.a - wgs84.b ∧ wgs84.a - wgs84.b < 21385 := by
  simp only [ReferenceEllipsoid.b, wgs84_a, wgs84_f]
  norm_num

/-- WGS 84 and GRS 80 differ in polar radius by about 0.105 mm. -/
theorem wgs84_b_sub_grs80_b : 0.0001 < wgs84.b - grs80.b ∧ wgs84.b - grs80.b < 0.0002 := by
  simp only [ReferenceEllipsoid.b, wgs84_a, wgs84_f, grs80_a, grs80_f]
  norm_num

end Geodesy
