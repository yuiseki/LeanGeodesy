import LeanGeodesy.GeodeticCoordinate
import LeanGeodesy.Projection.Mercator
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Data.Real.Pi.Bounds

/-!
# Great-circle distance

On a spherical Earth the shortest way between two places runs along a great
circle, and its length is the radius times the angle between the two
places seen from the centre, the central angle. This file defines that
angle through the unit vectors of the two places (`direction`, the
ellipsoid normal of `GeodeticCoordinate`) and proves

- the spherical law of cosines (`cos_centralAngle`) and the haversine
  formula that GIS software evaluates (`haversine`);
- that the great-circle distance is a metric on the sphere: symmetric, zero
  only between a place and itself, at most half the circumference, and
  satisfying the triangle inequality (`greatCircleDistance_comm`,
  `greatCircleDistance_eq_zero_iff`, `greatCircleDistance_le`,
  `greatCircleDistance_triangle`);
- the familiar special cases: along a meridian it is the difference in
  latitude and distances add up (`centralAngle_same_meridian`,
  `centralAngle_meridian_add`), along the equator it is the difference in
  longitude the shorter way round (`centralAngle_equator`), and the poles
  are antipodal (`centralAngle_poles`);
- one minute of latitude on a 6371 km sphere is about 1853 m, the origin of
  the nautical mile (`arcMinute_bounds`).

The triangle inequality comes from the triangle inequality for angles
between unit vectors (`angle_le_angle_add_angle`), which Mathlib states
only as `proof_wanted` and is proved here. The proof splits two vectors
into their parts along and across a third. The parts across have lengths
`sin α` and `sin β`, so by Cauchy-Schwarz the inner product is at least
`cos α cos β - sin α sin β = cos (α + β)`, and `arccos` is decreasing.

Geodesics on the ellipsoid, which are not plane curves, are not covered.
-/

namespace Geodesy

namespace Geodesic

open Real InnerProductGeometry

section AngleTriangle

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `arccos` is decreasing. -/
theorem arccos_le_arccos_of_le {x y : ℝ} (h : x ≤ y) : arccos y ≤ arccos x := by
  rw [arccos, arccos]
  linarith [monotone_arcsin h]

/-- For unit vectors the angle is the arccosine of the inner product. -/
theorem angle_eq_arccos_inner {u w : V} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    angle u w = arccos (inner u w) := by
  rw [angle, hu, hw, mul_one, div_one]

/-- The part of `u` perpendicular to the unit vector `v` has length
`sin (angle u v)`. -/
theorem norm_sub_inner_smul {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - (inner u v : ℝ) • v‖ = sin (angle u v) := by
  have hc : cos (angle u v) = inner u v := by
    rw [cos_angle, hu, hv, mul_one, div_one]
  have hvv : (inner v v : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have huu : (inner u u : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hsq : ‖u - (inner u v : ℝ) • v‖ ^ 2 = sin (angle u v) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm u v, hvv, huu, sin_sq, hc]
    ring
  have hs : 0 ≤ sin (angle u v) := sin_nonneg_of_nonneg_of_le_pi (angle_nonneg u v) (angle_le_pi u v)
  nlinarith [norm_nonneg (u - (inner u v : ℝ) • v)]

/-- The triangle inequality for angles between unit vectors. -/
theorem angle_le_angle_add_angle {u v w : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    angle u w ≤ angle u v + angle v w := by
  set α := angle u v with hα
  set β := angle v w with hβ
  by_cases hab : α + β ≤ π
  swap
  · exact (angle_le_pi u w).trans (le_of_lt (not_le.mp hab))
  -- `⟪u, w⟫ = cos α cos β + ⟪a, b⟫` with `a`, `b` the perpendicular parts.
  have hcα : cos α = inner u v := by rw [hα, cos_angle, hu, hv, mul_one, div_one]
  have hcβ : cos β = inner v w := by rw [hβ, cos_angle, hv, hw, mul_one, div_one]
  have hvv : (inner v v : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hsplit : (inner u w : ℝ) =
      inner u v * inner v w + inner (u - (inner u v : ℝ) • v) (w - (inner w v : ℝ) • v) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_left, real_inner_smul_right, hvv,
      real_inner_comm w v]
    ring
  have hna := norm_sub_inner_smul hu hv
  have hnb : ‖w - (inner w v : ℝ) • v‖ = sin β := by
    rw [norm_sub_inner_smul hw hv, hβ, angle_comm]
  have hcs := neg_le_of_abs_le
    (abs_real_inner_le_norm (u - (inner u v : ℝ) • v) (w - (inner w v : ℝ) • v))
  rw [hna, ← hα, hnb] at hcs
  have hkey : cos (α + β) ≤ inner u w := by
    rw [cos_add, hsplit, hcα, hcβ]
    linarith
  calc angle u w = arccos (inner u w) := angle_eq_arccos_inner hu hw
    _ ≤ arccos (cos (α + β)) := arccos_le_arccos_of_le hkey
    _ = α + β := arccos_cos (add_nonneg (angle_nonneg u v) (angle_nonneg v w)) hab


end AngleTriangle

/-! ## Directions on the sphere -/

/-- The unit vector at latitude `φ` and longitude `lam`. -/
noncomputable def direction (φ lam : ℝ) : E3 := vec3 (cos φ * cos lam) (cos φ * sin lam) (sin φ)

/-- It is the ellipsoid normal of a geodetic coordinate at that latitude and
longitude. -/
theorem normal_eq_direction (c : GeodeticCoordinate) :
    c.normal = direction c.lat.1 c.lon.toReal := by
  simp only [GeodeticCoordinate.normal, direction, Real.Angle.cos_toReal, Real.Angle.sin_toReal]

/-- The point of the sphere of radius `R` is `R` times the direction. -/
theorem spherePoint_eq_smul (R φ lam : ℝ) :
    Projection.spherePoint R φ lam = R • direction φ lam := by
  rw [Projection.spherePoint, direction, vec3_smul]
  refine vec3_congr ?_ ?_ ?_ <;> ring

theorem inner_direction (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    inner (direction φ₁ lam₁) (direction φ₂ lam₂) =
      sin φ₁ * sin φ₂ + cos φ₁ * cos φ₂ * cos (lam₁ - lam₂) := by
  rw [direction, direction, inner_vec3, cos_sub]
  ring

theorem norm_direction (φ lam : ℝ) : ‖direction φ lam‖ = 1 := by
  have h : ‖direction φ lam‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_direction, sub_self, cos_zero, mul_one]
    nlinarith [sin_sq_add_cos_sq φ]
  nlinarith [norm_nonneg (direction φ lam)]

theorem direction_ne_zero (φ lam : ℝ) : direction φ lam ≠ 0 := by
  intro h
  have := norm_direction φ lam
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-! ## The central angle -/

/-- The angle at the centre of the sphere between two positions. -/
noncomputable def centralAngle (φ₁ lam₁ φ₂ lam₂ : ℝ) : ℝ :=
  angle (direction φ₁ lam₁) (direction φ₂ lam₂)

/-- The spherical law of cosines. -/
theorem cos_centralAngle (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    cos (centralAngle φ₁ lam₁ φ₂ lam₂) =
      sin φ₁ * sin φ₂ + cos φ₁ * cos φ₂ * cos (lam₁ - lam₂) := by
  rw [centralAngle, cos_angle, norm_direction, norm_direction, mul_one, div_one, inner_direction]

theorem sin_half_sq (x : ℝ) : sin (x / 2) ^ 2 = (1 - cos x) / 2 := by
  have h := cos_sq_add_sin_sq (x / 2)
  have h2 : cos x = 2 * cos (x / 2) ^ 2 - 1 := by
    rw [← cos_two_mul]
    ring_nf
  linarith

/-- The haversine formula, the form of the law of cosines that GIS software
evaluates because it stays accurate for nearby points. -/
theorem haversine (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    sin (centralAngle φ₁ lam₁ φ₂ lam₂ / 2) ^ 2 =
      sin ((φ₂ - φ₁) / 2) ^ 2 + cos φ₁ * cos φ₂ * sin ((lam₂ - lam₁) / 2) ^ 2 := by
  rw [sin_half_sq, sin_half_sq, sin_half_sq, cos_centralAngle, cos_sub φ₂ φ₁,
    show lam₂ - lam₁ = -(lam₁ - lam₂) by ring, cos_neg]
  ring

theorem centralAngle_nonneg (φ₁ lam₁ φ₂ lam₂ : ℝ) : 0 ≤ centralAngle φ₁ lam₁ φ₂ lam₂ :=
  angle_nonneg _ _

theorem centralAngle_le_pi (φ₁ lam₁ φ₂ lam₂ : ℝ) : centralAngle φ₁ lam₁ φ₂ lam₂ ≤ π :=
  angle_le_pi _ _

theorem centralAngle_comm (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    centralAngle φ₁ lam₁ φ₂ lam₂ = centralAngle φ₂ lam₂ φ₁ lam₁ :=
  angle_comm _ _

theorem centralAngle_self (φ lam : ℝ) : centralAngle φ lam φ lam = 0 :=
  angle_self (direction_ne_zero φ lam)

/-- The central angle is zero only between a position and itself. -/
theorem centralAngle_eq_zero_iff (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    centralAngle φ₁ lam₁ φ₂ lam₂ = 0 ↔ direction φ₁ lam₁ = direction φ₂ lam₂ := by
  constructor
  · intro h
    have hc := cos_centralAngle φ₁ lam₁ φ₂ lam₂
    rw [h, cos_zero, ← inner_direction] at hc
    -- Unit vectors with inner product one are equal.
    have hsq : ‖direction φ₁ lam₁ - direction φ₂ lam₂‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_direction, norm_direction,
        one_pow]
      linarith [real_inner_comm (direction φ₁ lam₁) (direction φ₂ lam₂)]
    exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))
  · intro h
    rw [centralAngle, h]
    exact angle_self (direction_ne_zero _ _)

/-- The triangle inequality: going through a third position is never shorter. -/
theorem centralAngle_triangle (φ₁ lam₁ φ₂ lam₂ φ₃ lam₃ : ℝ) :
    centralAngle φ₁ lam₁ φ₃ lam₃ ≤ centralAngle φ₁ lam₁ φ₂ lam₂ + centralAngle φ₂ lam₂ φ₃ lam₃ :=
  angle_le_angle_add_angle (norm_direction _ _) (norm_direction _ _) (norm_direction _ _)

/-- Along a meridian the central angle is the difference in latitude. -/
theorem centralAngle_same_meridian {φ₁ φ₂ : ℝ} (h₁ : φ₁ ∈ Set.Icc (-(π / 2)) (π / 2))
    (h₂ : φ₂ ∈ Set.Icc (-(π / 2)) (π / 2)) (lam : ℝ) :
    centralAngle φ₁ lam φ₂ lam = |φ₁ - φ₂| := by
  rw [centralAngle, angle_eq_arccos_inner (norm_direction _ _) (norm_direction _ _),
    inner_direction, sub_self, cos_zero, mul_one,
    show sin φ₁ * sin φ₂ + cos φ₁ * cos φ₂ = cos (φ₁ - φ₂) by rw [cos_sub]; ring, ← cos_abs]
  exact arccos_cos (abs_nonneg _)
    (abs_le.mpr ⟨by linarith [h₁.1, h₂.2, pi_pos], by linarith [h₁.2, h₂.1, pi_pos]⟩)

/-- Along a meridian, distances add: going north from `φ₁` through `φ₂` to
`φ₃` covers exactly the angle from `φ₁` to `φ₃`. The meridian is a great
circle, and the triangle inequality is an equality along it. -/
theorem centralAngle_meridian_add {φ₁ φ₂ φ₃ : ℝ} (h₁ : φ₁ ∈ Set.Icc (-(π / 2)) (π / 2))
    (h₂ : φ₂ ∈ Set.Icc (-(π / 2)) (π / 2)) (h₃ : φ₃ ∈ Set.Icc (-(π / 2)) (π / 2))
    (h₁₂ : φ₁ ≤ φ₂) (h₂₃ : φ₂ ≤ φ₃) (lam : ℝ) :
    centralAngle φ₁ lam φ₃ lam = centralAngle φ₁ lam φ₂ lam + centralAngle φ₂ lam φ₃ lam := by
  rw [centralAngle_same_meridian h₁ h₃, centralAngle_same_meridian h₁ h₂,
    centralAngle_same_meridian h₂ h₃, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
    abs_of_nonpos (by linarith)]
  ring

/-- Along the equator the central angle is the difference in longitude, the
shorter way round. -/
theorem centralAngle_equator (lam₁ lam₂ : ℝ) :
    centralAngle 0 lam₁ 0 lam₂ = |((lam₁ - lam₂ : ℝ) : Real.Angle).toReal| := by
  rw [centralAngle, angle_eq_arccos_inner (norm_direction _ _) (norm_direction _ _),
    inner_direction]
  simp only [sin_zero, cos_zero, mul_zero, zero_add, one_mul]
  rw [← Real.Angle.cos_coe, ← Real.Angle.cos_toReal, ← cos_abs]
  exact arccos_cos (abs_nonneg _) (Real.Angle.abs_toReal_le_pi _)

/-- The poles are antipodal: half a turn apart. -/
theorem centralAngle_poles (lam₁ lam₂ : ℝ) : centralAngle (π / 2) lam₁ (-(π / 2)) lam₂ = π := by
  rw [centralAngle, angle_eq_arccos_inner (norm_direction _ _) (norm_direction _ _),
    inner_direction]
  simp [sin_neg]

/-! ## Great-circle distance -/

/-- The distance along a sphere of radius `R`. -/
noncomputable def greatCircleDistance (R φ₁ lam₁ φ₂ lam₂ : ℝ) : ℝ := R * centralAngle φ₁ lam₁ φ₂ lam₂

variable {R : ℝ}

theorem greatCircleDistance_nonneg (hR : 0 ≤ R) (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    0 ≤ greatCircleDistance R φ₁ lam₁ φ₂ lam₂ :=
  mul_nonneg hR (centralAngle_nonneg _ _ _ _)

/-- No two points are further apart than half the circumference. -/
theorem greatCircleDistance_le (hR : 0 ≤ R) (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    greatCircleDistance R φ₁ lam₁ φ₂ lam₂ ≤ π * R := by
  rw [greatCircleDistance, mul_comm π]
  exact mul_le_mul_of_nonneg_left (centralAngle_le_pi _ _ _ _) hR

theorem greatCircleDistance_comm (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    greatCircleDistance R φ₁ lam₁ φ₂ lam₂ = greatCircleDistance R φ₂ lam₂ φ₁ lam₁ := by
  rw [greatCircleDistance, greatCircleDistance, centralAngle_comm]

theorem greatCircleDistance_eq_zero_iff (hR : 0 < R) (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    greatCircleDistance R φ₁ lam₁ φ₂ lam₂ = 0 ↔ direction φ₁ lam₁ = direction φ₂ lam₂ := by
  rw [greatCircleDistance, mul_eq_zero, or_iff_right hR.ne', centralAngle_eq_zero_iff]

theorem greatCircleDistance_triangle (hR : 0 ≤ R) (φ₁ lam₁ φ₂ lam₂ φ₃ lam₃ : ℝ) :
    greatCircleDistance R φ₁ lam₁ φ₃ lam₃ ≤
      greatCircleDistance R φ₁ lam₁ φ₂ lam₂ + greatCircleDistance R φ₂ lam₂ φ₃ lam₃ := by
  simp only [greatCircleDistance, ← mul_add]
  exact mul_le_mul_of_nonneg_left (centralAngle_triangle _ _ _ _ _ _) hR

/-- On a sphere of radius 6371 km, one minute of latitude is between 1853 m
and 1854 m. This is where the nautical mile, defined as 1852 m, comes from. -/
theorem arcMinute_bounds (φ lam : ℝ) (h : φ ∈ Set.Icc (-(π / 2)) (π / 2 - π / 10800)) :
    1853 < greatCircleDistance 6371000 φ lam (φ + π / 10800) lam ∧
      greatCircleDistance 6371000 φ lam (φ + π / 10800) lam < 1854 := by
  have hpi := pi_pos
  rw [greatCircleDistance, centralAngle_same_meridian ⟨h.1, by linarith [h.2]⟩
    ⟨by linarith [h.1], by linarith [h.2]⟩, show φ - (φ + π / 10800) = -(π / 10800) by ring,
    abs_neg, abs_of_pos (by positivity)]
  constructor <;> nlinarith [pi_gt_d6, pi_lt_d6]

end Geodesic

end Geodesy
