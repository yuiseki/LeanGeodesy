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
- Every point of space has geodetic coordinates (`toECEF_surjective`). Off
  the axis the latitude equation changes sign between the poles, so it has
  a root by the intermediate value theorem, and that root with the height
  formula lands on the point; on the axis the point is straight above or
  below the north pole.
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

theorem continuous_primeVerticalRadius (E : ReferenceEllipsoid) :
    Continuous E.primeVerticalRadius := by
  have h : Continuous fun φ => 1 - E.e2 * sin φ ^ 2 := by fun_prop
  refine continuous_const.div h.sqrt fun φ => ?_
  exact (sqrt_pos.mpr (E.one_sub_e2_sin_sq_pos φ)).ne'

/-- Off the axis, the latitude equation has a root strictly between the
poles. -/
theorem exists_latitudeResidual_eq_zero (E : ReferenceEllipsoid) {p : ℝ} (hp : 0 < p) (z : ℝ) :
    ∃ φ ∈ Set.Ioo (-(π / 2)) (π / 2), E.latitudeResidual p z φ = 0 := by
  have hcont : ContinuousOn (E.latitudeResidual p z) (Set.Icc (-(π / 2)) (π / 2)) := by
    have := continuous_primeVerticalRadius E
    unfold ReferenceEllipsoid.latitudeResidual
    fun_prop
  have hlo : E.latitudeResidual p z (-(π / 2)) = -p := by
    simp [ReferenceEllipsoid.latitudeResidual, sin_neg, cos_neg]
  have hhi : E.latitudeResidual p z (π / 2) = p := by
    simp [ReferenceEllipsoid.latitudeResidual]
  have h0 : (0 : ℝ) ∈ Set.Ioo (E.latitudeResidual p z (-(π / 2))) (E.latitudeResidual p z (π / 2)) := by
    rw [hlo, hhi]; exact ⟨by linarith, hp⟩
  obtain ⟨φ, hφ, hF⟩ := intermediate_value_Ioo (by linarith [pi_pos]) hcont h0
  exact ⟨φ, hφ, hF⟩

/-- Every point of space is the ECEF position of some geodetic coordinate. -/
theorem toECEF_surjective (E : ReferenceEllipsoid) :
    Function.Surjective (GeodeticCoordinate.toECEF E) := by
  intro P
  set x := P 0
  set y := P 1
  set z := P 2
  set p := √(x ^ 2 + y ^ 2) with hpdef
  rcases (sqrt_nonneg (x ^ 2 + y ^ 2)).lt_or_eq with hp | hp
  · -- Off the axis.
    obtain ⟨φ, hφ, hF⟩ := exists_latitudeResidual_eq_zero E hp z
    set N := E.primeVerticalRadius φ
    set h := p * cos φ + z * sin φ - N * E.W2 φ with hh
    have hpc : (N + h) * cos φ = p := by
      simp only [ReferenceEllipsoid.latitudeResidual] at hF
      simp only [hh, ReferenceEllipsoid.W2]
      linear_combination (-sin φ) * hF + p * sin_sq_add_cos_sq φ
    have hzs : (N * (1 - E.e2) + h) * sin φ = z := by
      simp only [ReferenceEllipsoid.latitudeResidual] at hF
      simp only [hh, ReferenceEllipsoid.W2]
      linear_combination cos φ * hF + (N * E.e2 * sin φ + z) * sin_sq_add_cos_sq φ
    have habs : Complex.abs ⟨x, y⟩ = p := by
      rw [Complex.abs_apply, Complex.normSq_mk, hpdef]
      congr 1
      ring
    refine ⟨⟨⟨φ, hφ.1.le, hφ.2.le⟩, ecefLongitude x y, h⟩, ?_⟩
    rw [← vec3_eta P]
    simp only [GeodeticCoordinate.toECEF, ecefLongitude, Real.Angle.cos_coe, Real.Angle.sin_coe]
    refine vec3_congr ?_ ?_ hzs
    · rw [hpc, ← habs, Complex.abs_mul_cos_arg]
    · rw [hpc, ← habs, Complex.abs_mul_sin_arg]
  · -- On the axis: straight above or below the north pole.
    have hxy : x ^ 2 + y ^ 2 = 0 := by
      have h2 := sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))
      rw [← hp] at h2
      linarith
    have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    refine ⟨⟨GeodeticLatitude.northPole, 0, z - E.b⟩, ?_⟩
    rw [← vec3_eta P]
    have hb : E.primeVerticalRadius (π / 2) * (1 - E.e2) = E.b := by
      rw [E.primeVerticalRadius_pi_div_two, E.one_sub_e2_eq]
      field_simp [E.a_pos.ne', E.b_pos.ne']
      ring
    simp only [GeodeticCoordinate.toECEF, GeodeticLatitude.northPole, cos_pi_div_two,
      sin_pi_div_two, mul_zero, zero_mul, mul_one, hb]
    refine vec3_congr hx.symm hy.symm ?_
    ring

end Geodesy
