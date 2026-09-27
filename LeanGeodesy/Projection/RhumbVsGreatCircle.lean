import LeanGeodesy.Projection.Rhumb
import LeanGeodesy.Projection.Azimuthal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Great circle versus rhumb line

Between `A = (45° N, 0°)` and `B = (45° N, 90° E)` on the sphere of radius
`R`, three different "distances" can be measured, and GIS tools report all
three: the great-circle distance, the rhumb-line distance, and a distance
read off the Mercator map. This file computes them from the definitions and
compares them.

Lengths of curves are the integral of their speed (`curveLength`), not a
formula taken as given.

- A and B are on the same parallel, so the rhumb line between them is the
  parallel itself, heading due east (`parallel_hasBearing_east`), of length
  `R cos 45° · π/2 = √2 π R / 4` (`parallel_curveLength`). In general a
  rhumb line of bearing `α` from `φ₀` to `φ₁` has length
  `R (φ₁ - φ₀) / cos α` (`rhumb_curveLength`), the rhumb-distance formula,
  derived rather than assumed.
- The great circle has central angle `π/3` (`centralAngle_A_B`), so the
  great-circle distance is `π R / 3` (`greatCircleDistance_A_B`). It leaves
  A with a northward component, so not due east
  (`greatCircle_initial_not_east`), and its midpoint lies north of the
  45th parallel, so it is not the rhumb line (`greatArc_midpoint_not_on_parallel`).
- `π R / 3 < √2 π R / 4` (`greatCircleDistance_lt_rhumb_A_B`): the rhumb line is
  longer, as `Geodesic` guarantees for any path.
- The Mercator map distance between A and B, scaled by `cos 45°` as a web map
  converts map units to metres at a latitude, equals the parallel's length
  (`mercator_distance_scaled_A_B`): for points on one parallel, the scaled
  map distance measures the rhumb line, not the great circle.
-/

namespace Geodesy.Projection

open Real InnerProductGeometry Geodesic

/-- The length of a curve on `[a, b]`: the integral of its speed. -/
noncomputable def curveLength (γ : ℝ → E3) (a b : ℝ) : ℝ := ∫ t in a..b, ‖deriv γ t‖

variable {R : ℝ}

/-- A rhumb line of bearing `α` moves at the constant speed `R / cos α` per unit
of latitude... -/
theorem norm_rhumb_tangent (hR : 0 < R) (lam₀ φ₀ : ℝ) {α : ℝ}
    (hα : α ∈ Set.Ioo (-(π / 2)) (π / 2)) {φ : ℝ} (hc : 0 < cos φ) :
    ‖meridianTangent R φ (rhumbLon lam₀ φ₀ α φ) +
        (tan α / cos φ) • parallelTangent R φ (rhumbLon lam₀ φ₀ α φ)‖ = R / cos α := by
  have hca : 0 < cos α := cos_pos_of_mem_Ioo hα
  set lam := rhumbLon lam₀ φ₀ α φ
  have hsq : ‖meridianTangent R φ lam + (tan α / cos φ) • parallelTangent R φ lam‖ ^ 2 =
      (R / cos α) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (meridianTangent R φ lam) (parallelTangent R φ lam),
      inner_meridianTangent_parallelTangent, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, norm_meridianTangent_sq, norm_parallelTangent_sq,
      tan_eq_sin_div_cos]
    have hp := sin_sq_add_cos_sq α
    field_simp
    linear_combination R ^ 2 * cos α ^ 2 * cos φ ^ 2 * hp
  rw [← sqrt_sq (norm_nonneg _), hsq, sqrt_sq (div_pos hR hca).le]

/-- ...so between latitudes `φ₀ ≤ φ₁` it has length `R (φ₁ - φ₀) / cos α`, the
rhumb-distance formula. -/
theorem rhumb_curveLength (hR : 0 < R) (lam₀ : ℝ) {α : ℝ} (hα : α ∈ Set.Ioo (-(π / 2)) (π / 2))
    {φ₀ φ₁ : ℝ} (h₀ : φ₀ ∈ Set.Ioo (-(π / 2)) (π / 2)) (h₁ : φ₁ ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    curveLength (fun φ => spherePoint R φ (rhumbLon lam₀ φ₀ α φ)) φ₀ φ₁ = R * (φ₁ - φ₀) / cos α := by
  have hd : ∀ φ ∈ Set.uIcc φ₀ φ₁, ‖deriv (fun φ => spherePoint R φ (rhumbLon lam₀ φ₀ α φ)) φ‖ =
      R / cos α := fun φ hφ => by
    have hφ' : φ ∈ Set.Ioo (-(π / 2)) (π / 2) := by
      rcases Set.mem_uIcc.mp hφ with h | h
      · exact ⟨by linarith [h₀.1, h.1], by linarith [h₁.2, h.2]⟩
      · exact ⟨by linarith [h₁.1, h.1], by linarith [h₀.2, h.2]⟩
    have hc := cos_pos_of_mem_Ioo hφ'
    rw [(hasDerivAt_latitudeCurve (hasDerivAt_rhumbLon lam₀ φ₀ α hc)).deriv]
    exact norm_rhumb_tangent hR lam₀ φ₀ hα hc
  rw [curveLength, intervalIntegral.integral_congr hd, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-! ## A and B -/

/-- The parallel through A and B, as a curve in longitude. -/
noncomputable def parallel45 (R : ℝ) (lam : ℝ) : E3 := spherePoint R (π / 4) lam

/-- It heads due east: bearing `π/2`. -/
theorem parallel_hasBearing_east (hR : 0 < R) (lam : ℝ) :
    HasBearing R (π / 4) lam (parallelTangent R (π / 4) lam) (π / 2) := by
  have hc : 0 < cos (π / 4) := by rw [cos_pi_div_four]; positivity
  refine ⟨R * cos (π / 4), mul_pos hR hc, ?_, ?_⟩
  · rw [sin_pi_div_two, mul_one]
    rw [eastComponent, real_inner_self_eq_norm_sq, norm_parallelTangent_sq]
    field_simp
    ring
  · rw [cos_pi_div_two, mul_zero, northComponent, real_inner_comm,
      inner_meridianTangent_parallelTangent, zero_div]

/-- Its length from A to B is `√2 π R / 4`. -/
theorem parallel_curveLength (hR : 0 < R) : curveLength (parallel45 R) 0 (π / 2) = √2 * π * R / 4 := by
  have hc : 0 < cos (π / 4) := by rw [cos_pi_div_four]; positivity
  have hd : ∀ lam ∈ Set.uIcc (0 : ℝ) (π / 2), ‖deriv (parallel45 R) lam‖ = R * cos (π / 4) :=
    fun lam _ => by
      rw [show parallel45 R = fun lam => spherePoint R (π / 4) lam from rfl,
        (hasDerivAt_spherePoint_lon R (π / 4) lam).deriv,
        ← sqrt_sq (norm_nonneg _), norm_parallelTangent_sq, sqrt_sq (mul_pos hR hc).le]
  rw [curveLength, intervalIntegral.integral_congr hd, intervalIntegral.integral_const,
    smul_eq_mul, cos_pi_div_four]
  ring

/-- The central angle between A and B is `π/3`. -/
theorem centralAngle_A_B : centralAngle (π / 4) 0 (π / 4) (π / 2) = π / 3 := by
  rw [centralAngle, angle, norm_direction, norm_direction, mul_one, div_one, inner_direction_45,
    ← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]

/-- The great-circle distance between A and B is `π R / 3`. -/
theorem greatCircleDistance_A_B : greatCircleDistance R (π / 4) 0 (π / 4) (π / 2) = π * R / 3 := by
  rw [greatCircleDistance, centralAngle_A_B]
  ring

/-- The great circle does not leave A due east: its initial direction has a
positive northward component, where the rhumb line's is zero. -/
theorem greatCircle_initial_not_east (hR : 0 < R) :
    ¬ HasBearing R (π / 4) 0 (arcNormal (direction (π / 4) 0) (direction (π / 4) (π / 2))) (π / 2) := by
  rintro ⟨c, _, _, hn⟩
  rw [cos_pi_div_two, mul_zero] at hn
  have hpos := (mercator_not_preserves_azimuth hR).2.2
  have hscale : meridianTangent R (π / 4) 0 = R • meridianTangent 1 (π / 4) 0 := by
    simp only [meridianTangent, vec3_smul]
    refine vec3_congr ?_ ?_ ?_ <;> ring
  rw [northComponent, hscale, real_inner_smul_right,
    mul_div_cancel_left₀ _ hR.ne'] at hn
  linarith

/-- The midpoint of the great-circle arc from A to B lies north of the 45th
parallel, so the great circle is not the rhumb line. -/
theorem greatArc_midpoint_not_on_parallel (lam : ℝ) :
    greatArc (direction (π / 4) 0) (direction (π / 4) (π / 2)) (1 / 2) ≠ direction (π / 4) lam := by
  intro h
  have hθ : angle (direction (π / 4) 0) (direction (π / 4) (π / 2)) = π / 3 := centralAngle_A_B
  rw [greatArc, arcNormal, hθ, real_inner_comm (direction (π / 4) 0) (direction (π / 4) (π / 2)),
    inner_direction_45, show 1 / 2 * (π / 3) = π / 6 by ring, cos_pi_div_six, sin_pi_div_six,
    sin_pi_div_three] at h
  have hz := congrArg (fun v : E3 => v 2) h
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, direction, vec3_2,
    sin_pi_div_four] at hz
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have h2p : 0 < √2 := by positivity
  field_simp at hz
  ring_nf at hz
  rw [h3] at hz
  nlinarith

/-- The great-circle distance is shorter than the rhumb line. -/
theorem greatCircleDistance_lt_rhumb_A_B (hR : 0 < R) :
    greatCircleDistance R (π / 4) 0 (π / 4) (π / 2) < curveLength (parallel45 R) 0 (π / 2) := by
  rw [greatCircleDistance_A_B, parallel_curveLength hR]
  have hpi := pi_pos
  have h2 : (4 : ℝ) / 3 < √2 := by
    rw [show (4 : ℝ) / 3 = √((4 / 3) ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith [mul_pos hpi hR]

/-- The Mercator map distance between A and B, times `cos 45°`, is the length of
the parallel: on one parallel, the scaled map distance is the rhumb distance. -/
theorem mercator_distance_scaled_A_B (hR : 0 < R) :
    dist (mercator R (π / 4) 0) (mercator R (π / 4) (π / 2)) * cos (π / 4) =
      curveLength (parallel45 R) 0 (π / 2) := by
  rw [parallel_curveLength hR, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [mercator, vec2_0, vec2_1, sub_self, Real.dist_eq, sq_abs, zero_pow two_ne_zero,
    add_zero, mul_zero, zero_sub, even_two, Even.neg_pow, cos_pi_div_four]
  rw [sqrt_sq (by positivity)]
  ring

end Geodesy.Projection
