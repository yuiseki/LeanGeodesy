import LeanGeodesy.Projection.Azimuthal
import LeanGeodesy.Projection.EqualArea
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Buffers through the azimuthal equidistant projection

A buffer of radius `r` around a point is the set of places within distance
`r` of it. GIS libraries often build it by projecting with the azimuthal
equidistant projection centred on the point and drawing a planar circle
there. This file shows why that is exact on the sphere, using the existing
azimuthal equidistant projection centred on the north pole
(`azimuthalEquidistant`).

- A place at great-circle distance `r` from the centre is drawn at
  Euclidean distance `r` from the centre (`norm_azimuthalEquidistant_eq_iff`).
- The geodesic circle of radius `r`, the places at distance exactly `r`, is
  drawn as the Euclidean circle of radius `r` (`image_geodesicCircle`), and
  the geodesic disk, the places within `r`, as the Euclidean disk of radius
  `r` (`image_geodesicDisk`), for `0 ≤ r < π R`.

The projection keeps distances and azimuths from the centre, but not areas,
and this holds for whole buffers, not just locally. The geodesic disk of
angular radius `θ` is the cap north of latitude `π/2 - θ`
(`mem_geodesicDisk_iff`), whose area, the integral of the area element
`R · R cos φ` (`sphereCellArea`), is `2π R² (1 - cos θ)` (`capArea_eq`). Its
image, the Euclidean disk of radius `R θ`, has Lebesgue measure `π (R θ)²`
(`volume_image_geodesicDisk`). Since `1 - cos θ < θ² / 2`, the buffer is
drawn strictly larger than the cap for every `0 < θ < π`
(`azimuthalEquidistant_enlarges_buffer`).

Places are given by latitude and unwrapped longitude, `(φ, λ)` with
`φ ∈ [-π/2, π/2]`.
-/

namespace Geodesy.Projection

open Real Geodesic

variable {R : ℝ}

/-- The places at great-circle distance exactly `r` from the north pole. -/
def geodesicCircle (R r : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (-(π / 2)) (π / 2) ∧ greatCircleDistance R (π / 2) p.2 p.1 p.2 = r}

/-- The places within great-circle distance `r` of the north pole. -/
def geodesicDisk (R r : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (-(π / 2)) (π / 2) ∧ greatCircleDistance R (π / 2) p.2 p.1 p.2 ≤ r}

/-- The azimuthal equidistant projection of a place `(φ, λ)`. -/
noncomputable def aeqd (R : ℝ) (p : ℝ × ℝ) : E2 := azimuthalEquidistant R p.1 p.2

/-- A place is drawn at Euclidean distance `r` from the centre exactly when it
is at great-circle distance `r`. -/
theorem norm_azimuthalEquidistant_eq_iff (hR : 0 ≤ R) {φ : ℝ} (hφ : φ ∈ Set.Icc (-(π / 2)) (π / 2))
    (lam r : ℝ) :
    ‖azimuthalEquidistant R φ lam‖ = r ↔ greatCircleDistance R (π / 2) lam φ lam = r := by
  rw [azimuthalEquidistant_preserves_distanceFromCentre hR hφ]

theorem vec2_eta' (q : E2) : vec2 (q 0) (q 1) = q := by
  ext i
  fin_cases i <;> rfl

/-- Every point of the plane within `π R` of the centre is drawn from the place
at latitude `π/2 - ‖q‖ / R` and longitude the argument of `q`. -/
theorem aeqd_preimage (hR : 0 < R) {q : E2} (hq : ‖q‖ < π * R) :
    aeqd R (π / 2 - ‖q‖ / R, Complex.arg ⟨q 0, q 1⟩) = q ∧
      π / 2 - ‖q‖ / R ∈ Set.Icc (-(π / 2)) (π / 2) := by
  have hn := norm_nonneg q
  have habs : ‖(⟨q 0, q 1⟩ : ℂ)‖ = ‖q‖ := by
    rw [Complex.norm_def, Complex.normSq_mk, ← sqrt_sq hn, ← vec2_eta' q, norm_vec2_sq]
    simp only [vec2_0, vec2_1]
    congr 1
    ring
  constructor
  · rw [aeqd, azimuthalEquidistant]
    simp only [sub_sub_cancel, mul_div_cancel₀ _ hR.ne']
    conv_rhs => rw [← vec2_eta' q]
    rw [← habs, Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]
  · have h1 : ‖q‖ / R < π := by rw [div_lt_iff₀ hR]; linarith
    have h0 : 0 ≤ ‖q‖ / R := div_nonneg hn hR.le
    constructor <;> linarith

/-- The geodesic circle of radius `r` is drawn as the Euclidean circle of radius `r`. -/
theorem image_geodesicCircle (hR : 0 < R) {r : ℝ} (hr : r < π * R) :
    aeqd R '' geodesicCircle R r = Metric.sphere 0 r := by
  ext q
  constructor
  · rintro ⟨p, ⟨hφ, hd⟩, rfl⟩
    rw [mem_sphere_zero_iff_norm, aeqd, norm_azimuthalEquidistant_eq_iff hR.le hφ]
    exact hd
  · intro hq
    rw [mem_sphere_zero_iff_norm] at hq
    set p : ℝ × ℝ := (π / 2 - ‖q‖ / R, Complex.arg ⟨q 0, q 1⟩) with hpdef
    obtain ⟨he, hφ⟩ := aeqd_preimage hR (hq ▸ hr)
    have he' : azimuthalEquidistant R p.1 p.2 = q := he
    refine ⟨p, ⟨hφ, ?_⟩, he⟩
    rw [← norm_azimuthalEquidistant_eq_iff hR.le hφ, he', hq]

/-- The geodesic disk of radius `r` is drawn as the Euclidean disk of radius `r`. -/
theorem image_geodesicDisk (hR : 0 < R) {r : ℝ} (hr : r < π * R) :
    aeqd R '' geodesicDisk R r = Metric.closedBall 0 r := by
  ext q
  constructor
  · rintro ⟨p, ⟨hφ, hd⟩, rfl⟩
    rw [mem_closedBall_zero_iff, aeqd, azimuthalEquidistant_preserves_distanceFromCentre hR.le hφ]
    exact hd
  · intro hq
    rw [mem_closedBall_zero_iff] at hq
    set p : ℝ × ℝ := (π / 2 - ‖q‖ / R, Complex.arg ⟨q 0, q 1⟩) with hpdef
    obtain ⟨he, hφ⟩ := aeqd_preimage hR (lt_of_le_of_lt hq hr)
    have he' : azimuthalEquidistant R p.1 p.2 = q := he
    refine ⟨p, ⟨hφ, ?_⟩, he⟩
    rw [← azimuthalEquidistant_preserves_distanceFromCentre hR.le hφ, he']
    exact hq

/-! ## Areas of buffers -/

/-- The geodesic disk of radius `r` is the cap north of latitude `π/2 - r / R`. -/
theorem mem_geodesicDisk_iff (hR : 0 < R) (r : ℝ) (p : ℝ × ℝ) :
    p ∈ geodesicDisk R r ↔ p.1 ∈ Set.Icc (-(π / 2)) (π / 2) ∧ π / 2 - r / R ≤ p.1 := by
  unfold geodesicDisk
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hφ, hd⟩
    rw [greatCircleDistance, centralAngle, direction_pi_div_two, angle_northPole hφ] at hd
    refine ⟨hφ, ?_⟩
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hR]
    linarith
  · rintro ⟨hφ, hr⟩
    refine ⟨hφ, ?_⟩
    rw [greatCircleDistance, centralAngle, direction_pi_div_two, angle_northPole hφ]
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hR] at hr
    linarith

/-- The area of the spherical cap of angular radius `θ` around the north pole:
the cell between latitudes `π/2 - θ` and `π/2` and a full turn of longitude. -/
noncomputable def capArea (R θ : ℝ) : ℝ := sphereCellArea R (π / 2 - θ) (π / 2) 0 (2 * π)

theorem capArea_eq (R θ : ℝ) : capArea R θ = 2 * π * R ^ 2 * (1 - cos θ) := by
  rw [capArea, sphereCellArea_eq, sin_pi_div_two, sin_pi_div_two_sub]
  ring

/-- The Lebesgue measure of a Euclidean disk of radius `r` is `π r²`. -/
theorem volume_closedBall_E2 {r : ℝ} (hr : 0 ≤ r) :
    MeasureTheory.volume (Metric.closedBall (0 : E2) r) = ENNReal.ofReal (π * r ^ 2) := by
  have hΓ : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one]
    norm_num
  rw [EuclideanSpace.volume_closedBall, Fintype.card_fin]
  norm_num [hΓ, sq_sqrt pi_pos.le]
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- The buffer of radius `r` is drawn with area `π r²`. -/
theorem volume_image_geodesicDisk (hR : 0 < R) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < π * R) :
    MeasureTheory.volume (aeqd R '' geodesicDisk R r) = ENNReal.ofReal (π * r ^ 2) := by
  rw [image_geodesicDisk hR hr, volume_closedBall_E2 hr0]

/-- The azimuthal equidistant projection draws every buffer of radius
`0 < r < π R` strictly larger than the spherical cap it represents. -/
theorem azimuthalEquidistant_enlarges_buffer (hR : 0 < R) {r : ℝ} (hr0 : 0 < r) (hr : r < π * R) :
    capArea R (r / R) < (MeasureTheory.volume (aeqd R '' geodesicDisk R r)).toReal := by
  rw [volume_image_geodesicDisk hR hr0.le hr, ENNReal.toReal_ofReal (by positivity), capArea_eq]
  have hθ : r / R ≠ 0 := (div_pos hr0 hR).ne'
  have hcos := one_sub_sq_div_two_lt_cos hθ
  have hpi := pi_pos
  have hr2 : r ^ 2 = R ^ 2 * (r / R) ^ 2 := by field_simp
  rw [hr2]
  nlinarith [mul_pos (mul_pos hpi (pow_pos hR 2)) (by linarith : (0 : ℝ) < cos (r / R) - (1 - (r / R) ^ 2 / 2))]

end Geodesy.Projection
