import LeanGeodesy.Projection.Azimuthal
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
  have habs : Complex.abs ⟨q 0, q 1⟩ = ‖q‖ := by
    rw [Complex.abs_apply, Complex.normSq_mk, ← sqrt_sq hn, ← vec2_eta' q, norm_vec2_sq]
    simp only [vec2_0, vec2_1]
    congr 1
    ring
  constructor
  · rw [aeqd, azimuthalEquidistant]
    simp only [sub_sub_cancel, mul_div_cancel₀ _ hR.ne']
    conv_rhs => rw [← vec2_eta' q]
    rw [← habs, Complex.abs_mul_cos_arg, Complex.abs_mul_sin_arg]
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

end Geodesy.Projection
