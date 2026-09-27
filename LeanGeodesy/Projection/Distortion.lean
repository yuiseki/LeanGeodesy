import LeanGeodesy.Projection.Mercator

/-!
# Distortion of a map projection

At a point of the Earth, a small step north has length `M dφ` and a small
step east has length `P dλ`, where `M` is the meridian radius and
`P = N cos φ` the radius of the parallel (on a sphere of radius `R`, `M = R`
and `P = R cos φ`), and the two steps are perpendicular. A projection sends
the step north to `dLat` and the step east to `dLon` on the map: these are the
partial derivatives of the projection. Everything about its local
distortion follows from these two vectors (`LocalDistortion`).

- The scale along the meridian is `h = ‖dLat‖ / M` and along the parallel
  `k = ‖dLon‖ / P`; the area scale is `|det (dLat, dLon)| / (M P)`.
- When `dLat` and `dLon` are perpendicular, a small circle on the Earth is drawn
  as an ellipse with semi-axes `h` and `k`, Tissot's indicatrix
  (`tissot`), and the area scale is `h k` (`areaScale_of_orthogonal`).
- A projection is conformal, stretching every direction equally, exactly
  when `dLat ⊥ dLon` and `h = k` (`isConformal_iff`). Its area scale is then
  `h²` (`areaScale_of_isConformal`).
-/

namespace Geodesy.Projection

open Real

/-- The partial derivatives of a projection at one point, with the lengths of
the steps they come from. -/
structure LocalDistortion where
  /-- Length of the ground step north per unit latitude: `M`. -/
  meridianLength : ℝ
  /-- Length of the ground step east per unit longitude: `N cos φ`. -/
  parallelLength : ℝ
  /-- The step north has positive length. -/
  meridianLength_pos : 0 < meridianLength
  /-- The step east has positive length: the point is not a pole. -/
  parallelLength_pos : 0 < parallelLength
  /-- The image of the step north. -/
  dLat : E2
  /-- The image of the step east. -/
  dLon : E2

namespace LocalDistortion

variable (D : LocalDistortion)

/-- The scale along the meridian. -/
noncomputable def h : ℝ := ‖D.dLat‖ / D.meridianLength

/-- The scale along the parallel. -/
noncomputable def k : ℝ := ‖D.dLon‖ / D.parallelLength

/-- The signed area of the parallelogram spanned by two plane vectors. -/
def det2 (u v : E2) : ℝ := u 0 * v 1 - u 1 * v 0

/-- The area scale: map area over ground area. -/
noncomputable def areaScale : ℝ := |det2 D.dLat D.dLon| / (D.meridianLength * D.parallelLength)

/-- The squared length on the map of the image of the ground step made of `α`
steps north and `β` steps east. -/
theorem norm_image_sq (α β : ℝ) :
    ‖α • D.dLat + β • D.dLon‖ ^ 2 =
      α ^ 2 * ‖D.dLat‖ ^ 2 + 2 * α * β * inner ℝ D.dLat D.dLon + β ^ 2 * ‖D.dLon‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm D.dLon D.dLat]
  ring

/-- Tissot's indicatrix: when the images of north and east are perpendicular,
the ground step `(α M, β P)` becomes a map step of squared length
`(h α M)² + (k β P)²`, so the unit circle becomes an ellipse with semi-axes
`h` and `k`. -/
theorem tissot (horth : (inner ℝ D.dLat D.dLon : ℝ) = 0) (α β : ℝ) :
    ‖α • D.dLat + β • D.dLon‖ ^ 2 =
      (D.h * (α * D.meridianLength)) ^ 2 + (D.k * (β * D.parallelLength)) ^ 2 := by
  have hM := D.meridianLength_pos.ne'
  have hP := D.parallelLength_pos.ne'
  rw [norm_image_sq, horth, h, k]
  field_simp
  ring

theorem abs_det2_le (u v : E2) : |det2 u v| ≤ ‖u‖ * ‖v‖ := by
  have hu := EuclideanSpace.norm_eq u
  have hv := EuclideanSpace.norm_eq v
  rw [Fin.sum_univ_two] at hu hv
  simp only [Real.norm_eq_abs, sq_abs] at hu hv
  rw [hu, hv, ← sqrt_mul (by positivity), abs_le]
  have key : (u 0 * v 1 - u 1 * v 0) ^ 2 ≤ (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by
    nlinarith [sq_nonneg (u 0 * v 0 + u 1 * v 1)]
  have hs := sqrt_le_sqrt key
  rw [sqrt_sq_eq_abs] at hs
  constructor <;> unfold det2 <;> linarith [abs_le.mp hs]

/-- For perpendicular images, the parallelogram is a rectangle. -/
theorem abs_det2_of_orthogonal {u v : E2} (horth : (inner ℝ u v : ℝ) = 0) :
    |det2 u v| = ‖u‖ * ‖v‖ := by
  have hu := EuclideanSpace.norm_eq u
  have hv := EuclideanSpace.norm_eq v
  rw [Fin.sum_univ_two] at hu hv
  simp only [Real.norm_eq_abs, sq_abs] at hu hv
  have hi : u 0 * v 0 + u 1 * v 1 = 0 := by
    have := horth
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial] at this
    linarith
  rw [hu, hv, ← sqrt_mul (by positivity), ← sqrt_sq_eq_abs]
  congr 1
  unfold det2
  nlinarith [hi]

/-- For perpendicular images the area scale is `h k`. -/
theorem areaScale_of_orthogonal (horth : (inner ℝ D.dLat D.dLon : ℝ) = 0) :
    D.areaScale = D.h * D.k := by
  rw [areaScale, abs_det2_of_orthogonal horth, h, k]
  field_simp

/-- A conformal projection stretches every direction by the same factor. -/
def IsConformal : Prop := (inner ℝ D.dLat D.dLon : ℝ) = 0 ∧ D.h = D.k

/-- An equal-area projection keeps areas. -/
def IsEqualArea : Prop := D.areaScale = 1

/-- Conformal means that every ground step is stretched by the same factor. -/
theorem isConformal_iff :
    D.IsConformal ↔ ∀ α β : ℝ, ‖α • D.dLat + β • D.dLon‖ ^ 2 =
      D.h ^ 2 * ((α * D.meridianLength) ^ 2 + (β * D.parallelLength) ^ 2) := by
  have hM := D.meridianLength_pos
  have hP := D.parallelLength_pos
  constructor
  · rintro ⟨horth, hk⟩ α β
    rw [D.tissot horth, ← hk]
    ring
  · intro hall
    have h10 := hall 1 0
    have h01 := hall 0 1
    have h11 := hall 1 1
    rw [norm_image_sq] at h11
    simp only [one_smul, zero_smul, add_zero, zero_add, one_mul, zero_mul, one_pow, mul_one]
      at h10 h01 h11
    have hdLat : ‖D.dLat‖ ^ 2 = D.h ^ 2 * D.meridianLength ^ 2 := by
      simpa [zero_pow two_ne_zero] using h10
    have hdLon : ‖D.dLon‖ ^ 2 = D.h ^ 2 * D.parallelLength ^ 2 := by
      simpa [zero_pow two_ne_zero] using h01
    have horth : (inner ℝ D.dLat D.dLon : ℝ) = 0 := by nlinarith
    refine ⟨horth, ?_⟩
    have hk2 : D.k ^ 2 = D.h ^ 2 := by
      rw [k, div_pow, hdLon]
      field_simp
    have hh0 : 0 ≤ D.h := div_nonneg (norm_nonneg _) hM.le
    have hk0 : 0 ≤ D.k := div_nonneg (norm_nonneg _) hP.le
    nlinarith [sq_nonneg (D.h - D.k), sq_nonneg (D.h + D.k)]

/-- A conformal projection scales areas by the square of its scale. -/
theorem areaScale_of_isConformal (hc : D.IsConformal) : D.areaScale = D.h ^ 2 := by
  rw [D.areaScale_of_orthogonal hc.1, ← hc.2]
  ring

end LocalDistortion

end Geodesy.Projection
