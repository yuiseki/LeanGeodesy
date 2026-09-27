import LeanGeodesy.GeodeticCoordinate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Radii of curvature

At geodetic latitude `φ` the ellipsoid curves differently in two directions.

- Across the meridian, along the prime vertical, the radius of curvature is
  `N = a / √(1 - e² sin² φ)` (`primeVerticalRadius`, in `GeodeticLatitude`).
  The parallel through the point is a circle of radius `N cos φ`.
- Along the meridian it is

  ```
  M = a (1 - e²) / (1 - e² sin² φ)^(3/2)     (meridianRadius)
  ```

This file derives `M` rather than stating it. Differentiating the meridian
point `(N cos φ, N (1 - e²) sin φ)` in `φ` gives `(-M sin φ, M cos φ)`
(`hasDerivAt_meridianPoint_fst`, `hasDerivAt_meridianPoint_snd`), a vector
of length `M`. In space, the tangent to the meridian has length `M`, the
tangent to the parallel has length `N cos φ`, and the two are perpendicular
(`norm_meridianTangent_sq`, `norm_parallelTangent_sq`,
`inner_meridianTangent_parallelTangent`).

`N / M = (1 - e² sin² φ) / (1 - e²)` (`N_div_M`), so the two radii agree on
a sphere and at the poles, and `M < N` everywhere else. Map projections use
this ratio to measure how they distort an ellipsoid.
-/

namespace Geodesy

open Real

namespace ReferenceEllipsoid

variable (E : ReferenceEllipsoid)

/-- `W² = 1 - e² sin² φ`, the square of the `W` of the geodetic literature:
`N = a / W` and `M = a (1 - e²) / W³`. -/
noncomputable def W2 (φ : ℝ) : ℝ := 1 - E.e2 * sin φ ^ 2

theorem W2_pos (φ : ℝ) : 0 < W2 E φ := E.one_sub_e2_sin_sq_pos φ

/-- The radius of curvature of the meridian at latitude `φ`. -/
noncomputable def meridianRadius (φ : ℝ) : ℝ := E.a * (1 - E.e2) / (W2 E φ * √(W2 E φ))

theorem meridianRadius_pos (φ : ℝ) : 0 < meridianRadius E φ := by
  have := W2_pos E φ
  have := E.one_sub_e2_pos
  have := E.a_pos
  unfold meridianRadius
  positivity

theorem hasDerivAt_W2 (φ : ℝ) :
    HasDerivAt (W2 E) (-(E.e2 * (2 * sin φ * cos φ))) φ := by
  unfold W2
  convert ((hasDerivAt_sin φ).pow 2).const_mul E.e2 |>.const_sub 1 using 1 <;> try rfl
  ring

/-- The derivative of the prime vertical radius. -/
theorem hasDerivAt_primeVerticalRadius (φ : ℝ) :
    HasDerivAt E.primeVerticalRadius
      (E.a * E.e2 * sin φ * cos φ / (W2 E φ * √(W2 E φ))) φ := by
  have hD := W2_pos E φ
  have hs : 0 < √(W2 E φ) := sqrt_pos.mpr hD
  have h := (hasDerivAt_const φ E.a).div ((hasDerivAt_W2 E φ).sqrt hD.ne') hs.ne'
  have hN : E.primeVerticalRadius = fun φ => E.a / √(W2 E φ) := rfl
  rw [hN]
  convert h using 1 <;> try rfl
  have hsq : √(W2 E φ) ^ 2 = W2 E φ := sq_sqrt hD.le
  generalize √(W2 E φ) = s at hs hsq ⊢
  rw [← hsq]
  field_simp
  ring

/-- The distance from the axis, `N cos φ`, changes at rate `-M sin φ`. -/
theorem hasDerivAt_meridianPoint_fst (φ : ℝ) :
    HasDerivAt (fun φ => E.primeVerticalRadius φ * cos φ)
      (-(meridianRadius E φ * sin φ)) φ := by
  have hD := W2_pos E φ
  have hs : 0 < √(W2 E φ) := sqrt_pos.mpr hD
  convert (hasDerivAt_primeVerticalRadius E φ).mul (hasDerivAt_cos φ) using 1 <;> try rfl
  have hp := sin_sq_add_cos_sq φ
  simp only [meridianRadius, ReferenceEllipsoid.primeVerticalRadius]
  rw [show 1 - E.e2 * sin φ ^ 2 = W2 E φ from rfl]
  have hsq : √(W2 E φ) ^ 2 = 1 - E.e2 * sin φ ^ 2 := sq_sqrt hD.le
  generalize √(W2 E φ) = s at hs hsq ⊢
  rw [show W2 E φ = s ^ 2 by rw [hsq]; rfl]
  field_simp
  linear_combination (E.a * sin φ) * hsq - (E.a * E.e2 * sin φ) * hp

/-- The height above the equator, `N (1 - e²) sin φ`, changes at rate
`M cos φ`. -/
theorem hasDerivAt_meridianPoint_snd (φ : ℝ) :
    HasDerivAt (fun φ => E.primeVerticalRadius φ * (1 - E.e2) * sin φ)
      (meridianRadius E φ * cos φ) φ := by
  have hD := W2_pos E φ
  have hs : 0 < √(W2 E φ) := sqrt_pos.mpr hD
  convert ((hasDerivAt_primeVerticalRadius E φ).mul_const (1 - E.e2)).mul (hasDerivAt_sin φ) using 1 <;> try rfl
  have hp := sin_sq_add_cos_sq φ
  simp only [meridianRadius, ReferenceEllipsoid.primeVerticalRadius]
  rw [show 1 - E.e2 * sin φ ^ 2 = W2 E φ from rfl]
  have hsq : √(W2 E φ) ^ 2 = 1 - E.e2 * sin φ ^ 2 := sq_sqrt hD.le
  generalize √(W2 E φ) = s at hs hsq ⊢
  rw [show W2 E φ = s ^ 2 by rw [hsq]; rfl]
  field_simp
  linear_combination (-(E.a * (1 - E.e2) * cos φ)) * hsq

/-- The derivative of the meridian radius: `M' = 3 e² sin φ cos φ M / (1 - e² sin² φ)`. -/
theorem hasDerivAt_meridianRadius (φ : ℝ) :
    HasDerivAt E.meridianRadius (3 * E.e2 * sin φ * cos φ * meridianRadius E φ / W2 E φ) φ := by
  have hD := W2_pos E φ
  have hs : 0 < √(W2 E φ) := sqrt_pos.mpr hD
  have hW := hasDerivAt_W2 E φ
  have hprod := hW.mul (hW.sqrt hD.ne')
  have h := (hasDerivAt_const φ (E.a * (1 - E.e2))).div hprod (mul_pos hD hs).ne'
  have hM : E.meridianRadius = fun φ => E.a * (1 - E.e2) / (W2 E φ * √(W2 E φ)) := rfl
  rw [hM]
  convert h using 1 <;> try rfl
  have hsq : √(W2 E φ) ^ 2 = W2 E φ := sq_sqrt hD.le
  simp only [Pi.mul_apply]
  generalize √(W2 E φ) = s at hs hsq ⊢
  rw [← hsq]
  field_simp
  ring

/-- The point of the ellipsoid at geodetic latitude `φ` and longitude `lam`. -/
noncomputable def ellipsoidPoint (φ lam : ℝ) : E3 :=
  vec3 (E.primeVerticalRadius φ * cos φ * cos lam) (E.primeVerticalRadius φ * cos φ * sin lam)
    (E.primeVerticalRadius φ * (1 - E.e2) * sin φ)

/-- It is the surface point of a geodetic coordinate. -/
theorem ellipsoidPoint_eq_surfacePoint (c : GeodeticCoordinate) :
    ellipsoidPoint E c.lat.1 c.lon.toReal = GeodeticCoordinate.surfacePoint E c := by
  simp only [ellipsoidPoint, GeodeticCoordinate.surfacePoint, Real.Angle.cos_toReal,
    Real.Angle.sin_toReal]

/-- The tangent to the meridian of the ellipsoid. -/
noncomputable def meridianTangent (φ lam : ℝ) : E3 :=
  vec3 (-(meridianRadius E φ * sin φ) * cos lam) (-(meridianRadius E φ * sin φ) * sin lam)
    (meridianRadius E φ * cos φ)

/-- The tangent to the parallel of the ellipsoid. -/
noncomputable def parallelTangent (φ lam : ℝ) : E3 :=
  vec3 (-(E.primeVerticalRadius φ * cos φ * sin lam)) (E.primeVerticalRadius φ * cos φ * cos lam) 0

theorem hasDerivAt_ellipsoidPoint_lat (φ lam : ℝ) :
    HasDerivAt (fun φ => ellipsoidPoint E φ lam) (meridianTangent E φ lam) φ := by
  unfold ellipsoidPoint meridianTangent
  exact hasDerivAt_vec3 ((hasDerivAt_meridianPoint_fst E φ).mul_const _) ((hasDerivAt_meridianPoint_fst E φ).mul_const _)
    (hasDerivAt_meridianPoint_snd E φ)

theorem hasDerivAt_ellipsoidPoint_lon (φ lam : ℝ) :
    HasDerivAt (fun lam => ellipsoidPoint E φ lam) (parallelTangent E φ lam) lam := by
  unfold ellipsoidPoint parallelTangent
  refine hasDerivAt_vec3 ?_ ?_ (hasDerivAt_const _ _)
  · convert (hasDerivAt_cos lam).const_mul (E.primeVerticalRadius φ * cos φ) using 1 <;> try rfl
    ring
  · exact (hasDerivAt_sin lam).const_mul _

/-- The meridian tangent has length `M`. -/
theorem norm_meridianTangent_sq (φ lam : ℝ) :
    ‖meridianTangent E φ lam‖ ^ 2 = meridianRadius E φ ^ 2 := by
  rw [meridianTangent, norm_vec3_sq]
  have h1 := sin_sq_add_cos_sq φ
  have h2 := sin_sq_add_cos_sq lam
  linear_combination meridianRadius E φ ^ 2 * sin φ ^ 2 * h2 + meridianRadius E φ ^ 2 * h1

/-- The parallel tangent has length `N cos φ`. -/
theorem norm_parallelTangent_sq (φ lam : ℝ) :
    ‖parallelTangent E φ lam‖ ^ 2 = (E.primeVerticalRadius φ * cos φ) ^ 2 := by
  rw [parallelTangent, norm_vec3_sq]
  have h2 := sin_sq_add_cos_sq lam
  linear_combination (E.primeVerticalRadius φ * cos φ) ^ 2 * h2

/-- Meridians and parallels of the ellipsoid cross at right angles. -/
theorem inner_meridianTangent_parallelTangent (φ lam : ℝ) :
    inner ℝ (meridianTangent E φ lam) (parallelTangent E φ lam) = (0 : ℝ) := by
  rw [meridianTangent, parallelTangent, inner_vec3]
  ring

/-- `N / M = (1 - e² sin² φ) / (1 - e²)`. -/
theorem N_div_M (φ : ℝ) :
    E.primeVerticalRadius φ / meridianRadius E φ = W2 E φ / (1 - E.e2) := by
  have hD := W2_pos E φ
  have hs : 0 < √(W2 E φ) := sqrt_pos.mpr hD
  have he := E.one_sub_e2_pos
  have ha := E.a_pos
  simp only [meridianRadius, ReferenceEllipsoid.primeVerticalRadius]
  rw [show 1 - E.e2 * sin φ ^ 2 = W2 E φ from rfl]
  field_simp

end ReferenceEllipsoid

end Geodesy
