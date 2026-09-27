import LeanGeodesy.Projection.Distortion
import LeanGeodesy.Projection.WebMercator
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Cylindrical projections of the sphere

A cylindrical projection of the sphere of radius `R` keeps meridians as
equally spaced vertical lines and places the parallel at latitude `φ` at
height `R g(φ)`:

```
x = R λ,   y = R g(φ)                  (cylindrical)
```

Its partial derivatives are `(0, R g'(φ))` and `(R, 0)`
(`hasDerivAt_cylindrical_lat`, `hasDerivAt_cylindrical_lon`), always
perpendicular. So on the sphere, where the ground steps have lengths `R` and
`R cos φ` (`cylindricalDistortion`),

- the scale along the parallel is always `k = sec φ` (`cylindrical_k`),
  since every parallel is drawn as long as the equator;
- the scale along the meridian is `h = |g'(φ)|` (`cylindrical_h`);
- the area scale is `|g'(φ)| sec φ` (`cylindrical_areaScale`).

The choice of `g` decides what is kept:

| Projection | `g(φ)` | `h` | `k` | area scale |
| --- | --- | --- | --- | --- |
| Mercator | `arsinh (tan φ)` | `sec φ` | `sec φ` | `sec² φ` |
| Plate carrée | `φ` | `1` | `sec φ` | `sec φ` |
| Lambert cylindrical equal-area | `sin φ` | `cos φ` | `sec φ` | `1` |

Mercator is conformal (`mercator_isConformal`), Lambert's is equal-area
(`lambert_isEqualArea`), and plate carrée is neither away from the equator,
but keeps distances along meridians (`plateCarree_h`).

Conversely, a cylindrical projection with north up and the equator on the
`x` axis that is conformal at every latitude is Mercator's
(`eq_mercatorY_of_isConformal`), and one that is equal-area at every
latitude is Lambert's (`eq_sin_of_isEqualArea`): the condition on `g'`
fixes `g`. No cylindrical projection is both at any latitude but the
equator (`eq_zero_of_isConformal_of_isEqualArea`), since `sec φ = cos φ`
only there.

On an ellipsoid the ground steps have lengths `M` and `N cos φ` instead.
Web Mercator, which uses the spherical formulas there, has scales
`a sec φ / M` and `a sec φ / N` (`ellipsoidalMercator_h`,
`ellipsoidalMercator_k`), and so is not conformal on a flattened ellipsoid
(`ellipsoidalMercator_not_isConformal`).
-/

namespace Geodesy.Projection

open Real

/-- The cylindrical projection with northing function `g`. -/
noncomputable def cylindrical (R : ℝ) (g : ℝ → ℝ) (φ lam : ℝ) : E2 := vec2 (R * lam) (R * g φ)

theorem hasDerivAt_cylindrical_lat (R : ℝ) {g : ℝ → ℝ} {g' φ : ℝ} (hg : HasDerivAt g g' φ)
    (lam : ℝ) : HasDerivAt (fun φ => cylindrical R g φ lam) (vec2 0 (R * g')) φ :=
  hasDerivAt_vec2 (hasDerivAt_const _ _) (hg.const_mul R)

theorem hasDerivAt_cylindrical_lon (R : ℝ) (g : ℝ → ℝ) (φ lam : ℝ) :
    HasDerivAt (fun lam => cylindrical R g φ lam) (vec2 R 0) lam := by
  refine hasDerivAt_vec2 ?_ (hasDerivAt_const _ _)
  simpa using (hasDerivAt_id lam).const_mul R

theorem norm_vec2_zero_left (y : ℝ) : ‖vec2 0 y‖ = |y| := by
  rw [← sqrt_sq (norm_nonneg _), norm_vec2_sq, zero_pow two_ne_zero, zero_add, sqrt_sq_eq_abs]

theorem norm_vec2_zero_right (x : ℝ) : ‖vec2 x 0‖ = |x| := by
  rw [← sqrt_sq (norm_nonneg _), norm_vec2_sq, zero_pow two_ne_zero, add_zero, sqrt_sq_eq_abs]

/-- The distortion of a cylindrical projection whose northing function has
derivative `g'` at a latitude `φ` with `cos φ > 0`, on the sphere of radius `R`. -/
noncomputable def cylindricalDistortion {R : ℝ} (hR : 0 < R) (g' : ℝ) {φ : ℝ} (hc : 0 < cos φ) :
    LocalDistortion :=
  ⟨R, R * cos φ, hR, mul_pos hR hc, vec2 0 (R * g'), vec2 R 0⟩

/-! ## The spherical formulas on an ellipsoid -/

/-- The distortion of a Mercator map of radius `R`, fed with geodetic latitudes,
measured on the ellipsoid `E`, as Web Mercator is. -/
noncomputable def ellipsoidalMercatorDistortion (E : ReferenceEllipsoid) (R : ℝ) {φ : ℝ}
    (hc : 0 < cos φ) : LocalDistortion :=
  ⟨E.meridianRadius φ, E.primeVerticalRadius φ * cos φ, E.meridianRadius_pos φ,
    mul_pos (E.primeVerticalRadius_pos φ) hc, vec2 0 (R / cos φ), vec2 R 0⟩

section Ellipsoidal

variable (E : ReferenceEllipsoid) {R : ℝ} (hR : 0 < R) {φ : ℝ} (hc : 0 < cos φ)
include hR hc

theorem ellipsoidalMercator_h :
    (ellipsoidalMercatorDistortion E R hc).h = meridianScale E R φ := by
  simp only [LocalDistortion.h, ellipsoidalMercatorDistortion, norm_vec2_zero_left,
    abs_of_pos (div_pos hR hc), meridianScale]

theorem ellipsoidalMercator_k :
    (ellipsoidalMercatorDistortion E R hc).k = parallelScale E R φ := by
  simp only [LocalDistortion.k, ellipsoidalMercatorDistortion, norm_vec2_zero_right,
    abs_of_pos hR, parallelScale]

/-- On a flattened ellipsoid the spherical Mercator formulas are not conformal. -/
theorem ellipsoidalMercator_not_isConformal (hf : 0 < E.f) :
    ¬ (ellipsoidalMercatorDistortion E R hc).IsConformal := by
  rintro ⟨_, hhk⟩
  rw [ellipsoidalMercator_h E hR hc, ellipsoidalMercator_k E hR hc] at hhk
  exact (meridianScale_gt_parallelScale E hf R hR hc).ne' hhk

end Ellipsoidal

variable {R : ℝ} (hR : 0 < R) (g' : ℝ) {φ : ℝ} (hc : 0 < cos φ)
include hR hc

theorem cylindrical_orthogonal :
    (inner ℝ (cylindricalDistortion hR g' hc).dLat (cylindricalDistortion hR g' hc).dLon : ℝ) = 0 := by
  simp [cylindricalDistortion, inner_vec2]

/-- The scale along the meridian is `|g'|`. -/
theorem cylindrical_h : (cylindricalDistortion hR g' hc).h = |g'| := by
  simp only [LocalDistortion.h, cylindricalDistortion, norm_vec2_zero_left, abs_mul,
    abs_of_pos hR]
  field_simp

/-- The scale along the parallel is `sec φ`. -/
theorem cylindrical_k : (cylindricalDistortion hR g' hc).k = 1 / cos φ := by
  simp only [LocalDistortion.k, cylindricalDistortion, norm_vec2_zero_right, abs_of_pos hR]
  field_simp

/-- The area scale is `|g'| sec φ`. -/
theorem cylindrical_areaScale : (cylindricalDistortion hR g' hc).areaScale = |g'| / cos φ := by
  rw [LocalDistortion.areaScale_of_orthogonal _ (cylindrical_orthogonal hR g' hc),
    cylindrical_h hR g' hc, cylindrical_k hR g' hc]
  ring

/-- A cylindrical projection is conformal at `φ` exactly when `|g'| = sec φ`. -/
theorem cylindrical_isConformal_iff :
    (cylindricalDistortion hR g' hc).IsConformal ↔ |g'| = 1 / cos φ := by
  rw [LocalDistortion.IsConformal, cylindrical_h hR g' hc, cylindrical_k hR g' hc]
  exact ⟨fun h => h.2, fun h => ⟨cylindrical_orthogonal hR g' hc, h⟩⟩

/-- It is equal-area at `φ` exactly when `|g'| = cos φ`. -/
theorem cylindrical_isEqualArea_iff :
    (cylindricalDistortion hR g' hc).IsEqualArea ↔ |g'| = cos φ := by
  rw [LocalDistortion.IsEqualArea, cylindrical_areaScale hR g' hc, div_eq_one_iff_eq hc.ne']

/-- Mercator (`g = mercatorY`, `g' = sec φ`) is conformal. -/
theorem mercator_isConformal : (cylindricalDistortion hR (1 / cos φ) hc).IsConformal := by
  rw [cylindrical_isConformal_iff, abs_of_pos (one_div_pos.mpr hc)]

/-- Its area scale is `sec² φ`. -/
theorem mercator_areaScale : (cylindricalDistortion hR (1 / cos φ) hc).areaScale = 1 / cos φ ^ 2 := by
  rw [cylindrical_areaScale, abs_of_pos (one_div_pos.mpr hc)]
  field_simp

/-- Plate carrée (`g = id`, `g' = 1`) keeps distances along meridians. -/
theorem plateCarree_h : (cylindricalDistortion hR 1 hc).h = 1 := by
  rw [cylindrical_h, abs_one]

/-- Lambert's cylindrical projection (`g = sin`, `g' = cos φ`) is equal-area. -/
theorem lambert_isEqualArea : (cylindricalDistortion hR (cos φ) hc).IsEqualArea := by
  rw [cylindrical_isEqualArea_iff, abs_of_pos hc]

/-! ## Uniqueness -/

omit hR hc in
/-- Two functions with the same derivative on the open latitudes that agree at
the equator agree everywhere between the poles. -/
theorem eqOn_of_hasDerivAt_eq {f g d : ℝ → ℝ}
    (hf : ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), HasDerivAt f (d φ) φ)
    (hg : ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), HasDerivAt g (d φ) φ) (h0 : f 0 = g 0) :
    ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), f φ = g φ := by
  have hpi := pi_pos
  have hd : ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), HasDerivAt (fun t => f t - g t) 0 φ := fun φ hφ => by
    convert (hf φ hφ).sub (hg φ hφ) using 1
    rw [sub_self]
  intro φ hφ
  have hmem0 : (0 : ℝ) ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have hconst := Convex.is_const_of_fderivWithin_eq_zero (convex_Ioo _ _)
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [fderivWithin_of_isOpen isOpen_Ioo hx, (hd x hx).hasFDerivAt.fderiv]
      ext
      simp) hφ hmem0
  simp only [h0, sub_self] at hconst
  linarith

omit hR hc in
/-- A cylindrical projection with north up that is conformal at every latitude
between the poles, with the equator at height zero, is Mercator's. -/
theorem eq_mercatorY_of_isConformal {g g' : ℝ → ℝ} (hR : 0 < R) (h0 : g 0 = 0)
    (hg : ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), HasDerivAt g (g' φ) φ) (hpos : ∀ φ, 0 < g' φ)
    (hconf : ∀ φ (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)),
      (cylindricalDistortion hR (g' φ) (cos_pos_of_mem_Ioo hφ)).IsConformal) :
    ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), g φ = mercatorY φ := by
  refine eqOn_of_hasDerivAt_eq (d := fun φ => 1 / cos φ) (fun φ hφ => ?_)
    (fun φ hφ => hasDerivAt_mercatorY (cos_pos_of_mem_Ioo hφ)) (by rw [h0, mercatorY_zero])
  have h := (cylindrical_isConformal_iff hR (g' φ) (cos_pos_of_mem_Ioo hφ)).mp (hconf φ hφ)
  rw [abs_of_pos (hpos φ)] at h
  show HasDerivAt g (1 / cos φ) φ
  rw [← h]
  exact hg φ hφ

omit hR hc in
/-- A cylindrical projection with north up that is equal-area at every
latitude between the poles, with the equator at height zero, is Lambert's. -/
theorem eq_sin_of_isEqualArea {g g' : ℝ → ℝ} (hR : 0 < R) (h0 : g 0 = 0)
    (hg : ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), HasDerivAt g (g' φ) φ) (hpos : ∀ φ, 0 < g' φ)
    (harea : ∀ φ (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)),
      (cylindricalDistortion hR (g' φ) (cos_pos_of_mem_Ioo hφ)).IsEqualArea) :
    ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), g φ = sin φ := by
  refine eqOn_of_hasDerivAt_eq (d := cos) (fun φ hφ => ?_) (fun φ _ => hasDerivAt_sin φ)
    (by rw [h0, sin_zero])
  have h := (cylindrical_isEqualArea_iff hR (g' φ) (cos_pos_of_mem_Ioo hφ)).mp (harea φ hφ)
  rw [abs_of_pos (hpos φ)] at h
  rw [← h]
  exact hg φ hφ

/-- A cylindrical projection that is both conformal and equal-area at a
latitude between the poles is at the equator. -/
theorem eq_zero_of_isConformal_of_isEqualArea (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2))
    (hconf : (cylindricalDistortion hR g' hc).IsConformal)
    (harea : (cylindricalDistortion hR g' hc).IsEqualArea) : φ = 0 := by
  have h1 := (cylindrical_isConformal_iff hR g' hc).mp hconf
  have h2 := (cylindrical_isEqualArea_iff hR g' hc).mp harea
  rw [h1] at h2
  have hc1 : cos φ = 1 := by
    field_simp at h2
    nlinarith [cos_le_one φ]
  have hpi := pi_pos
  exact (cos_eq_one_iff_of_lt_of_lt (by linarith [hφ.1]) (by linarith [hφ.2])).mp hc1


omit hR hc in
/-- The northing functions have the derivatives used above. -/
theorem hasDerivAt_northings {φ : ℝ} (hc : 0 < cos φ) :
    HasDerivAt mercatorY (1 / cos φ) φ ∧ HasDerivAt (fun φ => φ) 1 φ ∧
      HasDerivAt sin (cos φ) φ :=
  ⟨hasDerivAt_mercatorY hc, hasDerivAt_id φ, hasDerivAt_sin φ⟩

end Geodesy.Projection
