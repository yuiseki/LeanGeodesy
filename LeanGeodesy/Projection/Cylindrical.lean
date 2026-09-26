import LeanGeodesy.Projection.Distortion

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

variable {R : ℝ} (hR : 0 < R) (g' : ℝ) {φ : ℝ} (hc : 0 < cos φ)
include hR hc

theorem cylindrical_orthogonal :
    (inner (cylindricalDistortion hR g' hc).dLat (cylindricalDistortion hR g' hc).dLon : ℝ) = 0 := by
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
  ring

/-- Plate carrée (`g = id`, `g' = 1`) keeps distances along meridians. -/
theorem plateCarree_h : (cylindricalDistortion hR 1 hc).h = 1 := by
  rw [cylindrical_h, abs_one]

/-- Lambert's cylindrical projection (`g = sin`, `g' = cos φ`) is equal-area. -/
theorem lambert_isEqualArea : (cylindricalDistortion hR (cos φ) hc).IsEqualArea := by
  rw [cylindrical_isEqualArea_iff, abs_of_pos hc]

omit hR hc in
/-- The northing functions have the derivatives used above. -/
theorem hasDerivAt_northings {φ : ℝ} (hc : 0 < cos φ) :
    HasDerivAt mercatorY (1 / cos φ) φ ∧ HasDerivAt (fun φ => φ) 1 φ ∧
      HasDerivAt sin (cos φ) φ :=
  ⟨hasDerivAt_mercatorY hc, hasDerivAt_id φ, hasDerivAt_sin φ⟩

end Geodesy.Projection
