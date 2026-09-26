import LeanGeodesy.Projection.Cylindrical
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# An equal-area projection, and Web Mercator's areas

Lambert's cylindrical equal-area projection is the cylindrical projection
with northing `R sin φ` (`lambertCylindrical`, an instance of the existing
`cylindrical` family). Locally it keeps areas (`lambert_isEqualArea`, from
`Cylindrical`). This file shows it keeps them globally too, and that Web
Mercator does not keep them at all.

A cell of the sphere between latitudes `φ₁, φ₂` and longitudes `λ₁, λ₂` has
area `∫∫ R · R cos φ dφ dλ`, the integral of the sphere's area element,
which is the first fundamental form's `M N cos φ` with `M = N = R`
(`sphereCellArea`, and `sphereCellArea_integrand_eq_areaElement`), which is
`R² (λ₂ - λ₁) (sin φ₂ - sin φ₁)` (`sphereCellArea_eq`). A cylindrical
projection draws the cell as a rectangle of area
`R² (λ₂ - λ₁) (g φ₂ - g φ₁)` (`cylindricalCellArea`).

- Lambert: the two areas are equal for every cell
  (`lambertCylindrical_preserves_cellArea`).
- Mercator: for every cell strictly north of the equator the map area is
  strictly larger (`mercator_enlarges_cellArea`), because
  `arsinh (tan φ) - sin φ` grows (`mercatorY_sub_sin_strictMonoOn`).
- Web Mercator on the ellipsoid: its area scale exceeds `1` at every
  latitude between the poles on any flattened ellipsoid with `e² ≤ 1/3`
  (`webMercator_areaScale_gt_one`), so it is not equal-area anywhere
  (`webMercator_not_isEqualArea`), and in particular not on WGS 84
  (`wgs84_webMercator_not_isEqualArea`).
- Lambert's projection is not conformal away from the equator
  (`lambertCylindrical_not_isConformal`).
-/

namespace Geodesy.Projection

open Real

/-- Lambert's cylindrical equal-area projection of the sphere of radius `R`. -/
noncomputable def lambertCylindrical (R φ lam : ℝ) : E2 := cylindrical R sin φ lam

/-- The area of the cell `[φ₁, φ₂] × [λ₁, λ₂]` of the sphere of radius `R`: the
integral of the sphere's area element `R · R cos φ`. -/
noncomputable def sphereCellArea (R φ₁ φ₂ lam₁ lam₂ : ℝ) : ℝ :=
  ∫ _ in lam₁..lam₂, ∫ φ in φ₁..φ₂, R * (R * cos φ)

theorem sphereCellArea_eq (R φ₁ φ₂ lam₁ lam₂ : ℝ) :
    sphereCellArea R φ₁ φ₂ lam₁ lam₂ = R ^ 2 * (lam₂ - lam₁) * (sin φ₂ - sin φ₁) := by
  simp only [sphereCellArea, intervalIntegral.integral_const_mul, integral_cos,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The area of the rectangle a cylindrical projection with northing `g` draws
the cell as. -/
def cylindricalCellArea (R : ℝ) (g : ℝ → ℝ) (φ₁ φ₂ lam₁ lam₂ : ℝ) : ℝ :=
  (R * lam₂ - R * lam₁) * (R * g φ₂ - R * g φ₁)

/-- Lambert's projection keeps the area of every cell. -/
theorem lambertCylindrical_preserves_cellArea (R φ₁ φ₂ lam₁ lam₂ : ℝ) :
    cylindricalCellArea R sin φ₁ φ₂ lam₁ lam₂ = sphereCellArea R φ₁ φ₂ lam₁ lam₂ := by
  rw [sphereCellArea_eq, cylindricalCellArea]
  ring

/-- `arsinh (tan φ) - sin φ` grows strictly from the equator to the pole. -/
theorem mercatorY_sub_sin_strictMonoOn :
    StrictMonoOn (fun φ => mercatorY φ - sin φ) (Set.Ico 0 (π / 2)) := by
  have hpi := pi_pos
  have hd : ∀ φ ∈ Set.Ico 0 (π / 2), HasDerivAt (fun φ => mercatorY φ - sin φ)
      (1 / cos φ - cos φ) φ := fun φ hφ =>
    (hasDerivAt_mercatorY (cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], hφ.2⟩)).sub (hasDerivAt_sin φ)
  refine strictMonoOn_of_deriv_pos (convex_Ico _ _)
    (fun φ hφ => (hd φ hφ).continuousAt.continuousWithinAt) fun φ hφ => ?_
  rw [interior_Ico] at hφ
  rw [(hd φ ⟨hφ.1.le, hφ.2⟩).deriv]
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [hφ.1], hφ.2⟩
  have hc1 : cos φ < 1 := by
    rw [← cos_zero]
    exact cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl hφ.2.le hφ.1
  rw [sub_pos, lt_div_iff₀ hc]
  nlinarith

/-- Mercator enlarges every cell strictly north of the equator. -/
theorem mercator_enlarges_cellArea {R φ₁ φ₂ lam₁ lam₂ : ℝ} (hR : 0 < R) (h₁ : 0 ≤ φ₁)
    (h₁₂ : φ₁ < φ₂) (h₂ : φ₂ < π / 2) (hl : lam₁ < lam₂) :
    sphereCellArea R φ₁ φ₂ lam₁ lam₂ < cylindricalCellArea R mercatorY φ₁ φ₂ lam₁ lam₂ := by
  have hm := mercatorY_sub_sin_strictMonoOn ⟨h₁, by linarith⟩ ⟨by linarith, h₂⟩ h₁₂
  simp only at hm
  rw [sphereCellArea_eq, cylindricalCellArea]
  have hR2 : 0 < R ^ 2 * (lam₂ - lam₁) := mul_pos (by positivity) (by linarith)
  have : R ^ 2 * (lam₂ - lam₁) * (sin φ₂ - sin φ₁) <
      R ^ 2 * (lam₂ - lam₁) * (mercatorY φ₂ - mercatorY φ₁) :=
    mul_lt_mul_of_pos_left (by linarith) hR2
  nlinarith

/-- Lambert's projection is not conformal away from the equator. -/
theorem lambertCylindrical_not_isConformal {R φ : ℝ} (hR : 0 < R) (hc : 0 < cos φ)
    (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) (h0 : φ ≠ 0) :
    ¬ (cylindricalDistortion hR (cos φ) hc).IsConformal :=
  fun hconf => h0 (eq_zero_of_isConformal_of_isEqualArea hR (cos φ) hc hφ hconf
    (lambert_isEqualArea hR hc))

/-! ## Web Mercator on the ellipsoid -/

/-- On a flattened ellipsoid with `e² ≤ 1/3`, Web Mercator (the spherical
Mercator formulas with radius `a`) enlarges areas at every latitude between
the poles. -/
theorem webMercator_areaScale_gt_one (E : ReferenceEllipsoid) (hf : 0 < E.f) (he : E.e2 ≤ 1 / 3)
    {φ : ℝ} (hc : 0 < cos φ) : 1 < (ellipsoidalMercatorDistortion E E.a hc).areaScale := by
  have horth : (inner (ellipsoidalMercatorDistortion E E.a hc).dLat
      (ellipsoidalMercatorDistortion E E.a hc).dLon : ℝ) = 0 := by
    simp [ellipsoidalMercatorDistortion, inner_vec2]
  rw [LocalDistortion.areaScale_of_orthogonal _ horth, ellipsoidalMercator_h E E.a_pos hc,
    ellipsoidalMercator_k E E.a_pos hc, meridianScale, parallelScale]
  have e2pos : 0 < E.e2 := mul_pos hf (by linarith [E.f_lt_one])
  have ha := E.a_pos
  have hW := E.W2_pos φ
  have hw : 0 < √(E.W2 φ) := sqrt_pos.mpr hW
  have hww : √(E.W2 φ) ^ 2 = E.W2 φ := sq_sqrt hW.le
  have hsc := sin_sq_add_cos_sq φ
  -- `W² ² > (1 - e²) cos² φ`, i.e. `M N cos² φ < a²`.
  have key : (1 - E.e2) * cos φ ^ 2 < E.W2 φ ^ 2 := by
    unfold ReferenceEllipsoid.W2
    nlinarith [sq_nonneg (sin φ), sq_nonneg (E.e2 * sin φ ^ 2), mul_nonneg e2pos.le (sq_nonneg (sin φ))]
  simp only [ReferenceEllipsoid.meridianRadius, ReferenceEllipsoid.primeVerticalRadius]
  rw [show 1 - E.e2 * sin φ ^ 2 = E.W2 φ from rfl]
  rw [show E.a / cos φ / (E.a * (1 - E.e2) / (E.W2 φ * √(E.W2 φ))) *
      (E.a / (E.a / √(E.W2 φ) * cos φ)) =
      E.W2 φ * √(E.W2 φ) * √(E.W2 φ) / ((1 - E.e2) * cos φ ^ 2) by
    field_simp [E.one_sub_e2_pos.ne']
    ring]
  rw [mul_assoc, ← sq, hww, one_lt_div (mul_pos E.one_sub_e2_pos (by positivity))]
  nlinarith

/-- So Web Mercator is not equal-area at any latitude between the poles. -/
theorem webMercator_not_isEqualArea (E : ReferenceEllipsoid) (hf : 0 < E.f) (he : E.e2 ≤ 1 / 3)
    {φ : ℝ} (hc : 0 < cos φ) : ¬ (ellipsoidalMercatorDistortion E E.a hc).IsEqualArea :=
  fun h => (webMercator_areaScale_gt_one E hf he hc).ne' h

/-- In particular on WGS 84. -/
theorem wgs84_webMercator_not_isEqualArea {φ : ℝ} (hc : 0 < cos φ) :
    ¬ (ellipsoidalMercatorDistortion wgs84 wgs84.a hc).IsEqualArea :=
  webMercator_not_isEqualArea wgs84 (by simp; norm_num)
    (by simp only [ReferenceEllipsoid.e2, wgs84_f]; norm_num) hc

end Geodesy.Projection
