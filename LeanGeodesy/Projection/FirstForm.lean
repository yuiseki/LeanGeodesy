import LeanGeodesy.FirstFundamentalForm
import LeanGeodesy.Projection.RhumbVsGreatCircle
import LeanGeodesy.Projection.EqualArea
import LeanGeodesy.MeridianArc

/-!
# The first fundamental form behind distortion, rhumb lines and areas

Short connections between `FirstFundamentalForm` and the projection files.

- The sphere tangents of `Projection.Mercator` are the ellipsoid tangents of
  the spherical reference ellipsoid (`sphere_meridianTangent_eq`,
  `sphere_parallelTangent_eq`), so the squared speed of a path parametrised
  by latitude is the first fundamental form of `(1, λ')`
  (`norm_sq_latitudeCurve_eq_firstForm`), and the rhumb line's speed
  `R / cos α` is its special case (`rhumb_speed_sq_eq_firstForm`).
- The integrand `R · R cos φ` of `sphereCellArea` is the sphere's area
  element (`sphereCellArea_integrand_eq_areaElement`).
- A local distortion measured on the ellipsoid has reference lengths `M` and
  `N cos φ`, the square roots of `E` and `G` (`LocalDistortion.ofEllipsoid`).
  It is conformal exactly when the map multiplies the first fundamental form
  by `h²` (`isConformal_iff_firstForm`): conformality is preserving the
  metric up to a scalar. The Web Mercator distortion of `Cylindrical` is of
  this form (`ellipsoidalMercatorDistortion_eq_ofEllipsoid`). Its area scale
  is the map Jacobian's area over the first fundamental form's area element,
  `|det (dLat, dLon)| / √(E G - F²)` (`areaScale_ofEllipsoid`).
- The meridian moves at speed `√I(1, 0) = M` (`norm_deriv_meridian`,
  `sqrt_firstForm_lat`), so the meridian arc `∫₀^φ M` is its curve length
  (`meridianArc_eq_curveLength`).
-/

namespace Geodesy.Projection

open Real ReferenceEllipsoid

variable {R : ℝ} (hR : 0 < R)
include hR

theorem sphere_meridianTangent_eq (φ lam : ℝ) :
    meridianTangent R φ lam = (ofSphere R hR).meridianTangent φ lam := by
  simp only [meridianTangent, ReferenceEllipsoid.meridianTangent, meridianRadius_ofSphere hR]
  refine vec3_congr ?_ ?_ ?_ <;> ring

theorem sphere_parallelTangent_eq (φ lam : ℝ) :
    parallelTangent R φ lam = (ofSphere R hR).parallelTangent φ lam := by
  simp only [parallelTangent, ReferenceEllipsoid.parallelTangent, primeVerticalRadius_ofSphere hR]

/-- The squared speed of a path parametrised by latitude on the sphere is the
first fundamental form of `(1, λ')`. -/
theorem norm_sq_latitudeCurve_eq_firstForm (φ lam lon' : ℝ) :
    ‖meridianTangent R φ lam + lon' • parallelTangent R φ lam‖ ^ 2 =
      (ofSphere R hR).firstForm φ (1, lon') := by
  rw [sphere_meridianTangent_eq hR, sphere_parallelTangent_eq hR, ← norm_dr_sq _ φ lam]
  simp [dr]

/-- The rhumb line's speed `R / cos α` is the first fundamental form of its
coordinate velocity `(1, tan α / cos φ)`. -/
theorem rhumb_speed_sq_eq_firstForm (lam₀ φ₀ : ℝ) {α : ℝ} (hα : α ∈ Set.Ioo (-(π / 2)) (π / 2))
    {φ : ℝ} (hc : 0 < cos φ) :
    (R / cos α) ^ 2 = (ofSphere R hR).firstForm φ (1, tan α / cos φ) := by
  rw [← norm_rhumb_tangent hR lam₀ φ₀ hα hc, norm_sq_latitudeCurve_eq_firstForm hR]

/-- The integrand of `sphereCellArea` is the sphere's area element. -/
theorem sphereCellArea_integrand_eq_areaElement {φ : ℝ} (hc : 0 ≤ cos φ) (lam : ℝ) :
    R * (R * cos φ) = (ofSphere R hR).areaElement φ lam := by
  rw [areaElement_ofSphere hR hc]
  ring

omit hR

/-- A local distortion measured on the ellipsoid: reference lengths `M` and
`N cos φ`, the square roots of the first fundamental form's `E` and `G`. -/
noncomputable def LocalDistortion.ofEllipsoid (E : ReferenceEllipsoid) {φ : ℝ} (hc : 0 < cos φ)
    (dLat dLon : E2) : LocalDistortion :=
  ⟨E.meridianRadius φ, E.primeVerticalRadius φ * cos φ, E.meridianRadius_pos φ,
    mul_pos (E.primeVerticalRadius_pos φ) hc, dLat, dLon⟩

theorem LocalDistortion.ofEllipsoid_lengths_sq (E : ReferenceEllipsoid) {φ : ℝ} (hc : 0 < cos φ)
    (dLat dLon : E2) (lam : ℝ) :
    (LocalDistortion.ofEllipsoid E hc dLat dLon).meridianLength ^ 2 = E.firstFormE φ lam ∧
      (LocalDistortion.ofEllipsoid E hc dLat dLon).parallelLength ^ 2 = E.firstFormG φ lam := by
  rw [firstFormE_eq, firstFormG_eq]
  exact ⟨rfl, rfl⟩

/-- Conformal means that the map multiplies the first fundamental form by `h²`:
the squared map length of the image of every coordinate step `v` is `h²` times
its squared length on the ellipsoid. -/
theorem isConformal_iff_firstForm (E : ReferenceEllipsoid) {φ : ℝ} (hc : 0 < cos φ)
    (dLat dLon : E2) :
    (LocalDistortion.ofEllipsoid E hc dLat dLon).IsConformal ↔
      ∀ v : ℝ × ℝ, ‖v.1 • dLat + v.2 • dLon‖ ^ 2 =
        (LocalDistortion.ofEllipsoid E hc dLat dLon).h ^ 2 * E.firstForm φ v := by
  rw [LocalDistortion.isConformal_iff]
  constructor
  · intro h v
    have hv := h v.1 v.2
    dsimp only [LocalDistortion.ofEllipsoid] at hv ⊢
    rw [hv]
    simp only [firstForm, metric]
    ring
  · intro h α β
    have hv := h (α, β)
    dsimp only [LocalDistortion.ofEllipsoid] at hv ⊢
    rw [hv]
    simp only [firstForm, metric]
    ring

/-- The local area distortion of a projection measured on the ellipsoid is the
area of the map Jacobian over the first fundamental form's area element. -/
theorem areaScale_ofEllipsoid (E : ReferenceEllipsoid) {φ : ℝ} (hc : 0 < cos φ) (dLat dLon : E2)
    (lam : ℝ) :
    (LocalDistortion.ofEllipsoid E hc dLat dLon).areaScale =
      |LocalDistortion.det2 dLat dLon| / E.areaElement φ lam := by
  rw [E.areaElement_eq hc.le, LocalDistortion.areaScale]
  simp only [LocalDistortion.ofEllipsoid, mul_assoc]

/-- `√I(1, 0) = M`: a unit step in latitude has length `M`. -/
theorem sqrt_firstForm_lat (E : ReferenceEllipsoid) (φ : ℝ) :
    √(E.firstForm φ (1, 0)) = E.meridianRadius φ := by
  simp only [firstForm, metric, mul_one, mul_zero, add_zero]
  exact sqrt_sq (E.meridianRadius_pos φ).le

/-- The meridian through longitude `lam` moves at speed `√I(1, 0)`. -/
theorem norm_deriv_meridian (E : ReferenceEllipsoid) (φ lam : ℝ) :
    ‖deriv (fun φ => E.ellipsoidPoint φ lam) φ‖ = √(E.firstForm φ (1, 0)) := by
  rw [deriv_lat, ← norm_dr E φ lam]
  simp [dr]

/-- The meridian arc from the equator to `φ` is the curve length of the meridian,
the integral of its first-fundamental-form speed. -/
theorem meridianArc_eq_curveLength (E : ReferenceEllipsoid) (φ lam : ℝ) :
    E.meridianArc φ = curveLength (fun φ => E.ellipsoidPoint φ lam) 0 φ := by
  rw [curveLength, meridianArc]
  refine intervalIntegral.integral_congr fun ψ _ => ?_
  rw [norm_deriv_meridian, sqrt_firstForm_lat]

/-- The Web Mercator distortion on the ellipsoid is measured against the first
fundamental form. -/
theorem ellipsoidalMercatorDistortion_eq_ofEllipsoid (E : ReferenceEllipsoid) (R' : ℝ) {φ : ℝ}
    (hc : 0 < cos φ) :
    ellipsoidalMercatorDistortion E R' hc =
      LocalDistortion.ofEllipsoid E hc (vec2 0 (R' / cos φ)) (vec2 R' 0) :=
  rfl

end Geodesy.Projection
