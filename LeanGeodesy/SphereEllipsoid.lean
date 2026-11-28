import LeanGeodesy.Spherical.Packing
import LeanGeodesy.Curvature
import LeanGeodesy.Projection.Mercator
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Unit sphere, spheres of radius `R` and the reference ellipsoid

The unit sphere, the sphere of radius `R` and an ellipsoid of revolution are the same
topological surface. This file makes the identifications explicit, with Mathlib's types:

1. **Point set and subtype.** `sphere_one_eq_setOf : sphere 1 = {x | ‖x‖ = 1}`, and the
   homeomorphism `unitSphereHomeomorph : UnitSphere ≃ₜ Metric.sphere (0 : E3) 1` (identity on
   vectors, an isometry).
2. **Radius `R`.** `sphereScale hR : Metric.sphere 0 1 ≃ₜ Metric.sphere 0 R`, `x ↦ R • x`, with
   `dist_sphereScale`: every distance is multiplied by exactly `R`.
3. **Axis scaling.** `axisScale a b = diag(a, a, b)`, the continuous linear equivalence
   `axisScaleEquiv : E3 ≃L[ℝ] E3` (`a, b ≠ 0`), the set equality
   `axisScale_image_sphere : axisScale a b '' sphere 1 = ellipsoid a b`, the homeomorphism
   `sphereEllipsoidHomeomorph : Metric.sphere 0 1 ≃ₜ ellipsoid a b`, and for a reference
   ellipsoid `ReferenceEllipsoid.sphereHomeomorph : Metric.sphere 0 1 ≃ₜ E.toSet` and
   `ReferenceEllipsoid.unitSphereHomeomorph : UnitSphere ≃ₜ E.toSet`.
4. **Bi-Lipschitz bounds.** For `0 < b ≤ a` and all `u v : E3`,
   `b * dist u v ≤ dist (S u) (S v) ≤ a * dist u v` (`dist_axisScale_bounds`); both constants
   are attained, by the antipodal equator pair (`dist_axisScale_equator`) and the pole pair
   (`dist_axisScale_poles`), which lie on the unit sphere (`extremal_pairs_mem_sphere`).
5. **Topology.** The ellipsoid is compact, connected, closed and bounded
   (`isCompact_ellipsoid`, `isConnected_ellipsoid`, `isClosed_ellipsoid`,
   `isBounded_ellipsoid`, and the subtype instances-as-theorems `compactSpace_ellipsoid`,
   `connectedSpace_ellipsoid`), because the unit sphere is.
6. **Linear scaling is not the geodetic correspondence.** `S` sends the unit-sphere point at
   latitude `β` to the ellipsoid point with *parametric (reduced)* latitude `β`
   (`axisScale_spherePoint`). On a flattened ellipsoid (`0 < f`) it does **not** send latitude
   `φ ∈ (0, π/2)` to geodetic latitude `φ` (`axisScale_spherePoint_ne_ellipsoidPoint`); the
   three hypotheses are each necessary (`axisScale_spherePoint_eq_ellipsoidPoint_of_f_eq_zero`,
   `axisScale_spherePoint_zero_eq_ellipsoidPoint`,
   `axisScale_spherePoint_pi_div_two_eq_ellipsoidPoint`). The correct correspondence is
   `ellipsoidPoint_eq_axisScale_spherePoint`: geodetic latitude `φ` with `|φ| < π / 2`
   corresponds to the unit-sphere latitude `β = parametricLatitude E φ`,
   `tan β = (b / a) tan φ`.

Related files: `SphereEllipsoid/StereographicMercator.lean` (polar stereographic in terms of
the Mercator ordinate) and `SphereEllipsoid/ChordApprox.lean` (arc minus chord `≤ θ³ / 24`).

What is not proved here: that `axisScale` is the *only* linear map onto the ellipsoid, any
statement about distances measured *along* the ellipsoid (geodesic distance), and the
bi-Lipschitz constants for the intrinsic (geodesic) metrics; all distances are Euclidean
distances in `E3`.
-/

namespace Geodesy.SphereEllipsoid

open Real Geodesy.Spherical Geodesy.Projection

/-! ## 1. The unit sphere as a point set and as a subtype -/

/-- `Geodesy.sphere 1` is the point set `{x | ‖x‖ = 1}`. -/
theorem sphere_one_eq_setOf : sphere 1 = {x : E3 | ‖x‖ = 1} := by
  ext x
  rw [Set.mem_ofPred_eq]
  exact mem_sphere_one_iff x

/-- The subtype `UnitSphere = {x : E3 // ‖x‖ = 1}` is homeomorphic to the subtype of the
set `Metric.sphere 0 1`; both maps are the identity on the underlying vector. -/
noncomputable def unitSphereHomeomorph : UnitSphere ≃ₜ Metric.sphere (0 : E3) 1 where
  toFun x := ⟨x.1, mem_sphere_zero_iff_norm.mpr x.2⟩
  invFun x := ⟨x.1, mem_sphere_zero_iff_norm.mp x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    continuous_subtype_val.subtype_mk fun x : UnitSphere => mem_sphere_zero_iff_norm.mpr x.2
  continuous_invFun := continuous_subtype_val.subtype_mk fun x : Metric.sphere (0 : E3) 1 =>
    mem_sphere_zero_iff_norm.mp x.2

@[simp] theorem coe_unitSphereHomeomorph (x : UnitSphere) :
    ((unitSphereHomeomorph x : Metric.sphere (0 : E3) 1) : E3) = x.1 := rfl

@[simp] theorem coe_unitSphereHomeomorph_symm (x : Metric.sphere (0 : E3) 1) :
    ((unitSphereHomeomorph.symm x : UnitSphere) : E3) = x.1 := rfl

/-- The homeomorphism is an isometry. -/
theorem dist_unitSphereHomeomorph (x y : UnitSphere) :
    dist (unitSphereHomeomorph x) (unitSphereHomeomorph y) = dist x y := rfl

/-! ## 2. The sphere of radius `R` and the unit sphere -/

/-- Scaling by `R > 0` maps the unit sphere onto the sphere of radius `R`. -/
noncomputable def sphereScale {R : ℝ} (hR : 0 < R) :
    Metric.sphere (0 : E3) 1 ≃ₜ Metric.sphere (0 : E3) R where
  toFun x := ⟨R • x.1, by
    have := x.2
    rw [mem_sphere_zero_iff_norm] at this ⊢
    rw [norm_smul, this, Real.norm_eq_abs, abs_of_pos hR, mul_one]⟩
  invFun x := ⟨R⁻¹ • x.1, by
    have := x.2
    rw [mem_sphere_zero_iff_norm] at this ⊢
    rw [norm_smul, this, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), inv_mul_cancel₀ hR.ne']⟩
  left_inv x := Subtype.ext (by simp [smul_smul, inv_mul_cancel₀ hR.ne'])
  right_inv x := Subtype.ext (by simp [smul_smul, mul_inv_cancel₀ hR.ne'])
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem coe_sphereScale {R : ℝ} (hR : 0 < R) (x : Metric.sphere (0 : E3) 1) :
    ((sphereScale hR x : Metric.sphere (0 : E3) R) : E3) = R • x.1 := rfl

@[simp] theorem coe_sphereScale_symm {R : ℝ} (hR : 0 < R) (x : Metric.sphere (0 : E3) R) :
    (((sphereScale hR).symm x : Metric.sphere (0 : E3) 1) : E3) = R⁻¹ • x.1 := rfl

/-- Scaling multiplies every distance by exactly `R`. -/
theorem dist_sphereScale {R : ℝ} (hR : 0 < R) (x y : Metric.sphere (0 : E3) 1) :
    dist (sphereScale hR x) (sphereScale hR y) = R * dist x y := by
  rw [Subtype.dist_eq, Subtype.dist_eq, coe_sphereScale, coe_sphereScale, dist_smul₀,
    Real.norm_eq_abs, abs_of_pos hR]

/-! ## 3. The axis scaling `diag(a, a, b)` -/

/-- The linear map `S = diag(a, a, b)`: stretch the equatorial plane by `a` and the
polar axis by `b`. -/
noncomputable def axisScale (a b : ℝ) (v : E3) : E3 := vec3 (a * v 0) (a * v 1) (b * v 2)

@[simp] theorem axisScale_apply_0 (a b : ℝ) (v : E3) : axisScale a b v 0 = a * v 0 := rfl
@[simp] theorem axisScale_apply_1 (a b : ℝ) (v : E3) : axisScale a b v 1 = a * v 1 := rfl
@[simp] theorem axisScale_apply_2 (a b : ℝ) (v : E3) : axisScale a b v 2 = b * v 2 := rfl

theorem axisScale_vec3 (a b x y z : ℝ) :
    axisScale a b (vec3 x y z) = vec3 (a * x) (a * y) (b * z) := rfl

theorem axisScale_add (a b : ℝ) (u v : E3) :
    axisScale a b (u + v) = axisScale a b u + axisScale a b v := by
  ext i; fin_cases i <;> simp [axisScale] <;> ring

theorem axisScale_smul (a b c : ℝ) (v : E3) :
    axisScale a b (c • v) = c • axisScale a b v := by
  ext i; fin_cases i <;> simp [axisScale] <;> ring

theorem axisScale_sub (a b : ℝ) (u v : E3) :
    axisScale a b (u - v) = axisScale a b u - axisScale a b v := by
  ext i; fin_cases i <;> simp [axisScale] <;> ring

theorem axisScale_axisScale (a b a' b' : ℝ) (v : E3) :
    axisScale a b (axisScale a' b' v) = axisScale (a * a') (b * b') v := by
  ext i; fin_cases i <;> simp [axisScale] <;> ring

@[simp] theorem axisScale_one_one (v : E3) : axisScale 1 1 v = v := by
  ext i; fin_cases i <;> simp [axisScale]

/-- `S = diag(a, a, b)` as a linear map. -/
noncomputable def axisScaleLinear (a b : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun := axisScale a b
  map_add' := axisScale_add a b
  map_smul' := axisScale_smul a b

theorem continuous_axisScale (a b : ℝ) : Continuous (axisScale a b) :=
  (axisScaleLinear a b).continuous_of_finiteDimensional

/-- For `a, b ≠ 0`, `S = diag(a, a, b)` as a continuous linear equivalence of `E3`;
its inverse is `diag(a⁻¹, a⁻¹, b⁻¹)`. -/
noncomputable def axisScaleEquiv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : E3 ≃L[ℝ] E3 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := axisScale a b
      invFun := axisScale a⁻¹ b⁻¹
      map_add' := axisScale_add a b
      map_smul' := axisScale_smul a b
      left_inv := fun v => by
        rw [axisScale_axisScale, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb, axisScale_one_one]
      right_inv := fun v => by
        rw [axisScale_axisScale, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, axisScale_one_one] }

@[simp] theorem coe_axisScaleEquiv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ⇑(axisScaleEquiv ha hb) = axisScale a b := rfl

@[simp] theorem coe_axisScaleEquiv_symm {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ⇑(axisScaleEquiv ha hb).symm = axisScale a⁻¹ b⁻¹ := rfl

/-- The squared norm of `S v`. -/
theorem norm_axisScale_sq (a b : ℝ) (v : E3) :
    ‖axisScale a b v‖ ^ 2 = a ^ 2 * (v 0 ^ 2 + v 1 ^ 2) + b ^ 2 * v 2 ^ 2 := by
  rw [norm_sq_eq]; simp only [axisScale_apply_0, axisScale_apply_1, axisScale_apply_2]; ring

/-- `S` maps the point set `Metric.sphere 0 1` onto the ellipsoid `ellipsoid a b`. -/
theorem axisScale_image_metricSphere {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    axisScale a b '' Metric.sphere (0 : E3) 1 = ellipsoid a b := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hv
    have h := norm_sq_eq v
    rw [hv] at h
    rw [mem_ellipsoid]
    simp only [axisScale_apply_0, axisScale_apply_1, axisScale_apply_2]
    rw [show (a * v 0) ^ 2 + (a * v 1) ^ 2 = a ^ 2 * (v 0 ^ 2 + v 1 ^ 2) by ring, mul_pow b,
      mul_div_cancel_left₀ _ ha2, mul_div_cancel_left₀ _ hb2]
    linarith
  · intro hw
    rw [mem_ellipsoid] at hw
    refine ⟨axisScale a⁻¹ b⁻¹ w, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm]
      have h := norm_axisScale_sq a⁻¹ b⁻¹ w
      have h1 : ‖axisScale a⁻¹ b⁻¹ w‖ ^ 2 = 1 := by
        rw [h, ← hw]; field_simp
      have := norm_nonneg (axisScale a⁻¹ b⁻¹ w)
      nlinarith
    · rw [axisScale_axisScale, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, axisScale_one_one]

/-- The same statement for `Geodesy.sphere 1`. -/
theorem axisScale_image_sphere {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    axisScale a b '' sphere 1 = ellipsoid a b :=
  axisScale_image_metricSphere ha hb

/-- The homeomorphism `Metric.sphere 0 1 ≃ₜ ellipsoid a b` induced by `S`. -/
noncomputable def sphereEllipsoidHomeomorph {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Metric.sphere (0 : E3) 1 ≃ₜ ellipsoid a b :=
  ((axisScaleEquiv ha hb).toHomeomorph.image (Metric.sphere (0 : E3) 1)).trans
    (Homeomorph.setCongr (axisScale_image_metricSphere ha hb))

@[simp] theorem coe_sphereEllipsoidHomeomorph {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (x : Metric.sphere (0 : E3) 1) :
    ((sphereEllipsoidHomeomorph ha hb x : ellipsoid a b) : E3) = axisScale a b x.1 := rfl

@[simp] theorem coe_sphereEllipsoidHomeomorph_symm {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (y : ellipsoid a b) :
    (((sphereEllipsoidHomeomorph ha hb).symm y : Metric.sphere (0 : E3) 1) : E3) =
      axisScale a⁻¹ b⁻¹ y.1 := rfl

/-- The homeomorphism from the unit sphere onto the surface of a reference ellipsoid. -/
noncomputable def _root_.Geodesy.ReferenceEllipsoid.sphereHomeomorph (E : ReferenceEllipsoid) :
    Metric.sphere (0 : E3) 1 ≃ₜ E.toSet :=
  sphereEllipsoidHomeomorph E.a_pos.ne' E.b_pos.ne'

@[simp] theorem _root_.Geodesy.ReferenceEllipsoid.coe_sphereHomeomorph (E : ReferenceEllipsoid)
    (x : Metric.sphere (0 : E3) 1) :
    ((E.sphereHomeomorph x : E.toSet) : E3) = axisScale E.a E.b x.1 := rfl

/-- The subtype `UnitSphere` is homeomorphic to the surface of a reference ellipsoid. -/
noncomputable def _root_.Geodesy.ReferenceEllipsoid.unitSphereHomeomorph (E : ReferenceEllipsoid) :
    UnitSphere ≃ₜ E.toSet :=
  SphereEllipsoid.unitSphereHomeomorph.trans E.sphereHomeomorph

/-! ## 4. Bi-Lipschitz bounds -/

/-- For `0 < b ≤ a`, `b ‖v‖ ≤ ‖S v‖ ≤ a ‖v‖`. -/
theorem norm_axisScale_bounds {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) (v : E3) :
    b * ‖v‖ ≤ ‖axisScale a b v‖ ∧ ‖axisScale a b v‖ ≤ a * ‖v‖ := by
  have ha : 0 < a := hb.trans_le hba
  have hv := norm_sq_eq v
  have hS := norm_axisScale_sq a b v
  have hab2 : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb.le hba 2
  have h0 : 0 ≤ v 0 ^ 2 + v 1 ^ 2 := by positivity
  have h2 : 0 ≤ v 2 ^ 2 := sq_nonneg _
  constructor
  · refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_
    rw [mul_pow, hv, hS]
    nlinarith
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, hv, hS]
    nlinarith

/-- Bi-Lipschitz bounds for `S = diag(a, a, b)` with `0 < b ≤ a`, on all of `E3`. -/
theorem dist_axisScale_bounds {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) (u v : E3) :
    b * dist u v ≤ dist (axisScale a b u) (axisScale a b v) ∧
      dist (axisScale a b u) (axisScale a b v) ≤ a * dist u v := by
  rw [dist_eq_norm, dist_eq_norm, ← axisScale_sub]
  exact norm_axisScale_bounds hb hba (u - v)

/-- The bi-Lipschitz bounds restricted to the homeomorphism onto the ellipsoid. -/
theorem dist_sphereEllipsoidHomeomorph_bounds {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (x y : Metric.sphere (0 : E3) 1) :
    b * dist x y ≤ dist (sphereEllipsoidHomeomorph (hb.trans_le hba).ne' hb.ne' x)
        (sphereEllipsoidHomeomorph (hb.trans_le hba).ne' hb.ne' y) ∧
      dist (sphereEllipsoidHomeomorph (hb.trans_le hba).ne' hb.ne' x)
        (sphereEllipsoidHomeomorph (hb.trans_le hba).ne' hb.ne' y) ≤ a * dist x y :=
  dist_axisScale_bounds hb hba x.1 y.1

/-- `S` is `a`-Lipschitz for `0 < b ≤ a`. -/
theorem lipschitzWith_axisScale {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    LipschitzWith ⟨a, (hb.trans_le hba).le⟩ (axisScale a b) :=
  LipschitzWith.of_dist_le_mul fun u v => (dist_axisScale_bounds hb hba u v).2

/-- On horizontal displacements (`u 2 = v 2`), `S` scales distances by exactly `|a|`. -/
theorem dist_axisScale_of_horizontal (a b : ℝ) {u v : E3} (h : u 2 = v 2) :
    dist (axisScale a b u) (axisScale a b v) = |a| * dist u v := by
  have key : dist (axisScale a b u) (axisScale a b v) ^ 2 = (|a| * dist u v) ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, ← axisScale_sub, norm_axisScale_sq, mul_pow, sq_abs,
      norm_sq_eq]
    simp [h]
  have := abs_nonneg a
  exact (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).mp key

/-- On vertical displacements (`u 0 = v 0`, `u 1 = v 1`), `S` scales distances by `|b|`. -/
theorem dist_axisScale_of_vertical (a b : ℝ) {u v : E3} (h0 : u 0 = v 0) (h1 : u 1 = v 1) :
    dist (axisScale a b u) (axisScale a b v) = |b| * dist u v := by
  have key : dist (axisScale a b u) (axisScale a b v) ^ 2 = (|b| * dist u v) ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, ← axisScale_sub, norm_axisScale_sq, mul_pow, sq_abs,
      norm_sq_eq]
    simp [h0, h1]
  have := abs_nonneg b
  exact (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).mp key

/-- The upper constant `a` is attained by the antipodal equator pair `(±1, 0, 0)`. -/
theorem dist_axisScale_equator {a b : ℝ} (ha : 0 < a) :
    dist (axisScale a b (vec3 1 0 0)) (axisScale a b (vec3 (-1) 0 0)) =
      a * dist (vec3 1 0 0) (vec3 (-1) 0 0) := by
  rw [dist_axisScale_of_horizontal a b (u := vec3 1 0 0) (v := vec3 (-1) 0 0) rfl, abs_of_pos ha]

/-- The lower constant `b` is attained by the pole pair `(0, 0, ±1)`. -/
theorem dist_axisScale_poles {a b : ℝ} (hb : 0 < b) :
    dist (axisScale a b (vec3 0 0 1)) (axisScale a b (vec3 0 0 (-1))) =
      b * dist (vec3 0 0 1) (vec3 0 0 (-1)) := by
  rw [dist_axisScale_of_vertical a b (u := vec3 0 0 1) (v := vec3 0 0 (-1)) rfl rfl,
    abs_of_pos hb]

private theorem vec3_sub' (x y z x' y' z' : ℝ) :
    vec3 x y z - vec3 x' y' z' = vec3 (x - x') (y - y') (z - z') := by
  ext i; fin_cases i <;> rfl

theorem vec3_mem_sphere_one {x y z : ℝ} (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    vec3 x y z ∈ Metric.sphere (0 : E3) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h1 : ‖vec3 x y z‖ ^ 2 = 1 := by rw [norm_vec3_sq, h]
  have := norm_nonneg (vec3 x y z)
  nlinarith

/-- Both endpoints of the equator pair and of the pole pair lie on the unit sphere, and the
pairs are at distance `2`. -/
theorem extremal_pairs_mem_sphere :
    vec3 1 0 0 ∈ Metric.sphere (0 : E3) 1 ∧ vec3 (-1) 0 0 ∈ Metric.sphere (0 : E3) 1 ∧
      vec3 0 0 1 ∈ Metric.sphere (0 : E3) 1 ∧ vec3 0 0 (-1) ∈ Metric.sphere (0 : E3) 1 ∧
      dist (vec3 1 0 0) (vec3 (-1) 0 0) = 2 ∧ dist (vec3 0 0 1) (vec3 0 0 (-1)) = 2 := by
  refine ⟨vec3_mem_sphere_one (by norm_num), vec3_mem_sphere_one (by norm_num),
    vec3_mem_sphere_one (by norm_num), vec3_mem_sphere_one (by norm_num), ?_, ?_⟩ <;>
  · have h : ∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 = 4 → ‖vec3 x y z‖ = 2 := fun x y z h => by
      have h1 : ‖vec3 x y z‖ ^ 2 = 2 ^ 2 := by rw [norm_vec3_sq, h]; norm_num
      exact (pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp h1
    rw [dist_eq_norm, vec3_sub']
    exact h _ _ _ (by norm_num)

/-! ## 5. Topology carried over by the homeomorphism -/

theorem one_lt_rank_E3 : 1 < Module.rank ℝ E3 := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
  norm_num

/-- The ellipsoid is compact. -/
theorem isCompact_ellipsoid {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : IsCompact (ellipsoid a b) := by
  rw [← axisScale_image_metricSphere ha hb]
  exact (isCompact_sphere 0 1).image (continuous_axisScale a b)

/-- The ellipsoid is connected. -/
theorem isConnected_ellipsoid {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsConnected (ellipsoid a b) := by
  rw [← axisScale_image_metricSphere ha hb]
  exact (isConnected_sphere one_lt_rank_E3 0 zero_le_one).image _
    (continuous_axisScale a b).continuousOn

/-- The ellipsoid is closed in `E3`. -/
theorem isClosed_ellipsoid {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : IsClosed (ellipsoid a b) :=
  (isCompact_ellipsoid ha hb).isClosed

/-- The ellipsoid is bounded. -/
theorem isBounded_ellipsoid {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Bornology.IsBounded (ellipsoid a b) :=
  (isCompact_ellipsoid ha hb).isBounded

/-- The same facts via the homeomorphism: the ellipsoid, as a subtype, is a compact connected
space. -/
theorem compactSpace_ellipsoid {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    CompactSpace (ellipsoid a b) := by
  have : CompactSpace (Metric.sphere (0 : E3) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  exact (sphereEllipsoidHomeomorph ha hb).compactSpace

theorem connectedSpace_ellipsoid {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ConnectedSpace (ellipsoid a b) := by
  have : ConnectedSpace (Metric.sphere (0 : E3) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere one_lt_rank_E3 0 zero_le_one)
  exact (sphereEllipsoidHomeomorph ha hb).surjective.connectedSpace
    (sphereEllipsoidHomeomorph ha hb).continuous

/-- A reference ellipsoid is compact, connected and closed. -/
theorem _root_.Geodesy.ReferenceEllipsoid.isCompact_toSet (E : ReferenceEllipsoid) : IsCompact E.toSet :=
  isCompact_ellipsoid E.a_pos.ne' E.b_pos.ne'

theorem _root_.Geodesy.ReferenceEllipsoid.isConnected_toSet (E : ReferenceEllipsoid) : IsConnected E.toSet :=
  isConnected_ellipsoid E.a_pos.ne' E.b_pos.ne'

theorem _root_.Geodesy.ReferenceEllipsoid.isClosed_toSet (E : ReferenceEllipsoid) : IsClosed E.toSet :=
  isClosed_ellipsoid E.a_pos.ne' E.b_pos.ne'

/-! ## 6. Linear scaling is not the geodetic correspondence -/

/-- `S` sends the unit-sphere point at latitude `β` to the ellipsoid point whose
*parametric (reduced)* latitude is `β`. -/
theorem axisScale_spherePoint (a b β lam : ℝ) :
    axisScale a b (spherePoint 1 β lam) =
      vec3 (a * cos β * cos lam) (a * cos β * sin lam) (b * sin β) := by
  rw [spherePoint, axisScale_vec3]
  refine vec3_congr ?_ ?_ ?_ <;> ring

/-- The image `S (spherePoint 1 β lam)` lies on the ellipsoid. -/
theorem axisScale_spherePoint_mem {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (β lam : ℝ) :
    axisScale a b (spherePoint 1 β lam) ∈ ellipsoid a b := by
  rw [← axisScale_image_metricSphere ha hb]
  refine Set.mem_image_of_mem _ (vec3_mem_sphere_one ?_)
  have h1 := sin_sq_add_cos_sq β
  have h2 := sin_sq_add_cos_sq lam
  linear_combination (cos β ^ 2) * h2 + h1

/-- **Counterexample.** On a flattened reference ellipsoid (`0 < f`), linear scaling does not
preserve geodetic latitude: for `0 < φ < π / 2` and every longitude, the image under
`S = diag(a, a, b)` of the unit-sphere point at latitude `φ` is *not* the ellipsoid point at
geodetic latitude `φ`. -/
theorem axisScale_spherePoint_ne_ellipsoidPoint (E : ReferenceEllipsoid) (hf : 0 < E.f)
    {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (lam : ℝ) :
    axisScale E.a E.b (spherePoint 1 φ lam) ≠ E.ellipsoidPoint φ lam := by
  intro h
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ1⟩
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith [pi_pos])
  have ha := E.a_pos
  have hb := E.b_pos
  have hba : E.b < E.a := by
    have : E.b = E.a * (1 - E.f) := rfl
    nlinarith
  rw [axisScale_spherePoint, ReferenceEllipsoid.ellipsoidPoint] at h
  have h0 := congrArg (fun v : E3 => v 0) h
  have h1 := congrArg (fun v : E3 => v 1) h
  have h2 := congrArg (fun v : E3 => v 2) h
  simp only [vec3_0, vec3_1, vec3_2] at h0 h1 h2
  set N := E.primeVerticalRadius φ
  -- The horizontal coordinates force `N = a`.
  have hN : (E.a - N) * cos φ = 0 := by
    linear_combination cos lam * h0 + sin lam * h1 - (E.a - N) * cos φ * sin_sq_add_cos_sq lam
  have hN' : N = E.a := by
    rcases mul_eq_zero.mp hN with h | h
    · linarith
    · exact absurd h hc.ne'
  -- The vertical coordinate then forces `b = a (1 - e²) = b² / a`, so `a = b`.
  rw [hN', E.one_sub_e2_eq] at h2
  have h3 : E.b * E.a = E.b ^ 2 := by
    have := mul_right_cancel₀ hs.ne' h2
    field_simp at this
    linarith
  have : E.a = E.b := by
    have := mul_left_cancel₀ hb.ne' (h3.trans (sq E.b))
    exact this
  linarith

/-- The parametric (reduced) latitude `β = arctan ((b / a) tan φ)` of geodetic latitude `φ`. -/
noncomputable def parametricLatitude (E : ReferenceEllipsoid) (φ : ℝ) : ℝ :=
  arctan (E.b / E.a * tan φ)

theorem tan_parametricLatitude (E : ReferenceEllipsoid) (φ : ℝ) :
    tan (parametricLatitude E φ) = E.b / E.a * tan φ := tan_arctan _

theorem parametricLatitude_mem_Ioo (E : ReferenceEllipsoid) (φ : ℝ) :
    parametricLatitude E φ ∈ Set.Ioo (-(π / 2)) (π / 2) :=
  ⟨neg_pi_div_two_lt_arctan _, arctan_lt_pi_div_two _⟩

/-- **The positive correspondence.** For `|φ| < π / 2`, the ellipsoid point at geodetic
latitude `φ` is the image under `S = diag(a, a, b)` of the unit-sphere point at the
parametric latitude `β`, where `tan β = (b / a) tan φ`. -/
theorem ellipsoidPoint_eq_axisScale_spherePoint (E : ReferenceEllipsoid) {φ : ℝ}
    (hφ0 : -(π / 2) < φ) (hφ1 : φ < π / 2) (lam : ℝ) :
    E.ellipsoidPoint φ lam = axisScale E.a E.b (spherePoint 1 (parametricLatitude E φ) lam) := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨hφ0, hφ1⟩
  have ha := E.a_pos
  have hb := E.b_pos
  set k := E.b / E.a with hk
  set Y := 1 + (k * tan φ) ^ 2 with hY
  have hYpos : 0 < Y := by positivity
  have hsY : 0 < √Y := Real.sqrt_pos.mpr hYpos
  have he : 1 - E.e2 = k ^ 2 := by rw [E.one_sub_e2_eq, hk, div_pow]
  have hW : 1 - E.e2 * sin φ ^ 2 = cos φ ^ 2 * Y := by
    have htan : cos φ ^ 2 * (k * tan φ) ^ 2 = k ^ 2 * sin φ ^ 2 := by
      rw [tan_eq_sin_div_cos, mul_pow, div_pow]
      field_simp
    rw [hY, mul_add, mul_one, htan, ← he]
    linear_combination -(sin_sq_add_cos_sq φ)
  have hsqrt : √(1 - E.e2 * sin φ ^ 2) = cos φ * √Y := by
    rw [hW, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le]
  rw [axisScale_spherePoint, ReferenceEllipsoid.ellipsoidPoint,
    ReferenceEllipsoid.primeVerticalRadius, hsqrt, parametricLatitude, cos_arctan, sin_arctan,
    ← hk, ← hY, he]
  have hbk : E.b = E.a * k := by rw [hk]; field_simp
  refine vec3_congr ?_ ?_ ?_
  · field_simp
  · field_simp
  · rw [hbk, tan_eq_sin_div_cos]
    field_simp

/-- The geodetic correspondence in existential form: some `β ∈ (-π/2, π/2)` with
`tan β = (b / a) tan φ` carries the unit-sphere point to the geodetic ellipsoid point. -/
theorem exists_parametricLatitude (E : ReferenceEllipsoid) {φ : ℝ}
    (hφ0 : -(π / 2) < φ) (hφ1 : φ < π / 2) (lam : ℝ) :
    ∃ β ∈ Set.Ioo (-(π / 2)) (π / 2), tan β = E.b / E.a * tan φ ∧
      E.ellipsoidPoint φ lam = axisScale E.a E.b (spherePoint 1 β lam) :=
  ⟨_, parametricLatitude_mem_Ioo E φ, tan_parametricLatitude E φ,
    ellipsoidPoint_eq_axisScale_spherePoint E hφ0 hφ1 lam⟩

/-! ### The hypotheses of the counterexample are necessary -/

/-- With zero flattening the parametric and geodetic latitudes agree, so `S` *does* carry
latitude `φ` to geodetic latitude `φ` for `|φ| < π / 2`. -/
theorem axisScale_spherePoint_eq_ellipsoidPoint_of_f_eq_zero (E : ReferenceEllipsoid)
    (hf : E.f = 0) {φ : ℝ} (hφ0 : -(π / 2) < φ) (hφ1 : φ < π / 2) (lam : ℝ) :
    axisScale E.a E.b (spherePoint 1 φ lam) = E.ellipsoidPoint φ lam := by
  have hba : E.b = E.a := (E.isSphere_tfae.out 1 2).mp hf
  have hβ : parametricLatitude E φ = φ := by
    rw [parametricLatitude, hba, div_self E.a_pos.ne', one_mul, arctan_tan hφ0 hφ1]
  rw [ellipsoidPoint_eq_axisScale_spherePoint E hφ0 hφ1, hβ]

/-- On the equator (`φ = 0`) `S` agrees with the geodetic point, whatever the flattening. -/
theorem axisScale_spherePoint_zero_eq_ellipsoidPoint (E : ReferenceEllipsoid) (lam : ℝ) :
    axisScale E.a E.b (spherePoint 1 0 lam) = E.ellipsoidPoint 0 lam := by
  rw [axisScale_spherePoint, ReferenceEllipsoid.ellipsoidPoint, E.primeVerticalRadius_zero]
  simp

/-- At the north pole (`φ = π / 2`) `S` agrees with the geodetic point, whatever the
flattening: both are `(0, 0, b)`. -/
theorem axisScale_spherePoint_pi_div_two_eq_ellipsoidPoint (E : ReferenceEllipsoid) (lam : ℝ) :
    axisScale E.a E.b (spherePoint 1 (π / 2) lam) = E.ellipsoidPoint (π / 2) lam := by
  rw [axisScale_spherePoint, ReferenceEllipsoid.ellipsoidPoint,
    E.primeVerticalRadius_pi_div_two, E.one_sub_e2_eq]
  simp only [cos_pi_div_two, sin_pi_div_two, mul_zero, zero_mul, mul_one]
  refine vec3_congr rfl rfl ?_
  have := E.a_pos.ne'
  have := E.b_pos.ne'
  field_simp

/-! ## Examples -/

/-- The ellipsoid with radii `2` and `1` is compact and connected. -/
example : IsCompact (ellipsoid 2 1) ∧ IsConnected (ellipsoid 2 1) :=
  ⟨isCompact_ellipsoid two_ne_zero one_ne_zero, isConnected_ellipsoid two_ne_zero one_ne_zero⟩

/-- On the unit sphere, doubling the radius doubles the chord between the poles. -/
example : dist (sphereScale (R := 2) two_pos ⟨vec3 0 0 1, vec3_mem_sphere_one (by norm_num)⟩)
      (sphereScale two_pos ⟨vec3 0 0 (-1), vec3_mem_sphere_one (by norm_num)⟩) = 2 * 2 := by
  rw [dist_sphereScale, Subtype.dist_eq]
  simp only
  rw [extremal_pairs_mem_sphere.2.2.2.2.2]

end Geodesy.SphereEllipsoid
