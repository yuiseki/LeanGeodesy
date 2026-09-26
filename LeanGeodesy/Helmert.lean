import LeanGeodesy.Surface
import Mathlib.LinearAlgebra.Determinant

/-!
# Helmert transformations

Two geodetic reference frames, say two realisations of WGS 84 or ITRF, put
the Earth's centre and axes in slightly different places and may disagree
slightly on the metre. The ECEF positions of one point in the two frames are
then related by a Helmert transformation

```
x' = t + s · R x
```

with a translation `t`, a scale factor `s > 0` (in practice `1 + ` a few parts
per billion) and a rotation `R`. The seven parameters of the usual
"seven-parameter transformation" are the three of `t`, the one of `s` and
three angles for `R`.

This file defines Helmert transformations as similarities of space and
proves that

- they multiply all distances by `s` (`dist_apply`), so they keep shapes
  and angles and change only size, position and orientation;
- composing two gives a Helmert transformation (`comp`, `comp_apply`), and
  each has an inverse that is one (`inv`, `inv_apply`, `apply_inv`).

In practice the rotation angles are tiny, milliarcseconds, and published
transformations use the linearised rotation `v ↦ v + r × v` with `r` the
vector of the three angles (`smallRotation`). That is not a rotation: it
stretches `v` by exactly `‖r × v‖` in quadrature,

```
‖v + r × v‖² = ‖v‖² + ‖r × v‖²          (norm_smallRotation_sq)
```

so it keeps lengths only along the axis `r` (`norm_smallRotation_eq_iff`),
and it stretches by at most `‖r‖² ‖v‖ / 2` (`norm_smallRotation_le`). For
angles up to a microradian (0.2 arcseconds) and points within 7000 km of
the centre, that is at most 3.5 micrometres (`smallRotation_error_small`),
which is why the linearisation is harmless.
-/

noncomputable section

namespace Geodesy

/-- A rotation of space: a linear isometry with determinant one. -/
structure Rotation where
  toIso : E3 ≃ₗᵢ[ℝ] E3
  det_eq_one : LinearMap.det (toIso.toLinearEquiv : E3 →ₗ[ℝ] E3) = 1

namespace Rotation

instance : CoeFun Rotation (fun _ => E3 → E3) := ⟨fun R => R.toIso⟩

/-- Doing nothing. -/
def id : Rotation := ⟨LinearIsometryEquiv.refl ℝ E3, LinearMap.det_id⟩

/-- Rotating by `R₁` and then by `R₂`. -/
def trans (R₁ R₂ : Rotation) : Rotation :=
  ⟨R₁.toIso.trans R₂.toIso, by
    have h := LinearMap.det_comp (R₂.toIso.toLinearEquiv : E3 →ₗ[ℝ] E3)
      (R₁.toIso.toLinearEquiv : E3 →ₗ[ℝ] E3)
    rw [R₁.det_eq_one, R₂.det_eq_one, mul_one] at h
    exact h⟩

/-- Rotating back. -/
def symm (R : Rotation) : Rotation :=
  ⟨R.toIso.symm, by
    have h := LinearMap.det_comp (R.toIso.toLinearEquiv : E3 →ₗ[ℝ] E3)
      (R.toIso.symm.toLinearEquiv : E3 →ₗ[ℝ] E3)
    have hid : (R.toIso.toLinearEquiv : E3 →ₗ[ℝ] E3) ∘ₗ
        (R.toIso.symm.toLinearEquiv : E3 →ₗ[ℝ] E3) = LinearMap.id := by
      ext v; simp
    rw [hid, LinearMap.det_id, R.det_eq_one, one_mul] at h
    exact h.symm⟩

@[simp] theorem trans_apply (R₁ R₂ : Rotation) (v : E3) : R₁.trans R₂ v = R₂ (R₁ v) := rfl
@[simp] theorem symm_apply_apply (R : Rotation) (v : E3) : R.symm (R v) = v := R.toIso.symm_apply_apply v
@[simp] theorem apply_symm_apply (R : Rotation) (v : E3) : R (R.symm v) = v := R.toIso.apply_symm_apply v

theorem map_add (R : Rotation) (u v : E3) : R (u + v) = R u + R v := R.toIso.map_add u v
theorem map_smul (R : Rotation) (c : ℝ) (v : E3) : R (c • v) = c • R v := R.toIso.map_smul c v
theorem map_neg (R : Rotation) (v : E3) : R (-v) = -R v := R.toIso.map_neg v
theorem dist_map (R : Rotation) (u v : E3) : dist (R u) (R v) = dist u v := R.toIso.dist_map u v

end Rotation

/-- A Helmert transformation `x ↦ t + s · R x`. -/
structure Helmert where
  translation : E3
  scale : ℝ
  scale_pos : 0 < scale
  rotation : Rotation

namespace Helmert

variable (H H₁ H₂ : Helmert)

/-- Applying the transformation to a position. -/
def apply (x : E3) : E3 := H.translation + H.scale • H.rotation x

/-- A Helmert transformation multiplies every distance by its scale. -/
theorem dist_apply (x y : E3) : dist (H.apply x) (H.apply y) = H.scale * dist x y := by
  simp only [apply, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos H.scale_pos,
    Rotation.dist_map]

/-- The identity. -/
def id : Helmert := ⟨0, 1, one_pos, Rotation.id⟩

@[simp] theorem id_apply (x : E3) : id.apply x = x := by
  simp [apply, id, Rotation.id]

/-- `H₁` followed by `H₂`. -/
def comp : Helmert :=
  ⟨H₂.translation + H₂.scale • H₂.rotation H₁.translation, H₂.scale * H₁.scale,
    mul_pos H₂.scale_pos H₁.scale_pos, H₁.rotation.trans H₂.rotation⟩

/-- Doing `H₁` and then `H₂` is the Helmert transformation `comp H₁ H₂`. -/
theorem comp_apply (x : E3) : (comp H₁ H₂).apply x = H₂.apply (H₁.apply x) := by
  simp only [apply, comp, Rotation.trans_apply, Rotation.map_add, Rotation.map_smul, smul_add,
    smul_smul, add_assoc]

/-- The inverse transformation. -/
def inv : Helmert :=
  ⟨-(H.scale⁻¹ • H.rotation.symm H.translation), H.scale⁻¹, inv_pos.mpr H.scale_pos,
    H.rotation.symm⟩

theorem inv_apply (x : E3) : H.inv.apply (H.apply x) = x := by
  have hs := H.scale_pos.ne'
  simp only [apply, inv, Rotation.map_add, Rotation.map_smul, Rotation.symm_apply_apply, smul_add,
    smul_smul, inv_mul_cancel₀ hs, one_smul]
  abel

theorem apply_inv (x : E3) : H.apply (H.inv.apply x) = x := by
  have hs := H.scale_pos.ne'
  simp only [apply, inv, Rotation.map_add, Rotation.map_smul, Rotation.map_neg,
    Rotation.apply_symm_apply, smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hs, one_smul]
  abel

end Helmert

/-! ## The linearised rotation -/

/-- The cross product `r × v`. -/
def cross (r v : E3) : E3 :=
  vec3 (r 1 * v 2 - r 2 * v 1) (r 2 * v 0 - r 0 * v 2) (r 0 * v 1 - r 1 * v 0)

/-- The linearised rotation by the small angles `r`: `v + r × v`. -/
def smallRotation (r v : E3) : E3 := v + cross r v

theorem inner_eq_components (u v : E3) : (inner u v : ℝ) = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  rw [← vec3_eta u, ← vec3_eta v]
  simp only [vec3, PiLp.inner_apply, Fin.sum_univ_three]
  simp

/-- `r × v` is perpendicular to `v`. -/
theorem inner_cross_right (r v : E3) : (inner v (cross r v) : ℝ) = 0 := by
  rw [inner_eq_components, cross]
  simp only [vec3_0, vec3_1, vec3_2]
  ring

/-- Lagrange's identity: `‖r × v‖² = ‖r‖² ‖v‖² - ⟪r, v⟫²`. -/
theorem norm_cross_sq (r v : E3) :
    ‖cross r v‖ ^ 2 = ‖r‖ ^ 2 * ‖v‖ ^ 2 - (inner r v : ℝ) ^ 2 := by
  rw [norm_sq_eq, norm_sq_eq, norm_sq_eq, inner_eq_components, cross]
  simp only [vec3_0, vec3_1, vec3_2]
  ring

/-- The linearised rotation stretches `v` by `r × v` in quadrature. -/
theorem norm_smallRotation_sq (r v : E3) :
    ‖smallRotation r v‖ ^ 2 = ‖v‖ ^ 2 + ‖cross r v‖ ^ 2 := by
  rw [smallRotation, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_add_right, inner_cross_right, real_inner_comm v (cross r v), inner_cross_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

/-- It keeps the length of `v` only when `r × v = 0`, that is, along the axis. -/
theorem norm_smallRotation_eq_iff (r v : E3) :
    ‖smallRotation r v‖ = ‖v‖ ↔ cross r v = 0 := by
  have h := norm_smallRotation_sq r v
  constructor
  · intro he
    rw [he] at h
    have : ‖cross r v‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  · intro hc
    rw [hc, norm_zero] at h
    have := norm_nonneg (smallRotation r v)
    nlinarith [norm_nonneg v]

/-- The stretch is second order in the angles: at most `‖r‖² ‖v‖ / 2`. -/
theorem norm_smallRotation_le (r v : E3) :
    ‖v‖ ≤ ‖smallRotation r v‖ ∧ ‖smallRotation r v‖ ≤ ‖v‖ + ‖r‖ ^ 2 * ‖v‖ / 2 := by
  have h := norm_smallRotation_sq r v
  have hc := norm_cross_sq r v
  have hv := norm_nonneg v
  have hr := norm_nonneg r
  have hm := norm_nonneg (smallRotation r v)
  constructor
  · nlinarith [sq_nonneg ‖cross r v‖]
  · -- `‖v‖² + ‖r‖²‖v‖² ≤ (‖v‖ + ‖r‖²‖v‖/2)²`.
    have hle : ‖smallRotation r v‖ ^ 2 ≤ (‖v‖ + ‖r‖ ^ 2 * ‖v‖ / 2) ^ 2 := by
      nlinarith [sq_nonneg (inner r v : ℝ), sq_nonneg (‖r‖ ^ 2 * ‖v‖ / 2), mul_nonneg hv hr]
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hle

/-- For angles up to a microradian and points within 7000 km of the centre,
the linearised rotation changes lengths by at most 3.5 micrometres. -/
theorem smallRotation_error_small {r v : E3} (hr : ‖r‖ ≤ 1e-6) (hv : ‖v‖ ≤ 7e6) :
    ‖smallRotation r v‖ - ‖v‖ ≤ 3.5e-6 := by
  have h := (norm_smallRotation_le r v).2
  have hr0 := norm_nonneg r
  have hv0 := norm_nonneg v
  have hr2 : ‖r‖ ^ 2 ≤ 1e-12 := by nlinarith
  nlinarith [mul_le_mul hr2 hv (norm_nonneg v) (by norm_num)]

end Geodesy

end
