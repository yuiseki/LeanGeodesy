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

end Geodesy

end
