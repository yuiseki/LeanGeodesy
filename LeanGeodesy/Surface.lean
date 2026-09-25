import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Spheres and ellipsoids of revolution

Geodesy models the Earth by a surface in three-dimensional space with its
centre at the origin and its axis of rotation along `z`.

The simplest model is a sphere of radius `R`. A better one is an *ellipsoid
of revolution* (a spheroid): the ellipse `p² / a² + z² / b² = 1` in a
meridian plane, spun about the `z` axis. Here `a` is the equatorial radius
and `b` the polar radius; the Earth is flattened at the poles, so `b < a`.
In coordinates:

```
(x² + y²) / a² + z² / b² = 1
```

With `a = b` this is the sphere of radius `a` (`ellipsoid_self`).
-/

namespace Geodesy

open Real

/-- Three-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A vector from its three coordinates. -/
noncomputable def vec3 (x y z : ℝ) : E3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![x, y, z]

@[simp] theorem vec3_0 (x y z : ℝ) : vec3 x y z 0 = x := rfl
@[simp] theorem vec3_1 (x y z : ℝ) : vec3 x y z 1 = y := rfl
@[simp] theorem vec3_2 (x y z : ℝ) : vec3 x y z 2 = z := rfl

theorem vec3_eta (v : E3) : vec3 (v 0) (v 1) (v 2) = v := by
  ext i
  fin_cases i <;> rfl

/-- Two vectors are equal when their coordinates are. -/
theorem vec3_congr {x y z x' y' z' : ℝ} (hx : x = x') (hy : y = y') (hz : z = z') :
    vec3 x y z = vec3 x' y' z' := by
  rw [hx, hy, hz]

theorem vec3_add (x y z x' y' z' : ℝ) :
    vec3 x y z + vec3 x' y' z' = vec3 (x + x') (y + y') (z + z') := by
  ext i
  fin_cases i <;> rfl

theorem vec3_smul (c x y z : ℝ) : c • vec3 x y z = vec3 (c * x) (c * y) (c * z) := by
  ext i
  fin_cases i <;> rfl

/-- The squared length of a vector is the sum of its squared coordinates. -/
theorem norm_sq_eq (v : E3) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The sphere of radius `R` about the origin. -/
def sphere (R : ℝ) : Set E3 := Metric.sphere 0 R

/-- The ellipsoid of revolution with equatorial radius `a` and polar radius
`b`. -/
def ellipsoid (a b : ℝ) : Set E3 := {v | (v 0 ^ 2 + v 1 ^ 2) / a ^ 2 + v 2 ^ 2 / b ^ 2 = 1}

theorem mem_ellipsoid {a b : ℝ} {v : E3} :
    v ∈ ellipsoid a b ↔ (v 0 ^ 2 + v 1 ^ 2) / a ^ 2 + v 2 ^ 2 / b ^ 2 = 1 := Iff.rfl

/-- An ellipsoid with equal radii is a sphere. -/
theorem ellipsoid_self {R : ℝ} (hR : 0 < R) : ellipsoid R R = sphere R := by
  ext v
  rw [mem_ellipsoid, sphere, Metric.mem_sphere, dist_zero_right]
  have hR2 : R ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    have hs : ‖v‖ ^ 2 = R ^ 2 := by
      rw [norm_sq_eq]
      field_simp at h
      linarith
    nlinarith [norm_nonneg v]
  · intro h
    have hs := norm_sq_eq v
    rw [h] at hs
    field_simp
    linarith

/-- The equator is a circle of radius `a`. -/
theorem equator_mem {a b : ℝ} (ha : a ≠ 0) (lon : ℝ) :
    vec3 (a * cos lon) (a * sin lon) 0 ∈ ellipsoid a b := by
  rw [mem_ellipsoid]
  simp only [vec3_0, vec3_1, vec3_2]
  have := sin_sq_add_cos_sq lon
  field_simp
  nlinarith

/-- The poles are at distance `b` from the centre. -/
theorem northPole_mem {a b : ℝ} (hb : b ≠ 0) : vec3 0 0 b ∈ ellipsoid a b := by
  rw [mem_ellipsoid]
  simp [hb]

theorem southPole_mem {a b : ℝ} (hb : b ≠ 0) : vec3 0 0 (-b) ∈ ellipsoid a b := by
  rw [mem_ellipsoid]
  simp [hb]

/-! ## Coordinates, inner products and derivatives -/

theorem norm_vec3_sq (x y z : ℝ) : ‖vec3 x y z‖ ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
  rw [norm_sq_eq]
  simp

theorem inner_vec3 (x y z x' y' z' : ℝ) :
    inner (vec3 x y z) (vec3 x' y' z') = x * x' + y * y' + z * z' := by
  simp [vec3, PiLp.inner_apply, Fin.sum_univ_three]

/-- A curve in space is differentiated coordinate by coordinate. -/
theorem hasDerivAt_vec3 {f g h : ℝ → ℝ} {f' g' h' t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) (hh : HasDerivAt h h' t) :
    HasDerivAt (fun s => vec3 (f s) (g s) (h s)) (vec3 f' g' h') t := by
  have hp : HasDerivAt (fun s => ![f s, g s, h s]) ![f', g', h'] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i <;> simpa
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp

end Geodesy
