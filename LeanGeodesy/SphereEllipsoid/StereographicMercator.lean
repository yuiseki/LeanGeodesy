import LeanGeodesy.Projection.Stereographic

/-!
# Polar stereographic in terms of the Mercator ordinate

On the sphere of radius `R`, the north-polar stereographic projection and the Mercator
projection are tied by one identity: the stereographic radius is `2 R e^(-y)`, where
`y = mercatorY φ = arsinh (tan φ)` is the Mercator ordinate. This file proves it for
`-π/2 < φ < π/2`, from

```
exp (arsinh (tan φ)) = (1 + sin φ) / cos φ      (exp_mercatorY)
```

What is proved: `exp_mercatorY`, `exp_neg_mercatorY`, `stereographicFactor_eq_two_exp_neg`
and `stereographic_eq_mercator` (all on the open latitude interval).

What is not proved: the ellipsoidal versions of either projection. The hypothesis
`φ < π / 2` cannot be dropped: at the north pole Mathlib's junk value `tan (π / 2) = 0` gives
`mercatorY (π / 2) = 0`, so the right-hand side is the point `(2R, 0)` at `lam = 0` while the
projection is the origin (`stereographic_eq_mercator_fails_at_northPole`).
-/

namespace Geodesy.SphereEllipsoid

open Real Geodesy.Projection

/-- `exp (mercatorY φ) = (1 + sin φ) / cos φ` for `-π/2 < φ < π/2`. -/
theorem exp_mercatorY {φ : ℝ} (hφ0 : -(π / 2) < φ) (hφ1 : φ < π / 2) :
    exp (mercatorY φ) = (1 + sin φ) / cos φ := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨hφ0, hφ1⟩
  have h1 : 1 + tan φ ^ 2 = (1 / cos φ) ^ 2 := by
    rw [tan_eq_sin_div_cos]
    field_simp
    linear_combination sin_sq_add_cos_sq φ
  rw [mercatorY, exp_arsinh, h1, Real.sqrt_sq (by positivity), tan_eq_sin_div_cos]
  field_simp
  ring

/-- `exp (-(mercatorY φ)) = cos φ / (1 + sin φ)` for `-π/2 < φ < π/2`. -/
theorem exp_neg_mercatorY {φ : ℝ} (hφ0 : -(π / 2) < φ) (hφ1 : φ < π / 2) :
    exp (-(mercatorY φ)) = cos φ / (1 + sin φ) := by
  rw [exp_neg, exp_mercatorY hφ0 hφ1, inv_div]

/-- The stereographic radial factor is `2 e^(-y)` with `y` the Mercator ordinate. -/
theorem stereographicFactor_eq_two_exp_neg {φ : ℝ} (hφ0 : -(π / 2) < φ) (hφ1 : φ < π / 2) :
    stereographicFactor φ = 2 * exp (-(mercatorY φ)) := by
  rw [exp_neg_mercatorY hφ0 hφ1, stereographicFactor, mul_div_assoc]

/-- **Polar stereographic from Mercator.** For `-π/2 < φ < π/2`,
`stereographic R φ lam = (2 R e^(-y) cos lam, 2 R e^(-y) sin lam)` with `y = mercatorY φ`. -/
theorem stereographic_eq_mercator (R : ℝ) {φ : ℝ} (hφ0 : -(π / 2) < φ) (hφ1 : φ < π / 2)
    (lam : ℝ) :
    stereographic R φ lam =
      vec2 (2 * R * exp (-(mercatorY φ)) * cos lam) (2 * R * exp (-(mercatorY φ)) * sin lam) := by
  rw [stereographic, stereographicFactor_eq_two_exp_neg hφ0 hφ1]
  congr 1 <;> ring

/-- **Counterexample at the pole.** For `R ≠ 0` the identity fails at `φ = π / 2`: the
stereographic image of the pole is the origin, but `mercatorY (π / 2) = 0` (junk value). -/
theorem stereographic_eq_mercator_fails_at_northPole {R : ℝ} (hR : R ≠ 0) :
    stereographic R (π / 2) 0 ≠
      vec2 (2 * R * exp (-(mercatorY (π / 2))) * cos 0)
        (2 * R * exp (-(mercatorY (π / 2))) * sin 0) := by
  rw [stereographic_northPole, mercatorY, tan_pi_div_two, arsinh_zero, neg_zero, exp_zero,
    cos_zero, sin_zero]
  intro h
  have := congrArg (fun v : E2 => v 0) h
  simp [vec2] at this
  exact hR this

end Geodesy.SphereEllipsoid
