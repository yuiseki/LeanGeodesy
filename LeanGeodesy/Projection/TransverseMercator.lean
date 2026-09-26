import LeanGeodesy.Projection.Cylindrical
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Transverse Mercator on the sphere

Mercator's projection is true to scale along the equator and distorts more
and more away from it. Turning the sphere a quarter turn, so that a chosen
meridian plays the role of the equator, gives a projection that is true to
scale along that central meridian instead: the transverse Mercator
projection, the basis of UTM and of most national grids.

With `B = cos φ sin λ`, the sine of the angular distance from the central
meridian `λ = 0`, the transverse Mercator projection of the sphere of radius
`R` is

```
x = R · mercatorY (arcsin B) = R artanh B,
y = R arctan (tan φ / cos λ)                       (tmX, tmY)
```

for `|φ| < π/2` and `|λ| < π/2`. The easting is the Mercator northing of the
turned sphere. On the central meridian the easting is zero and the northing
is `R φ`, the distance along the meridian (`tmX_central`, `tmY_central`).

The partial derivatives are (`hasDerivAt_tmX_lat`, `hasDerivAt_tmX_lon`,
`hasDerivAt_tmY_lat`, `hasDerivAt_tmY_lon`)

```
∂(x, y)/∂φ = R / (1 - B²) · (-sin φ sin λ, cos λ)
∂(x, y)/∂λ = R cos φ / (1 - B²) · (cos λ, sin φ sin λ)
```
-/

namespace Geodesy.Projection

open Real

/-- `cos φ sin λ`: the sine of the angular distance from the central meridian. -/
noncomputable def tmB (φ lam : ℝ) : ℝ := cos φ * sin lam

/-- The easting of the transverse Mercator projection of the sphere of radius `R`. -/
noncomputable def tmX (R φ lam : ℝ) : ℝ := R * mercatorY (arcsin (tmB φ lam))

/-- The northing of the transverse Mercator projection of the sphere of radius `R`. -/
noncomputable def tmY (R φ lam : ℝ) : ℝ := R * arctan (tan φ / cos lam)

/-- On the central meridian the easting is zero. -/
theorem tmX_central (R φ : ℝ) : tmX R φ 0 = 0 := by simp [tmX, tmB]

/-- On the central meridian the northing is the distance along the meridian:
the projection is true to scale there. -/
theorem tmY_central (R : ℝ) {φ : ℝ} (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) : tmY R φ 0 = R * φ := by
  simp [tmY, arctan_tan hφ.1 hφ.2]

/-- On the equator the northing is zero. -/
theorem tmY_equator (R lam : ℝ) : tmY R 0 lam = 0 := by simp [tmY]

/-- Off the meridians a quarter turn away, `B² < 1`. -/
theorem tmB_sq_lt_one (φ : ℝ) {lam : ℝ} (hl : 0 < cos lam) : tmB φ lam ^ 2 < 1 := by
  unfold tmB
  have h1 := sin_sq_add_cos_sq φ
  have h2 := sin_sq_add_cos_sq lam
  have : cos φ ^ 2 * sin lam ^ 2 < 1 := by
    have hs : sin lam ^ 2 < 1 := by nlinarith
    have hc : cos φ ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (cos φ), sq_nonneg (sin lam)]
  nlinarith

/-- `d/dB mercatorY (arcsin B) = 1 / (1 - B²)`: the easting grows like `artanh`. -/
theorem hasDerivAt_mercatorY_arcsin {B : ℝ} (hB : B ^ 2 < 1) :
    HasDerivAt (fun B => mercatorY (arcsin B)) (1 / (1 - B ^ 2)) B := by
  have h1 : 0 < 1 - B ^ 2 := by linarith
  have hs : 0 < √(1 - B ^ 2) := sqrt_pos.mpr h1
  have hc : 0 < cos (arcsin B) := by rw [cos_arcsin]; exact hs
  have hB1 : B ≠ -1 := fun h => by rw [h] at hB; norm_num at hB
  have hB2 : B ≠ 1 := fun h => by rw [h] at hB; norm_num at hB
  have h := (hasDerivAt_mercatorY hc).comp B (hasDerivAt_arcsin hB1 hB2)
  rw [cos_arcsin] at h
  convert h using 1
  field_simp

theorem hasDerivAt_tmB_lat (φ lam : ℝ) :
    HasDerivAt (fun φ => tmB φ lam) (-sin φ * sin lam) φ := by
  unfold tmB
  simpa using (hasDerivAt_cos φ).mul_const (sin lam)

theorem hasDerivAt_tmB_lon (φ lam : ℝ) :
    HasDerivAt (fun lam => tmB φ lam) (cos φ * cos lam) lam := by
  unfold tmB
  exact (hasDerivAt_sin lam).const_mul (cos φ)

variable (R : ℝ) {φ lam : ℝ}

theorem hasDerivAt_tmX_lat (hl : 0 < cos lam) :
    HasDerivAt (fun φ => tmX R φ lam) (R * (-sin φ * sin lam) / (1 - tmB φ lam ^ 2)) φ := by
  have h := ((hasDerivAt_mercatorY_arcsin (tmB_sq_lt_one φ hl)).comp φ
    (hasDerivAt_tmB_lat φ lam)).const_mul R
  unfold tmX
  convert h using 1
  ring

theorem hasDerivAt_tmX_lon (hl : 0 < cos lam) :
    HasDerivAt (fun lam => tmX R φ lam) (R * (cos φ * cos lam) / (1 - tmB φ lam ^ 2)) lam := by
  have h := ((hasDerivAt_mercatorY_arcsin (tmB_sq_lt_one φ hl)).comp lam
    (hasDerivAt_tmB_lon φ lam)).const_mul R
  unfold tmX
  convert h using 1
  ring

/-- `1 - B² = cos² φ cos² λ + sin² φ`. -/
theorem one_sub_tmB_sq (φ lam : ℝ) :
    1 - tmB φ lam ^ 2 = cos φ ^ 2 * cos lam ^ 2 + sin φ ^ 2 := by
  unfold tmB
  have h1 := sin_sq_add_cos_sq φ
  have h2 := sin_sq_add_cos_sq lam
  linear_combination (-1 : ℝ) * h1 - cos φ ^ 2 * h2

theorem hasDerivAt_tmY_lat (hφ : 0 < cos φ) (hl : 0 < cos lam) :
    HasDerivAt (fun φ => tmY R φ lam) (R * cos lam / (1 - tmB φ lam ^ 2)) φ := by
  have hu : HasDerivAt (fun φ => tan φ / cos lam) (1 / cos φ ^ 2 / cos lam) φ :=
    (hasDerivAt_tan hφ.ne').div_const _
  have h := ((hasDerivAt_arctan (tan φ / cos lam)).comp φ hu).const_mul R
  unfold tmY
  convert h using 1
  have hB := tmB_sq_lt_one φ hl
  have hD : 0 < 1 - tmB φ lam ^ 2 := by linarith
  rw [one_sub_tmB_sq] at hD ⊢
  rw [tan_eq_sin_div_cos]
  field_simp
  ring

theorem hasDerivAt_tmY_lon (hφ : 0 < cos φ) (hl : 0 < cos lam) :
    HasDerivAt (fun lam => tmY R φ lam)
      (R * (sin φ * cos φ * sin lam) / (1 - tmB φ lam ^ 2)) lam := by
  have hu : HasDerivAt (fun lam => tan φ / cos lam) ((0 * cos lam - tan φ * -sin lam) / cos lam ^ 2)
      lam := (hasDerivAt_const lam (tan φ)).div (hasDerivAt_cos lam) hl.ne'
  have h := ((hasDerivAt_arctan (tan φ / cos lam)).comp lam hu).const_mul R
  unfold tmY
  convert h using 1
  have hB := tmB_sq_lt_one φ hl
  have hD : 0 < 1 - tmB φ lam ^ 2 := by linarith
  rw [one_sub_tmB_sq] at hD ⊢
  rw [tan_eq_sin_div_cos]
  field_simp
  ring

end Geodesy.Projection
