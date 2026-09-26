import LeanGeodesy.Projection.Cylindrical

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

end Geodesy.Projection
