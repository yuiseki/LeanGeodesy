import LeanGeodesy.Projection.Cylindrical
import LeanGeodesy.Angle
import Mathlib.Analysis.Real.Pi.Bounds
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

They are perpendicular, and both scales equal `1 / √(1 - B²)`
(`tm_h`, `tm_k`), so the projection is conformal (`tm_isConformal`). Its
scale factor depends only on the distance from the central meridian: it is
`1` on the central meridian (`tmScale_central`) and grows away from it
(`one_lt_tmScale`), exactly as Mercator's grows away from the equator.

UTM uses the transverse Mercator projection in zones 6° wide and multiplies
it by `k₀ = 0.9996` (`utmScale`), so that the scale is a little too small on
the central meridian and exactly right on two lines on either side of it
(`utmScale_equator_eq_one_iff`). On the sphere this keeps the scale within
`[0.9996, 1.00098)` across a whole zone (`utmScale_bounds`): distances on
the grid are within 0.1 % of distances on the sphere.
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
  convert h using 1 <;> try rfl
  field_simp
  exact sq_sqrt h1.le

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
  convert h using 1 <;> try rfl
  ring

theorem hasDerivAt_tmX_lon (hl : 0 < cos lam) :
    HasDerivAt (fun lam => tmX R φ lam) (R * (cos φ * cos lam) / (1 - tmB φ lam ^ 2)) lam := by
  have h := ((hasDerivAt_mercatorY_arcsin (tmB_sq_lt_one φ hl)).comp lam
    (hasDerivAt_tmB_lon φ lam)).const_mul R
  unfold tmX
  convert h using 1 <;> try rfl
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
  convert h using 1 <;> try rfl
  have hB := tmB_sq_lt_one φ hl
  have hD : 0 < 1 - tmB φ lam ^ 2 := by linarith
  rw [one_sub_tmB_sq] at hD ⊢
  rw [tan_eq_sin_div_cos]
  field_simp

theorem hasDerivAt_tmY_lon (hφ : 0 < cos φ) (hl : 0 < cos lam) :
    HasDerivAt (fun lam => tmY R φ lam)
      (R * (sin φ * cos φ * sin lam) / (1 - tmB φ lam ^ 2)) lam := by
  have hu : HasDerivAt (fun lam => tan φ / cos lam) ((0 * cos lam - tan φ * -sin lam) / cos lam ^ 2)
      lam := (hasDerivAt_const lam (tan φ)).div (hasDerivAt_cos lam) hl.ne'
  have h := ((hasDerivAt_arctan (tan φ / cos lam)).comp lam hu).const_mul R
  unfold tmY
  convert h using 1 <;> try rfl
  have hB := tmB_sq_lt_one φ hl
  have hD : 0 < 1 - tmB φ lam ^ 2 := by linarith
  rw [one_sub_tmB_sq] at hD ⊢
  rw [tan_eq_sin_div_cos]
  field_simp
  ring

/-! ## Conformality and scale -/

/-- The scale factor of the transverse Mercator projection: `1 / √(1 - B²)`. -/
noncomputable def tmScale (φ lam : ℝ) : ℝ := 1 / √(1 - tmB φ lam ^ 2)

/-- The partial derivatives of the transverse Mercator projection as a local
distortion on the sphere of radius `R`. -/
noncomputable def tmDistortion (hR : 0 < R) (hφ : 0 < cos φ) (_hl : 0 < cos lam) : LocalDistortion :=
  ⟨R, R * cos φ, hR, mul_pos hR hφ,
    vec2 (R * (-sin φ * sin lam) / (1 - tmB φ lam ^ 2)) (R * cos lam / (1 - tmB φ lam ^ 2)),
    vec2 (R * (cos φ * cos lam) / (1 - tmB φ lam ^ 2))
      (R * (sin φ * cos φ * sin lam) / (1 - tmB φ lam ^ 2))⟩

section Conformal

variable {R} (hR : 0 < R) (hφ : 0 < cos φ) (hl : 0 < cos lam)
include hR hφ hl

theorem tm_orthogonal :
    (inner ℝ (tmDistortion R hR hφ hl).dLat (tmDistortion R hR hφ hl).dLon : ℝ) = 0 := by
  simp only [tmDistortion, inner_vec2]
  ring

theorem tm_h : (tmDistortion R hR hφ hl).h = tmScale φ lam := by
  have hB := tmB_sq_lt_one φ hl
  have hD : 0 < 1 - tmB φ lam ^ 2 := by linarith
  have hsq : ‖(tmDistortion R hR hφ hl).dLat‖ ^ 2 = R ^ 2 / (1 - tmB φ lam ^ 2) := by
    simp only [tmDistortion, norm_vec2_sq]
    have e : sin φ ^ 2 * sin lam ^ 2 + cos lam ^ 2 = 1 - tmB φ lam ^ 2 := by
      rw [one_sub_tmB_sq]
      have h1 := sin_sq_add_cos_sq φ
      have h2 := sin_sq_add_cos_sq lam
      linear_combination sin φ ^ 2 * h2 - cos lam ^ 2 * h1
    field_simp
    rw [← e]
  have hn : ‖(tmDistortion R hR hφ hl).dLat‖ = R / √(1 - tmB φ lam ^ 2) := by
    rw [← sqrt_sq (norm_nonneg _), hsq, sqrt_div' _ hD.le, sqrt_sq hR.le]
  rw [LocalDistortion.h, hn, tmScale]
  simp only [tmDistortion]
  field_simp

theorem tm_k : (tmDistortion R hR hφ hl).k = tmScale φ lam := by
  have hB := tmB_sq_lt_one φ hl
  have hD : 0 < 1 - tmB φ lam ^ 2 := by linarith
  have hsq : ‖(tmDistortion R hR hφ hl).dLon‖ ^ 2 =
      (R * cos φ) ^ 2 / (1 - tmB φ lam ^ 2) := by
    simp only [tmDistortion, norm_vec2_sq]
    have e : cos lam ^ 2 + sin φ ^ 2 * sin lam ^ 2 = 1 - tmB φ lam ^ 2 := by
      rw [one_sub_tmB_sq]
      have h1 := sin_sq_add_cos_sq φ
      have h2 := sin_sq_add_cos_sq lam
      linear_combination sin φ ^ 2 * h2 - cos lam ^ 2 * h1
    field_simp
    rw [← e]
  have hRc : 0 < R * cos φ := mul_pos hR hφ
  have hn : ‖(tmDistortion R hR hφ hl).dLon‖ = R * cos φ / √(1 - tmB φ lam ^ 2) := by
    rw [← sqrt_sq (norm_nonneg _), hsq, sqrt_div' _ hD.le, sqrt_sq hRc.le]
  rw [LocalDistortion.k, hn, tmScale]
  simp only [tmDistortion]
  field_simp

/-- The transverse Mercator projection of the sphere is conformal. -/
theorem tm_isConformal : (tmDistortion R hR hφ hl).IsConformal :=
  ⟨tm_orthogonal hR hφ hl, by rw [tm_h, tm_k]⟩

end Conformal

/-- The scale factor is `1` on the central meridian. -/
theorem tmScale_central (φ : ℝ) : tmScale φ 0 = 1 := by simp [tmScale, tmB]

/-- Away from the central meridian (and off the poles) the scale factor exceeds `1`. -/
theorem one_lt_tmScale (hl : 0 < cos lam) (hB : tmB φ lam ≠ 0) : 1 < tmScale φ lam := by
  have hB2 := tmB_sq_lt_one φ hl
  have hpos : 0 < tmB φ lam ^ 2 := by positivity
  have hD : 0 < 1 - tmB φ lam ^ 2 := by linarith
  have hs : √(1 - tmB φ lam ^ 2) < 1 := by
    rw [sqrt_lt' one_pos]; linarith
  rw [tmScale, lt_div_iff₀ (sqrt_pos.mpr hD), one_mul]
  exact hs

/-! ## UTM -/

/-- The UTM scale factor: the transverse Mercator scale times `0.9996`. -/
noncomputable def utmScale (φ lam : ℝ) : ℝ := 0.9996 * tmScale φ lam

theorem one_le_tmScale (φ : ℝ) (hl : 0 < cos lam) : 1 ≤ tmScale φ lam := by
  have hB2 := tmB_sq_lt_one φ hl
  have hD : 0 < 1 - tmB φ lam ^ 2 := by linarith
  have hs : √(1 - tmB φ lam ^ 2) ≤ 1 := sqrt_le_one.mpr (by nlinarith [sq_nonneg (tmB φ lam)])
  rw [tmScale, le_div_iff₀ (sqrt_pos.mpr hD), one_mul]
  exact hs

/-- Within 3° of the central meridian the UTM scale is between 0.9996 and
1.00098. -/
theorem utmScale_bounds (φ : ℝ) (hl : |lam| ≤ degToRad 3) :
    0.9996 ≤ utmScale φ lam ∧ utmScale φ lam < 1.00098 := by
  have hx : degToRad 3 < 0.05236 := by rw [degToRad]; nlinarith [pi_lt_d6]
  have hlam2 : lam ^ 2 ≤ 0.05236 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
  have hcos : 0.998629 ≤ cos lam := by
    have := one_sub_sq_div_two_le_cos (x := lam)
    nlinarith
  have hl0 : 0 < cos lam := by linarith
  have hB2 : tmB φ lam ^ 2 ≤ 1 - cos lam ^ 2 := by
    unfold tmB
    have h1 := sin_sq_add_cos_sq lam
    have h2 : cos φ ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq φ, sq_nonneg (sin φ)]
    nlinarith [sq_nonneg (sin lam)]
  have hD : 0.998629 ^ 2 ≤ 1 - tmB φ lam ^ 2 := by nlinarith
  have hs : 0.998629 ≤ √(1 - tmB φ lam ^ 2) := by
    rw [show (0.998629 : ℝ) = √(0.998629 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hD
  have hspos : 0 < √(1 - tmB φ lam ^ 2) := by linarith
  constructor
  · have := one_le_tmScale φ hl0
    unfold utmScale
    linarith
  · unfold utmScale tmScale
    rw [mul_one_div, div_lt_iff₀ hspos]
    nlinarith

/-- On the equator the UTM scale is exact where `sin² λ = 1 - 0.9996²`: on two
lines, one on each side of the central meridian. -/
theorem utmScale_equator_eq_one_iff (hl : 0 < cos lam) :
    utmScale 0 lam = 1 ↔ sin lam ^ 2 = 1 - 0.9996 ^ 2 := by
  have hB2 := tmB_sq_lt_one 0 hl
  have hD : 0 < 1 - tmB 0 lam ^ 2 := by linarith
  have hB : tmB 0 lam = sin lam := by simp [tmB]
  rw [hB] at hD
  have hs := sqrt_pos.mpr hD
  unfold utmScale tmScale
  rw [hB, mul_one_div, div_eq_one_iff_eq hs.ne']
  constructor
  · intro h
    have := congrArg (· ^ 2) h
    simp only [sq_sqrt hD.le] at this
    linarith
  · intro h
    rw [show 1 - sin lam ^ 2 = 0.9996 ^ 2 by linarith, sqrt_sq (by norm_num)]

end Geodesy.Projection
