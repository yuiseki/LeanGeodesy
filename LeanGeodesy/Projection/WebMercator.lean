import LeanGeodesy.Curvature
import LeanGeodesy.WGS84
import LeanGeodesy.Projection.Mercator
import Mathlib.Data.Real.Pi.Bounds

/-!
# Web Mercator (EPSG:3857)

Web maps, from OpenStreetMap to Google Maps, draw the world with Web
Mercator. It takes a WGS 84 latitude and longitude and applies the
spherical Mercator formulas on a sphere whose radius is the WGS 84
semi-major axis `a = 6378137 m`:

```
x = a λ,   y = a · mercatorY φ.
```

The theorems here explain the numbers every web map is built on.

- Longitudes fill `x ∈ (-π a, π a]` (`x_mem`), about ±20037508.34 m
  (`halfExtent_bounds`).
- The poles are infinitely far away, so the map is cut off at the latitude
  `maxLatitude` whose northing is `π a` (`y_maxLatitude`). The world then
  becomes a square (`y_mem_iff`), which is what lets it be cut into square
  tiles.
- At zoom `z` the square is `256 · 2^z` pixels wide, and every point of the
  square lands on a pixel inside it (`pixel_mem`). Each zoom level doubles
  the pixel coordinates (`pixelX_succ`).
- A pixel covers `2π a cos φ / (256 · 2^z)` metres of ground
  (`groundResolution_eq`), about 156543.03 m at the equator at zoom 0
  (`groundResolution_zero_bounds`). The `cos φ` is the Mercator scale factor
  at work.

## Not conformal on the ellipsoid

Web Mercator feeds WGS 84 geodetic latitudes, which live on an ellipsoid,
into formulas made for a sphere. Measured against the ellipsoid it is not
quite conformal, and this file proves by how much.

On the ellipsoid the point at geodetic latitude `φ` and longitude `λ` is
(`surfacePoint`)

```
(N cos φ cos λ, N cos φ sin λ, N (1 - e²) sin φ).
```

Moving along the parallel traces a circle of radius `N cos φ`, as on the
sphere. Moving along the meridian is different: the tangent has length

```
M = a (1 - e²) / (1 - e² sin² φ)^(3/2),
```

the radius of curvature of the meridian, which is smaller than `N`
(`hasDerivAt_ellipsoidPoint_lat`, `norm_meridianTangent_sq`).

The map stretches the meridian by `R sec φ / M` and the parallel by
`R sec φ / N`, so their ratio is

```
N / M = (1 - e² sin² φ) / (1 - e²)   (scale_ratio)
```

This is `1` on a sphere and larger than `1` everywhere between the poles
on a flattened ellipsoid (`meridianScale_gt_parallelScale`): a small circle
on the ellipsoid is drawn as an ellipse stretched north to south. On WGS 84
the ratio is largest at the equator, about `1.00674`
(`wgs84_equator_scale_ratio`), an elongation of about 0.67 %.
-/

namespace Geodesy.Projection

open Real

/-- The radius of the Web Mercator sphere: the WGS 84 semi-major axis. -/
noncomputable def webMercatorRadius : ℝ := wgs84.a

theorem webMercatorRadius_eq : webMercatorRadius = 6378137 := rfl

theorem webMercatorRadius_pos : 0 < webMercatorRadius := wgs84.a_pos

local notation "a" => webMercatorRadius

/-- The easting of a longitude. -/
noncomputable def webMercatorX (lon : GeodeticLongitude) : ℝ := a * lon.toReal

/-- The northing of a latitude strictly between the poles. -/
noncomputable def webMercatorY (φ : ℝ) : ℝ := a * mercatorY φ

/-- The projection of a WGS 84 coordinate. The height is ignored. -/
noncomputable def webMercator (c : GeodeticCoordinate) : E2 :=
  vec2 (webMercatorX c.lon) (webMercatorY c.lat.1)

/-- It is Mercator's projection of the sphere of radius `a`. -/
theorem webMercator_eq_mercator (c : GeodeticCoordinate) :
    webMercator c = mercator a c.lat.1 c.lon.toReal := rfl

/-! ## The square world -/

/-- Half the width of the world: `π a`. -/
noncomputable def halfExtent : ℝ := π * a

theorem halfExtent_pos : 0 < halfExtent := mul_pos pi_pos webMercatorRadius_pos

/-- `π a` is 20037508.34 m to the centimetre. -/
theorem halfExtent_bounds : 20037508.34 < halfExtent ∧ halfExtent < 20037508.35 := by
  rw [halfExtent, webMercatorRadius_eq]
  constructor <;> nlinarith [pi_gt_d20, pi_lt_d20]

/-- Every longitude has an easting in `(-π a, π a]`. -/
theorem x_mem (lon : GeodeticLongitude) :
    -halfExtent < webMercatorX lon ∧ webMercatorX lon ≤ halfExtent := by
  have ha := webMercatorRadius_pos
  have h₁ := Real.Angle.neg_pi_lt_toReal lon
  have h₂ := Real.Angle.toReal_le_pi lon
  rw [webMercatorX, halfExtent]
  constructor <;> nlinarith

/-- The latitude at which the map is cut off, about 85.05°. -/
noncomputable def maxLatitude : ℝ := gd π

theorem maxLatitude_mem : maxLatitude ∈ Set.Ioo (-(π / 2)) (π / 2) := gd_mem π

theorem maxLatitude_pos : 0 < maxLatitude := by
  rw [maxLatitude, gd]
  simpa [arctan_zero] using arctan_strictMono (sinh_pos_iff.mpr pi_pos)

/-- `tan (maxLatitude) = sinh π`. -/
theorem tan_maxLatitude : tan maxLatitude = sinh π := by
  rw [maxLatitude, gd, tan_arctan]

/-- The cut-off latitude is where the northing reaches `π a`, the same as
the easting at the antimeridian. -/
theorem y_maxLatitude : webMercatorY maxLatitude = halfExtent := by
  rw [webMercatorY, maxLatitude, mercatorY_gd, halfExtent, mul_comm]

/-- A latitude is inside the square exactly when it is no further from the
equator than `maxLatitude`. -/
theorem y_mem_iff {φ : ℝ} (h : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    (-halfExtent ≤ webMercatorY φ ∧ webMercatorY φ ≤ halfExtent) ↔
      (-maxLatitude ≤ φ ∧ φ ≤ maxLatitude) := by
  have ha := webMercatorRadius_pos
  have hm := maxLatitude_mem
  have hm' : -maxLatitude ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hm.2], by linarith [hm.1]⟩
  have hup : mercatorY maxLatitude = π := mercatorY_gd π
  have hlo : mercatorY (-maxLatitude) = -π := by rw [mercatorY_neg, hup]
  have mono := mercatorY_strictMonoOn
  rw [webMercatorY, halfExtent]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · by_contra hlt
      have := mono h hm' (lt_of_not_le hlt)
      rw [hlo] at this
      nlinarith
    · by_contra hlt
      have := mono hm h (lt_of_not_le hlt)
      rw [hup] at this
      nlinarith
  · rintro ⟨h₁, h₂⟩
    have e₁ := mono.monotoneOn hm' h h₁
    have e₂ := mono.monotoneOn h hm h₂
    rw [hlo] at e₁
    rw [hup] at e₂
    constructor <;> nlinarith

/-- Inverting the projection: the latitude and longitude of a map point. -/
noncomputable def webMercatorInverse (x y : ℝ) : ℝ × ℝ := (gd (y / a), x / a)

theorem webMercatorInverse_webMercator {φ : ℝ} (h : φ ∈ Set.Ioo (-(π / 2)) (π / 2))
    (lon : GeodeticLongitude) :
    webMercatorInverse (webMercatorX lon) (webMercatorY φ) = (φ, lon.toReal) := by
  have ha := webMercatorRadius_pos.ne'
  simp only [webMercatorInverse, webMercatorX, webMercatorY, mul_div_cancel_left₀ _ ha,
    gd_mercatorY h]

/-! ## Tiles and pixels -/

/-- The width of the world in pixels at zoom `z`, with 256-pixel tiles. -/
noncomputable def worldPixels (z : ℕ) : ℝ := 256 * 2 ^ z

theorem worldPixels_pos (z : ℕ) : 0 < worldPixels z := by unfold worldPixels; positivity

/-- The pixel column of an easting, counted from the antimeridian at the left. -/
noncomputable def pixelX (z : ℕ) (x : ℝ) : ℝ := (x + halfExtent) / (2 * halfExtent) * worldPixels z

/-- The pixel row of a northing, counted from the top edge downwards. -/
noncomputable def pixelY (z : ℕ) (y : ℝ) : ℝ := (halfExtent - y) / (2 * halfExtent) * worldPixels z

/-- Every point of the square lands on a pixel of the world. -/
theorem pixel_mem (z : ℕ) {x y : ℝ} (hx : -halfExtent ≤ x ∧ x ≤ halfExtent)
    (hy : -halfExtent ≤ y ∧ y ≤ halfExtent) :
    (0 ≤ pixelX z x ∧ pixelX z x ≤ worldPixels z) ∧
      (0 ≤ pixelY z y ∧ pixelY z y ≤ worldPixels z) := by
  have hH := halfExtent_pos
  have hW := worldPixels_pos z
  have hle : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * halfExtent →
      0 ≤ t / (2 * halfExtent) * worldPixels z ∧ t / (2 * halfExtent) * worldPixels z ≤ worldPixels z := by
    intro t h0 h1
    have hq : t / (2 * halfExtent) ≤ 1 := (div_le_one (by linarith)).mpr h1
    exact ⟨by positivity, by nlinarith [div_nonneg h0 (by linarith : (0 : ℝ) ≤ 2 * halfExtent)]⟩
  exact ⟨hle _ (by linarith) (by linarith), hle _ (by linarith) (by linarith)⟩

/-- Zooming in by one level doubles every pixel coordinate. -/
theorem pixelX_succ (z : ℕ) (x : ℝ) : pixelX (z + 1) x = 2 * pixelX z x := by
  simp only [pixelX, worldPixels, pow_succ]
  ring

theorem pixelY_succ (z : ℕ) (y : ℝ) : pixelY (z + 1) y = 2 * pixelY z y := by
  simp only [pixelY, worldPixels, pow_succ]
  ring

/-- The ground distance covered by one pixel at zoom `z` and latitude `φ`. -/
noncomputable def groundResolution (z : ℕ) (φ : ℝ) : ℝ :=
  2 * halfExtent / worldPixels z / scaleFactor φ

/-- The familiar formula: `2π a cos φ / (256 · 2^z)` metres per pixel. -/
theorem groundResolution_eq (z : ℕ) (φ : ℝ) :
    groundResolution z φ = 2 * π * a * cos φ / (256 * 2 ^ z) := by
  simp only [groundResolution, halfExtent, worldPixels, scaleFactor, one_div, div_inv_eq_mul]
  ring

/-- At zoom 0 on the equator one pixel is 156543.03 m. -/
theorem groundResolution_zero_bounds :
    156543.03 < groundResolution 0 0 ∧ groundResolution 0 0 < 156543.04 := by
  rw [groundResolution_eq, webMercatorRadius_eq]
  simp only [cos_zero, pow_zero]
  constructor <;> nlinarith [pi_gt_d20, pi_lt_d20]

/-- Each zoom level halves the ground resolution. -/
theorem groundResolution_succ (z : ℕ) (φ : ℝ) :
    groundResolution (z + 1) φ = groundResolution z φ / 2 := by
  simp only [groundResolution_eq, pow_succ]
  ring

section EllipsoidScale

variable (E : ReferenceEllipsoid)

/-! ## The scale of a Mercator map of radius `R` measured on the ellipsoid

The map sends a step `dφ` north to `R sec φ dφ` and a step `dλ` east to
`R dλ` (`hasDerivAt_mercator_lat`, `hasDerivAt_mercator_lon`). -/

/-- The scale along the meridian: map length over ellipsoid length. -/
noncomputable def meridianScale (R φ : ℝ) : ℝ := R / cos φ / E.meridianRadius φ

/-- The scale along the parallel. -/
noncomputable def parallelScale (R φ : ℝ) : ℝ := R / (E.primeVerticalRadius φ * cos φ)

/-- The two scales differ by the factor `N / M`. -/
theorem scale_ratio (R : ℝ) (hR : 0 < R) {φ : ℝ} (hc : 0 < cos φ) :
    meridianScale E R φ / parallelScale E R φ = E.W2 φ / (1 - E.e2) := by
  have hM := E.meridianRadius_pos φ
  have hN := E.primeVerticalRadius_pos φ
  rw [← E.N_div_M]
  simp only [meridianScale, parallelScale]
  field_simp
  ring

/-- On a sphere the two scales agree: Mercator is conformal there. -/
theorem meridianScale_eq_parallelScale_of_sphere (hf : E.f = 0) (R φ : ℝ) :
    meridianScale E R φ = parallelScale E R φ := by
  have he : E.e2 = 0 := (E.isSphere_tfae.out 0 2).mp hf
  simp [meridianScale, parallelScale, ReferenceEllipsoid.meridianRadius, ReferenceEllipsoid.W2, ReferenceEllipsoid.primeVerticalRadius,
    he, div_div, mul_comm]

/-- On a flattened ellipsoid the meridian is stretched more than the
parallel everywhere between the poles: a Mercator map fed with geodetic
latitudes is not conformal. -/
theorem meridianScale_gt_parallelScale (hf : 0 < E.f) (R : ℝ) (hR : 0 < R) {φ : ℝ}
    (hc : 0 < cos φ) : parallelScale E R φ < meridianScale E R φ := by
  have he : 0 < E.e2 := mul_pos hf (by linarith [E.f_lt_one])
  have hk : 0 < parallelScale E R φ := by
    have := E.primeVerticalRadius_pos φ
    unfold parallelScale
    positivity
  have hr := scale_ratio E R hR hc
  have h1 : 1 < E.W2 φ / (1 - E.e2) := by
    rw [one_lt_div E.one_sub_e2_pos, ReferenceEllipsoid.W2]
    have hp := sin_sq_add_cos_sq φ
    have : 0 < cos φ ^ 2 := by positivity
    nlinarith
  rw [← hr, one_lt_div hk] at h1
  exact h1

/-- On WGS 84 at the equator the meridian is stretched 1.00674 times as
much as the parallel. -/
theorem wgs84_equator_scale_ratio (R : ℝ) (hR : 0 < R) :
    1.006739 < meridianScale wgs84 R 0 / parallelScale wgs84 R 0 ∧
      meridianScale wgs84 R 0 / parallelScale wgs84 R 0 < 1.006740 := by
  rw [scale_ratio wgs84 R hR (by simp)]
  simp only [ReferenceEllipsoid.W2, sin_zero, ReferenceEllipsoid.e2, wgs84_f]
  norm_num

end EllipsoidScale

end Geodesy.Projection
