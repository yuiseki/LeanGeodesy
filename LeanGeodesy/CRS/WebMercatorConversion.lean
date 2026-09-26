import LeanGeodesy.CRS.WebMercator

/-!
# Converting between WGS 84 geographic 2D and Web Mercator

The conversion GIS users know as EPSG:4326 to EPSG:3857 and back, assembled
from the CRSs this library constructs: `wgs84Geographic`, the WGS 84
geographic 2D CRS (latitude and longitude, no height), and
`webMercatorCRS`, the Web Mercator projected CRS over it.

Both CRSs are on the same datum, so this is a coordinate conversion by a
projection, not a transformation between datums: no ECEF position and no
Helmert transformation is involved. The formulas are those of
`webMercatorCRS.forward` and `webMercatorCRS.inverse`, reused, not restated.

The conversion is only meaningful inside Web Mercator's domain, the
latitudes within the cut-off, and its image, the square world. Both
restrictions are in the types:

- `WebMercatorValidCoordinate`, the WGS 84 geographic 2D coordinates in the
  domain (`mem_webMercatorValid_iff`);
- `WebMercatorImageCoordinate`, the Web Mercator coordinates in the image.

`toWebMercator` goes from the first to the second (`toWebMercator_pt`), and
`fromWebMercator` back, with latitude `gd (y / a)` and longitude `x / a`
(`fromWebMercator_lat`, `fromWebMercator_lon`).

The two undo each other (`fromWebMercator_toWebMercator`,
`toWebMercator_fromWebMercator`), so they form a bijection between the valid
geographic coordinates and the square (`webMercatorEquiv`), which is
`ProjectedCRS.forward_bijOn` for `webMercatorCRS`
(`webMercatorConversion_bijOn`).

Landmarks, read off existing theorems:

- the equator goes to `y = 0` and the prime meridian to `x = 0`
  (`toWebMercator_equator`, `toWebMercator_primeMeridian`);
- the cut-off latitudes go to the top and bottom edges `y = ± π a`
  (`toWebMercator_maxLatitude`, `toWebMercator_neg_maxLatitude`);
- the antimeridian goes to the right edge `x = π a`
  (`toWebMercator_antimeridian`), and no longitude reaches the left edge
  (`toWebMercator_x_ne_left`): 180° east and 180° west are one longitude,
  drawn once.
-/

namespace Geodesy

open Projection

/-- A WGS 84 geographic 2D coordinate inside Web Mercator's domain: latitude
within the cut-off. -/
abbrev WebMercatorValidCoordinate :=
  {p : wgs84Geographic.Coordinate // p ∈ webMercatorCRS.domain}

/-- A Web Mercator coordinate inside the image: the square world. -/
abbrev WebMercatorImageCoordinate :=
  {q : webMercatorCRS.Coordinate // q.pt ∈ webMercatorCRS.image}

/-- A WGS 84 geographic 2D coordinate is valid for Web Mercator exactly when
its latitude is within the cut-off. -/
theorem mem_webMercatorValid_iff (p : wgs84Geographic.Coordinate) :
    p ∈ webMercatorCRS.domain ↔ -maxLatitude ≤ p.lat.1 ∧ p.lat.1 ≤ maxLatitude :=
  Iff.rfl

/-- WGS 84 geographic 2D to Web Mercator: `webMercatorCRS.project`, landing in
the image. -/
noncomputable def toWebMercator (p : WebMercatorValidCoordinate) : WebMercatorImageCoordinate :=
  ⟨webMercatorCRS.project p.1, webMercatorCRS.forward_mapsTo p.2⟩

/-- The converted coordinate is the Web Mercator easting of the longitude and
northing of the latitude. -/
theorem toWebMercator_pt (p : WebMercatorValidCoordinate) :
    (toWebMercator p).1.pt = vec2 (webMercatorX p.1.lon) (webMercatorY p.1.lat.1) :=
  rfl

/-- Web Mercator to WGS 84 geographic 2D: `webMercatorCRS.unproject`, defined only
on the image and landing in the domain. -/
noncomputable def fromWebMercator (q : WebMercatorImageCoordinate) : WebMercatorValidCoordinate :=
  ⟨webMercatorCRS.unproject q.1, webMercatorCRS.inverse_mapsTo q.2⟩

/-- The latitude read back is `gd (y / a)`. -/
theorem fromWebMercator_lat (q : WebMercatorImageCoordinate) :
    (fromWebMercator q).1.lat.1 = gd (q.1.pt 1 / webMercatorRadius) :=
  webMercatorCRS_inverse_lat q.1.pt

/-- The longitude read back is `x / a`, modulo a full turn. -/
theorem fromWebMercator_lon (q : WebMercatorImageCoordinate) :
    (fromWebMercator q).1.lon = ((q.1.pt 0 / webMercatorRadius : ℝ) : Real.Angle) :=
  webMercatorCRS_inverse_lon q.1.pt

/-! ## Round trips -/

/-- Converting a valid WGS 84 coordinate to Web Mercator and back gives it back. -/
theorem fromWebMercator_toWebMercator (p : WebMercatorValidCoordinate) :
    fromWebMercator (toWebMercator p) = p :=
  Subtype.ext (webMercatorCRS.unproject_project p.2)

/-- Converting a Web Mercator coordinate of the square to WGS 84 and back gives
it back. -/
theorem toWebMercator_fromWebMercator (q : WebMercatorImageCoordinate) :
    toWebMercator (fromWebMercator q) = q :=
  Subtype.ext (webMercatorCRS.project_unproject q.2)

/-- The conversion is a bijection between the valid WGS 84 geographic 2D
coordinates and the square. -/
noncomputable def webMercatorEquiv : WebMercatorValidCoordinate ≃ WebMercatorImageCoordinate where
  toFun := toWebMercator
  invFun := fromWebMercator
  left_inv := fromWebMercator_toWebMercator
  right_inv := toWebMercator_fromWebMercator

/-- The conversion is the forward map of `webMercatorCRS`... -/
theorem toWebMercator_pt_eq_forward (p : WebMercatorValidCoordinate) :
    (toWebMercator p).1.pt = webMercatorCRS.forward p.1 :=
  rfl

/-- ...which is a bijection from the domain onto the image. -/
theorem webMercatorConversion_bijOn :
    Set.BijOn webMercatorCRS.forward webMercatorCRS.domain webMercatorCRS.image :=
  webMercatorCRS.forward_bijOn

/-! ## Landmarks -/

/-- The equator goes to `y = 0`. -/
theorem toWebMercator_equator (p : WebMercatorValidCoordinate) (h : p.1.lat.1 = 0) :
    (toWebMercator p).1.pt 1 = 0 := by
  simp [toWebMercator_pt, h, webMercatorY]

/-- The prime meridian goes to `x = 0`. -/
theorem toWebMercator_primeMeridian (p : WebMercatorValidCoordinate) (h : p.1.lon = 0) :
    (toWebMercator p).1.pt 0 = 0 := by
  simp [toWebMercator_pt, h, webMercatorX]

/-- The northern cut-off latitude goes to the top edge `y = π a`. -/
theorem toWebMercator_maxLatitude (p : WebMercatorValidCoordinate) (h : p.1.lat.1 = maxLatitude) :
    (toWebMercator p).1.pt 1 = halfExtent := by
  simp only [toWebMercator_pt, vec2_1, h, y_maxLatitude]

/-- The southern cut-off latitude goes to the bottom edge `y = -π a`. -/
theorem toWebMercator_neg_maxLatitude (p : WebMercatorValidCoordinate)
    (h : p.1.lat.1 = -maxLatitude) : (toWebMercator p).1.pt 1 = -halfExtent := by
  simp only [toWebMercator_pt, vec2_1, h, webMercatorY, mercatorY_neg, mul_neg]
  rw [← webMercatorY, y_maxLatitude]

/-- The antimeridian goes to the right edge `x = π a`. -/
theorem toWebMercator_antimeridian (p : WebMercatorValidCoordinate)
    (h : p.1.lon = (Real.pi : Real.Angle)) : (toWebMercator p).1.pt 0 = halfExtent := by
  simp only [toWebMercator_pt, vec2_0, h, webMercatorX, Real.Angle.toReal_pi, halfExtent, mul_comm]

/-- No longitude reaches the left edge `x = -π a`. -/
theorem toWebMercator_x_ne_left (p : WebMercatorValidCoordinate) :
    (toWebMercator p).1.pt 0 ≠ -halfExtent := by
  rw [toWebMercator_pt, vec2_0]
  exact (x_mem p.1.lon).1.ne'

end Geodesy
