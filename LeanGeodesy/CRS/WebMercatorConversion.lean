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

`toWebMercator` goes from the first to the second (`toWebMercator_pt`).
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

end Geodesy
