import LeanGeodesy.CRS.Basic
import LeanGeodesy.WGS84

/-!
# The WGS 84 geographic CRS

The geographic CRS on the WGS 84 ellipsoid (`wgs84`, with `a = 6378137 m` and
`1 / f = 298.257223563`). Its coordinates are WGS 84 latitudes and
longitudes, and each one means a point of the WGS 84 ellipsoid.
-/

namespace Geodesy

/-- The geographic CRS on the WGS 84 ellipsoid. -/
noncomputable def wgs84Geographic : GeographicCRS := ⟨wgs84⟩

@[simp] theorem wgs84Geographic_ellipsoid : wgs84Geographic.ellipsoid = wgs84 := rfl

/-- Every WGS 84 coordinate means a point of the WGS 84 ellipsoid. -/
theorem wgs84Geographic_toPoint_mem (c : wgs84Geographic.Coordinate) :
    wgs84Geographic.toPoint c ∈ wgs84.toSet :=
  wgs84Geographic.toPoint_mem c

end Geodesy
