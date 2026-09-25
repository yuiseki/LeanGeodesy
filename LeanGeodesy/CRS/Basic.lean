import LeanGeodesy.GeodeticCoordinate
import LeanGeodesy.Projection.Mercator

/-!
# Coordinate reference systems

A pair of numbers is not a position until it is said what the numbers are
measured against. A coordinate reference system (CRS) says it. This file
defines the two kinds of CRS a web map needs, as mathematical objects.

- A `GeographicCRS` fixes a reference ellipsoid. Its coordinates are a
  geodetic latitude and longitude, and each one means a point of that
  ellipsoid (`GeographicCRS.toPoint`, `GeographicCRS.toPoint_mem`).
- A `ProjectedCRS` fixes a geographic CRS, a region of it (`domain`), a
  region of the plane (`image`), and a projection between them with an
  inverse. Its coordinates are points of the plane, and each one in the
  image means the geographic coordinate that the inverse gives back.

Coordinates carry their CRS in their type: `C.Coordinate` and
`D.Coordinate` are different types for different CRSs, so a coordinate
cannot silently be read against the wrong system.

A geodetic datum is modelled only by its ellipsoid, centred at the origin
with its axis along `z`, and longitudes are counted from the meridian in
the `xz` plane. The datum's realisation (its reference frame, epoch and
station coordinates), units and axis order are not modelled. Nothing here
refers to any registry of CRS definitions; see `CRS/EPSG.lean` for
how known identifiers are attached as labels.
-/

namespace Geodesy

/-- A geographic coordinate reference system, given by its reference ellipsoid. -/
structure GeographicCRS where
  /-- The ellipsoid that coordinates are measured on. -/
  ellipsoid : ReferenceEllipsoid

namespace GeographicCRS

variable (C : GeographicCRS)

/-- A coordinate of the geographic CRS `C`: a geodetic latitude and longitude
on `C`'s ellipsoid. The CRS is part of the type. -/
@[ext] structure Coordinate (C : GeographicCRS) where
  lat : GeodeticLatitude
  lon : GeodeticLongitude

/-- The same coordinate with height zero, as a geodetic coordinate. -/
def Coordinate.toGeodetic {C : GeographicCRS} (c : C.Coordinate) : GeodeticCoordinate :=
  ⟨c.lat, c.lon, 0⟩

/-- The point of space a coordinate means. -/
noncomputable def toPoint (c : C.Coordinate) : E3 :=
  GeodeticCoordinate.surfacePoint C.ellipsoid c.toGeodetic

/-- It lies on the CRS's ellipsoid. -/
theorem toPoint_mem (c : C.Coordinate) : C.toPoint c ∈ C.ellipsoid.toSet :=
  GeodeticCoordinate.surfacePoint_mem _ _

/-- It is the ECEF position of the coordinate at height zero. -/
theorem toPoint_eq_toECEF (c : C.Coordinate) :
    C.toPoint c = GeodeticCoordinate.toECEF C.ellipsoid c.toGeodetic := by
  rw [toPoint, GeodeticCoordinate.toECEF_eq]
  simp [Coordinate.toGeodetic]

end GeographicCRS

open Projection in
/-- A projected coordinate reference system: a geographic CRS, a region of it,
a region of the plane, and a projection between them with an inverse. -/
structure ProjectedCRS where
  /-- The geographic CRS being projected. -/
  base : GeographicCRS
  /-- The geographic coordinates the projection is used for. -/
  domain : Set base.Coordinate
  /-- The region of the plane that those coordinates fill. -/
  image : Set E2
  /-- The projection. -/
  forward : base.Coordinate → E2
  /-- Its inverse. -/
  inverse : E2 → base.Coordinate
  forward_mapsTo : Set.MapsTo forward domain image
  inverse_mapsTo : Set.MapsTo inverse image domain
  inverse_forward : ∀ c ∈ domain, inverse (forward c) = c
  forward_inverse : ∀ p ∈ image, forward (inverse p) = p

namespace ProjectedCRS

open Projection

variable (P : ProjectedCRS)

/-- A coordinate of the projected CRS `P`: a point of the plane. The CRS is part
of the type. -/
@[ext] structure Coordinate (P : ProjectedCRS) where
  pt : E2

/-- Projecting a geographic coordinate gives a projected coordinate. -/
def project (c : P.base.Coordinate) : P.Coordinate := ⟨P.forward c⟩

/-- Reading a projected coordinate back as a geographic one. -/
def unproject (p : P.Coordinate) : P.base.Coordinate := P.inverse p.pt

/-- Projecting a coordinate of the domain and reading it back gives it back. -/
theorem unproject_project {c : P.base.Coordinate} (hc : c ∈ P.domain) :
    P.unproject (P.project c) = c :=
  P.inverse_forward c hc

/-- Reading a coordinate of the image back and projecting it gives it back. -/
theorem project_unproject {p : P.Coordinate} (hp : p.pt ∈ P.image) :
    P.project (P.unproject p) = p :=
  Coordinate.ext (P.forward_inverse p.pt hp)

/-- The projection is a bijection from the domain onto the image. -/
theorem forward_bijOn : Set.BijOn P.forward P.domain P.image :=
  Set.InvOn.bijOn ⟨fun c hc => P.inverse_forward c hc, fun p hp => P.forward_inverse p hp⟩
    P.forward_mapsTo P.inverse_mapsTo

/-- Its inverse is a bijection the other way. -/
theorem inverse_bijOn : Set.BijOn P.inverse P.image P.domain :=
  Set.InvOn.bijOn ⟨fun p hp => P.forward_inverse p hp, fun c hc => P.inverse_forward c hc⟩
    P.inverse_mapsTo P.forward_mapsTo

/-- A projected coordinate in the image means the point of space that its
geographic coordinate means. -/
noncomputable def toPoint (p : P.Coordinate) : E3 := P.base.toPoint (P.unproject p)

/-- Projecting and then locating a point finds the same point as locating it
directly. -/
theorem toPoint_project {c : P.base.Coordinate} (hc : c ∈ P.domain) :
    P.toPoint (P.project c) = P.base.toPoint c := by
  rw [toPoint, P.unproject_project hc]

end ProjectedCRS

end Geodesy
