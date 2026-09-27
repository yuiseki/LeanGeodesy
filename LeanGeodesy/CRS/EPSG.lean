import LeanGeodesy.CRS.WebMercator

/-!
# EPSG identifiers as labels

The EPSG Geodetic Parameter Dataset gives identifiers to published CRS
definitions. This file attaches two of them, as labels, to CRSs that this
library constructs mathematically:

| Label | Constructed CRS | What the published definition calls it |
| --- | --- | --- |
| `EPSG:4326` | `wgs84Geographic` | WGS 84, geographic 2D |
| `EPSG:3857` | `webMercatorCRS` | WGS 84 / Pseudo-Mercator |

A label records which published definition a constructed CRS is meant to
correspond to. It is not a proof of that correspondence, and nothing in the
library depends on it: no theorem mentions an identifier, and the EPSG
dataset is not read, copied or assumed anywhere. What the published
definitions add beyond the mathematics here is not modelled, in particular:

- units: EPSG:4326 is in degrees, this library in radians (see `Angle`);
- axis order: EPSG:4326 lists latitude before longitude, which here are
  named fields rather than positions;
- the datum's realisations: WGS 84 has been realised several times, while
  here a datum is only its ellipsoid;
- areas of use, stated by the dataset in degrees.
-/

namespace Geodesy.CRS.EPSG

/-- An identifier issued by an authority, such as `EPSG:4326`. -/
structure Identifier where
  authority : String
  code : ℕ
  deriving DecidableEq, Repr

/-- The usual written form, `authority:code`. -/
def Identifier.toString (i : Identifier) : String := i.authority ++ ":" ++ Nat.repr i.code

def epsg4326 : Identifier := ⟨"EPSG", 4326⟩
def epsg3857 : Identifier := ⟨"EPSG", 3857⟩

example : epsg4326.toString = "EPSG:4326" := by decide
example : epsg3857.toString = "EPSG:3857" := by decide

/-- A constructed object together with the identifier of the published
definition it is meant to correspond to. -/
structure Labelled (α : Type) where
  /-- The identifier of the published definition. -/
  identifier : Identifier
  /-- The object constructed in this library. -/
  value : α

/-- `EPSG:4326` names the WGS 84 geographic CRS. -/
noncomputable def wgs84Geographic : Labelled GeographicCRS := ⟨epsg4326, Geodesy.wgs84Geographic⟩

/-- `EPSG:3857` names the Web Mercator projected CRS. -/
noncomputable def webMercator : Labelled ProjectedCRS := ⟨epsg3857, Geodesy.webMercatorCRS⟩

end Geodesy.CRS.EPSG
