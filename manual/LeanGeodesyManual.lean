import VersoManual
import LeanGeodesyManual.PartEllipsoid
import LeanGeodesyManual.PartTiles
import LeanGeodesyManual.PartCRS

open Verso.Genre Manual

#doc (Manual) "LeanGeodesy" =>
%%%
shortTitle := "LeanGeodesy"
%%%

LeanGeodesy proves in Lean 4 the mathematics that GIS software takes for
granted: the shape of the Earth, how map projections distort it, which
routes are shortest, how web map tiles are numbered, and how coordinate
systems relate. This book walks through it in order. Every declaration
shown is taken from the library as it is built, with its signature and
documentation; nothing is restated by hand, and every theorem is proved.

The book follows three lines of argument, which can be read independently.

```
Part I: The Earth as an ellipsoid

Ellipsoid geometry
↓
Differential geometry
↓
Projection
↓
Geodesics


Part II: Tiles

Tile Grid
↓
Quadtree
↓
SpatialOrder
├─ Morton
└─ Hilbert


Part III: Coordinate reference systems

CRS
```

Part I is the mathematical spine. It builds everything from a reference
ellipsoid: its radii of curvature, then its first fundamental form, which
measures length, angle and area on it. Map projections are then measured
against that form, which is what distortion means, and the shortest routes
come out of the same form as the geodesic equations.

```
Reference Ellipsoid
        ↓
Curvature
        ↓
First Fundamental Form
        ↓
Local Distortion
      ↙   ↓   ↘
Mercator  Equal Area  Azimuthal
```

Part II starts where Part I leaves Web Mercator, as a square world, and cuts
it into tiles. From there it is combinatorics on natural numbers: the tiles
form a quadtree, and a spatial index numbers them so that each subtree is
one interval. Morton and Hilbert are two such numberings.

Part III puts the pieces together as coordinate reference systems: the
conversion between EPSG:4326 and EPSG:3857 is a projection from Part I,
while moving between datums goes through space.

{include 1 LeanGeodesyManual.PartEllipsoid}
{include 1 LeanGeodesyManual.PartTiles}
{include 1 LeanGeodesyManual.PartCRS}
