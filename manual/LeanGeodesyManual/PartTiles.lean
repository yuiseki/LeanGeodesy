import VersoManual
import LeanGeodesyManual.Chapters.TileGrid
import LeanGeodesyManual.Chapters.Quadtree
import LeanGeodesyManual.Chapters.SpatialOrder

open Verso.Genre Manual

#doc (Manual) "Part II: Tiles" =>

Web maps cut the square world of Web Mercator into tiles, and spatial
indexes number the tiles. This part proves what those numbers guarantee.

```
Tile Grid
↓
Quadtree
↓
SpatialOrder
├─ Morton
└─ Hilbert
```

The tile grid chapter connects the tiles to the projection of Part I. From
the quadtree chapter on, everything is combinatorics on natural numbers.

{include 1 LeanGeodesyManual.Chapters.TileGrid}
{include 1 LeanGeodesyManual.Chapters.Quadtree}
{include 1 LeanGeodesyManual.Chapters.SpatialOrder}
