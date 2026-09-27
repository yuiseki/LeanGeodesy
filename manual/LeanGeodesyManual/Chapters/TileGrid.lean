import VersoManual
import LeanGeodesy

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The tile grid" =>

The projection chapter ended with Web Mercator drawing the world as a
square, $`256 \cdot 2^z` pixels wide at zoom $`z`. Web maps cut that square
into $`2^z \times 2^z` tiles of $`256 \times 256` pixels. This chapter
proves that a point's tile is well defined and that zooming in refines the
grid; the next chapter shows that this refinement is a quadtree.

```
Tile Grid
↓
Quadtree
↓
SpatialOrder
├─ Morton
└─ Hilbert
```

# Pixels

Each zoom level doubles the pixel coordinates, and every point of the square
lands on a pixel inside it.

{docstring Geodesy.Projection.pixel_mem}

{docstring Geodesy.Projection.pixelX_succ}

# The tile of a point

A point's tile is its pixel coordinate divided by 256, rounded down. The
tile contains the point's pixel, and the indices lie in $`0 .. 2^z - 1` on
the half-open square: the right edge, the antimeridian, and the bottom edge,
the southern cut-off, are excluded, where the index would be one past the
grid.

{docstring Geodesy.Projection.tileX}

{docstring Geodesy.Projection.tileX_spec}

{docstring Geodesy.Projection.tileX_lt}

{docstring Geodesy.Projection.tileX_halfExtent}

# Zooming in

Zooming in by one level doubles the pixel coordinates, so the tile at zoom
$`z + 1` halves, rounded down, to the tile at zoom $`z`, and is one of its
two children in each direction. That is what makes the tiles a quadtree.

{docstring Geodesy.Projection.tileX_succ_div_two}

{docstring Geodesy.Projection.tileX_succ_eq}
