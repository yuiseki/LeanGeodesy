import VersoManual
import LeanGeodesy

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Spatial orders: Morton and Hilbert" =>

A spatial index numbers the tiles of a zoom level with a single number
below $`4^z`, so that tiles close in the quadtree of the previous chapter
get close numbers. This chapter first says what every such numbering must
satisfy, and proves everything an index is used for from that alone. It
then builds the two numberings in use, Morton and Hilbert, and shows what
tells them apart.

```
SpatialOrder
├─ Morton
└─ Hilbert
```

# What a spatial order is

A spatial order numbers the tiles of every zoom level, one-to-one, so that
the number of a tile's parent is the tile's number divided by 4.

{docstring Geodesy.Tiles.SpatialOrder}

That one property is enough. The number of the ancestor $`k` generations up
is the number divided by $`4^k`, and a tile descends from $`s` exactly when
its number lies in one interval. So the subtree of every tile is one
interval of numbers, and a range query on it is an interval scan.

{docstring Geodesy.Tiles.SpatialOrder.index_ancestor}

{docstring Geodesy.Tiles.SpatialOrder.ancestor_eq_iff_mem_interval}

{docstring Geodesy.Tiles.SpatialOrder.subtree_eq_symm_interval}

What distinguishes orders is whether consecutive tiles share an edge.

{docstring Geodesy.Tiles.SpatialOrder.IsAdjacentOrder}

# Morton

A tile can be named three ways: by its column and row, by its quadtree path,
or by its Morton code, four times its parent's code plus its child digit.
The three are in bijection, and the triangle commutes. The Morton code
interleaves the bits of the column and the row: the Z-order curve.

{docstring Geodesy.Tiles.mortonEquiv}

{docstring Geodesy.Tiles.tile_path_morton_bijective}

{docstring Geodesy.Tiles.mortonEquiv_eq_trans}

{docstring Geodesy.Tiles.morton_eq_interleave}

The Morton order is a spatial order, but not an adjacent one: the Z-order
curve jumps.

{docstring Geodesy.Tiles.mortonOrder}

{docstring Geodesy.Tiles.mortonOrder_not_isAdjacentOrder}

# Hilbert

The Hilbert order visits the same tiles so that consecutive tiles always
share an edge. At zoom $`z + 1` the curve of zoom $`z` is placed in each
quadrant after a symmetry of the grid, and because the curve at every zoom
starts at $`(0, 0)` and ends at $`(2^z - 1, 0)`, the pieces join.

{docstring Geodesy.Tiles.quadPlace}

{docstring Geodesy.Tiles.hilbertD_zero}

{docstring Geodesy.Tiles.hilbertD_last}

{docstring Geodesy.Tiles.hilbert_adjacent}

The order visits every tile exactly once. The recursive encoder reads off
the quadrant and undoes its symmetry; it is computable, and neither it nor
the bijection uses the axiom of choice.

{docstring Geodesy.Tiles.hilbertEquiv}

{docstring Geodesy.Tiles.hilbertOrder}

{docstring Geodesy.Tiles.hilbertOrder_isAdjacentOrder}
