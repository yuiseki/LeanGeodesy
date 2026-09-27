import VersoManual
import LeanGeodesy

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The quadtree" =>

The tile grid chapter showed that a tile at zoom $`z + 1` halves to a tile
at zoom $`z`. This chapter forgets the map and keeps only that structure,
which is pure combinatorics on natural numbers: every tile has a parent and
four children, and a tile is the same thing as its path from the root. The
next chapter numbers the tiles along such paths.

# Tiles, parents and children

At zoom $`z` the tiles are the pairs $`(x, y)` with $`x, y < 2^z`. A tile at
zoom $`z + 1` has as parent $`(x / 2, y / 2)`, and is one of its four
children, told apart by the digit $`2 (y \bmod 2) + (x \bmod 2)`, the digit
of a Bing Maps quadkey. Splitting a tile into its parent and its digit is a
bijection.

{docstring Geodesy.Tiles.Tile}

{docstring Geodesy.Tiles.childDigit}

{docstring Geodesy.Tiles.split}

{docstring Geodesy.Tiles.card_children}

# Tiles are paths from the root

Repeating the split from the root, a tile at zoom $`z` is the same thing as
a path of $`z` child digits, coarsest first: the path of a tile is the path
of its parent followed by its own digit.

{docstring Geodesy.Tiles.QuadPath}

{docstring Geodesy.Tiles.tileEquivPath}

{docstring Geodesy.Tiles.tileEquivPath_succ}

# Ancestors

The ancestor $`k` generations up is the parent taken $`k` times, and its
column and row are divided by $`2^k`.

{docstring Geodesy.Tiles.ancestor}

{docstring Geodesy.Tiles.ancestor_val}

# Adjacent tiles

Two tiles are adjacent when they share an edge: they agree in one coordinate
and differ by one in the other. The next chapter compares spatial orders by
whether consecutive tiles are adjacent.

{docstring Geodesy.Tiles.Adjacent}
