# Toward Rust with lean-rs

This note records which definitions of LeanGeodesy could later be compiled to
Rust with [lean-rs](https://github.com/conao3/lean-rs), which theorems would
then describe the Rust functions, and what stands in the way. Nothing here is
generated or built yet: there is no Rust code in this repository, and CI does
not run lean-rs.

It was written against lean-rs at commit `90bdd9c` (generator version 3, Lean
`v4.35.0`), from its README and its sources (`LeanRust/Marshal.lean`,
`Main.lean`). lean-rs was not run on this library; every "expected" below is
read from that code, not observed.

## What lean-rs does, and what it guarantees

lean-rs compiles the IR that Lean's compiler produces for a module
(`Lean.Compiler.IR`) to Rust source that mirrors Lean's C backend
(`lean-rust module generate`, or `lean-rust project generate` for a whole
Lake package; `lean!` embeds Lean source in a Rust file). Theorems are not
compiled; they have no IR. What carries over is this: a generated function
computes what the Lean definition computes, so the theorems proved about that
definition describe the values the Rust function returns.

That transfer rests on things Lean does not check:

- lean-rs itself: its translation of the IR and its runtime (object layout,
  reference counting, `Nat` arithmetic) are tested against Lean's C backend,
  not proved;
- Lean's compiler, as for any compiled Lean code (`@[csimp]` replacements and
  `@[implemented_by]` are trusted);
- the hypotheses of each theorem: the functions return something on every
  input, but a theorem says nothing about inputs outside its hypotheses, and
  the Rust caller has to establish them;
- any hand-written Rust around the generated code, for example converting
  `lean_rust::Nat` to `u32`.

A definition becomes a public Rust function only if every argument and the
result have a Rust type: `Bool` and `Decidable p` (as `bool`), `Nat` and
`Int` (arbitrary precision), fixed-width integers, `Float`, `Char`, `String`,
`List`, `Array`, `Option`, `Except`, products, `Fin n` with `n` reducing to a
literal, and structures and inductive types built from these. lean-rs skips,
with a reason, a definition that has no IR (`noncomputable`), takes a proof
argument, uses a function type, a type variable, `Subtype`, a type family or
a type that is not an inductive type or holds one that is not (`ℝ` holds a
quotient of Cauchy sequences, `Set` is a predicate, `Finset` holds a
`Multiset`, which is a quotient), or takes an argument whose type has proof
fields. By default it exports the public
definitions written in a module, but not instances; others can be named with
`--roots`.

## Candidates

Every candidate is pure arithmetic on natural numbers, already separate from
the real-number geometry. "As is" means no change to the Lean code is needed.

| Definition | Expected Rust signature | Theorems that describe it | Status |
| --- | --- | --- | --- |
| `Geodesy.Tiles.childDigit` (`Tiles/Quadtree.lean`) | `(x: Nat, y: Nat) -> Nat` | `childDigit_lt`, `split`, `morton_mod_four` | as is |
| `Geodesy.Tiles.morton` (`Tiles/Morton.lean`) | `(z: Nat, x: Nat, y: Nat) -> Nat` | `mortonEquiv_val` (it is the bijection `mortonEquiv` on tiles), `morton_div_four`, `morton_mod_four`, `morton_eq_interleave`, `morton_jumps`, `morton_not_adjacent`; through `mortonEquiv_val`, `tile_path_morton_bijective`, `morton_ancestor_eq_iff_mem_interval`, `morton_subtree_eq_interval` | as is |
| `Geodesy.Tiles.quadPlace` (`Tiles/Hilbert.lean`) | `(n: Nat, q: Nat, p: (Nat, Nat)) -> (Nat, Nat)` | `quadPlace_zero` … `quadPlace_three`, `quadPlace_adj`, `quadPlace_inj`, `quadPlace_halve` | as is |
| `Geodesy.Tiles.hilbertD` | `(z: Nat, i: Nat) -> (Nat, Nat)` | `hilbertD_lt`, `hilbertD_zero`, `hilbertD_last`, `hilbertD_adj`, `hilbertD_inj`, `hilbertD_halve`, `hilbertE_hilbertD`; through `decode`, `hilbert_adjacent`, `parent_hilbert_decode`, `ancestor_decode` | as is |
| `Geodesy.Tiles.quadUnplace` | `(n: Nat, p: (Nat, Nat)) -> (Nat, (Nat, Nat))` | `quadUnplace_quadPlace`, `quadUnplace_spec` | as is |
| `Geodesy.Tiles.hilbertE` | `(z: Nat, p: (Nat, Nat)) -> Nat` | `hilbertE_lt`, `hilbertE_hilbertD`, `hilbertD_hilbertE`; through `encode`, `encode_decode`, `decode_encode`, `ancestor_eq_iff_encode_mem_interval` | as is |
| the `DecidableRel AdjN` instance (`Tiles/Adjacency.lean`) | `(p: (Nat, Nat), q: (Nat, Nat)) -> bool` | `AdjN.symm`, `AdjN.irrefl`, `hilbertD_adj` | instance with a generated name; must be named with `--roots`, not tried |
| `Geodesy.CRS.EPSG.Identifier`, `Identifier.toString`, `epsg4326`, `epsg3857` | a struct of `String` and `Nat`; `-> String` | none (two `example`s); they are labels, not proved to match the EPSG dataset | as is |

The hypotheses the Rust caller must establish are those of the theorems: for
`hilbertD z i`, `i < 4 ^ z`; for `hilbertE z p`, `p.1 < 2 ^ z ∧ p.2 < 2 ^ z`;
for `morton z x y` to be the code of a tile, `x, y < 2 ^ z`. Subtraction is
`Nat` subtraction (truncated at 0), as in Lean.

## Kept out, and why

- `Tile z`, `QuadPath z`, `split`, `parent`, `ancestor`, `tileEquivPath`,
  `mortonEquiv`, `pathEquivMorton`, `decode`, `encode`, `hilbertEquiv`,
  `Adjacent`, `SpatialOrder`, `mortonOrder`, `hilbertOrder`. `Tile z` is
  `Fin (2 ^ z) × Fin (2 ^ z)`, whose bound is not a literal; `QuadPath` is a
  function type; an `Equiv` has function and proof fields. They stay as they
  are: the bounds in the types are what the theorems are about. Their
  computation is that of the candidates above, by definition (`decode`,
  `encode`) or by theorems (`mortonEquiv_val`, `parent_val`, `ancestor_val`).
- No Morton decoder on natural numbers exists; the inverse is
  `(mortonEquiv z).symm`, on `Fin` types. Exporting one would need a new
  definition and a new theorem, which is not preparation.
- `tileIndex`, `tileX`, `tileY` and `tileOfPoint`: `noncomputable`, floor of
  a real number.
- Ellipsoids, geodetic coordinates, the first fundamental form, projections,
  distortion, geodesics, Helmert transformations and CRS conversions: all over
  `ℝ` (and `EuclideanSpace ℝ (Fin 3)`, `EuclideanSpace ℝ (Fin 2)`), mostly
  `noncomputable`, with no IR. A Rust implementation in `f64` would not inherit
  any theorem here: nothing relates floating-point arithmetic to `ℝ`, and this
  library does not replace `ℝ` by `Float` to make one.
- `CRS.EPSG.wgs84Geographic`, `CRS.EPSG.webMercator`: `noncomputable` (their
  values are real-number CRSs).

## Changes made for this

- `Tiles/Morton.lean` imported `Tiles.Grid`, and through it Web Mercator and
  Mathlib's real analysis, only for its last section, which relates Morton
  codes to the tile of a point. That section (`tileOfPoint`,
  `parent_tileOfPoint`, `morton_tileOfPoint_succ_div_four`,
  `tileOfPoint_surjective`) moved unchanged to `Tiles/TileOfPoint.lean`. Now
  `Tiles.Quadtree`, `Tiles.Morton`, `Tiles.Adjacency`, `Tiles.Hilbert` and
  `Tiles.SpatialOrder` import no real-number geometry, so a Lean package that
  compiles the candidates does not have to build it. Names, statements and
  proofs are unchanged; `Tiles.Morton` and `Tiles.Hilbert` now import the
  tactics they use (`ring`, `linarith`, `interval_cases`), which used to
  arrive through Web Mercator. `import LeanGeodesy` gives the same
  declarations. A
  file that imports `LeanGeodesy.Tiles.Morton` alone and uses `tileOfPoint`
  must now import `LeanGeodesy.Tiles.TileOfPoint`.

## Open before starting

- Toolchain. lean-rs is pinned to Lean `v4.35.0`, and `lean-rust` reads the IR
  stored in `.olean` files built by its own Lean version. LeanGeodesy,
  LeanComputationalGeometry and LeanGeospatial are on Lean `v4.34.0` and
  Mathlib `v4.34.0`. Generating Rust needs the three upgraded together (see
  `AGENTS.md`) or a lean-rs for `v4.34.0`; neither was done here.
- Not tried: running `lean-rust module generate` on `LeanGeodesy.Tiles.Hilbert`
  and `LeanGeodesy.Tiles.Morton` with `--output json`, which lists exported
  and skipped definitions; whether the anonymous `AdjN` instance is accepted
  through `--roots`; whether the runtime has every extern the Mathlib-built IR
  calls (exit code 254 means it does not).
- `Nat` in Rust is `lean_rust::Nat`. Narrowing to `u32` or `u64` is ordinary
  Rust, outside the theorems.
