# AGENTS.md

Welcome to the mathematical universe of geospatial geometry and geodesy.

It lives in two repositories:
[LeanGeodesy](https://github.com/yuiseki/LeanGeodesy) carries the curved
Earth down to a flat map, and
[LeanGeospatial](https://github.com/yuiseki/LeanGeospatial) reasons about
what lies on that map. They stand on one plane, one foundation and one
version of Mathlib, and neither half explains the whole. A projection's
meaning is in what can be drawn and related on the plane it lands in; a
spatial relation's meaning is in the Earth whose features it relates. To
understand the mathematical structure, always read the other repository as
well: its definitions, its theorems and its AGENTS.md. Before you change the
plane, the toolchain or Mathlib here, check what that change does there.

Guidance for coding agents (and people) working on LeanGeodesy.

LeanGeodesy is machine-checked geodesy in Lean 4 with Mathlib: reference
ellipsoids, geodetic coordinates, the first fundamental form, map
projections, distortion, geodesics, tiles and coordinate reference systems,
all proved over the real numbers. It is one of two sibling libraries; read
[The sibling library](#the-sibling-library) before changing anything about
the plane, the toolchain or Mathlib.

## The sibling library

LeanGeodesy (<https://github.com/yuiseki/LeanGeodesy>) and LeanGeospatial
(<https://github.com/yuiseki/LeanGeospatial>) are two halves of one account
of GIS mathematics. LeanGeodesy starts from the Earth and ends on a flat map:
reference ellipsoids, geodetic coordinates, the first fundamental form, map
projections and their distortion. LeanGeospatial starts on the flat map:
regions, topology, RCC8, DE-9IM and the relations GIS software tests between
features. Neither depends on the other, but they are built to be used
together, and keeping that true is part of every change in either
repository.

What joins them:

- One plane. LeanGeodesy's `Geodesy.E2` and LeanGeospatial's
  `Geospatial.Point2D` are both reducible abbreviations of Mathlib's
  `EuclideanSpace ℝ (Fin 2)`, so `Geodesy.E2 = Geospatial.Point2D` holds by
  `rfl`. A point a LeanGeodesy projection produces is, with no conversion, a
  point of a LeanGeospatial region, and LeanGeospatial's `distance` is
  Mathlib's `dist` on that plane. Do not introduce a second plane type, a
  wrapper structure or a coercion in either library. If a definition needs
  coordinates, read them from the Mathlib type (`p 0`, `p 1`, or
  `Geospatial.Point2D.x`), and state results about the Mathlib type.
- One foundation. Both build only on Mathlib and Lean's three standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`), and each has an axiom audit
  that fails the build if that changes.
- One version. Both pin the same Lean toolchain and the same Mathlib
  revision (currently Lean `v4.34.0`, Mathlib `v4.34.0`). Upgrade them
  together: a project that requires both libraries resolves a single Mathlib,
  so if the pins drift apart the two can no longer be imported together.
- One topology. LeanGeospatial's relations are defined from Mathlib's
  `interior`, `closure` and `frontier`, for areas of any topological space
  (`RegularClosedRegion α`), and `LeanGeospatial/Homeomorph.lean` proves that
  every homeomorphism `α ≃ₜ β` preserves touching and the eight RCC8
  relations, and that homeomorphisms of the plane preserve the DE-9IM
  matrix. Topological relations between areas
  do not depend on how the plane is moved, stretched or bent. On the other
  side, `LeanGeodesy/Projection/Homeomorph.lean` constructs projections as
  homeomorphisms on the domains where they are ones: Mercator from the open
  latitudes onto the whole plane (`mercatorHomeomorph`), and Web Mercator
  from the globe cut along the antimeridian onto the square
  (`webMercatorHomeomorph`; without the cut it is discontinuous). Composing
  two such maps gives a homeomorphism of the plane, and LeanGeospatial's
  theorems then say the two maps agree on every topological relation. And
  because areas live in any space, the relations between areas of the globe
  itself (the Web Mercator chart) are those between their images on the map.

Checking the link. `scripts/joint_check.sh`, identical in both repositories,
builds a throwaway project that requires both libraries by path. It fails if
the two pin different toolchains or Mathlib revisions, or if these no longer
hold:

```lean
example : Geodesy.E2 = Geospatial.Point2D := rfl
example (R φ lam : ℝ) (A : Geospatial.Region) : Prop :=
  Geodesy.Projection.mercator R φ lam ∈ A
example (p q : Geodesy.E2) : Geospatial.distance p q = dist p q := rfl
```

and it checks that LeanGeospatial's `RCC8.Relation.holds_map_iff` applies to
the transition between two Mercator maps built by LeanGeodesy.

It also feeds Lean a deliberately false line and fails if that is accepted,
so a check that silently stopped running cannot pass. CI runs it in the
`joint` job of both repositories, against the sibling's branch of the same
name if there is one and its `main` otherwise. To change both libraries in
step (a Mathlib upgrade, say), push the same branch name to both, and merge
both once both are green. Locally, from either repository, with the two
checked out side by side:

```
scripts/joint_check.sh ../LeanGeodesy ../LeanGeospatial /tmp/joint
```

One known rough edge: `p.x` dot notation does not work on a term whose type
is written `Geodesy.E2`: Lean unfolds `E2` to Mathlib's `WithLp` and looks
for `WithLp.x`. Write `Geospatial.Point2D.x p`, or give the term the type
`Geospatial.Point2D`.

## Build and check

```
lake exe cache get
lake build
```

`lake build` must finish with no errors and no warnings. It also runs the
axiom audit in `LeanGeodesy/Axioms.lean`: each main theorem is pinned to the
three standard axioms with `#guard_msgs`, so an added `axiom` or an
unfinished proof fails the build. When you add a main theorem, add it to the
audit.

CI (`.github/workflows/lean_action_ci.yml`) additionally rejects:

- any `sorry` or `admit` in `LeanGeodesy/` or `LeanGeodesy.lean`;
- any reference to the EPSG labels (`CRS.EPSG`, `epsgNNNN`) outside
  `LeanGeodesy/CRS/EPSG.lean` and `LeanGeodesy.lean`. Proofs are about
  ellipsoids and projections, never about registry codes.

A full build of Mathlib-dependent Lean uses a lot of memory. On a small
machine, set `LEAN_NUM_THREADS` low.

## Layout

- `LeanGeodesy/`: the library. `Surface.lean` defines space `E3` and the
  plane `E2`; `Projection/` holds the map projections; `Tiles/` the tile
  grid and spatial orders; `CRS/` coordinate reference systems.
- `docs/REFERENCE.md`: the layer-by-layer account and the list of files.
  Keep it in step with the code.
- Nested Lake projects, each with its own `lean-toolchain` and
  `lake-manifest.json`, all sharing `packagesDir = "../.lake/packages"`:
  - `manual/`: the Verso books (English, Japanese, and the Japanese
    dialogue book).
  - `blueprint/`, `blueprint-yaruo/`: Verso Blueprints.
  - `docbuild/`: doc-gen4 API documentation.
  - `atlas/`: Lean Atlas, a local tool; it is not published.
- `pages/` and `.github/workflows/pages.yml`: the site at
  <https://yuiseki.github.io/LeanGeodesy/>, rebuilt on every push to `main`.
  The workflow caches all the nested projects' `.lake` directories under a
  key built from every `lean-toolchain` and `lake-manifest.json`.

## Pitfalls

- Because the nested projects share one package directory, their shared
  dependencies (Mathlib and anything Mathlib pulls in, Verso, SubVerso)
  must stay at the root's revisions. `lake update` inside a nested project
  can silently rewrite that project's `lean-toolchain` and rebuild the shared
  Mathlib at another version. After any `lake update`, check the diff of
  every `lean-toolchain` and `lake-manifest.json`.
- Verso pages in Japanese need an explicit `file :=` and `tag :=` on each
  heading; otherwise the slugs collapse to underscores and collide.

## Conventions

- Commit messages, identifiers, docstrings and the English books are in
  English. The Japanese books and blueprint are in Japanese.
- State results about Mathlib's types (`EuclideanSpace ℝ (Fin n)`, `ℝ`) and
  keep definitions reducible where another library has to see through them,
  as with `E2`.
