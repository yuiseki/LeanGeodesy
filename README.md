# LeanGeodesy

Machine-checked mathematics behind geodesy and GIS, in Lean 4 with Mathlib.

Latitude, longitude, ellipsoidal height, map projections, distances, bearings
and coordinate reference systems are defined from first principles, and what
GIS software relies on is proved about them as theorems over the real numbers.
Nothing is evaluated in floating point, and the library has no `sorry`, no
`admit` and no `axiom` of its own (see [Axiom audit](#axiom-audit)).

The full, layer-by-layer account is in [docs/REFERENCE.md](docs/REFERENCE.md).

## Why LeanGeodesy?

### For GIS practitioners

The library answers questions like these with theorems you can read from the
definitions up:

- Why does Web Mercator distort area, and by how much?
- Why are rhumb lines straight on a Mercator map?
- Why does a great-circle route differ from a constant-bearing route?
- What does an azimuthal equidistant projection preserve, and why is a
  buffer drawn with it exact?
- How is a datum transformation different from a map projection?
- What do latitude, longitude, ellipsoidal height, ECEF and a CRS mean?

Everyday formulas, such as the haversine distance, the rhumb-line distance,
Web Mercator's tile resolution or the UTM scale factor, appear as theorems
with their assumptions stated.

### For Lean and mathematics users

Geodesy is a compact piece of classical differential geometry with concrete
numbers attached. The library:

- embeds a reference ellipsoid in ℝ³ with geodetic latitude and longitude as
  coordinates;
- derives the first fundamental form from the partial derivatives of that
  embedding;
- obtains length, speed, angle and the area element from that one metric;
- combines it with a projection's derivative to describe local distortion,
  Tissot's indicatrix and conformality;
- combines the embedding with the geodesic condition to derive the affine
  geodesic equations in both coordinates;
- adds rotational symmetry to derive Clairaut's relation.

The geodesic equations and Clairaut's relation are not derived from the first
fundamental form alone: the proofs are extrinsic, using the embedding in ℝ³
and coordinate computation, not an intrinsic Koszul formula or Levi-Civita
connection.

## One mathematical spine

```
ReferenceEllipsoid (a, f)
  → M(φ), N(φ)                       radii of curvature
  → ∂r/∂φ, ∂r/∂λ                     tangents of the embedding in ℝ³
  → FirstFundamentalForm             E = M², F = 0, G = (N cos φ)²
       ├→ length / speed             ds² = M² dφ² + (N cos φ)² dλ²
       ├→ angle                      cos θ = g(u, v) / √(I(u) I(v))
       ├→ area element               dA = M N cos φ dφ dλ
       └→ projection distortion
              + projection derivative
              → h, k, Tissot, conformality, area scale

FirstFundamentalForm + E′, G′
  + embedded acceleration / geodesic condition
  → affine geodesic equations (latitude and longitude)
       + rotational symmetry
       → Clairaut relation
```

Separate lines of argument, not reduced to the first fundamental form:

```
spherical geometry in ℝ³           → great circles, central angle, shortest paths
Mercator + integration             → rhumb lines become straight lines
azimuthal projection + spheres     → centre distance and azimuth kept, exact buffers
integration and Lebesgue measure   → finite cell and buffer areas
ECEF / Helmert / CRS               → coordinate transformations and conversions
Web Mercator pixels + integers     → tile grid, quadtree, Morton and Hilbert orders
```

## What is actually proved?

A selection; [docs/REFERENCE.md](docs/REFERENCE.md) lists everything.

| Result | Theorem |
| --- | --- |
| `E = M²`, `F = 0`, `G = (N cos φ)²`, and `dA = M N cos φ dφ dλ` | `firstFormE_eq`, `firstFormG_eq`, `areaElement_eq` |
| A projection is conformal exactly when it multiplies the first fundamental form by `h²` | `isConformal_iff_firstForm` |
| Affine geodesics on the ellipsoid are exactly the solutions of the latitude and longitude equations | `isGeodesic_iff_equations` |
| Clairaut: `N cos φ sin A` is constant along a geodesic | `clairaut` |
| The great-circle arc is the shortest curve on a sphere | `angularLength_greatArc_le` |
| Constant bearing on the sphere is a straight line on Mercator | `constantBearing_iff_mercatorLine` |
| Lambert's cylindrical projection keeps the area of every latitude-longitude cell | `lambertCylindrical_preserves_cellArea` |
| EPSG:4326 geographic 2D and EPSG:3857 convert back and forth as a bijection | `webMercatorEquiv` |
| Web Mercator tiles at zoom `z`, quadtree paths of length `z` and Morton codes below `4^z` are in bijection | `tile_path_morton_bijective`, `mortonEquiv_eq_trans` |
| The Hilbert order visits every tile once and consecutive tiles share an edge; the Morton order does not | `hilbertEquiv`, `hilbert_adjacent`, `morton_not_adjacent` |

## What map projections keep and distort

On the sphere unless stated. "Local" means the scale factors at a point.

| Projection | Local angles | Area | Distance | Azimuth from a centre |
| --- | --- | --- | --- | --- |
| Mercator, sphere | kept between the poles (`mercator_isConformal`) | enlarged by `sec² φ` locally, and every cell north of the equator (`mercator_enlarges_cellArea`) | scale `sec φ`: 1 on the equator, 2 at 60° (`scaleFactor_60`) | not kept: 45° N 0° to 45° N 90° E (`mercator_not_preserves_azimuth`) |
| Web Mercator, WGS 84 | not kept: meridian stretched 1.00674 times the parallel at the equator (`wgs84_equator_scale_ratio`) | enlarged at every latitude (`webMercator_areaScale_gt_one`) | not examined | not kept: same example (`webMercator_not_preserves_azimuth`) |
| Lambert cylindrical equal-area | not kept off the equator (`lambertCylindrical_not_isConformal`) | kept locally and for every latitude-longitude cell (`lambertCylindrical_preserves_cellArea`) | scale `cos φ` on meridians, `sec φ` on parallels | not examined |
| Azimuthal equidistant, pole-centred | not kept off the pole (`azimuthalEquidistant_not_isConformal`) | not kept; every buffer of radius `0 < r < π R` enlarged (`azimuthalEquidistant_enlarges_buffer`) | kept from the centre (`azimuthalEquidistant_preserves_distanceFromCentre`) | kept from the pole only (`azimuthalEquidistant_preserves_azimuth`) |
| Transverse Mercator, sphere | kept for `|λ| < π/2` (`tm_isConformal`) | enlarged off the central meridian (`one_lt_tmScale`) | true scale only on the central meridian; UTM within `[0.9996, 1.00098)` within 3° (`utmScale_bounds`) | not examined |

## From GIS questions to theorems

| Question | Theorem |
| --- | --- |
| Why does Web Mercator distort area? | `webMercator_areaScale_gt_one` |
| Why is a rhumb line straight on Mercator? | `constantBearing_iff_mercatorLine` |
| How do a great circle and a rhumb line differ? | `greatCircleDistance_lt_rhumb_A_B` |
| What does an azimuthal equidistant buffer mean? | `image_geodesicCircle`, `image_geodesicDisk` |
| What does conformal mean mathematically? | `isConformal_iff_firstForm` |
| Why do tile indices form a quadtree, and what do Morton and Hilbert orders guarantee? | `parent_tileOfPoint`, `morton_eq_interleave`, `hilbert_adjacent` |
| How is a datum transformation different from a projection? | `toPoint3D_transform` (through ECEF and Helmert) versus `webMercatorEquiv` (within one datum) |

## Scope

Solving for ellipsoidal geodesics (existence, the direct and inverse
problems, geodesic distance), the agreement of the metric length above with
the arc length of smooth curves (the integral of speed), the uniqueness of
the ellipsoidal ECEF inverse, published transformation parameters, CRS
registries, the ellipsoidal transverse Mercator projection, ellipsoidal
rhumb lines, azimuthal projections centred off the pole, projections other
than those above, and the second fundamental form, shape operator, principal
curvatures and Gaussian curvature are not covered yet. The geodesic results
use the embedding in ℝ³; an intrinsic Levi-Civita connection is not
formalised.

## Build

```
lake exe cache get
lake build
```

Lean `v4.16.0`, Mathlib `v4.16.0`.

## Axiom audit

`LeanGeodesy/Axioms.lean` pins the main theorems to Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`, which come in through
Mathlib's real numbers) with `#guard_msgs`. Adding an axiom or leaving a
proof unfinished changes the printed axioms and fails `lake build`. CI also
rejects any `sorry` or `admit` in the sources, and any reference to the EPSG
labels outside `CRS/EPSG.lean`.

## Reference

The detailed account of every layer and the list of files are in
[docs/REFERENCE.md](docs/REFERENCE.md).
