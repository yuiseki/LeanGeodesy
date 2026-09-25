# LeanGeodesy

Machine-checked foundations of geodetic coordinates and map projections, in
Lean 4 with Mathlib.

A GPS receiver reports a latitude, a longitude and a height, and a web map
draws them with Web Mercator. This library proves, from the definitions up,
what those numbers mean: which ellipsoid they refer to, why latitude and
longitude are different kinds of quantity, how they name a point in space,
what a projection keeps and distorts when it draws that point flat, and
what a coordinate reference system is. It is written to understand the
principles behind GIS, not to compute with them, so every statement is a
theorem about real numbers and nothing is evaluated in floating point.

The whole library is proved with no `sorry`, no `admit` and no `axiom` of its
own (see [Axiom audit](#axiom-audit)).

## Layers

Each layer uses only the ones above it.

```
Angle
  ↓
Sphere / Ellipsoid            (Surface.lean)
  ↓
ReferenceEllipsoid
  ↓
WGS84
  ↓
GeodeticLatitude  GeodeticLongitude
  ↓
GeodeticCoordinate
  ↓
Curvature
  ↓
Projection.Mercator
  ↓
Projection.WebMercator        Geodesic
  ↓
CRS
```

`Geodesic` uses only the layers up to `GeodeticCoordinate` (and the sphere
point of `Projection.Mercator`), so it sits beside the projections.

### Angle

Coordinates are published in degrees, often as degrees, minutes and seconds,
while trigonometry works in radians. `degToRad` and `radToDeg` are inverse to
each other (`radToDeg_degToRad`, `degToRad_radToDeg`), additive and strictly
increasing, so converting never reorders or merges angles. `dms d m s` reads
degrees, minutes and seconds, and `dms_carry` proves that 60 minutes carry
into one degree and 60 seconds into one minute.

### Sphere and ellipsoid

Space is `EuclideanSpace ℝ (Fin 3)`, with `vec3 x y z` for a point. A sphere
of radius `R` is the set of points at distance `R` from the centre. An
ellipsoid of revolution with equatorial radius `a` and polar radius `b` is

```
(x² + y²) / a² + z² / b² = 1
```

and `ellipsoid_self` proves that an ellipsoid with equal radii is exactly the
sphere of that radius. The rest of the library works on the ellipsoid, and
this is the bridge back to the spherical picture.

### ReferenceEllipsoid

A geodetic datum fixes its ellipsoid by two numbers, the semi-major axis `a`
and the flattening `f`. Everything else is derived:

| Quantity | Definition | Proved equal to |
| --- | --- | --- |
| polar radius `b` | `a (1 - f)` | |
| flattening `f` | field | `(a - b) / a` (`f_eq`) |
| first eccentricity squared `e²` | `f (2 - f)` | `(a² - b²) / a²` (`e2_eq`) |
| second eccentricity squared `e'²` | `e² / (1 - e²)` | `(a² - b²) / b²` (`ep2_eq`) |

`b_sq : b² = a² (1 - e²)` is the relation every later formula uses.
`isSphere_tfae` proves that `f = 0`, `b = a`, `e² = 0` and "the surface is
the sphere of radius `a`" are four ways of saying the same thing.

### WGS84

WGS 84, the datum of GPS, defines `a = 6378137 m` and
`1 / f = 298.257223563` (NGA.STND.0036, Table 3.1). With exact rational
arithmetic the library proves the derived values that tables usually just
list:

- polar radius `6356752.3142 m < b < 6356752.3143 m` (`wgs84_b_bounds`);
- `0.00669437999014 < e² < 0.00669437999015` (`wgs84_e2_bounds`);
- the Earth is flattened by between 21384 m and 21385 m (`wgs84_a_sub_b`).

GRS 80, the ellipsoid of ITRF-based datums such as Japan's JGD2011, has the
same `a` and `1 / f = 298.257222101`. `wgs84_b_sub_grs80_b` proves that the
two polar radii differ by between 0.1 mm and 0.2 mm, which is why the two
ellipsoids are interchangeable for mapping.

### GeodeticLongitude

Longitude wraps around: 190° east is 170° west. So a longitude is not a real
number but an angle modulo a full turn, which is Mathlib's `Real.Angle`.
Published longitudes pick one representative in `(-180°, 180°]`
(`toDegrees_mem`), and a value already in that range is read back unchanged
(`toDegrees_ofDegrees`). The antimeridian shows the convention: 180° east
and 180° west are the same longitude (`antimeridian`), and it is published
as 180 (`toDegrees_ofDegrees_neg180`).

### GeodeticLatitude

Latitude does not wrap, so it is a real number in `[-π/2, π/2]`. On an
ellipsoid there are two latitudes, and the one on maps is not the one seen
from the centre:

- the geodetic latitude `φ` is the angle between the equatorial plane and
  the ellipsoid's normal at the point, the direction a plumb line would hang
  if gravity were perpendicular to the ellipsoid;
- the geocentric latitude `ψ` is the angle between the equatorial plane and
  the line from the centre to the point.

In a meridian plane the point at geodetic latitude `φ` is

```
p = N cos φ,   z = N (1 - e²) sin φ,   N = a / √(1 - e² sin² φ)
```

with `N` the prime vertical radius of curvature. The library proves that

- this point lies on the meridian ellipse (`meridianPoint_mem`);
- the ellipse's normal there points in direction `(cos φ, sin φ)`, so its
  angle is indeed `φ` (`meridianNormal_eq`);
- its geocentric latitude satisfies `tan ψ = (1 - e²) tan φ`
  (`geocentric_tan`);
- on a sphere the two latitudes agree (`geocentric_tan_of_sphere`), and on a
  flattened ellipsoid `|tan ψ| ≤ |tan φ|`, so the geocentric latitude is
  never further from the equator (`abs_geocentric_tan_le`);
- `N = a` at the equator and `N = a² / b` at the poles
  (`primeVerticalRadius_zero`, `primeVerticalRadius_pi_div_two`).

### GeodeticCoordinate

A geodetic coordinate is a latitude, a longitude and an ellipsoidal height
`h`. It names a point in Earth-centred, Earth-fixed (ECEF) coordinates:

```
x = (N + h) cos φ cos λ
y = (N + h) cos φ sin λ
z = (N (1 - e²) + h) sin φ
```

The theorems say what makes these coordinates geodetic:

- at `h = 0` the point lies on the ellipsoid (`surfacePoint_mem`);
- the ellipsoid's normal there is a positive multiple of the unit vector `n`
  with elevation `φ` and azimuth `λ` (`gradient_eq`, `norm_normal`);
- the point at height `h` is `h` metres from the surface point along `n`
  (`toECEF_eq`), so height is measured along the normal, not towards the
  centre;
- on a sphere of radius `R` the point is `(R + h) n` (`toECEF_of_sphere`),
  at distance `R + h` from the centre (`norm_toECEF_of_sphere`).

### Curvature

At a point of the ellipsoid the surface curves differently along the
meridian and across it. Across it the radius is `N`; along it the radius is

```
M = a (1 - e²) / (1 - e² sin² φ)^(3/2)
```

which the library derives rather than states: differentiating the meridian
point `(N cos φ, N (1 - e²) sin φ)` in `φ` gives `(-M sin φ, M cos φ)`
(`hasDerivAt_meridianPoint_fst`, `hasDerivAt_meridianPoint_snd`). In space
the tangent to the meridian has length `M`, the tangent to the parallel has
length `N cos φ`, and the two are perpendicular. Their ratio is
`N / M = (1 - e² sin² φ) / (1 - e²)` (`N_div_M`).

### Projection.Mercator

Mercator keeps longitude as the easting and stretches latitude into the
northing `y = arsinh (tan φ) = ln (tan (π/4 + φ/2))` (`mercatorY`,
`mercatorY_eq_log_tan`). The library proves that

- `y` is a strictly increasing, odd bijection from the open latitudes
  `(-π/2, π/2)` onto the real line, inverted by the Gudermannian function
  `gd y = arctan (sinh y)` (`mercatorY_bijOn`, `gd_mercatorY`,
  `mercatorY_gd`);
- `y` tends to infinity at the pole, so the poles can never be drawn
  (`tendsto_mercatorY_pi_div_two`);
- its derivative is `sec φ` (`hasDerivAt_mercatorY`).

On a sphere of radius `R` the tangents to the meridian and the parallel
have lengths `R` and `R cos φ`; on the map their images have lengths
`R sec φ` and `R`. Both are stretched by `sec φ`, and since both pairs are
perpendicular, every direction is stretched by exactly `sec φ`
(`conformal`). That is what conformal means. Scale still grows with
latitude: distances double at 60° (`scaleFactor_60`) and areas quadruple,
which is why Greenland looks as large as Africa.

### Projection.WebMercator

Web Mercator (EPSG:3857), the projection of OpenStreetMap and most web maps,
applies the spherical formulas to WGS 84 latitude and longitude on a sphere
of radius `a = 6378137 m`.

- Eastings fill `(-π a, π a]` (`x_mem`), with
  `20037508.34 m < π a < 20037508.35 m` (`halfExtent_bounds`).
- The map is cut off at `maxLatitude = gd π`, the latitude whose northing
  is `π a` (`y_maxLatitude`), and a latitude is inside the map exactly when
  it is within that cut-off (`y_mem_iff`). So the world is a square, which
  is what lets it be cut into square tiles. The cut-off is between 85.05°
  and 85.06° (`maxLatitude_deg_bounds`): its cosine is `1 / cosh π`
  (`cos_maxLatitude`), `e^π` is between 23.14 and 23.15 by the Taylor series
  (`exp_pi_bounds`), and `cos 85.05° = sin 4.95°` and `cos 85.06° = sin 4.94°`
  are bounded the same way.
- At zoom `z` the square is `256 · 2^z` pixels wide; every point of it lands
  on a pixel (`pixel_mem`), and each zoom level doubles pixel coordinates
  (`pixelX_succ`).
- One pixel covers `2π a cos φ / (256 · 2^z)` metres of ground
  (`groundResolution_eq`), between 156543.03 m and 156543.04 m on the
  equator at zoom 0 (`groundResolution_zero_bounds`), and half as much at
  each further zoom level (`groundResolution_succ`).

Measured against the WGS 84 ellipsoid rather than the sphere, Web Mercator
is not conformal. It stretches the meridian `N / M` times as much as the
parallel (`scale_ratio`). That ratio is `1` on a sphere
(`meridianScale_eq_parallelScale_of_sphere`), greater than `1` between the
poles of any flattened ellipsoid (`meridianScale_gt_parallelScale`), and
between 1.006739 and 1.006740 on the WGS 84 equator
(`wgs84_equator_scale_ratio`). So a small circle on the Earth is drawn as an
ellipse elongated north to south by about 0.67 %.

### Geodesic

On a spherical Earth the shortest way between two places runs along a great
circle, and its length is the radius times the central angle, the angle
between the two places seen from the centre. The library defines the
central angle through the unit vectors of the two places (`direction`, the
same vector as the ellipsoid normal `GeodeticCoordinate.normal`) and proves

- the spherical law of cosines (`cos_centralAngle`) and the haversine
  formula (`haversine`);
- that the great-circle distance is a metric: symmetric, zero only between
  a place and itself, at most half the circumference, and satisfying the
  triangle inequality (`greatCircleDistance_comm`,
  `greatCircleDistance_eq_zero_iff`, `greatCircleDistance_le`,
  `greatCircleDistance_triangle`);
- the special cases: along a meridian the central angle is the difference
  in latitude and distances add up (`centralAngle_same_meridian`,
  `centralAngle_meridian_add`), along the equator it is the difference in
  longitude the shorter way round (`centralAngle_equator`), and the poles
  are antipodal (`centralAngle_poles`);
- that great circles are shortest. A path from `u` to `w` sampled at
  points in between turns through at least the central angle `θ`
  (`angle_le_sum_angle`, `greatCircleDistance_le_sum`), by the triangle
  inequality and induction. The great-circle arc
  `greatArc u w t = cos (t θ) u + sin (t θ) n`, with `n` the unit vector
  perpendicular to `u` towards `w`, runs from `u` to `w` on the sphere
  (`greatArc_zero`, `greatArc_one`, `norm_greatArc`), its points at
  fractions `s` and `t` are `|s - t| θ` apart (`angle_greatArc`), so
  however it is sampled in order the angles add up to exactly `θ`
  (`sum_angle_greatArc`). The points that make the triangle inequality an
  equality are exactly the points of the arc (`angle_add_angle_eq_iff`):
  splitting such a point along `u`, along `n` and the rest, equality forces
  the first two parts to be `cos α` and `sin α`, and the unit length leaves
  nothing for the rest;
- that the arc is the shortest curve. The length of a curve in a metric
  space is the supremum of such sums over all samplings in order
  (`angularLength`, valued in `ℝ≥0∞` since it may be infinite). Every curve
  from `u` to `w` is at least `θ` long (`angle_le_angularLength`), the arc
  is exactly `θ` long (`angularLength_greatArc`), and a curve on the sphere
  that is only `θ` long passes only through points of the arc
  (`mem_greatArc_of_angularLength_eq`);
- one minute of latitude on a 6371 km sphere is between 1853 m and 1854 m,
  which is where the nautical mile comes from (`arcMinute_bounds`).

The triangle inequality rests on the triangle inequality for angles between
unit vectors (`angle_le_angle_add_angle`), which Mathlib `v4.16.0` lists only
as `proof_wanted` and which is proved here.

### CRS

This layer does not formalise the EPSG specifications. It defines what a
coordinate reference system is as a mathematical object, and then
constructs WGS 84 and Web Mercator as examples of that definition.

- A `GeographicCRS` is given by its reference ellipsoid. Its coordinates
  are a geodetic latitude and longitude, and each one means a point of that
  ellipsoid (`GeographicCRS.toPoint_mem`), the ECEF position at height zero
  (`toPoint_eq_toECEF`).
- A `ProjectedCRS` is given by a geographic CRS, a domain of its
  coordinates, an image in the plane, and a forward map and an inverse
  that map each into the other and undo each other. The forward map is
  then a bijection from the domain onto the image (`forward_bijOn`), and
  projecting and unprojecting round-trip on each side
  (`unproject_project`, `project_unproject`).
- Coordinates carry their CRS in their type (`C.Coordinate`,
  `P.Coordinate`), so a coordinate cannot be read against the wrong system
  by accident.

The examples:

- `wgs84Geographic` is the geographic CRS on the WGS 84 ellipsoid.
- `webMercatorCRS` is the projected CRS over it whose forward map is
  `Projection.webMercator` (`webMercatorCRS_forward`) and whose inverse is
  built from `Projection.webMercatorInverse`. Its domain is the latitudes
  within `maxLatitude` (`webMercatorCRS_domain`), and a coordinate is in it
  exactly when its latitude is strictly between the poles and its
  projection lands in the square (`mem_webMercatorCRS_domain_iff`), which is
  the existing `Projection.y_mem_iff` seen from the CRS. The poles are
  outside it (`northPole_not_mem_webMercatorCRS_domain`).

A datum is modelled only by its ellipsoid. Its realisations, units, axis
order and areas of use are outside the definition.

EPSG identifiers are kept apart from all of this. `CRS/EPSG.lean` attaches
`EPSG:4326` to `wgs84Geographic` and `EPSG:3857` to `webMercatorCRS` as
labels saying which published definitions they are meant to correspond to.
A label is not a proof of that correspondence. No theorem uses an
identifier, no EPSG table or constant is assumed, and CI checks that no
other file refers to the labels.

## Scope

Geodesics on the ellipsoid, the agreement of the metric length above with
the arc length of smooth curves (the integral of speed), the inverse ECEF
conversion, datum transformations, transformations between CRSs, CRS
registries and projections other than Mercator are not covered yet.

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

## Files

| File | Contents |
| --- | --- |
| `LeanGeodesy/Angle.lean` | Degrees, radians, degrees-minutes-seconds |
| `LeanGeodesy/Surface.lean` | Points in space, spheres, ellipsoids of revolution |
| `LeanGeodesy/ReferenceEllipsoid.lean` | `a`, `f` and the derived `b`, `e²`, `e'²` |
| `LeanGeodesy/WGS84.lean` | WGS 84 and GRS 80, with bounds on derived values |
| `LeanGeodesy/GeodeticLongitude.lean` | Longitude as an angle modulo a full turn |
| `LeanGeodesy/GeodeticLatitude.lean` | Geodetic and geocentric latitude, the meridian ellipse |
| `LeanGeodesy/GeodeticCoordinate.lean` | Latitude, longitude, height and ECEF |
| `LeanGeodesy/Curvature.lean` | Meridian radius of curvature and the tangents of the ellipsoid |
| `LeanGeodesy/Projection/Mercator.lean` | The Mercator function, its inverse, and conformality on the sphere |
| `LeanGeodesy/Projection/WebMercator.lean` | EPSG:3857, the square world, tiles, and distortion on the ellipsoid |
| `LeanGeodesy/Projection/CutoffLatitude.lean` | The cut-off latitude is between 85.05° and 85.06° |
| `LeanGeodesy/Geodesic.lean` | Central angle, haversine, great-circle distance as a metric |
| `LeanGeodesy/CRS/Basic.lean` | Geographic and projected CRSs as mathematical objects |
| `LeanGeodesy/CRS/WGS84.lean` | The WGS 84 geographic CRS |
| `LeanGeodesy/CRS/WebMercator.lean` | The Web Mercator projected CRS over WGS 84 |
| `LeanGeodesy/CRS/EPSG.lean` | `EPSG:4326` and `EPSG:3857` as labels, used by no proof |
| `LeanGeodesy/Axioms.lean` | Axiom audit of the main theorems |
