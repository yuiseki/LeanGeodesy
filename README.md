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
GeodeticCoordinate ── ECEFInverse ── Helmert
  ↓
Curvature ── MeridianArc
  ↓
Projection.Mercator
  ↓
Projection.WebMercator        Geodesic
  ↓
Projection.Distortion ── Projection.Cylindrical ── Projection.TransverseMercator
  │                       └─ Projection.EqualArea
  └─ Projection.Azimuthal (with Geodesic)
  ↓
CRS (and CRS.Transformation, which uses ECEFInverse and Helmert)
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

### ECEFInverse

Going from an ECEF position back to latitude, longitude and height.

- The longitude is the argument of `x + y i` (`ecefLongitude_toECEF`).
- With `p = √(x² + y²)` the distance from the axis (`toECEF_p`), the
  latitude is a root of `p sin φ - z cos φ - e² N(φ) sin φ cos φ`
  (`latitudeResidual_toECEF`), the equation iterative methods solve, and
  given the latitude the height is
  `h = p cos φ + z sin φ - a √(1 - e² sin² φ)` (`height_eq`), with no
  division by `cos φ`.
- Every point of space has geodetic coordinates (`toECEF_surjective`): off
  the axis the latitude equation goes from `-p` at the south pole to `p` at
  the north pole, so it has a root by the intermediate value theorem, and
  the root with the height formula lands on the point; on the axis the point
  is straight above or below the north pole.
- On a sphere the inverse has the closed form latitude `arcsin (z / r)`,
  height `r - R` (`sphereInverse`), and it undoes `toECEF`
  (`sphereInverse_toECEF`).

That the latitude is unique for points above the ellipsoid is not proved.

### Helmert

Two reference frames place the Earth's centre, axes and metre slightly
differently, and ECEF positions in them are related by a Helmert
transformation `x' = t + s R x`, with `R` a rotation (a linear isometry of
determinant one).

- It multiplies all distances by `s` (`dist_apply`); two compose to a third
  (`comp_apply`) and each has an inverse (`inv_apply`, `apply_inv`).
- The seven-parameter form linearises the rotation as `v + r × v`
  (`smallRotation`). That is not a rotation: exactly
  `‖v + r × v‖² = ‖v‖² + ‖r × v‖²` (`norm_smallRotation_sq`), so lengths
  are kept only along the axis (`norm_smallRotation_eq_iff`), with
  `‖r × v‖² = ‖r‖² ‖v‖² - ⟪r, v⟫²` (`norm_cross_sq`). The stretch is at most
  `‖r‖² ‖v‖ / 2` (`norm_smallRotation_le`): for angles up to a microradian
  and points within 7000 km of the centre, at most 3.5 micrometres
  (`smallRotation_error_small`).

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

### MeridianArc

The distance along the meridian from the equator to latitude `φ` is
`m(φ) = ∫₀^φ M(ψ) dψ` (`meridianArc`). It has no closed form on an ellipsoid,
and geodetic software evaluates it by series; the library proves what the
integral says.

- `m` grows at rate `M` (`hasDerivAt_meridianArc`), so it is strictly
  increasing (`meridianArc_strictMono`), and it is odd (`meridianArc_neg`).
- On a sphere it is `a φ` (`meridianArc_of_sphere`).
- `M` runs from `b² / a` at the equator to `a² / b` at the poles
  (`meridianRadius_zero`, `meridianRadius_pi_div_two`,
  `meridianRadius_mem`), so `(b² / a) φ ≤ m(φ) ≤ (a² / b) φ` for `0 ≤ φ`
  (`meridianArc_bounds`).
- On a flattened ellipsoid `M` grows strictly towards the pole
  (`meridianRadius_strictMonoOn`), so a band of latitude of a given width
  is longer along the meridian the further it is from the equator
  (`meridianArc_band_lt`). On WGS 84 the first degree north of the equator
  is shorter than the last degree before the pole
  (`wgs84_first_degree_lt_last_degree`). Measuring exactly this, in Lapland
  and in Peru, is how the eighteenth century learned that the Earth is
  flattened.
- On WGS 84 the quarter meridian, from the equator to the pole, is between
  10001960 m and 10001975 m (`wgs84_quarterMeridian_bounds`). The metre was
  defined in 1791 as a ten-millionth of it, so the Earth turned out about
  0.02 % larger than intended. The proof squeezes `1 / s³`, with
  `s = √(1 - e² sin² ψ)`, between the second-order binomial series of
  `(1 - x)^(-3/2)` and that series plus `3 x³` (`inv_cube_bounds`, checked
  by factoring out `(1 - s)³`), and integrates the polynomials exactly with
  `∫₀^{π/2} sin² = π/4` and `∫₀^{π/2} sin⁴ = 3π/16` (`integral_poly_sin`,
  `quarterMeridian_bounds`).

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

### Projection.Distortion and Projection.Cylindrical

A projection sends a ground step north, of length `M` per unit latitude,
and a ground step east, of length `N cos φ` per unit longitude, to two
vectors on the map: its partial derivatives. Everything about its local
distortion follows from them (`LocalDistortion`).

- The scale along the meridian is `h`, along the parallel `k`, and the area
  scale is the determinant over `M N cos φ`.
- When the two images are perpendicular a small circle becomes an ellipse
  with semi-axes `h` and `k`, Tissot's indicatrix (`tissot`), and the area
  scale is `h k` (`areaScale_of_orthogonal`).
- A projection is conformal, stretching every step equally, exactly when
  the images are perpendicular and `h = k` (`isConformal_iff`); its area
  scale is then `h²` (`areaScale_of_isConformal`).

Cylindrical projections of the sphere, `x = R λ`, `y = R g(φ)`, have
`k = sec φ` always, `h = |g'(φ)|`, and area scale `|g'(φ)| sec φ`
(`cylindrical_k`, `cylindrical_h`, `cylindrical_areaScale`).

| Projection | `g(φ)` | `h` | `k` | area scale |
| --- | --- | --- | --- | --- |
| Mercator | `arsinh (tan φ)` | `sec φ` | `sec φ` | `sec² φ` |
| Plate carrée | `φ` | `1` | `sec φ` | `sec φ` |
| Lambert cylindrical equal-area | `sin φ` | `cos φ` | `sec φ` | `1` |

A cylindrical projection with north up and the equator on the `x` axis
that is conformal at every latitude is Mercator's
(`eq_mercatorY_of_isConformal`), one that is equal-area everywhere is
Lambert's (`eq_sin_of_isEqualArea`), and none is both at any latitude but
the equator (`eq_zero_of_isConformal_of_isEqualArea`). On an ellipsoid the
spherical Mercator formulas, as Web Mercator uses them, have scales
`a sec φ / M` and `a sec φ / N` and are not conformal
(`ellipsoidalMercator_not_isConformal`).

### What each projection keeps

`Projection.EqualArea` and `Projection.Azimuthal` add an equal-area and an
azimuthal projection, so that what each projection keeps and loses can be
compared as theorems. Each entry names the theorem.

| Projection | Angles (conformal) | Areas | Azimuths from the centre |
| --- | --- | --- | --- |
| Mercator, sphere | kept: `mercator_isConformal` | enlarged: `mercator_areaScale`, `mercator_enlarges_cellArea` | lost: `mercator_not_preserves_azimuth` |
| Web Mercator, WGS 84 | lost: `ellipsoidalMercator_not_isConformal` | enlarged everywhere: `webMercator_areaScale_gt_one`, `wgs84_webMercator_not_isEqualArea` | lost: `webMercator_not_preserves_azimuth` |
| Lambert cylindrical equal-area | lost off the equator: `lambertCylindrical_not_isConformal` | kept, locally and for every cell: `lambert_isEqualArea`, `lambertCylindrical_preserves_cellArea` | |
| Azimuthal equidistant, polar | lost: `azimuthalEquidistant_not_isConformal` | lost: `azimuthalEquidistant_not_isEqualArea` | kept: `azimuthalEquidistant_preserves_azimuth` |
| Transverse Mercator, sphere | kept: `tm_isConformal` | enlarged off the central meridian: `one_lt_tmScale` | |

The azimuthal equidistant projection centred on the north pole draws each
point exactly `R` times the horizontal part of the initial velocity of the
great-circle arc from the pole (`azimuthalEquidistant_preserves_azimuth`,
using `hasDerivAt_greatArc_zero` and `arcNormal_northPole`), so it also
keeps distances from the centre
(`azimuthalEquidistant_preserves_distanceFromCentre`) and along meridians
(`azimuthalEquidistant_h`), while stretching parallels by
`(π/2 - φ) / cos φ > 1` (`one_lt_azimuthalEquidistant_k`).

Cell areas are the integral of the area element `R · R cos φ`
(`sphereCellArea`, `sphereCellArea_eq`). Mercator's enlargement of cells
comes from `arsinh (tan φ) - sin φ` growing
(`mercatorY_sub_sin_strictMonoOn`). Web Mercator's area scale on the
ellipsoid is above `1` because `(1 - e²) cos² φ < (1 - e² sin² φ)²` when
`0 < e² ≤ 1/3`. Mercator fails to keep azimuths from `(45° N, 0°)` to
`(45° N, 90° E)`: the map line is due east, while the great circle leaves
with a northward component.

### Projection.TransverseMercator

Turning the sphere so that a chosen meridian plays the role of the equator
gives the transverse Mercator projection, the basis of UTM. With
`B = cos φ sin λ`, the sine of the distance from the central meridian,
`x = R · mercatorY (arcsin B)` and `y = R arctan (tan φ / cos λ)`
(`tmX`, `tmY`).

- On the central meridian `x = 0` and `y = R φ`: true to scale there
  (`tmX_central`, `tmY_central`).
- The partial derivatives are
  `R / (1 - B²) · (-sin φ sin λ, cos λ)` and
  `R cos φ / (1 - B²) · (cos λ, sin φ sin λ)`
  (`hasDerivAt_tmX_lat`, `hasDerivAt_tmX_lon`, `hasDerivAt_tmY_lat`,
  `hasDerivAt_tmY_lon`). They are perpendicular with both scales
  `1 / √(1 - B²)` (`tm_h`, `tm_k`), so the projection is conformal
  (`tm_isConformal`), with scale `1` on the central meridian growing away
  from it (`tmScale_central`, `one_lt_tmScale`).
- UTM multiplies the scale by `0.9996`. Within 3° of the central meridian
  the scale then stays between 0.9996 and 1.00098 (`utmScale_bounds`), and
  on the equator it is exact where `sin² λ = 1 - 0.9996²`, one line on each
  side of the central meridian (`utmScale_equator_eq_one_iff`).

This is the spherical transverse Mercator projection; the ellipsoidal one
used by UTM in practice (the Gauss-Krüger series) is not covered.

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

A transformation between two geographic CRSs (`CRSTransformation`) is a
Helmert transformation between their frames, applied to three-dimensional
coordinates (`Coordinate3D`): to ECEF on the source ellipsoid, through the
Helmert transformation, and back to latitude, longitude and height on the
target ellipsoid, which exists by `toECEF_surjective`. The transformed
coordinate names the moved point (`toPoint3D_transform`), transforming back
returns to the same point (`toPoint3D_inverse_transform`), and distances are
multiplied by the scale (`dist_transform`).

#### Converting EPSG:4326 and EPSG:3857

`CRS/WebMercatorConversion.lean` connects the two constructed CRSs in the
form GIS users need: EPSG:4326, the WGS 84 geographic 2D CRS (latitude and
longitude, no height), to and from EPSG:3857, the Web Mercator projected 2D
CRS. "WGS 84" alone names a datum, not a CRS; this is the geographic 2D CRS
on it.

- It is a coordinate conversion by a projection within one datum, not a
  Helmert transformation: no ECEF position is involved, and the formulas are
  `webMercatorCRS.forward` and `inverse`, reused.
- The valid inputs and outputs are types: WGS 84 coordinates within the
  cut-off latitude (`WebMercatorValidCoordinate`) and Web Mercator
  coordinates in the square (`WebMercatorImageCoordinate`). `toWebMercator`
  and `fromWebMercator` undo each other (`fromWebMercator_toWebMercator`,
  `toWebMercator_fromWebMercator`) and form a bijection (`webMercatorEquiv`,
  `webMercatorConversion_bijOn`).
- The equator and prime meridian go to `y = 0` and `x = 0`, the cut-off
  latitudes to the top and bottom edges, and the antimeridian to the right
  edge; no longitude reaches the left edge.
- Latitude and longitude are named fields here. Whether a file or an API
  writes a coordinate as `(lat, lon)` or `(lon, lat)` is a matter of
  serialisation, separate from what the CRS means, and is not modelled.
- Heights, EPSG:4979 (geographic 3D) and ECEF are outside this conversion.

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
the arc length of smooth curves (the integral of speed), the uniqueness of
the ellipsoidal ECEF inverse, published transformation parameters, CRS
registries, the ellipsoidal transverse Mercator projection and projections
other than the Mercator family are not covered yet.

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
| `LeanGeodesy/ECEFInverse.lean` | From ECEF back to latitude, longitude and height |
| `LeanGeodesy/Helmert.lean` | Helmert transformations and the linearised rotation |
| `LeanGeodesy/Curvature.lean` | Meridian radius of curvature and the tangents of the ellipsoid |
| `LeanGeodesy/MeridianArc.lean` | Meridian arc length as an integral of `M`, and its bounds |
| `LeanGeodesy/QuarterMeridian.lean` | The WGS 84 quarter meridian is 10001960 m to 10001975 m |
| `LeanGeodesy/Projection/Mercator.lean` | The Mercator function, its inverse, and conformality on the sphere |
| `LeanGeodesy/Projection/WebMercator.lean` | EPSG:3857, the square world, tiles, and distortion on the ellipsoid |
| `LeanGeodesy/Projection/CutoffLatitude.lean` | The cut-off latitude is between 85.05° and 85.06° |
| `LeanGeodesy/Projection/Distortion.lean` | Scales, area scale, Tissot's indicatrix, conformality |
| `LeanGeodesy/Projection/Cylindrical.lean` | Mercator, plate carrée and Lambert; uniqueness |
| `LeanGeodesy/Projection/EqualArea.lean` | Lambert's equal-area projection, cell areas, Web Mercator's area scale |
| `LeanGeodesy/Projection/Azimuthal.lean` | Azimuthal equidistant projection; Mercator does not keep azimuths |
| `LeanGeodesy/Projection/TransverseMercator.lean` | Spherical transverse Mercator, conformality, UTM scale |
| `LeanGeodesy/Geodesic.lean` | Central angle, haversine, great-circle distance as a metric |
| `LeanGeodesy/CRS/Basic.lean` | Geographic and projected CRSs as mathematical objects |
| `LeanGeodesy/CRS/WGS84.lean` | The WGS 84 geographic CRS |
| `LeanGeodesy/CRS/WebMercator.lean` | The Web Mercator projected CRS over WGS 84 |
| `LeanGeodesy/CRS/WebMercatorConversion.lean` | EPSG:4326 geographic 2D to and from EPSG:3857, as a bijection |
| `LeanGeodesy/CRS/Transformation.lean` | Transformations between geographic CRSs through ECEF |
| `LeanGeodesy/CRS/EPSG.lean` | `EPSG:4326` and `EPSG:3857` as labels, used by no proof |
| `LeanGeodesy/Axioms.lean` | Axiom audit of the main theorems |
