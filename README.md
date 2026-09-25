# LeanGeodesy

Machine-checked foundations of geodetic coordinates, in Lean 4 with Mathlib.

A GPS receiver reports a latitude, a longitude and a height. This library
proves, from the definitions up, what those three numbers mean: which
ellipsoid they refer to, why latitude and longitude are different kinds of
quantity, and how they name a point in space. It is written to understand
the principles behind GIS, not to compute with them, so every statement is
a theorem about real numbers and nothing is evaluated in floating point.

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
```

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

## Scope

The library stops at geodetic coordinates. Distances and geodesics on the
sphere or ellipsoid, the inverse ECEF conversion, datum transformations and
map projections are outside it.

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
rejects any `sorry` or `admit` in the sources.

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
| `LeanGeodesy/Axioms.lean` | Axiom audit of the main theorems |
