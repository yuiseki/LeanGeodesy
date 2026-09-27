import VersoManual
import LeanGeodesy

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Ellipsoid geometry" =>

Before anything can be measured on the Earth, the Earth needs a shape and
positions on it need names. This chapter fixes both: the Earth is an
ellipsoid of revolution, and a place on it is named by a geodetic latitude,
a longitude and a height. Nothing here needs calculus yet; the next chapter,
on differential geometry, starts from the formulas set up here.

# Angles

Coordinates are published in degrees, often as degrees, minutes and seconds,
while trigonometry works in radians. Everything in the library is in
radians, and one degree is $`\pi / 180` radians.

{docstring Geodesy.degToRad}

{docstring Geodesy.dms}

# The shape: spheres and ellipsoids

Geodesy models the Earth by a surface with its centre at the origin and its
axis of rotation along $`z`. The simplest model is a sphere of radius $`R`.
A better one is an ellipsoid of revolution: the ellipse
$`p^2 / a^2 + z^2 / b^2 = 1` in a meridian plane, spun about the axis, with
$`a` the equatorial radius and $`b` the polar radius.

{docstring Geodesy.ellipsoid}

{docstring Geodesy.ellipsoid_self}

# Reference ellipsoids

A geodetic datum fixes its ellipsoid by two numbers, the semi-major axis
$`a` and the flattening $`f`. Everything else is derived from them: the
semi-minor axis $`b = a (1 - f)` and the first eccentricity squared
$`e^2 = f (2 - f) = (a^2 - b^2) / a^2`. A flattening of $`0` is a sphere; the
Earth's is about $`1/298`.

{docstring Geodesy.ReferenceEllipsoid}

{docstring Geodesy.ReferenceEllipsoid.b}

{docstring Geodesy.ReferenceEllipsoid.e2}

{docstring Geodesy.ReferenceEllipsoid.e2_eq}

{docstring Geodesy.ReferenceEllipsoid.isSphere_tfae}

# WGS 84

WGS 84, the datum of GPS, sets $`a = 6378137` m and $`1/f = 298.257223563`.
The library bounds the derived quantities with exact rational arithmetic,
and shows that GRS 80, the ellipsoid of ITRF-based datums, differs from it
by about a tenth of a millimetre in polar radius.

{docstring Geodesy.wgs84}

{docstring Geodesy.wgs84_b_sub_grs80_b}

# Longitude

Longitude is the angle east of the prime meridian. Going once around
brings you back, so a longitude is not a real number but an angle modulo a
full turn: Mathlib's `Real.Angle`. The antimeridian shows the convention:
180° east and 180° west are one longitude.

{docstring Geodesy.GeodeticLongitude}

{docstring Geodesy.GeodeticLongitude.antimeridian}

# Latitude

On an ellipsoid, the angle seen from the centre between a point and the
equator is the geocentric latitude $`\psi`, and it is not the latitude on
maps. The geodetic latitude $`\varphi` is the angle of the ellipsoid's
normal. In a meridian plane the point at geodetic latitude $`\varphi` is
$`(N \cos \varphi, N (1 - e^2) \sin \varphi)` with the prime vertical radius
$`N = a / \sqrt{1 - e^2 \sin^2 \varphi}`, and the two latitudes are related by
$`\tan \psi = (1 - e^2) \tan \varphi`.

{docstring Geodesy.ReferenceEllipsoid.primeVerticalRadius}

{docstring Geodesy.ReferenceEllipsoid.meridianPoint_mem}

{docstring Geodesy.ReferenceEllipsoid.meridianNormal_eq}

{docstring Geodesy.ReferenceEllipsoid.geocentric_tan}

# Geodetic coordinates

A latitude, a longitude and an ellipsoidal height name a point of space in
Earth-centred, Earth-fixed (ECEF) coordinates. At height $`0` the point lies
on the ellipsoid, and the height is measured along the ellipsoid's normal,
not towards the centre.

{docstring Geodesy.GeodeticCoordinate}

{docstring Geodesy.GeodeticCoordinate.toECEF}

{docstring Geodesy.GeodeticCoordinate.surfacePoint_mem}

{docstring Geodesy.GeodeticCoordinate.toECEF_eq}

# Along the meridian

The distance along the meridian from the equator to latitude $`\varphi` is
the integral $`m(\varphi) = \int_0^\varphi M(\psi)\, d\psi` of the meridian
radius of curvature $`M`, which the next chapter derives. It has no closed
form on an ellipsoid, but what it says can be proved: a degree of latitude
is shorter near the equator than near the poles, the measurement that showed
in the eighteenth century that the Earth is flattened.

{docstring Geodesy.ReferenceEllipsoid.meridianArc}

{docstring Geodesy.ReferenceEllipsoid.meridianArc_bounds}

{docstring Geodesy.wgs84_first_degree_lt_last_degree}

In 1791 the metre was defined as one ten-millionth of the quarter meridian.
On WGS 84 the quarter meridian is between 10001960 m and 10001975 m, so the
Earth came out about 0.02 % larger than the definition intended.

{docstring Geodesy.wgs84_quarterMeridian_bounds}
