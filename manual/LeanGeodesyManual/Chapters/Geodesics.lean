import VersoManual
import LeanGeodesy

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Geodesics" =>

The last chapter ended with a rhumb line that was not the shortest route.
This chapter asks what the shortest routes are. On a sphere they are great
circles, and that is proved from the geometry of unit vectors. On the
ellipsoid the question becomes the geodesic equations, which come out of the
first fundamental form of the differential geometry chapter, and they carry
a conservation law, Clairaut's relation.

# Great circles on the sphere

The great-circle distance between two places is the radius times the
central angle, the angle between them seen from the centre. It satisfies
the spherical law of cosines and the haversine formula that GIS software
evaluates, and it is a metric: symmetric, zero only between a place and
itself, and satisfying the triangle inequality.

{docstring Geodesy.Geodesic.centralAngle}

{docstring Geodesy.Geodesic.haversine}

{docstring Geodesy.Geodesic.greatCircleDistance_triangle}

The triangle inequality rests on the triangle inequality for angles between
unit vectors, proved in the library.

{docstring Geodesy.Geodesic.angle_le_angle_add_angle}

# Great circles are shortest

The length of a curve on the sphere is the supremum of the angles it turns
through, however it is sampled. The great-circle arc has length exactly the
central angle, no curve is shorter, and a curve that is as short runs along
the arc.

{docstring Geodesy.Geodesic.angularLength}

{docstring Geodesy.Geodesic.angularLength_greatArc}

{docstring Geodesy.Geodesic.angularLength_greatArc_le}

{docstring Geodesy.Geodesic.mem_greatArc_of_angularLength_eq}

One minute of latitude on a 6371 km sphere is about 1853 m, where the
nautical mile comes from.

{docstring Geodesy.Geodesic.arcMinute_bounds}

# The geodesic condition on the ellipsoid

A geodesic is a curve that does not turn within the surface: its
acceleration in space has no component along $`\partial r / \partial \varphi`
or $`\partial r / \partial \lambda`. This is the condition for an affinely
parametrised geodesic, so a geodesic also has constant speed.

{docstring Geodesy.ReferenceEllipsoid.EllipsoidCurve}

{docstring Geodesy.ReferenceEllipsoid.EllipsoidCurve.IsGeodesic}

{docstring Geodesy.ReferenceEllipsoid.EllipsoidCurve.geodesic_speed_const}

# The geodesic equations

The first fundamental form turns the condition into equations in
coordinates. With $`E = M^2` and $`G = (N \cos \varphi)^2` and their
derivatives from the differential geometry chapter,
$`E \varphi'' + \tfrac12 E' \varphi'^2 - \tfrac12 G' \lambda'^2 = 0` and
$`G \lambda'' + G' \varphi' \lambda' = 0`, and conversely the two equations
are exactly the geodesic condition.

{docstring Geodesy.ReferenceEllipsoid.EllipsoidCurve.geodesic_latitude_equation}

{docstring Geodesy.ReferenceEllipsoid.EllipsoidCurve.geodesic_longitude_equation}

{docstring Geodesy.ReferenceEllipsoid.EllipsoidCurve.isGeodesic_iff_equations}

# Clairaut's relation

Longitude does not appear in the metric, because the ellipsoid is a surface
of revolution, and that symmetry brings a conservation law: along a geodesic
$`(N \cos \varphi)^2 \lambda'` is constant. Together with constant speed, with
$`p = N \cos \varphi` the distance from the axis and $`A` the azimuth,
$`p \sin A` is constant, the form used in geodetic software.

{docstring Geodesy.ReferenceEllipsoid.EllipsoidCurve.clairaut_G_mul_lon'}

{docstring Geodesy.ReferenceEllipsoid.EllipsoidCurve.clairaut}

The parallels show where the conservation laws stop being enough: a parallel
run at constant speed satisfies both, yet it is a geodesic exactly when it
is the equator.

{docstring Geodesy.ReferenceEllipsoid.parallelCurve_isGeodesic_iff}
