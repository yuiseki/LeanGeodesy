import VersoManual
import LeanGeodesy

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Projection" =>

A map projection sends the curved surface of the previous chapter to the
flat plane, and no projection can do that without distortion. This chapter
first says precisely what distortion is, using the first fundamental form,
and then examines the projections a GIS user meets: Mercator and Web
Mercator, Lambert's equal-area projection, the azimuthal equidistant
projection and the transverse Mercator projection behind UTM.

```
Local Distortion
      ↙   ↓   ↘
Mercator  Equal Area  Azimuthal
```

# Local distortion

At a point, a small step north has length $`M\, d\varphi` and a small step
east has length $`N \cos \varphi\, d\lambda`, and the two are perpendicular.
A projection sends them to two vectors on the map, its partial derivatives.
Everything about its local distortion follows from those two vectors: the
scale $`h` along the meridian, the scale $`k` along the parallel, the area
scale, and Tissot's indicatrix, the ellipse that a small circle becomes.

{docstring Geodesy.Projection.LocalDistortion}

{docstring Geodesy.Projection.LocalDistortion.tissot}

{docstring Geodesy.Projection.LocalDistortion.isConformal_iff}

The reference lengths are the square roots of the first fundamental form's
$`E` and $`G`. So conformality, keeping angles, is exactly preserving the
first fundamental form up to a scalar, and the area scale is the map's area
over the ellipsoid's area element.

{docstring Geodesy.Projection.LocalDistortion.ofEllipsoid}

{docstring Geodesy.Projection.isConformal_iff_firstForm}

{docstring Geodesy.Projection.areaScale_ofEllipsoid}

# Cylindrical projections and Mercator

A cylindrical projection keeps meridians as equally spaced vertical lines and
places the parallel at latitude $`\varphi` at height $`R\, g(\varphi)`. Every
parallel is drawn as long as the equator, so its scale is always
$`\sec \varphi`; the choice of $`g` decides the rest. Mercator's choice,
$`g(\varphi) = \operatorname{arsinh}(\tan \varphi)
= \ln \tan(\pi/4 + \varphi/2)`, has derivative $`\sec \varphi`, so both
scales agree and the projection is conformal.

{docstring Geodesy.Projection.cylindricalDistortion}

{docstring Geodesy.Projection.mercatorY_eq_log_tan}

{docstring Geodesy.Projection.hasDerivAt_mercatorY}

{docstring Geodesy.Projection.mercator_isConformal}

The condition on $`g'` fixes $`g`: a cylindrical projection that is
conformal at every latitude is Mercator's, one that is equal-area at every
latitude is Lambert's, and none is both away from the equator.

{docstring Geodesy.Projection.eq_mercatorY_of_isConformal}

{docstring Geodesy.Projection.eq_sin_of_isEqualArea}

Scale grows with latitude: distances double at 60° and areas quadruple,
which is why Greenland looks as large as Africa.

{docstring Geodesy.Projection.scaleFactor_60}

# Web Mercator

Web maps apply the spherical Mercator formulas to WGS 84 latitudes on a
sphere of radius $`a = 6378137` m. The poles are infinitely far away, so the
map is cut off where the northing reaches $`\pi a` and the world becomes a
square, a little short of 85.06°.

{docstring Geodesy.Projection.webMercator}

{docstring Geodesy.Projection.y_maxLatitude}

{docstring Geodesy.Projection.maxLatitude_deg_bounds}

At zoom $`z` the square is $`256 \cdot 2^z` pixels wide, and a pixel covers
$`2 \pi a \cos \varphi / (256 \cdot 2^z)` metres of ground. The second part
of this book cuts this square into tiles.

{docstring Geodesy.Projection.groundResolution_eq}

Web Mercator feeds ellipsoidal latitudes into spherical formulas, so on the
ellipsoid it is not quite conformal: it stretches the meridian more than the
parallel, by the ratio $`N / M` of the previous chapter, about 0.67 % at the
equator on WGS 84.

{docstring Geodesy.Projection.ellipsoidalMercator_not_isConformal}

{docstring Geodesy.Projection.wgs84_equator_scale_ratio}

# Equal area

Lambert's cylindrical equal-area projection takes $`g = \sin`. It keeps
areas locally, and also for every latitude-longitude cell, whose area on the
sphere is the integral of the area element of the previous chapter. Mercator
enlarges every cell north of the equator, and Web Mercator is equal-area
nowhere on a flattened ellipsoid.

{docstring Geodesy.Projection.lambert_isEqualArea}

{docstring Geodesy.Projection.lambertCylindrical_preserves_cellArea}

{docstring Geodesy.Projection.mercator_enlarges_cellArea}

{docstring Geodesy.Projection.webMercator_not_isEqualArea}

# Azimuthal equidistant and buffers

The azimuthal equidistant projection centred on the pole draws a point at
its great-circle distance from the centre, in the direction of the
great-circle arc from the centre to it. It keeps distances and azimuths from
the centre, and is neither conformal nor equal-area.

{docstring Geodesy.Projection.azimuthalEquidistant}

{docstring Geodesy.Projection.azimuthalEquidistant_preserves_distanceFromCentre}

{docstring Geodesy.Projection.azimuthalEquidistant_preserves_azimuth}

{docstring Geodesy.Projection.azimuthalEquidistant_not_isConformal}

This is why GIS libraries build a buffer by projecting azimuthally and
drawing a planar circle: the geodesic disk is drawn exactly as a Euclidean
disk. Its area is not kept; every buffer is drawn larger than it is.

{docstring Geodesy.Projection.image_geodesicDisk}

{docstring Geodesy.Projection.azimuthalEquidistant_enlarges_buffer}

Mercator does not keep azimuths from a centre: between two points on the
45th parallel the map displacement points due east, while the great circle
leaves with a northward component.

{docstring Geodesy.Projection.mercator_not_preserves_azimuth}

# Transverse Mercator and UTM

Turning the sphere a quarter turn, so that a chosen meridian plays the role
of the equator, gives the transverse Mercator projection: conformal, and
true to scale along the central meridian instead of the equator. UTM
multiplies it by $`0.9996`, which keeps the scale within
$`[0.9996, 1.00098)` across a whole 6° zone.

{docstring Geodesy.Projection.tm_isConformal}

{docstring Geodesy.Projection.tmScale_central}

{docstring Geodesy.Projection.utmScale_bounds}

# Rhumb lines

A rhumb line keeps a constant compass bearing. It is exactly what Mercator
draws as a straight line, the property that made Mercator's map a
navigation chart.

{docstring Geodesy.Projection.constantBearing_iff_mercatorLine}

{docstring Geodesy.Projection.rhumb_curveLength}

A rhumb line is not the shortest route. Between 45° N 0° and 45° N 90° E the
great circle is shorter, and a web map's scaled distance between the two
measures the rhumb line, not the great circle. The next chapter proves that
great circles are always shortest.

{docstring Geodesy.Projection.greatCircleDistance_lt_rhumb_A_B}

{docstring Geodesy.Projection.mercator_distance_scaled_A_B}
