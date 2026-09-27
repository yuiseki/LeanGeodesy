import VersoManual
import LeanGeodesy

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Coordinate reference systems" =>

A pair of numbers is not a position until it is said what the numbers are
measured against. A coordinate reference system (CRS) says it. This chapter
builds the two kinds of CRS a web map needs from the ellipsoid of the first
part and the projections of its third chapter, converts between EPSG:4326
and EPSG:3857, and shows how moving between datums differs: through ECEF
positions and a Helmert transformation, not through a projection.

# Geographic and projected CRSs

A geographic CRS fixes a reference ellipsoid; its coordinates are a geodetic
latitude and longitude, each meaning a point of that ellipsoid. A projected
CRS fixes a geographic CRS, a region of it, a region of the plane and a
projection between them with an inverse. Coordinates carry their CRS in
their type, so a coordinate cannot silently be read against the wrong
system.

{docstring Geodesy.GeographicCRS}

{docstring Geodesy.GeographicCRS.toPoint_mem}

{docstring Geodesy.ProjectedCRS}

{docstring Geodesy.ProjectedCRS.forward_bijOn}

# WGS 84 and Web Mercator as CRSs

The WGS 84 geographic CRS sits on the WGS 84 ellipsoid. The Web Mercator
projected CRS over it has as domain the latitudes within the cut-off of the
projection chapter, and as image the square world.

{docstring Geodesy.wgs84Geographic}

{docstring Geodesy.webMercatorCRS}

{docstring Geodesy.mem_webMercatorCRS_domain_iff}

# Converting EPSG:4326 and EPSG:3857

Both CRSs are on the same datum, so moving between them is a conversion by
a projection. The two directions undo each other, so they form a bijection
between the valid geographic coordinates and the square.

{docstring Geodesy.toWebMercator}

{docstring Geodesy.fromWebMercator}

{docstring Geodesy.webMercatorEquiv}

180° east and 180° west are one longitude, so the antimeridian is drawn once,
on the right edge.

{docstring Geodesy.toWebMercator_antimeridian}

{docstring Geodesy.toWebMercator_x_ne_left}

# EPSG identifiers are labels

The EPSG identifiers are attached to the constructed CRSs as labels. A label
records which published definition a CRS is meant to correspond to; it is
not a proof of that correspondence, and no theorem depends on it.

{docstring Geodesy.CRS.EPSG.Labelled}

{docstring Geodesy.CRS.EPSG.wgs84Geographic}

# From ECEF back to geodetic coordinates

The first chapter turned latitude, longitude and height into a point of
space. Going back, the longitude is the direction of the point's shadow on
the equator, the geodetic latitude is a root of the equation that iterative
methods solve, and every point of space has geodetic coordinates.

{docstring Geodesy.GeodeticCoordinate.ecefLongitude_toECEF}

{docstring Geodesy.GeodeticCoordinate.latitudeResidual_toECEF}

{docstring Geodesy.GeodeticCoordinate.height_eq}

{docstring Geodesy.toECEF_surjective}

# Helmert transformations

Two reference frames put the Earth's centre and axes in slightly different
places. The positions of one point in the two frames are related by a
Helmert transformation, a translation, a scale and a rotation. It multiplies
all distances by the scale, and these transformations compose and invert.

{docstring Geodesy.Helmert}

{docstring Geodesy.Helmert.dist_apply}

{docstring Geodesy.Helmert.comp}

{docstring Geodesy.Helmert.inv}

Published transformations use the linearised rotation $`v \mapsto v + r \times v`.
That is not a rotation, but for angles up to a microradian and points within
7000 km of the centre it is off by at most 3.5 micrometres.

{docstring Geodesy.smallRotation_error_small}

# Transformations between geographic CRSs

Moving a coordinate to another geographic CRS goes through space: to an
ECEF position on the source ellipsoid, through a Helmert transformation,
and back to latitude, longitude and height on the target ellipsoid. The
transformed coordinate names exactly the moved point, and transforming back
returns to the same point.

{docstring Geodesy.CRSTransformation}

{docstring Geodesy.CRSTransformation.toPoint3D_transform}

{docstring Geodesy.CRSTransformation.toPoint3D_inverse_transform}
