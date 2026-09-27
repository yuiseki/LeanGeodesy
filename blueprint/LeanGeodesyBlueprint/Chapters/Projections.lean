import Verso
import VersoManual
import VersoBlueprint
import LeanGeodesy

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "From the reference ellipsoid to map projections" =>

Every statement below links to declarations already proved in LeanGeodesy;
nothing is restated here.

:::definition "reference_ellipsoid" (lean := "Geodesy.ReferenceEllipsoid, Geodesy.ReferenceEllipsoid.b, Geodesy.ReferenceEllipsoid.e2, Geodesy.ReferenceEllipsoid.e2_eq, Geodesy.ReferenceEllipsoid.b_sq")
A reference ellipsoid is fixed by its semi-major axis $`a` and flattening $`f`.
The semi-minor axis is $`b = a (1 - f)` and the first eccentricity squared is
$`e^2 = f (2 - f) = (a^2 - b^2) / a^2`.
:::

:::theorem "curvature" (lean := "Geodesy.ReferenceEllipsoid.meridianRadius, Geodesy.ReferenceEllipsoid.hasDerivAt_meridianPoint_fst, Geodesy.ReferenceEllipsoid.hasDerivAt_meridianPoint_snd, Geodesy.ReferenceEllipsoid.norm_meridianTangent_sq, Geodesy.ReferenceEllipsoid.inner_meridianTangent_parallelTangent, Geodesy.ReferenceEllipsoid.N_div_M")
At geodetic latitude $`\varphi` the meridian has radius of curvature
$`M = a (1 - e^2) / (1 - e^2 \sin^2 \varphi)^{3/2}` and the parallel has
radius $`N \cos \varphi`. The tangents to the meridian and the parallel are
perpendicular, of lengths $`M` and $`N \cos \varphi`, and
$`N / M = (1 - e^2 \sin^2 \varphi) / (1 - e^2)`.
This is derived from {uses "reference_ellipsoid"}[].
:::

:::proof "curvature"
Differentiate the meridian point $`(N \cos \varphi, N (1 - e^2) \sin \varphi)`
in $`\varphi`: the derivative is $`(-M \sin \varphi, M \cos \varphi)`, a vector
of length $`M`.
:::

:::theorem "first_fundamental_form" (lean := "Geodesy.ReferenceEllipsoid.firstFormE_eq, Geodesy.ReferenceEllipsoid.firstFormF_eq, Geodesy.ReferenceEllipsoid.firstFormG_eq, Geodesy.ReferenceEllipsoid.metric_self_eq_zero_iff, Geodesy.ReferenceEllipsoid.norm_dr_sq, Geodesy.ReferenceEllipsoid.speed_sq_curve")
In the coordinates $`(\varphi, \lambda)` the first fundamental form of the
ellipsoid is $`E = M^2`, $`F = 0`, $`G = (N \cos \varphi)^2`, so the line
element is $`ds^2 = M^2 d\varphi^2 + (N \cos \varphi)^2 d\lambda^2`. It is
positive definite away from the poles.
Its coefficients are the tangent lengths of {uses "curvature"}[].
:::

:::proof "first_fundamental_form"
The partial derivatives of the surface are the meridian and parallel
tangents, whose lengths and orthogonality are known.
:::

:::definition "local_distortion" (lean := "Geodesy.Projection.LocalDistortion, Geodesy.Projection.LocalDistortion.ofEllipsoid, Geodesy.Projection.LocalDistortion.tissot, Geodesy.Projection.LocalDistortion.isConformal_iff, Geodesy.Projection.isConformal_iff_firstForm, Geodesy.Projection.areaScale_ofEllipsoid")
A projection sends a step north and a step east to two vectors on the map.
Measured against the reference lengths $`\sqrt{E} = M` and
$`\sqrt{G} = N \cos \varphi` of {uses "first_fundamental_form"}[], they give
the scales $`h` and $`k`, the area scale
$`|\det| / \sqrt{E G - F^2}`, and Tissot's indicatrix. The projection is
conformal exactly when it multiplies the first fundamental form by $`h^2`.
:::

:::theorem "mercator" (lean := "Geodesy.Projection.hasDerivAt_mercatorY, Geodesy.Projection.mercatorY_eq_log_tan, Geodesy.Projection.mercator_isConformal")
Mercator's northing $`y = \operatorname{arsinh} (\tan \varphi)
= \ln \tan (\pi/4 + \varphi/2)` has derivative $`\sec \varphi`, and the
projection is conformal in the sense of {uses "local_distortion"}[].
:::

:::proof "mercator"
On the sphere the steps north and east have lengths $`R` and $`R \cos \varphi`;
on the map they are perpendicular with lengths $`R \sec \varphi` and $`R`.
Both are stretched by the same factor $`\sec \varphi`.
:::

:::theorem "equal_area" (lean := "Geodesy.Projection.lambert_isEqualArea, Geodesy.Projection.lambertCylindrical_preserves_cellArea, Geodesy.Projection.mercator_enlarges_cellArea, Geodesy.Projection.webMercator_not_isEqualArea")
Lambert's cylindrical equal-area projection has area scale $`1` in the sense
of {uses "local_distortion"}[], and keeps the area of every cell. Mercator
enlarges every cell north of the equator, and Web Mercator is equal-area
nowhere on a flattened ellipsoid.
:::

:::proof "equal_area"
A cylindrical projection with northing $`R\,g(\varphi)` has area scale
$`g'(\varphi) / \cos \varphi`, which is $`1` for $`g = \sin`. Integrating,
a cell has area $`R^2 (\lambda_2 - \lambda_1)(\sin \varphi_2 - \sin \varphi_1)` on
both the sphere and the map, while Mercator's $`\operatorname{arsinh} (\tan \varphi) - \sin \varphi`
is strictly increasing.
:::

:::theorem "azimuthal" (lean := "Geodesy.Projection.azimuthalEquidistant_preserves_azimuth, Geodesy.Projection.azimuthalEquidistant_preserves_distanceFromCentre, Geodesy.Projection.azimuthalEquidistant_not_isConformal, Geodesy.Projection.azimuthalEquidistant_not_isEqualArea")
The azimuthal equidistant projection centred on the pole keeps azimuths and
great-circle distances from the centre. Measured by
{uses "local_distortion"}[], it is neither conformal nor equal-area.
:::

:::proof "azimuthal"
The point is drawn at $`R` times the horizontal part of the initial velocity
of the great-circle arc from the pole. Its scale is $`1` along meridians and
$`(\pi/2 - \varphi) / \cos \varphi > 1` along parallels.
:::
