import VersoManual
import LeanGeodesy

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "LeanGeodesy: from the reference ellipsoid to map projections" =>
%%%
shortTitle := "LeanGeodesy"
%%%

How the local distortion of map projections is derived from the reference
ellipsoid. Every declaration shown here is taken from the library as it is
built; its signature and documentation are not restated by hand.

```
Reference Ellipsoid
        ↓
Curvature
        ↓
First Fundamental Form
        ↓
Local Distortion
      ↙   ↓   ↘
Mercator  Equal Area  Azimuthal
```

# Reference ellipsoid

A reference ellipsoid is fixed by its semi-major axis $`a` and flattening
$`f`. The semi-minor axis is $`b = a (1 - f)` and the first eccentricity
squared is $`e^2 = f (2 - f) = (a^2 - b^2) / a^2`.

{docstring Geodesy.ReferenceEllipsoid}

{docstring Geodesy.ReferenceEllipsoid.e2_eq}

# Curvature

At geodetic latitude $`\varphi` the meridian has radius of curvature
$`M = a (1 - e^2) / (1 - e^2 \sin^2 \varphi)^{3/2}` and the parallel has
radius $`N \cos \varphi`. The meridian radius is derived by differentiating
the meridian point, not stated.

{docstring Geodesy.ReferenceEllipsoid.meridianRadius}

{docstring Geodesy.ReferenceEllipsoid.hasDerivAt_meridianPoint_fst}

{docstring Geodesy.ReferenceEllipsoid.inner_meridianTangent_parallelTangent}

{docstring Geodesy.ReferenceEllipsoid.N_div_M}

# First fundamental form

In the coordinates $`(\varphi, \lambda)` the tangent lengths of the previous
section give $`E = M^2`, $`F = 0`, $`G = (N \cos \varphi)^2`, so
$`ds^2 = M^2 d\varphi^2 + (N \cos \varphi)^2 d\lambda^2`.

{docstring Geodesy.ReferenceEllipsoid.firstFormE_eq}

{docstring Geodesy.ReferenceEllipsoid.firstFormF_eq}

{docstring Geodesy.ReferenceEllipsoid.firstFormG_eq}

{docstring Geodesy.ReferenceEllipsoid.norm_dr_sq}

# Local distortion

A projection sends a step north and a step east to two vectors on the map.
Measured against $`\sqrt{E} = M` and $`\sqrt{G} = N \cos \varphi`, they give
the scales $`h`, $`k` and the area scale. A projection is conformal exactly
when it multiplies the first fundamental form by $`h^2`.

{docstring Geodesy.Projection.LocalDistortion}

{docstring Geodesy.Projection.LocalDistortion.ofEllipsoid}

{docstring Geodesy.Projection.isConformal_iff_firstForm}

{docstring Geodesy.Projection.areaScale_ofEllipsoid}

# Mercator

Mercator's northing $`y = \operatorname{arsinh} (\tan \varphi)` has
derivative $`\sec \varphi`, so both steps are stretched by the same factor.

{docstring Geodesy.Projection.hasDerivAt_mercatorY}

{docstring Geodesy.Projection.mercator_isConformal}

The statements are elaborated against the library, so they can be checked in
place:

```lean
#check @Geodesy.Projection.mercator_isConformal
```

# Equal area

{docstring Geodesy.Projection.lambertCylindrical_preserves_cellArea}

{docstring Geodesy.Projection.webMercator_not_isEqualArea}

# Azimuthal

{docstring Geodesy.Projection.azimuthalEquidistant_preserves_distanceFromCentre}

{docstring Geodesy.Projection.azimuthalEquidistant_not_isConformal}
