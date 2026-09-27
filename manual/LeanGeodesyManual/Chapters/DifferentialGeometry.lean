import VersoManual
import LeanGeodesy

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Differential geometry" =>

The previous chapter gave the ellipsoid and named its points. This one
measures it: how it curves, how long a small step on it is, what angle two
directions make and how much area a small patch covers. All of this comes
from one object, the first fundamental form, and the next two chapters,
on projections and on geodesics, are built on it.

```
ReferenceEllipsoid (a, f)
  → M(φ), N(φ)                 radii of curvature
  → ∂r/∂φ, ∂r/∂λ               tangents in ℝ³
  → first fundamental form     E = M², F = 0, G = (N cos φ)²
       ├→ length and speed     ds² = M² dφ² + (N cos φ)² dλ²
       ├→ angle
       ├→ area element         dA = M N cos φ dφ dλ
       └→ projection distortion (next chapter)
```

# Radii of curvature

At geodetic latitude $`\varphi` the ellipsoid curves differently in two
directions. Across the meridian the radius of curvature is the prime
vertical radius $`N`, and the parallel through the point is a circle of
radius $`N \cos \varphi`. Along the meridian it is
$`M = a (1 - e^2) / (1 - e^2 \sin^2 \varphi)^{3/2}`.

The library derives $`M` rather than stating it: differentiating the
meridian point $`(N \cos \varphi, N (1 - e^2) \sin \varphi)` in $`\varphi`
gives $`(-M \sin \varphi, M \cos \varphi)`, a vector of length $`M`.

{docstring Geodesy.ReferenceEllipsoid.meridianRadius}

{docstring Geodesy.ReferenceEllipsoid.hasDerivAt_meridianPoint_fst}

{docstring Geodesy.ReferenceEllipsoid.hasDerivAt_meridianPoint_snd}

# Tangents in space

In space the surface is $`r(\varphi, \lambda)`. Its two partial derivatives
are the meridian tangent and the parallel tangent. They are perpendicular,
of lengths $`M` and $`N \cos \varphi`.

{docstring Geodesy.ReferenceEllipsoid.ellipsoidPoint}

{docstring Geodesy.ReferenceEllipsoid.norm_meridianTangent_sq}

{docstring Geodesy.ReferenceEllipsoid.norm_parallelTangent_sq}

{docstring Geodesy.ReferenceEllipsoid.inner_meridianTangent_parallelTangent}

The ratio of the two radii is what map projections will measure distortion
by: they agree on a sphere and at the poles, and $`M < N` everywhere else.

{docstring Geodesy.ReferenceEllipsoid.N_div_M}

# The first fundamental form

With latitude and longitude as local coordinates, a step
$`(d\varphi, d\lambda)` has squared length
$`E\, d\varphi^2 + 2 F\, d\varphi\, d\lambda + G\, d\lambda^2`, where
$`E`, $`F`, $`G` are the inner products of the partial derivatives. The
lengths and the orthogonality just proved give them at once.

{docstring Geodesy.ReferenceEllipsoid.firstFormE_eq}

{docstring Geodesy.ReferenceEllipsoid.firstFormF_eq}

{docstring Geodesy.ReferenceEllipsoid.firstFormG_eq}

The form's bilinear version is a metric: symmetric, bilinear, never
negative, and away from the poles zero only on the zero vector. At the poles
$`G = 0`, since every longitude names the same point.

{docstring Geodesy.ReferenceEllipsoid.metric_self_eq_zero_iff}

# Length, speed and angle

The form is what the ellipsoid's actual tangent vectors measure: the
coordinate step $`v` is the tangent vector $`dr\, v`, and its squared length
is the line element. A curve on the ellipsoid therefore has squared speed
$`M^2 \varphi'^2 + (N \cos \varphi)^2 \lambda'^2`, and the angle between two
directions is read off the metric too.

{docstring Geodesy.ReferenceEllipsoid.norm_dr_sq}

{docstring Geodesy.ReferenceEllipsoid.speed_sq_curve}

{docstring Geodesy.ReferenceEllipsoid.cos_angle_dr}

# Area

The area element comes from the same coefficients:
$`\sqrt{E G - F^2} = M N \cos \varphi`. On a sphere of radius $`R`,
$`M = N = R` and the area element is $`R^2 \cos \varphi`.

{docstring Geodesy.ReferenceEllipsoid.areaElement_eq}

{docstring Geodesy.ReferenceEllipsoid.areaElement_ofSphere}

# How the form changes with latitude

The coefficients depend on the latitude only. Their derivatives are what
the geodesic equations of the last chapter of this part will need.

{docstring Geodesy.ReferenceEllipsoid.hasDerivAt_meridianRadius}

{docstring Geodesy.ReferenceEllipsoid.hasDerivAt_firstFormE}

{docstring Geodesy.ReferenceEllipsoid.hasDerivAt_firstFormG}
