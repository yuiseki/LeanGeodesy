import VersoManual
import LeanGeodesyManual.Chapters.EllipsoidGeometry
import LeanGeodesyManual.Chapters.DifferentialGeometry
import LeanGeodesyManual.Chapters.Projection
import LeanGeodesyManual.Chapters.Geodesics

open Verso.Genre Manual

#doc (Manual) "Part I: The Earth as an ellipsoid" =>

The Earth is modelled as an ellipsoid of revolution. This part goes from
its two defining numbers to what can be measured on it and on maps of it.

```
Ellipsoid geometry
↓
Differential geometry
↓
Projection
↓
Geodesics
```

The first chapter gives the shape and names positions on it. The second
measures the surface with its radii of curvature and first fundamental form.
The third measures map projections against that form, and the fourth finds
the shortest routes, first on the sphere and then, through the same form, on
the ellipsoid.

{include 1 LeanGeodesyManual.Chapters.EllipsoidGeometry}
{include 1 LeanGeodesyManual.Chapters.DifferentialGeometry}
{include 1 LeanGeodesyManual.Chapters.Projection}
{include 1 LeanGeodesyManual.Chapters.Geodesics}
