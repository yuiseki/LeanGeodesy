import LeanGeodesy
import LeanAtlas

/-!
Main theorems for Lean Compass, marked here so that the library itself does
not depend on lean-atlas. They are the ends of the projection spine:
reference ellipsoid, curvature, first fundamental form, local distortion,
then Mercator, equal-area and azimuthal projections.
-/

attribute [formalMeta "Mercator is conformal"
  "Mercator's projection stretches every direction equally" mainTheorem]
  Geodesy.Projection.mercator_isConformal

attribute [formalMeta "Lambert keeps cell areas"
  "Lambert's cylindrical equal-area projection keeps the area of every cell" mainTheorem]
  Geodesy.Projection.lambertCylindrical_preserves_cellArea

attribute [formalMeta "Web Mercator is not equal-area"
  "On a flattened ellipsoid Web Mercator is equal-area nowhere" mainTheorem]
  Geodesy.Projection.webMercator_not_isEqualArea

attribute [formalMeta "Azimuthal equidistant keeps distances"
  "Distances from the centre are great-circle distances" mainTheorem]
  Geodesy.Projection.azimuthalEquidistant_preserves_distanceFromCentre

attribute [formalMeta "Azimuthal equidistant is not conformal"
  "Its scale along parallels exceeds its scale along meridians" mainTheorem]
  Geodesy.Projection.azimuthalEquidistant_not_isConformal
