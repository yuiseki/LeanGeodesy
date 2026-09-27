import LeanGeodesy
import LeanAtlas

/-!
Main theorems for Lean Compass, marked here so that the library itself does
not depend on lean-atlas. They are the results the books build up to: the
first fundamental form, conformality as a property of that form, what
Mercator, Lambert and the azimuthal equidistant projection keep, great
circles as shortest paths, and the geodesic equations with Clairaut's
relation. lean-atlas drops every name containing `_eq_`, so theorems such as
`meridianArc_eq_curveLength` cannot be marked.
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

attribute [formalMeta "First fundamental form: E = M²"
  "The first fundamental form of the ellipsoid has E = M²" mainTheorem]
  Geodesy.ReferenceEllipsoid.firstFormE_eq

attribute [formalMeta "Conformal iff it scales the first fundamental form"
  "A projection is conformal exactly when it multiplies the first fundamental form by h²" mainTheorem]
  Geodesy.Projection.isConformal_iff_firstForm

attribute [formalMeta "Conformal cylindrical projections are Mercator"
  "A cylindrical projection conformal at every latitude is Mercator's" mainTheorem]
  Geodesy.Projection.eq_mercatorY_of_isConformal

attribute [formalMeta "No cylindrical projection is conformal and equal-area"
  "Away from the equator no cylindrical projection keeps both angles and areas" mainTheorem]
  Geodesy.Projection.eq_zero_of_isConformal_of_isEqualArea

attribute [formalMeta "Great circles are shortest"
  "No curve on the sphere is shorter than the great-circle arc" mainTheorem]
  Geodesy.Geodesic.angularLength_greatArc_le

attribute [formalMeta "Geodesic equations"
  "Affine geodesics on the ellipsoid are exactly the solutions of the geodesic equations" mainTheorem]
  Geodesy.ReferenceEllipsoid.EllipsoidCurve.isGeodesic_iff_equations

attribute [formalMeta "Clairaut's relation"
  "Along a geodesic, N cos φ sin A is constant" mainTheorem]
  Geodesy.ReferenceEllipsoid.EllipsoidCurve.clairaut

attribute [formalMeta "Hilbert order is adjacent"
  "In the Hilbert order, consecutive tiles always share an edge" mainTheorem]
  Geodesy.Tiles.hilbertOrder_isAdjacentOrder

attribute [formalMeta "Morton order is not adjacent"
  "In the Morton order, consecutive tiles need not share an edge" mainTheorem]
  Geodesy.Tiles.mortonOrder_not_isAdjacentOrder
