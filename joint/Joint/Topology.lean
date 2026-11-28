import Joint.Basic

/-!
# Topological relations survive the passage from the sphere to the ellipsoid

LeanGeodesy's linear scaling `axisScale a b` carries the unit sphere homeomorphically onto the
ellipsoid of a reference ellipsoid (`ReferenceEllipsoid.sphereHomeomorph`). LeanGeospatial proves
that every homeomorphism preserves the eight RCC8 relations (`RCC8.Relation.holds_map_iff`) and,
with the cube dimension, the whole DE-9IM matrix (`de9im_map`, `cubeDim_compatible`). Combined:

* `rcc8_sphere_ellipsoid_iff`: two regions of the unit sphere stand in an RCC8 relation iff their
  images on the ellipsoid do;
* `de9im_sphere_ellipsoid_eq`: the DE-9IM matrices agree;
* the same for LeanGeodesy's `UnitSphere` type (`rcc8_unitSphere_ellipsoid_iff`).

These are topological statements: the scaling changes distances by factors between `b` and `a`
(`dist_axisScale_bounds`) and does not preserve geodetic latitude
(`axisScale_spherePoint_ne_ellipsoidPoint`); only parametric latitude is kept.
-/

namespace Joint

open Geodesy Geospatial Geospatial.DE9IM

/-- **RCC8 relations are the same on the sphere and on the ellipsoid.** -/
theorem rcc8_sphere_ellipsoid_iff (E : ReferenceEllipsoid)
    (A B : RegularClosedRegion Geospatial.Spaces.S2) (r : RCC8.Relation) :
    r.holds (A.map E.sphereHomeomorph) (B.map E.sphereHomeomorph) ↔ r.holds A B :=
  RCC8.Relation.holds_map_iff _ A B r

/-- **The DE-9IM matrix is the same on the sphere and on the ellipsoid.** -/
theorem de9im_sphere_ellipsoid_eq (E : ReferenceEllipsoid) (A B : Set Geospatial.Spaces.S2) :
    de9im (cubeDim 2) (E.sphereHomeomorph '' A) (E.sphereHomeomorph '' B) =
      de9im (cubeDim 2) A B :=
  de9im_map (cubeDim_compatible 2 E.sphereHomeomorph) A B

/-- The same for LeanGeodesy's `UnitSphere` type. -/
theorem rcc8_unitSphere_ellipsoid_iff (E : ReferenceEllipsoid)
    (A B : RegularClosedRegion Geodesy.Spherical.UnitSphere) (r : RCC8.Relation) :
    r.holds (A.map E.unitSphereHomeomorph) (B.map E.unitSphereHomeomorph) ↔ r.holds A B :=
  RCC8.Relation.holds_map_iff _ A B r

end Joint
