import LeanGeodesy.CRS.Basic
import LeanGeodesy.ECEFInverse
import LeanGeodesy.Helmert

/-!
# Transformations between geographic CRSs

Moving a coordinate from one geographic CRS to another, for example from an
older realisation of a datum to a newer one, is done in three steps:

1. turn the latitude, longitude and height into an ECEF position on the
   source ellipsoid (`GeodeticCoordinate.toECEF`);
2. move the position into the target frame with a Helmert transformation;
3. turn it back into latitude, longitude and height on the target
   ellipsoid.

Step 3 is possible because every point of space has geodetic coordinates
(`toECEF_surjective`). This file defines three-dimensional coordinates of a
geographic CRS (`GeographicCRS.Coordinate3D`) and a transformation between
two CRSs as a Helmert transformation between their frames, and proves that
the transformed coordinate names exactly the moved point
(`toPoint3D_transform`) and that transforming back returns to the same point
(`toPoint3D_inverse_transform`).

It is the position, not the coordinate, that is recovered: on the axis the
longitude is arbitrary, so the coordinates themselves need not match.
-/

namespace Geodesy

namespace GeographicCRS

variable (C : GeographicCRS)

/-- A three-dimensional coordinate of `C`: latitude, longitude and height above
`C`'s ellipsoid. The CRS is part of the type. -/
@[ext] structure Coordinate3D (C : GeographicCRS) where
  toGeodetic : GeodeticCoordinate

/-- The point of space it names. -/
noncomputable def toPoint3D (c : C.Coordinate3D) : E3 :=
  GeodeticCoordinate.toECEF C.ellipsoid c.toGeodetic

/-- Every point of space has coordinates in every geographic CRS. -/
theorem toPoint3D_surjective : Function.Surjective C.toPoint3D := fun P => by
  obtain ⟨c, hc⟩ := toECEF_surjective C.ellipsoid P
  exact ⟨⟨c⟩, hc⟩

/-- The height-zero coordinate names the same point as the 2D coordinate. -/
theorem toPoint3D_of_height_zero (c : C.Coordinate) : C.toPoint3D ⟨c.toGeodetic⟩ = C.toPoint c :=
  (C.toPoint_eq_toECEF c).symm

end GeographicCRS

/-- A transformation from the geographic CRS `C` to `D`: the Helmert
transformation taking positions in `C`'s frame to positions in `D`'s. -/
structure CRSTransformation (C D : GeographicCRS) where
  /-- The Helmert transformation from the frame of `C` to the frame of `D`. -/
  helmert : Helmert

namespace CRSTransformation

variable {C D : GeographicCRS} (T : CRSTransformation C D)

/-- The transformed coordinate: some coordinate of `D` naming the moved point. -/
noncomputable def transform (c : C.Coordinate3D) : D.Coordinate3D :=
  Classical.choose (D.toPoint3D_surjective (T.helmert.apply (C.toPoint3D c)))

/-- The transformed coordinate names the moved point. -/
theorem toPoint3D_transform (c : C.Coordinate3D) :
    D.toPoint3D (T.transform c) = T.helmert.apply (C.toPoint3D c) :=
  Classical.choose_spec (D.toPoint3D_surjective _)

/-- The transformation back from `D` to `C`. -/
noncomputable def inverse : CRSTransformation D C := ⟨T.helmert.inv⟩

/-- Transforming and transforming back returns to the same point. -/
theorem toPoint3D_inverse_transform (c : C.Coordinate3D) :
    C.toPoint3D (T.inverse.transform (T.transform c)) = C.toPoint3D c := by
  rw [toPoint3D_transform, inverse, toPoint3D_transform, Helmert.inv_apply]

/-- Distances between transformed points are the source distances times the
scale. -/
theorem dist_transform (c c' : C.Coordinate3D) :
    dist (D.toPoint3D (T.transform c)) (D.toPoint3D (T.transform c')) =
      T.helmert.scale * dist (C.toPoint3D c) (C.toPoint3D c') := by
  rw [toPoint3D_transform, toPoint3D_transform, Helmert.dist_apply]

end CRSTransformation

end Geodesy
