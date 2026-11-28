import LeanGeodesy
import LeanGeospatial
import LeanComputationalGeometry

/-!
# One foundation: the plane, space, ℝⁿ and the unit sphere across the three libraries

The three libraries never import one another; this file, built only by
`scripts/joint_check.sh`, states how their types and maps line up.

* **ℝⁿ is the common foundation**: every point type is Mathlib's `EuclideanSpace ℝ (Fin n)`, so
  the planes and the spaces of the three libraries, and LeanComputationalGeometry's `PointN n`,
  are equal by `rfl`.
* **The unit sphere as a set** is `Metric.sphere (0 : ℝ³) 1` in all three libraries
  (`Geodesy.sphere 1`, `ComputationalGeometry.S2`, `Geospatial.Spaces.S2`): equal by `rfl`.
* **The unit sphere as a type** comes in two forms: Mathlib's subtype of that set
  (`↥(Metric.sphere 0 1)`, used by LeanGeospatial and LeanComputationalGeometry) and
  LeanGeodesy's `UnitSphere := {x : E3 // ‖x‖ = 1}`. They are not definitionally equal (the
  predicates `dist x 0 = 1` and `‖x‖ = 1` differ); `unitSphereHomeomorph` is the natural
  homeomorphism (LeanGeodesy's `SphereEllipsoid.unitSphereHomeomorph`), the identity on points,
  and it preserves distances.
* **Maps**: LeanComputationalGeometry's `radial` is LeanGeospatial's `radialProj` read in `ℝ³`
  (`radial_eq_radialProj`), and LeanGeospatial's inclusion `inclS2` is the subtype coercion.
-/

namespace Joint

open Geodesy

/-! ## The plane and space are one type -/

example : Geodesy.E2 = Geospatial.Point2D := rfl
example : Geodesy.E2 = ComputationalGeometry.Point2D := rfl
example : Geospatial.Point2D = ComputationalGeometry.Point2D := rfl
example : ComputationalGeometry.PointN 2 = Geodesy.E2 := rfl

example : Geodesy.E3 = ComputationalGeometry.Point3D := rfl
example : Geodesy.E3 = Geospatial.Spaces.E3 := rfl
example : Geodesy.E3 = Geospatial.DE9IM.Space3.E3 := rfl
example : ComputationalGeometry.PointN 3 = Geodesy.E3 := rfl

/-- The coordinates read the same. -/
example (p : ComputationalGeometry.Point2D) :
    ComputationalGeometry.Point2D.x p = Geospatial.Point2D.x p := rfl

/-- LeanGeospatial's distance is Mathlib's distance on that plane. -/
example (p q : Geodesy.E2) : Geospatial.distance p q = dist p q := rfl

/-! ## The unit sphere: one set, two types -/

example : Geodesy.sphere 1 = ComputationalGeometry.S2 := rfl
example : (Geospatial.Spaces.S2 : Set Geodesy.E3) = ComputationalGeometry.S2 := rfl
example : ↥Geospatial.Spaces.S2 = ↥ComputationalGeometry.S2 := rfl

/-- LeanGeodesy's unit sphere type and the subtype of the unit sphere used by LeanGeospatial and
LeanComputationalGeometry: LeanGeodesy's homeomorphism (the identity on points), reused. -/
noncomputable def unitSphereHomeomorph : Geodesy.Spherical.UnitSphere ≃ₜ Geospatial.Spaces.S2 :=
  Geodesy.SphereEllipsoid.unitSphereHomeomorph

@[simp] theorem unitSphereHomeomorph_val (x : Geodesy.Spherical.UnitSphere) :
    (unitSphereHomeomorph x : Geodesy.E3) = x.1 := rfl

/-- It preserves distances: LeanGeodesy's chord distance is the distance of the subtype. -/
theorem chordDist_eq_dist (x y : Geodesy.Spherical.UnitSphere) :
    Spherical.chordDist x y = dist (unitSphereHomeomorph x) (unitSphereHomeomorph y) := rfl

/-! ## Maps between space and the sphere -/

/-- LeanComputationalGeometry's radial projection is LeanGeospatial's, read in space. -/
theorem radial_eq_radialProj (v : Geodesy.E3) (hv : v ≠ 0) :
    ComputationalGeometry.radial v = (Geospatial.Spaces.radialProj ⟨v, hv⟩ : Geodesy.E3) := rfl

/-- LeanGeospatial's inclusion is the subtype coercion. -/
theorem inclS2_eq_val (p : Geospatial.Spaces.S2) : Geospatial.Spaces.inclS2 p = p.1 := rfl

/-! ## Earlier joint facts -/

/-- The `d`-dimensional Morton code of LeanComputationalGeometry is LeanGeodesy's tile Morton
code for `d = 2`: the 2-D case is not implemented twice. -/
theorem morton_eq_mortonD : ∀ (z x y : ℕ),
    Geodesy.Tiles.morton z x y = ComputationalGeometry.mortonD 2 z ![x, y]
  | 0, _, _ => rfl
  | z + 1, x, y => by
    rw [ComputationalGeometry.mortonD_two_succ, ← morton_eq_mortonD z]
    rfl

/-- A point a LeanGeodesy projection draws is a point of a LeanGeospatial region, with no
conversion. -/
example (R φ lam : ℝ) (A : Geospatial.Region) : Prop :=
  Geodesy.Projection.mercator R φ lam ∈ A

/-- Points that LeanGeodesy's Mercator projection draws feed LeanComputationalGeometry's
orientation test directly. -/
example (R φ₁ l₁ φ₂ l₂ φ₃ l₃ : ℝ) :
    ComputationalGeometry.orient (Geodesy.Projection.mercator R φ₂ l₂)
        (Geodesy.Projection.mercator R φ₁ l₁) (Geodesy.Projection.mercator R φ₃ l₃) =
      -ComputationalGeometry.orient (Geodesy.Projection.mercator R φ₁ l₁)
        (Geodesy.Projection.mercator R φ₂ l₂) (Geodesy.Projection.mercator R φ₃ l₃) :=
  ComputationalGeometry.orient_swap₁₂ _ _ _

/-- A segment of LeanComputationalGeometry is a LeanGeospatial region. -/
example (s : ComputationalGeometry.Segment) : Geospatial.Region := s.toSet

/-- LeanGeospatial's relations apply to LeanComputationalGeometry's triangles. -/
example (T : ComputationalGeometry.Triangle) (A : Geospatial.Region) : Prop :=
  Geospatial.Within T.toSet A

/-- Two Mercator maps of one globe at different scales differ by a homeomorphism of the plane,
so they agree on every RCC8 relation between the areas drawn on them. -/
example (R₁ R₂ : ℝ) (h₁ : R₁ ≠ 0) (h₂ : R₂ ≠ 0)
    (A B : Geospatial.RegularClosedRegion Geospatial.Point2D)
    (r : Geospatial.RCC8.Relation) :
    let e := (Geodesy.Projection.mercatorHomeomorph R₁ h₁).symm.trans
      (Geodesy.Projection.mercatorHomeomorph R₂ h₂)
    r.holds (A.map e) (B.map e) ↔ r.holds A B :=
  Geospatial.RCC8.Relation.holds_map_iff _ A B r

/-- On the globe itself: the RCC8 relation between two areas of the Web Mercator chart is the
relation between their images on the map. -/
example (A B : Geospatial.RegularClosedRegion Geodesy.Projection.webMercatorChart)
    (r : Geospatial.RCC8.Relation) :
    r.holds (A.map Geodesy.Projection.webMercatorHomeomorph)
      (B.map Geodesy.Projection.webMercatorHomeomorph) ↔ r.holds A B :=
  Geospatial.RCC8.Relation.holds_map_iff _ A B r

end Joint
