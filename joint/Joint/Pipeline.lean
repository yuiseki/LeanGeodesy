import Joint.Projections

/-!
# From the globe to the plane and back: a worked cross-library proof

Two great-circle arcs on the unit sphere are given by LeanGeodesy's latitude and longitude
(`spherePoint 1 φ lam`), at latitude `π/4`:

* arc `A` from longitude `0` to longitude `π`, arc `B` from `π/2` to `-π/2`; and
* arc `C` from longitude `0` to `π/2`, arc `D` from `π` to `3π/2`.

The pipeline:

1. **LeanGeodesy → LeanComputationalGeometry.** The endpoints lie in the open upper hemisphere;
   the gnomonic projection, written in geodetic coordinates (`gnomonic_spherePoint`), sends them
   to the integer points `(1, 0)`, `(-1, 0)`, `(0, 1)`, `(0, -1)`.
2. **Compute in the plane.** LeanComputationalGeometry's exact integer segment test
   `intersectTestI` is evaluated by `decide`.
3. **Back to the sphere.** `intersectsS2_arc_iff` (arc intersection in a hemisphere is segment
   intersection of the gnomonic images) turns the answer into a statement about the arcs, read
   as LeanGeospatial's `Intersects` / `Disjoint` of sets of `ℝ³`.

Conclusions: `A` and `B` intersect (`arcs_AB_intersect`); `C` and `D` do not
(`arcs_CD_disjoint`).
-/

namespace Joint

open Real Geodesy Geodesy.Projection ComputationalGeometry

theorem spherePoint_mem_upperHemi {φ : ℝ} (h : 0 < sin φ) (lam : ℝ) :
    spherePoint 1 φ lam ∈ upperHemi := by
  refine ⟨mem_sphere_zero_iff_norm.mpr (norm_spherePoint_one φ lam), ?_⟩
  simp only [Point3D.z, spherePoint, vec3_2, one_mul]; exact h

theorem sin_pi_div_four_pos : 0 < sin (π / 4) := by
  rw [sin_pi_div_four]; positivity

/-- The gnomonic image of a point at latitude `π/4`. -/
theorem gnomonic_lat_pi_div_four (lam : ℝ) :
    gnomonic (spherePoint 1 (π / 4) lam) = Point2D.mk (cos lam) (sin lam) := by
  rw [gnomonic_spherePoint one_ne_zero, cos_pi_div_four, sin_pi_div_four]
  have h : √2 / 2 ≠ 0 := by positivity
  apply Point2D.ext <;> simp only [Point2D.x_mk, Point2D.y_mk] <;> field_simp

theorem img_mk (x y : ℤ) : Point2D.mk (x : ℝ) (y : ℝ) = (IPoint.toPoint2D ⟨x, y⟩) := rfl

/-- The four endpoints at latitude `π/4` and longitudes `0, π, π/2, -π/2`, and their images. -/
theorem gA : gnomonic (spherePoint 1 (π / 4) 0) = IPoint.toPoint2D ⟨1, 0⟩ := by
  rw [gnomonic_lat_pi_div_four]; simp [IPoint.toPoint2D]
theorem gA' : gnomonic (spherePoint 1 (π / 4) π) = IPoint.toPoint2D ⟨-1, 0⟩ := by
  rw [gnomonic_lat_pi_div_four]; simp [IPoint.toPoint2D]
theorem gB : gnomonic (spherePoint 1 (π / 4) (π / 2)) = IPoint.toPoint2D ⟨0, 1⟩ := by
  rw [gnomonic_lat_pi_div_four]; simp [IPoint.toPoint2D]
theorem gB' : gnomonic (spherePoint 1 (π / 4) (-(π / 2))) = IPoint.toPoint2D ⟨0, -1⟩ := by
  rw [gnomonic_lat_pi_div_four]; simp [IPoint.toPoint2D]
theorem gD' : gnomonic (spherePoint 1 (π / 4) (3 * π / 2)) = IPoint.toPoint2D ⟨0, -1⟩ := by
  rw [gnomonic_lat_pi_div_four]
  have hc : cos (3 * π / 2) = 0 := by
    rw [show 3 * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two, neg_zero]
  have hs : sin (3 * π / 2) = -1 := by
    rw [show 3 * π / 2 = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]
  simp [IPoint.toPoint2D, hc, hs]

/-- Arc intersection on the sphere, decided by the integer segment test. -/
theorem arc_intersects_iff_intersectTestI {a b c d : Geodesy.E3} (ha : a ∈ upperHemi)
    (hb : b ∈ upperHemi) (hc : c ∈ upperHemi) (hd : d ∈ upperHemi) {s t : ISegment}
    (hs : (⟨gnomonic a, gnomonic b⟩ : Segment) = s.toSegment)
    (ht : (⟨gnomonic c, gnomonic d⟩ : Segment) = t.toSegment) :
    Geospatial.Intersects (arc a b) (arc c d) ↔ intersectTestI s t = true := by
  have := intersectsS2_arc_iff ha hb hc hd
  rw [hs, ht, intersects_iff_intersectTestI] at this
  exact this

/-- **Arcs `A` and `B` cross**, decided in the plane. -/
theorem arcs_AB_intersect :
    Geospatial.Intersects (arc (spherePoint 1 (π / 4) 0) (spherePoint 1 (π / 4) π))
      (arc (spherePoint 1 (π / 4) (π / 2)) (spherePoint 1 (π / 4) (-(π / 2)))) := by
  have h := sin_pi_div_four_pos
  rw [arc_intersects_iff_intersectTestI (spherePoint_mem_upperHemi h _)
    (spherePoint_mem_upperHemi h _) (spherePoint_mem_upperHemi h _)
    (spherePoint_mem_upperHemi h _) (s := ⟨⟨1, 0⟩, ⟨-1, 0⟩⟩) (t := ⟨⟨0, 1⟩, ⟨0, -1⟩⟩)
    (by rw [gA, gA']; rfl) (by rw [gB, gB']; rfl)]
  decide

/-- **Arcs `C` and `D` are disjoint**, decided in the plane. -/
theorem arcs_CD_disjoint :
    ¬ Geospatial.Intersects (arc (spherePoint 1 (π / 4) 0) (spherePoint 1 (π / 4) (π / 2)))
      (arc (spherePoint 1 (π / 4) π) (spherePoint 1 (π / 4) (3 * π / 2))) := by
  have h := sin_pi_div_four_pos
  rw [arc_intersects_iff_intersectTestI (spherePoint_mem_upperHemi h _)
    (spherePoint_mem_upperHemi h _) (spherePoint_mem_upperHemi h _)
    (spherePoint_mem_upperHemi h _) (s := ⟨⟨1, 0⟩, ⟨0, 1⟩⟩) (t := ⟨⟨-1, 0⟩, ⟨0, -1⟩⟩)
    (by rw [gA, gB]; rfl) (by rw [gA', gD']; rfl)]
  decide

end Joint
