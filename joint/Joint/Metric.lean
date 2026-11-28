import Joint.Basic

/-!
# Geodesic distance, chord distance and spherical Voronoi cells

LeanGeodesy measures the unit sphere by the central angle `geoDist` and the chord `chordDist`
(`Geodesy.Spherical`); LeanComputationalGeometry's spherical Voronoi cells
(`ComputationalGeometry.sphVoronoiCell`) are defined with Mathlib's angle, the same quantity.
Proved here:

* `sphVoronoiCell_eq_geoDist`: LeanComputationalGeometry's spherical Voronoi cell of a site is
  exactly the Voronoi cell for LeanGeodesy's geodesic distance;
* `sphVoronoiCell_eq_chordDist`: and it is the Voronoi cell for LeanGeodesy's chord distance,
  combining LeanComputationalGeometry's `sphVoronoiCell_eq` (chordal cells of `ℝ³` cut by the
  sphere).

The metric comparison itself is LeanGeodesy's and is reused, not repeated: the chord is
`2 sin (θ / 2)` (`chordDist_eq_two_sin_half`), `chordDist ≤ geoDist ≤ (π / 2) chordDist`
(`chordDist_le_geoDist`, `geoDist_le_pi_div_two_mul_chordDist`), and the two distances define the
same topology (`geoDist_topology_equiv_chordDist`). Nothing here is specific to the Earth: it is
the geometry of the unit sphere of `ℝ³`.
-/

namespace Joint

open Geodesy Geodesy.Spherical

/-- The sites, as points of space. -/
def sitesE3 (S : Set Geodesy.Spherical.UnitSphere) : Set Geodesy.E3 := Subtype.val '' S

/-- **The spherical Voronoi cell is the geodesic Voronoi cell.** -/
theorem sphVoronoiCell_eq_geoDist (S : Set Geodesy.Spherical.UnitSphere) (s : Geodesy.Spherical.UnitSphere) :
    ComputationalGeometry.sphVoronoiCell (sitesE3 S) s.1 =
      Subtype.val '' {p : Geodesy.Spherical.UnitSphere | ∀ t ∈ S, geoDist p s ≤ geoDist p t} := by
  ext v
  constructor
  · rintro ⟨hv, hcell⟩
    refine ⟨⟨v, mem_sphere_zero_iff_norm.mp hv⟩, fun t ht => hcell t.1 ⟨t, ht, rfl⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨mem_sphere_zero_iff_norm.mpr p.2, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hp t ht

/-- **… and the chordal Voronoi cell.** -/
theorem sphVoronoiCell_eq_chordDist (S : Set Geodesy.Spherical.UnitSphere) (s : Geodesy.Spherical.UnitSphere) :
    ComputationalGeometry.sphVoronoiCell (sitesE3 S) s.1 =
      Subtype.val '' {p : Geodesy.Spherical.UnitSphere | ∀ t ∈ S, chordDist p s ≤ chordDist p t} := by
  have hS : sitesE3 S ⊆ ComputationalGeometry.S2 := by
    rintro _ ⟨t, -, rfl⟩; exact mem_sphere_zero_iff_norm.mpr t.2
  rw [ComputationalGeometry.sphVoronoiCell_eq hS (mem_sphere_zero_iff_norm.mpr s.2)]
  ext v
  constructor
  · rintro ⟨hv, hcell⟩
    exact ⟨⟨v, mem_sphere_zero_iff_norm.mp hv⟩, fun t ht => hcell t.1 ⟨t, ht, rfl⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨mem_sphere_zero_iff_norm.mpr p.2, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hp t ht

end Joint
