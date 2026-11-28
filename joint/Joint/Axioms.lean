import Joint.Basic
import Joint.Projections
import Joint.Metric
import Joint.Topology
import Joint.Pipeline

/-!
# Axiom audit of the joint theorems

Every theorem joining the three libraries depends only on the three standard axioms.
-/

/-- info: 'Joint.unitSphereHomeomorph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.unitSphereHomeomorph

/-- info: 'Joint.chordDist_eq_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.chordDist_eq_dist

/-- info: 'Joint.radial_eq_radialProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.radial_eq_radialProj

/-- info: 'Joint.inclS2_eq_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.inclS2_eq_val

/-- info: 'Joint.morton_eq_mortonD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.morton_eq_mortonD

/-- info: 'Joint.stereographic_eq_two_smul_stereoProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.stereographic_eq_two_smul_stereoProj

/-- info: 'Joint.gnomonic_spherePoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.gnomonic_spherePoint

/-- info: 'Joint.norm_spherePoint_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.norm_spherePoint_one

/-- info: 'Joint.radial_spherePoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.radial_spherePoint

/-- info: 'Joint.sphVoronoiCell_eq_geoDist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.sphVoronoiCell_eq_geoDist

/-- info: 'Joint.sphVoronoiCell_eq_chordDist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.sphVoronoiCell_eq_chordDist

/-- info: 'Joint.rcc8_sphere_ellipsoid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.rcc8_sphere_ellipsoid_iff

/-- info: 'Joint.de9im_sphere_ellipsoid_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.de9im_sphere_ellipsoid_eq

/-- info: 'Joint.rcc8_unitSphere_ellipsoid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.rcc8_unitSphere_ellipsoid_iff

/-- info: 'Joint.spherePoint_mem_upperHemi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.spherePoint_mem_upperHemi

/-- info: 'Joint.gnomonic_lat_pi_div_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.gnomonic_lat_pi_div_four

/-- info: 'Joint.arc_intersects_iff_intersectTestI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.arc_intersects_iff_intersectTestI

/-- info: 'Joint.arcs_AB_intersect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.arcs_AB_intersect

/-- info: 'Joint.arcs_CD_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Joint.arcs_CD_disjoint
