import LeanGeodesy

/-!
# Axiom audit

Each theorem below may depend only on Lean's three standard axioms, which
come in through Mathlib's construction of the real numbers. If anything in
this project adds an `axiom` or leaves a proof unfinished (which shows up as
`sorryAx`), the expected messages stop matching and `lake build` fails.

This file is not imported by `LeanGeodesy`; the library's glob builds it.
-/

/-- info: 'Geodesy.degToRad_radToDeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.degToRad_radToDeg

/-- info: 'Geodesy.radToDeg_degToRad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.radToDeg_degToRad

/-- info: 'Geodesy.degToRad_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.degToRad_strictMono

/-- info: 'Geodesy.dms_carry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.dms_carry

/-- info: 'Geodesy.norm_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.norm_sq_eq

/-- info: 'Geodesy.ellipsoid_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.ellipsoid_self

/-- info: 'Geodesy.ReferenceEllipsoid.e2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.ReferenceEllipsoid.e2_eq

/-- info: 'Geodesy.ReferenceEllipsoid.ep2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.ReferenceEllipsoid.ep2_eq

/-- info: 'Geodesy.ReferenceEllipsoid.b_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.ReferenceEllipsoid.b_sq

/-- info: 'Geodesy.ReferenceEllipsoid.isSphere_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.ReferenceEllipsoid.isSphere_tfae

/-- info: 'Geodesy.ReferenceEllipsoid.ofSphere_toSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.ReferenceEllipsoid.ofSphere_toSet

/-- info: 'Geodesy.wgs84_b_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.wgs84_b_bounds

/-- info: 'Geodesy.wgs84_e2_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.wgs84_e2_bounds

/-- info: 'Geodesy.grs80_b_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.grs80_b_bounds

/-- info: 'Geodesy.wgs84_a_sub_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.wgs84_a_sub_b

/-- info: 'Geodesy.wgs84_b_sub_grs80_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.wgs84_b_sub_grs80_b

/-- info: 'Geodesy.GeodeticLongitude.toDegrees_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.GeodeticLongitude.toDegrees_mem

/-- info: 'Geodesy.GeodeticLongitude.antimeridian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.GeodeticLongitude.antimeridian

/-- info: 'Geodesy.GeodeticLongitude.toDegrees_ofDegrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.GeodeticLongitude.toDegrees_ofDegrees

/-- info: 'Geodesy.GeodeticLongitude.toDegrees_ofDegrees_neg180' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.GeodeticLongitude.toDegrees_ofDegrees_neg180

/-- info: 'Geodesy.ReferenceEllipsoid.primeVerticalRadius_pi_div_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.ReferenceEllipsoid.primeVerticalRadius_pi_div_two

/-- info: 'Geodesy.ReferenceEllipsoid.meridianPoint_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.ReferenceEllipsoid.meridianPoint_mem

/-- info: 'Geodesy.ReferenceEllipsoid.meridianNormal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.ReferenceEllipsoid.meridianNormal_eq

/-- info: 'Geodesy.ReferenceEllipsoid.geocentric_tan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.ReferenceEllipsoid.geocentric_tan

/-- info: 'Geodesy.ReferenceEllipsoid.geocentric_tan_of_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.ReferenceEllipsoid.geocentric_tan_of_sphere

/-- info: 'Geodesy.ReferenceEllipsoid.abs_geocentric_tan_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.ReferenceEllipsoid.abs_geocentric_tan_le

/-- info: 'Geodesy.GeodeticCoordinate.norm_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.GeodeticCoordinate.norm_normal

/-- info: 'Geodesy.GeodeticCoordinate.surfacePoint_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.GeodeticCoordinate.surfacePoint_mem

/-- info: 'Geodesy.GeodeticCoordinate.gradient_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.GeodeticCoordinate.gradient_eq

/-- info: 'Geodesy.GeodeticCoordinate.toECEF_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.GeodeticCoordinate.toECEF_eq

/-- info: 'Geodesy.GeodeticCoordinate.toECEF_of_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.GeodeticCoordinate.toECEF_of_sphere

/-- info: 'Geodesy.GeodeticCoordinate.norm_toECEF_of_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Geodesy.GeodeticCoordinate.norm_toECEF_of_sphere
