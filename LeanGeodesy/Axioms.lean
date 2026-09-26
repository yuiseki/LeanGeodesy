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
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.degToRad_radToDeg

/-- info: 'Geodesy.radToDeg_degToRad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.radToDeg_degToRad

/-- info: 'Geodesy.degToRad_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.degToRad_strictMono

/-- info: 'Geodesy.dms_carry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.dms_carry

/-- info: 'Geodesy.norm_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.norm_sq_eq

/-- info: 'Geodesy.ellipsoid_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ellipsoid_self

/-- info: 'Geodesy.ReferenceEllipsoid.e2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.e2_eq

/-- info: 'Geodesy.ReferenceEllipsoid.ep2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.ep2_eq

/-- info: 'Geodesy.ReferenceEllipsoid.b_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.b_sq

/-- info: 'Geodesy.ReferenceEllipsoid.isSphere_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.isSphere_tfae

/-- info: 'Geodesy.ReferenceEllipsoid.ofSphere_toSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.ofSphere_toSet

/-- info: 'Geodesy.wgs84_b_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.wgs84_b_bounds

/-- info: 'Geodesy.wgs84_e2_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.wgs84_e2_bounds

/-- info: 'Geodesy.grs80_b_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.grs80_b_bounds

/-- info: 'Geodesy.wgs84_a_sub_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.wgs84_a_sub_b

/-- info: 'Geodesy.wgs84_b_sub_grs80_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.wgs84_b_sub_grs80_b

/-- info: 'Geodesy.GeodeticLongitude.toDegrees_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticLongitude.toDegrees_mem

/-- info: 'Geodesy.GeodeticLongitude.antimeridian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticLongitude.antimeridian

/-- info: 'Geodesy.GeodeticLongitude.toDegrees_ofDegrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticLongitude.toDegrees_ofDegrees

/-- info: 'Geodesy.GeodeticLongitude.toDegrees_ofDegrees_neg180' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticLongitude.toDegrees_ofDegrees_neg180

/-- info: 'Geodesy.ReferenceEllipsoid.primeVerticalRadius_pi_div_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.primeVerticalRadius_pi_div_two

/-- info: 'Geodesy.ReferenceEllipsoid.meridianPoint_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.meridianPoint_mem

/-- info: 'Geodesy.ReferenceEllipsoid.meridianNormal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.meridianNormal_eq

/-- info: 'Geodesy.ReferenceEllipsoid.geocentric_tan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.geocentric_tan

/-- info: 'Geodesy.ReferenceEllipsoid.geocentric_tan_of_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.geocentric_tan_of_sphere

/-- info: 'Geodesy.ReferenceEllipsoid.abs_geocentric_tan_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.abs_geocentric_tan_le

/-- info: 'Geodesy.GeodeticCoordinate.norm_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticCoordinate.norm_normal

/-- info: 'Geodesy.GeodeticCoordinate.surfacePoint_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticCoordinate.surfacePoint_mem

/-- info: 'Geodesy.GeodeticCoordinate.gradient_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticCoordinate.gradient_eq

/-- info: 'Geodesy.GeodeticCoordinate.toECEF_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticCoordinate.toECEF_eq

/-- info: 'Geodesy.GeodeticCoordinate.toECEF_of_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticCoordinate.toECEF_of_sphere

/-- info: 'Geodesy.GeodeticCoordinate.norm_toECEF_of_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticCoordinate.norm_toECEF_of_sphere

/-- info: 'Geodesy.ReferenceEllipsoid.hasDerivAt_primeVerticalRadius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.hasDerivAt_primeVerticalRadius

/-- info: 'Geodesy.ReferenceEllipsoid.hasDerivAt_meridianPoint_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.hasDerivAt_meridianPoint_fst

/-- info: 'Geodesy.ReferenceEllipsoid.hasDerivAt_meridianPoint_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.hasDerivAt_meridianPoint_snd

/-- info: 'Geodesy.ReferenceEllipsoid.hasDerivAt_ellipsoidPoint_lat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.hasDerivAt_ellipsoidPoint_lat

/-- info: 'Geodesy.ReferenceEllipsoid.norm_meridianTangent_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.norm_meridianTangent_sq

/-- info: 'Geodesy.ReferenceEllipsoid.inner_meridianTangent_parallelTangent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.inner_meridianTangent_parallelTangent

/-- info: 'Geodesy.ReferenceEllipsoid.N_div_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.N_div_M

/-- info: 'Geodesy.Projection.gd_mercatorY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.gd_mercatorY

/-- info: 'Geodesy.Projection.mercatorY_gd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.mercatorY_gd

/-- info: 'Geodesy.Projection.mercatorY_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.mercatorY_bijOn

/-- info: 'Geodesy.Projection.tendsto_mercatorY_pi_div_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.tendsto_mercatorY_pi_div_two

/-- info: 'Geodesy.Projection.hasDerivAt_mercatorY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.hasDerivAt_mercatorY

/-- info: 'Geodesy.Projection.mercatorY_eq_log_tan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.mercatorY_eq_log_tan

/-- info: 'Geodesy.Projection.spherePoint_eq_toECEF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.spherePoint_eq_toECEF

/-- info: 'Geodesy.Projection.hasDerivAt_spherePoint_lat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.hasDerivAt_spherePoint_lat

/-- info: 'Geodesy.Projection.hasDerivAt_mercator_lat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.hasDerivAt_mercator_lat

/-- info: 'Geodesy.Projection.conformal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.conformal

/-- info: 'Geodesy.Projection.scaleFactor_60' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.scaleFactor_60

/-- info: 'Geodesy.Projection.halfExtent_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.halfExtent_bounds

/-- info: 'Geodesy.Projection.x_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.x_mem

/-- info: 'Geodesy.Projection.y_maxLatitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.y_maxLatitude

/-- info: 'Geodesy.Projection.y_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.y_mem_iff

/-- info: 'Geodesy.Projection.webMercatorInverse_webMercator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.webMercatorInverse_webMercator

/-- info: 'Geodesy.Projection.pixel_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.pixel_mem

/-- info: 'Geodesy.Projection.groundResolution_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.groundResolution_eq

/-- info: 'Geodesy.Projection.groundResolution_zero_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.groundResolution_zero_bounds

/-- info: 'Geodesy.Projection.scale_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.scale_ratio

/-- info: 'Geodesy.Projection.meridianScale_eq_parallelScale_of_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.meridianScale_eq_parallelScale_of_sphere

/-- info: 'Geodesy.Projection.meridianScale_gt_parallelScale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.meridianScale_gt_parallelScale

/-- info: 'Geodesy.Projection.wgs84_equator_scale_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.wgs84_equator_scale_ratio

/-- info: 'Geodesy.GeographicCRS.toPoint_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeographicCRS.toPoint_mem

/-- info: 'Geodesy.GeographicCRS.toPoint_eq_toECEF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeographicCRS.toPoint_eq_toECEF

/-- info: 'Geodesy.ProjectedCRS.unproject_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ProjectedCRS.unproject_project

/-- info: 'Geodesy.ProjectedCRS.project_unproject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ProjectedCRS.project_unproject

/-- info: 'Geodesy.ProjectedCRS.forward_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ProjectedCRS.forward_bijOn

/-- info: 'Geodesy.ProjectedCRS.inverse_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ProjectedCRS.inverse_bijOn

/-- info: 'Geodesy.ProjectedCRS.toPoint_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ProjectedCRS.toPoint_project

/-- info: 'Geodesy.wgs84Geographic_toPoint_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.wgs84Geographic_toPoint_mem

/-- info: 'Geodesy.webMercatorCRS_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.webMercatorCRS_forward

/-- info: 'Geodesy.webMercatorCRS_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.webMercatorCRS_project

/-- info: 'Geodesy.webMercatorCRS_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.webMercatorCRS_domain

/-- info: 'Geodesy.mem_webMercatorCRS_domain_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.mem_webMercatorCRS_domain_iff

/-- info: 'Geodesy.northPole_not_mem_webMercatorCRS_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.northPole_not_mem_webMercatorCRS_domain

/-- info: 'Geodesy.webMercatorCRS_unproject_project' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.webMercatorCRS_unproject_project

/-- info: 'Geodesy.webMercatorCRS_project_unproject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.webMercatorCRS_project_unproject

/-- info: 'Geodesy.Geodesic.angle_le_angle_add_angle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.angle_le_angle_add_angle

/-- info: 'Geodesy.Geodesic.normal_eq_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.normal_eq_direction

/-- info: 'Geodesy.Geodesic.cos_centralAngle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.cos_centralAngle

/-- info: 'Geodesy.Geodesic.haversine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.haversine

/-- info: 'Geodesy.Geodesic.centralAngle_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.centralAngle_eq_zero_iff

/-- info: 'Geodesy.Geodesic.centralAngle_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.centralAngle_triangle

/-- info: 'Geodesy.Geodesic.centralAngle_same_meridian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.centralAngle_same_meridian

/-- info: 'Geodesy.Geodesic.centralAngle_meridian_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.centralAngle_meridian_add

/-- info: 'Geodesy.Geodesic.centralAngle_equator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.centralAngle_equator

/-- info: 'Geodesy.Geodesic.centralAngle_poles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.centralAngle_poles

/-- info: 'Geodesy.Geodesic.greatCircleDistance_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.greatCircleDistance_le

/-- info: 'Geodesy.Geodesic.greatCircleDistance_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.greatCircleDistance_eq_zero_iff

/-- info: 'Geodesy.Geodesic.greatCircleDistance_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.greatCircleDistance_triangle

/-- info: 'Geodesy.Geodesic.arcMinute_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.arcMinute_bounds

/-- info: 'Geodesy.Projection.cos_maxLatitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.cos_maxLatitude

/-- info: 'Geodesy.Projection.exp_pi_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.exp_pi_bounds

/-- info: 'Geodesy.Projection.inv_cosh_pi_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.inv_cosh_pi_bounds

/-- info: 'Geodesy.Projection.maxLatitude_deg_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.maxLatitude_deg_bounds

/-- info: 'Geodesy.Geodesic.angle_le_sum_angle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.angle_le_sum_angle

/-- info: 'Geodesy.Geodesic.greatArc_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.greatArc_one

/-- info: 'Geodesy.Geodesic.norm_greatArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.norm_greatArc

/-- info: 'Geodesy.Geodesic.angle_greatArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.angle_greatArc

/-- info: 'Geodesy.Geodesic.sum_angle_greatArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.sum_angle_greatArc

/-- info: 'Geodesy.Geodesic.angle_add_angle_greatArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.angle_add_angle_greatArc

/-- info: 'Geodesy.Geodesic.greatCircleDistance_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.greatCircleDistance_le_sum

/-- info: 'Geodesy.Geodesic.eq_greatArc_of_angle_add_angle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.eq_greatArc_of_angle_add_angle

/-- info: 'Geodesy.Geodesic.angle_add_angle_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.angle_add_angle_eq_iff

/-- info: 'Geodesy.Geodesic.angle_le_angularLength' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.angle_le_angularLength

/-- info: 'Geodesy.Geodesic.angularLength_greatArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.angularLength_greatArc

/-- info: 'Geodesy.Geodesic.angularLength_greatArc_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.angularLength_greatArc_le

/-- info: 'Geodesy.Geodesic.mem_greatArc_of_angularLength_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Geodesic.mem_greatArc_of_angularLength_eq

/-- info: 'Geodesy.ReferenceEllipsoid.meridianRadius_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.meridianRadius_zero

/-- info: 'Geodesy.ReferenceEllipsoid.meridianRadius_pi_div_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.meridianRadius_pi_div_two

/-- info: 'Geodesy.ReferenceEllipsoid.meridianRadius_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.meridianRadius_mem

/-- info: 'Geodesy.ReferenceEllipsoid.meridianRadius_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.meridianRadius_strictMonoOn

/-- info: 'Geodesy.ReferenceEllipsoid.hasDerivAt_meridianArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.hasDerivAt_meridianArc

/-- info: 'Geodesy.ReferenceEllipsoid.meridianArc_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.meridianArc_strictMono

/-- info: 'Geodesy.ReferenceEllipsoid.meridianArc_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.meridianArc_neg

/-- info: 'Geodesy.ReferenceEllipsoid.meridianArc_of_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.meridianArc_of_sphere

/-- info: 'Geodesy.ReferenceEllipsoid.meridianArc_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.meridianArc_bounds

/-- info: 'Geodesy.ReferenceEllipsoid.meridianArc_band_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.meridianArc_band_lt

/-- info: 'Geodesy.wgs84_first_degree_lt_last_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.wgs84_first_degree_lt_last_degree

/-- info: 'Geodesy.inv_cube_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.inv_cube_bounds

/-- info: 'Geodesy.integral_poly_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.integral_poly_sin

/-- info: 'Geodesy.ReferenceEllipsoid.meridianRadius_poly_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.meridianRadius_poly_bounds

/-- info: 'Geodesy.ReferenceEllipsoid.quarterMeridian_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.quarterMeridian_bounds

/-- info: 'Geodesy.wgs84_quarterMeridian_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.wgs84_quarterMeridian_bounds

/-- info: 'Geodesy.GeodeticCoordinate.ecefLongitude_toECEF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticCoordinate.ecefLongitude_toECEF

/-- info: 'Geodesy.GeodeticCoordinate.toECEF_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticCoordinate.toECEF_p

/-- info: 'Geodesy.GeodeticCoordinate.latitudeResidual_toECEF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticCoordinate.latitudeResidual_toECEF

/-- info: 'Geodesy.GeodeticCoordinate.height_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeodeticCoordinate.height_eq

/-- info: 'Geodesy.exists_latitudeResidual_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.exists_latitudeResidual_eq_zero

/-- info: 'Geodesy.toECEF_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.toECEF_surjective

/-- info: 'Geodesy.sphereInverse_toECEF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.sphereInverse_toECEF

/-- info: 'Geodesy.Helmert.dist_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Helmert.dist_apply

/-- info: 'Geodesy.Helmert.comp_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Helmert.comp_apply

/-- info: 'Geodesy.Helmert.inv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Helmert.inv_apply

/-- info: 'Geodesy.Helmert.apply_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Helmert.apply_inv

/-- info: 'Geodesy.norm_cross_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.norm_cross_sq

/-- info: 'Geodesy.norm_smallRotation_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.norm_smallRotation_sq

/-- info: 'Geodesy.norm_smallRotation_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.norm_smallRotation_eq_iff

/-- info: 'Geodesy.norm_smallRotation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.norm_smallRotation_le

/-- info: 'Geodesy.smallRotation_error_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.smallRotation_error_small

/-- info: 'Geodesy.GeographicCRS.toPoint3D_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.GeographicCRS.toPoint3D_surjective

/-- info: 'Geodesy.CRSTransformation.toPoint3D_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.CRSTransformation.toPoint3D_transform

/-- info: 'Geodesy.CRSTransformation.toPoint3D_inverse_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.CRSTransformation.toPoint3D_inverse_transform

/-- info: 'Geodesy.CRSTransformation.dist_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.CRSTransformation.dist_transform

/-- info: 'Geodesy.Projection.LocalDistortion.tissot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.LocalDistortion.tissot

/-- info: 'Geodesy.Projection.LocalDistortion.areaScale_of_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.LocalDistortion.areaScale_of_orthogonal

/-- info: 'Geodesy.Projection.LocalDistortion.isConformal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.LocalDistortion.isConformal_iff

/-- info: 'Geodesy.Projection.LocalDistortion.areaScale_of_isConformal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.LocalDistortion.areaScale_of_isConformal

/-- info: 'Geodesy.Projection.cylindrical_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.cylindrical_h

/-- info: 'Geodesy.Projection.cylindrical_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.cylindrical_k

/-- info: 'Geodesy.Projection.cylindrical_areaScale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.cylindrical_areaScale

/-- info: 'Geodesy.Projection.cylindrical_isConformal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.cylindrical_isConformal_iff

/-- info: 'Geodesy.Projection.cylindrical_isEqualArea_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.cylindrical_isEqualArea_iff

/-- info: 'Geodesy.Projection.mercator_isConformal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.mercator_isConformal

/-- info: 'Geodesy.Projection.mercator_areaScale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.mercator_areaScale

/-- info: 'Geodesy.Projection.plateCarree_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.plateCarree_h

/-- info: 'Geodesy.Projection.lambert_isEqualArea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.lambert_isEqualArea

/-- info: 'Geodesy.Projection.eq_mercatorY_of_isConformal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.eq_mercatorY_of_isConformal

/-- info: 'Geodesy.Projection.eq_sin_of_isEqualArea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.eq_sin_of_isEqualArea

/-- info: 'Geodesy.Projection.eq_zero_of_isConformal_of_isEqualArea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.eq_zero_of_isConformal_of_isEqualArea

/-- info: 'Geodesy.Projection.ellipsoidalMercator_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.ellipsoidalMercator_h

/-- info: 'Geodesy.Projection.ellipsoidalMercator_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.ellipsoidalMercator_k

/-- info: 'Geodesy.Projection.ellipsoidalMercator_not_isConformal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.ellipsoidalMercator_not_isConformal

/-- info: 'Geodesy.Projection.tmY_central' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.tmY_central

/-- info: 'Geodesy.Projection.tmB_sq_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.tmB_sq_lt_one

/-- info: 'Geodesy.Projection.hasDerivAt_mercatorY_arcsin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.hasDerivAt_mercatorY_arcsin

/-- info: 'Geodesy.Projection.hasDerivAt_tmX_lat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.hasDerivAt_tmX_lat

/-- info: 'Geodesy.Projection.hasDerivAt_tmX_lon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.hasDerivAt_tmX_lon

/-- info: 'Geodesy.Projection.hasDerivAt_tmY_lat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.hasDerivAt_tmY_lat

/-- info: 'Geodesy.Projection.hasDerivAt_tmY_lon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.hasDerivAt_tmY_lon

/-- info: 'Geodesy.Projection.tm_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.tm_orthogonal

/-- info: 'Geodesy.Projection.tm_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.tm_h

/-- info: 'Geodesy.Projection.tm_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.tm_k

/-- info: 'Geodesy.Projection.tm_isConformal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.tm_isConformal

/-- info: 'Geodesy.Projection.tmScale_central' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.tmScale_central

/-- info: 'Geodesy.Projection.one_lt_tmScale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.one_lt_tmScale

/-- info: 'Geodesy.Projection.utmScale_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.utmScale_bounds

/-- info: 'Geodesy.Projection.utmScale_equator_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.utmScale_equator_eq_one_iff

/-- info: 'Geodesy.toWebMercator_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.toWebMercator_pt

/-- info: 'Geodesy.fromWebMercator_lat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.fromWebMercator_lat

/-- info: 'Geodesy.fromWebMercator_lon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.fromWebMercator_lon

/-- info: 'Geodesy.fromWebMercator_toWebMercator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.fromWebMercator_toWebMercator

/-- info: 'Geodesy.toWebMercator_fromWebMercator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.toWebMercator_fromWebMercator

/-- info: 'Geodesy.webMercatorConversion_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.webMercatorConversion_bijOn

/-- info: 'Geodesy.toWebMercator_equator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.toWebMercator_equator

/-- info: 'Geodesy.toWebMercator_primeMeridian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.toWebMercator_primeMeridian

/-- info: 'Geodesy.toWebMercator_maxLatitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.toWebMercator_maxLatitude

/-- info: 'Geodesy.toWebMercator_neg_maxLatitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.toWebMercator_neg_maxLatitude

/-- info: 'Geodesy.toWebMercator_antimeridian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.toWebMercator_antimeridian

/-- info: 'Geodesy.toWebMercator_x_ne_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.toWebMercator_x_ne_left

/-- info: 'Geodesy.Projection.sphereCellArea_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.sphereCellArea_eq

/-- info: 'Geodesy.Projection.lambertCylindrical_preserves_cellArea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.lambertCylindrical_preserves_cellArea

/-- info: 'Geodesy.Projection.mercatorY_sub_sin_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.mercatorY_sub_sin_strictMonoOn

/-- info: 'Geodesy.Projection.mercator_enlarges_cellArea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.mercator_enlarges_cellArea

/-- info: 'Geodesy.Projection.lambertCylindrical_not_isConformal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.lambertCylindrical_not_isConformal

/-- info: 'Geodesy.Projection.webMercator_areaScale_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.webMercator_areaScale_gt_one

/-- info: 'Geodesy.Projection.webMercator_not_isEqualArea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.webMercator_not_isEqualArea

/-- info: 'Geodesy.Projection.wgs84_webMercator_not_isEqualArea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.wgs84_webMercator_not_isEqualArea

/-- info: 'Geodesy.Projection.angle_northPole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.angle_northPole

/-- info: 'Geodesy.Projection.arcNormal_northPole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.arcNormal_northPole

/-- info: 'Geodesy.Projection.hasDerivAt_greatArc_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.hasDerivAt_greatArc_zero

/-- info: 'Geodesy.Projection.azimuthalEquidistant_preserves_azimuth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.azimuthalEquidistant_preserves_azimuth

/-- info: 'Geodesy.Projection.azimuthalEquidistant_preserves_distanceFromCentre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.azimuthalEquidistant_preserves_distanceFromCentre

/-- info: 'Geodesy.Projection.azimuthalEquidistant_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.azimuthalEquidistant_h

/-- info: 'Geodesy.Projection.one_lt_azimuthalEquidistant_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.one_lt_azimuthalEquidistant_k

/-- info: 'Geodesy.Projection.azimuthalEquidistant_not_isConformal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.azimuthalEquidistant_not_isConformal

/-- info: 'Geodesy.Projection.azimuthalEquidistant_not_isEqualArea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.azimuthalEquidistant_not_isEqualArea

/-- info: 'Geodesy.Projection.mercator_not_preserves_azimuth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.mercator_not_preserves_azimuth

/-- info: 'Geodesy.Projection.webMercator_not_preserves_azimuth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.webMercator_not_preserves_azimuth

/-- info: 'Geodesy.Projection.hasDerivAt_latitudeCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.hasDerivAt_latitudeCurve

/-- info: 'Geodesy.Projection.northComponent_latitudeCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.northComponent_latitudeCurve

/-- info: 'Geodesy.Projection.eastComponent_latitudeCurve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.eastComponent_latitudeCurve

/-- info: 'Geodesy.Projection.hasBearing_latitudeCurve_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.hasBearing_latitudeCurve_iff

/-- info: 'Geodesy.Projection.rhumb_hasBearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.rhumb_hasBearing

/-- info: 'Geodesy.Projection.mercator_rhumb_on_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.mercator_rhumb_on_line

/-- info: 'Geodesy.Projection.constantBearing_iff_mercatorLine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.constantBearing_iff_mercatorLine

/-- info: 'Geodesy.Projection.norm_rhumb_tangent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.norm_rhumb_tangent

/-- info: 'Geodesy.Projection.rhumb_curveLength' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.rhumb_curveLength

/-- info: 'Geodesy.Projection.parallel_hasBearing_east' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.parallel_hasBearing_east

/-- info: 'Geodesy.Projection.parallel_curveLength' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.parallel_curveLength

/-- info: 'Geodesy.Projection.centralAngle_A_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.centralAngle_A_B

/-- info: 'Geodesy.Projection.greatCircleDistance_A_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.greatCircleDistance_A_B

/-- info: 'Geodesy.Projection.greatCircle_initial_not_east' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.greatCircle_initial_not_east

/-- info: 'Geodesy.Projection.greatArc_midpoint_not_on_parallel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.greatArc_midpoint_not_on_parallel

/-- info: 'Geodesy.Projection.greatCircleDistance_lt_rhumb_A_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.greatCircleDistance_lt_rhumb_A_B

/-- info: 'Geodesy.Projection.mercator_distance_scaled_A_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.mercator_distance_scaled_A_B

/-- info: 'Geodesy.Projection.norm_azimuthalEquidistant_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.norm_azimuthalEquidistant_eq_iff

/-- info: 'Geodesy.Projection.aeqd_preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.aeqd_preimage

/-- info: 'Geodesy.Projection.image_geodesicCircle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.image_geodesicCircle

/-- info: 'Geodesy.Projection.image_geodesicDisk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.image_geodesicDisk

/-- info: 'Geodesy.Projection.mem_geodesicDisk_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.mem_geodesicDisk_iff

/-- info: 'Geodesy.Projection.capArea_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.capArea_eq

/-- info: 'Geodesy.Projection.volume_closedBall_E2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.volume_closedBall_E2

/-- info: 'Geodesy.Projection.volume_image_geodesicDisk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.volume_image_geodesicDisk

/-- info: 'Geodesy.Projection.azimuthalEquidistant_enlarges_buffer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.Projection.azimuthalEquidistant_enlarges_buffer

/-- info: 'Geodesy.ReferenceEllipsoid.firstFormE_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.firstFormE_eq

/-- info: 'Geodesy.ReferenceEllipsoid.firstFormF_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.firstFormF_eq

/-- info: 'Geodesy.ReferenceEllipsoid.firstFormG_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.firstFormG_eq

/-- info: 'Geodesy.ReferenceEllipsoid.firstFormG_pole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.firstFormG_pole

/-- info: 'Geodesy.ReferenceEllipsoid.metric_eq_EFG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.metric_eq_EFG

/-- info: 'Geodesy.ReferenceEllipsoid.metric_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.metric_comm

/-- info: 'Geodesy.ReferenceEllipsoid.metric_add_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.metric_add_left

/-- info: 'Geodesy.ReferenceEllipsoid.metric_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.metric_smul_left

/-- info: 'Geodesy.ReferenceEllipsoid.firstForm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.firstForm_nonneg

/-- info: 'Geodesy.ReferenceEllipsoid.metric_self_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.metric_self_eq_zero_iff

/-- info: 'Geodesy.ReferenceEllipsoid.firstForm_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.firstForm_pos

/-- info: 'Geodesy.ReferenceEllipsoid.inner_dr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.inner_dr

/-- info: 'Geodesy.ReferenceEllipsoid.norm_dr_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.norm_dr_sq

/-- info: 'Geodesy.ReferenceEllipsoid.hasDerivAt_curve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.hasDerivAt_curve

/-- info: 'Geodesy.ReferenceEllipsoid.speed_sq_curve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.speed_sq_curve

/-- info: 'Geodesy.ReferenceEllipsoid.cos_angle_dr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.cos_angle_dr

/-- info: 'Geodesy.ReferenceEllipsoid.metric_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Geodesy.ReferenceEllipsoid.metric_eq_zero_iff
