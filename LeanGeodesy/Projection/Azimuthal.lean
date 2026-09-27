import LeanGeodesy.Projection.Distortion
import LeanGeodesy.Geodesic
import LeanGeodesy.Projection.WebMercator

/-!
# An azimuthal projection

The azimuthal equidistant projection centred on the north pole draws the
point at latitude `φ` and longitude `λ` at distance `R (π/2 - φ)` from the
centre in the direction `λ`:

```
x = R (π/2 - φ) cos λ,   y = R (π/2 - φ) sin λ       (azimuthalEquidistant)
```

It is defined by what it keeps, and the proofs connect it to the great
circles of `Geodesic`. The tangent plane at the north pole is the `xy`
plane, so a direction there is read off by dropping the `z` coordinate
(`horizontal`).

- It keeps azimuths from the centre: the point is drawn exactly `R` times
  the horizontal part of the initial velocity of the great-circle arc from
  the pole to it (`azimuthalEquidistant_preserves_azimuth`), whose direction
  is `(cos λ, sin λ)` (`arcNormal_northPole`).
- It keeps distances from the centre: the point is drawn at the
  great-circle distance from the pole
  (`azimuthalEquidistant_preserves_distanceFromCentre`).
- Its scale is `1` along meridians (`azimuthalEquidistant_h`) and
  `(π/2 - φ) / cos φ > 1` along parallels (`azimuthalEquidistant_k`,
  `one_lt_azimuthalEquidistant_k`), so it is neither conformal nor
  equal-area (`azimuthalEquidistant_not_isConformal`,
  `azimuthalEquidistant_not_isEqualArea`).

Mercator, and so Web Mercator, does not keep azimuths from a centre. From
`c = (45° N, 0°)` to `p = (45° N, 90° E)` the map displacement points due
east, since both points have the same northing, but the great circle from
`c` to `p`, the shortest route, leaves `c` with a northward component
(`mercator_not_preserves_azimuth`, `webMercator_not_preserves_azimuth`).
Mercator is conformal and draws east as `+x` and north as `+y` at `c`
(`hasDerivAt_mercator_lon`, `hasDerivAt_mercator_lat`), so a straight line
on the map starts in a different direction from the route it joins.
-/

namespace Geodesy.Projection

open Real InnerProductGeometry Geodesic

/-- The north pole, as a unit vector. -/
noncomputable def northPole : E3 := direction (π / 2) 0

theorem direction_pi_div_two (lam : ℝ) : direction (π / 2) lam = northPole := by
  simp [northPole, direction]

/-- The angle from the north pole to latitude `φ` is `π/2 - φ`. -/
theorem angle_northPole {φ : ℝ} (hφ : φ ∈ Set.Icc (-(π / 2)) (π / 2)) (lam : ℝ) :
    angle northPole (direction φ lam) = π / 2 - φ := by
  have hpi := pi_pos
  have h := centralAngle_same_meridian ⟨by linarith, le_rfl⟩ hφ lam
  rw [centralAngle, direction_pi_div_two, abs_of_nonneg (by linarith [hφ.2])] at h
  exact h

/-- The direction in which the great circle from the north pole to `(φ, λ)`
leaves the pole is `(cos λ, sin λ, 0)`. -/
theorem arcNormal_northPole {φ : ℝ} (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) (lam : ℝ) :
    arcNormal northPole (direction φ lam) = vec3 (cos lam) (sin lam) 0 := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo hφ
  rw [arcNormal, angle_northPole ⟨hφ.1.le, hφ.2.le⟩, sin_pi_div_two_sub]
  have hi : (inner ℝ (direction φ lam) northPole : ℝ) = sin φ := by
    rw [northPole, direction, direction, inner_vec3, cos_pi_div_two, sin_pi_div_two]
    ring
  have hsub : direction φ lam - sin φ • northPole = cos φ • vec3 (cos lam) (sin lam) 0 := by
    ext i
    fin_cases i <;> simp [direction, northPole, vec3, cos_pi_div_two, sin_pi_div_two]
  rw [hi, hsub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- The great-circle arc leaves `u` with velocity `θ` times `arcNormal u w`. -/
theorem hasDerivAt_greatArc_zero (u w : E3) :
    HasDerivAt (greatArc u w) (angle u w • arcNormal u w) 0 := by
  have hc := ((hasDerivAt_id (0 : ℝ)).mul_const (angle u w)).cos.smul_const u
  have hs := ((hasDerivAt_id (0 : ℝ)).mul_const (angle u w)).sin.smul_const (arcNormal u w)
  have h := hc.add hs
  unfold greatArc
  convert h using 1 <;> (try rfl)
  simp

/-- A tangent vector at the north pole, read in the tangent plane. -/
noncomputable def horizontal (v : E3) : E2 := vec2 (v 0) (v 1)

theorem horizontal_smul (c : ℝ) (v : E3) : horizontal (c • v) = c • horizontal v := by
  simp [horizontal, vec2_smul]

/-- The azimuthal equidistant projection centred on the north pole. -/
noncomputable def azimuthalEquidistant (R φ lam : ℝ) : E2 :=
  vec2 (R * (π / 2 - φ) * cos lam) (R * (π / 2 - φ) * sin lam)

variable {R φ : ℝ}

/-- It keeps azimuths from the centre: each point is drawn `R` times the
horizontal part of the initial velocity of the great-circle arc from the pole
to it. -/
theorem azimuthalEquidistant_preserves_azimuth (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) (lam : ℝ) :
    ∃ v, HasDerivAt (greatArc northPole (direction φ lam)) v 0 ∧
      azimuthalEquidistant R φ lam = R • horizontal v := by
  refine ⟨_, hasDerivAt_greatArc_zero _ _, ?_⟩
  rw [arcNormal_northPole hφ, angle_northPole ⟨hφ.1.le, hφ.2.le⟩, horizontal_smul,
    horizontal, azimuthalEquidistant]
  simp only [vec3_0, vec3_1, vec2_smul]
  ring_nf

/-- It keeps distances from the centre. -/
theorem azimuthalEquidistant_preserves_distanceFromCentre (hR : 0 ≤ R)
    (hφ : φ ∈ Set.Icc (-(π / 2)) (π / 2)) (lam : ℝ) :
    ‖azimuthalEquidistant R φ lam‖ = greatCircleDistance R (π / 2) lam φ lam := by
  have hpi := pi_pos
  rw [greatCircleDistance, centralAngle, direction_pi_div_two, angle_northPole hφ]
  have hd : 0 ≤ R * (π / 2 - φ) := mul_nonneg hR (by linarith [hφ.2])
  rw [← sqrt_sq (norm_nonneg _), azimuthalEquidistant, norm_vec2_sq,
    show (R * (π / 2 - φ) * cos lam) ^ 2 + (R * (π / 2 - φ) * sin lam) ^ 2 =
      (R * (π / 2 - φ)) ^ 2 * (cos lam ^ 2 + sin lam ^ 2) by ring,
    cos_sq_add_sin_sq, mul_one, sqrt_sq hd]

/-! ## Distortion -/

theorem hasDerivAt_azimuthalEquidistant_lat (R φ lam : ℝ) :
    HasDerivAt (fun φ => azimuthalEquidistant R φ lam) (vec2 (-(R * cos lam)) (-(R * sin lam))) φ := by
  unfold azimuthalEquidistant
  refine hasDerivAt_vec2 ?_ ?_
  · convert (((hasDerivAt_id φ).const_sub (π / 2)).const_mul R).mul_const (cos lam) using 1 <;> (try rfl)
    simp
  · convert (((hasDerivAt_id φ).const_sub (π / 2)).const_mul R).mul_const (sin lam) using 1 <;> (try rfl)
    simp

theorem hasDerivAt_azimuthalEquidistant_lon (R φ lam : ℝ) :
    HasDerivAt (fun lam => azimuthalEquidistant R φ lam)
      (vec2 (-(R * (π / 2 - φ) * sin lam)) (R * (π / 2 - φ) * cos lam)) lam := by
  unfold azimuthalEquidistant
  refine hasDerivAt_vec2 ?_ ?_
  · convert (hasDerivAt_cos lam).const_mul (R * (π / 2 - φ)) using 1; ring
  · exact (hasDerivAt_sin lam).const_mul (R * (π / 2 - φ))

/-- The partial derivatives as a local distortion on the sphere of radius `R`. -/
noncomputable def azimuthalEquidistantDistortion (hR : 0 < R) (hc : 0 < cos φ) (lam : ℝ) :
    LocalDistortion :=
  ⟨R, R * cos φ, hR, mul_pos hR hc, vec2 (-(R * cos lam)) (-(R * sin lam)),
    vec2 (-(R * (π / 2 - φ) * sin lam)) (R * (π / 2 - φ) * cos lam)⟩

section Distortion

variable (hR : 0 < R) (hc : 0 < cos φ) (lam : ℝ)
include hR hc

theorem azimuthalEquidistant_orthogonal :
    (inner ℝ (azimuthalEquidistantDistortion hR hc lam).dLat
      (azimuthalEquidistantDistortion hR hc lam).dLon : ℝ) = 0 := by
  simp only [azimuthalEquidistantDistortion, inner_vec2]
  ring

/-- Distances along meridians are kept. -/
theorem azimuthalEquidistant_h : (azimuthalEquidistantDistortion hR hc lam).h = 1 := by
  simp only [LocalDistortion.h, azimuthalEquidistantDistortion]
  rw [← sqrt_sq (norm_nonneg _), norm_vec2_sq,
    show (-(R * cos lam)) ^ 2 + (-(R * sin lam)) ^ 2 = R ^ 2 * (cos lam ^ 2 + sin lam ^ 2) by ring,
    cos_sq_add_sin_sq, mul_one, sqrt_sq hR.le, div_self hR.ne']

/-- Along parallels the scale is `(π/2 - φ) / cos φ`. -/
theorem azimuthalEquidistant_k (hφ : φ < π / 2) :
    (azimuthalEquidistantDistortion hR hc lam).k = (π / 2 - φ) / cos φ := by
  simp only [LocalDistortion.k, azimuthalEquidistantDistortion]
  have hd : 0 ≤ R * (π / 2 - φ) := mul_nonneg hR.le (by linarith)
  rw [← sqrt_sq (norm_nonneg _), norm_vec2_sq,
    show (-(R * (π / 2 - φ) * sin lam)) ^ 2 + (R * (π / 2 - φ) * cos lam) ^ 2 =
      (R * (π / 2 - φ)) ^ 2 * (sin lam ^ 2 + cos lam ^ 2) by ring,
    sin_sq_add_cos_sq, mul_one, sqrt_sq hd]
  field_simp

/-- ...which exceeds `1` everywhere off the pole. -/
theorem one_lt_azimuthalEquidistant_k (hφ : φ < π / 2) :
    1 < (azimuthalEquidistantDistortion hR hc lam).k := by
  rw [azimuthalEquidistant_k hR hc lam hφ, one_lt_div hc, ← sin_pi_div_two_sub]
  exact sin_lt (by linarith)

/-- So it is not conformal... -/
theorem azimuthalEquidistant_not_isConformal (hφ : φ < π / 2) :
    ¬ (azimuthalEquidistantDistortion hR hc lam).IsConformal := fun h => by
  have := one_lt_azimuthalEquidistant_k hR hc lam hφ
  rw [← h.2, azimuthalEquidistant_h] at this
  exact lt_irrefl 1 this

/-- ...and not equal-area. -/
theorem azimuthalEquidistant_not_isEqualArea (hφ : φ < π / 2) :
    ¬ (azimuthalEquidistantDistortion hR hc lam).IsEqualArea := fun h => by
  have := one_lt_azimuthalEquidistant_k hR hc lam hφ
  rw [LocalDistortion.IsEqualArea, LocalDistortion.areaScale_of_orthogonal _
    (azimuthalEquidistant_orthogonal hR hc lam), azimuthalEquidistant_h, one_mul] at h
  rw [h] at this
  exact lt_irrefl 1 this

end Distortion

/-! ## Mercator does not keep azimuths -/

theorem inner_direction_45 :
    (inner ℝ (direction (π / 4) 0) (direction (π / 4) (π / 2)) : ℝ) = 1 / 2 := by
  rw [inner_direction, sub_eq_add_neg, zero_add, cos_neg, cos_pi_div_two, cos_pi_div_four,
    sin_pi_div_four]
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  nlinarith

theorem sin_angle_45_pos : 0 < sin (angle (direction (π / 4) 0) (direction (π / 4) (π / 2))) := by
  rw [angle, norm_direction, norm_direction, mul_one, div_one, inner_direction_45, sin_arccos]
  norm_num

/-- From `(45° N, 0°)` to `(45° N, 90° E)`, Mercator's map displacement points due
east, while the great circle leaves with a northward component: its initial
direction has positive inner product with the unit northward tangent. -/
theorem mercator_not_preserves_azimuth (hR : 0 < R) :
    (mercator R (π / 4) (π / 2) - mercator R (π / 4) 0) 1 = 0 ∧
      0 < (mercator R (π / 4) (π / 2) - mercator R (π / 4) 0) 0 ∧
      0 < (inner ℝ (arcNormal (direction (π / 4) 0) (direction (π / 4) (π / 2)))
        (meridianTangent 1 (π / 4) 0) : ℝ) := by
  have hpi := pi_pos
  refine ⟨by simp [mercator], by simp [mercator]; positivity, ?_⟩
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have hs := sin_angle_45_pos
  rw [arcNormal, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
    real_inner_comm (direction (π / 4) 0) (direction (π / 4) (π / 2)), inner_direction_45]
  apply mul_pos (inv_pos.mpr hs)
  simp only [direction, meridianTangent, inner_vec3, cos_pi_div_two, sin_pi_div_two, cos_zero,
    sin_zero, cos_pi_div_four, sin_pi_div_four]
  nlinarith

/-- The same holds for Web Mercator, which is Mercator's projection of the sphere
of radius `a`. -/
theorem webMercator_not_preserves_azimuth :
    (mercator webMercatorRadius (π / 4) (π / 2) - mercator webMercatorRadius (π / 4) 0) 1 = 0 ∧
      0 < (mercator webMercatorRadius (π / 4) (π / 2) - mercator webMercatorRadius (π / 4) 0) 0 ∧
      0 < (inner ℝ (arcNormal (direction (π / 4) 0) (direction (π / 4) (π / 2)))
        (meridianTangent 1 (π / 4) 0) : ℝ) :=
  mercator_not_preserves_azimuth webMercatorRadius_pos

end Geodesy.Projection
