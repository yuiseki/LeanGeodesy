import LeanGeodesy.GeodeticCoordinate
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Mercator function

Mercator's projection keeps longitude as the horizontal coordinate and
stretches latitude vertically by

```
y = arsinh (tan φ) = ln (tan (π/4 + φ/2))
```

on the unit sphere. The second form is the one in textbooks
(`mercatorY_eq_log_tan`); the first is easier to reason about. Its inverse is
the Gudermannian function `φ = arctan (sinh y)`.

This file proves that the function is a bijection from the open latitude
interval `(-π/2, π/2)` onto the whole real line (`gd_mercatorY`,
`mercatorY_gd`), that it preserves north and south (`mercatorY_strictMonoOn`,
`mercatorY_neg`), that it grows without bound towards the pole
(`tendsto_mercatorY_pi_div_two`), so the poles themselves can never be
drawn, and that its derivative is `sec φ` (`hasDerivAt_mercatorY`), which is
what makes the projection conformal.

## Mercator is conformal on the sphere

A map projection sends the point at latitude `φ` and longitude `λ` on a
sphere of radius `R` to a point of the plane. Mercator's sends it to

```
x = R λ,   y = R · mercatorY φ.
```

Moving a little along the meridian or along the parallel traces a tangent
vector on the sphere (`hasDerivAt_spherePoint_lat`,
`hasDerivAt_spherePoint_lon`) and a tangent vector on the map
(`hasDerivAt_mercator_lat`, `hasDerivAt_mercator_lon`). On the sphere the
two are perpendicular, of lengths `R` and `R cos φ`: parallels shrink
towards the poles. On the map they are perpendicular too, of lengths
`R sec φ` and `R`.

So both are stretched by the same factor `sec φ`, and because both pairs
are perpendicular, so is every combination of them (`conformal`): an
arbitrary direction on the sphere is stretched by exactly `sec φ`. That is
what conformal means. Shapes are kept locally, while scale grows with
latitude: distances double at 60° (`scaleFactor_60`) and areas quadruple
(`areaFactor_60`), which is why Greenland looks as large as Africa.
-/

namespace Geodesy.Projection

open Real Filter Topology


/-- The Mercator northing on the unit sphere. -/
noncomputable def mercatorY (φ : ℝ) : ℝ := arsinh (tan φ)

/-- The Gudermannian function, the inverse of `mercatorY`. -/
noncomputable def gd (y : ℝ) : ℝ := arctan (sinh y)

@[simp] theorem mercatorY_zero : mercatorY 0 = 0 := by simp [mercatorY]

/-- The southern hemisphere is the mirror image of the northern one. -/
theorem mercatorY_neg (φ : ℝ) : mercatorY (-φ) = -mercatorY φ := by
  simp [mercatorY, tan_neg, arsinh_neg]

/-- Further north is higher on the map. -/
theorem mercatorY_strictMonoOn : StrictMonoOn mercatorY (Set.Ioo (-(π / 2)) (π / 2)) :=
  arsinh_strictMono.comp_strictMonoOn strictMonoOn_tan

/-- Every northing comes from a latitude strictly between the poles. -/
theorem gd_mem (y : ℝ) : gd y ∈ Set.Ioo (-(π / 2)) (π / 2) :=
  ⟨neg_pi_div_two_lt_arctan _, arctan_lt_pi_div_two _⟩

/-- Projecting and then inverting gives the latitude back. -/
theorem gd_mercatorY {φ : ℝ} (h : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) : gd (mercatorY φ) = φ := by
  rw [gd, mercatorY, sinh_arsinh, arctan_tan h.1 h.2]

/-- Inverting and then projecting gives the northing back. -/
theorem mercatorY_gd (y : ℝ) : mercatorY (gd y) = y := by
  rw [gd, mercatorY, tan_arctan, arsinh_sinh]

/-- So `mercatorY` is a bijection from the open latitudes onto the real line. -/
theorem mercatorY_bijOn : Set.BijOn mercatorY (Set.Ioo (-(π / 2)) (π / 2)) Set.univ :=
  ⟨fun _ _ => trivial, mercatorY_strictMonoOn.injOn,
    fun y _ => ⟨gd y, gd_mem y, mercatorY_gd y⟩⟩

/-- Approaching the north pole, the northing grows without bound: the pole
is infinitely far up the map. -/
theorem tendsto_mercatorY_pi_div_two :
    Tendsto mercatorY (𝓝[<] (π / 2)) atTop :=
  sinhOrderIso.symm.tendsto_atTop.comp tendsto_tan_pi_div_two

theorem sqrt_one_add_tan_sq {φ : ℝ} (hc : 0 < cos φ) : √(1 + tan φ ^ 2) = 1 / cos φ := by
  rw [← inv_inv (1 + tan φ ^ 2), inv_one_add_tan_sq hc.ne', sqrt_inv, sqrt_sq hc.le, one_div]

/-- The derivative is `sec φ`. -/
theorem hasDerivAt_mercatorY {φ : ℝ} (hc : 0 < cos φ) :
    HasDerivAt mercatorY (1 / cos φ) φ := by
  have h := (hasDerivAt_arsinh (tan φ)).comp φ (hasDerivAt_tan hc.ne')
  rw [sqrt_one_add_tan_sq hc] at h
  convert h using 1
  field_simp
  ring

/-- The textbook form: `y = ln (tan (π/4 + φ/2))`. -/
theorem mercatorY_eq_log_tan {φ : ℝ} (h : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    mercatorY φ = log (tan (π / 4 + φ / 2)) := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo h
  -- Work with the half angle `u = φ / 2`, in `(-π/4, π/4)`.
  obtain ⟨u, rfl⟩ : ∃ u, φ = 2 * u := ⟨φ / 2, by ring⟩
  have hu : 2 * u / 2 = u := by ring
  rw [hu]
  have hpi := pi_pos
  -- `sin` and `cos` of `π/4 + u` are positive, since that angle is in `(0, π/2)`.
  have hs' : 0 < sin (π / 4 + u) :=
    sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2])
  have hc' : 0 < cos (π / 4 + u) := cos_pos_of_mem_Ioo ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [sin_add, sin_pi_div_four, cos_pi_div_four] at hs'
  rw [cos_add, sin_pi_div_four, cos_pi_div_four] at hc'
  have h2 : (0 : ℝ) < √2 := by positivity
  have hsum : 0 < cos u + sin u := by nlinarith
  have hdiff : 0 < cos u - sin u := by nlinarith
  rw [mercatorY, arsinh, sqrt_one_add_tan_sq hc, tan_eq_sin_div_cos, tan_eq_sin_div_cos,
    sin_add, cos_add, sin_pi_div_four, cos_pi_div_four, sin_two_mul, cos_two_mul]
  congr 1
  have hp := sin_sq_add_cos_sq u
  have hcos2 : 2 * cos u ^ 2 - 1 = (cos u - sin u) * (cos u + sin u) := by nlinarith
  rw [hcos2]
  have hd : √2 * cos u - √2 * sin u ≠ 0 := by nlinarith
  field_simp
  linear_combination (-(√2 * (cos u - sin u))) * hp

/-! ## Vectors in the plane -/

/-- The Euclidean plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The plane vector with coordinates `x, y`. -/
noncomputable def vec2 (x y : ℝ) : E2 := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![x, y]

@[simp] theorem vec2_0 (x y : ℝ) : vec2 x y 0 = x := rfl
@[simp] theorem vec2_1 (x y : ℝ) : vec2 x y 1 = y := rfl

theorem vec2_add (x y x' y' : ℝ) : vec2 x y + vec2 x' y' = vec2 (x + x') (y + y') := by
  ext i
  fin_cases i <;> rfl

theorem vec2_smul (c x y : ℝ) : c • vec2 x y = vec2 (c * x) (c * y) := by
  ext i
  fin_cases i <;> rfl

theorem norm_vec2_sq (x y : ℝ) : ‖vec2 x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [EuclideanSpace.norm_eq, sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_two]
  simp only [vec2_0, vec2_1, Real.norm_eq_abs, sq_abs]

theorem inner_vec2 (x y x' y' : ℝ) : inner (vec2 x y) (vec2 x' y') = x * x' + y * y' := by
  simp [vec2, PiLp.inner_apply, Fin.sum_univ_two]

/-- A curve in the plane is differentiated coordinate by coordinate. -/
theorem hasDerivAt_vec2 {f g : ℝ → ℝ} {f' g' t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) : HasDerivAt (fun s => vec2 (f s) (g s)) (vec2 f' g') t := by
  have hp : HasDerivAt (fun s => ![f s, g s]) ![f', g'] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i <;> simpa
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp

/-! ## The sphere and its tangents -/

variable (R : ℝ)

/-- The point of the sphere of radius `R` at latitude `φ` and longitude `lam`. -/
noncomputable def spherePoint (φ lam : ℝ) : E3 :=
  vec3 (R * cos φ * cos lam) (R * cos φ * sin lam) (R * sin φ)

/-- It is the ECEF position of the geodetic coordinate at height zero on a
spherical reference ellipsoid. -/
theorem spherePoint_eq_toECEF (hR : 0 < R) (lat : GeodeticLatitude) (lon : GeodeticLongitude) :
    spherePoint R lat.1 lon.toReal =
      GeodeticCoordinate.toECEF (ReferenceEllipsoid.ofSphere R hR) ⟨lat, lon, 0⟩ := by
  rw [GeodeticCoordinate.toECEF_of_sphere _ _ rfl]
  simp only [spherePoint, GeodeticCoordinate.normal, vec3_smul, Real.Angle.cos_toReal,
    Real.Angle.sin_toReal, ReferenceEllipsoid.ofSphere, add_zero]
  refine vec3_congr ?_ ?_ ?_ <;> ring

/-- The tangent to the meridian: the direction of increasing latitude. -/
noncomputable def meridianTangent (φ lam : ℝ) : E3 :=
  vec3 (-(R * sin φ * cos lam)) (-(R * sin φ * sin lam)) (R * cos φ)

/-- The tangent to the parallel: the direction of increasing longitude. -/
noncomputable def parallelTangent (φ lam : ℝ) : E3 :=
  vec3 (-(R * cos φ * sin lam)) (R * cos φ * cos lam) 0

theorem hasDerivAt_spherePoint_lat (φ lam : ℝ) :
    HasDerivAt (fun φ => spherePoint R φ lam) (meridianTangent R φ lam) φ := by
  unfold spherePoint meridianTangent
  refine hasDerivAt_vec3 ?_ ?_ ?_
  · convert (((hasDerivAt_cos φ).const_mul R).mul_const (cos lam)) using 1; ring
  · convert (((hasDerivAt_cos φ).const_mul R).mul_const (sin lam)) using 1; ring
  · exact (hasDerivAt_sin φ).const_mul R

theorem hasDerivAt_spherePoint_lon (φ lam : ℝ) :
    HasDerivAt (fun lam => spherePoint R φ lam) (parallelTangent R φ lam) lam := by
  unfold spherePoint parallelTangent
  refine hasDerivAt_vec3 ?_ ?_ ?_
  · convert ((hasDerivAt_cos lam).const_mul (R * cos φ)) using 1; ring
  · exact (hasDerivAt_sin lam).const_mul (R * cos φ)
  · exact hasDerivAt_const _ _

theorem norm_meridianTangent_sq (φ lam : ℝ) : ‖meridianTangent R φ lam‖ ^ 2 = R ^ 2 := by
  rw [meridianTangent, norm_vec3_sq]
  have h1 := sin_sq_add_cos_sq φ
  have h2 := sin_sq_add_cos_sq lam
  linear_combination R ^ 2 * sin φ ^ 2 * h2 + R ^ 2 * h1

/-- Parallels shrink towards the poles: the parallel at latitude `φ` has
radius `R cos φ`. -/
theorem norm_parallelTangent_sq (φ lam : ℝ) : ‖parallelTangent R φ lam‖ ^ 2 = (R * cos φ) ^ 2 := by
  rw [parallelTangent, norm_vec3_sq]
  have h2 := sin_sq_add_cos_sq lam
  linear_combination (R * cos φ) ^ 2 * h2

/-- Meridians and parallels cross at right angles. -/
theorem inner_meridianTangent_parallelTangent (φ lam : ℝ) :
    inner (meridianTangent R φ lam) (parallelTangent R φ lam) = (0 : ℝ) := by
  rw [meridianTangent, parallelTangent, inner_vec3]
  ring

/-! ## The map -/

/-- Mercator's projection of the sphere of radius `R`. -/
noncomputable def mercator (φ lam : ℝ) : E2 := vec2 (R * lam) (R * mercatorY φ)

theorem hasDerivAt_mercator_lat {φ : ℝ} (hc : 0 < cos φ) (lam : ℝ) :
    HasDerivAt (fun φ => mercator R φ lam) (vec2 0 (R / cos φ)) φ := by
  unfold mercator
  refine hasDerivAt_vec2 (hasDerivAt_const _ _) ?_
  convert (hasDerivAt_mercatorY hc).const_mul R using 1
  ring

theorem hasDerivAt_mercator_lon (φ lam : ℝ) :
    HasDerivAt (fun lam => mercator R φ lam) (vec2 R 0) lam := by
  unfold mercator
  refine hasDerivAt_vec2 ?_ (hasDerivAt_const _ _)
  simpa using (hasDerivAt_id lam).const_mul R

/-- The scale factor of Mercator's projection at latitude `φ`. -/
noncomputable def scaleFactor (φ : ℝ) : ℝ := 1 / cos φ

/-- Mercator is conformal: every tangent direction on the sphere, a
combination `α` of the meridian and `β` of the parallel, is stretched by the
same factor `sec φ`, whatever its direction. -/
theorem conformal {φ : ℝ} (hc : 0 < cos φ) (lam α β : ℝ) :
    ‖α • vec2 0 (R / cos φ) + β • vec2 R 0‖ =
      scaleFactor φ * ‖α • meridianTangent R φ lam + β • parallelTangent R φ lam‖ := by
  have hk : 0 < scaleFactor φ := one_div_pos.mpr hc
  have hsq : ‖α • vec2 0 (R / cos φ) + β • vec2 R 0‖ ^ 2 =
      (scaleFactor φ * ‖α • meridianTangent R φ lam + β • parallelTangent R φ lam‖) ^ 2 := by
    rw [mul_pow, meridianTangent, parallelTangent, vec2_smul, vec2_smul, vec2_add, vec3_smul,
      vec3_smul, vec3_add, norm_vec2_sq, norm_vec3_sq, scaleFactor]
    have h1 := sin_sq_add_cos_sq φ
    have h2 := sin_sq_add_cos_sq lam
    field_simp
    linear_combination
      (-(α ^ 2 * R ^ 2 * sin φ ^ 2) - β ^ 2 * R ^ 2 * cos φ ^ 2) * h2 - α ^ 2 * R ^ 2 * h1
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hk.le (norm_nonneg _))).mp hsq

/-- At the equator the map is true to scale. -/
theorem scaleFactor_zero : scaleFactor 0 = 1 := by simp [scaleFactor]

/-- At 60° north or south, distances on the map are doubled. -/
theorem scaleFactor_60 : scaleFactor (degToRad 60) = 2 := by
  rw [scaleFactor, show degToRad 60 = π / 3 by unfold degToRad; ring, cos_pi_div_three]
  norm_num

/-- So areas at 60° are drawn four times too large. -/
theorem areaFactor_60 : scaleFactor (degToRad 60) ^ 2 = 4 := by
  rw [scaleFactor_60]
  norm_num

end Geodesy.Projection
