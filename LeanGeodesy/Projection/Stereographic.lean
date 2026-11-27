import LeanGeodesy.Projection.Azimuthal
import LeanGeodesy.Angle
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Polar stereographic projection and UPS

Mercator and transverse Mercator blow up at the poles or cut them off. To map
the polar regions conformally, GIS and military/aviation grids pair UTM
(`80° S` to `84° N`) with the *Universal Polar Stereographic* (UPS) system over
the poles.

Projecting the sphere of radius `R` from the south pole onto the tangent plane
at the north pole sends `(φ, λ)` (`φ > -π/2`) to radial distance

```
r(φ) = R · 2 cos φ / (1 + sin φ) = 2 R tan ((π/2 - φ) / 2)
```

in the direction `(cos λ, sin λ)` (`stereographicFactor`, `stereographic`):

- at the north pole `φ = π/2` it lands smoothly at the origin (`stereographic_northPole`);
- `stereographicFactor` is a bijection from `(-π/2, π/2]` onto `[0, ∞)` with
  closed-form inverse `stereographicLat u = π/2 - 2 arctan (u / 2)`
  (`stereographicLat_factor`, `stereographicFactor_lat`, `stereographicFactor_bijOn`);
- it preserves azimuths from the north pole (`stereographic_preserves_azimuth`)
  and maps circles of constant latitude to Euclidean circles centred at the
  origin (`norm_stereographic`);
- it is conformal everywhere on `(-π/2, π/2)` (`stereographic_isConformal`),
  with isotropic scale `2 / (1 + sin φ)` (`1` at the north pole, `2` at the
  equator);
- UPS multiplies by `k₀ = 0.994` (`upsScale`), keeping the scale in
  `[0.994, 1)` across the entire north UPS zone `[84° N, 90° N]`
  (`upsScale_bounds_84`) and in `[0.994, 1.0017)` down to `80° N`
  (`upsScale_bounds_80`), with exact unit scale at `sin φ = 0.988`
  (`upsScale_eq_one_iff`).
-/

namespace Geodesy.Projection

open Real Geodesic

/-- The dimensionless radial factor `2 cos φ / (1 + sin φ)` of the north-polar
stereographic projection. -/
noncomputable def stereographicFactor (φ : ℝ) : ℝ :=
  2 * cos φ / (1 + sin φ)

/-- The inverse latitude map `π/2 - 2 arctan (u / 2)` for radial factor `u ≥ 0`. -/
noncomputable def stereographicLat (u : ℝ) : ℝ :=
  π / 2 - 2 * arctan (u / 2)

/-- North-polar stereographic projection of the sphere of radius `R` onto the
plane tangent at the north pole. -/
noncomputable def stereographic (R φ lam : ℝ) : E2 :=
  vec2 (R * stereographicFactor φ * cos lam) (R * stereographicFactor φ * sin lam)

/-- The isotropic local scale factor `2 / (1 + sin φ)` of polar stereographic. -/
noncomputable def stereographicScale (φ : ℝ) : ℝ :=
  2 / (1 + sin φ)

theorem one_add_sin_pos {φ : ℝ} (hφ : -(π / 2) < φ) (hhi : φ ≤ π / 2) :
    0 < 1 + sin φ := by
  have hlt : -1 < sin φ := by
    have hsn : sin (-(π / 2)) = -1 := by simp
    rw [← hsn]
    exact strictMonoOn_sin
      ⟨le_rfl, by linarith [pi_pos]⟩
      ⟨hφ.le, hhi⟩
      hφ
  linarith

@[simp] theorem stereographicFactor_pi_div_two : stereographicFactor (π / 2) = 0 := by
  simp [stereographicFactor]

@[simp] theorem stereographicFactor_zero : stereographicFactor 0 = 2 := by
  simp [stereographicFactor]

/-- At the north pole the projection lands smoothly at the origin. -/
theorem stereographic_northPole (R lam : ℝ) : stereographic R (π / 2) lam = vec2 0 0 := by
  simp [stereographic]

theorem stereographicFactor_nonneg {φ : ℝ} (hφ : φ ∈ Set.Ioc (-(π / 2)) (π / 2)) :
    0 ≤ stereographicFactor φ := by
  have hc : 0 ≤ cos φ := cos_nonneg_of_neg_pi_div_two_le_of_le hφ.1.le hφ.2
  have hd : 0 < 1 + sin φ := one_add_sin_pos hφ.1 hφ.2
  unfold stereographicFactor
  positivity

/-- Half-angle form: `2 cos φ / (1 + sin φ) = 2 tan ((π/2 - φ) / 2)`. -/
theorem stereographicFactor_eq_two_tan {φ : ℝ} (hφ : φ ∈ Set.Ioc (-(π / 2)) (π / 2)) :
    stereographicFactor φ = 2 * tan ((π / 2 - φ) / 2) := by
  set θ := (π / 2 - φ) / 2
  have hφ_eq : φ = π / 2 - 2 * θ := by simp only [θ]; ring
  have hθ_mem : θ ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    simp only [θ, Set.mem_Ioo]
    constructor <;> linarith [hφ.1, hφ.2, pi_pos]
  have hcθ : 0 < cos θ := cos_pos_of_mem_Ioo hθ_mem
  have hcos : cos φ = 2 * sin θ * cos θ := by
    rw [hφ_eq, cos_pi_div_two_sub, sin_two_mul]
  have hsin : 1 + sin φ = 2 * cos θ ^ 2 := by
    rw [hφ_eq, sin_pi_div_two_sub, cos_two_mul]
    ring
  rw [stereographicFactor, hcos, hsin, tan_eq_sin_div_cos]
  have := hcθ.ne'
  field_simp

theorem stereographicLat_mem {u : ℝ} (hu : 0 ≤ u) :
    stereographicLat u ∈ Set.Ioc (-(π / 2)) (π / 2) := by
  have h0 : 0 ≤ arctan (u / 2) := arctan_nonneg.mpr (by linarith)
  have hlt : arctan (u / 2) < π / 2 := arctan_lt_pi_div_two _
  unfold stereographicLat
  exact ⟨by linarith, by linarith⟩

/-- Inverting `stereographicFactor` recovers the latitude on `(-π/2, π/2]`. -/
theorem stereographicLat_factor {φ : ℝ} (hφ : φ ∈ Set.Ioc (-(π / 2)) (π / 2)) :
    stereographicLat (stereographicFactor φ) = φ := by
  rw [stereographicFactor_eq_two_tan hφ, stereographicLat]
  have hθ1 : -(π / 2) < (π / 2 - φ) / 2 := by linarith [hφ.2, pi_pos]
  have hθ2 : (π / 2 - φ) / 2 < π / 2 := by linarith [hφ.1]
  rw [mul_div_cancel_left₀ _ two_ne_zero, arctan_tan hθ1 hθ2]
  ring

/-- Projecting `stereographicLat u` recovers any nonnegative radial factor `u`. -/
theorem stereographicFactor_lat {u : ℝ} (hu : 0 ≤ u) :
    stereographicFactor (stereographicLat u) = u := by
  rw [stereographicFactor_eq_two_tan (stereographicLat_mem hu)]
  have harg : (π / 2 - stereographicLat u) / 2 = arctan (u / 2) := by
    unfold stereographicLat; ring
  rw [harg, tan_arctan]
  ring

/-- `stereographicFactor` is a bijection from `(-π/2, π/2]` onto `[0, ∞)`. -/
theorem stereographicFactor_bijOn :
    Set.BijOn stereographicFactor (Set.Ioc (-(π / 2)) (π / 2)) (Set.Ici 0) := by
  refine ⟨fun φ hφ => stereographicFactor_nonneg hφ, ?_, ?_⟩
  · intro φ₁ h₁ φ₂ h₂ heq
    have := congrArg stereographicLat heq
    rwa [stereographicLat_factor h₁, stereographicLat_factor h₂] at this
  · intro u (hu : 0 ≤ u)
    exact ⟨stereographicLat u, stereographicLat_mem hu, stereographicFactor_lat hu⟩

/-- Parallels of latitude map to circles of radius `R · stereographicFactor φ`
around the origin. -/
theorem norm_stereographic {R : ℝ} (hR : 0 ≤ R) {φ : ℝ}
    (hφ : φ ∈ Set.Ioc (-(π / 2)) (π / 2)) (lam : ℝ) :
    ‖stereographic R φ lam‖ = R * stereographicFactor φ := by
  have hrf : 0 ≤ R * stereographicFactor φ := mul_nonneg hR (stereographicFactor_nonneg hφ)
  have hsq : ‖stereographic R φ lam‖ ^ 2 = (R * stereographicFactor φ) ^ 2 := by
    rw [stereographic, norm_vec2_sq]
    linear_combination (R * stereographicFactor φ) ^ 2 * sin_sq_add_cos_sq lam
  nlinarith [norm_nonneg (stereographic R φ lam)]

/-- Polar stereographic preserves azimuths from the north pole: each point lies
in the horizontal initial direction of the great circle from the pole to it. -/
theorem stereographic_preserves_azimuth (R : ℝ) {φ : ℝ}
    (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) (lam : ℝ) :
    stereographic R φ lam =
      (R * stereographicFactor φ) • horizontal (arcNormal northPole (direction φ lam)) := by
  rw [arcNormal_northPole hφ, horizontal, stereographic, vec2_smul]
  simp

/-! ## Derivatives and conformality -/

/-- `d/dφ (2 cos φ / (1 + sin φ)) = -2 / (1 + sin φ)`. -/
theorem hasDerivAt_stereographicFactor {φ : ℝ} (hd : 1 + sin φ ≠ 0) :
    HasDerivAt stereographicFactor (-stereographicScale φ) φ := by
  have hnum : HasDerivAt (fun φ => 2 * cos φ) (-(2 * sin φ)) φ := by
    convert (hasDerivAt_cos φ).const_mul 2 using 1; ring
  have hden : HasDerivAt (fun φ => 1 + sin φ) (cos φ) φ := by
    convert (hasDerivAt_sin φ).const_add 1 using 1
  unfold stereographicFactor stereographicScale
  convert hnum.div hden hd using 1
  have hp := sin_sq_add_cos_sq φ
  field_simp
  linarith [hp]

theorem hasDerivAt_stereographic_lat (R : ℝ) {φ : ℝ} (hd : 1 + sin φ ≠ 0) (lam : ℝ) :
    HasDerivAt (fun φ => stereographic R φ lam)
      (vec2 (-(R * stereographicScale φ * cos lam))
            (-(R * stereographicScale φ * sin lam))) φ := by
  unfold stereographic
  refine hasDerivAt_vec2 ?_ ?_
  · convert ((hasDerivAt_stereographicFactor hd).const_mul R).mul_const (cos lam) using 1
    ring
  · convert ((hasDerivAt_stereographicFactor hd).const_mul R).mul_const (sin lam) using 1
    ring

theorem hasDerivAt_stereographic_lon (R φ lam : ℝ) :
    HasDerivAt (fun lam => stereographic R φ lam)
      (vec2 (-(R * stereographicFactor φ * sin lam))
            (R * stereographicFactor φ * cos lam)) lam := by
  unfold stereographic
  refine hasDerivAt_vec2 ?_ ?_
  · convert (hasDerivAt_cos lam).const_mul (R * stereographicFactor φ) using 1
    ring
  · exact (hasDerivAt_sin lam).const_mul (R * stereographicFactor φ)

/-- Local distortion of polar stereographic on the sphere of radius `R`. -/
noncomputable def stereographicDistortion {R : ℝ} (hR : 0 < R) {φ : ℝ}
    (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) (lam : ℝ) : LocalDistortion :=
  ⟨R, R * cos φ, hR, mul_pos hR (cos_pos_of_mem_Ioo hφ),
    vec2 (-(R * stereographicScale φ * cos lam)) (-(R * stereographicScale φ * sin lam)),
    vec2 (-(R * stereographicFactor φ * sin lam)) (R * stereographicFactor φ * cos lam)⟩

theorem stereographic_h {R : ℝ} (hR : 0 < R) {φ : ℝ}
    (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) (lam : ℝ) :
    (stereographicDistortion hR hφ lam).h = stereographicScale φ := by
  have hd : 0 < 1 + sin φ := one_add_sin_pos hφ.1 hφ.2.le
  have hs : 0 < stereographicScale φ := div_pos two_pos hd
  have hnorm : ‖(stereographicDistortion hR hφ lam).dLat‖ = R * stereographicScale φ := by
    have hsq : ‖(stereographicDistortion hR hφ lam).dLat‖ ^ 2 = (R * stereographicScale φ) ^ 2 := by
      dsimp only [stereographicDistortion]
      rw [norm_vec2_sq]
      linear_combination (R * stereographicScale φ) ^ 2 * sin_sq_add_cos_sq lam
    nlinarith [norm_nonneg (stereographicDistortion hR hφ lam).dLat, mul_pos hR hs]
  rw [LocalDistortion.h, hnorm]
  dsimp only [stereographicDistortion]
  exact mul_div_cancel_left₀ _ hR.ne'

theorem stereographic_k {R : ℝ} (hR : 0 < R) {φ : ℝ}
    (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) (lam : ℝ) :
    (stereographicDistortion hR hφ lam).k = stereographicScale φ := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo hφ
  have hd : 0 < 1 + sin φ := one_add_sin_pos hφ.1 hφ.2.le
  have hrf : 0 ≤ R * stereographicFactor φ :=
    mul_nonneg hR.le (stereographicFactor_nonneg ⟨hφ.1, hφ.2.le⟩)
  have hnorm : ‖(stereographicDistortion hR hφ lam).dLon‖ = R * stereographicFactor φ := by
    have hsq : ‖(stereographicDistortion hR hφ lam).dLon‖ ^ 2 =
        (R * stereographicFactor φ) ^ 2 := by
      dsimp only [stereographicDistortion]
      rw [norm_vec2_sq]
      linear_combination (R * stereographicFactor φ) ^ 2 * sin_sq_add_cos_sq lam
    nlinarith [norm_nonneg (stereographicDistortion hR hφ lam).dLon]
  rw [LocalDistortion.k, hnorm]
  dsimp only [stereographicDistortion]
  unfold stereographicFactor stereographicScale
  have := hR.ne'
  have := hc.ne'
  have := hd.ne'
  field_simp

/-- Polar stereographic is conformal everywhere on the open latitudes
`(-π/2, π/2)`. -/
theorem stereographic_isConformal {R : ℝ} (hR : 0 < R) {φ : ℝ}
    (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) (lam : ℝ) :
    (stereographicDistortion hR hφ lam).IsConformal := by
  refine ⟨?_, ?_⟩
  · dsimp only [stereographicDistortion]
    rw [inner_vec2]
    ring
  · rw [stereographic_h hR hφ lam, stereographic_k hR hφ lam]

/-- At the north pole the scale factor is `1`; on `(-π/2, π/2)` it exceeds `1`;
at the equator it is `2`. -/
theorem stereographicScale_pi_div_two : stereographicScale (π / 2) = 1 := by
  simp [stereographicScale]
  norm_num

theorem stereographicScale_zero : stereographicScale 0 = 2 := by
  simp [stereographicScale]

theorem one_lt_stereographicScale {φ : ℝ} (hφ : φ ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    1 < stereographicScale φ := by
  have hd : 0 < 1 + sin φ := one_add_sin_pos hφ.1 hφ.2.le
  have hsin : sin φ < 1 := by
    rw [← sin_pi_div_two]
    exact strictMonoOn_sin ⟨hφ.1.le, hφ.2.le⟩ ⟨by linarith [pi_pos], le_rfl⟩ hφ.2
  rw [stereographicScale, one_lt_div hd]
  linarith

/-! ## Universal Polar Stereographic (UPS) -/

/-- The UPS scale factor: polar stereographic multiplied by `k₀ = 0.994`. -/
noncomputable def upsScale (φ : ℝ) : ℝ := 0.994 * stereographicScale φ

theorem upsScale_pi_div_two : upsScale (π / 2) = 0.994 := by
  rw [upsScale, stereographicScale_pi_div_two, mul_one]

/-- UPS has exact unit scale on the parallel `sin φ = 0.988` (`φ ≈ 81.11° N`). -/
theorem upsScale_eq_one_iff {φ : ℝ} (hd : 0 < 1 + sin φ) :
    upsScale φ = 1 ↔ sin φ = 0.988 := by
  unfold upsScale stereographicScale
  rw [mul_div_assoc', div_eq_one_iff_eq hd.ne']
  constructor <;> intro h <;> linarith

/-- Across the north UPS zone `[84° N, 90° N]`, the UPS scale stays in
`[0.994, 1)`. -/
theorem upsScale_bounds_84 {φ : ℝ} (hlo : degToRad 84 ≤ φ) (hhi : φ ≤ π / 2) :
    0.994 ≤ upsScale φ ∧ upsScale φ < 1 := by
  set θ := π / 2 - φ
  have hθ0 : 0 ≤ θ := by simp only [θ]; linarith
  have hθ_hi : θ ≤ 0.104721 := by
    simp only [θ, degToRad] at hlo ⊢
    nlinarith [pi_lt_d6]
  have hθ2 : θ ^ 2 ≤ 0.104721 ^ 2 := pow_le_pow_left₀ hθ0 hθ_hi 2
  have hsin_eq : sin φ = cos θ := by
    have : φ = π / 2 - θ := by simp only [θ]; ring
    rw [this, sin_pi_div_two_sub]
  have hcos_lb : 1 - θ ^ 2 / 2 ≤ cos θ := one_sub_sq_div_two_le_cos
  have hd_lb : 1.9945 < 1 + sin φ := by
    rw [hsin_eq]
    nlinarith
  have hd_ub : 1 + sin φ ≤ 2 := by linarith [sin_le_one φ]
  have hd_pos : 0 < 1 + sin φ := by linarith
  unfold upsScale stereographicScale
  constructor
  · rw [mul_div_assoc', le_div_iff₀ hd_pos]
    linarith
  · rw [mul_div_assoc', div_lt_iff₀ hd_pos]
    linarith

/-- Including the overlap down to `80° N`, the UPS scale stays within
`[0.994, 1.0017)`. -/
theorem upsScale_bounds_80 {φ : ℝ} (hlo : degToRad 80 ≤ φ) (hhi : φ ≤ π / 2) :
    0.994 ≤ upsScale φ ∧ upsScale φ < 1.0017 := by
  set θ := π / 2 - φ
  have hθ0 : 0 ≤ θ := by simp only [θ]; linarith
  have hθ_hi : θ ≤ 0.174533 := by
    simp only [θ, degToRad] at hlo ⊢
    nlinarith [pi_lt_d6]
  have hθ2 : θ ^ 2 ≤ 0.174533 ^ 2 := pow_le_pow_left₀ hθ0 hθ_hi 2
  have hsin_eq : sin φ = cos θ := by
    have : φ = π / 2 - θ := by simp only [θ]; ring
    rw [this, sin_pi_div_two_sub]
  have hcos_lb : 1 - θ ^ 2 / 2 ≤ cos θ := one_sub_sq_div_two_le_cos
  have hd_lb : 1.98476 < 1 + sin φ := by
    rw [hsin_eq]
    nlinarith
  have hd_ub : 1 + sin φ ≤ 2 := by linarith [sin_le_one φ]
  have hd_pos : 0 < 1 + sin φ := by linarith
  unfold upsScale stereographicScale
  constructor
  · rw [mul_div_assoc', le_div_iff₀ hd_pos]
    linarith
  · rw [mul_div_assoc', div_lt_iff₀ hd_pos]
    linarith

end Geodesy.Projection
