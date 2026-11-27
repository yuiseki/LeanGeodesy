import LeanGeodesy.Geodesic.Ellipsoid

/-!
# The second fundamental form and curvatures of the ellipsoid

The first fundamental form measures lengths and angles within the surface; the
second measures how the surface bends in space, against its outward unit normal

```
n(φ, λ) = (cos φ cos λ, cos φ sin λ, sin φ)          (unitNormal)
```

Differentiating `n` in latitude and longitude gives the Weingarten equations
 directly (`hasDerivAt_unitNormal_lat`, `hasDerivAt_unitNormal_lon`):

```
∂n/∂φ = (1 / M) ∂r/∂φ,   ∂n/∂λ = (1 / N) ∂r/∂λ
```

So the meridians and parallels are the principal directions of the ellipsoid,
with inward principal curvatures `1 / M` and `1 / N` — the reason `M` and `N`
are called the radii of curvature of the meridian and prime vertical.

Pairing the second derivatives of `r` with the outward normal `n` gives the
second fundamental form (`secondFormL`, `secondFormM`, `secondFormN`):

```
L = -M,   M_II = 0,   N_II = -N cos² φ
```

From the two fundamental forms together follow:

- the normal component of any curve's spatial acceleration is `II(φ', λ')`
  (`EllipsoidCurve.inner_acc_unitNormal`);
- Euler's curvature formula: at azimuth `A` from north, the inward normal
  curvature is `(cos² A) / M + (sin² A) / N` (`normalCurvature_azimuth`),
  bounded between `1 / N` and `1 / M` (`normalCurvature_bounds`) because
  `M ≤ N` (`meridianRadius_le_primeVerticalRadius`);
- Gaussian curvature `K = (L N_II - M_II²) / (E G - F²) = 1 / (M N) > 0`
  (`gaussianCurvature_eq_det`, `gaussianCurvature_pos`), largest at the equator
  (`1 / b²`) and smallest at the poles (`b² / a⁴`);
- mean curvature `H = (1 / M + 1 / N) / 2` and Gaussian radius of curvature
  `R_G = √(M N)` (`M ≤ R_G ≤ N`);
- Gauss's Theorema Egregium on the ellipsoid (`gaussianCurvature_eq_intrinsic`):

  ```
  K = -(1 / √(E G)) · d/dφ ((d/dφ √G) / √E)
  ```

  showing that `K` is determined by the first fundamental form alone.
-/

namespace Geodesy

open Real

/-- The outward unit normal of an ellipsoid of revolution at geodetic latitude
`φ` and unwrapped longitude `lam`: `(cos φ cos λ, cos φ sin λ, sin φ)`. -/
noncomputable def unitNormal (φ lam : ℝ) : E3 :=
  vec3 (cos φ * cos lam) (cos φ * sin lam) (sin φ)

theorem norm_unitNormal_sq (φ lam : ℝ) : ‖unitNormal φ lam‖ ^ 2 = 1 := by
  rw [unitNormal, norm_vec3_sq]
  have h1 := sin_sq_add_cos_sq φ
  have h2 := sin_sq_add_cos_sq lam
  linear_combination cos φ ^ 2 * h2 + h1

theorem norm_unitNormal (φ lam : ℝ) : ‖unitNormal φ lam‖ = 1 := by
  have h := norm_unitNormal_sq φ lam
  nlinarith [norm_nonneg (unitNormal φ lam)]

/-- `unitNormal` agrees with `GeodeticCoordinate.normal`. -/
theorem unitNormal_eq_normal (c : GeodeticCoordinate) :
    unitNormal c.lat.1 c.lon.toReal = c.normal := by
  simp only [unitNormal, GeodeticCoordinate.normal, Real.Angle.cos_toReal, Real.Angle.sin_toReal]

namespace ReferenceEllipsoid

variable (E : ReferenceEllipsoid)

/-! ## Orthogonality and Weingarten equations -/

/-- The meridian tangent is perpendicular to the unit normal. -/
theorem inner_meridianTangent_unitNormal (φ lam : ℝ) :
    inner ℝ (E.meridianTangent φ lam) (unitNormal φ lam) = (0 : ℝ) := by
  rw [meridianTangent, unitNormal, inner_vec3]
  have h2 := sin_sq_add_cos_sq lam
  linear_combination -(E.meridianRadius φ * sin φ * cos φ) * h2

/-- The parallel tangent is perpendicular to the unit normal. -/
theorem inner_parallelTangent_unitNormal (φ lam : ℝ) :
    inner ℝ (E.parallelTangent φ lam) (unitNormal φ lam) = (0 : ℝ) := by
  rw [parallelTangent, unitNormal, inner_vec3]
  ring

/-- Every tangent vector `dr (dφ, dλ)` is perpendicular to the unit normal. -/
theorem inner_dr_unitNormal (φ lam : ℝ) (v : ℝ × ℝ) :
    inner ℝ (E.dr φ lam v) (unitNormal φ lam) = (0 : ℝ) := by
  rw [dr, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_meridianTangent_unitNormal, inner_parallelTangent_unitNormal]
  ring

/-- First Weingarten equation: `∂n/∂φ = (1 / M) ∂r/∂φ`. -/
theorem hasDerivAt_unitNormal_lat (φ lam : ℝ) :
    HasDerivAt (fun φ => unitNormal φ lam)
      ((1 / E.meridianRadius φ) • E.meridianTangent φ lam) φ := by
  have hM := (E.meridianRadius_pos φ).ne'
  unfold unitNormal meridianTangent
  rw [vec3_smul]
  refine hasDerivAt_vec3 ?_ ?_ ?_
  · convert (hasDerivAt_cos φ).mul_const (cos lam) using 1
    field_simp
  · convert (hasDerivAt_cos φ).mul_const (sin lam) using 1
    field_simp
  · convert hasDerivAt_sin φ using 1
    field_simp

/-- Second Weingarten equation: `∂n/∂λ = (1 / N) ∂r/∂λ`. -/
theorem hasDerivAt_unitNormal_lon (φ lam : ℝ) :
    HasDerivAt (fun lam => unitNormal φ lam)
      ((1 / E.primeVerticalRadius φ) • E.parallelTangent φ lam) lam := by
  have hN := (E.primeVerticalRadius_pos φ).ne'
  unfold unitNormal parallelTangent
  rw [vec3_smul]
  refine hasDerivAt_vec3 ?_ ?_ ?_
  · convert (hasDerivAt_cos lam).const_mul (cos φ) using 1
    field_simp
  · convert (hasDerivAt_sin lam).const_mul (cos φ) using 1
    field_simp
  · convert hasDerivAt_const lam (sin φ) using 1
    ring

/-- The outward Weingarten / inward shape operator in `(dφ, dλ)` coordinates:
`dn(dr v) = dr (shapeOperator φ v)`. -/
noncomputable def shapeOperator (φ : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.1 / E.meridianRadius φ, v.2 / E.primeVerticalRadius φ)

/-- Along a curve `(φ(t), λ(t))`, the unit normal changes at rate
`dr (φ' / M, λ' / N)`. -/
theorem hasDerivAt_unitNormal_curve {φ lon : ℝ → ℝ} {φ' lon' t : ℝ}
    (hφ : HasDerivAt φ φ' t) (hl : HasDerivAt lon lon' t) :
    HasDerivAt (fun s => unitNormal (φ s) (lon s))
      (E.dr (φ t) (lon t) (E.shapeOperator (φ t) (φ', lon'))) t := by
  have hM := (E.meridianRadius_pos (φ t)).ne'
  have hN := (E.primeVerticalRadius_pos (φ t)).ne'
  unfold unitNormal dr meridianTangent parallelTangent shapeOperator
  rw [vec3_smul, vec3_smul, vec3_add]
  refine hasDerivAt_vec3 ?_ ?_ ?_
  · convert (hφ.cos.mul hl.cos) using 1
    field_simp
  · convert (hφ.cos.mul hl.sin) using 1
    field_simp
  · convert hφ.sin using 1
    field_simp
    ring

/-! ## Second derivatives and the second fundamental form -/

/-- `L = ⟨∂²r/∂φ², n⟩`. -/
noncomputable def secondFormL (φ lam : ℝ) : ℝ :=
  inner ℝ (deriv (fun φ => E.meridianTangent φ lam) φ) (unitNormal φ lam)

/-- `M_II = ⟨∂²r/∂φ∂λ, n⟩`. -/
noncomputable def secondFormM (φ lam : ℝ) : ℝ :=
  inner ℝ (deriv (fun lam => E.meridianTangent φ lam) lam) (unitNormal φ lam)

/-- `N_II = ⟨∂²r/∂λ², n⟩`. -/
noncomputable def secondFormN (φ lam : ℝ) : ℝ :=
  inner ℝ (deriv (fun lam => E.parallelTangent φ lam) lam) (unitNormal φ lam)

theorem hasDerivAt_meridianTangent_lat (φ lam : ℝ) :
    HasDerivAt (fun φ => E.meridianTangent φ lam)
      (let M' := 3 * E.e2 * sin φ * cos φ * E.meridianRadius φ / E.W2 φ
       vec3 (-(M' * sin φ + E.meridianRadius φ * cos φ) * cos lam)
            (-(M' * sin φ + E.meridianRadius φ * cos φ) * sin lam)
            (M' * cos φ - E.meridianRadius φ * sin φ)) φ := by
  have hM := E.hasDerivAt_meridianRadius φ
  have h1 : HasDerivAt (fun φ => -(E.meridianRadius φ * sin φ))
      (-((3 * E.e2 * sin φ * cos φ * E.meridianRadius φ / E.W2 φ) * sin φ +
        E.meridianRadius φ * cos φ)) φ := (hM.mul (hasDerivAt_sin φ)).neg
  have h2 : HasDerivAt (fun φ => E.meridianRadius φ * cos φ)
      ((3 * E.e2 * sin φ * cos φ * E.meridianRadius φ / E.W2 φ) * cos φ -
        E.meridianRadius φ * sin φ) φ := by
    convert hM.mul (hasDerivAt_cos φ) using 1
    ring
  unfold meridianTangent
  exact hasDerivAt_vec3 (h1.mul_const (cos lam)) (h1.mul_const (sin lam)) h2

theorem hasDerivAt_meridianTangent_lon (φ lam : ℝ) :
    HasDerivAt (fun lam => E.meridianTangent φ lam)
      (vec3 (E.meridianRadius φ * sin φ * sin lam)
            (-(E.meridianRadius φ * sin φ * cos lam)) 0) lam := by
  unfold meridianTangent
  refine hasDerivAt_vec3 ?_ ?_ (hasDerivAt_const _ _)
  · convert (hasDerivAt_cos lam).const_mul (-(E.meridianRadius φ * sin φ)) using 1
    ring
  · convert (hasDerivAt_sin lam).const_mul (-(E.meridianRadius φ * sin φ)) using 1
    ring

theorem hasDerivAt_parallelTangent_lon (φ lam : ℝ) :
    HasDerivAt (fun lam => E.parallelTangent φ lam)
      (vec3 (-(E.primeVerticalRadius φ * cos φ * cos lam))
            (-(E.primeVerticalRadius φ * cos φ * sin lam)) 0) lam := by
  unfold parallelTangent
  refine hasDerivAt_vec3 ?_ ?_ (hasDerivAt_const _ _)
  · convert ((hasDerivAt_sin lam).const_mul (E.primeVerticalRadius φ * cos φ)).neg using 1
  · convert (hasDerivAt_cos lam).const_mul (E.primeVerticalRadius φ * cos φ) using 1
    ring

/-- `L = -M`. -/
theorem secondFormL_eq (φ lam : ℝ) : E.secondFormL φ lam = -E.meridianRadius φ := by
  rw [secondFormL, (E.hasDerivAt_meridianTangent_lat φ lam).deriv, unitNormal, inner_vec3]
  have h1 := sin_sq_add_cos_sq φ
  have h2 := sin_sq_add_cos_sq lam
  linear_combination
    -((3 * E.e2 * sin φ * cos φ * E.meridianRadius φ / E.W2 φ * sin φ +
      E.meridianRadius φ * cos φ) * cos φ) * h2 - E.meridianRadius φ * h1

/-- `M_II = 0`: meridians and parallels are conjugate (and orthogonal, so lines
of curvature). -/
theorem secondFormM_eq (φ lam : ℝ) : E.secondFormM φ lam = 0 := by
  rw [secondFormM, (E.hasDerivAt_meridianTangent_lon φ lam).deriv, unitNormal, inner_vec3]
  ring

/-- `N_II = -N cos² φ`. -/
theorem secondFormN_eq (φ lam : ℝ) :
    E.secondFormN φ lam = -E.primeVerticalRadius φ * cos φ ^ 2 := by
  rw [secondFormN, (E.hasDerivAt_parallelTangent_lon φ lam).deriv, unitNormal, inner_vec3]
  have h2 := sin_sq_add_cos_sq lam
  linear_combination -(E.primeVerticalRadius φ * cos φ ^ 2) * h2

/-- The second fundamental form as a symmetric bilinear form on coordinate steps:
`II(u, v) = -M uφ vφ - N cos² φ uλ vλ`. -/
noncomputable def secondForm (φ : ℝ) (u v : ℝ × ℝ) : ℝ :=
  -E.meridianRadius φ * u.1 * v.1 - E.primeVerticalRadius φ * cos φ ^ 2 * u.2 * v.2

theorem secondForm_eq_LMN (φ lam : ℝ) (u v : ℝ × ℝ) :
    E.secondForm φ u v = E.secondFormL φ lam * u.1 * v.1 +
      E.secondFormM φ lam * (u.1 * v.2 + u.2 * v.1) +
      E.secondFormN φ lam * u.2 * v.2 := by
  rw [secondFormL_eq, secondFormM_eq, secondFormN_eq, secondForm]
  ring

theorem secondForm_comm (φ : ℝ) (u v : ℝ × ℝ) : E.secondForm φ u v = E.secondForm φ v u := by
  simp only [secondForm]; ring

/-- Self-adjointness of `shapeOperator` relating the two fundamental forms:
`I(shapeOperator u, v) = -II(u, v)`. -/
theorem metric_shapeOperator (φ : ℝ) (u v : ℝ × ℝ) :
    E.metric φ (E.shapeOperator φ u) v = -E.secondForm φ u v := by
  have hM := (E.meridianRadius_pos φ).ne'
  have hN := (E.primeVerticalRadius_pos φ).ne'
  simp only [metric, shapeOperator, secondForm]
  field_simp
  ring

/-- Along any twice-differentiable curve on the ellipsoid, the outward normal
component of spatial acceleration is `II(φ', λ')`. -/
theorem EllipsoidCurve.inner_acc_unitNormal {E : ReferenceEllipsoid} (γ : EllipsoidCurve E)
    (t : ℝ) :
    inner ℝ (γ.acc t) (unitNormal (γ.lat t) (γ.lon t)) =
      E.secondForm (γ.lat t) (γ.lat' t, γ.lon' t) (γ.lat' t, γ.lon' t) := by
  have hzero : ∀ s, inner ℝ (γ.vel s) (unitNormal (γ.lat s) (γ.lon s)) = (0 : ℝ) := fun s =>
    E.inner_dr_unitNormal (γ.lat s) (γ.lon s) (γ.lat' s, γ.lon' s)
  have hd : HasDerivAt (fun s => inner ℝ (γ.vel s) (unitNormal (γ.lat s) (γ.lon s))) _ t :=
    (γ.hasDerivAt_vel t).inner ℝ
      (E.hasDerivAt_unitNormal_curve (γ.hasDerivAt_lat t) (γ.hasDerivAt_lon t))
  have hd0 : HasDerivAt (fun s => inner ℝ (γ.vel s) (unitNormal (γ.lat s) (γ.lon s))) 0 t := by
    simp_rw [hzero]
    exact hasDerivAt_const t 0
  have hsum := hd.unique hd0
  rw [E.inner_dr, E.metric_comm, E.metric_shapeOperator] at hsum
  linarith

/-! ## Principal curvatures and Euler's curvature formula -/

/-- `M ≤ N` everywhere on a reference ellipsoid (`f ≥ 0`), with equality at the
poles or on a sphere. -/
theorem meridianRadius_le_primeVerticalRadius (φ : ℝ) :
    E.meridianRadius φ ≤ E.primeVerticalRadius φ := by
  have hM := E.meridianRadius_pos φ
  have he := E.one_sub_e2_pos
  have hratio := E.N_div_M φ
  have hle : 1 ≤ E.W2 φ / (1 - E.e2) := by
    rw [one_le_div he]
    unfold W2
    nlinarith [E.e2_nonneg, sin_sq_le_one φ]
  rw [← hratio, one_le_div hM] at hle
  exact hle

/-- On a flattened ellipsoid (`0 < e²`), `M < N` strictly between the poles. -/
theorem meridianRadius_lt_primeVerticalRadius (he2 : 0 < E.e2) {φ : ℝ} (hc : cos φ ≠ 0) :
    E.meridianRadius φ < E.primeVerticalRadius φ := by
  have hM := E.meridianRadius_pos φ
  have he := E.one_sub_e2_pos
  have hratio := E.N_div_M φ
  have hsin : sin φ ^ 2 < 1 := by
    have h1 := sin_sq_add_cos_sq φ
    have hc2 : 0 < cos φ ^ 2 := sq_pos_of_ne_zero hc
    linarith
  have hlt : 1 < E.W2 φ / (1 - E.e2) := by
    rw [one_lt_div he]
    unfold W2
    nlinarith
  rw [← hratio, one_lt_div hM] at hlt
  exact hlt

/-- The inward normal curvature in coordinate direction `v = (dφ, dλ)`:
`-II(v, v) / I(v)`. Positive everywhere on the ellipsoid for `v ≠ 0`. -/
noncomputable def normalCurvature (φ : ℝ) (v : ℝ × ℝ) : ℝ :=
  -E.secondForm φ v v / E.firstForm φ v

/-- Along a meridian (`dλ = 0`, `dφ ≠ 0`), the normal curvature is `1 / M`. -/
theorem normalCurvature_meridian (φ : ℝ) {dφ : ℝ} (hd : dφ ≠ 0) :
    E.normalCurvature φ (dφ, 0) = 1 / E.meridianRadius φ := by
  have hM := (E.meridianRadius_pos φ).ne'
  simp only [normalCurvature, secondForm, firstForm, metric]
  field_simp
  ring

/-- Along a parallel (`dφ = 0`, `dλ ≠ 0`, `cos φ ≠ 0`), the normal curvature is
`1 / N` — the curvature of the normal section along the prime vertical, not of
the parallel circle itself (`1 / (N cos φ)`). -/
theorem normalCurvature_primeVertical {φ : ℝ} (hc : cos φ ≠ 0) {dl : ℝ} (hd : dl ≠ 0) :
    E.normalCurvature φ (0, dl) = 1 / E.primeVerticalRadius φ := by
  have hN := (E.primeVerticalRadius_pos φ).ne'
  simp only [normalCurvature, secondForm, firstForm, metric]
  field_simp
  ring

/-- Unit tangent step at azimuth `A` clockwise from north:
`(cos A / M, sin A / (N cos φ))`. -/
noncomputable def azimuthStep (φ A : ℝ) : ℝ × ℝ :=
  (cos A / E.meridianRadius φ, sin A / (E.primeVerticalRadius φ * cos φ))

theorem firstForm_azimuthStep {φ : ℝ} (hc : cos φ ≠ 0) (A : ℝ) :
    E.firstForm φ (E.azimuthStep φ A) = 1 := by
  have hM := (E.meridianRadius_pos φ).ne'
  have hN := (E.primeVerticalRadius_pos φ).ne'
  simp only [firstForm, metric, azimuthStep]
  field_simp
  exact cos_sq_add_sin_sq A

/-- Euler's curvature formula on the ellipsoid: at azimuth `A`, the inward
normal curvature is `(cos² A) / M + (sin² A) / N`. -/
theorem normalCurvature_azimuth {φ : ℝ} (hc : cos φ ≠ 0) (A : ℝ) :
    E.normalCurvature φ (E.azimuthStep φ A) =
      cos A ^ 2 / E.meridianRadius φ + sin A ^ 2 / E.primeVerticalRadius φ := by
  have hM := (E.meridianRadius_pos φ).ne'
  have hN := (E.primeVerticalRadius_pos φ).ne'
  rw [normalCurvature, E.firstForm_azimuthStep hc A, div_one]
  simp only [secondForm, azimuthStep]
  field_simp
  ring

/-- The principal curvatures `1 / N` and `1 / M` bound the normal curvature in
every tangent direction. -/
theorem normalCurvature_bounds {φ : ℝ} (hc : 0 < cos φ) {v : ℝ × ℝ} (hv : v ≠ 0) :
    1 / E.primeVerticalRadius φ ≤ E.normalCurvature φ v ∧
      E.normalCurvature φ v ≤ 1 / E.meridianRadius φ := by
  have hI := E.firstForm_pos hc hv
  have hM := E.meridianRadius_pos φ
  have hN := E.primeVerticalRadius_pos φ
  have hMN := E.meridianRadius_le_primeVerticalRadius φ
  rw [normalCurvature, div_le_iff₀ hI, le_div_iff₀ hI]
  simp only [secondForm, firstForm, metric]
  constructor
  · have h1 : E.meridianRadius φ ^ 2 / E.primeVerticalRadius φ ≤ E.meridianRadius φ := by
      rw [div_le_iff₀ hN]
      nlinarith
    have h2 : 0 ≤ v.1 ^ 2 := sq_nonneg v.1
    have h3 : (E.primeVerticalRadius φ * cos φ) ^ 2 / E.primeVerticalRadius φ =
        E.primeVerticalRadius φ * cos φ ^ 2 := by field_simp
    calc 1 / E.primeVerticalRadius φ *
          (E.meridianRadius φ ^ 2 * v.1 * v.1 +
            (E.primeVerticalRadius φ * cos φ) ^ 2 * v.2 * v.2)
        = (E.meridianRadius φ ^ 2 / E.primeVerticalRadius φ) * v.1 ^ 2 +
            ((E.primeVerticalRadius φ * cos φ) ^ 2 / E.primeVerticalRadius φ) * v.2 ^ 2 := by ring
      _ ≤ E.meridianRadius φ * v.1 ^ 2 + E.primeVerticalRadius φ * cos φ ^ 2 * v.2 ^ 2 := by
            rw [h3]; nlinarith
      _ = -(-E.meridianRadius φ * v.1 * v.1 - E.primeVerticalRadius φ * cos φ ^ 2 * v.2 * v.2) := by
            ring
  · have h1 : E.primeVerticalRadius φ * cos φ ^ 2 ≤
        (E.primeVerticalRadius φ * cos φ) ^ 2 / E.meridianRadius φ := by
      rw [le_div_iff₀ hM]
      have hc2 : 0 ≤ cos φ ^ 2 := sq_nonneg (cos φ)
      nlinarith
    have h2 : 0 ≤ v.2 ^ 2 := sq_nonneg v.2
    have h3 : E.meridianRadius φ ^ 2 / E.meridianRadius φ = E.meridianRadius φ := by field_simp
    calc -(-E.meridianRadius φ * v.1 * v.1 - E.primeVerticalRadius φ * cos φ ^ 2 * v.2 * v.2)
        = E.meridianRadius φ * v.1 ^ 2 + E.primeVerticalRadius φ * cos φ ^ 2 * v.2 ^ 2 := by ring
      _ ≤ (E.meridianRadius φ ^ 2 / E.meridianRadius φ) * v.1 ^ 2 +
            ((E.primeVerticalRadius φ * cos φ) ^ 2 / E.meridianRadius φ) * v.2 ^ 2 := by
            rw [h3]; nlinarith
      _ = 1 / E.meridianRadius φ *
            (E.meridianRadius φ ^ 2 * v.1 * v.1 +
              (E.primeVerticalRadius φ * cos φ) ^ 2 * v.2 * v.2) := by ring

/-! ## Gaussian curvature, mean curvature, and Gauss's Theorema Egregium -/

/-- The Gaussian curvature `K = 1 / (M N)`. -/
noncomputable def gaussianCurvature (φ : ℝ) : ℝ :=
  1 / (E.meridianRadius φ * E.primeVerticalRadius φ)

/-- The mean curvature `H = (1 / M + 1 / N) / 2`. -/
noncomputable def meanCurvature (φ : ℝ) : ℝ :=
  (1 / E.meridianRadius φ + 1 / E.primeVerticalRadius φ) / 2

/-- The Gaussian (geometric-mean) radius of curvature `R_G = √(M N)`. -/
noncomputable def gaussianRadius (φ : ℝ) : ℝ :=
  √(E.meridianRadius φ * E.primeVerticalRadius φ)

theorem gaussianCurvature_pos (φ : ℝ) : 0 < E.gaussianCurvature φ := by
  unfold gaussianCurvature
  exact div_pos one_pos (mul_pos (E.meridianRadius_pos φ) (E.primeVerticalRadius_pos φ))

theorem meanCurvature_pos (φ : ℝ) : 0 < E.meanCurvature φ := by
  unfold meanCurvature
  have := E.meridianRadius_pos φ
  have := E.primeVerticalRadius_pos φ
  positivity

/-- Extrinsic determinant formula: `(L N_II - M_II²) / (E G - F²) = 1 / (M N)`
off the poles. -/
theorem gaussianCurvature_eq_det {φ : ℝ} (hc : cos φ ≠ 0) (lam : ℝ) :
    (E.secondFormL φ lam * E.secondFormN φ lam - E.secondFormM φ lam ^ 2) /
      (E.firstFormE φ lam * E.firstFormG φ lam - E.firstFormF φ lam ^ 2) =
    E.gaussianCurvature φ := by
  have hM := (E.meridianRadius_pos φ).ne'
  have hN := (E.primeVerticalRadius_pos φ).ne'
  rw [secondFormL_eq, secondFormM_eq, secondFormN_eq, firstFormE_eq, firstFormF_eq,
    firstFormG_eq, gaussianCurvature]
  field_simp
  ring

/-- Closed form of Gaussian curvature in `W² = 1 - e² sin² φ`:
`K = W⁴ / (a² (1 - e²))`. -/
theorem gaussianCurvature_eq_W2 (φ : ℝ) :
    E.gaussianCurvature φ = E.W2 φ ^ 2 / (E.a ^ 2 * (1 - E.e2)) := by
  have hW := E.W2_pos φ
  have hs : 0 < √(E.W2 φ) := sqrt_pos.mpr hW
  have ha := E.a_pos.ne'
  have he := E.one_sub_e2_pos.ne'
  have hsq : √(E.W2 φ) ^ 2 = E.W2 φ := sq_sqrt hW.le
  simp only [gaussianCurvature, meridianRadius, primeVerticalRadius]
  rw [show 1 - E.e2 * sin φ ^ 2 = E.W2 φ from rfl]
  field_simp
  rw [hsq]

/-- At the equator, `K = 1 / b²`. -/
theorem gaussianCurvature_zero : E.gaussianCurvature 0 = 1 / E.b ^ 2 := by
  rw [gaussianCurvature_eq_W2, W2, sin_zero, zero_pow two_ne_zero, mul_zero, sub_zero, one_pow,
    E.b_sq]

/-- At the poles, `K = b² / a⁴`. -/
theorem gaussianCurvature_pi_div_two : E.gaussianCurvature (π / 2) = E.b ^ 2 / E.a ^ 4 := by
  have ha := E.a_pos.ne'
  rw [gaussianCurvature_eq_W2, W2, sin_pi_div_two, one_pow, mul_one, E.b_sq]
  have he := E.one_sub_e2_pos.ne'
  field_simp

/-- `M ≤ √(M N) ≤ N` everywhere, and `K = 1 / R_G²`. -/
theorem gaussianRadius_bounds (φ : ℝ) :
    E.meridianRadius φ ≤ E.gaussianRadius φ ∧
      E.gaussianRadius φ ≤ E.primeVerticalRadius φ ∧
      E.gaussianCurvature φ = 1 / E.gaussianRadius φ ^ 2 := by
  have hM := E.meridianRadius_pos φ
  have hN := E.primeVerticalRadius_pos φ
  have hMN := E.meridianRadius_le_primeVerticalRadius φ
  refine ⟨?_, ?_, ?_⟩
  · rw [gaussianRadius, le_sqrt hM.le (mul_nonneg hM.le hN.le)]
    nlinarith
  · rw [gaussianRadius, sqrt_le_iff]
    exact ⟨hN.le, by nlinarith⟩
  · rw [gaussianCurvature, gaussianRadius, sq_sqrt (mul_nonneg hM.le hN.le)]

/-- On a sphere of radius `R`, Gaussian curvature is `1 / R²` and mean curvature
is `1 / R`. -/
theorem gaussianCurvature_ofSphere {R : ℝ} (hR : 0 < R) (φ : ℝ) :
    (ofSphere R hR).gaussianCurvature φ = 1 / R ^ 2 := by
  rw [gaussianCurvature, meridianRadius_ofSphere hR, primeVerticalRadius_ofSphere hR]
  ring

theorem meanCurvature_ofSphere {R : ℝ} (hR : 0 < R) (φ : ℝ) :
    (ofSphere R hR).meanCurvature φ = 1 / R := by
  have := hR.ne'
  rw [meanCurvature, meridianRadius_ofSphere hR, primeVerticalRadius_ofSphere hR]
  field_simp
  ring

/-- Gauss's Theorema Egregium on the ellipsoid: on the open latitudes `0 < cos φ`,
Gaussian curvature equals `-(1 / areaElement) · d/dφ ((d/dφ √G) / √E)`, so it
depends solely on the first fundamental form (`firstFormE`, `firstFormG`, and
`firstFormF = 0`), not on the ambient space `ℝ³`. -/
theorem gaussianCurvature_eq_intrinsic {φ : ℝ} (hc : 0 < cos φ) (lam : ℝ) :
    -(1 / E.areaElement φ lam) *
      deriv (fun ψ => deriv (fun θ => √(E.firstFormG θ lam)) ψ / √(E.firstFormE ψ lam)) φ =
    E.gaussianCurvature φ := by
  have hopen : IsOpen {ψ : ℝ | 0 < cos ψ} := isOpen_lt continuous_const continuous_cos
  have hnhds : {ψ : ℝ | 0 < cos ψ} ∈ nhds φ := hopen.mem_nhds hc
  have hinner : ∀ ψ : ℝ, 0 < cos ψ →
      deriv (fun θ => √(E.firstFormG θ lam)) ψ / √(E.firstFormE ψ lam) = -sin ψ := by
    intro ψ hψ
    have hevG : (fun θ => √(E.firstFormG θ lam)) =ᶠ[nhds ψ]
        fun θ => E.primeVerticalRadius θ * cos θ := by
      filter_upwards [hopen.mem_nhds hψ] with θ (hθ : 0 < cos θ)
      rw [firstFormG_eq, sqrt_sq (mul_nonneg (E.primeVerticalRadius_pos θ).le hθ.le)]
    have hdG : HasDerivAt (fun θ => √(E.firstFormG θ lam)) (-(E.meridianRadius ψ * sin ψ)) ψ :=
      hevG.hasDerivAt_iff.mpr (E.hasDerivAt_meridianPoint_fst ψ)
    have hE : √(E.firstFormE ψ lam) = E.meridianRadius ψ := by
      rw [firstFormE_eq, sqrt_sq (E.meridianRadius_pos ψ).le]
    rw [hdG.deriv, hE]
    have hM := (E.meridianRadius_pos ψ).ne'
    field_simp
  have hevOuter :
      (fun ψ => deriv (fun θ => √(E.firstFormG θ lam)) ψ / √(E.firstFormE ψ lam)) =ᶠ[nhds φ]
      fun ψ => -sin ψ := by
    filter_upwards [hnhds] with ψ hψ
    exact hinner ψ hψ
  have hdOuter :
      HasDerivAt (fun ψ => deriv (fun θ => √(E.firstFormG θ lam)) ψ / √(E.firstFormE ψ lam))
        (-cos φ) φ :=
    hevOuter.hasDerivAt_iff.mpr (hasDerivAt_sin φ).neg
  rw [hdOuter.deriv, E.areaElement_eq hc.le lam, gaussianCurvature]
  have hM := (E.meridianRadius_pos φ).ne'
  have hN := (E.primeVerticalRadius_pos φ).ne'
  have hc' := hc.ne'
  field_simp

end ReferenceEllipsoid

end Geodesy
