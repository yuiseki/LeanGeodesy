import LeanGeodesy.Curvature
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# The first fundamental form of the ellipsoid

With geodetic latitude `φ` and longitude `λ` as local coordinates, the
ellipsoid is the surface `r(φ, λ) = ellipsoidPoint E φ λ`. Its first
fundamental form measures tangent vectors given in coordinates: a step
`(dφ, dλ)` has squared length

```
I(dφ, dλ) = E dφ² + 2 F dφ dλ + G dλ²
```

with `E = ⟨∂r/∂φ, ∂r/∂φ⟩`, `F = ⟨∂r/∂φ, ∂r/∂λ⟩`, `G = ⟨∂r/∂λ, ∂r/∂λ⟩`
(`firstFormE`, `firstFormF`, `firstFormG`). The partial derivatives are the
meridian and parallel tangents of `Curvature`, whose lengths `M` and `N cos φ`
and orthogonality were proved there, so

```
E = M²,   F = 0,   G = (N cos φ)²          (firstFormE_eq, firstFormF_eq, firstFormG_eq)
```

The form's bilinear version `metric` is symmetric and bilinear, never
negative, and on the open latitudes `|φ| < π/2` it vanishes only on the zero
vector (`metric_self_eq_zero_iff`): a positive definite metric. At the poles
`G = 0` and the coordinates degenerate, since every longitude names the
same point.

The form is what the ellipsoid's actual tangent vectors measure. The
coordinate step `v = (dφ, dλ)` is the tangent vector
`dr v = dφ ∂r/∂φ + dλ ∂r/∂λ` (`dr`), and inner products of these are the
metric (`inner_dr`), so

```
‖dr v‖² = M² dφ² + (N cos φ)² dλ²          (norm_dr_sq, the line element ds²)
```

A curve `t ↦ (φ(t), λ(t))` on the ellipsoid has velocity `dr (φ', λ')`
(`hasDerivAt_curve`, from the derivatives of `N cos φ` and `N (1 - e²) sin φ`
in `Curvature`), so its squared speed is `M² φ'² + (N cos φ)² λ'²`
(`speed_sq_curve`). Angles are the metric too: the cosine of the angle
between `dr u` and `dr v` is `g(u, v) / √(I(u) I(v))` (`cos_angle_dr`), and
they are perpendicular exactly when `g(u, v) = 0` (`metric_eq_zero_iff`).

The area element comes from the same coefficients:
`√(E G - F²) = M N cos φ` (`areaElement_eq`), so `dA = M N cos φ dφ dλ`. On a
sphere of radius `R`, `M = N = R` (`meridianRadius_ofSphere`,
`primeVerticalRadius_ofSphere`), the line element is
`R² dφ² + R² cos² φ dλ²` (`firstForm_ofSphere`) and the area element
`R² cos φ` (`areaElement_ofSphere`).

The coefficients depend on the latitude only. Their derivatives are
`E' = 2 M M'` and `G' = -2 N cos φ · M sin φ` (`hasDerivAt_firstFormE`,
`hasDerivAt_firstFormG`), from `M' = 3 e² sin φ cos φ M / (1 - e² sin² φ)`
(`hasDerivAt_meridianRadius`) and `(N cos φ)' = -M sin φ`.

Longitude is an unwrapped real coordinate here: the form is local.
-/

namespace Geodesy

open Real

namespace ReferenceEllipsoid

variable (E : ReferenceEllipsoid)

/-! ## The coefficients -/

/-- `E = ⟨∂r/∂φ, ∂r/∂φ⟩`. -/
noncomputable def firstFormE (φ lam : ℝ) : ℝ :=
  inner (deriv (fun φ => E.ellipsoidPoint φ lam) φ) (deriv (fun φ => E.ellipsoidPoint φ lam) φ)

/-- `F = ⟨∂r/∂φ, ∂r/∂λ⟩`. -/
noncomputable def firstFormF (φ lam : ℝ) : ℝ :=
  inner (deriv (fun φ => E.ellipsoidPoint φ lam) φ) (deriv (fun lam => E.ellipsoidPoint φ lam) lam)

/-- `G = ⟨∂r/∂λ, ∂r/∂λ⟩`. -/
noncomputable def firstFormG (φ lam : ℝ) : ℝ :=
  inner (deriv (fun lam => E.ellipsoidPoint φ lam) lam) (deriv (fun lam => E.ellipsoidPoint φ lam) lam)

theorem deriv_lat (φ lam : ℝ) :
    deriv (fun φ => E.ellipsoidPoint φ lam) φ = E.meridianTangent φ lam :=
  (E.hasDerivAt_ellipsoidPoint_lat φ lam).deriv

theorem deriv_lon (φ lam : ℝ) :
    deriv (fun lam => E.ellipsoidPoint φ lam) lam = E.parallelTangent φ lam :=
  (E.hasDerivAt_ellipsoidPoint_lon φ lam).deriv

/-- `E = M²`. -/
theorem firstFormE_eq (φ lam : ℝ) : E.firstFormE φ lam = E.meridianRadius φ ^ 2 := by
  rw [firstFormE, deriv_lat, real_inner_self_eq_norm_sq, norm_meridianTangent_sq]

/-- `F = 0`: meridians and parallels cross at right angles. -/
theorem firstFormF_eq (φ lam : ℝ) : E.firstFormF φ lam = 0 := by
  rw [firstFormF, deriv_lat, deriv_lon, inner_meridianTangent_parallelTangent]

/-- `G = (N cos φ)²`. -/
theorem firstFormG_eq (φ lam : ℝ) :
    E.firstFormG φ lam = (E.primeVerticalRadius φ * cos φ) ^ 2 := by
  rw [firstFormG, deriv_lon, real_inner_self_eq_norm_sq, norm_parallelTangent_sq]

/-- On the open latitudes `E` and `G` are positive. -/
theorem firstFormE_pos (φ lam : ℝ) : 0 < E.firstFormE φ lam := by
  rw [firstFormE_eq]; exact pow_pos (E.meridianRadius_pos φ) 2

theorem firstFormG_pos {φ : ℝ} (hc : 0 < cos φ) (lam : ℝ) : 0 < E.firstFormG φ lam := by
  rw [firstFormG_eq]; exact pow_pos (mul_pos (E.primeVerticalRadius_pos φ) hc) 2

/-- At the poles `G = 0`: the longitude coordinate degenerates. -/
theorem firstFormG_pole (lam : ℝ) : E.firstFormG (π / 2) lam = 0 := by
  rw [firstFormG_eq, cos_pi_div_two, mul_zero, zero_pow two_ne_zero]

/-! ## The metric -/

/-- The first fundamental form as a bilinear form on coordinate tangent vectors
`u = (uφ, uλ)`, `v = (vφ, vλ)`: `M² uφ vφ + (N cos φ)² uλ vλ`. -/
noncomputable def metric (φ : ℝ) (u v : ℝ × ℝ) : ℝ :=
  E.meridianRadius φ ^ 2 * u.1 * v.1 + (E.primeVerticalRadius φ * cos φ) ^ 2 * u.2 * v.2

/-- The first fundamental form: `I(v) = g(v, v) = M² dφ² + (N cos φ)² dλ²`. -/
noncomputable def firstForm (φ : ℝ) (v : ℝ × ℝ) : ℝ := E.metric φ v v

/-- The metric is `E uφ vφ + F (uφ vλ + uλ vφ) + G uλ vλ`. -/
theorem metric_eq_EFG (φ lam : ℝ) (u v : ℝ × ℝ) :
    E.metric φ u v = E.firstFormE φ lam * u.1 * v.1 +
      E.firstFormF φ lam * (u.1 * v.2 + u.2 * v.1) + E.firstFormG φ lam * u.2 * v.2 := by
  rw [firstFormE_eq, firstFormF_eq, firstFormG_eq, metric]
  ring

theorem metric_comm (φ : ℝ) (u v : ℝ × ℝ) : E.metric φ u v = E.metric φ v u := by
  simp only [metric]; ring

theorem metric_add_left (φ : ℝ) (u u' v : ℝ × ℝ) :
    E.metric φ (u + u') v = E.metric φ u v + E.metric φ u' v := by
  simp only [metric, Prod.fst_add, Prod.snd_add]; ring

theorem metric_smul_left (φ c : ℝ) (u v : ℝ × ℝ) :
    E.metric φ (c • u) v = c * E.metric φ u v := by
  simp only [metric, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem metric_add_right (φ : ℝ) (u v v' : ℝ × ℝ) :
    E.metric φ u (v + v') = E.metric φ u v + E.metric φ u v' := by
  rw [metric_comm, metric_add_left, metric_comm, E.metric_comm φ v' u]

theorem metric_smul_right (φ c : ℝ) (u v : ℝ × ℝ) :
    E.metric φ u (c • v) = c * E.metric φ u v := by
  rw [metric_comm, metric_smul_left, metric_comm]

/-- The form is never negative. -/
theorem firstForm_nonneg (φ : ℝ) (v : ℝ × ℝ) : 0 ≤ E.firstForm φ v := by
  simp only [firstForm, metric]
  nlinarith [sq_nonneg (E.meridianRadius φ * v.1), sq_nonneg (E.primeVerticalRadius φ * cos φ * v.2)]

/-- On the open latitudes it vanishes only on the zero vector: the metric is
positive definite there. -/
theorem metric_self_eq_zero_iff {φ : ℝ} (hc : 0 < cos φ) (v : ℝ × ℝ) :
    E.metric φ v v = 0 ↔ v = 0 := by
  have hM := E.meridianRadius_pos φ
  have hN := mul_pos (E.primeVerticalRadius_pos φ) hc
  constructor
  · intro h
    simp only [metric] at h
    have h1 : (E.meridianRadius φ * v.1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (E.meridianRadius φ * v.1),
        sq_nonneg (E.primeVerticalRadius φ * cos φ * v.2)]
    have h2 : (E.primeVerticalRadius φ * cos φ * v.2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (E.meridianRadius φ * v.1),
        sq_nonneg (E.primeVerticalRadius φ * cos φ * v.2)]
    have e1 : v.1 = 0 := by
      rcases mul_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1) with h | h
      · exact absurd h hM.ne'
      · exact h
    have e2 : v.2 = 0 := by
      rcases mul_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2) with h | h
      · exact absurd h hN.ne'
      · exact h
    exact Prod.ext e1 e2
  · rintro rfl
    simp [metric]

theorem firstForm_pos {φ : ℝ} (hc : 0 < cos φ) {v : ℝ × ℝ} (hv : v ≠ 0) : 0 < E.firstForm φ v :=
  lt_of_le_of_ne (E.firstForm_nonneg φ v) (fun h => hv ((E.metric_self_eq_zero_iff hc v).mp h.symm))

/-! ## Actual tangent vectors -/

/-- The tangent vector of the ellipsoid for the coordinate step `(dφ, dλ)`:
`dφ ∂r/∂φ + dλ ∂r/∂λ`. -/
noncomputable def dr (φ lam : ℝ) (v : ℝ × ℝ) : E3 :=
  v.1 • E.meridianTangent φ lam + v.2 • E.parallelTangent φ lam

/-- Inner products of tangent vectors are given by the metric. -/
theorem inner_dr (φ lam : ℝ) (u v : ℝ × ℝ) :
    inner (E.dr φ lam u) (E.dr φ lam v) = E.metric φ u v := by
  have h0 := E.inner_meridianTangent_parallelTangent φ lam
  have h0' : (inner (E.parallelTangent φ lam) (E.meridianTangent φ lam) : ℝ) = 0 := by
    rw [real_inner_comm]; exact h0
  rw [dr, dr, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, h0, h0',
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_meridianTangent_sq,
    norm_parallelTangent_sq, metric]
  ring

/-- The line element: the squared length of the tangent vector for `(dφ, dλ)` is
`M² dφ² + (N cos φ)² dλ²`. -/
theorem norm_dr_sq (φ lam : ℝ) (v : ℝ × ℝ) : ‖E.dr φ lam v‖ ^ 2 = E.firstForm φ v := by
  rw [← real_inner_self_eq_norm_sq, inner_dr, firstForm]

theorem norm_dr (φ lam : ℝ) (v : ℝ × ℝ) : ‖E.dr φ lam v‖ = √(E.firstForm φ v) := by
  rw [← norm_dr_sq, sqrt_sq (norm_nonneg _)]

/-- A curve given by latitude and longitude has velocity `dr (φ', λ')`. -/
theorem hasDerivAt_curve {φ lon : ℝ → ℝ} {φ' lon' t : ℝ} (hφ : HasDerivAt φ φ' t)
    (hl : HasDerivAt lon lon' t) :
    HasDerivAt (fun t => E.ellipsoidPoint (φ t) (lon t)) (E.dr (φ t) (lon t) (φ', lon')) t := by
  have hp := (E.hasDerivAt_meridianPoint_fst (φ t)).comp t hφ
  have hz := (E.hasDerivAt_meridianPoint_snd (φ t)).comp t hφ
  unfold ellipsoidPoint dr meridianTangent parallelTangent
  rw [vec3_smul, vec3_smul, vec3_add]
  refine hasDerivAt_vec3 ?_ ?_ ?_
  · convert hp.mul hl.cos using 1
    simp only [Function.comp]
    ring
  · convert hp.mul hl.sin using 1
    simp only [Function.comp]
    ring
  · convert hz using 1
    simp only [Function.comp]
    ring

/-- The squared speed of a curve on the ellipsoid is `M² φ'² + (N cos φ)² λ'²`. -/
theorem speed_sq_curve {φ lon : ℝ → ℝ} {φ' lon' t : ℝ} (hφ : HasDerivAt φ φ' t)
    (hl : HasDerivAt lon lon' t) :
    ‖deriv (fun t => E.ellipsoidPoint (φ t) (lon t)) t‖ ^ 2 = E.firstForm (φ t) (φ', lon') := by
  rw [(E.hasDerivAt_curve hφ hl).deriv, norm_dr_sq]

/-- Angles between tangent vectors are given by the metric. -/
theorem cos_angle_dr (φ lam : ℝ) (u v : ℝ × ℝ) :
    cos (InnerProductGeometry.angle (E.dr φ lam u) (E.dr φ lam v)) =
      E.metric φ u v / (√(E.firstForm φ u) * √(E.firstForm φ v)) := by
  rw [InnerProductGeometry.cos_angle, inner_dr, norm_dr, norm_dr]

/-- Two tangent vectors are perpendicular exactly when the metric pairs them to zero. -/
theorem metric_eq_zero_iff (φ lam : ℝ) (u v : ℝ × ℝ) :
    E.metric φ u v = 0 ↔ (inner (E.dr φ lam u) (E.dr φ lam v) : ℝ) = 0 := by
  rw [inner_dr]

/-! ## Derivatives of the coefficients -/

/-- `E' = 2 M M'`. -/
noncomputable def firstFormE' (φ : ℝ) : ℝ :=
  2 * E.meridianRadius φ * (3 * E.e2 * sin φ * cos φ * E.meridianRadius φ / E.W2 φ)

/-- `G' = 2 (N cos φ) (N cos φ)' = -2 N cos φ · M sin φ`. -/
noncomputable def firstFormG' (φ : ℝ) : ℝ :=
  2 * (E.primeVerticalRadius φ * cos φ) * (-(E.meridianRadius φ * sin φ))

theorem hasDerivAt_firstFormE (φ lam : ℝ) :
    HasDerivAt (fun φ => E.firstFormE φ lam) (E.firstFormE' φ) φ := by
  have hfun : (fun φ => E.firstFormE φ lam) = fun φ => E.meridianRadius φ ^ 2 := by
    funext φ; exact E.firstFormE_eq φ lam
  rw [hfun, firstFormE']
  convert (E.hasDerivAt_meridianRadius φ).pow 2 using 1
  push_cast
  ring

theorem hasDerivAt_firstFormG (φ lam : ℝ) :
    HasDerivAt (fun φ => E.firstFormG φ lam) (E.firstFormG' φ) φ := by
  have hfun : (fun φ => E.firstFormG φ lam) = fun φ => (E.primeVerticalRadius φ * cos φ) ^ 2 := by
    funext φ; exact E.firstFormG_eq φ lam
  rw [hfun, firstFormG']
  convert (E.hasDerivAt_meridianPoint_fst φ).pow 2 using 1
  push_cast
  ring

/-! ## The area element -/

/-- The area element `√(E G - F²)`. -/
noncomputable def areaElement (φ lam : ℝ) : ℝ :=
  √(E.firstFormE φ lam * E.firstFormG φ lam - E.firstFormF φ lam ^ 2)

/-- `√(E G - F²) = M N cos φ`, so `dA = M N cos φ dφ dλ`. It vanishes at the poles. -/
theorem areaElement_eq {φ : ℝ} (hc : 0 ≤ cos φ) (lam : ℝ) :
    E.areaElement φ lam = E.meridianRadius φ * E.primeVerticalRadius φ * cos φ := by
  rw [areaElement, firstFormE_eq, firstFormF_eq, firstFormG_eq,
    show E.meridianRadius φ ^ 2 * (E.primeVerticalRadius φ * cos φ) ^ 2 - 0 ^ 2 =
      (E.meridianRadius φ * E.primeVerticalRadius φ * cos φ) ^ 2 by ring,
    sqrt_sq (mul_nonneg (mul_pos (E.meridianRadius_pos φ) (E.primeVerticalRadius_pos φ)).le hc)]

theorem areaElement_pos {φ : ℝ} (hc : 0 < cos φ) (lam : ℝ) : 0 < E.areaElement φ lam := by
  rw [E.areaElement_eq hc.le]
  exact mul_pos (mul_pos (E.meridianRadius_pos φ) (E.primeVerticalRadius_pos φ)) hc

end ReferenceEllipsoid

/-! ## The sphere -/

namespace ReferenceEllipsoid

variable {R : ℝ} (hR : 0 < R)

theorem e2_ofSphere : (ofSphere R hR).e2 = 0 := ((ofSphere R hR).isSphere_tfae.out 0 2).mp rfl

/-- On a sphere `M = R`. -/
theorem meridianRadius_ofSphere (φ : ℝ) : (ofSphere R hR).meridianRadius φ = R := by
  rw [meridianRadius, W2, e2_ofSphere hR]
  simp [ofSphere]

/-- On a sphere `N = R`. -/
theorem primeVerticalRadius_ofSphere (φ : ℝ) : (ofSphere R hR).primeVerticalRadius φ = R := by
  rw [primeVerticalRadius, e2_ofSphere hR]
  simp [ofSphere]

/-- On a sphere `ds² = R² dφ² + R² cos² φ dλ²`. -/
theorem firstForm_ofSphere (φ : ℝ) (v : ℝ × ℝ) :
    (ofSphere R hR).firstForm φ v = R ^ 2 * v.1 ^ 2 + R ^ 2 * cos φ ^ 2 * v.2 ^ 2 := by
  simp only [firstForm, metric, meridianRadius_ofSphere hR, primeVerticalRadius_ofSphere hR]
  ring

/-- On a sphere `dA = R² cos φ dφ dλ`. -/
theorem areaElement_ofSphere {φ : ℝ} (hc : 0 ≤ cos φ) (lam : ℝ) :
    (ofSphere R hR).areaElement φ lam = R ^ 2 * cos φ := by
  rw [areaElement_eq _ hc, meridianRadius_ofSphere hR, primeVerticalRadius_ofSphere hR]
  ring

end ReferenceEllipsoid

end Geodesy
