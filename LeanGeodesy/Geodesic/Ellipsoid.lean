import LeanGeodesy.FirstFundamentalForm
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Geodesics on the ellipsoid and Clairaut's relation

A geodesic is a curve that does not turn within the surface: its
acceleration has no component along the surface. With latitude and
longitude as coordinates the surface directions are spanned by `∂r/∂φ` and
`∂r/∂λ`, so a curve is a geodesic when

```
⟨r'', ∂r/∂φ⟩ = 0   and   ⟨r'', ∂r/∂λ⟩ = 0            (IsGeodesic)
```

The first fundamental form turns the second condition into an equation in
coordinates. By `inner_dr`, `⟨r', ∂r/∂λ⟩ = G λ'` with `G = (N cos φ)²`, and
because the ellipsoid is a surface of revolution, `⟨r', d/dt ∂r/∂λ⟩ = 0`
(`inner_velocity_deriv_parallelTangent`). So

```
⟨r'', ∂r/∂λ⟩ = d/dt ((N cos φ)² λ')                  (hasDerivAt_G_mul_lon')
```

and the longitude component of the geodesic equation is
`d/dt ((N cos φ)² λ') = 0`. Longitude does not appear in the metric, and
this is the conservation law it brings:

- Clairaut's relation: along a geodesic `(N cos φ)² λ'` is constant
  (`clairaut_G_mul_lon'`);
- geodesics have constant speed (`geodesic_speed_const`), since
  `⟨r'', r'⟩ = φ' ⟨r'', ∂r/∂φ⟩ + λ' ⟨r'', ∂r/∂λ⟩`;
- together, with `p = N cos φ` the distance from the axis and `A` the
  azimuth, `p sin A` is constant (`clairaut`): the form used in geodetic
  software, since `sin A = p λ' / ‖r'‖` (`sinAzimuth_eq`).

The curve is given by functions `lat`, `lon` with derivatives `lat'`, `lon'`
and a velocity `dr (lat', lon')` (the actual velocity, `hasDerivAt_position`)
with derivative `acc` (`EllipsoidCurve`). Longitude is an unwrapped real.
-/

namespace Geodesy

open Real

namespace ReferenceEllipsoid

variable (E : ReferenceEllipsoid)

/-- A twice differentiable curve on the ellipsoid, in latitude and longitude. -/
structure EllipsoidCurve where
  lat : ℝ → ℝ
  lon : ℝ → ℝ
  lat' : ℝ → ℝ
  lon' : ℝ → ℝ
  /-- The acceleration in space. -/
  acc : ℝ → E3
  hasDerivAt_lat : ∀ t, HasDerivAt lat (lat' t) t
  hasDerivAt_lon : ∀ t, HasDerivAt lon (lon' t) t
  hasDerivAt_vel : ∀ t, HasDerivAt (fun s => E.dr (lat s) (lon s) (lat' s, lon' s)) (acc t) t

namespace EllipsoidCurve

variable {E} (γ : EllipsoidCurve E)

/-- The position in space. -/
noncomputable def position (t : ℝ) : E3 := E.ellipsoidPoint (γ.lat t) (γ.lon t)

/-- The velocity in space: `dr (φ', λ')`. -/
noncomputable def vel (t : ℝ) : E3 := E.dr (γ.lat t) (γ.lon t) (γ.lat' t, γ.lon' t)

/-- The velocity is the derivative of the position. -/
theorem hasDerivAt_position (t : ℝ) : HasDerivAt γ.position (γ.vel t) t :=
  E.hasDerivAt_curve (γ.hasDerivAt_lat t) (γ.hasDerivAt_lon t)

/-- The meridian and parallel tangents at the curve's point. -/
noncomputable def rLat (t : ℝ) : E3 := E.meridianTangent (γ.lat t) (γ.lon t)
noncomputable def rLon (t : ℝ) : E3 := E.parallelTangent (γ.lat t) (γ.lon t)

/-- A geodesic: no acceleration along the surface. -/
def IsGeodesic : Prop :=
  ∀ t, (inner (γ.acc t) (γ.rLat t) : ℝ) = 0 ∧ (inner (γ.acc t) (γ.rLon t) : ℝ) = 0

/-- `⟨r', ∂r/∂λ⟩ = G λ'`, from the first fundamental form. -/
theorem inner_vel_rLon (t : ℝ) :
    (inner (γ.vel t) (γ.rLon t) : ℝ) = (E.primeVerticalRadius (γ.lat t) * cos (γ.lat t)) ^ 2 * γ.lon' t := by
  have h : γ.rLon t = E.dr (γ.lat t) (γ.lon t) (0, 1) := by simp [rLon, dr]
  rw [vel, h, inner_dr, metric]
  ring

/-- The derivative of `∂r/∂λ` along the curve. -/
noncomputable def rLon' (t : ℝ) : E3 :=
  vec3 (E.meridianRadius (γ.lat t) * sin (γ.lat t) * γ.lat' t * sin (γ.lon t) -
      E.primeVerticalRadius (γ.lat t) * cos (γ.lat t) * cos (γ.lon t) * γ.lon' t)
    (-(E.meridianRadius (γ.lat t) * sin (γ.lat t) * γ.lat' t * cos (γ.lon t)) -
      E.primeVerticalRadius (γ.lat t) * cos (γ.lat t) * sin (γ.lon t) * γ.lon' t) 0

theorem hasDerivAt_rLon (t : ℝ) : HasDerivAt γ.rLon (γ.rLon' t) t := by
  have hp := (E.hasDerivAt_meridianPoint_fst (γ.lat t)).comp t (γ.hasDerivAt_lat t)
  have hl := γ.hasDerivAt_lon t
  have hfun : γ.rLon = fun s => vec3 (-(E.primeVerticalRadius (γ.lat s) * cos (γ.lat s) * sin (γ.lon s)))
      (E.primeVerticalRadius (γ.lat s) * cos (γ.lat s) * cos (γ.lon s)) 0 := by
    funext s; simp [rLon, parallelTangent]
  rw [hfun, rLon']
  refine hasDerivAt_vec3 ?_ ?_ (hasDerivAt_const _ _)
  · convert (hp.mul hl.sin).neg using 1
    simp only [Function.comp]
    ring
  · convert hp.mul hl.cos using 1
    simp only [Function.comp]
    ring

/-- The rotational symmetry: the velocity is perpendicular to the rate of change
of `∂r/∂λ`. -/
theorem inner_velocity_deriv_parallelTangent (t : ℝ) : (inner (γ.vel t) (γ.rLon' t) : ℝ) = 0 := by
  simp only [vel, dr, rLon', meridianTangent, parallelTangent, vec3_smul, vec3_add, inner_vec3]
  ring

/-- The longitude component of the geodesic equation: `⟨r'', ∂r/∂λ⟩` is the
derivative of `(N cos φ)² λ'`. -/
theorem hasDerivAt_G_mul_lon' (t : ℝ) :
    HasDerivAt (fun s => (E.primeVerticalRadius (γ.lat s) * cos (γ.lat s)) ^ 2 * γ.lon' s)
      (inner (γ.acc t) (γ.rLon t)) t := by
  have h := HasDerivAt.inner ℝ (γ.hasDerivAt_vel t) (γ.hasDerivAt_rLon t)
  have hfun : (fun s => (E.primeVerticalRadius (γ.lat s) * cos (γ.lat s)) ^ 2 * γ.lon' s) =
      fun s => (inner (γ.vel s) (γ.rLon s) : ℝ) := by
    funext s; rw [inner_vel_rLon]
  rw [hfun]
  convert h using 1
  rw [show (inner (E.dr (γ.lat t) (γ.lon t) (γ.lat' t, γ.lon' t)) (γ.rLon' t) : ℝ) =
    inner (γ.vel t) (γ.rLon' t) from rfl, inner_velocity_deriv_parallelTangent, zero_add]

/-- Clairaut's relation: along a geodesic `(N cos φ)² λ'` is constant. -/
theorem clairaut_G_mul_lon' (hg : γ.IsGeodesic) (s t : ℝ) :
    (E.primeVerticalRadius (γ.lat s) * cos (γ.lat s)) ^ 2 * γ.lon' s =
      (E.primeVerticalRadius (γ.lat t) * cos (γ.lat t)) ^ 2 * γ.lon' t := by
  have hd : ∀ x, HasDerivAt (fun s => (E.primeVerticalRadius (γ.lat s) * cos (γ.lat s)) ^ 2 * γ.lon' s)
      0 x := fun x => by
    have := γ.hasDerivAt_G_mul_lon' x
    rwa [(hg x).2] at this
  exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) s t

/-- `⟨r'', r'⟩ = φ' ⟨r'', ∂r/∂φ⟩ + λ' ⟨r'', ∂r/∂λ⟩`. -/
theorem inner_acc_vel (t : ℝ) :
    (inner (γ.acc t) (γ.vel t) : ℝ) =
      γ.lat' t * inner (γ.acc t) (γ.rLat t) + γ.lon' t * inner (γ.acc t) (γ.rLon t) := by
  rw [vel, dr, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rfl

/-- Geodesics have constant speed. -/
theorem geodesic_speed_const (hg : γ.IsGeodesic) (s t : ℝ) : ‖γ.vel s‖ = ‖γ.vel t‖ := by
  have hd : ∀ x, HasDerivAt (fun s => (inner (γ.vel s) (γ.vel s) : ℝ)) 0 x := fun x => by
    have h := HasDerivAt.inner ℝ (γ.hasDerivAt_vel x) (γ.hasDerivAt_vel x)
    have e : (inner (γ.acc x) (γ.vel x) : ℝ) = 0 := by rw [inner_acc_vel, (hg x).1, (hg x).2]; ring
    convert h using 1
    have e' : (inner (γ.acc x) (E.dr (γ.lat x) (γ.lon x) (γ.lat' x, γ.lon' x)) : ℝ) = 0 := e
    rw [real_inner_comm, e']
    ring
  have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) s t
  simp only [real_inner_self_eq_norm_sq] at hc
  rw [← sqrt_sq (norm_nonneg (γ.vel s)), hc, sqrt_sq (norm_nonneg _)]

/-- The sine of the azimuth: the eastward component of the velocity over the speed. -/
noncomputable def sinAzimuth (t : ℝ) : ℝ := inner (γ.vel t) (γ.rLon t) / (‖γ.rLon t‖ * ‖γ.vel t‖)

/-- `sin A = p λ' / ‖r'‖` with `p = N cos φ`. -/
theorem sinAzimuth_eq {t : ℝ} (hc : 0 < cos (γ.lat t)) :
    γ.sinAzimuth t = E.primeVerticalRadius (γ.lat t) * cos (γ.lat t) * γ.lon' t / ‖γ.vel t‖ := by
  have hp : 0 < E.primeVerticalRadius (γ.lat t) * cos (γ.lat t) :=
    mul_pos (E.primeVerticalRadius_pos _) hc
  have hn : ‖γ.rLon t‖ = E.primeVerticalRadius (γ.lat t) * cos (γ.lat t) := by
    rw [← sqrt_sq (norm_nonneg _), rLon, norm_parallelTangent_sq, sqrt_sq hp.le]
  rw [sinAzimuth, inner_vel_rLon, hn]
  rcases eq_or_ne ‖γ.vel t‖ 0 with h0 | h0
  · simp [h0]
  · field_simp
    ring

/-- Clairaut's relation in azimuth form: along a geodesic between the poles,
`N cos φ sin A` is constant. -/
theorem clairaut (hg : γ.IsGeodesic) {s t : ℝ} (hs : 0 < cos (γ.lat s)) (ht : 0 < cos (γ.lat t)) :
    E.primeVerticalRadius (γ.lat s) * cos (γ.lat s) * γ.sinAzimuth s =
      E.primeVerticalRadius (γ.lat t) * cos (γ.lat t) * γ.sinAzimuth t := by
  rw [γ.sinAzimuth_eq hs, γ.sinAzimuth_eq ht, γ.geodesic_speed_const hg s t]
  have h := γ.clairaut_G_mul_lon' hg s t
  calc _ = (E.primeVerticalRadius (γ.lat s) * cos (γ.lat s)) ^ 2 * γ.lon' s / ‖γ.vel t‖ := by ring
    _ = (E.primeVerticalRadius (γ.lat t) * cos (γ.lat t)) ^ 2 * γ.lon' t / ‖γ.vel t‖ := by rw [h]
    _ = _ := by ring

end EllipsoidCurve

end ReferenceEllipsoid

end Geodesy
