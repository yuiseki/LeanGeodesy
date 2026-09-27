import LeanGeodesy.FirstFundamentalForm
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Geodesics on the ellipsoid and Clairaut's relation

A geodesic is a curve that does not turn within the surface. With latitude
and longitude as coordinates the surface directions are spanned by `∂r/∂φ`
and `∂r/∂λ`, and `IsGeodesic` asks that the acceleration in space have no
component along them:

```
⟨r'', ∂r/∂φ⟩ = 0   and   ⟨r'', ∂r/∂λ⟩ = 0            (IsGeodesic)
```

This is the condition for an affinely parametrised geodesic: the
acceleration is purely normal, so the curve neither turns within the surface
nor speeds up or slows down (`geodesic_speed_const`). A geodesic traced at
varying speed, the same path under another parametrisation, has an
acceleration component along its own velocity and does not satisfy
`IsGeodesic`; the unparametrised notion would only ask the tangential
acceleration to be parallel to the velocity.

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

Conversely, where `φ' ≠ 0` the two conservation laws give back both
components of the geodesic equation (`isGeodesicAt_of_conserved`): constant
speed forces `φ' ⟨r'', ∂r/∂φ⟩ = 0`. This is the latitude component in
first-integral form. Where `φ' = 0` the conservation laws
are not enough, as the parallels show: a parallel run at constant speed
satisfies both, yet it is a geodesic exactly when it is the equator
(`parallelCurve_isGeodesic_iff`), because its acceleration points at the
axis and so has a component `N cos φ M sin φ` along the meridian.

The latitude component comes out explicitly too. With `E' = 2 M M'` and
`G' = -2 N cos φ M sin φ` from `FirstFundamentalForm`, the velocity pairs
with `∂r/∂φ` to `E φ'` and with the rate of change of `∂r/∂φ` to
`½ E' φ'² + ½ G' λ'²` (`inner_vel_rLat'`), so

```
⟨r'', ∂r/∂φ⟩ = E φ'' + ½ E' φ'² - ½ G' λ'²             (inner_acc_rLat)
```

and an affinely parametrised geodesic satisfies both

```
E φ'' + ½ E' φ'² - ½ G' λ'² = 0                        (geodesic_latitude_equation)
G λ'' + G' φ' λ' = 0                                   (geodesic_longitude_equation)
```

the second being the expanded form of `d/dt (G λ') = 0`. Divided by `E`,
the first is `φ'' + Γ^φ_{φφ} φ'² + Γ^φ_{λλ} λ'² = 0` with
`Γ^φ_{φφ} = E' / 2E` and `Γ^φ_{λλ} = -G' / 2E`
(`geodesic_latitude_equation_christoffel`). Conversely the two equations at
a time are exactly the geodesic condition there (`isGeodesicAt_iff_equations`,
`isGeodesic_iff_equations`). For the parallels it reduces to
`-½ G'(φ₀) = 0`, recovering that only the equator is a geodesic
(`parallelCurve_latitude_equation_iff`).

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
  /-- The latitude along the curve. -/
  lat : ℝ → ℝ
  /-- The longitude along the curve, unwrapped. -/
  lon : ℝ → ℝ
  /-- The rate of change of the latitude. -/
  lat' : ℝ → ℝ
  /-- The rate of change of the longitude. -/
  lon' : ℝ → ℝ
  /-- The acceleration in space. -/
  acc : ℝ → E3
  /-- `lat'` is the derivative of `lat`. -/
  hasDerivAt_lat : ∀ t, HasDerivAt lat (lat' t) t
  /-- `lon'` is the derivative of `lon`. -/
  hasDerivAt_lon : ∀ t, HasDerivAt lon (lon' t) t
  /-- `acc` is the derivative of the velocity `dr (lat', lon')`. -/
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

/-- An affinely parametrised (constant-speed) geodesic: the acceleration in space
has no component along the surface, so it is normal to the surface. A
reparametrisation at non-constant speed of such a curve is not `IsGeodesic`. -/
def IsGeodesic : Prop :=
  ∀ t, (inner ℝ (γ.acc t) (γ.rLat t) : ℝ) = 0 ∧ (inner ℝ (γ.acc t) (γ.rLon t) : ℝ) = 0

/-- `⟨r', ∂r/∂λ⟩ = G λ'`, from the first fundamental form. -/
theorem inner_vel_rLon (t : ℝ) :
    (inner ℝ (γ.vel t) (γ.rLon t) : ℝ) = (E.primeVerticalRadius (γ.lat t) * cos (γ.lat t)) ^ 2 * γ.lon' t := by
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
  · convert (hp.mul hl.sin).neg using 1 <;> (try rfl)
    simp only [Function.comp]
    ring
  · convert hp.mul hl.cos using 1 <;> (try rfl)
    simp only [Function.comp]
    ring

/-- The rotational symmetry: the velocity is perpendicular to the rate of change
of `∂r/∂λ`. -/
theorem inner_velocity_deriv_parallelTangent (t : ℝ) : (inner ℝ (γ.vel t) (γ.rLon' t) : ℝ) = 0 := by
  simp only [vel, dr, rLon', meridianTangent, parallelTangent, vec3_smul, vec3_add, inner_vec3]
  ring

/-- The longitude component of the geodesic equation: `⟨r'', ∂r/∂λ⟩` is the
derivative of `(N cos φ)² λ'`. -/
theorem hasDerivAt_G_mul_lon' (t : ℝ) :
    HasDerivAt (fun s => (E.primeVerticalRadius (γ.lat s) * cos (γ.lat s)) ^ 2 * γ.lon' s)
      (inner ℝ (γ.acc t) (γ.rLon t)) t := by
  have h := HasDerivAt.inner ℝ (γ.hasDerivAt_vel t) (γ.hasDerivAt_rLon t)
  have hfun : (fun s => (E.primeVerticalRadius (γ.lat s) * cos (γ.lat s)) ^ 2 * γ.lon' s) =
      fun s => (inner ℝ (γ.vel s) (γ.rLon s) : ℝ) := by
    funext s; rw [inner_vel_rLon]
  rw [hfun]
  convert h using 1 <;> (try rfl)
  rw [show (inner ℝ (E.dr (γ.lat t) (γ.lon t) (γ.lat' t, γ.lon' t)) (γ.rLon' t) : ℝ) =
    inner ℝ (γ.vel t) (γ.rLon' t) from rfl, inner_velocity_deriv_parallelTangent, zero_add]

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
    (inner ℝ (γ.acc t) (γ.vel t) : ℝ) =
      γ.lat' t * inner ℝ (γ.acc t) (γ.rLat t) + γ.lon' t * inner ℝ (γ.acc t) (γ.rLon t) := by
  rw [vel, dr, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rfl

/-- Geodesics have constant speed. -/
theorem geodesic_speed_const (hg : γ.IsGeodesic) (s t : ℝ) : ‖γ.vel s‖ = ‖γ.vel t‖ := by
  have hd : ∀ x, HasDerivAt (fun s => (inner ℝ (γ.vel s) (γ.vel s) : ℝ)) 0 x := fun x => by
    have h := HasDerivAt.inner ℝ (γ.hasDerivAt_vel x) (γ.hasDerivAt_vel x)
    have e : (inner ℝ (γ.acc x) (γ.vel x) : ℝ) = 0 := by rw [inner_acc_vel, (hg x).1, (hg x).2]; ring
    convert h using 1 <;> (try rfl)
    have e' : (inner ℝ (γ.acc x) (E.dr (γ.lat x) (γ.lon x) (γ.lat' x, γ.lon' x)) : ℝ) = 0 := e
    rw [real_inner_comm, e']
    ring
  have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) s t
  simp only [real_inner_self_eq_norm_sq] at hc
  rw [← sqrt_sq (norm_nonneg (γ.vel s)), hc, sqrt_sq (norm_nonneg _)]

/-- The sine of the azimuth: the eastward component of the velocity over the speed. -/
noncomputable def sinAzimuth (t : ℝ) : ℝ := inner ℝ (γ.vel t) (γ.rLon t) / (‖γ.rLon t‖ * ‖γ.vel t‖)

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

/-! ## The conservation laws characterise geodesics where `φ' ≠ 0` -/

/-- Where `φ' ≠ 0`, constant `(N cos φ)² λ'` and constant speed make the curve a
geodesic at that point. -/
theorem isGeodesicAt_of_conserved
    (hc : ∀ s t, (E.primeVerticalRadius (γ.lat s) * cos (γ.lat s)) ^ 2 * γ.lon' s =
      (E.primeVerticalRadius (γ.lat t) * cos (γ.lat t)) ^ 2 * γ.lon' t)
    (hv : ∀ s t, ‖γ.vel s‖ = ‖γ.vel t‖) {t : ℝ} (hlat : γ.lat' t ≠ 0) :
    (inner ℝ (γ.acc t) (γ.rLat t) : ℝ) = 0 ∧ (inner ℝ (γ.acc t) (γ.rLon t) : ℝ) = 0 := by
  have hlon : (inner ℝ (γ.acc t) (γ.rLon t) : ℝ) = 0 := by
    have h := γ.hasDerivAt_G_mul_lon' t
    have hfun : (fun s => (E.primeVerticalRadius (γ.lat s) * cos (γ.lat s)) ^ 2 * γ.lon' s) =
        fun _ => (E.primeVerticalRadius (γ.lat t) * cos (γ.lat t)) ^ 2 * γ.lon' t := by
      funext s; exact hc s t
    rw [hfun] at h
    exact h.unique (hasDerivAt_const t _)
  have hvel : (inner ℝ (γ.acc t) (γ.vel t) : ℝ) = 0 := by
    have h := HasDerivAt.inner ℝ (γ.hasDerivAt_vel t) (γ.hasDerivAt_vel t)
    have hfun : (fun s => (inner ℝ (E.dr (γ.lat s) (γ.lon s) (γ.lat' s, γ.lon' s))
        (E.dr (γ.lat s) (γ.lon s) (γ.lat' s, γ.lon' s)) : ℝ)) = fun _ => ‖γ.vel t‖ ^ 2 := by
      funext s
      rw [real_inner_self_eq_norm_sq]
      exact congrArg (· ^ 2) (hv s t)
    rw [hfun] at h
    have h0 := h.unique (hasDerivAt_const t _)
    have e : (inner ℝ (E.dr (γ.lat t) (γ.lon t) (γ.lat' t, γ.lon' t)) (γ.acc t) : ℝ) =
        inner ℝ (γ.acc t) (γ.vel t) := real_inner_comm _ _
    have e2 : (inner ℝ (γ.acc t) (E.dr (γ.lat t) (γ.lon t) (γ.lat' t, γ.lon' t)) : ℝ) =
        inner ℝ (γ.acc t) (γ.vel t) := rfl
    rw [e, e2] at h0
    linarith
  refine ⟨?_, hlon⟩
  rw [inner_acc_vel, hlon, mul_zero, add_zero] at hvel
  rcases mul_eq_zero.mp hvel with h | h
  · exact absurd h hlat
  · exact h

/-! ## The latitude component of the geodesic equation -/

/-- The derivative of `∂r/∂φ` along the curve, using `M'`. -/
noncomputable def rLat' (t : ℝ) : E3 :=
  let φ := γ.lat t
  let M := E.meridianRadius φ
  let M' := 3 * E.e2 * sin φ * cos φ * M / E.W2 φ
  vec3 (-((M' * sin φ + M * cos φ) * γ.lat' t) * cos (γ.lon t) + M * sin φ * sin (γ.lon t) * γ.lon' t)
    (-((M' * sin φ + M * cos φ) * γ.lat' t) * sin (γ.lon t) - M * sin φ * cos (γ.lon t) * γ.lon' t)
    ((M' * cos φ - M * sin φ) * γ.lat' t)

theorem hasDerivAt_rLat (t : ℝ) : HasDerivAt γ.rLat (γ.rLat' t) t := by
  have hM := (E.hasDerivAt_meridianRadius (γ.lat t)).comp t (γ.hasDerivAt_lat t)
  have hs := (γ.hasDerivAt_lat t).sin
  have hc := (γ.hasDerivAt_lat t).cos
  have hl := γ.hasDerivAt_lon t
  have hfun : γ.rLat = fun s => vec3 (-(E.meridianRadius (γ.lat s) * sin (γ.lat s)) * cos (γ.lon s))
      (-(E.meridianRadius (γ.lat s) * sin (γ.lat s)) * sin (γ.lon s))
      (E.meridianRadius (γ.lat s) * cos (γ.lat s)) := by
    funext s; simp [rLat, meridianTangent]
  rw [hfun, rLat']
  refine hasDerivAt_vec3 ?_ ?_ ?_
  · convert ((hM.mul hs).neg).mul hl.cos using 1 <;> (try rfl)
    simp only [Function.comp_apply, Pi.mul_apply, Pi.neg_apply]
    ring
  · convert ((hM.mul hs).neg).mul hl.sin using 1 <;> (try rfl)
    simp only [Function.comp_apply, Pi.mul_apply, Pi.neg_apply]
    ring
  · convert hM.mul hc using 1 <;> (try rfl)
    simp only [Function.comp_apply]
    ring

/-- `⟨r', ∂r/∂φ⟩ = E φ'`, from the first fundamental form. -/
theorem inner_vel_rLat (t : ℝ) :
    (inner ℝ (γ.vel t) (γ.rLat t) : ℝ) = E.meridianRadius (γ.lat t) ^ 2 * γ.lat' t := by
  have h : γ.rLat t = E.dr (γ.lat t) (γ.lon t) (1, 0) := by simp [rLat, dr]
  rw [vel, h, inner_dr, metric]
  ring

/-- `⟨r', d/dt ∂r/∂φ⟩ = ½ E' φ'² + ½ G' λ'²`. -/
theorem inner_vel_rLat' (t : ℝ) :
    (inner ℝ (γ.vel t) (γ.rLat' t) : ℝ) =
      E.firstFormE' (γ.lat t) / 2 * γ.lat' t ^ 2 + E.firstFormG' (γ.lat t) / 2 * γ.lon' t ^ 2 := by
  simp only [vel, dr, rLat', meridianTangent, parallelTangent, vec3_smul, vec3_add, inner_vec3,
    firstFormE', firstFormG']
  have hp := sin_sq_add_cos_sq (γ.lat t)
  have hq := sin_sq_add_cos_sq (γ.lon t)
  linear_combination
    (E.meridianRadius (γ.lat t) * (3 * E.e2 * sin (γ.lat t) * cos (γ.lat t) *
      E.meridianRadius (γ.lat t) / E.W2 (γ.lat t)) * γ.lat' t ^ 2) * hp +
    ((E.meridianRadius (γ.lat t) * sin (γ.lat t) * (3 * E.e2 * sin (γ.lat t) * cos (γ.lat t) *
      E.meridianRadius (γ.lat t) / E.W2 (γ.lat t)) * sin (γ.lat t) +
      E.meridianRadius (γ.lat t) * sin (γ.lat t) * E.meridianRadius (γ.lat t) * cos (γ.lat t)) *
      γ.lat' t ^ 2 - E.primeVerticalRadius (γ.lat t) * cos (γ.lat t) * E.meridianRadius (γ.lat t) *
      sin (γ.lat t) * γ.lon' t ^ 2) * hq

/-- The latitude component of the geodesic equation:
`⟨r'', ∂r/∂φ⟩ = E φ'' + ½ E' φ'² - ½ G' λ'²`, for a curve whose `φ'` has
derivative `φ''`. -/
theorem inner_acc_rLat {t lat'' : ℝ} (h2 : HasDerivAt γ.lat' lat'' t) :
    (inner ℝ (γ.acc t) (γ.rLat t) : ℝ) =
      E.meridianRadius (γ.lat t) ^ 2 * lat'' + E.firstFormE' (γ.lat t) / 2 * γ.lat' t ^ 2 -
        E.firstFormG' (γ.lat t) / 2 * γ.lon' t ^ 2 := by
  have hinner := HasDerivAt.inner ℝ (γ.hasDerivAt_vel t) (γ.hasDerivAt_rLat t)
  have hE : HasDerivAt (fun s => E.meridianRadius (γ.lat s) ^ 2)
      (E.firstFormE' (γ.lat t) * γ.lat' t) t := by
    convert ((E.hasDerivAt_meridianRadius (γ.lat t)).comp t (γ.hasDerivAt_lat t)).pow 2 using 1 <;> (try rfl)
    simp only [firstFormE', Function.comp]
    push_cast
    ring
  have hprod := hE.mul h2
  have hfun : (fun s => (inner ℝ (E.dr (γ.lat s) (γ.lon s) (γ.lat' s, γ.lon' s)) (γ.rLat s) : ℝ)) =
      fun s => E.meridianRadius (γ.lat s) ^ 2 * γ.lat' s := by
    funext s; exact γ.inner_vel_rLat s
  rw [hfun] at hinner
  have heq := hinner.unique hprod
  have e1 : (inner ℝ (E.dr (γ.lat t) (γ.lon t) (γ.lat' t, γ.lon' t)) (γ.rLat' t) : ℝ) =
      inner ℝ (γ.vel t) (γ.rLat' t) := rfl
  rw [e1, inner_vel_rLat'] at heq
  linarith

/-- Along an affinely parametrised geodesic the latitude satisfies
`E φ'' + ½ E' φ'² - ½ G' λ'² = 0`. -/
theorem geodesic_latitude_equation (hg : γ.IsGeodesic) {t lat'' : ℝ} (h2 : HasDerivAt γ.lat' lat'' t) :
    E.meridianRadius (γ.lat t) ^ 2 * lat'' + E.firstFormE' (γ.lat t) / 2 * γ.lat' t ^ 2 -
      E.firstFormG' (γ.lat t) / 2 * γ.lon' t ^ 2 = 0 := by
  rw [← γ.inner_acc_rLat h2]
  exact (hg t).1

/-- Along an affinely parametrised geodesic the longitude satisfies
`G λ'' + G' φ' λ' = 0`, the expanded form of `d/dt (G λ') = 0`. -/
theorem geodesic_longitude_equation (hg : γ.IsGeodesic) {t lon'' : ℝ}
    (h2 : HasDerivAt γ.lon' lon'' t) :
    (E.primeVerticalRadius (γ.lat t) * cos (γ.lat t)) ^ 2 * lon'' +
      E.firstFormG' (γ.lat t) * γ.lat' t * γ.lon' t = 0 := by
  have hG : HasDerivAt (fun s => (E.primeVerticalRadius (γ.lat s) * cos (γ.lat s)) ^ 2)
      (E.firstFormG' (γ.lat t) * γ.lat' t) t := by
    convert ((E.hasDerivAt_meridianPoint_fst (γ.lat t)).comp t (γ.hasDerivAt_lat t)).pow 2 using 1 <;> (try rfl)
    simp only [firstFormG', Function.comp]
    push_cast
    ring
  have heq := (γ.hasDerivAt_G_mul_lon' t).unique (hG.mul h2)
  rw [(hg t).2] at heq
  linarith

/-- The two Christoffel symbols of the latitude equation:
`Γ^φ_{φφ} = E' / (2E)` and `Γ^φ_{λλ} = -G' / (2E)`. -/
noncomputable def christoffelLatLatLat (φ : ℝ) : ℝ := E.firstFormE' φ / (2 * E.meridianRadius φ ^ 2)
noncomputable def christoffelLatLonLon (φ : ℝ) : ℝ := -E.firstFormG' φ / (2 * E.meridianRadius φ ^ 2)

/-- The latitude equation in Christoffel form:
`φ'' + Γ^φ_{φφ} φ'² + Γ^φ_{λλ} λ'² = 0`. -/
theorem geodesic_latitude_equation_christoffel (hg : γ.IsGeodesic) {t lat'' : ℝ}
    (h2 : HasDerivAt γ.lat' lat'' t) :
    lat'' + christoffelLatLatLat (E := E) (γ.lat t) * γ.lat' t ^ 2 +
      christoffelLatLonLon (E := E) (γ.lat t) * γ.lon' t ^ 2 = 0 := by
  have h := γ.geodesic_latitude_equation hg h2
  have hM := (E.meridianRadius_pos (γ.lat t)).ne'
  simp only [christoffelLatLatLat, christoffelLatLonLon]
  field_simp
  linear_combination 2 * h

/-- `⟨r'', ∂r/∂λ⟩ = G λ'' + G' φ' λ'`, for a curve whose `λ'` has derivative `λ''`. -/
theorem inner_acc_rLon {t lon'' : ℝ} (h3 : HasDerivAt γ.lon' lon'' t) :
    (inner ℝ (γ.acc t) (γ.rLon t) : ℝ) =
      (E.primeVerticalRadius (γ.lat t) * cos (γ.lat t)) ^ 2 * lon'' +
        E.firstFormG' (γ.lat t) * γ.lat' t * γ.lon' t := by
  have hG : HasDerivAt (fun s => (E.primeVerticalRadius (γ.lat s) * cos (γ.lat s)) ^ 2)
      (E.firstFormG' (γ.lat t) * γ.lat' t) t := by
    convert ((E.hasDerivAt_meridianPoint_fst (γ.lat t)).comp t (γ.hasDerivAt_lat t)).pow 2 using 1 <;> (try rfl)
    simp only [firstFormG', Function.comp]
    push_cast
    ring
  rw [(γ.hasDerivAt_G_mul_lon' t).unique (hG.mul h3)]
  ring

/-- At a time `t`, the curve is an affinely parametrised geodesic (no
acceleration along the surface) exactly when both coordinate equations hold:
`E φ'' + ½ E' φ'² - ½ G' λ'² = 0` and `G λ'' + G' φ' λ' = 0`. -/
theorem isGeodesicAt_iff_equations {t lat'' lon'' : ℝ} (h2 : HasDerivAt γ.lat' lat'' t)
    (h3 : HasDerivAt γ.lon' lon'' t) :
    ((inner ℝ (γ.acc t) (γ.rLat t) : ℝ) = 0 ∧ (inner ℝ (γ.acc t) (γ.rLon t) : ℝ) = 0) ↔
      (E.meridianRadius (γ.lat t) ^ 2 * lat'' + E.firstFormE' (γ.lat t) / 2 * γ.lat' t ^ 2 -
          E.firstFormG' (γ.lat t) / 2 * γ.lon' t ^ 2 = 0 ∧
        (E.primeVerticalRadius (γ.lat t) * cos (γ.lat t)) ^ 2 * lon'' +
          E.firstFormG' (γ.lat t) * γ.lat' t * γ.lon' t = 0) := by
  rw [γ.inner_acc_rLat h2, γ.inner_acc_rLon h3]

/-- So a curve with second derivatives everywhere is an affinely parametrised
geodesic exactly when the latitude and longitude equations hold at every time. -/
theorem isGeodesic_iff_equations {lat'' lon'' : ℝ → ℝ}
    (h2 : ∀ t, HasDerivAt γ.lat' (lat'' t) t) (h3 : ∀ t, HasDerivAt γ.lon' (lon'' t) t) :
    γ.IsGeodesic ↔ ∀ t,
      E.meridianRadius (γ.lat t) ^ 2 * lat'' t + E.firstFormE' (γ.lat t) / 2 * γ.lat' t ^ 2 -
          E.firstFormG' (γ.lat t) / 2 * γ.lon' t ^ 2 = 0 ∧
        (E.primeVerticalRadius (γ.lat t) * cos (γ.lat t)) ^ 2 * lon'' t +
          E.firstFormG' (γ.lat t) * γ.lat' t * γ.lon' t = 0 :=
  forall_congr' fun t => γ.isGeodesicAt_iff_equations (h2 t) (h3 t)

end EllipsoidCurve

/-! ## Parallels -/

/-- The parallel at latitude `φ₀`, run eastward at one radian of longitude per
unit time. -/
noncomputable def parallelCurve (φ₀ : ℝ) : EllipsoidCurve E where
  lat := fun _ => φ₀
  lon := id
  lat' := fun _ => 0
  lon' := fun _ => 1
  acc := fun s => vec3 (-(E.primeVerticalRadius φ₀ * cos φ₀ * cos s))
    (-(E.primeVerticalRadius φ₀ * cos φ₀ * sin s)) 0
  hasDerivAt_lat := fun _ => hasDerivAt_const _ _
  hasDerivAt_lon := fun t => hasDerivAt_id t
  hasDerivAt_vel := fun t => by
    have hfun : (fun s => E.dr φ₀ (id s) (0, 1)) = fun s =>
        vec3 (-(E.primeVerticalRadius φ₀ * cos φ₀ * sin s)) (E.primeVerticalRadius φ₀ * cos φ₀ * cos s) 0 := by
      funext s; simp [dr, parallelTangent]
    show HasDerivAt (fun s => E.dr φ₀ (id s) (0, 1)) _ t
    rw [hfun]
    refine hasDerivAt_vec3 ?_ ?_ (hasDerivAt_const _ _)
    · exact ((hasDerivAt_sin t).const_mul (E.primeVerticalRadius φ₀ * cos φ₀)).neg
    · convert (hasDerivAt_cos t).const_mul (E.primeVerticalRadius φ₀ * cos φ₀) using 1; ring

/-- A parallel strictly between the poles is a geodesic exactly when it is the
equator: otherwise its acceleration, pointing at the axis, has a component
`N cos φ₀ · M sin φ₀` along the meridian. -/
theorem parallelCurve_isGeodesic_iff {φ₀ : ℝ} (hc : 0 < cos φ₀) :
    (E.parallelCurve φ₀).IsGeodesic ↔ sin φ₀ = 0 := by
  have hlat : ∀ t, (inner ℝ ((E.parallelCurve φ₀).acc t) ((E.parallelCurve φ₀).rLat t) : ℝ) =
      E.primeVerticalRadius φ₀ * cos φ₀ * (E.meridianRadius φ₀ * sin φ₀) := fun t => by
    simp only [parallelCurve, EllipsoidCurve.rLat, meridianTangent, inner_vec3, id]
    have := sin_sq_add_cos_sq t
    linear_combination (E.primeVerticalRadius φ₀ * cos φ₀ * (E.meridianRadius φ₀ * sin φ₀)) * this
  have hlon : ∀ t, (inner ℝ ((E.parallelCurve φ₀).acc t) ((E.parallelCurve φ₀).rLon t) : ℝ) = 0 :=
    fun t => by
      simp only [parallelCurve, EllipsoidCurve.rLon, parallelTangent, inner_vec3, id]
      ring
  have hp : 0 < E.primeVerticalRadius φ₀ * cos φ₀ := mul_pos (E.primeVerticalRadius_pos φ₀) hc
  have hM := E.meridianRadius_pos φ₀
  constructor
  · intro hg
    have h := (hg 0).1
    rw [hlat] at h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hp.ne'
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hM.ne'
      · exact h
  · intro hs t
    exact ⟨by rw [hlat, hs]; ring, hlon t⟩

/-- The latitude equation recovers the parallels: for the parallel at `φ₀`,
where `φ' = φ'' = 0` and `λ' = 1`, it reduces to `-½ G'(φ₀) = 0`, which holds
exactly at the equator, and it is exactly the geodesic condition there. -/
theorem parallelCurve_latitude_equation_iff {φ₀ : ℝ} (hc : 0 < cos φ₀) :
    ((E.parallelCurve φ₀).IsGeodesic ↔
      E.meridianRadius φ₀ ^ 2 * 0 + E.firstFormE' φ₀ / 2 * 0 ^ 2 - E.firstFormG' φ₀ / 2 * 1 ^ 2 = 0) ∧
    (E.meridianRadius φ₀ ^ 2 * 0 + E.firstFormE' φ₀ / 2 * 0 ^ 2 - E.firstFormG' φ₀ / 2 * 1 ^ 2 = 0 ↔
      sin φ₀ = 0) := by
  have hp : 0 < E.primeVerticalRadius φ₀ * cos φ₀ := mul_pos (E.primeVerticalRadius_pos φ₀) hc
  have hM := E.meridianRadius_pos φ₀
  have halg : E.meridianRadius φ₀ ^ 2 * 0 + E.firstFormE' φ₀ / 2 * 0 ^ 2 - E.firstFormG' φ₀ / 2 * 1 ^ 2 = 0 ↔
      sin φ₀ = 0 := by
    simp only [firstFormG']
    constructor
    · intro h
      have h' : E.primeVerticalRadius φ₀ * cos φ₀ * E.meridianRadius φ₀ * sin φ₀ = 0 := by linarith
      rcases mul_eq_zero.mp h' with h | h
      · exact absurd h (mul_pos hp hM).ne'
      · exact h
    · intro h; rw [h]; ring
  refine ⟨?_, halg⟩
  rw [E.parallelCurve_isGeodesic_iff hc, halg]

/-- In particular the equator is a geodesic. -/
theorem equator_isGeodesic : (E.parallelCurve 0).IsGeodesic :=
  (E.parallelCurve_isGeodesic_iff (by simp)).mpr sin_zero

namespace EllipsoidCurve

end EllipsoidCurve

end ReferenceEllipsoid

end Geodesy
