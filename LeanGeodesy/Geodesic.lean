import LeanGeodesy.GeodeticCoordinate
import LeanGeodesy.Projection.Mercator
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.ENNReal.Real

/-!
# Great-circle distance

On a spherical Earth the shortest way between two places runs along a great
circle, and its length is the radius times the angle between the two
places seen from the centre, the central angle. This file defines that
angle through the unit vectors of the two places (`direction`, the
ellipsoid normal of `GeodeticCoordinate`) and proves

- the spherical law of cosines (`cos_centralAngle`) and the haversine
  formula that GIS software evaluates (`haversine`);
- that the great-circle distance is a metric on the sphere: symmetric, zero
  only between a place and itself, at most half the circumference, and
  satisfying the triangle inequality (`greatCircleDistance_comm`,
  `greatCircleDistance_eq_zero_iff`, `greatCircleDistance_le`,
  `greatCircleDistance_triangle`);
- the familiar special cases: along a meridian it is the difference in
  latitude and distances add up (`centralAngle_same_meridian`,
  `centralAngle_meridian_add`), along the equator it is the difference in
  longitude the shorter way round (`centralAngle_equator`), and the poles
  are antipodal (`centralAngle_poles`);
- that great circles are shortest: a path sampled at points in between
  turns through at least the central angle (`angle_le_sum_angle`,
  `greatCircleDistance_le_sum`), while the great-circle arc (`greatArc`)
  turns through exactly the central angle however it is sampled in order
  (`sum_angle_greatArc`), and the points that make the triangle inequality
  an equality are exactly the points of the arc (`angle_add_angle_eq_iff`);
- that, with the length of a curve defined as the supremum of such sums
  (`angularLength`), the arc has length exactly the central angle, no curve
  from `u` to `w` is shorter (`angularLength_greatArc`,
  `angularLength_greatArc_le`), and a curve on the sphere that is as short
  runs along the arc (`mem_greatArc_of_angularLength_eq`);
- one minute of latitude on a 6371 km sphere is about 1853 m, the origin of
  the nautical mile (`arcMinute_bounds`).

The triangle inequality comes from the triangle inequality for angles
between unit vectors (`angle_le_angle_add_angle`), which Mathlib states
only as `proof_wanted` and is proved here. The proof splits two vectors
into their parts along and across a third. The parts across have lengths
`sin α` and `sin β`, so by Cauchy-Schwarz the inner product is at least
`cos α cos β - sin α sin β = cos (α + β)`, and `arccos` is decreasing.

The length here is the length of a curve in the sphere with its great-circle
metric. That it agrees with the arc length of a smooth curve, the integral
of its speed, is not proved. Geodesics on the ellipsoid, which are not plane
curves, are not covered.
-/

namespace Geodesy

namespace Geodesic

open Real InnerProductGeometry

section AngleTriangle

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `arccos` is decreasing. -/
theorem arccos_le_arccos_of_le {x y : ℝ} (h : x ≤ y) : arccos y ≤ arccos x := by
  rw [arccos, arccos]
  linarith [monotone_arcsin h]

/-- For unit vectors the angle is the arccosine of the inner product. -/
theorem angle_eq_arccos_inner {u w : V} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    angle u w = arccos (inner u w) := by
  rw [angle, hu, hw, mul_one, div_one]

/-- The part of `u` perpendicular to the unit vector `v` has length
`sin (angle u v)`. -/
theorem norm_sub_inner_smul {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - (inner u v : ℝ) • v‖ = sin (angle u v) := by
  have hc : cos (angle u v) = inner u v := by
    rw [cos_angle, hu, hv, mul_one, div_one]
  have hvv : (inner v v : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have huu : (inner u u : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hsq : ‖u - (inner u v : ℝ) • v‖ ^ 2 = sin (angle u v) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm u v, hvv, huu, sin_sq, hc]
    ring
  have hs : 0 ≤ sin (angle u v) := sin_nonneg_of_nonneg_of_le_pi (angle_nonneg u v) (angle_le_pi u v)
  nlinarith [norm_nonneg (u - (inner u v : ℝ) • v)]

/-- The triangle inequality for angles between unit vectors. -/
theorem angle_le_angle_add_angle {u v w : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    angle u w ≤ angle u v + angle v w := by
  set α := angle u v with hα
  set β := angle v w with hβ
  by_cases hab : α + β ≤ π
  swap
  · exact (angle_le_pi u w).trans (le_of_lt (not_le.mp hab))
  -- `⟪u, w⟫ = cos α cos β + ⟪a, b⟫` with `a`, `b` the perpendicular parts.
  have hcα : cos α = inner u v := by rw [hα, cos_angle, hu, hv, mul_one, div_one]
  have hcβ : cos β = inner v w := by rw [hβ, cos_angle, hv, hw, mul_one, div_one]
  have hvv : (inner v v : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hsplit : (inner u w : ℝ) =
      inner u v * inner v w + inner (u - (inner u v : ℝ) • v) (w - (inner w v : ℝ) • v) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_left, real_inner_smul_right, hvv,
      real_inner_comm w v]
    ring
  have hna := norm_sub_inner_smul hu hv
  have hnb : ‖w - (inner w v : ℝ) • v‖ = sin β := by
    rw [norm_sub_inner_smul hw hv, hβ, angle_comm]
  have hcs := neg_le_of_abs_le
    (abs_real_inner_le_norm (u - (inner u v : ℝ) • v) (w - (inner w v : ℝ) • v))
  rw [hna, ← hα, hnb] at hcs
  have hkey : cos (α + β) ≤ inner u w := by
    rw [cos_add, hsplit, hcα, hcβ]
    linarith
  calc angle u w = arccos (inner u w) := angle_eq_arccos_inner hu hw
    _ ≤ arccos (cos (α + β)) := arccos_le_arccos_of_le hkey
    _ = α + β := arccos_cos (add_nonneg (angle_nonneg u v) (angle_nonneg v w)) hab


/-! ## Great circles are shortest

A path on the sphere from `u` to `w`, sampled at points `u = p₀, p₁, …, pₙ = w`,
turns through at least the central angle `θ` between `u` and `w`
(`angle_le_sum_angle`). Along the great-circle arc `greatArc u w` the sum is
exactly `θ` for every sampling in order (`sum_angle_greatArc`). The length
of a curve on the sphere is the supremum of such sums, so this is what makes
the great-circle arc the shortest way from `u` to `w`. -/

/-- Chains of unit vectors: the angle from the first to the last is at most
the sum of the angles between consecutive ones. -/
theorem angle_le_sum_angle (p : ℕ → V) (hp : ∀ i, ‖p i‖ = 1) (n : ℕ) :
    angle (p 0) (p n) ≤ ∑ i ∈ Finset.range n, angle (p i) (p (i + 1)) := by
  induction n with
  | zero => simp [angle_self, (norm_ne_zero_iff.mp (by rw [hp 0]; exact one_ne_zero))]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (angle_le_angle_add_angle (hp 0) (hp n) (hp (n + 1))).trans (by linarith)

variable {u w : V}

/-- The unit vector perpendicular to `u` in the plane of `u` and `w`, pointing
towards `w`. -/
noncomputable def arcNormal (u w : V) : V := (sin (angle u w))⁻¹ • (w - (inner w u : ℝ) • u)

/-- The great-circle arc from `u` to `w`, at the fraction `t` of the way. -/
noncomputable def greatArc (u w : V) (t : ℝ) : V :=
  cos (t * angle u w) • u + sin (t * angle u w) • arcNormal u w

theorem inner_self_of_norm_one {v : V} (hv : ‖v‖ = 1) : (inner v v : ℝ) = 1 := by
  rw [real_inner_self_eq_norm_sq, hv, one_pow]

theorem greatArc_zero : greatArc u w 0 = u := by simp [greatArc]

section Arc

variable (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hs : 0 < sin (angle u w))
include hu hw hs

omit hw hs in
theorem inner_u_arcNormal : (inner u (arcNormal u w) : ℝ) = 0 := by
  rw [arcNormal, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
    inner_self_of_norm_one hu, real_inner_comm w u]
  ring

theorem inner_arcNormal_self : (inner (arcNormal u w) (arcNormal u w) : ℝ) = 1 := by
  have hn : ‖w - (inner w u : ℝ) • u‖ = sin (angle u w) := by
    rw [norm_sub_inner_smul hw hu, angle_comm]
  rw [arcNormal, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hn]
  field_simp
  ring

/-- Points of the arc are the cosine of the angle apart. -/
theorem inner_greatArc (s t : ℝ) :
    (inner (greatArc u w s) (greatArc u w t) : ℝ) = cos ((s - t) * angle u w) := by
  have h1 := inner_u_arcNormal (w := w) hu
  have h2 := inner_arcNormal_self hu hw hs
  have h0 := inner_self_of_norm_one hu
  have h1' : (inner (arcNormal u w) u : ℝ) = 0 := by rw [real_inner_comm]; exact h1
  simp only [greatArc, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, h0, h1, h1', h2]
  rw [sub_mul, cos_sub]
  ring

/-- The arc stays on the unit sphere. -/
theorem norm_greatArc (t : ℝ) : ‖greatArc u w t‖ = 1 := by
  have h := inner_greatArc hu hw hs t t
  rw [sub_self, zero_mul, cos_zero, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (greatArc u w t)]

theorem greatArc_one : greatArc u w 1 = w := by
  have hc : cos (angle u w) = inner w u := by
    rw [cos_angle, hu, hw, mul_one, div_one, real_inner_comm]
  rw [greatArc, one_mul, arcNormal, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, hc]
  abel

/-- Points of the arc at fractions `s` and `t` are `|s - t| θ` apart. -/
theorem angle_greatArc {s t : ℝ} (hs' : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    angle (greatArc u w s) (greatArc u w t) = |s - t| * angle u w := by
  have hθ := angle_nonneg u w
  have hθπ := angle_le_pi u w
  rw [angle_eq_arccos_inner (norm_greatArc hu hw hs s) (norm_greatArc hu hw hs t),
    inner_greatArc hu hw hs, ← cos_abs, abs_mul, abs_of_nonneg hθ]
  have hst : |s - t| ≤ 1 := abs_le.mpr ⟨by linarith [hs'.1, ht.2], by linarith [hs'.2, ht.1]⟩
  exact arccos_cos (by positivity) (by nlinarith [abs_nonneg (s - t)])

/-- Sampling the arc in order, the angles add up to exactly `θ`. -/
theorem sum_angle_greatArc (τ : ℕ → ℝ) (n : ℕ) (hmono : Monotone τ)
    (h0 : τ 0 = 0) (hn : τ n = 1) (hmem : ∀ i, i ≤ n → τ i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i ∈ Finset.range n, angle (greatArc u w (τ i)) (greatArc u w (τ (i + 1))) = angle u w := by
  have hterm : ∀ i ∈ Finset.range n, angle (greatArc u w (τ i)) (greatArc u w (τ (i + 1))) =
      (τ (i + 1) - τ i) * angle u w := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [angle_greatArc hu hw hs (hmem i hi'.le) (hmem (i + 1) hi'), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ i)))]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, Finset.sum_range_sub, hn, h0, sub_zero,
    one_mul]

/-- A point of the arc between `u` and `w` makes the triangle inequality an
equality: the detour through it costs nothing. -/
theorem angle_add_angle_greatArc {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    angle u (greatArc u w t) + angle (greatArc u w t) w = angle u w := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have e0 := angle_greatArc hu hw hs h0 ht
  have e1 := angle_greatArc hu hw hs ht h1
  rw [greatArc_zero] at e0
  rw [greatArc_one hu hw hs] at e1
  rw [e0, e1, zero_sub, abs_neg, abs_of_nonneg ht.1, abs_of_nonpos (by linarith [ht.2])]
  ring

/-- Conversely, a point that makes the triangle inequality an equality lies
on the arc: the arc is the only way from `u` to `w` with no detour. -/
theorem eq_greatArc_of_angle_add_angle {p : V} (hp : ‖p‖ = 1)
    (h : angle u p + angle p w = angle u w) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, p = greatArc u w t := by
  set θ := angle u w with hθ
  set n := arcNormal u w with hn
  set α := angle u p with hα
  have hθpos : 0 < θ := by
    rcases (angle_nonneg u w).lt_or_eq with h' | h'
    · exact h'
    · have h0 : sin θ = 0 := by rw [hθ, ← h', sin_zero]
      linarith
  have hαθ : α ≤ θ := by linarith [angle_nonneg p w]
  have hα0 : 0 ≤ α := angle_nonneg u p
  have huu := inner_self_of_norm_one hu
  have hun : (inner u n : ℝ) = 0 := inner_u_arcNormal (w := w) hu
  have hnn : (inner n n : ℝ) = 1 := inner_arcNormal_self hu hw hs
  have hnu : (inner n u : ℝ) = 0 := by rw [real_inner_comm]; exact hun
  -- `w = cos θ u + sin θ n`.
  have hw' : w = cos θ • u + sin θ • n := by
    have := greatArc_one hu hw hs
    rw [greatArc, one_mul] at this
    exact this.symm
  -- The components of `p` along `u` and `n`.
  set a := (inner p u : ℝ) with ha
  set b := (inner p n : ℝ) with hb
  have ha' : a = cos α := by rw [ha, hα, cos_angle, hu, hp, one_mul, div_one, real_inner_comm]
  have hpw : (inner p w : ℝ) = cos (θ - α) := by
    rw [show θ - α = angle p w by linarith, cos_angle, hp, hw, one_mul, div_one]
  have hb' : b = sin α := by
    have e : (inner p w : ℝ) = a * cos θ + b * sin θ := by
      rw [hw', inner_add_right, real_inner_smul_right, real_inner_smul_right]
      ring
    rw [hpw, cos_sub, ha'] at e
    have : sin θ * (b - sin α) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hs.ne'
    · linarith
  -- The rest of `p` is perpendicular to `u` and `n`, and has length zero.
  set r := p - a • u - b • n with hr
  have hrr : (inner r r : ℝ) = 1 - a ^ 2 - b ^ 2 := by
    have hpp := inner_self_of_norm_one hp
    have hup : (inner u p : ℝ) = a := by rw [ha, real_inner_comm]
    have hnp : (inner n p : ℝ) = b := by rw [hb, real_inner_comm]
    simp only [hr, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hpp, huu, hun, hnu, hnn, hup, hnp, ← ha, ← hb]
    ring
  have hr0 : r = 0 := by
    rw [ha', hb', show 1 - cos α ^ 2 - sin α ^ 2 = 0 by nlinarith [sin_sq_add_cos_sq α]] at hrr
    exact inner_self_eq_zero.mp hrr
  refine ⟨α / θ, ⟨div_nonneg hα0 hθpos.le, (div_le_one hθpos).mpr hαθ⟩, ?_⟩
  rw [greatArc, div_mul_cancel₀ α hθpos.ne', ← hn, ← ha', ← hb']
  rw [hr, sub_sub, sub_eq_zero] at hr0
  exact hr0

/-- So the points with no detour are exactly the points of the arc. -/
theorem angle_add_angle_eq_iff {p : V} (hp : ‖p‖ = 1) :
    angle u p + angle p w = angle u w ↔ ∃ t ∈ Set.Icc (0 : ℝ) 1, p = greatArc u w t := by
  constructor
  · exact eq_greatArc_of_angle_add_angle hu hw hs hp
  · rintro ⟨t, ht, rfl⟩
    exact angle_add_angle_greatArc hu hw hs ht

end Arc


/-! ## Curve length

The length of a curve in a metric space is the supremum, over all ways of
sampling it in order, of the distances between consecutive samples. On the
sphere with the great-circle metric the distance is the angle, so the
(angular) length of a curve `γ` on `[0, 1]` is the supremum of the sums
above. It can be infinite, so it takes values in `ℝ≥0∞`. -/

/-- `τ 0 = 0 ≤ τ 1 ≤ ... ≤ τ n = 1`: a way of sampling `[0, 1]` in order. -/
def IsPartition (n : ℕ) (τ : ℕ → ℝ) : Prop := Monotone τ ∧ τ 0 = 0 ∧ τ n = 1

theorem IsPartition.mem {n : ℕ} {τ : ℕ → ℝ} (h : IsPartition n τ) {i : ℕ} (hi : i ≤ n) :
    τ i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨h.2.1 ▸ h.1 (Nat.zero_le i), h.2.2 ▸ h.1 hi⟩

/-- The sum of the angles between consecutive samples. -/
noncomputable def sampledAngle (γ : ℝ → V) (n : ℕ) (τ : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, angle (γ (τ i)) (γ (τ (i + 1)))

/-- The angular length of a curve on `[0, 1]`. -/
noncomputable def angularLength (γ : ℝ → V) : ENNReal :=
  ⨆ (n : ℕ) (τ : ℕ → ℝ) (_ : IsPartition n τ), ENNReal.ofReal (sampledAngle γ n τ)

theorem sampledAngle_le_angularLength (γ : ℝ → V) {n : ℕ} {τ : ℕ → ℝ} (h : IsPartition n τ) :
    ENNReal.ofReal (sampledAngle γ n τ) ≤ angularLength γ :=
  le_iSup₂_of_le n τ (le_iSup_of_le h le_rfl)

/-- Sampling only the two ends. -/
def endsPartition : ℕ → ℝ := fun i => if i = 0 then 0 else 1

theorem isPartition_ends : IsPartition 1 endsPartition := by
  refine ⟨fun i j hij => ?_, by simp [endsPartition], by simp [endsPartition]⟩
  simp only [endsPartition]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- Sampling the two ends and the point at `t`. -/
def throughPartition (t : ℝ) : ℕ → ℝ := fun i => if i = 0 then 0 else if i = 1 then t else 1

theorem isPartition_through {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsPartition 2 (throughPartition t) := by
  refine ⟨fun i j hij => ?_, by simp [throughPartition], by simp [throughPartition]⟩
  simp only [throughPartition]
  split_ifs <;> first | (exfalso; omega) | linarith [ht.1, ht.2]

/-- Every curve from `u` to `w` is at least as long as the central angle. -/
theorem angle_le_angularLength (γ : ℝ → V) (h0 : γ 0 = u) (h1 : γ 1 = w) :
    ENNReal.ofReal (angle u w) ≤ angularLength γ := by
  have := sampledAngle_le_angularLength γ isPartition_ends
  simpa [sampledAngle, endsPartition, h0, h1] using this

section ArcLength

variable (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hs : 0 < sin (angle u w))
include hu hw hs

/-- The great-circle arc is exactly as long as the central angle. -/
theorem angularLength_greatArc : angularLength (greatArc u w) = ENNReal.ofReal (angle u w) := by
  refine le_antisymm ?_ (angle_le_angularLength _ (greatArc_zero) (greatArc_one hu hw hs))
  refine iSup₂_le fun n τ => iSup_le fun h => ?_
  rw [sampledAngle, sum_angle_greatArc hu hw hs τ n h.1 h.2.1 h.2.2 (fun i hi => h.mem hi)]

/-- So no curve from `u` to `w` is shorter than the great-circle arc. -/
theorem angularLength_greatArc_le (γ : ℝ → V) (h0 : γ 0 = u) (h1 : γ 1 = w) :
    angularLength (greatArc u w) ≤ angularLength γ := by
  rw [angularLength_greatArc hu hw hs]
  exact angle_le_angularLength γ h0 h1

/-- And a curve on the sphere from `u` to `w` that is as short as the arc runs
along it: each of its points is a point of the arc. -/
theorem mem_greatArc_of_angularLength_eq (γ : ℝ → V) (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖γ t‖ = 1)
    (h0 : γ 0 = u) (h1 : γ 1 = w) (hL : angularLength γ = ENNReal.ofReal (angle u w))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, γ t = greatArc u w s := by
  have hle := sampledAngle_le_angularLength γ (isPartition_through ht)
  rw [hL] at hle
  have hsum : sampledAngle γ 2 (throughPartition t) = angle u (γ t) + angle (γ t) w := by
    simp [sampledAngle, Finset.sum_range_succ, throughPartition, h0, h1]
  rw [hsum, ENNReal.ofReal_le_ofReal_iff (angle_nonneg u w)] at hle
  have hge := angle_le_angle_add_angle hu (hγ t ht) hw
  exact eq_greatArc_of_angle_add_angle hu hw hs (hγ t ht) (le_antisymm hle hge)

end ArcLength

end AngleTriangle

/-! ## Directions on the sphere -/

/-- The unit vector at latitude `φ` and longitude `lam`. -/
noncomputable def direction (φ lam : ℝ) : E3 := vec3 (cos φ * cos lam) (cos φ * sin lam) (sin φ)

/-- It is the ellipsoid normal of a geodetic coordinate at that latitude and
longitude. -/
theorem normal_eq_direction (c : GeodeticCoordinate) :
    c.normal = direction c.lat.1 c.lon.toReal := by
  simp only [GeodeticCoordinate.normal, direction, Real.Angle.cos_toReal, Real.Angle.sin_toReal]

/-- The point of the sphere of radius `R` is `R` times the direction. -/
theorem spherePoint_eq_smul (R φ lam : ℝ) :
    Projection.spherePoint R φ lam = R • direction φ lam := by
  rw [Projection.spherePoint, direction, vec3_smul]
  refine vec3_congr ?_ ?_ ?_ <;> ring

theorem inner_direction (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    inner (direction φ₁ lam₁) (direction φ₂ lam₂) =
      sin φ₁ * sin φ₂ + cos φ₁ * cos φ₂ * cos (lam₁ - lam₂) := by
  rw [direction, direction, inner_vec3, cos_sub]
  ring

theorem norm_direction (φ lam : ℝ) : ‖direction φ lam‖ = 1 := by
  have h : ‖direction φ lam‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_direction, sub_self, cos_zero, mul_one]
    nlinarith [sin_sq_add_cos_sq φ]
  nlinarith [norm_nonneg (direction φ lam)]

theorem direction_ne_zero (φ lam : ℝ) : direction φ lam ≠ 0 := by
  intro h
  have := norm_direction φ lam
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-! ## The central angle -/

/-- The angle at the centre of the sphere between two positions. -/
noncomputable def centralAngle (φ₁ lam₁ φ₂ lam₂ : ℝ) : ℝ :=
  angle (direction φ₁ lam₁) (direction φ₂ lam₂)

/-- The spherical law of cosines. -/
theorem cos_centralAngle (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    cos (centralAngle φ₁ lam₁ φ₂ lam₂) =
      sin φ₁ * sin φ₂ + cos φ₁ * cos φ₂ * cos (lam₁ - lam₂) := by
  rw [centralAngle, cos_angle, norm_direction, norm_direction, mul_one, div_one, inner_direction]

theorem sin_half_sq (x : ℝ) : sin (x / 2) ^ 2 = (1 - cos x) / 2 := by
  have h := cos_sq_add_sin_sq (x / 2)
  have h2 : cos x = 2 * cos (x / 2) ^ 2 - 1 := by
    rw [← cos_two_mul]
    ring_nf
  linarith

/-- The haversine formula, the form of the law of cosines that GIS software
evaluates because it stays accurate for nearby points. -/
theorem haversine (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    sin (centralAngle φ₁ lam₁ φ₂ lam₂ / 2) ^ 2 =
      sin ((φ₂ - φ₁) / 2) ^ 2 + cos φ₁ * cos φ₂ * sin ((lam₂ - lam₁) / 2) ^ 2 := by
  rw [sin_half_sq, sin_half_sq, sin_half_sq, cos_centralAngle, cos_sub φ₂ φ₁,
    show lam₂ - lam₁ = -(lam₁ - lam₂) by ring, cos_neg]
  ring

theorem centralAngle_nonneg (φ₁ lam₁ φ₂ lam₂ : ℝ) : 0 ≤ centralAngle φ₁ lam₁ φ₂ lam₂ :=
  angle_nonneg _ _

theorem centralAngle_le_pi (φ₁ lam₁ φ₂ lam₂ : ℝ) : centralAngle φ₁ lam₁ φ₂ lam₂ ≤ π :=
  angle_le_pi _ _

theorem centralAngle_comm (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    centralAngle φ₁ lam₁ φ₂ lam₂ = centralAngle φ₂ lam₂ φ₁ lam₁ :=
  angle_comm _ _

theorem centralAngle_self (φ lam : ℝ) : centralAngle φ lam φ lam = 0 :=
  angle_self (direction_ne_zero φ lam)

/-- The central angle is zero only between a position and itself. -/
theorem centralAngle_eq_zero_iff (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    centralAngle φ₁ lam₁ φ₂ lam₂ = 0 ↔ direction φ₁ lam₁ = direction φ₂ lam₂ := by
  constructor
  · intro h
    have hc := cos_centralAngle φ₁ lam₁ φ₂ lam₂
    rw [h, cos_zero, ← inner_direction] at hc
    -- Unit vectors with inner product one are equal.
    have hsq : ‖direction φ₁ lam₁ - direction φ₂ lam₂‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_direction, norm_direction,
        one_pow]
      linarith [real_inner_comm (direction φ₁ lam₁) (direction φ₂ lam₂)]
    exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))
  · intro h
    rw [centralAngle, h]
    exact angle_self (direction_ne_zero _ _)

/-- The triangle inequality: going through a third position is never shorter. -/
theorem centralAngle_triangle (φ₁ lam₁ φ₂ lam₂ φ₃ lam₃ : ℝ) :
    centralAngle φ₁ lam₁ φ₃ lam₃ ≤ centralAngle φ₁ lam₁ φ₂ lam₂ + centralAngle φ₂ lam₂ φ₃ lam₃ :=
  angle_le_angle_add_angle (norm_direction _ _) (norm_direction _ _) (norm_direction _ _)

/-- Along a meridian the central angle is the difference in latitude. -/
theorem centralAngle_same_meridian {φ₁ φ₂ : ℝ} (h₁ : φ₁ ∈ Set.Icc (-(π / 2)) (π / 2))
    (h₂ : φ₂ ∈ Set.Icc (-(π / 2)) (π / 2)) (lam : ℝ) :
    centralAngle φ₁ lam φ₂ lam = |φ₁ - φ₂| := by
  rw [centralAngle, angle_eq_arccos_inner (norm_direction _ _) (norm_direction _ _),
    inner_direction, sub_self, cos_zero, mul_one,
    show sin φ₁ * sin φ₂ + cos φ₁ * cos φ₂ = cos (φ₁ - φ₂) by rw [cos_sub]; ring, ← cos_abs]
  exact arccos_cos (abs_nonneg _)
    (abs_le.mpr ⟨by linarith [h₁.1, h₂.2, pi_pos], by linarith [h₁.2, h₂.1, pi_pos]⟩)

/-- Along a meridian, distances add: going north from `φ₁` through `φ₂` to
`φ₃` covers exactly the angle from `φ₁` to `φ₃`. The meridian is a great
circle, and the triangle inequality is an equality along it. -/
theorem centralAngle_meridian_add {φ₁ φ₂ φ₃ : ℝ} (h₁ : φ₁ ∈ Set.Icc (-(π / 2)) (π / 2))
    (h₂ : φ₂ ∈ Set.Icc (-(π / 2)) (π / 2)) (h₃ : φ₃ ∈ Set.Icc (-(π / 2)) (π / 2))
    (h₁₂ : φ₁ ≤ φ₂) (h₂₃ : φ₂ ≤ φ₃) (lam : ℝ) :
    centralAngle φ₁ lam φ₃ lam = centralAngle φ₁ lam φ₂ lam + centralAngle φ₂ lam φ₃ lam := by
  rw [centralAngle_same_meridian h₁ h₃, centralAngle_same_meridian h₁ h₂,
    centralAngle_same_meridian h₂ h₃, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
    abs_of_nonpos (by linarith)]
  ring

/-- Along the equator the central angle is the difference in longitude, the
shorter way round. -/
theorem centralAngle_equator (lam₁ lam₂ : ℝ) :
    centralAngle 0 lam₁ 0 lam₂ = |((lam₁ - lam₂ : ℝ) : Real.Angle).toReal| := by
  rw [centralAngle, angle_eq_arccos_inner (norm_direction _ _) (norm_direction _ _),
    inner_direction]
  simp only [sin_zero, cos_zero, mul_zero, zero_add, one_mul]
  rw [← Real.Angle.cos_coe, ← Real.Angle.cos_toReal, ← cos_abs]
  exact arccos_cos (abs_nonneg _) (Real.Angle.abs_toReal_le_pi _)

/-- The poles are antipodal: half a turn apart. -/
theorem centralAngle_poles (lam₁ lam₂ : ℝ) : centralAngle (π / 2) lam₁ (-(π / 2)) lam₂ = π := by
  rw [centralAngle, angle_eq_arccos_inner (norm_direction _ _) (norm_direction _ _),
    inner_direction]
  simp [sin_neg]

/-! ## Great-circle distance -/

/-- The distance along a sphere of radius `R`. -/
noncomputable def greatCircleDistance (R φ₁ lam₁ φ₂ lam₂ : ℝ) : ℝ := R * centralAngle φ₁ lam₁ φ₂ lam₂

variable {R : ℝ}

theorem greatCircleDistance_nonneg (hR : 0 ≤ R) (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    0 ≤ greatCircleDistance R φ₁ lam₁ φ₂ lam₂ :=
  mul_nonneg hR (centralAngle_nonneg _ _ _ _)

/-- No two points are further apart than half the circumference. -/
theorem greatCircleDistance_le (hR : 0 ≤ R) (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    greatCircleDistance R φ₁ lam₁ φ₂ lam₂ ≤ π * R := by
  rw [greatCircleDistance, mul_comm π]
  exact mul_le_mul_of_nonneg_left (centralAngle_le_pi _ _ _ _) hR

theorem greatCircleDistance_comm (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    greatCircleDistance R φ₁ lam₁ φ₂ lam₂ = greatCircleDistance R φ₂ lam₂ φ₁ lam₁ := by
  rw [greatCircleDistance, greatCircleDistance, centralAngle_comm]

theorem greatCircleDistance_eq_zero_iff (hR : 0 < R) (φ₁ lam₁ φ₂ lam₂ : ℝ) :
    greatCircleDistance R φ₁ lam₁ φ₂ lam₂ = 0 ↔ direction φ₁ lam₁ = direction φ₂ lam₂ := by
  rw [greatCircleDistance, mul_eq_zero, or_iff_right hR.ne', centralAngle_eq_zero_iff]

theorem greatCircleDistance_triangle (hR : 0 ≤ R) (φ₁ lam₁ φ₂ lam₂ φ₃ lam₃ : ℝ) :
    greatCircleDistance R φ₁ lam₁ φ₃ lam₃ ≤
      greatCircleDistance R φ₁ lam₁ φ₂ lam₂ + greatCircleDistance R φ₂ lam₂ φ₃ lam₃ := by
  simp only [greatCircleDistance, ← mul_add]
  exact mul_le_mul_of_nonneg_left (centralAngle_triangle _ _ _ _ _ _) hR

/-- A journey through places `(φ i, lam i)` is never shorter than the
great-circle distance from the first to the last. -/
theorem greatCircleDistance_le_sum (hR : 0 ≤ R) (φ lam : ℕ → ℝ) (n : ℕ) :
    greatCircleDistance R (φ 0) (lam 0) (φ n) (lam n) ≤
      ∑ i ∈ Finset.range n, greatCircleDistance R (φ i) (lam i) (φ (i + 1)) (lam (i + 1)) := by
  simp only [greatCircleDistance, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (angle_le_sum_angle (fun i => direction (φ i) (lam i)) (fun i => norm_direction _ _) n) hR

/-- On a sphere of radius 6371 km, one minute of latitude is between 1853 m
and 1854 m. This is where the nautical mile, defined as 1852 m, comes from. -/
theorem arcMinute_bounds (φ lam : ℝ) (h : φ ∈ Set.Icc (-(π / 2)) (π / 2 - π / 10800)) :
    1853 < greatCircleDistance 6371000 φ lam (φ + π / 10800) lam ∧
      greatCircleDistance 6371000 φ lam (φ + π / 10800) lam < 1854 := by
  have hpi := pi_pos
  rw [greatCircleDistance, centralAngle_same_meridian ⟨h.1, by linarith [h.2]⟩
    ⟨by linarith [h.1], by linarith [h.2]⟩, show φ - (φ + π / 10800) = -(π / 10800) by ring,
    abs_neg, abs_of_pos (by positivity)]
  constructor <;> nlinarith [pi_gt_d6, pi_lt_d6]

end Geodesic

end Geodesy
