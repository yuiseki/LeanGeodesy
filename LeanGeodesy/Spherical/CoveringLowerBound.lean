import LeanGeodesy.Spherical.CoveringBenchmarks

/-!
# Lower bounds on the covering radius of every configuration

The earlier files bound the covering radius of one given configuration. This
file proves bounds that hold for all configurations of `n` points, and with
them the first global optimality theorem for spherical covering here: the
regular tetrahedron is an optimal 4-point covering (L. Fejes Tóth's `N = 4`
case).

## Balanced supporting half-spaces

If every point lies in the half-space `⟪V, x⟫ ≤ c`, a covering of radius `r`
has `cos r · ‖V‖ ≤ c` (`cos_mul_norm_le_of_halfSpace`). Summing over several
such half-spaces gives `cos r · Σ ‖V k‖ ≤ Σ c k`
(`cos_mul_sum_norm_le_of_halfSpaces`). When the normals are balanced
(`Σ V k = 0`, as the area vectors of the faces of a closed polyhedron are), the
right-hand side can often be computed from the points, and the inequality
becomes a bound for every configuration.

## Four points

For four points `P₀, …, P₃`, let `M₁ = (P₂ - P₀) × (P₃ - P₀)` and its cyclic
companions, `M₀ = -(M₁ + M₂ + M₃)`: these are the gradients of the oriented
volume `D`, the (unnormalized) normals of the faces opposite each point. Then
`⟪M i, P j⟫` is the same for the three `j ≠ i`, and `⟪M i, P i⟫` differs from it
by `D`. With the sign chosen so that the opposite point is on the inner side,
each `M i` is a supporting half-space; `Σ M i = 0` and `‖P i‖ = 1` give
`3 Σ c i ≤ Σ ‖M i‖`, hence `cos r ≤ 1/3` (`cos_le_one_third_of_isCovering_four`).
This is the vector form of Euler's inequality `R ≥ 3 r` for a tetrahedron: the
face centroids lie on the sphere of radius `R / 3` about `(P₀ + ⋯ + P₃) / 3`.
If all `M i` vanish the four points are collinear, hence at most two distinct
points of the sphere, and they lie in a closed hemisphere.

No area, triangulation or Euler formula is needed for `N = 4`. For `N = 6, 12`
(the other cases of L. Fejes Tóth's theorem) the same weighting needs the face
structure of the hull; see `docs/COVERING.md`.
-/

namespace Geodesy.Spherical

open Real Geodesic

/-! ## Supporting half-spaces with unnormalized normals -/

/-- If every point satisfies `⟪V, p i⟫ ≤ c`, every covering radius `r ∈ [0, π]`
has `cos r · ‖V‖ ≤ c`. -/
theorem cos_mul_norm_le_of_halfSpace {n : ℕ} {p : Fin n → UnitSphere} {r : ℝ} (h0 : 0 ≤ r)
    (hπ : r ≤ π) (hcov : IsCovering p r) (V : E3) {c : ℝ}
    (hc : ∀ i, inner ℝ V (p i).1 ≤ c) : cos r * ‖V‖ ≤ c := by
  by_cases hV : V = 0
  · obtain ⟨i, -⟩ := hcov (Classical.arbitrary UnitSphere)
    have := hc i
    rw [hV, inner_zero_left] at this
    rw [hV, norm_zero, mul_zero]
    exact this
  · have hn : 0 < ‖V‖ := norm_pos_iff.2 hV
    let u : UnitSphere := ⟨‖V‖⁻¹ • V, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']⟩
    have h := cos_le_of_supportPlane h0 hπ hcov u (c := c / ‖V‖) (fun i => by
      show inner ℝ (p i).1 (‖V‖⁻¹ • V) ≤ c / ‖V‖
      rw [inner_smul_right, real_inner_comm, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (hc i) (inv_nonneg.2 hn.le))
    rwa [le_div_iff₀ hn] at h

/-- Summing supporting half-spaces: `cos r · Σ ‖V k‖ ≤ Σ c k`. -/
theorem cos_mul_sum_norm_le_of_halfSpaces {n m : ℕ} {p : Fin n → UnitSphere} {r : ℝ}
    (h0 : 0 ≤ r) (hπ : r ≤ π) (hcov : IsCovering p r) (V : Fin m → E3) (c : Fin m → ℝ)
    (hc : ∀ k i, inner ℝ (V k) (p i).1 ≤ c k) :
    cos r * ∑ k, ‖V k‖ ≤ ∑ k, c k := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => cos_mul_norm_le_of_halfSpace h0 hπ hcov (V k) (hc k)

/-! ## Coordinates and the cross product -/

/-- The cross product in coordinates. -/
noncomputable def cross3 (a b : E3) : E3 :=
  vec3 (a 1 * b 2 - a 2 * b 1) (a 2 * b 0 - a 0 * b 2) (a 0 * b 1 - a 1 * b 0)

theorem inner_E3 (x y : E3) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  have := inner_vec3 (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
  rwa [vec3_eta, vec3_eta] at this

/-- A nonzero vector orthogonal to every `x` with `x × d = 0`, for `d ≠ 0`. -/
private theorem exists_perp_of_ne {d : E3} (hd : d ≠ 0) :
    ∃ w : E3, w ≠ 0 ∧ ∀ x : E3, cross3 x d = 0 → inner ℝ w x = 0 := by
  have hcoord : d 0 ≠ 0 ∨ d 1 ≠ 0 ∨ d 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hd
    rw [← vec3_eta d, h.1, h.2.1, h.2.2]
    ext i; fin_cases i <;> rfl
  have orth : ∀ (e x : E3), cross3 x d = 0 → inner ℝ (cross3 d e) x = 0 := by
    intro e x hx
    have h0 := congrArg (· 0) hx
    have h1 := congrArg (· 1) hx
    have h2 := congrArg (· 2) hx
    simp only [cross3, vec3_0, vec3_1, vec3_2, PiLp.zero_apply] at h0 h1 h2
    rw [inner_E3]
    simp only [cross3, vec3_0, vec3_1, vec3_2]
    linear_combination (e 0) * h0 + (e 1) * h1 + (e 2) * h2
  rcases hcoord with h | h | h
  · refine ⟨cross3 d (vec3 0 1 0), fun hw => h ?_, fun x hx => orth _ x hx⟩
    have := congrArg (· 2) hw
    simpa [cross3] using this
  · refine ⟨cross3 d (vec3 1 0 0), fun hw => h ?_, fun x hx => orth _ x hx⟩
    have := congrArg (· 2) hw
    simpa [cross3] using this
  · refine ⟨cross3 d (vec3 1 0 0), fun hw => h ?_, fun x hx => orth _ x hx⟩
    have := congrArg (· 1) hw
    simpa [cross3] using this

/-- Three vectors with pairwise vanishing cross products have a common nonzero
orthogonal vector. -/
private theorem exists_perp_of_cross_eq_zero {a b c : E3} (hab : cross3 a b = 0)
    (hbc : cross3 b c = 0) (hca : cross3 c a = 0) :
    ∃ w : E3, w ≠ 0 ∧ inner ℝ w a = 0 ∧ inner ℝ w b = 0 ∧ inner ℝ w c = 0 := by
  have self : ∀ x : E3, cross3 x x = 0 := by
    intro x; ext i; fin_cases i <;> simp [cross3] <;> ring
  have swap : ∀ x y : E3, cross3 x y = 0 → cross3 y x = 0 := by
    intro x y h
    have hneg : cross3 y x = -cross3 x y := by
      ext i; fin_cases i <;> simp [cross3] <;> ring
    rw [hneg, h, neg_zero]
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · by_cases hc : c = 0
      · refine ⟨vec3 1 0 0, fun h => ?_, by simp [ha], by simp [hb], by simp [hc]⟩
        have := congrArg (· 0) h
        simp at this
      · obtain ⟨w, hw, hperp⟩ := exists_perp_of_ne hc
        exact ⟨w, hw, hperp a (swap _ _ hca), hperp b (hbc), hperp c (self c)⟩
    · obtain ⟨w, hw, hperp⟩ := exists_perp_of_ne hb
      exact ⟨w, hw, hperp a hab, hperp b (self b), hperp c (swap _ _ hbc)⟩
  · obtain ⟨w, hw, hperp⟩ := exists_perp_of_ne ha
    exact ⟨w, hw, hperp a (self a), hperp b (swap _ _ hab), hperp c hca⟩

/-! ## Four points -/

/-- Every covering of `S²` by four closed caps of radius `r ∈ [0, π]` has
`cos r ≤ 1/3`. -/
theorem cos_le_one_third_of_isCovering_four {p : Fin 4 → UnitSphere} {r : ℝ} (h0 : 0 ≤ r)
    (hπ : r ≤ π) (hcov : IsCovering p r) : cos r ≤ 1 / 3 := by
  set P0 := (p 0).1 with hP0
  set P1 := (p 1).1 with hP1
  set P2 := (p 2).1 with hP2
  set P3 := (p 3).1 with hP3
  set a := P1 - P0
  set b := P2 - P0
  set c := P3 - P0
  set M1 := cross3 b c
  set M2 := cross3 c a
  set M3 := cross3 a b
  set M0 := -(M1 + M2 + M3)
  set D := inner ℝ a M1
  by_cases hdeg : M1 = 0 ∧ M2 = 0 ∧ M3 = 0
  · -- Degenerate: the four points are collinear, so they lie in a closed hemisphere.
    obtain ⟨hM1, hM2, hM3⟩ := hdeg
    obtain ⟨w, hw, hwa, hwb, hwc⟩ := exists_perp_of_cross_eq_zero hM3 hM1 hM2
    have hconst : ∀ i : Fin 4, inner ℝ w (p i).1 = inner ℝ w P0 := by
      intro i
      fin_cases i
      · rfl
      · show inner ℝ w P1 = _
        have : P1 = a + P0 := by simp [a]
        rw [this, inner_add_right, hwa, zero_add]
      · show inner ℝ w P2 = _
        have : P2 = b + P0 := by simp [b]
        rw [this, inner_add_right, hwb, zero_add]
      · show inner ℝ w P3 = _
        have : P3 = c + P0 := by simp [c]
        rw [this, inner_add_right, hwc, zero_add]
    set s : ℝ := if inner ℝ w P0 ≤ 0 then 1 else -1 with hs
    have hsw : s * inner ℝ w P0 ≤ 0 := by
      rw [hs]; split_ifs with h
      · linarith
      · push Not at h; linarith
    have hsabs : |s| = 1 := by rw [hs]; split_ifs <;> simp
    have h := cos_mul_norm_le_of_halfSpace h0 hπ hcov (s • w) (c := 0) (fun i => by
      rw [inner_smul_left, hconst i]; simpa using hsw)
    rw [norm_smul, Real.norm_eq_abs, hsabs, one_mul] at h
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
    have : cos r ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    linarith
  · -- Nondegenerate weighting by the face normals.
    set σ : ℝ := if 0 ≤ D then -1 else 1 with hσ
    have hσD : σ * D ≤ 0 := by
      rw [hσ]; split_ifs with h
      · linarith
      · push Not at h; nlinarith
    have hσabs : |σ| = 1 := by rw [hσ]; split_ifs <;> simp
    -- the face identities, as polynomial identities in the coordinates
    have e : ∀ (x y : E3), inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := inner_E3
    have c1 : inner ℝ M1 P2 = inner ℝ M1 P0 ∧ inner ℝ M1 P3 = inner ℝ M1 P0 ∧
        inner ℝ M1 P1 = inner ℝ M1 P0 + D := by
      simp only [e, M1, D, a, b, c, cross3, vec3_0, vec3_1, vec3_2, PiLp.sub_apply]
      refine ⟨by ring, by ring, by ring⟩
    have c2 : inner ℝ M2 P1 = inner ℝ M2 P0 ∧ inner ℝ M2 P3 = inner ℝ M2 P0 ∧
        inner ℝ M2 P2 = inner ℝ M2 P0 + D := by
      simp only [e, M1, M2, D, a, b, c, cross3, vec3_0, vec3_1, vec3_2, PiLp.sub_apply]
      refine ⟨by ring, by ring, by ring⟩
    have c3 : inner ℝ M3 P1 = inner ℝ M3 P0 ∧ inner ℝ M3 P2 = inner ℝ M3 P0 ∧
        inner ℝ M3 P3 = inner ℝ M3 P0 + D := by
      simp only [e, M1, M3, D, a, b, c, cross3, vec3_0, vec3_1, vec3_2, PiLp.sub_apply]
      refine ⟨by ring, by ring, by ring⟩
    have c0 : inner ℝ M0 P2 = inner ℝ M0 P1 ∧ inner ℝ M0 P3 = inner ℝ M0 P1 ∧
        inner ℝ M0 P0 = inner ℝ M0 P1 + D := by
      simp only [e, M0, M1, M2, M3, D, a, b, c, cross3, vec3_0, vec3_1, vec3_2,
        PiLp.sub_apply, PiLp.neg_apply, PiLp.add_apply]
      refine ⟨by ring, by ring, by ring⟩
    have self_le : ∀ X : ℝ, σ * (X + D) ≤ σ * X := fun X => by nlinarith [hσD]
    have q0 : (p 0).1 = P0 := rfl
    have q1 : (p 1).1 = P1 := rfl
    have q2 : (p 2).1 = P2 := rfl
    have q3 : (p 3).1 = P3 := rfl
    have face : ∀ (M : E3) (C : ℝ), inner ℝ (σ • M) P0 ≤ C → inner ℝ (σ • M) P1 ≤ C →
        inner ℝ (σ • M) P2 ≤ C → inner ℝ (σ • M) P3 ≤ C → cos r * ‖σ • M‖ ≤ C := by
      intro M C h0' h1' h2' h3'
      refine cos_mul_norm_le_of_halfSpace h0 hπ hcov (σ • M) (fun i => ?_)
      fin_cases i
      · exact h0'
      · exact h1'
      · exact h2'
      · exact h3'
    simp only [inner_smul_left, conj_trivial] at face
    have f0 := face M0 (σ * inner ℝ M0 P1) (by rw [c0.2.2]; exact self_le _) le_rfl
      (by rw [c0.1]) (by rw [c0.2.1])
    have f1 := face M1 (σ * inner ℝ M1 P0) le_rfl (by rw [c1.2.2]; exact self_le _)
      (by rw [c1.1]) (by rw [c1.2.1])
    have f2 := face M2 (σ * inner ℝ M2 P0) le_rfl (by rw [c2.1])
      (by rw [c2.2.2]; exact self_le _) (by rw [c2.2.1])
    have f3 := face M3 (σ * inner ℝ M3 P0) le_rfl (by rw [c3.1]) (by rw [c3.2.1])
      (by rw [c3.2.2]; exact self_le _)
    -- the weights balance: Σ ⟪M k, P₀ + ⋯ + P₃⟫ = 0
    have hsum : 3 * (σ * inner ℝ M0 P1 + σ * inner ℝ M1 P0 + σ * inner ℝ M2 P0 +
        σ * inner ℝ M3 P0) + (σ * inner ℝ M0 P0 + σ * inner ℝ M1 P1 + σ * inner ℝ M2 P2 +
        σ * inner ℝ M3 P3) = 0 := by
      simp only [e, M0, M1, M2, M3, a, b, c, cross3, vec3_0, vec3_1, vec3_2,
        PiLp.sub_apply, PiLp.neg_apply, PiLp.add_apply]
      ring
    have hnorm : ∀ (M P : E3), ‖P‖ = 1 → -(σ * inner ℝ M P) ≤ ‖σ • M‖ := by
      intro M P hP
      have h := abs_real_inner_le_norm (σ • M) P
      rw [hP, mul_one, inner_smul_left, conj_trivial] at h
      exact (neg_le_abs _).trans h
    have n0 := hnorm M0 P0 (p 0).2
    have n1 := hnorm M1 P1 (p 1).2
    have n2 := hnorm M2 P2 (p 2).2
    have n3 := hnorm M3 P3 (p 3).2
    set T := ‖σ • M0‖ + ‖σ • M1‖ + ‖σ • M2‖ + ‖σ • M3‖ with hT
    have hTpos : 0 < T := by
      have hn : ∀ M : E3, ‖σ • M‖ = ‖M‖ := fun M => by
        rw [norm_smul, Real.norm_eq_abs, hσabs, one_mul]
      rw [hT, hn, hn, hn, hn]
      by_contra hle
      push Not at hle
      have g0 := norm_nonneg M0
      have g1 := norm_nonneg M1
      have g2 := norm_nonneg M2
      have g3 := norm_nonneg M3
      have z1 : ‖M1‖ = 0 := by linarith
      have z2 : ‖M2‖ = 0 := by linarith
      have z3 : ‖M3‖ = 0 := by linarith
      exact hdeg ⟨norm_eq_zero.1 z1, norm_eq_zero.1 z2, norm_eq_zero.1 z3⟩
    have hle : cos r * T ≤ T / 3 := by
      have := add_le_add (add_le_add (add_le_add f0 f1) f2) f3
      rw [← mul_add, ← mul_add, ← mul_add] at this
      linarith
    by_contra hgt
    push Not at hgt
    nlinarith

/-- Every configuration of four points has covering radius at least
`arccos (1/3)`. -/
theorem arccos_one_third_le_coveringRadius (p : Fin 4 → UnitSphere) :
    arccos (1 / 3) ≤ coveringRadius (by norm_num : 1 ≤ 4) p := by
  have h0 := coveringRadius_nonneg (by norm_num : 1 ≤ 4) p
  have hπ := coveringRadius_le_pi (by norm_num : 1 ≤ 4) p
  have hcos := cos_le_one_third_of_isCovering_four h0 hπ
    (isCovering_coveringRadius (by norm_num : 1 ≤ 4) p)
  calc arccos (1 / 3) ≤ arccos (cos (coveringRadius _ p)) := arccos_le_arccos_of_le hcos
    _ = coveringRadius _ p := arccos_cos h0 hπ

/-- Global optimality for `N = 4` (L. Fejes Tóth): four closed caps of radius `r`
can cover `S²` exactly when `arccos (1/3) ≤ r`, and the regular tetrahedron is
an optimal configuration. -/
theorem covering_4_optimal (r : ℝ) :
    (∃ p : Fin 4 → UnitSphere, IsCovering p r) ↔ arccos (1 / 3) ≤ r := by
  constructor
  · rintro ⟨p, hp⟩
    have hr := (coveringRadius_le_iff (by norm_num : 1 ≤ 4) p r).2 hp
    exact (arccos_one_third_le_coveringRadius p).trans hr
  · intro hr
    refine ⟨tetrahedron4, (coveringRadius_le_iff (by norm_num : 1 ≤ 4) _ r).1 ?_⟩
    rw [coveringRadius_tetrahedron4]
    exact hr

/-- The regular tetrahedron minimizes the covering radius among all
configurations of four points. -/
theorem coveringRadius_tetrahedron4_le (q : Fin 4 → UnitSphere) :
    coveringRadius (by norm_num : 1 ≤ 4) tetrahedron4 ≤ coveringRadius (by norm_num : 1 ≤ 4) q := by
  rw [coveringRadius_tetrahedron4]
  exact arccos_one_third_le_coveringRadius q

/-! ## Two and three points -/

/-- If all the points have the same inner product with a nonzero `w` (they lie
in a plane), they lie in a closed hemisphere, and every covering radius
`r ∈ [0, π]` has `cos r ≤ 0`. -/
theorem cos_nonpos_of_inner_const {n : ℕ} {p : Fin n → UnitSphere} {r : ℝ} (h0 : 0 ≤ r)
    (hπ : r ≤ π) (hcov : IsCovering p r) {w : E3} (hw : w ≠ 0) {κ : ℝ}
    (hconst : ∀ i, inner ℝ w (p i).1 = κ) : cos r ≤ 0 := by
  set s : ℝ := if κ ≤ 0 then 1 else -1 with hs
  have hsw : s * κ ≤ 0 := by
    rw [hs]; split_ifs with h
    · linarith
    · push Not at h; linarith
  have hsabs : |s| = 1 := by rw [hs]; split_ifs <;> simp
  have h := cos_mul_norm_le_of_halfSpace h0 hπ hcov (s • w) (c := 0) (fun i => by
    rw [inner_smul_left, hconst i]; simpa using hsw)
  rw [norm_smul, Real.norm_eq_abs, hsabs, one_mul] at h
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  by_contra hc
  push Not at hc
  nlinarith

/-- Three points always lie in a closed hemisphere: every covering of `S²` by
three caps of radius `r ∈ [0, π]` has `cos r ≤ 0`. -/
theorem cos_nonpos_of_isCovering_three {p : Fin 3 → UnitSphere} {r : ℝ} (h0 : 0 ≤ r)
    (hπ : r ≤ π) (hcov : IsCovering p r) : cos r ≤ 0 := by
  set a := (p 1).1 - (p 0).1
  set b := (p 2).1 - (p 0).1
  have hperp : ∃ w : E3, w ≠ 0 ∧ inner ℝ w a = 0 ∧ inner ℝ w b = 0 := by
    by_cases hab : cross3 a b = 0
    · have self : cross3 b b = 0 := by ext i; fin_cases i <;> simp [cross3] <;> ring
      have hba : cross3 b a = 0 := by
        have hneg : cross3 b a = -cross3 a b := by
          ext i; fin_cases i <;> simp [cross3] <;> ring
        rw [hneg, hab, neg_zero]
      obtain ⟨w, hw, hwa, hwb, -⟩ := exists_perp_of_cross_eq_zero hab self hba
      exact ⟨w, hw, hwa, hwb⟩
    · refine ⟨cross3 a b, hab, ?_, ?_⟩
      · rw [inner_E3]; simp only [cross3, vec3_0, vec3_1, vec3_2]; ring
      · rw [inner_E3]; simp only [cross3, vec3_0, vec3_1, vec3_2]; ring
  obtain ⟨w, hw, hwa, hwb⟩ := hperp
  refine cos_nonpos_of_inner_const h0 hπ hcov hw (κ := inner ℝ w (p 0).1) fun i => ?_
  fin_cases i
  · rfl
  · show inner ℝ w (p 1).1 = _
    have : (p 1).1 = a + (p 0).1 := by simp [a]
    rw [this, inner_add_right, hwa, zero_add]
  · show inner ℝ w (p 2).1 = _
    have : (p 2).1 = b + (p 0).1 := by simp [b]
    rw [this, inner_add_right, hwb, zero_add]

/-- Points summing to zero cover `S²` at radius `π / 2`: for every `x` the inner
products `⟪p i, x⟫` sum to zero, so one of them is nonnegative. -/
theorem isCovering_pi_div_two_of_sum_eq_zero {n : ℕ} (hn : 1 ≤ n) {p : Fin n → UnitSphere}
    (hsum : ∑ i, (p i).1 = 0) : IsCovering p (π / 2) := by
  rw [isCovering_iff_inner p (by positivity) (by linarith [pi_pos]), cos_pi_div_two]
  intro x
  by_contra h
  push Not at h
  have hneg : ∑ i, inner ℝ (p i).1 x.1 < 0 :=
    Finset.sum_neg (fun i _ => h i) (Finset.univ_nonempty_iff.2 ⟨⟨0, by omega⟩⟩)
  rw [← sum_inner, hsum, inner_zero_left] at hneg
  exact lt_irrefl _ hneg

/-- Global optimality for `N = 3`: three caps of radius `r` cover `S²` exactly
when `π / 2 ≤ r`. -/
theorem covering_3_optimal (r : ℝ) :
    (∃ p : Fin 3 → UnitSphere, IsCovering p r) ↔ π / 2 ≤ r := by
  constructor
  · rintro ⟨p, hp⟩
    have hr := (coveringRadius_le_iff (by norm_num : 1 ≤ 3) p r).2 hp
    have h0 := coveringRadius_nonneg (by norm_num : 1 ≤ 3) p
    have hπ := coveringRadius_le_pi (by norm_num : 1 ≤ 3) p
    have hcos := cos_nonpos_of_isCovering_three h0 hπ
      (isCovering_coveringRadius (by norm_num : 1 ≤ 3) p)
    have : π / 2 ≤ coveringRadius (by norm_num : 1 ≤ 3) p := by
      by_contra hlt
      push Not at hlt
      have := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hlt⟩
      linarith
    linarith
  · intro hr
    refine ⟨eqTriangle3, fun x => ?_⟩
    have hsum : ∑ i, (eqTriangle3 i).1 = 0 := by
      rw [Fin.sum_univ_three]
      simp only [eqTriangle3, vec3_add]
      ext i; fin_cases i <;> (simp; try ring)
    obtain ⟨i, hi⟩ := isCovering_pi_div_two_of_sum_eq_zero (by norm_num) hsum x
    exact ⟨i, le_trans hi hr⟩

/-- Global optimality for `N = 2`: two caps of radius `r` cover `S²` exactly
when `π / 2 ≤ r`. -/
theorem covering_2_optimal (r : ℝ) :
    (∃ p : Fin 2 → UnitSphere, IsCovering p r) ↔ π / 2 ≤ r := by
  constructor
  · rintro ⟨p, hp⟩
    refine (covering_3_optimal r).1 ⟨![p 0, p 1, p 1], fun x => ?_⟩
    obtain ⟨i, hi⟩ := hp x
    fin_cases i
    · exact ⟨0, hi⟩
    · exact ⟨1, hi⟩
  · intro hr
    refine ⟨poles2, fun x => ?_⟩
    have hsum : ∑ i, (poles2 i).1 = 0 := by
      rw [Fin.sum_univ_two]
      simp only [poles2, vec3_add]
      ext i; fin_cases i <;> simp
    obtain ⟨i, hi⟩ := isCovering_pi_div_two_of_sum_eq_zero (by norm_num) hsum x
    exact ⟨i, le_trans hi hr⟩

end Geodesy.Spherical
