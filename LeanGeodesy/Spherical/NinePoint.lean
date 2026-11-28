import LeanGeodesy.Spherical.Jucovic9

/-!
# The nine-point covering problem, decomposed

`Jucovic9.lean` proves the covering radius of Jucovič's configuration and its
optimality within one symmetric family. This file separates what global
optimality would need into independent statements, and proves the parts that
are proved.

## The combinatorial type

`IsTTPSupported q` says that each of the 14 triangles of the triaugmented
triangular prism, with the labelling of `jucovicFaceVerts` (`A₀A₁A₂` the
equatorial vertices, `Bₖ`, `Cₖ` the upper and lower ones), lies in a plane
`⟪N, ·⟫ = κ` with `κ > 0` that has all nine points on its inner side. `IsTTP p`
allows any relabelling. For points in general position this says that the
hull is a triaugmented triangular prism with that labelling and contains the
origin in its interior; that equivalence with the face-lattice definition is
not proved here, and only the supporting-plane form is used.

## Three independent statements

* `TTPOptimal`: every configuration of this type has covering radius at least
  `arccos h⋆`. Open; numerically supported (see `docs/research`).
* `OptimalIsTTP`: every optimal 9-point configuration has this type. This is
  what the abstract of Wimmer 2017 reports; its exact hypotheses and proof are
  unread here, so it is a hypothesis, never a theorem of this file.
* Proved: `jucovicStar` has the type (`isTTP_jucovicStar`), and the two
  statements together give global optimality
  (`coveringRadius_jucovicStar_le_of_TTP`).

## A reduction of `TTPOptimal` to one smooth inequality

`arccos_le_coveringRadius_of_harmonic`: if some supporting half-spaces
`⟪N k, ·⟫ ≤ κ k` and weights `w k ≥ 0` with `Σ w = 1` satisfy
`Σ w k ‖N k‖ / κ k ≥ 1/ρ` (the weighted harmonic mean of the face distances
`κ k / ‖N k‖` is at most `ρ`), then the covering radius is at least `arccos ρ`.
It is `cos_mul_sum_norm_le_of_halfSpaces` with `V k = (w k / κ k) N k`. With
the KKT multipliers of Jucovič's configuration as weights (each triangle `λ_T`,
each side `λ_V`), equality holds there (`jucovic_active_dist`), and
`TTPHarmonic` states the inequality for every configuration of the type;
`TTPHarmonic → TTPOptimal` is proved. `TTPHarmonic` itself is open.
-/

namespace Geodesy.Spherical

open Real Geodesic

/-! ## Face distances of Jucovič's configuration: 8 active, 6 inactive -/

private theorem norm_eq_of_sq {v : E3} {c : ℝ} (hc : 0 ≤ c) (h : ‖v‖ ^ 2 = c ^ 2) : ‖v‖ = c :=
  (sq_eq_sq₀ (norm_nonneg _) hc).1 h

/-- The squared norms of the face normals. -/
theorem jucovicFaceNormal_norm_sq (t h : ℝ) (f : Fin 14) :
    ‖jucovicFaceNormal t h f‖ ^ 2 =
      ![1, 1, h ^ 2 + (1 - t / 2) ^ 2, h ^ 2 + (1 - t / 2) ^ 2, h ^ 2 + (1 - t / 2) ^ 2,
        h ^ 2 + (1 - t / 2) ^ 2, h ^ 2 + (1 - t / 2) ^ 2, h ^ 2 + (1 - t / 2) ^ 2,
        4 * t ^ 2 - 4 * t + 4, 4 * t ^ 2 - 4 * t + 4, 4 * t ^ 2 - 4 * t + 4,
        4 * t ^ 2 - 4 * t + 4, 4 * t ^ 2 - 4 * t + 4, 4 * t ^ 2 - 4 * t + 4] f := by
  have h3 := sqrt3_sq
  fin_cases f <;> (show ‖vec3 _ _ _‖ ^ 2 = _; rw [norm_vec3_sq]; simp) <;>
    first
    | done
    | ring1
    | linear_combination (t ^ 2) * h3
    | linear_combination (h ^ 2 / 4) * h3
    | linear_combination ((1 - t) ^ 2) * h3


/-- The eight active faces (the two triangles and the six sides) are at distance
exactly `h⋆` from the origin: `‖N‖ h⋆ = κ`. -/
theorem jucovic_active_dist (f : Fin 14) (hf : f.val < 2 ∨ 8 ≤ f.val) :
    ‖jucovicFaceNormal tStar hStar f‖ * hStar = jucovicFaceOffset tStar hStar f := by
  have hts := tStar_mem
  have h2 := hStar_sq
  have hps := hStar_pos
  have hq : 4 * tStar ^ 4 - 4 * tStar ^ 3 + 3 * tStar ^ 2 + 4 * tStar - 4 = 0 :=
    jucovicQuartic_tStar
  have hn := jucovicFaceNormal_norm_sq tStar hStar f
  have hs : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have h3 := sqrt3_sq
  -- the side normals have ‖N‖ = √3 t⋆ / h⋆
  have side : ∀ v : E3, ‖v‖ ^ 2 = 4 * tStar ^ 2 - 4 * tStar + 4 → ‖v‖ * hStar = √3 * tStar := by
    intro v hv
    have : ‖v‖ = √3 * tStar / hStar := by
      apply norm_eq_of_sq (by have := hts.1; positivity)
      rw [hv, div_pow, mul_pow, h3, h2]
      field_simp
      have : 1 - tStar ^ 2 ≠ 0 := by nlinarith [hts.1, hts.2]
      rw [eq_div_iff this]
      linear_combination -hq
    rw [this]; field_simp
  fin_cases f <;> simp at hf <;> simp at hn <;> simp only [jucovicFaceOffset] <;> simp <;>
    first
    | (rw [norm_eq_of_sq zero_le_one (by simpa using hn)]; ring)
    | exact side _ hn

/-- The six slopes are inactive: their distance `κ / ‖N‖` exceeds `h⋆`. -/
theorem jucovic_slope_dist (f : Fin 14) (hf : 2 ≤ f.val ∧ f.val < 8) :
    ‖jucovicFaceNormal tStar hStar f‖ * hStar < jucovicFaceOffset tStar hStar f := by
  have hts := tStar_mem
  have h2 := hStar_sq
  have hps := hStar_pos
  have hn := jucovicFaceNormal_norm_sq tStar hStar f
  have hlt : ∀ v : E3, ‖v‖ ^ 2 = hStar ^ 2 + (1 - tStar / 2) ^ 2 → ‖v‖ * hStar < hStar := by
    intro v hv
    have : ‖v‖ < 1 := by
      have : ‖v‖ ^ 2 < 1 := by rw [hv, h2]; nlinarith [hts.1, hts.2]
      nlinarith [norm_nonneg v]
    nlinarith
  fin_cases f <;> simp at hf <;> simp at hn <;> simp only [jucovicFaceOffset] <;> simp <;>
    exact hlt _ hn

/-! ## The weighted harmonic mean of face distances bounds the covering radius -/

/-- If supporting half-spaces `⟪N k, ·⟫ ≤ κ k` (`κ k > 0`) and weights `w k ≥ 0`,
`Σ w = 1`, have `Σ w k ‖N k‖ / κ k ≥ 1/ρ`, the covering radius is at least
`arccos ρ`. (`κ k / ‖N k‖` is the distance of the `k`-th plane, so the hypothesis
says that the weighted harmonic mean of the distances is at most `ρ`.) -/
theorem arccos_le_coveringRadius_of_harmonic {n m : ℕ} (hn : 1 ≤ n) (p : Fin n → UnitSphere)
    (N : Fin m → E3) (κ w : Fin m → ℝ) (hκ : ∀ k, 0 < κ k) (hw : ∀ k, 0 ≤ w k)
    (hsum : ∑ k, w k = 1) (hsupp : ∀ k i, inner ℝ (N k) (p i).1 ≤ κ k) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hharm : 1 / ρ ≤ ∑ k, w k * ‖N k‖ / κ k) :
    arccos ρ ≤ coveringRadius hn p := by
  set r := coveringRadius hn p
  have h0 := coveringRadius_nonneg hn p
  have hπ := coveringRadius_le_pi hn p
  have hcov : IsCovering p r := isCovering_coveringRadius hn p
  have key := cos_mul_sum_norm_le_of_halfSpaces h0 hπ hcov (fun k => (w k / κ k) • N k) w
    (fun k i => by
      rw [real_inner_smul_left]
      have hwk : 0 ≤ w k / κ k := div_nonneg (hw k) (hκ k).le
      calc w k / κ k * inner ℝ (N k) (p i).1 ≤ w k / κ k * κ k :=
            mul_le_mul_of_nonneg_left (hsupp k i) hwk
        _ = w k := by field_simp [(hκ k).ne'])
  have hnorm : ∀ k, ‖(w k / κ k) • N k‖ = w k * ‖N k‖ / κ k := fun k => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hw k) (hκ k).le)]; ring
  simp only [hnorm, hsum] at key
  set S := ∑ k, w k * ‖N k‖ / κ k
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hharm
  have hc : cos r ≤ ρ := by
    by_contra hgt
    push Not at hgt
    have h1 : 1 ≤ ρ * S := by rw [div_le_iff₀ hρ0] at hharm; linarith
    nlinarith
  calc arccos ρ ≤ arccos (cos r) := arccos_le_arccos_of_le hc
    _ = r := arccos_cos h0 hπ

/-! ## The combinatorial type and the decomposition -/

/-- Each of the 14 triangles of the triaugmented triangular prism (labelled as in
`jucovicFaceVerts`) lies in a plane `⟪N, ·⟫ = κ`, `κ > 0`, with all nine points on
its inner side. -/
def IsTTPSupported (q : Fin 9 → UnitSphere) : Prop :=
  ∀ f : Fin 14, ∃ N : E3, ∃ κ : ℝ, 0 < κ ∧
    inner ℝ N (q (jucovicFaceVerts f).1).1 = κ ∧ inner ℝ N (q (jucovicFaceVerts f).2.1).1 = κ ∧
    inner ℝ N (q (jucovicFaceVerts f).2.2).1 = κ ∧ ∀ i, inner ℝ N (q i).1 ≤ κ

/-- A configuration has the type of the triaugmented triangular prism under some
labelling of its points. -/
def IsTTP (p : Fin 9 → UnitSphere) : Prop :=
  ∃ σ : Equiv.Perm (Fin 9), IsTTPSupported (p ∘ σ)

/-- Optimality within the type (open). -/
def TTPOptimal : Prop :=
  ∀ p : Fin 9 → UnitSphere, IsTTP p → arccos hStar ≤ coveringRadius (by norm_num : 1 ≤ 9) p

/-- Every optimal 9-point configuration has the type (reported by the abstract of
Wimmer 2017; unverified here, so only ever a hypothesis). -/
def OptimalIsTTP : Prop :=
  ∀ p : Fin 9 → UnitSphere,
    (∀ q, coveringRadius (by norm_num : 1 ≤ 9) p ≤ coveringRadius (by norm_num : 1 ≤ 9) q) →
      IsTTP p

/-- The weighted harmonic-mean inequality over the eight faces that are active at
Jucovič's configuration (two triangles with weight `wT`, six sides with weight
`wV`), for every configuration of the type and every choice of supporting
planes (open). -/
def TTPHarmonic (wT wV : ℝ) : Prop :=
  ∀ q : Fin 9 → UnitSphere, ∀ (N : Fin 14 → E3) (κ : Fin 14 → ℝ),
    (∀ f, 0 < κ f ∧ ∀ i, inner ℝ (N f) (q i).1 ≤ κ f) →
      1 / hStar ≤ wT * ‖N 0‖ / κ 0 + wT * ‖N 1‖ / κ 1 + wV * ‖N 8‖ / κ 8 + wV * ‖N 9‖ / κ 9 +
        wV * ‖N 10‖ / κ 10 + wV * ‖N 11‖ / κ 11 + wV * ‖N 12‖ / κ 12 + wV * ‖N 13‖ / κ 13

/-- Jucovič's configuration has the type. -/
theorem isTTP_jucovicStar : IsTTP jucovicStar := by
  refine ⟨Equiv.refl _, fun f => ?_⟩
  have hts := tStar_mem
  have hps := hStar_pos
  have hs : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨e1, e2, e3⟩ := jucovic_face_on tStar hStar f
  refine ⟨jucovicFaceNormal tStar hStar f, jucovicFaceOffset tStar hStar f, ?_, e1, e2, e3,
    fun i => jucovic_face_supporting (by linarith [hts.1]) hts.2.le hps f i⟩
  have ht0 : 0 < tStar := by linarith [hts.1]
  fin_cases f <;> simp [jucovicFaceOffset] <;> positivity

/-- Permuting the points does not change the covering radius. -/
theorem coveringRadius_comp_perm (p : Fin 9 → UnitSphere) (σ : Equiv.Perm (Fin 9)) :
    coveringRadius (by norm_num : 1 ≤ 9) (p ∘ σ) = coveringRadius (by norm_num : 1 ≤ 9) p := by
  apply le_antisymm
  · rw [coveringRadius_le_iff, isCovering_comp_equiv]
    exact isCovering_coveringRadius _ p
  · rw [coveringRadius_le_iff, ← isCovering_comp_equiv p σ]
    exact isCovering_coveringRadius _ _

/-- The harmonic-mean inequality, for any weights `wT, wV ≥ 0` with
`2 wT + 6 wV = 1`, implies optimality within the type. -/
theorem TTPOptimal_of_harmonic {wT wV : ℝ} (hT : 0 ≤ wT) (hV : 0 ≤ wV)
    (hsum : 2 * wT + 6 * wV = 1) (hH : TTPHarmonic wT wV) : TTPOptimal := by
  intro p ⟨σ, hσ⟩
  rw [← coveringRadius_comp_perm p σ]
  choose N κ hκ _ _ _ hsupp using hσ
  have hps := hStar_pos
  let idx : Fin 8 → Fin 14 := ![0, 1, 8, 9, 10, 11, 12, 13]
  let w : Fin 8 → ℝ := ![wT, wT, wV, wV, wV, wV, wV, wV]
  refine arccos_le_coveringRadius_of_harmonic _ (p ∘ σ) (fun k => N (idx k)) (fun k => κ (idx k))
    w (fun k => hκ _) (fun k => by fin_cases k <;> simp [w, hT, hV]) ?_
    (fun k i => hsupp _ i) hps ?_
  · simp [w, Fin.sum_univ_eight]; linarith
  · have := hH (p ∘ σ) N κ (fun f => ⟨hκ f, hsupp f⟩)
    simp only [Fin.sum_univ_eight]
    simpa [w, idx] using this

/-- Conditional global optimality: optimality within the type together with the
reduction of optimal configurations to the type gives optimality of Jucovič's
configuration among all 9-point configurations. Both are hypotheses. -/
theorem coveringRadius_jucovicStar_le_of_TTP (hT : TTPOptimal) (hW : OptimalIsTTP)
    (q : Fin 9 → UnitSphere) :
    coveringRadius (by norm_num : 1 ≤ 9) jucovicStar ≤ coveringRadius (by norm_num : 1 ≤ 9) q := by
  obtain ⟨p, hp⟩ := exists_optimal_covering (by norm_num : 1 ≤ 9)
  rw [coveringRadius_jucovicStar]
  exact (hT p (hW p hp)).trans (hp q)

end Geodesy.Spherical
