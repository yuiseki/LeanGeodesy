import LeanGeodesy.Spherical.NinePointReduce

/-!
# The elimination of `A₀, A₁, A₂`, formally

`TTPHarmonic` quantifies over 9 points and 14 strict supporting planes. This
file makes the elimination of the three equatorial points precise and proves

`ReducedHarmonic ↔ RelaxedHarmonic → TTPHarmonic → TTPOptimal`

(`reduced_iff_relaxed`, `TTPHarmonic_of_relaxed`, `TTPOptimal_of_reduced`).

## The relaxation (a sufficient condition, not an equivalence)

Every face other than the two triangles passes through exactly one equatorial
point `Aₖ` (`faceA`). `RelaxedFaceSupport` is `FaceSupport` without the
conditions "the other equatorial points `Aⱼ` are strictly inside a plane
through `Aₖ`" (`CrossA`). Strict support implies relaxed support, so
`RelaxedHarmonic → TTPHarmonic`; the converse is not claimed.

## The split (an equivalence)

After the relaxation every remaining condition involves at most one `Aₖ`.
`relaxed_iff` splits the relaxed conditions into
* `OuterFeasible`: the two triangle planes, with the six points `B`, `C`;
* `SubFeasible k`: the four faces through `Aₖ` (two slopes, two sides) with
  `Aₖ`, `B`, `C`, and `Aₖ` strictly inside the two triangle planes.

`SubFeasible k` depends only on `Aₖ`, `B`, `C`, the two triangle planes and
the four planes through `Aₖ` (`sub_congr`); `OuterFeasible` only on `B`, `C`
and the two triangle planes (`outer_congr`). The active sum is
`wT (1/d_T + 1/d_Bot) + wV Σₖ sideVal k` (`activeSum_eq`), where `sideVal k`
involves only the two sides through `Aₖ`.

`subValues k q N κ` is the set of values of `sideVal k` over all `Aₖ` and all
planes through `Aₖ` that are feasible for the `B`, `C` and triangle planes of
`(q, N, κ)`; `reducedObjective` replaces each `sideVal k` by the infimum of
this set. `ReducedHarmonic` asks `1/h⋆ ≤ reducedObjective` for every feasible
outer datum **whose three sets are nonempty**: if some set is empty the outer
datum belongs to no configuration and nothing is asked (this also keeps the
convention `sInf ∅ = 0` out of the statement). The sets are bounded below by
`0` (`subValues_nonneg`), so `sInf` is the true infimum, and no minimum is
assumed to exist.

`reducedObjective` depends only on `B`, `C` and the two triangle planes
(`reducedObjective_congr`). The planes of `Aₖ` are eliminated (they range
inside the infimum); the two triangle planes are not eliminated here. For
three distinct points of the sphere the plane through them is unique up to
positive scaling, so this is a statement about the six points `B`, `C`; that
uniqueness is not proved in Lean, and `ReducedHarmonic` quantifies over all
planes, which can only make it stronger.

## Sharpness

At Jucovič's configuration the active sum is `1/h⋆` (`activeSum_jucovicStar`),
so `reducedObjective ≤ 1/h⋆` there (`reducedObjective_jucovicStar_le`). The
reduced inequality is tight at Jucovič's `B`, `C` exactly when each of the
three subproblems is minimized by Jucovič's `Aₖ` (`JucovicSubMinimal`):
`JucovicSubMinimal → reducedObjective = 1/h⋆` there, and for `wV > 0`,
`ReducedHarmonic → JucovicSubMinimal`. `JucovicSubMinimal` is open.
-/

namespace Geodesy.Spherical

open Real

/-! ## The relaxation -/

/-- Face `f` passes through an equatorial point (`f ≥ 2`) and `i` is an
equatorial point: the condition "`i` is inside the plane of `f`" couples two
different `A`s, unless `i` is the vertex of `f`. -/
def CrossA (f : Fin 14) (i : Fin 9) : Prop := 2 ≤ f.val ∧ i.val < 3

instance (f : Fin 14) (i : Fin 9) : Decidable (CrossA f i) := by unfold CrossA; infer_instance

/-- `FaceSupport` without the cross-`A` conditions. -/
def RelaxedFaceSupport (q : Fin 9 → UnitSphere) (f : Fin 14) (N : E3) (κ : ℝ) : Prop :=
  0 < κ ∧ (∀ i, OnFace f i → inner ℝ N (q i).1 = κ) ∧
    ∀ i, ¬ OnFace f i → ¬ CrossA f i → inner ℝ N (q i).1 < κ

theorem FaceSupport.relaxed {q : Fin 9 → UnitSphere} {f : Fin 14} {N : E3} {κ : ℝ}
    (h : FaceSupport q f N κ) : RelaxedFaceSupport q f N κ :=
  ⟨h.1, h.2.1, fun i hi _ => h.2.2 i hi⟩

/-- The harmonic-mean inequality over the relaxed configurations (open). -/
def RelaxedHarmonic (wT wV : ℝ) : Prop :=
  ∀ q : Fin 9 → UnitSphere, ∀ (N : Fin 14 → E3) (κ : Fin 14 → ℝ),
    (∀ f, RelaxedFaceSupport q f (N f) (κ f)) → 1 / hStar ≤ activeSum wT wV N κ

/-- The relaxation is a sufficient condition. -/
theorem TTPHarmonic_of_relaxed {wT wV : ℝ} (h : RelaxedHarmonic wT wV) : TTPHarmonic wT wV :=
  fun q N κ hs => h q N κ (fun f => (hs f).relaxed)

/-! ## Combinatorics of the labelling -/

/-- The label of `Aₖ`. -/
def eqIdx (k : Fin 3) : Fin 9 := ⟨k.val, by omega⟩

/-- The equatorial point on face `f ≥ 2` (the value at `0`, `1` is unused). -/
def faceA : Fin 14 → Fin 3 := ![0, 0, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 2, 0]

/-- The two sides through `Aₖ`: `AₖBₖCₖ` and `AₖBₖ₋₁Cₖ₋₁`. -/
def sideOne : Fin 3 → Fin 14 := ![8, 9, 10]
def sideTwo : Fin 3 → Fin 14 := ![13, 11, 12]

theorem onFace_faceA : ∀ f : Fin 14, 2 ≤ f.val → OnFace f (eqIdx (faceA f)) := by decide

theorem faceA_of_onFace : ∀ (f : Fin 14) (k : Fin 3), OnFace f (eqIdx k) → 2 ≤ f.val ∧ faceA f = k := by
  decide

theorem onFace_ge_three_of_lt_two : ∀ (f : Fin 14) (i : Fin 9), f.val < 2 → OnFace f i → 3 ≤ i.val := by
  decide

theorem onFace_of_onFace_eqIdx : ∀ (f : Fin 14) (k : Fin 3) (i : Fin 9), OnFace f (eqIdx k) →
    OnFace f i → i = eqIdx k ∨ 3 ≤ i.val := by
  decide

theorem not_onFace_eqIdx_zero : ∀ k : Fin 3, ¬ OnFace 0 (eqIdx k) := by decide
theorem not_onFace_eqIdx_one : ∀ k : Fin 3, ¬ OnFace 1 (eqIdx k) := by decide

theorem sideOne_spec : ∀ k : Fin 3, OnFace (sideOne k) (eqIdx k) ∧ 2 ≤ (sideOne k).val ∧
    faceA (sideOne k) = k := by decide
theorem sideTwo_spec : ∀ k : Fin 3, OnFace (sideTwo k) (eqIdx k) ∧ 2 ≤ (sideTwo k).val ∧
    faceA (sideTwo k) = k := by decide

/-! ## The split -/

/-- The part of `activeSum` that involves `Aₖ`: its two sides. -/
noncomputable def sideVal (k : Fin 3) (N : Fin 14 → E3) (κ : Fin 14 → ℝ) : ℝ :=
  ‖N (sideOne k)‖ / κ (sideOne k) + ‖N (sideTwo k)‖ / κ (sideTwo k)

theorem activeSum_eq (wT wV : ℝ) (N : Fin 14 → E3) (κ : Fin 14 → ℝ) :
    activeSum wT wV N κ = wT * (‖N 0‖ / κ 0 + ‖N 1‖ / κ 1) + wV * ∑ k, sideVal k N κ := by
  simp only [activeSum, sideVal, Fin.sum_univ_three, sideOne, sideTwo]
  simp
  ring

/-- The conditions that involve no equatorial point: the two triangle planes,
with the six points `B`, `C`. -/
def OuterFeasible (q : Fin 9 → UnitSphere) (N : Fin 14 → E3) (κ : Fin 14 → ℝ) : Prop :=
  ∀ f : Fin 14, f.val < 2 → 0 < κ f ∧ (∀ i, OnFace f i → inner ℝ (N f) (q i).1 = κ f) ∧
    ∀ i, ¬ OnFace f i → 3 ≤ i.val → inner ℝ (N f) (q i).1 < κ f

/-- The conditions that involve `Aₖ`: the four faces through it, and `Aₖ`
strictly inside the two triangle planes. -/
def SubFeasible (k : Fin 3) (q : Fin 9 → UnitSphere) (N : Fin 14 → E3) (κ : Fin 14 → ℝ) : Prop :=
  (∀ f, OnFace f (eqIdx k) → RelaxedFaceSupport q f (N f) (κ f)) ∧
    inner ℝ (N 0) (q (eqIdx k)).1 < κ 0 ∧ inner ℝ (N 1) (q (eqIdx k)).1 < κ 1

private theorem fin14_lt_two {f : Fin 14} (hf : f.val < 2) : f = 0 ∨ f = 1 := by
  rcases (show f.val = 0 ∨ f.val = 1 by omega) with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- The relaxed conditions are exactly the outer ones together with the three
independent subproblems. -/
theorem relaxed_iff {q : Fin 9 → UnitSphere} {N : Fin 14 → E3} {κ : Fin 14 → ℝ} :
    (∀ f, RelaxedFaceSupport q f (N f) (κ f)) ↔
      OuterFeasible q N κ ∧ ∀ k, SubFeasible k q N κ := by
  constructor
  · intro h
    refine ⟨fun f hf => ⟨(h f).1, (h f).2.1, fun i hi _ => (h f).2.2 i hi ?_⟩, fun k =>
      ⟨fun f _ => h f, (h 0).2.2 _ (not_onFace_eqIdx_zero k) (by simp [CrossA]),
        (h 1).2.2 _ (not_onFace_eqIdx_one k) (by simp [CrossA])⟩⟩
    simp [CrossA]; omega
  · rintro ⟨ho, hs⟩ f
    by_cases hf : f.val < 2
    · obtain ⟨h0, h1, h2⟩ := ho f hf
      refine ⟨h0, h1, fun i hi _ => ?_⟩
      by_cases h3 : 3 ≤ i.val
      · exact h2 i hi h3
      · have hi' : i = eqIdx ⟨i.val, by omega⟩ := Fin.ext rfl
        rw [hi']
        rcases fin14_lt_two hf with rfl | rfl
        · exact (hs _).2.1
        · exact (hs _).2.2
    · exact (hs (faceA f)).1 f (onFace_faceA f (by omega))

/-- `OuterFeasible` depends only on `B`, `C` and the two triangle planes. -/
theorem outer_congr {q q' : Fin 9 → UnitSphere} {N N' : Fin 14 → E3} {κ κ' : Fin 14 → ℝ}
    (hq : ∀ i : Fin 9, 3 ≤ i.val → q' i = q i) (hN0 : N' 0 = N 0) (hN1 : N' 1 = N 1)
    (hκ0 : κ' 0 = κ 0) (hκ1 : κ' 1 = κ 1) (h : OuterFeasible q N κ) : OuterFeasible q' N' κ' := by
  intro f hf
  rcases fin14_lt_two hf with rfl | rfl
  · obtain ⟨h0, h1, h2⟩ := h 0 hf
    refine ⟨by rw [hκ0]; exact h0, fun i hi => ?_, fun i hi h3 => ?_⟩
    · rw [hN0, hκ0, hq i (onFace_ge_three_of_lt_two 0 i hf hi)]; exact h1 i hi
    · rw [hN0, hκ0, hq i h3]; exact h2 i hi h3
  · obtain ⟨h0, h1, h2⟩ := h 1 hf
    refine ⟨by rw [hκ1]; exact h0, fun i hi => ?_, fun i hi h3 => ?_⟩
    · rw [hN1, hκ1, hq i (onFace_ge_three_of_lt_two 1 i hf hi)]; exact h1 i hi
    · rw [hN1, hκ1, hq i h3]; exact h2 i hi h3

/-- `SubFeasible k` depends only on `Aₖ`, `B`, `C`, the two triangle planes and
the planes of the faces through `Aₖ`. -/
theorem sub_congr (k : Fin 3) {q q' : Fin 9 → UnitSphere} {N N' : Fin 14 → E3}
    {κ κ' : Fin 14 → ℝ} (hA : q' (eqIdx k) = q (eqIdx k)) (hq : ∀ i : Fin 9, 3 ≤ i.val → q' i = q i)
    (hN : ∀ f, OnFace f (eqIdx k) → N' f = N f ∧ κ' f = κ f) (hN0 : N' 0 = N 0) (hN1 : N' 1 = N 1)
    (hκ0 : κ' 0 = κ 0) (hκ1 : κ' 1 = κ 1) (h : SubFeasible k q N κ) : SubFeasible k q' N' κ' := by
  obtain ⟨hf, h0, h1⟩ := h
  refine ⟨fun f hfk => ?_, by rw [hN0, hκ0, hA]; exact h0, by rw [hN1, hκ1, hA]; exact h1⟩
  obtain ⟨hNf, hκf⟩ := hN f hfk
  obtain ⟨a0, a1, a2⟩ := hf f hfk
  have hf2 := (faceA_of_onFace f k hfk).1
  refine ⟨by rw [hκf]; exact a0, fun i hi => ?_, fun i hi hc => ?_⟩
  · rw [hNf, hκf]
    rcases onFace_of_onFace_eqIdx f k i hfk hi with rfl | h3
    · rw [hA]; exact a1 _ hi
    · rw [hq i h3]; exact a1 i hi
  · have h3 : 3 ≤ i.val := by simp [CrossA] at hc; omega
    rw [hNf, hκf, hq i h3]; exact a2 i hi hc

/-- Every feasible point of the `k`-th subproblem obeys the two-plane bound,
with `c` the cosine between the two side normals (which still depends on the
planes, so this does not by itself eliminate them). -/
theorem sideVal_bound {k : Fin 3} {q : Fin 9 → UnitSphere} {N : Fin 14 → E3} {κ : Fin 14 → ℝ}
    (h : SubFeasible k q N κ) :
    8 ≤ (1 + inner ℝ (N (sideOne k)) (N (sideTwo k)) / (‖N (sideOne k)‖ * ‖N (sideTwo k)‖)) *
      sideVal k N κ ^ 2 := by
  obtain ⟨a0, a1, -⟩ := h.1 _ (sideOne_spec k).1
  obtain ⟨b0, b1, -⟩ := h.1 _ (sideTwo_spec k).1
  exact face_pair_bound (q (eqIdx k)) a0 b0 (a1 _ (sideOne_spec k).1) (b1 _ (sideTwo_spec k).1)

/-! ## The reduced inequality -/

/-- The values of `sideVal k` over all `Aₖ` and planes through `Aₖ` that are
feasible for the `B`, `C` and triangle planes of `(q, N, κ)`. -/
def subValues (k : Fin 3) (q : Fin 9 → UnitSphere) (N : Fin 14 → E3) (κ : Fin 14 → ℝ) : Set ℝ :=
  {v | ∃ (q' : Fin 9 → UnitSphere) (N' : Fin 14 → E3) (κ' : Fin 14 → ℝ),
    (∀ i : Fin 9, 3 ≤ i.val → q' i = q i) ∧ N' 0 = N 0 ∧ N' 1 = N 1 ∧ κ' 0 = κ 0 ∧ κ' 1 = κ 1 ∧
      SubFeasible k q' N' κ' ∧ v = sideVal k N' κ'}

/-- The reduced objective: the triangle terms, and for each `Aₖ` the infimum
of its subproblem. -/
noncomputable def reducedObjective (wT wV : ℝ) (q : Fin 9 → UnitSphere) (N : Fin 14 → E3)
    (κ : Fin 14 → ℝ) : ℝ :=
  wT * (‖N 0‖ / κ 0 + ‖N 1‖ / κ 1) + wV * ∑ k, sInf (subValues k q N κ)

/-- The reduced inequality (open): for every feasible outer datum whose three
subproblems are feasible. -/
def ReducedHarmonic (wT wV : ℝ) : Prop :=
  ∀ q : Fin 9 → UnitSphere, ∀ (N : Fin 14 → E3) (κ : Fin 14 → ℝ),
    OuterFeasible q N κ → (∀ k, (subValues k q N κ).Nonempty) →
      1 / hStar ≤ reducedObjective wT wV q N κ

theorem sideVal_nonneg {k : Fin 3} {q : Fin 9 → UnitSphere} {N : Fin 14 → E3} {κ : Fin 14 → ℝ}
    (h : SubFeasible k q N κ) : 0 ≤ sideVal k N κ := by
  have h1 := (h.1 _ (sideOne_spec k).1).1
  have h2 := (h.1 _ (sideTwo_spec k).1).1
  unfold sideVal; positivity

theorem subValues_nonneg {k : Fin 3} {q : Fin 9 → UnitSphere} {N : Fin 14 → E3}
    {κ : Fin 14 → ℝ} {v : ℝ} (hv : v ∈ subValues k q N κ) : 0 ≤ v := by
  obtain ⟨_, _, _, _, _, _, _, _, hs, rfl⟩ := hv
  exact sideVal_nonneg hs

theorem subValues_bddBelow (k : Fin 3) (q : Fin 9 → UnitSphere) (N : Fin 14 → E3)
    (κ : Fin 14 → ℝ) : BddBelow (subValues k q N κ) :=
  ⟨0, fun _ hv => subValues_nonneg hv⟩

/-- The subproblem sets depend only on `B`, `C` and the two triangle planes. -/
theorem subValues_congr (k : Fin 3) {q q' : Fin 9 → UnitSphere} {N N' : Fin 14 → E3}
    {κ κ' : Fin 14 → ℝ} (hq : ∀ i : Fin 9, 3 ≤ i.val → q' i = q i) (hN0 : N' 0 = N 0)
    (hN1 : N' 1 = N 1) (hκ0 : κ' 0 = κ 0) (hκ1 : κ' 1 = κ 1) :
    subValues k q' N' κ' = subValues k q N κ := by
  ext v
  constructor
  · rintro ⟨Q, M, K, hQ, hM0, hM1, hK0, hK1, hs, rfl⟩
    exact ⟨Q, M, K, fun i h => (hQ i h).trans (hq i h), hM0.trans hN0, hM1.trans hN1,
      hK0.trans hκ0, hK1.trans hκ1, hs, rfl⟩
  · rintro ⟨Q, M, K, hQ, hM0, hM1, hK0, hK1, hs, rfl⟩
    exact ⟨Q, M, K, fun i h => (hQ i h).trans (hq i h).symm, hM0.trans hN0.symm,
      hM1.trans hN1.symm, hK0.trans hκ0.symm, hK1.trans hκ1.symm, hs, rfl⟩

/-- The reduced objective depends only on `B`, `C` and the two triangle planes. -/
theorem reducedObjective_congr (wT wV : ℝ) {q q' : Fin 9 → UnitSphere} {N N' : Fin 14 → E3}
    {κ κ' : Fin 14 → ℝ} (hq : ∀ i : Fin 9, 3 ≤ i.val → q' i = q i) (hN0 : N' 0 = N 0)
    (hN1 : N' 1 = N 1) (hκ0 : κ' 0 = κ 0) (hκ1 : κ' 1 = κ 1) :
    reducedObjective wT wV q' N' κ' = reducedObjective wT wV q N κ := by
  simp only [reducedObjective, hN0, hN1, hκ0, hκ1, subValues_congr _ hq hN0 hN1 hκ0 hκ1]

/-- On a relaxed configuration, the reduced objective is at most the active sum. -/
theorem reducedObjective_le_activeSum {wT wV : ℝ} (hV : 0 ≤ wV) {q : Fin 9 → UnitSphere}
    {N : Fin 14 → E3} {κ : Fin 14 → ℝ} (hs : ∀ k, SubFeasible k q N κ) :
    reducedObjective wT wV q N κ ≤ activeSum wT wV N κ := by
  have mem : ∀ k, sideVal k N κ ∈ subValues k q N κ :=
    fun k => ⟨q, N, κ, fun _ _ => rfl, rfl, rfl, rfl, rfl, hs k, rfl⟩
  have hle : ∑ k, sInf (subValues k q N κ) ≤ ∑ k, sideVal k N κ :=
    Finset.sum_le_sum fun k _ => csInf_le (subValues_bddBelow k q N κ) (mem k)
  rw [activeSum_eq, reducedObjective]
  have := mul_le_mul_of_nonneg_left hle hV
  linarith

/-- The reduced inequality implies the relaxed one. -/
theorem relaxed_of_reduced {wT wV : ℝ} (hV : 0 ≤ wV) (hR : ReducedHarmonic wT wV) :
    RelaxedHarmonic wT wV := by
  intro q N κ h
  obtain ⟨ho, hs⟩ := relaxed_iff.1 h
  have mem : ∀ k, sideVal k N κ ∈ subValues k q N κ :=
    fun k => ⟨q, N, κ, fun _ _ => rfl, rfl, rfl, rfl, rfl, hs k, rfl⟩
  exact (hR q N κ ho fun k => ⟨_, mem k⟩).trans (reducedObjective_le_activeSum hV hs)

/-- The relaxed inequality implies the reduced one: the split loses nothing. -/
theorem reduced_of_relaxed {wT wV : ℝ} (hV : 0 ≤ wV) (hH : RelaxedHarmonic wT wV) :
    ReducedHarmonic wT wV := by
  intro q N κ ho hne
  by_contra hlt
  push Not at hlt
  set R := reducedObjective wT wV q N κ with hRdef
  set δ := 1 / hStar - R
  have hδ : 0 < δ := by simp only [δ]; linarith
  set ε := δ / (3 * wV + 1)
  have hε : 0 < ε := div_pos hδ (by linarith)
  have hpick : ∀ k, ∃ v ∈ subValues k q N κ, v < sInf (subValues k q N κ) + ε :=
    fun k => Real.lt_sInf_add_pos (hne k) hε
  choose v hv hvlt using hpick
  choose Q NN KK hQ hN0 hN1 hK0 hK1 hSub hval using hv
  let q'' : Fin 9 → UnitSphere := fun i => if h : i.val < 3 then Q ⟨i.val, h⟩ i else q i
  let N'' : Fin 14 → E3 := fun f => if f.val < 2 then N f else NN (faceA f) f
  let κ'' : Fin 14 → ℝ := fun f => if f.val < 2 then κ f else KK (faceA f) f
  have hq3 : ∀ i : Fin 9, 3 ≤ i.val → q'' i = q i := fun i h => by
    simp [q'', show ¬ i.val < 3 by omega]
  have hN''0 : N'' 0 = N 0 := by simp [N'']
  have hN''1 : N'' 1 = N 1 := by simp [N'']
  have hκ''0 : κ'' 0 = κ 0 := by simp [κ'']
  have hκ''1 : κ'' 1 = κ 1 := by simp [κ'']
  have hfaces : ∀ k f, OnFace f (eqIdx k) → N'' f = NN k f ∧ κ'' f = KK k f := by
    intro k f hf
    obtain ⟨h2, hk⟩ := faceA_of_onFace f k hf
    have hn : ¬ f.val < 2 := by omega
    subst hk
    exact ⟨ite_eq_right_of_eq_false _ _ (eq_false hn), ite_eq_right_of_eq_false _ _ (eq_false hn)⟩
  have hrel : ∀ f, RelaxedFaceSupport q'' f (N'' f) (κ'' f) := by
    refine relaxed_iff.2 ⟨outer_congr hq3 hN''0 hN''1 hκ''0 hκ''1 ho, fun k => ?_⟩
    refine sub_congr k (q := Q k) (N := NN k) (κ := KK k) ?_ ?_ (hfaces k) ?_ ?_ ?_ ?_ (hSub k)
    · simp [q'', eqIdx]
    · intro i h; rw [hq3 i h, hQ k i h]
    · rw [hN''0, hN0 k]
    · rw [hN''1, hN1 k]
    · rw [hκ''0, hK0 k]
    · rw [hκ''1, hK1 k]
  have hsv : ∀ k, sideVal k N'' κ'' = v k := by
    intro k
    rw [hval k]
    obtain ⟨a1, b1⟩ := hfaces k _ (sideOne_spec k).1
    obtain ⟨a2, b2⟩ := hfaces k _ (sideTwo_spec k).1
    simp only [sideVal, a1, b1, a2, b2]
  have key := hH q'' N'' κ'' hrel
  rw [activeSum_eq, hN''0, hN''1, hκ''0, hκ''1] at key
  simp only [hsv] at key
  have hsum : ∑ k, v k ≤ ∑ k, sInf (subValues k q N κ) + 3 * ε := by
    have : ∑ k, v k ≤ ∑ k, (sInf (subValues k q N κ) + ε) :=
      Finset.sum_le_sum fun k _ => (hvlt k).le
    simpa [Finset.sum_add_distrib, mul_comm] using this
  have h3 : wV * (3 * ε) < δ := by
    have : wV * (3 * ε) = δ * (3 * wV / (3 * wV + 1)) := by
      simp only [ε]; field_simp
    rw [this]
    have : 3 * wV / (3 * wV + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  have := mul_le_mul_of_nonneg_left hsum hV
  simp only [δ, hRdef, reducedObjective] at h3
  nlinarith

/-- The split is an equivalence. -/
theorem reduced_iff_relaxed {wT wV : ℝ} (hV : 0 ≤ wV) :
    ReducedHarmonic wT wV ↔ RelaxedHarmonic wT wV :=
  ⟨relaxed_of_reduced hV, reduced_of_relaxed hV⟩

/-- The chain `ReducedHarmonic → RelaxedHarmonic → TTPHarmonic → TTPOptimal`. -/
theorem TTPOptimal_of_reduced {wT wV : ℝ} (hT : 0 ≤ wT) (hV : 0 ≤ wV) (hsum : 2 * wT + 6 * wV = 1)
    (hR : ReducedHarmonic wT wV) : TTPOptimal :=
  TTPOptimal_of_harmonic hT hV hsum (TTPHarmonic_of_relaxed (relaxed_of_reduced hV hR))

/-! ## Sharpness at Jucovič's configuration -/

theorem jucovic_relaxed (f : Fin 14) :
    RelaxedFaceSupport jucovicStar f (jucovicFaceNormal tStar hStar f)
      (jucovicFaceOffset tStar hStar f) := (jucovic_faceSupport f).relaxed

theorem jucovic_subFeasible (k : Fin 3) :
    SubFeasible k jucovicStar (jucovicFaceNormal tStar hStar) (jucovicFaceOffset tStar hStar) :=
  (relaxed_iff.1 jucovic_relaxed).2 k

theorem jucovic_outerFeasible :
    OuterFeasible jucovicStar (jucovicFaceNormal tStar hStar) (jucovicFaceOffset tStar hStar) :=
  (relaxed_iff.1 jucovic_relaxed).1

/-- At Jucovič's configuration both sides through `Aₖ` are at distance `h⋆`. -/
theorem sideVal_jucovicStar (k : Fin 3) :
    sideVal k (jucovicFaceNormal tStar hStar) (jucovicFaceOffset tStar hStar) = 2 / hStar := by
  have hps := hStar_pos
  have e : ∀ f : Fin 14, 8 ≤ f.val →
      ‖jucovicFaceNormal tStar hStar f‖ / jucovicFaceOffset tStar hStar f = 1 / hStar := by
    intro f hf
    have h := jucovic_active_dist f (Or.inr hf)
    have hk := (jucovic_faceSupport f).1
    rw [div_eq_div_iff hk.ne' hps.ne', ← h]; ring
  have h1 : 8 ≤ (sideOne k).val := by fin_cases k <;> decide
  have h2 : 8 ≤ (sideTwo k).val := by fin_cases k <;> decide
  rw [sideVal, e _ h1, e _ h2]; ring

/-- The reduced objective at Jucovič's `B`, `C` is at most `1/h⋆`. -/
theorem reducedObjective_jucovicStar_le {wT wV : ℝ} (hV : 0 ≤ wV) (hsum : 2 * wT + 6 * wV = 1) :
    reducedObjective wT wV jucovicStar (jucovicFaceNormal tStar hStar)
      (jucovicFaceOffset tStar hStar) ≤ 1 / hStar :=
  (reducedObjective_le_activeSum hV jucovic_subFeasible).trans (activeSum_jucovicStar hsum).le

/-- Jucovič's `Aₖ` minimizes each subproblem for Jucovič's `B`, `C` (open). -/
def JucovicSubMinimal : Prop :=
  ∀ k : Fin 3, ∀ v ∈ subValues k jucovicStar (jucovicFaceNormal tStar hStar)
    (jucovicFaceOffset tStar hStar), 2 / hStar ≤ v

/-- If the subproblems are minimized at Jucovič's `Aₖ`, the reduced objective
equals `1/h⋆` at Jucovič's `B`, `C`. -/
theorem reducedObjective_jucovicStar_eq {wT wV : ℝ} (hsum : 2 * wT + 6 * wV = 1)
    (hm : JucovicSubMinimal) :
    reducedObjective wT wV jucovicStar (jucovicFaceNormal tStar hStar)
      (jucovicFaceOffset tStar hStar) = 1 / hStar := by
  have hps := hStar_pos
  have hinf : ∀ k, sInf (subValues k jucovicStar (jucovicFaceNormal tStar hStar)
      (jucovicFaceOffset tStar hStar)) = 2 / hStar := by
    intro k
    have mem : 2 / hStar ∈ subValues k jucovicStar (jucovicFaceNormal tStar hStar)
        (jucovicFaceOffset tStar hStar) :=
      ⟨_, _, _, fun _ _ => rfl, rfl, rfl, rfl, rfl, jucovic_subFeasible k,
        (sideVal_jucovicStar k).symm⟩
    exact le_antisymm (csInf_le (subValues_bddBelow _ _ _ _) mem) (le_csInf ⟨_, mem⟩ (hm k))
  have e0 := sideVal_jucovicStar 0
  have h0 : ‖jucovicFaceNormal tStar hStar 0‖ / jucovicFaceOffset tStar hStar 0 = 1 / hStar := by
    have h := jucovic_active_dist 0 (Or.inl (by decide))
    have hk := (jucovic_faceSupport 0).1
    rw [div_eq_div_iff hk.ne' hps.ne', ← h]; ring
  have h1 : ‖jucovicFaceNormal tStar hStar 1‖ / jucovicFaceOffset tStar hStar 1 = 1 / hStar := by
    have h := jucovic_active_dist 1 (Or.inl (by decide))
    have hk := (jucovic_faceSupport 1).1
    rw [div_eq_div_iff hk.ne' hps.ne', ← h]; ring
  simp only [reducedObjective, h0, h1, hinf, Fin.sum_univ_three]
  field_simp
  linear_combination hsum

/-- With `wV > 0`, the reduced inequality contains, at Jucovič's `B`, `C`, the
three subproblem minimality statements. -/
theorem jucovicSubMinimal_of_reduced {wT wV : ℝ} (hV : 0 < wV) (hsum : 2 * wT + 6 * wV = 1)
    (hR : ReducedHarmonic wT wV) : JucovicSubMinimal := by
  have hps := hStar_pos
  set S := fun k => subValues k jucovicStar (jucovicFaceNormal tStar hStar)
    (jucovicFaceOffset tStar hStar)
  have mem : ∀ k, 2 / hStar ∈ S k := fun k =>
    ⟨_, _, _, fun _ _ => rfl, rfl, rfl, rfl, rfl, jucovic_subFeasible k,
      (sideVal_jucovicStar k).symm⟩
  have hle : ∀ k, sInf (S k) ≤ 2 / hStar := fun k => csInf_le (subValues_bddBelow _ _ _ _) (mem k)
  have hge := hR _ _ _ jucovic_outerFeasible (fun k => ⟨_, mem k⟩)
  have h0 : ‖jucovicFaceNormal tStar hStar 0‖ / jucovicFaceOffset tStar hStar 0 = 1 / hStar := by
    have h := jucovic_active_dist 0 (Or.inl (by decide))
    have hk := (jucovic_faceSupport 0).1
    rw [div_eq_div_iff hk.ne' hps.ne', ← h]; ring
  have h1 : ‖jucovicFaceNormal tStar hStar 1‖ / jucovicFaceOffset tStar hStar 1 = 1 / hStar := by
    have h := jucovic_active_dist 1 (Or.inl (by decide))
    have hk := (jucovic_faceSupport 1).1
    rw [div_eq_div_iff hk.ne' hps.ne', ← h]; ring
  simp only [reducedObjective, h0, h1, Fin.sum_univ_three] at hge
  intro k v hv
  -- every infimum is at most `2/h⋆` and their weighted sum is at least `6/h⋆`, so all equal `2/h⋆`
  have hk : 2 / hStar ≤ sInf (S k) := by
    have a0 := hle 0; have a1 := hle 1; have a2 := hle 2
    have hw : wT * (1 / hStar + 1 / hStar) + wV * (2 / hStar + 2 / hStar + 2 / hStar) = 1 / hStar := by
      field_simp; linear_combination hsum
    fin_cases k
    · show 2 / hStar ≤ sInf (S 0); nlinarith
    · show 2 / hStar ≤ sInf (S 1); nlinarith
    · show 2 / hStar ≤ sInf (S 2); nlinarith
  exact hk.trans (csInf_le (subValues_bddBelow _ _ _ _) hv)

end Geodesy.Spherical
