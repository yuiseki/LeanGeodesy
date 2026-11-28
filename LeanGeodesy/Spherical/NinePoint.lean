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
`⟪N, ·⟫ = κ` with `κ > 0` (the origin strictly inside) that has the six other
points strictly inside (`FaceSupport`). `IsTTP p` allows any relabelling.

What follows from this, in Lean: the nine points are distinct
(`IsTTPSupported.injective`), so each labelled triangle has three distinct
vertices of the sphere, which are never collinear (`unit_collinear`); the
normals are nonzero and each face distance `κ / ‖N‖` is in `(0, 1]`
(`FaceSupport.dist_mem`); distinct faces lie in distinct planes
(`FaceSupport.separated`). The definition is invariant under positive scaling
of the planes, under maps preserving inner products, and (`IsTTP`) under
relabelling (`faceSupport_smul`, `faceSupport_map`, `isTTP_comp_perm`).

What is argued but not proved in Lean: the definition holds exactly when the
convex hull is a simplicial polytope whose faces are the 14 labelled
triangles and which contains the origin in its interior. (If the hull has
these facets, their planes are strict supporting planes. Conversely, 14
distinct facets with exactly three points each, on at most 9 vertices, are
all the facets, since a 3-polytope has at most `2V - 4` facets.) Only the
supporting-plane form is used.

(Correction, 2026-11-28: until commit `705f459` the support was non-strict,
`⟪N, q i⟫ ≤ κ` for every point. Then all fourteen planes may coincide, and
`TTPHarmonic` was false; see `Spherical/NinePointAudit.lean`.)

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

/-- Vertex `i` is one of the three vertices of face `f` (labelling of
`jucovicFaceVerts`). -/
def OnFace (f : Fin 14) (i : Fin 9) : Prop :=
  i = (jucovicFaceVerts f).1 ∨ i = (jucovicFaceVerts f).2.1 ∨ i = (jucovicFaceVerts f).2.2

instance (f : Fin 14) (i : Fin 9) : Decidable (OnFace f i) := by unfold OnFace; infer_instance

/-- The plane `⟪N, ·⟫ = κ` is a strict supporting plane of face `f` of `q`: the
origin is strictly inside (`κ > 0`), the three vertices of `f` are on the plane,
and the six other points are strictly inside.

(Correction, 2026-11-28: the versions of commits `504e62a` and `bf906c0`
asked only `⟪N, q i⟫ ≤ κ` for every point, and were false; see
`Spherical/NinePointAudit.lean`.) -/
def FaceSupport (q : Fin 9 → UnitSphere) (f : Fin 14) (N : E3) (κ : ℝ) : Prop :=
  0 < κ ∧ (∀ i, OnFace f i → inner ℝ N (q i).1 = κ) ∧
    ∀ i, ¬ OnFace f i → inner ℝ N (q i).1 < κ

/-- Each of the 14 labelled triangles has a strict supporting plane with the
origin strictly inside. -/
def IsTTPSupported (q : Fin 9 → UnitSphere) : Prop :=
  ∀ f : Fin 14, ∃ N : E3, ∃ κ : ℝ, FaceSupport q f N κ

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

/-- The weighted sum of the reciprocal distances `‖N f‖ / κ f` of the eight faces
that are active at Jucovič's configuration: the two triangles with weight `wT`,
the six sides with weight `wV`. -/
noncomputable def activeSum (wT wV : ℝ) (N : Fin 14 → E3) (κ : Fin 14 → ℝ) : ℝ :=
  wT * ‖N 0‖ / κ 0 + wT * ‖N 1‖ / κ 1 + wV * ‖N 8‖ / κ 8 + wV * ‖N 9‖ / κ 9 +
    wV * ‖N 10‖ / κ 10 + wV * ‖N 11‖ / κ 11 + wV * ‖N 12‖ / κ 12 + wV * ‖N 13‖ / κ 13

/-- The weighted harmonic-mean inequality over the eight active faces, for every
configuration and every choice of strict supporting planes of its fourteen
labelled faces (open). -/
def TTPHarmonic (wT wV : ℝ) : Prop :=
  ∀ q : Fin 9 → UnitSphere, ∀ (N : Fin 14 → E3) (κ : Fin 14 → ℝ),
    (∀ f, FaceSupport q f (N f) (κ f)) → 1 / hStar ≤ activeSum wT wV N κ

/-! ## What the definition implies -/

theorem FaceSupport.le {q : Fin 9 → UnitSphere} {f : Fin 14} {N : E3} {κ : ℝ}
    (h : FaceSupport q f N κ) (i : Fin 9) : inner ℝ N (q i).1 ≤ κ := by
  by_cases hi : OnFace f i
  · exact (h.2.1 i hi).le
  · exact (h.2.2 i hi).le

/-- The offset is at most the norm of the normal (Cauchy–Schwarz on a vertex). -/
theorem FaceSupport.offset_le_norm {q : Fin 9 → UnitSphere} {f : Fin 14} {N : E3} {κ : ℝ}
    (h : FaceSupport q f N κ) : κ ≤ ‖N‖ := by
  have hv := h.2.1 _ (Or.inl rfl : OnFace f (jucovicFaceVerts f).1)
  have := real_inner_le_norm N (q (jucovicFaceVerts f).1).1
  rw [(q _).2, mul_one] at this
  linarith

theorem FaceSupport.norm_pos {q : Fin 9 → UnitSphere} {f : Fin 14} {N : E3} {κ : ℝ}
    (h : FaceSupport q f N κ) : 0 < ‖N‖ := lt_of_lt_of_le h.1 h.offset_le_norm

/-- The distance `κ / ‖N‖` of a face plane is in `(0, 1]`. -/
theorem FaceSupport.dist_mem {q : Fin 9 → UnitSphere} {f : Fin 14} {N : E3} {κ : ℝ}
    (h : FaceSupport q f N κ) : 0 < κ / ‖N‖ ∧ κ / ‖N‖ ≤ 1 :=
  ⟨div_pos h.1 h.norm_pos, (div_le_one h.norm_pos).2 h.offset_le_norm⟩

/-- Any two labels are separated by a face: some face contains the first and not
the second. -/
theorem exists_face_separating : ∀ i j : Fin 9, i ≠ j → ∃ f, OnFace f i ∧ ¬ OnFace f j := by
  decide

/-- Any two faces are separated by a vertex. -/
theorem exists_vertex_separating : ∀ f g : Fin 14, f ≠ g → ∃ i, OnFace f i ∧ ¬ OnFace g i := by
  decide

/-- Strict support forces the nine points to be distinct. -/
theorem IsTTPSupported.injective {q : Fin 9 → UnitSphere} (h : IsTTPSupported q) :
    Function.Injective q := by
  intro i j hij
  by_contra hne
  obtain ⟨f, hi, hj⟩ := exists_face_separating i j hne
  obtain ⟨N, κ, hs⟩ := h f
  have e1 := hs.2.1 i hi
  have e2 := hs.2.2 j hj
  rw [hij] at e1
  linarith

/-- Strict support forces distinct faces to lie in distinct planes: a vertex of
one is strictly inside the other. -/
theorem FaceSupport.separated {q : Fin 9 → UnitSphere} {f g : Fin 14} (hfg : f ≠ g) {N N' : E3}
    {κ κ' : ℝ} (hf : FaceSupport q f N κ) (hg : FaceSupport q g N' κ') :
    ∃ i, inner ℝ N (q i).1 = κ ∧ inner ℝ N' (q i).1 < κ' := by
  obtain ⟨i, hi, hi'⟩ := exists_vertex_separating f g hfg
  exact ⟨i, hf.2.1 i hi, hg.2.2 i hi'⟩

/-- Three distinct points of the sphere are never collinear: if
`a + s (b - a)` is a unit vector, `a ≠ b` unit vectors, then `s = 0` or `s = 1`. -/
theorem unit_collinear {a b : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) {s : ℝ}
    (hs : ‖a + s • (b - a)‖ = 1) : s = 0 ∨ s = 1 := by
  have hd : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hab.symm)
  have e : ‖a + s • (b - a)‖ ^ 2 = 1 + s * (s - 1) * ‖b - a‖ ^ 2 := by
    rw [@norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs,
      ha]
    have : inner ℝ a (b - a) = -(‖b - a‖ ^ 2) / 2 := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq, ha]
      have := @norm_sub_sq_real _ _ _ b a
      rw [ha, hb] at this
      have hba : inner ℝ b a = inner ℝ a b := real_inner_comm _ _
      linarith
    rw [this]; ring
  rw [hs] at e
  have : s * (s - 1) = 0 := by
    have hd2 : 0 < ‖b - a‖ ^ 2 := by positivity
    nlinarith
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-! ## Invariance -/

/-- Positive scaling of a plane does not change support or reciprocal distance. -/
theorem faceSupport_smul {q : Fin 9 → UnitSphere} {f : Fin 14} {N : E3} {κ s : ℝ} (hs : 0 < s) :
    FaceSupport q f (s • N) (s * κ) ↔ FaceSupport q f N κ := by
  simp only [FaceSupport, real_inner_smul_left]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨pos_of_mul_pos_right h0 hs.le, fun i hi => ?_, fun i hi => ?_⟩
    · exact mul_left_cancel₀ hs.ne' (h1 i hi)
    · exact lt_of_mul_lt_mul_left (h2 i hi) hs.le
  · rintro ⟨h0, h1, h2⟩
    exact ⟨mul_pos hs h0, fun i hi => by rw [h1 i hi], fun i hi => mul_lt_mul_of_pos_left (h2 i hi) hs⟩

theorem norm_smul_div_mul {N : E3} {κ s : ℝ} (hs : 0 < s) : ‖s • N‖ / (s * κ) = ‖N‖ / κ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_div_mul_left _ _ hs.ne']

/-- A map preserving inner products (a rotation or reflection) carries strict
supporting planes to strict supporting planes. -/
theorem faceSupport_map {g : E3 → E3} (hg : ∀ a b, inner ℝ (g a) (g b) = inner ℝ a b)
    {q q' : Fin 9 → UnitSphere} (hq : ∀ i, (q' i).1 = g (q i).1) {f : Fin 14} {N : E3} {κ : ℝ} :
    FaceSupport q' f (g N) κ ↔ FaceSupport q f N κ := by
  simp only [FaceSupport, hq, hg]

theorem norm_map_of_inner {g : E3 → E3} (hg : ∀ a b, inner ℝ (g a) (g b) = inner ℝ a b) (v : E3) :
    ‖g v‖ = ‖v‖ := by
  have h := hg v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The type does not depend on the labelling. -/
theorem isTTP_comp_perm (p : Fin 9 → UnitSphere) (τ : Equiv.Perm (Fin 9)) :
    IsTTP (p ∘ τ) ↔ IsTTP p := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨τ * σ, by
      simpa [Function.comp_def, Equiv.Perm.mul_apply] using hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨τ⁻¹ * σ, by simpa [Function.comp_def, Equiv.Perm.mul_apply] using hσ⟩

/-! ## Jucovič's configuration has the type -/

set_option maxHeartbeats 4000000 in
/-- For `1/2 < t < 1` every face plane of `jucovicVec t h` has the six points
off the face strictly inside. -/
theorem jucovic_face_strict {t h : ℝ} (ht : 1 / 2 < t) (ht1 : t < 1) (hh : 0 < h)
    (f : Fin 14) (i : Fin 9) (hi : ¬ OnFace f i) :
    inner ℝ (jucovicFaceNormal t h f) (jucovicVec t h i) < jucovicFaceOffset t h f := by
  have h3 := sqrt3_sq
  have hs : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have ht0 : 0 < t := by linarith
  have a1 := mul_pos hs ht0
  have a2 := mul_pos hs (by linarith : (0 : ℝ) < t - 1 / 2)
  have a3 := mul_pos a1 (by linarith : (0 : ℝ) < 1 - t)
  have a4 := mul_pos a1 ht0
  have a5 := mul_pos hh ht0
  have a6 := mul_pos hh (by linarith : (0 : ℝ) < 1 - t)
  have a7 := mul_pos hs (by linarith : (0 : ℝ) < 1 - t)
  fin_cases f <;> fin_cases i <;> (try simp [OnFace, jucovicFaceVerts] at hi) <;>
    simp [jucovicFaceNormal, jucovicFaceOffset, jucovicVec, inner_vec3] <;>
    ring_nf <;> (try simp only [h3]) <;> nlinarith

theorem jucovic_faceSupport (f : Fin 14) :
    FaceSupport jucovicStar f (jucovicFaceNormal tStar hStar f) (jucovicFaceOffset tStar hStar f) := by
  have hts := tStar_mem
  have hps := hStar_pos
  have ht0 : 0 < tStar := by linarith [hts.1]
  have hs : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨e1, e2, e3⟩ := jucovic_face_on tStar hStar f
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
  · fin_cases f <;> simp [jucovicFaceOffset] <;> positivity
  · rcases hi with rfl | rfl | rfl
    · exact e1
    · exact e2
    · exact e3
  · exact jucovic_face_strict (by linarith [hts.1]) hts.2 hps f i hi

/-- Jucovič's configuration has the type. -/
theorem isTTP_jucovicStar : IsTTP jucovicStar :=
  ⟨Equiv.refl _, fun f => ⟨_, _, jucovic_faceSupport f⟩⟩

/-- At Jucovič's configuration the active sum is exactly `1/h⋆` when
`2 wT + 6 wV = 1`: if `TTPHarmonic` holds, it is sharp. -/
theorem activeSum_jucovicStar {wT wV : ℝ} (hsum : 2 * wT + 6 * wV = 1) :
    activeSum wT wV (jucovicFaceNormal tStar hStar) (jucovicFaceOffset tStar hStar) = 1 / hStar := by
  have hps := hStar_pos
  have e : ∀ f : Fin 14, (f.val < 2 ∨ 8 ≤ f.val) →
      ‖jucovicFaceNormal tStar hStar f‖ / jucovicFaceOffset tStar hStar f = 1 / hStar := by
    intro f hf
    have h := jucovic_active_dist f hf
    have hk : 0 < jucovicFaceOffset tStar hStar f := by
      have := (jucovic_faceSupport f).1; exact this
    rw [div_eq_div_iff hk.ne' hps.ne', ← h]; ring
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e8 := e 8 (by decide)
  have e9 := e 9 (by decide); have e10 := e 10 (by decide); have e11 := e 11 (by decide)
  have e12 := e 12 (by decide); have e13 := e 13 (by decide)
  simp only [activeSum, mul_div_assoc, e0, e1, e8, e9, e10, e11, e12, e13]
  linear_combination (1 / hStar) * hsum

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
  choose N κ hs using hσ
  have hps := hStar_pos
  let idx : Fin 8 → Fin 14 := ![0, 1, 8, 9, 10, 11, 12, 13]
  let w : Fin 8 → ℝ := ![wT, wT, wV, wV, wV, wV, wV, wV]
  refine arccos_le_coveringRadius_of_harmonic _ (p ∘ σ) (fun k => N (idx k)) (fun k => κ (idx k))
    w (fun k => (hs _).1) (fun k => by fin_cases k <;> simp [w, hT, hV]) ?_
    (fun k i => (hs _).le i) hps ?_
  · simp [w, Fin.sum_univ_eight]; linarith
  · have := hH (p ∘ σ) N κ hs
    simp only [Fin.sum_univ_eight]
    simpa [w, idx, activeSum] using this

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
