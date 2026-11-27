import LeanGeodesy.Spherical.Covering

/-!
# An exact checker for spherical covering radii

A certificate that `n` points of `S²`, given as nonzero rational direction
vectors `q i` (the point is `q i / ‖q i‖`), cover the sphere by caps of radius
`arccos √R` for a rational `R ∈ [0, 1]`.

The trust base is this file and Lean's kernel. The tree in a certificate may
come from any program, floating point included; it is only data that
`checkCover` re-checks in exact rational arithmetic.

## The idea, and why it needs no facet list

By `isCovering_iff_inner` the claim is `∀ u ∈ S², ∃ i, √R ≤ ⟪p i, u⟫`. Every
`u ≠ 0` is a positive multiple of a point of the surface of the cube
`[-1, 1]³`, that is of one of six faces, with the other two coordinates in
`[-1, 1]` (`exists_face`). A certificate gives, for each face, a guillotine
subdivision of the square `[-1, 1]²` into boxes (`CoverTree`), each leaf naming
a point `i`. On a box `[u0, u1] × [v0, v1]` of a face `x_a = t = ±1`:

* `⟪q i, x⟫ ≥ L`, where `L` takes the smaller end of each coordinate range
  (the inner product is linear);
* `‖x‖² ≤ M`, where `M` takes the larger end (the norm squared is convex);

so `L ≥ 0` and `R ‖q i‖² M ≤ L²` give `R ‖q i‖² ‖x‖² ≤ ⟪q i, x⟫²` on the whole
box (`leafOK`). That the boxes cover the face is true by construction: a cut at
`m` sends `u ≤ m` left and `u ≥ m` right. So the covering of the sphere by the
leaves needs no completeness argument about a polytope, and no convex hull is
computed. What the method cannot do is reach `R` equal to the true value of a
configuration: at a deep hole the margin is zero, so a box touching it fails.
A certificate proves `coveringRadius ≤ arccos √R` for `R` a little below the
true `cos² r`, and the slack shrinks as the subdivision refines.
-/

namespace Geodesy.Spherical

open Real Geodesic

/-- A rational vector. -/
abbrev Q3 := ℚ × ℚ × ℚ

/-- The squared length of a rational vector. -/
def nrm2 (q : Q3) : ℚ := q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2

/-- Cyclic rotation of the coordinates, putting axis `a` first. -/
def rot : Fin 3 → Q3 → Q3
  | ⟨0, _⟩, q => q
  | ⟨1, _⟩, q => (q.2.1, q.2.2, q.1)
  | ⟨2, _⟩, q => (q.2.2, q.1, q.2.1)

/-- The real vector of a rational triple. -/
noncomputable def qv (q : Q3) : E3 := vec3 q.1 q.2.1 q.2.2

/-- The vector whose rotated coordinates are `(t, u, v)`. -/
noncomputable def rotVec : Fin 3 → ℝ → ℝ → ℝ → E3
  | ⟨0, _⟩, t, u, v => vec3 t u v
  | ⟨1, _⟩, t, u, v => vec3 v t u
  | ⟨2, _⟩, t, u, v => vec3 u v t

theorem nrm2_rot (a : Fin 3) (q : Q3) : nrm2 (rot a q) = nrm2 q := by
  fin_cases a <;> simp [rot, nrm2] <;> ring

theorem nrm2_nonneg (q : Q3) : 0 ≤ nrm2 q := by
  unfold nrm2; positivity

theorem norm_qv_sq (q : Q3) : ‖qv q‖ ^ 2 = (nrm2 q : ℝ) := by
  unfold qv nrm2
  rw [norm_vec3_sq]; push_cast; ring

theorem inner_qv_rotVec (a : Fin 3) (q : Q3) (t u v : ℝ) :
    inner ℝ (qv q) (rotVec a t u v) =
      ((rot a q).1 : ℝ) * t + ((rot a q).2.1 : ℝ) * u + ((rot a q).2.2 : ℝ) * v := by
  fin_cases a <;> simp [qv, rotVec, rot, inner_vec3] <;> ring

theorem norm_rotVec_sq (a : Fin 3) (t u v : ℝ) :
    ‖rotVec a t u v‖ ^ 2 = t ^ 2 + u ^ 2 + v ^ 2 := by
  fin_cases a <;> simp [rotVec, norm_vec3_sq] <;> ring

/-! ## Faces of the cube -/

private theorem face_of {x y z : ℝ} (hx : x ≠ 0) (hy : |y| ≤ |x|) (hz : |z| ≤ |x|) :
    ∃ (b : Bool) (u v lam : ℝ), 0 < lam ∧ -1 ≤ u ∧ u ≤ 1 ∧ -1 ≤ v ∧ v ≤ 1 ∧
      x = lam * (if b then 1 else -1) ∧ y = lam * u ∧ z = lam * v := by
  have hxp : 0 < |x| := abs_pos.2 hx
  have h1 : abs (y / |x|) ≤ 1 := by rw [abs_div, abs_abs, div_le_one hxp]; exact hy
  have h2 : abs (z / |x|) ≤ 1 := by rw [abs_div, abs_abs, div_le_one hxp]; exact hz
  refine ⟨decide (0 ≤ x), y / |x|, z / |x|, |x|, hxp, (abs_le.1 h1).1, (abs_le.1 h1).2,
    (abs_le.1 h2).1, (abs_le.1 h2).2, ?_, ?_, ?_⟩
  · by_cases h : 0 ≤ x
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (not_le.1 h)]
  · field_simp
  · field_simp

/-- Every nonzero vector is a positive multiple of a point of one of the six
faces of the cube `[-1, 1]³`, with the two free coordinates in `[-1, 1]`. -/
theorem exists_face (w : E3) (hw : w ≠ 0) :
    ∃ (a : Fin 3) (b : Bool) (u v lam : ℝ), 0 < lam ∧ -1 ≤ u ∧ u ≤ 1 ∧ -1 ≤ v ∧ v ≤ 1 ∧
      w = lam • rotVec a (if b then 1 else -1) u v := by
  have hnz : ¬ (w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hw
    rw [← vec3_eta w, h0, h1, h2]
    ext i; fin_cases i <;> rfl
  have case0 : |w 1| ≤ |w 0| → |w 2| ≤ |w 0| → ∃ (a : Fin 3) (b : Bool) (u v lam : ℝ),
      0 < lam ∧ -1 ≤ u ∧ u ≤ 1 ∧ -1 ≤ v ∧ v ≤ 1 ∧
      w = lam • rotVec a (if b then 1 else -1) u v := by
    intro hy hz
    have hx : w 0 ≠ 0 := by
      intro h0
      apply hnz
      have : |w 1| ≤ 0 := by simpa [h0] using hy
      have : |w 2| ≤ 0 := by simpa [h0] using hz
      exact ⟨h0, abs_nonpos_iff.1 (by assumption), abs_nonpos_iff.1 (by assumption)⟩
    obtain ⟨b, u, v, lam, hl, hu1, hu2, hv1, hv2, ex, ey, ez⟩ := face_of hx hy hz
    refine ⟨0, b, u, v, lam, hl, hu1, hu2, hv1, hv2, ?_⟩
    rw [← vec3_eta w, ex, ey, ez]
    simp [rotVec, vec3_smul]
  have case1 : |w 2| ≤ |w 1| → |w 0| ≤ |w 1| → ∃ (a : Fin 3) (b : Bool) (u v lam : ℝ),
      0 < lam ∧ -1 ≤ u ∧ u ≤ 1 ∧ -1 ≤ v ∧ v ≤ 1 ∧
      w = lam • rotVec a (if b then 1 else -1) u v := by
    intro hz hx
    have hy : w 1 ≠ 0 := by
      intro h0
      apply hnz
      have : |w 2| ≤ 0 := by simpa [h0] using hz
      have : |w 0| ≤ 0 := by simpa [h0] using hx
      exact ⟨abs_nonpos_iff.1 (by assumption), h0, abs_nonpos_iff.1 (by assumption)⟩
    obtain ⟨b, u, v, lam, hl, hu1, hu2, hv1, hv2, ey, ez, ex⟩ := face_of hy hz hx
    refine ⟨1, b, u, v, lam, hl, hu1, hu2, hv1, hv2, ?_⟩
    rw [← vec3_eta w, ex, ey, ez]
    simp [rotVec, vec3_smul]
  have case2 : |w 0| ≤ |w 2| → |w 1| ≤ |w 2| → ∃ (a : Fin 3) (b : Bool) (u v lam : ℝ),
      0 < lam ∧ -1 ≤ u ∧ u ≤ 1 ∧ -1 ≤ v ∧ v ≤ 1 ∧
      w = lam • rotVec a (if b then 1 else -1) u v := by
    intro hx hy
    have hz : w 2 ≠ 0 := by
      intro h0
      apply hnz
      have : |w 0| ≤ 0 := by simpa [h0] using hx
      have : |w 1| ≤ 0 := by simpa [h0] using hy
      exact ⟨abs_nonpos_iff.1 (by assumption), abs_nonpos_iff.1 (by assumption), h0⟩
    obtain ⟨b, u, v, lam, hl, hu1, hu2, hv1, hv2, ez, ex, ey⟩ := face_of hz hx hy
    refine ⟨2, b, u, v, lam, hl, hu1, hu2, hv1, hv2, ?_⟩
    rw [← vec3_eta w, ex, ey, ez]
    simp [rotVec, vec3_smul]
  rcases le_total |w 1| |w 0| with h10 | h01
  · rcases le_total |w 2| |w 0| with h20 | h02
    · exact case0 h10 h20
    · exact case2 h02 (h10.trans h02)
  · rcases le_total |w 2| |w 1| with h21 | h12
    · exact case1 h21 h01
    · exact case2 (h01.trans h12) h12

/-! ## The certificate and its checker -/

/-- A guillotine subdivision of a face square: a leaf names the point `i` that
covers its box; a cut splits the first or second free coordinate at `m`. -/
inductive CoverTree
  | leaf (i : ℕ)
  | cutU (m : ℚ) (l r : CoverTree)
  | cutV (m : ℚ) (l r : CoverTree)
  deriving Repr

/-- The lower bound of `⟪q, x⟫` on the box, `x = (t, u, v)` in rotated
coordinates. -/
def lowerDot (q : Q3) (t u0 u1 v0 v1 : ℚ) : ℚ :=
  q.1 * t + min (q.2.1 * u0) (q.2.1 * u1) + min (q.2.2 * v0) (q.2.2 * v1)

/-- The upper bound of `‖x‖²` on the box. -/
def normUpper (t u0 u1 v0 v1 : ℚ) : ℚ :=
  t ^ 2 + max (u0 ^ 2) (u1 ^ 2) + max (v0 ^ 2) (v1 ^ 2)

/-- The test at a leaf. -/
def leafOK (R : ℚ) (q : Q3) (t u0 u1 v0 v1 : ℚ) : Bool :=
  decide (0 ≤ lowerDot q t u0 u1 v0 v1 ∧
    R * nrm2 q * normUpper t u0 u1 v0 v1 ≤ lowerDot q t u0 u1 v0 v1 ^ 2)

/-- Check one face tree on the box `[u0, u1] × [v0, v1]`. -/
def chk {n : ℕ} (q : Fin n → Q3) (R : ℚ) (a : Fin 3) (t : ℚ) :
    CoverTree → ℚ → ℚ → ℚ → ℚ → Bool
  | .leaf i, u0, u1, v0, v1 =>
      if h : i < n then leafOK R (rot a (q ⟨i, h⟩)) t u0 u1 v0 v1 else false
  | .cutU m l r, u0, u1, v0, v1 =>
      chk q R a t l u0 m v0 v1 && chk q R a t r m u1 v0 v1
  | .cutV m l r, u0, u1, v0, v1 =>
      chk q R a t l u0 u1 v0 m && chk q R a t r u0 u1 m v1

/-- The sign of face `b`. -/
def faceSign (b : Bool) : ℚ := if b then 1 else -1

/-- Check a full certificate: `R ∈ [0, 1]` and a tree for each of the six faces
of the cube. -/
def checkCover {n : ℕ} (q : Fin n → Q3) (R : ℚ) (T : Fin 3 → Bool → CoverTree) : Bool :=
  decide (0 ≤ R ∧ R ≤ 1) &&
    (List.finRange 3).all fun a =>
      [true, false].all fun b => chk q R a (faceSign b) (T a b) (-1) 1 (-1) 1

/-! ## Soundness -/

private theorem min_mul_le (q a b x : ℝ) (h1 : a ≤ x) (h2 : x ≤ b) :
    min (q * a) (q * b) ≤ q * x := by
  rcases le_total 0 q with h | h
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left h1 h)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left h2 h)

private theorem sq_le_max_sq (a b x : ℝ) (h1 : a ≤ x) (h2 : x ≤ b) :
    x ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
  rcases le_total 0 x with h | h
  · exact (pow_le_pow_left₀ h h2 2).trans (le_max_right _ _)
  · have : -x ≤ -a := by linarith
    have := pow_le_pow_left₀ (by linarith) this 2
    calc x ^ 2 = (-x) ^ 2 := by ring
      _ ≤ (-a) ^ 2 := this
      _ = a ^ 2 := by ring
      _ ≤ _ := le_max_left _ _

private theorem leafOK_sound {R : ℚ} (hR : 0 ≤ R) {q : Q3} {t u0 u1 v0 v1 : ℚ}
    (h : leafOK R q t u0 u1 v0 v1 = true) (u v : ℝ) (hu0 : (u0 : ℝ) ≤ u) (hu1 : u ≤ u1)
    (hv0 : (v0 : ℝ) ≤ v) (hv1 : v ≤ v1) :
    0 ≤ (q.1 : ℝ) * t + q.2.1 * u + q.2.2 * v ∧
      (R : ℝ) * (nrm2 q : ℝ) * ((t : ℝ) ^ 2 + u ^ 2 + v ^ 2) ≤
        ((q.1 : ℝ) * t + q.2.1 * u + q.2.2 * v) ^ 2 := by
  obtain ⟨hL, hRL⟩ := of_decide_eq_true h
  have hLr : (0 : ℝ) ≤ (lowerDot q t u0 u1 v0 v1 : ℝ) := by exact_mod_cast hL
  have hRLr : (R : ℝ) * (nrm2 q : ℝ) * (normUpper t u0 u1 v0 v1 : ℝ) ≤
      (lowerDot q t u0 u1 v0 v1 : ℝ) ^ 2 := by exact_mod_cast hRL
  have hlow : (lowerDot q t u0 u1 v0 v1 : ℝ) ≤ (q.1 : ℝ) * t + q.2.1 * u + q.2.2 * v := by
    unfold lowerDot
    push_cast
    have h1 := min_mul_le (q.2.1 : ℝ) u0 u1 u hu0 hu1
    have h2 := min_mul_le (q.2.2 : ℝ) v0 v1 v hv0 hv1
    linarith
  have hup : (t : ℝ) ^ 2 + u ^ 2 + v ^ 2 ≤ (normUpper t u0 u1 v0 v1 : ℝ) := by
    unfold normUpper
    push_cast
    have h1 := sq_le_max_sq (u0 : ℝ) u1 u hu0 hu1
    have h2 := sq_le_max_sq (v0 : ℝ) v1 v hv0 hv1
    linarith
  have hRn : (0 : ℝ) ≤ (R : ℝ) * (nrm2 q : ℝ) := by
    have := nrm2_nonneg q
    have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR
    have : (0 : ℝ) ≤ (nrm2 q : ℝ) := by exact_mod_cast this
    positivity
  refine ⟨hLr.trans hlow, ?_⟩
  calc (R : ℝ) * (nrm2 q : ℝ) * ((t : ℝ) ^ 2 + u ^ 2 + v ^ 2)
      ≤ (R : ℝ) * (nrm2 q : ℝ) * (normUpper t u0 u1 v0 v1 : ℝ) :=
        mul_le_mul_of_nonneg_left hup hRn
    _ ≤ (lowerDot q t u0 u1 v0 v1 : ℝ) ^ 2 := hRLr
    _ ≤ _ := pow_le_pow_left₀ hLr hlow 2

/-- What a successful check of a face tree proves: every point of every box it
covers has a point `i` with `R ‖q i‖² ‖x‖² ≤ ⟪q i, x⟫²` and `0 ≤ ⟪q i, x⟫`. -/
theorem chk_sound {n : ℕ} (q : Fin n → Q3) (R : ℚ) (hR : 0 ≤ R) (a : Fin 3) (t : ℚ) :
    ∀ (T : CoverTree) (u0 u1 v0 v1 : ℚ), chk q R a t T u0 u1 v0 v1 = true →
      ∀ u v : ℝ, (u0 : ℝ) ≤ u → u ≤ u1 → (v0 : ℝ) ≤ v → v ≤ v1 →
        ∃ i : Fin n, 0 ≤ inner ℝ (qv (q i)) (rotVec a t u v) ∧
          (R : ℝ) * ‖qv (q i)‖ ^ 2 * ‖rotVec a t u v‖ ^ 2 ≤
            (inner ℝ (qv (q i)) (rotVec a t u v)) ^ 2 := by
  intro T
  induction T with
  | leaf i =>
    intro u0 u1 v0 v1 h u v hu0 hu1 hv0 hv1
    simp only [chk] at h
    split_ifs at h with hi
    obtain ⟨h1, h2⟩ := leafOK_sound hR h u v hu0 hu1 hv0 hv1
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · rw [inner_qv_rotVec]; exact h1
    · rw [inner_qv_rotVec, norm_qv_sq, norm_rotVec_sq, ← nrm2_rot a (q ⟨i, hi⟩)]
      exact h2
  | cutU m l r ihl ihr =>
    intro u0 u1 v0 v1 h u v hu0 hu1 hv0 hv1
    simp only [chk, Bool.and_eq_true] at h
    rcases le_total u (m : ℝ) with hm | hm
    · exact ihl _ _ _ _ h.1 u v hu0 hm hv0 hv1
    · exact ihr _ _ _ _ h.2 u v hm hu1 hv0 hv1
  | cutV m l r ihl ihr =>
    intro u0 u1 v0 v1 h u v hu0 hu1 hv0 hv1
    simp only [chk, Bool.and_eq_true] at h
    rcases le_total v (m : ℝ) with hm | hm
    · exact ihl _ _ _ _ h.1 u v hu0 hu1 hv0 hm
    · exact ihr _ _ _ _ h.2 u v hu0 hu1 hm hv1

/-- A configuration `p` realizes the rational directions `q`: each point is
`q i` normalized. -/
def Realizes {n : ℕ} (q : Fin n → Q3) (p : Fin n → UnitSphere) : Prop :=
  ∀ i, (p i).1 = ‖qv (q i)‖⁻¹ • qv (q i)

/-- Soundness of the checker: an accepted certificate gives, in every unit
direction, a point of the configuration with inner product at least `√R`. -/
theorem checkCover_sound {n : ℕ} {q : Fin n → Q3} {R : ℚ} {T : Fin 3 → Bool → CoverTree}
    (h : checkCover q R T = true) {p : Fin n → UnitSphere} (hp : Realizes q p)
    (u : UnitSphere) : ∃ i : Fin n, √(R : ℝ) ≤ inner ℝ (p i).1 u.1 := by
  simp only [checkCover, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies] at h
  obtain ⟨⟨hR0, -⟩, hfaces⟩ := h
  have hRr : (0 : ℝ) ≤ R := by exact_mod_cast hR0
  have hu0 : u.1 ≠ 0 := by
    intro h0; have := u.2; rw [h0, norm_zero] at this; exact zero_ne_one this
  obtain ⟨a, b, u', v', lam, hl, h1, h2, h3, h4, hw⟩ := exists_face u.1 hu0
  have hcheck : chk q R a (faceSign b) (T a b) (-1) 1 (-1) 1 = true := by
    exact hfaces a b (by cases b <;> simp)
  obtain ⟨i, hi0, hi⟩ := chk_sound q R hR0 a (faceSign b) (T a b) (-1) 1 (-1) 1 hcheck u' v'
    (by push_cast; exact h1) (by push_cast; exact h2) (by push_cast; exact h3)
    (by push_cast; exact h4)
  refine ⟨i, ?_⟩
  have hs : ((faceSign b : ℚ) : ℝ) = if b then 1 else -1 := by
    unfold faceSign; split_ifs <;> simp
  rw [hs] at hi0 hi
  set x := rotVec a (if b then 1 else -1) u' v' with hx
  set A := inner ℝ (qv (q i)) x with hA
  have hxn : ‖x‖ ^ 2 = 1 + u' ^ 2 + v' ^ 2 := by
    rw [hx, norm_rotVec_sq]; split_ifs <;> ring
  have hxpos : 0 < ‖x‖ := by
    have : 0 < ‖x‖ ^ 2 := by rw [hxn]; positivity
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at this; simp at this)
  have hq0 : ‖qv (q i)‖ ≠ 0 := by
    intro h0
    have h1 := hp i
    rw [h0, inv_zero, zero_smul] at h1
    have := (p i).2
    rw [h1, norm_zero] at this
    exact zero_ne_one this
  have hqpos : 0 < ‖qv (q i)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq0)
  have hunit : lam * ‖x‖ = 1 := by
    have := u.2
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos hl] at this
    exact this
  have hinner : inner ℝ (p i).1 u.1 = A * ‖qv (q i)‖⁻¹ * lam := by
    rw [hp i, hw, inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    rw [hA]; ring
  rw [hinner]
  have hB : 0 < ‖qv (q i)‖ * ‖x‖ := mul_pos hqpos hxpos
  have hlam : lam = ‖x‖⁻¹ := by field_simp; linarith
  have hfinal : A * ‖qv (q i)‖⁻¹ * lam = A / (‖qv (q i)‖ * ‖x‖) := by
    rw [hlam]; field_simp
  rw [hfinal, Real.sqrt_le_iff]
  refine ⟨div_nonneg hi0 hB.le, ?_⟩
  rw [div_pow, le_div_iff₀ (by positivity)]
  calc (R : ℝ) * (‖qv (q i)‖ * ‖x‖) ^ 2 = (R : ℝ) * ‖qv (q i)‖ ^ 2 * ‖x‖ ^ 2 := by ring
    _ ≤ A ^ 2 := hi

/-- An accepted certificate bounds the covering radius: the configuration
covers `S²` by closed caps of radius `arccos √R`. -/
theorem isCovering_of_checkCover {n : ℕ} {q : Fin n → Q3} {R : ℚ}
    {T : Fin 3 → Bool → CoverTree} (h : checkCover q R T = true) {p : Fin n → UnitSphere}
    (hp : Realizes q p) : IsCovering p (arccos √(R : ℝ)) := by
  have hR : 0 ≤ R ∧ R ≤ 1 := by
    simp only [checkCover, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have hRr0 : (0 : ℝ) ≤ R := by exact_mod_cast hR.1
  have hRr1 : (R : ℝ) ≤ 1 := by exact_mod_cast hR.2
  have hs1 : √(R : ℝ) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hRr1
  rw [isCovering_iff_inner p (arccos_nonneg _) (arccos_le_pi _),
    cos_arccos (by linarith [Real.sqrt_nonneg (R : ℝ)]) hs1]
  intro x
  exact checkCover_sound h hp x

/-- The covering radius of a configuration with an accepted certificate is at
most `arccos √R`. -/
theorem coveringRadius_le_of_checkCover {n : ℕ} (hn : 1 ≤ n) {q : Fin n → Q3} {R : ℚ}
    {T : Fin 3 → Bool → CoverTree} (h : checkCover q R T = true) {p : Fin n → UnitSphere}
    (hp : Realizes q p) : coveringRadius hn p ≤ arccos √(R : ℝ) :=
  (coveringRadius_le_iff hn p _).2 (isCovering_of_checkCover h hp)

end Geodesy.Spherical
