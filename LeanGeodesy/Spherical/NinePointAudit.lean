import LeanGeodesy.Spherical.NinePoint

/-!
# Counterexamples to the supporting-plane statements of the nine-point problem

Until 2026-11-28 the statement `TTPHarmonic` asked, for every configuration and every choice of
planes through the fourteen labelled triangles that keep all nine points on
their inner side, that the weighted sum `Σ w_f ‖N_f‖ / κ_f` over the eight
active faces be at least `1/h⋆`. With non-strict support (`⟪N_f, q i⟫ ≤ κ_f`
for every point) this is false: nothing stops all fourteen planes from being
one and the same plane.

* `allEqual`: the nine points coincide at the north pole; every face plane is
  `z = 1`. The weighted sum is `2 wT + 6 wV`.
* `smallCircle`: nine distinct points on the circle `z = 12/13`; every face
  plane is `z = 12/13`. The weighted sum is `13/12 (2 wT + 6 wV)`. The points
  are distinct, the labelled triangles are non-degenerate, all fourteen faces
  share one plane, and the origin is not in the convex hull (the hull is a flat
  disk at height `12/13`).

With `2 wT + 6 wV = 1` both sums are below `1/h⋆ ≈ 1.4364`
(`not_TTPHarmonic_allEqual`, `not_TTPHarmonic_smallCircle`). That statement is
kept here as `TTPHarmonicWeak`, only as the target of these counterexamples.

The repaired definitions (`FaceSupport`, `IsTTPSupported`, `TTPHarmonic` in
`NinePoint.lean`) ask the six points off each face to be strictly inside its
plane. Both configurations are rejected by them under every labelling
(`not_isTTP_allEqual`, `not_isTTP_smallCircle`); these are the regression tests.
-/

namespace Geodesy.Spherical

open Real

/-- The supporting-plane condition of commits `504e62a`–`705f459`: non-strict
support. Kept only as the target of the counterexamples below. -/
def FaceSupportWeak (q : Fin 9 → UnitSphere) (f : Fin 14) (N : E3) (κ : ℝ) : Prop :=
  0 < κ ∧ inner ℝ N (q (jucovicFaceVerts f).1).1 = κ ∧ inner ℝ N (q (jucovicFaceVerts f).2.1).1 = κ ∧
    inner ℝ N (q (jucovicFaceVerts f).2.2).1 = κ ∧ ∀ i, inner ℝ N (q i).1 ≤ κ

/-- `TTPHarmonic` as stated in commit `bf906c0` (false: see below). -/
def TTPHarmonicWeak (wT wV : ℝ) : Prop :=
  ∀ q : Fin 9 → UnitSphere, ∀ (N : Fin 14 → E3) (κ : Fin 14 → ℝ),
    (∀ f, FaceSupportWeak q f (N f) (κ f)) → 1 / hStar ≤ activeSum wT wV N κ

/-- Strict support implies the weak one, so `TTPHarmonicWeak` would imply the
repaired `TTPHarmonic`; the converse fails. -/
theorem FaceSupport.weak {q : Fin 9 → UnitSphere} {f : Fin 14} {N : E3} {κ : ℝ}
    (h : FaceSupport q f N κ) : FaceSupportWeak q f N κ :=
  ⟨h.1, h.2.1 _ (Or.inl rfl), h.2.1 _ (Or.inr (Or.inl rfl)), h.2.1 _ (Or.inr (Or.inr rfl)), h.le⟩

theorem TTPHarmonic_of_weak {wT wV : ℝ} (h : TTPHarmonicWeak wT wV) : TTPHarmonic wT wV :=
  fun q N κ hs => h q N κ (fun f => (hs f).weak)

/-- The north pole. -/
noncomputable def northPole : UnitSphere :=
  ⟨vec3 0 0 1, by
    have := norm_vec3_sq (0 : ℝ) 0 1
    nlinarith [norm_nonneg (vec3 (0 : ℝ) 0 1)]⟩

/-- The nine points all at the north pole. -/
noncomputable def allEqual : Fin 9 → UnitSphere := fun _ => northPole

/-- Integer coordinates `(x, y)` of nine points with `x² + y² = 25`. -/
def smallCircleXY : Fin 9 → ℤ × ℤ :=
  ![(5, 0), (0, 5), (-5, 0), (0, -5), (3, 4), (4, 3), (-3, 4), (-4, -3), (3, -4)]

theorem smallCircleXY_sq (i : Fin 9) :
    (smallCircleXY i).1 ^ 2 + (smallCircleXY i).2 ^ 2 = 25 := by
  fin_cases i <;> decide

/-- Nine distinct points on the circle `z = 12/13`. -/
noncomputable def smallCircle : Fin 9 → UnitSphere := fun i =>
  ⟨vec3 ((smallCircleXY i).1 / 13) ((smallCircleXY i).2 / 13) (12 / 13), by
    have h := smallCircleXY_sq i
    have h' : ((smallCircleXY i).1 : ℝ) ^ 2 + ((smallCircleXY i).2 : ℝ) ^ 2 = 25 := by
      exact_mod_cast h
    have hn := norm_vec3_sq ((smallCircleXY i).1 / 13 : ℝ) ((smallCircleXY i).2 / 13) (12 / 13)
    have : ‖vec3 ((smallCircleXY i).1 / 13 : ℝ) ((smallCircleXY i).2 / 13) (12 / 13)‖ ^ 2 = 1 := by
      rw [hn]; field_simp; linear_combination h'
    nlinarith [norm_nonneg (vec3 ((smallCircleXY i).1 / 13 : ℝ) ((smallCircleXY i).2 / 13) (12 / 13))]⟩

theorem smallCircle_injective : Function.Injective smallCircle := by
  intro i j hij
  have e0 := congrArg (fun v : UnitSphere => v.1 0) hij
  have e1 := congrArg (fun v : UnitSphere => v.1 1) hij
  simp [smallCircle, vec3] at e0 e1
  fin_cases i <;> fin_cases j <;> simp_all [smallCircleXY]

theorem hStar_lt_one : hStar < 1 := by
  have h2 := hStar_sq
  have hp := hStar_pos
  obtain ⟨ht1, ht2⟩ := tStar_mem
  nlinarith

theorem hStar_lt_12_13 : hStar < 12 / 13 := by
  have h2 := hStar_sq
  have hp := hStar_pos
  have ht := tStar_bracket
  nlinarith

theorem allEqual_support' (f : Fin 14) :
    0 < (1 : ℝ) ∧ inner ℝ (vec3 0 0 1) (allEqual (jucovicFaceVerts f).1).1 = 1 ∧
      inner ℝ (vec3 0 0 1) (allEqual (jucovicFaceVerts f).2.1).1 = 1 ∧
      inner ℝ (vec3 0 0 1) (allEqual (jucovicFaceVerts f).2.2).1 = 1 ∧
      ∀ i, inner ℝ (vec3 (0 : ℝ) 0 1) (allEqual i).1 ≤ 1 := by
  simp only [allEqual, northPole, inner_vec3]
  norm_num

/-- The weak supporting-plane condition holds for `allEqual` with every plane
equal to `z = 1`. -/
theorem allEqual_support (f : Fin 14) : FaceSupportWeak allEqual f (vec3 0 0 1) 1 := by
  unfold FaceSupportWeak
  exact allEqual_support' f

theorem smallCircle_support' (f : Fin 14) :
    0 < (12 / 13 : ℝ) ∧ inner ℝ (vec3 0 0 1) (smallCircle (jucovicFaceVerts f).1).1 = 12 / 13 ∧
      inner ℝ (vec3 0 0 1) (smallCircle (jucovicFaceVerts f).2.1).1 = 12 / 13 ∧
      inner ℝ (vec3 0 0 1) (smallCircle (jucovicFaceVerts f).2.2).1 = 12 / 13 ∧
      ∀ i, inner ℝ (vec3 (0 : ℝ) 0 1) (smallCircle i).1 ≤ 12 / 13 := by
  simp [smallCircle, inner_vec3]

/-- The weak supporting-plane condition holds for `smallCircle` with every
plane equal to `z = 12/13`. -/
theorem smallCircle_support (f : Fin 14) :
    FaceSupportWeak smallCircle f (vec3 0 0 1) (12 / 13) := smallCircle_support' f

theorem norm_vec3_001 : ‖vec3 (0 : ℝ) 0 1‖ = 1 := northPole.2

/-- `TTPHarmonicWeak` (non-strict support) is false for every pair of weights
with `2 wT + 6 wV = 1`: all nine points at the north pole. -/
theorem not_TTPHarmonic_allEqual {wT wV : ℝ} (hsum : 2 * wT + 6 * wV = 1) :
    ¬ TTPHarmonicWeak wT wV := by
  intro hH
  have h := hH allEqual (fun _ => vec3 0 0 1) (fun _ => 1) allEqual_support
  simp only [activeSum, norm_vec3_001] at h
  have hlt : 1 < 1 / hStar := by
    rw [lt_div_iff₀ hStar_pos]; linarith [hStar_lt_one]
  linarith

/-- `TTPHarmonicWeak` (non-strict support) is false for every pair of weights
with `2 wT + 6 wV = 1`, also on nine distinct points: the circle `z = 12/13`. -/
theorem not_TTPHarmonic_smallCircle {wT wV : ℝ} (hsum : 2 * wT + 6 * wV = 1) :
    ¬ TTPHarmonicWeak wT wV := by
  intro hH
  have h := hH smallCircle (fun _ => vec3 0 0 1) (fun _ => 12 / 13) smallCircle_support
  simp only [activeSum, norm_vec3_001] at h
  have hlt : 13 / 12 < 1 / hStar := by
    rw [lt_div_iff₀ hStar_pos]; nlinarith [hStar_lt_12_13]
  have : wT * 1 / (12 / 13) + wT * 1 / (12 / 13) + wV * 1 / (12 / 13) + wV * 1 / (12 / 13) +
      wV * 1 / (12 / 13) + wV * 1 / (12 / 13) + wV * 1 / (12 / 13) + wV * 1 / (12 / 13) =
      13 / 12 := by
    field_simp; linarith
  linarith

/-! ## Regression: the repaired definition rejects both configurations -/

theorem not_isTTPSupported_of_not_injective {q : Fin 9 → UnitSphere}
    (h : ¬ Function.Injective q) : ¬ IsTTPSupported q := fun hs => h hs.injective

/-- Coincident points are rejected under every labelling. -/
theorem not_isTTP_allEqual : ¬ IsTTP allEqual := by
  rintro ⟨σ, hσ⟩
  have := hσ.injective (a₁ := 0) (a₂ := 1) rfl
  exact absurd this (by decide)

theorem inner_vec3_right (N : E3) (x y z : ℝ) :
    inner ℝ N (vec3 x y z) = N 0 * x + N 1 * y + N 2 * z := by
  simp [vec3, PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- A plane through three non-collinear points of the plane `z = c` contains
every point of it. -/
theorem inner_eq_of_three_coplanar {N : E3} {κ c x₁ y₁ x₂ y₂ x₃ y₃ x y : ℝ}
    (hD : (x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁) ≠ 0)
    (h1 : inner ℝ N (vec3 x₁ y₁ c) = κ) (h2 : inner ℝ N (vec3 x₂ y₂ c) = κ)
    (h3 : inner ℝ N (vec3 x₃ y₃ c) = κ) : inner ℝ N (vec3 x y c) = κ := by
  rw [inner_vec3_right] at h1 h2 h3 ⊢
  have ha : N 0 * ((x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁)) = 0 := by
    linear_combination (y₃ - y₁) * (h2 - h1) - (y₂ - y₁) * (h3 - h1)
  have hb : N 1 * ((x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁)) = 0 := by
    linear_combination (x₂ - x₁) * (h3 - h1) - (x₃ - x₁) * (h2 - h1)
  have ha' := (mul_eq_zero.1 ha).resolve_right hD
  have hb' := (mul_eq_zero.1 hb).resolve_right hD
  rw [ha', hb'] at h1 ⊢
  linarith

/-- Any three distinct points of `smallCircle` are non-collinear. -/
theorem smallCircleXY_det : ∀ a b c : Fin 9, a ≠ b → a ≠ c → b ≠ c →
    ((smallCircleXY b).1 - (smallCircleXY a).1) * ((smallCircleXY c).2 - (smallCircleXY a).2) -
      ((smallCircleXY c).1 - (smallCircleXY a).1) * ((smallCircleXY b).2 - (smallCircleXY a).2) ≠ 0 := by
  decide

/-- Nine distinct coplanar points are rejected under every labelling: the plane
of a face contains the other six points too. -/
theorem not_isTTP_smallCircle : ¬ IsTTP smallCircle := by
  rintro ⟨σ, hσ⟩
  obtain ⟨N, κ, hs⟩ := hσ 0
  have v3 := hs.2.1 3 (by decide)
  have v4 := hs.2.1 4 (by decide)
  have v5 := hs.2.1 5 (by decide)
  have o6 := hs.2.2 6 (by decide)
  simp only [Function.comp_apply, smallCircle] at v3 v4 v5 o6
  have hD := smallCircleXY_det (σ 3) (σ 4) (σ 5) (by simp) (by simp) (by simp)
  have hD' : (((smallCircleXY (σ 4)).1 : ℝ) / 13 - (smallCircleXY (σ 3)).1 / 13) *
      ((smallCircleXY (σ 5)).2 / 13 - (smallCircleXY (σ 3)).2 / 13) -
      (((smallCircleXY (σ 5)).1 : ℝ) / 13 - (smallCircleXY (σ 3)).1 / 13) *
      ((smallCircleXY (σ 4)).2 / 13 - (smallCircleXY (σ 3)).2 / 13) ≠ 0 := by
    intro h0
    apply hD
    have : ((((smallCircleXY (σ 4)).1 - (smallCircleXY (σ 3)).1) *
        ((smallCircleXY (σ 5)).2 - (smallCircleXY (σ 3)).2) -
        ((smallCircleXY (σ 5)).1 - (smallCircleXY (σ 3)).1) *
        ((smallCircleXY (σ 4)).2 - (smallCircleXY (σ 3)).2) : ℤ) : ℝ) = 0 := by
      push_cast; linear_combination 169 * h0
    exact_mod_cast this
  have := inner_eq_of_three_coplanar hD' v3 v4 v5
    (x := (smallCircleXY (σ 6)).1 / 13) (y := (smallCircleXY (σ 6)).2 / 13)
  linarith

end Geodesy.Spherical
