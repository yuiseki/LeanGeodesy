import LeanGeodesy.Spherical.NinePoint

/-!
# Counterexamples to the supporting-plane statements of the nine-point problem

The statement `TTPHarmonic` asks, for every configuration and every choice of
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
(`not_TTPHarmonic_allEqual`, `not_TTPHarmonic_smallCircle`).
-/

namespace Geodesy.Spherical

open Real

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

/-- The supporting-plane hypothesis of `TTPHarmonic` holds for `allEqual` with
every plane equal to `z = 1`. -/
theorem allEqual_support (f : Fin 14) :
    0 < (1 : ℝ) ∧ inner ℝ (vec3 0 0 1) (allEqual (jucovicFaceVerts f).1).1 = 1 ∧
      inner ℝ (vec3 0 0 1) (allEqual (jucovicFaceVerts f).2.1).1 = 1 ∧
      inner ℝ (vec3 0 0 1) (allEqual (jucovicFaceVerts f).2.2).1 = 1 ∧
      ∀ i, inner ℝ (vec3 (0 : ℝ) 0 1) (allEqual i).1 ≤ 1 := by
  simp only [allEqual, northPole, inner_vec3]
  norm_num

/-- The supporting-plane hypothesis of `TTPHarmonic` holds for `smallCircle`
with every plane equal to `z = 12/13`. -/
theorem smallCircle_support (f : Fin 14) :
    0 < (12 / 13 : ℝ) ∧ inner ℝ (vec3 0 0 1) (smallCircle (jucovicFaceVerts f).1).1 = 12 / 13 ∧
      inner ℝ (vec3 0 0 1) (smallCircle (jucovicFaceVerts f).2.1).1 = 12 / 13 ∧
      inner ℝ (vec3 0 0 1) (smallCircle (jucovicFaceVerts f).2.2).1 = 12 / 13 ∧
      ∀ i, inner ℝ (vec3 (0 : ℝ) 0 1) (smallCircle i).1 ≤ 12 / 13 := by
  simp [smallCircle, inner_vec3]

theorem norm_vec3_001 : ‖vec3 (0 : ℝ) 0 1‖ = 1 := northPole.2

/-- `TTPHarmonic` (with non-strict support) is false for every pair of weights
with `2 wT + 6 wV = 1`: all nine points at the north pole. -/
theorem not_TTPHarmonic_allEqual {wT wV : ℝ} (hsum : 2 * wT + 6 * wV = 1) :
    ¬ TTPHarmonic wT wV := by
  intro hH
  have h := hH allEqual (fun _ => vec3 0 0 1) (fun _ => 1) allEqual_support
  simp only [norm_vec3_001] at h
  have hlt : 1 < 1 / hStar := by
    rw [lt_div_iff₀ hStar_pos]; linarith [hStar_lt_one]
  linarith

/-- `TTPHarmonic` (with non-strict support) is false for every pair of weights
with `2 wT + 6 wV = 1`, also on nine distinct points: the circle `z = 12/13`. -/
theorem not_TTPHarmonic_smallCircle {wT wV : ℝ} (hsum : 2 * wT + 6 * wV = 1) :
    ¬ TTPHarmonic wT wV := by
  intro hH
  have h := hH smallCircle (fun _ => vec3 0 0 1) (fun _ => 12 / 13) smallCircle_support
  simp only [norm_vec3_001] at h
  have hlt : 13 / 12 < 1 / hStar := by
    rw [lt_div_iff₀ hStar_pos]; nlinarith [hStar_lt_12_13]
  have : wT * 1 / (12 / 13) + wT * 1 / (12 / 13) + wV * 1 / (12 / 13) + wV * 1 / (12 / 13) +
      wV * 1 / (12 / 13) + wV * 1 / (12 / 13) + wV * 1 / (12 / 13) + wV * 1 / (12 / 13) =
      13 / 12 := by
    field_simp; linarith
  linarith

end Geodesy.Spherical
