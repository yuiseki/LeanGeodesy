import LeanGeodesy.Spherical.CoveringLowerBound

/-!
# Jucovič's covering of the sphere by nine caps

Jucovič (Mat.-fyz. časopis 10 (1960), 99–104, §2) covers `S²` by nine equal
caps of radius `45°53'`: an equilateral triangle `A₁A₂A₃` on a great circle,
and above and below it the apexes `Bᵢ`, `Cᵢ` of congruent isosceles triangles
on the sides `AᵢAᵢ₊₁`, with legs `68°58'`. This file formalizes that
configuration exactly and proves its covering radius. It is the best known
9-point covering (numerically); nothing here says it is optimal among all
9-point configurations.

## The model

For `0 < t < 1` and `h = √(1 - t²)`, with `θₖ = 2πk/3`:

* `Aₖ = (cos θₖ, sin θₖ, 0)`,
* `Bₖ = (t cos(θₖ + π/3), t sin(θₖ + π/3), h)`, `Cₖ` the mirror image in `z = 0`.

`jucovicVec t h` lists them as `A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂`. The symmetry group
is `D₃h` (rotation by `2π/3`, the mirror `y ↦ -y`, the mirror `z ↦ -z`).

The faces through `A₀` in the sector `0 ≤ φ ≤ π/3`, `z ≥ 0`, and their distances
from the origin:

* `B₀B₁B₂` (plane `z = h`): `h`;
* `A₀B₀C₀` (normal `(√3 t, 2 - t, 0)`): `√3 t / (2 √(t² - t + 1))`, a supporting
  plane exactly when `t ≥ 1/2`;
* `A₀B₂B₀` (normal `(h, 0, 1 - t/2)`): `h / √(h² + (1 - t/2)²)`, at least `h`
  exactly when `t ≥ 2/3`.

The optimal parameter `t⋆` makes the first two equal, which after squaring is
`4t⁴ - 4t³ + 3t² + 4t - 4 = 0` (`jucovicQuartic`); its unique root in `(0, 1)`
lies in `(2/3, 1)`.
-/

namespace Geodesy.Spherical

open Real Geodesic

/-! ## The quartic and its root -/

/-- `4t⁴ - 4t³ + 3t² + 4t - 4`. -/
def jucovicQuartic (t : ℝ) : ℝ := 4 * t ^ 4 - 4 * t ^ 3 + 3 * t ^ 2 + 4 * t - 4

theorem jucovicQuartic_strictMonoOn : StrictMonoOn jucovicQuartic (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  simp only [jucovicQuartic]
  have hba : 0 < b - a := by linarith
  have key : 0 < 4 * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) - 4 * (a ^ 2 + a * b + b ^ 2) +
      3 * (a + b) + 4 := by
    nlinarith [mul_nonneg ha hb, sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2),
      mul_nonneg (mul_nonneg ha hb) (add_nonneg ha hb), mul_nonneg ha (sq_nonneg (a - 1 / 2)),
      mul_nonneg hb (sq_nonneg (b - 1 / 2)), sq_nonneg (a - b), mul_nonneg ha (sq_nonneg (b - 1 / 2)),
      mul_nonneg hb (sq_nonneg (a - 1 / 2))]
  have : 4 * b ^ 4 - 4 * b ^ 3 + 3 * b ^ 2 + 4 * b - 4 -
      (4 * a ^ 4 - 4 * a ^ 3 + 3 * a ^ 2 + 4 * a - 4) =
      (b - a) * (4 * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) - 4 * (a ^ 2 + a * b + b ^ 2) +
        3 * (a + b) + 4) := by ring
  nlinarith [mul_pos hba key]

theorem exists_jucovicQuartic_root : ∃ t ∈ Set.Ioo (2 / 3 : ℝ) 1, jucovicQuartic t = 0 := by
  have hc : ContinuousOn jucovicQuartic (Set.Icc (2 / 3) 1) := by
    unfold jucovicQuartic; fun_prop
  have h := intermediate_value_Ioo (by norm_num : (2 / 3 : ℝ) ≤ 1) hc
  have h0 : (0 : ℝ) ∈ Set.Ioo (jucovicQuartic (2 / 3)) (jucovicQuartic 1) := by
    simp only [jucovicQuartic, Set.mem_Ioo]; norm_num
  obtain ⟨t, ht, hft⟩ := h h0
  exact ⟨t, ht, hft⟩

/-- The optimal parameter: the root of `4t⁴ - 4t³ + 3t² + 4t - 4` in `(2/3, 1)`. -/
noncomputable def tStar : ℝ := Classical.choose exists_jucovicQuartic_root

theorem tStar_mem : tStar ∈ Set.Ioo (2 / 3 : ℝ) 1 :=
  (Classical.choose_spec exists_jucovicQuartic_root).1

theorem jucovicQuartic_tStar : jucovicQuartic tStar = 0 :=
  (Classical.choose_spec exists_jucovicQuartic_root).2

/-- `tStar` is the only nonnegative root. -/
theorem eq_tStar_of_jucovicQuartic {t : ℝ} (ht : 0 ≤ t) (h : jucovicQuartic t = 0) :
    t = tStar :=
  jucovicQuartic_strictMonoOn.injOn ht (le_of_lt (lt_trans (by norm_num) tStar_mem.1))
    (h.trans jucovicQuartic_tStar.symm)

/-- A bracket for `tStar` from the sign of the quartic: `0.7178 < tStar < 0.7179`. -/
theorem tStar_bracket : (7178 / 10000 : ℝ) < tStar ∧ tStar < 7179 / 10000 := by
  have h0 : (0 : ℝ) ≤ tStar := le_of_lt (lt_trans (by norm_num) tStar_mem.1)
  constructor
  · by_contra hle
    push Not at hle
    have := jucovicQuartic_strictMonoOn.monotoneOn h0 (by norm_num : (0 : ℝ) ≤ 7178 / 10000) hle
    rw [jucovicQuartic_tStar] at this
    simp only [jucovicQuartic] at this
    norm_num at this
  · by_contra hle
    push Not at hle
    have := jucovicQuartic_strictMonoOn.monotoneOn (by norm_num : (0 : ℝ) ≤ 7179 / 10000) h0 hle
    rw [jucovicQuartic_tStar] at this
    simp only [jucovicQuartic] at this
    norm_num at this

/-- The height `h⋆ = √(1 - t⋆²)` of the upper triangle. -/
noncomputable def hStar : ℝ := √(1 - tStar ^ 2)

theorem hStar_sq : hStar ^ 2 = 1 - tStar ^ 2 :=
  Real.sq_sqrt (by nlinarith [tStar_mem.1, tStar_mem.2])

theorem hStar_pos : 0 < hStar :=
  Real.sqrt_pos.2 (by nlinarith [tStar_mem.1, tStar_mem.2])

/-- `h⋆ = cos ρ⋆` is a root of `16x⁸ - 72x⁶ + 129x⁴ - 66x² + 9` (the polynomial
Rathbun 2020 identified numerically): it is `f(t⋆) f(-t⋆)` written in `h⋆²`. -/
theorem hStar_octic : 16 * hStar ^ 8 - 72 * hStar ^ 6 + 129 * hStar ^ 4 - 66 * hStar ^ 2 + 9 = 0 := by
  have h2 := hStar_sq
  have hq : 4 * tStar ^ 4 - 4 * tStar ^ 3 + 3 * tStar ^ 2 + 4 * tStar - 4 = 0 :=
    jucovicQuartic_tStar
  have e : 16 * hStar ^ 8 - 72 * hStar ^ 6 + 129 * hStar ^ 4 - 66 * hStar ^ 2 + 9 =
      16 * (hStar ^ 2) ^ 4 - 72 * (hStar ^ 2) ^ 3 + 129 * (hStar ^ 2) ^ 2 - 66 * hStar ^ 2 + 9 := by
    ring
  rw [e, h2]
  linear_combination (4 * tStar ^ 4 + 4 * tStar ^ 3 + 3 * tStar ^ 2 - 4 * tStar - 4) * hq

/-! ## The nine points -/

/-- The nine points `A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂` for parameters `t`, `h`. -/
noncomputable def jucovicVec (t h : ℝ) : Fin 9 → E3 :=
  ![vec3 1 0 0, vec3 (-1 / 2) (√3 / 2) 0, vec3 (-1 / 2) (-(√3 / 2)) 0,
    vec3 (t / 2) (√3 / 2 * t) h, vec3 (-t) 0 h, vec3 (t / 2) (-(√3 / 2 * t)) h,
    vec3 (t / 2) (√3 / 2 * t) (-h), vec3 (-t) 0 (-h), vec3 (t / 2) (-(√3 / 2 * t)) (-h)]

private theorem sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem norm_jucovicVec {t h : ℝ} (hth : t ^ 2 + h ^ 2 = 1) (i : Fin 9) :
    ‖jucovicVec t h i‖ = 1 := by
  have h3 := sqrt3_sq
  have hsq : ‖jucovicVec t h i‖ ^ 2 = 1 := by
    fin_cases i <;> (show ‖vec3 _ _ _‖ ^ 2 = 1; rw [norm_vec3_sq]) <;>
      first | (norm_num; done) | linear_combination (1 / 4 : ℝ) * h3 | linear_combination hth |
        linear_combination hth + (t ^ 2 / 4) * h3
  nlinarith [norm_nonneg (jucovicVec t h i)]

/-- The configuration of parameter `t ∈ (0, 1)`, with `h = √(1 - t²)`. -/
noncomputable def jucovic (t : ℝ) (ht : t ^ 2 ≤ 1) : Fin 9 → UnitSphere := fun i =>
  ⟨jucovicVec t (√(1 - t ^ 2)) i, norm_jucovicVec (by rw [Real.sq_sqrt (by linarith)]; ring) i⟩

/-- Jucovič's configuration: the parameter `t⋆`. -/
noncomputable def jucovicStar : Fin 9 → UnitSphere :=
  jucovic tStar (by nlinarith [tStar_mem.1, tStar_mem.2])

theorem jucovic_coe (t : ℝ) (ht : t ^ 2 ≤ 1) (i : Fin 9) :
    (jucovic t ht i).1 = jucovicVec t (√(1 - t ^ 2)) i := rfl

/-- The nine points are distinct. -/
theorem jucovic_injective {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Function.Injective (jucovic t (by nlinarith)) := by
  have hpos : 0 < √(1 - t ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have h3 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  intro i j hij
  have e0 := congrArg (fun v : UnitSphere => v.1 0) hij
  have e1 := congrArg (fun v : UnitSphere => v.1 1) hij
  have e2 := congrArg (fun v : UnitSphere => v.1 2) hij
  simp only [jucovic_coe] at e0 e1 e2
  fin_cases i <;> fin_cases j <;>
    simp [jucovicVec] at e0 e1 e2 ⊢ <;> nlinarith

/-! ## The symmetry group `D₃h` -/

/-- The mirror `z ↦ -z`. -/
noncomputable def symZ (v : E3) : E3 := vec3 (v 0) (v 1) (-(v 2))
/-- The mirror `y ↦ -y`. -/
noncomputable def symS (v : E3) : E3 := vec3 (v 0) (-(v 1)) (v 2)
/-- The rotation by `2π/3` about the `z`-axis. -/
noncomputable def symR (v : E3) : E3 :=
  vec3 (-(v 0) / 2 - √3 / 2 * v 1) (√3 / 2 * v 0 - v 1 / 2) (v 2)
/-- The rotation by `-2π/3` about the `z`-axis. -/
noncomputable def symRi (v : E3) : E3 :=
  vec3 (-(v 0) / 2 + √3 / 2 * v 1) (-(√3 / 2) * v 0 - v 1 / 2) (v 2)

theorem inner_symZ (a b : E3) : inner ℝ (symZ a) (symZ b) = inner ℝ a b := by
  rw [inner_E3, inner_E3]; simp only [symZ, vec3_0, vec3_1, vec3_2]; ring
theorem inner_symS (a b : E3) : inner ℝ (symS a) (symS b) = inner ℝ a b := by
  rw [inner_E3, inner_E3]; simp only [symS, vec3_0, vec3_1, vec3_2]; ring
theorem inner_symR (a b : E3) : inner ℝ (symR a) (symR b) = inner ℝ a b := by
  rw [inner_E3, inner_E3]; simp only [symR, vec3_0, vec3_1, vec3_2]
  linear_combination (a 0 * b 0 + a 1 * b 1) / 4 * sqrt3_sq
theorem inner_symRi (a b : E3) : inner ℝ (symRi a) (symRi b) = inner ℝ a b := by
  rw [inner_E3, inner_E3]; simp only [symRi, vec3_0, vec3_1, vec3_2]
  linear_combination (a 0 * b 0 + a 1 * b 1) / 4 * sqrt3_sq

private theorem norm_of_inner {g : E3 → E3} (hg : ∀ a b, inner ℝ (g a) (g b) = inner ℝ a b)
    (x : E3) : ‖g x‖ = ‖x‖ := by
  have h := hg x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The support property is invariant under a symmetry that permutes the points. -/
theorem support_of_sym {t h ρ : ℝ} {g : E3 → E3} (hg : ∀ a b, inner ℝ (g a) (g b) = inner ℝ a b)
    (hperm : ∀ i, ∃ j, g (jucovicVec t h j) = jucovicVec t h i) (x : E3)
    (hx : ∃ i, ρ * ‖g x‖ ≤ inner ℝ (jucovicVec t h i) (g x)) :
    ∃ i, ρ * ‖x‖ ≤ inner ℝ (jucovicVec t h i) x := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hperm i
  refine ⟨j, ?_⟩
  rw [← hj, hg, norm_of_inner hg] at hi
  exact hi

theorem perm_symZ (t h : ℝ) : ∀ i, ∃ j, symZ (jucovicVec t h j) = jucovicVec t h i := by
  intro i
  fin_cases i
  · exact ⟨0, by simp [symZ, jucovicVec]⟩
  · exact ⟨1, by simp [symZ, jucovicVec]⟩
  · exact ⟨2, by simp [symZ, jucovicVec]⟩
  · exact ⟨6, by simp [symZ, jucovicVec]⟩
  · exact ⟨7, by simp [symZ, jucovicVec]⟩
  · exact ⟨8, by simp [symZ, jucovicVec]⟩
  · exact ⟨3, by simp [symZ, jucovicVec]⟩
  · exact ⟨4, by simp [symZ, jucovicVec]⟩
  · exact ⟨5, by simp [symZ, jucovicVec]⟩

theorem perm_symS (t h : ℝ) : ∀ i, ∃ j, symS (jucovicVec t h j) = jucovicVec t h i := by
  intro i
  fin_cases i
  · exact ⟨0, by simp [symS, jucovicVec]⟩
  · exact ⟨2, by simp [symS, jucovicVec]⟩
  · exact ⟨1, by simp [symS, jucovicVec]⟩
  · exact ⟨5, by simp [symS, jucovicVec]⟩
  · exact ⟨4, by simp [symS, jucovicVec]⟩
  · exact ⟨3, by simp [symS, jucovicVec]⟩
  · exact ⟨8, by simp [symS, jucovicVec]⟩
  · exact ⟨7, by simp [symS, jucovicVec]⟩
  · exact ⟨6, by simp [symS, jucovicVec]⟩

/-- Close a coordinate identity that may involve `√3 ^ 2`. -/
local macro "sqrt3_close" : tactic =>
  `(tactic| first
    | done
    | (apply vec3_eq_of <;> (ring_nf; try simp only [sqrt3_sq]; try ring_nf))
    | (ring_nf; try simp only [sqrt3_sq]; try ring_nf))

private theorem vec3_eq_of {x y z x' y' z' : ℝ} (hx : x = x') (hy : y = y') (hz : z = z') :
    vec3 x y z = vec3 x' y' z' := vec3_congr hx hy hz

theorem perm_symR (t h : ℝ) : ∀ i, ∃ j, symR (jucovicVec t h j) = jucovicVec t h i := by
  have h3 := sqrt3_sq
  intro i
  fin_cases i
  · refine ⟨2, ?_⟩; simp [symR, jucovicVec]; sqrt3_close
  · refine ⟨0, ?_⟩; simp [symR, jucovicVec]
  · refine ⟨1, ?_⟩; simp [symR, jucovicVec]; sqrt3_close
  · refine ⟨5, ?_⟩; simp [symR, jucovicVec]; sqrt3_close
  · refine ⟨3, ?_⟩; simp [symR, jucovicVec]; sqrt3_close
  · refine ⟨4, ?_⟩; simp [symR, jucovicVec]
  · refine ⟨8, ?_⟩; simp [symR, jucovicVec]; sqrt3_close
  · refine ⟨6, ?_⟩; simp [symR, jucovicVec]; sqrt3_close
  · refine ⟨7, ?_⟩; simp [symR, jucovicVec]

theorem perm_symRi (t h : ℝ) : ∀ i, ∃ j, symRi (jucovicVec t h j) = jucovicVec t h i := by
  have h3 := sqrt3_sq
  intro i
  fin_cases i
  · refine ⟨1, ?_⟩; simp [symRi, jucovicVec]; sqrt3_close
  · refine ⟨2, ?_⟩; simp [symRi, jucovicVec]; sqrt3_close
  · refine ⟨0, ?_⟩; simp [symRi, jucovicVec]
  · refine ⟨4, ?_⟩; simp [symRi, jucovicVec]
  · refine ⟨5, ?_⟩; simp [symRi, jucovicVec]; sqrt3_close
  · refine ⟨3, ?_⟩; simp [symRi, jucovicVec]; sqrt3_close
  · refine ⟨7, ?_⟩; simp [symRi, jucovicVec]
  · refine ⟨8, ?_⟩; simp [symRi, jucovicVec]; sqrt3_close
  · refine ⟨6, ?_⟩; simp [symRi, jucovicVec]; sqrt3_close

end Geodesy.Spherical
