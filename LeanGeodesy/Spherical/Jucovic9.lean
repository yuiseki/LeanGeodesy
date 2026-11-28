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

theorem sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

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

/-! ## Faces: a direction in the cone over a face sees one of its vertices -/

/-- If `x = l a + m b + n c` with `l, m, n ≥ 0`, and the plane `⟪N, ·⟫ = κ > 0`
through `a, b, c` is at distance at least `ρ` from the origin (`ρ ‖N‖ ≤ κ`), then
one of `a, b, c` has `ρ ‖x‖ ≤ ⟪·, x⟫`. -/
theorem face_support {a b c x N : E3} {l m n κ ρ : ℝ} (hl : 0 ≤ l) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hx : x = l • a + m • b + n • c) (ha : inner ℝ N a = κ) (hb : inner ℝ N b = κ)
    (hc : inner ℝ N c = κ) (hκ : 0 < κ) (hd : ρ * ‖N‖ ≤ κ) :
    ρ * ‖x‖ ≤ inner ℝ a x ∨ ρ * ‖x‖ ≤ inner ℝ b x ∨ ρ * ‖x‖ ≤ inner ℝ c x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hxx : ‖x‖ ^ 2 = l * inner ℝ a x + m * inner ℝ b x + n * inner ℝ c x := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 1 [hx]
    rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left]
  have hNx : inner ℝ N x = (l + m + n) * κ := by
    rw [hx, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, ha, hb, hc]
    ring
  have hCS : inner ℝ N x ≤ ‖N‖ * ‖x‖ := real_inner_le_norm N x
  have hN0 : N ≠ 0 := by
    intro h0; rw [h0, inner_zero_left] at ha; linarith
  have hNpos : 0 < ‖N‖ := norm_pos_iff.2 hN0
  have hsx : (l + m + n) * ρ ≤ ‖x‖ := by
    have : (l + m + n) * ρ * ‖N‖ ≤ ‖N‖ * ‖x‖ := by
      calc (l + m + n) * ρ * ‖N‖ = (l + m + n) * (ρ * ‖N‖) := by ring
        _ ≤ (l + m + n) * κ := mul_le_mul_of_nonneg_left hd (by linarith)
        _ = inner ℝ N x := hNx.symm
        _ ≤ ‖N‖ * ‖x‖ := hCS
    nlinarith
  rcases eq_or_lt_of_le (show 0 ≤ l + m + n by linarith) with hs | hs
  · have hl0 : l = 0 := by linarith
    have hm0 : m = 0 := by linarith
    have hn0 : n = 0 := by linarith
    have : x = 0 := by rw [hx, hl0, hm0, hn0]; simp
    rw [this, inner_zero_right, norm_zero, mul_zero] at h1
    exact lt_irrefl _ h1
  · set δ := min (min (ρ * ‖x‖ - inner ℝ a x) (ρ * ‖x‖ - inner ℝ b x)) (ρ * ‖x‖ - inner ℝ c x)
    have hδ : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
    have da : δ ≤ ρ * ‖x‖ - inner ℝ a x := (min_le_left _ _).trans (min_le_left _ _)
    have db : δ ≤ ρ * ‖x‖ - inner ℝ b x := (min_le_left _ _).trans (min_le_right _ _)
    have dc : δ ≤ ρ * ‖x‖ - inner ℝ c x := min_le_right _ _
    have hxn := norm_nonneg x
    nlinarith [mul_le_mul_of_nonneg_left da hl, mul_le_mul_of_nonneg_left db hm,
      mul_le_mul_of_nonneg_left dc hn, mul_pos hs hδ, mul_le_mul_of_nonneg_right hsx hxn]

private theorem mul_norm_le_of_sq {ρ κ : ℝ} {N : E3} (hκ : 0 ≤ κ)
    (h : ρ ^ 2 * ‖N‖ ^ 2 ≤ κ ^ 2) : ρ * ‖N‖ ≤ κ :=
  le_of_pow_le_pow_left₀ two_ne_zero hκ (by rw [mul_pow]; exact h)

/-- Close a field identity that may involve `√3 ^ 2`. -/
local macro "field3" : tactic =>
  `(tactic| (field_simp; ring_nf; try simp only [sqrt3_sq]; try ring_nf))

/-! ## The fundamental sector -/

/-- In the sector `0 ≤ y ≤ √3 x`, `z ≥ 0`, some point sees the direction `x` at
inner product at least `ρ ‖x‖`, as soon as the three faces through `A₀` in that
sector are at distance at least `ρ`: `ρ ≤ h` (top), `ρ² (4t² - 4t + 4) ≤ 3t²`
(side `A₀B₀C₀`), `ρ² (h² + (1 - t/2)²) ≤ h²` (slope `A₀B₂B₀`). -/
theorem jucovic_support_sector {t h ρ : ℝ} (ht0 : 0 < t) (hh : 0 < h)
    (hT : ρ ≤ h) (hV : ρ ^ 2 * (4 * t ^ 2 - 4 * t + 4) ≤ 3 * t ^ 2)
    (hU : ρ ^ 2 * (h ^ 2 + (1 - t / 2) ^ 2) ≤ h ^ 2) (x : E3) (hx1 : 0 ≤ x 1)
    (hx01 : x 1 ≤ √3 * x 0) (hx2 : 0 ≤ x 2) :
    ∃ i, ρ * ‖x‖ ≤ inner ℝ (jucovicVec t h i) x := by
  have h3 := sqrt3_sq
  have hs : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hx0 : 0 ≤ x 0 := by nlinarith
  have h3x : √3 * x 1 ≤ 3 * x 0 := by nlinarith
  set x0 := x 0
  set x1 := x 1
  set x2 := x 2
  have hxv : vec3 x0 x1 x2 = x := vec3_eta x
  by_cases hTc : 2 * h * x0 ≤ t * x2
  · -- the top face B₀B₁B₂
    have key := face_support (a := jucovicVec t h 3) (b := jucovicVec t h 4)
      (c := jucovicVec t h 5) (x := x) (N := vec3 0 0 1)
      (l := (t * x2 + h * x0 + h * √3 * x1) / (3 * h * t))
      (m := (t * x2 - 2 * h * x0) / (3 * h * t))
      (n := (t * x2 + h * x0 - h * √3 * x1) / (3 * h * t)) (κ := h) (ρ := ρ)
      (by positivity) (div_nonneg (by linarith) (by positivity))
      (div_nonneg (by nlinarith) (by positivity))
      (by
        rw [← hxv]; simp only [jucovicVec, Matrix.cons_val, vec3_smul, vec3_add]
        apply vec3_congr <;> field3)
      (by simp [jucovicVec, inner_vec3]) (by simp [jucovicVec, inner_vec3])
      (by simp [jucovicVec, inner_vec3]) hh
      (by
        have hN1 : ‖vec3 (0 : ℝ) 0 1‖ = 1 :=
          (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [norm_vec3_sq]; norm_num)
        rw [hN1, mul_one]; exact hT)
    rcases key with k | k | k
    · exact ⟨3, k⟩
    · exact ⟨4, k⟩
    · exact ⟨5, k⟩
  · push Not at hTc
    by_cases hVc : 3 * t * x2 ≤ 2 * h * √3 * x1
    · -- the side face A₀B₀C₀
      have key := face_support (a := jucovicVec t h 0) (b := jucovicVec t h 3)
        (c := jucovicVec t h 6) (x := x) (N := vec3 (√3 * t) (2 - t) 0)
        (l := (3 * x0 - √3 * x1) / 3)
        (m := (2 * h * √3 * x1 + 3 * t * x2) / (6 * h * t))
        (n := (2 * h * √3 * x1 - 3 * t * x2) / (6 * h * t)) (κ := √3 * t) (ρ := ρ)
        (div_nonneg (by linarith) (by norm_num)) (by positivity)
        (div_nonneg (by linarith) (by positivity))
        (by
          rw [← hxv]; simp only [jucovicVec, Matrix.cons_val, vec3_smul, vec3_add]
          apply vec3_congr <;> field3)
        (by simp [jucovicVec, inner_vec3]) (by simp [jucovicVec, inner_vec3]; ring)
        (by simp [jucovicVec, inner_vec3]; ring) (by positivity)
        (mul_norm_le_of_sq (by positivity) (by
          rw [norm_vec3_sq]
          have : (√3 * t) ^ 2 + (2 - t) ^ 2 + 0 ^ 2 = 4 * t ^ 2 - 4 * t + 4 := by
            rw [mul_pow, h3]; ring
          rw [this, mul_pow, h3]; linarith))
      rcases key with k | k | k
      · exact ⟨0, k⟩
      · exact ⟨3, k⟩
      · exact ⟨6, k⟩
    · -- the slope face A₀B₂B₀
      push Not at hVc
      have key := face_support (a := jucovicVec t h 0) (b := jucovicVec t h 5)
        (c := jucovicVec t h 3) (x := x) (N := vec3 h 0 (1 - t / 2))
        (l := (2 * h * x0 - t * x2) / (2 * h))
        (m := (3 * t * x2 - 2 * h * √3 * x1) / (6 * h * t))
        (n := (3 * t * x2 + 2 * h * √3 * x1) / (6 * h * t)) (κ := h) (ρ := ρ)
        (div_nonneg (by linarith) (by positivity))
        (div_nonneg (by linarith) (by positivity)) (by positivity)
        (by
          rw [← hxv]; simp only [jucovicVec, Matrix.cons_val, vec3_smul, vec3_add]
          apply vec3_congr <;> field3)
        (by simp [jucovicVec, inner_vec3]) (by simp [jucovicVec, inner_vec3]; ring)
        (by simp [jucovicVec, inner_vec3]; ring) hh
        (mul_norm_le_of_sq hh.le (by
          rw [norm_vec3_sq]
          have : h ^ 2 + 0 ^ 2 + (1 - t / 2) ^ 2 = h ^ 2 + (1 - t / 2) ^ 2 := by ring
          rw [this]; exact hU))
      rcases key with k | k | k
      · exact ⟨0, k⟩
      · exact ⟨5, k⟩
      · exact ⟨3, k⟩

/-! ## Every direction, by symmetry -/

/-- Under the same face conditions, every direction `x` has a point with
`ρ ‖x‖ ≤ ⟪p i, x⟫`: map `x` into the sector by the mirror in `z`, a rotation,
and the mirror in `y`. -/
theorem jucovic_support {t h ρ : ℝ} (ht0 : 0 < t) (hh : 0 < h) (hT : ρ ≤ h)
    (hV : ρ ^ 2 * (4 * t ^ 2 - 4 * t + 4) ≤ 3 * t ^ 2)
    (hU : ρ ^ 2 * (h ^ 2 + (1 - t / 2) ^ 2) ≤ h ^ 2) (x : E3) :
    ∃ i, ρ * ‖x‖ ≤ inner ℝ (jucovicVec t h i) x := by
  have h3 := sqrt3_sq
  have hs : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have core := jucovic_support_sector ht0 hh hT hV hU
  -- the last step: the mirror in `y`
  have stepS : ∀ y : E3, 0 ≤ y 2 → y 1 ≤ √3 * y 0 → -(y 1) ≤ √3 * y 0 →
      ∃ i, ρ * ‖y‖ ≤ inner ℝ (jucovicVec t h i) y := by
    intro y hy2 hy1 hy1'
    by_cases hpos : 0 ≤ y 1
    · exact core y hpos hy1 hy2
    · push Not at hpos
      refine support_of_sym inner_symS (perm_symS t h) y (core (symS y) ?_ ?_ ?_)
      · simp only [symS, vec3_1]; linarith
      · simp only [symS, vec3_0, vec3_1]; linarith
      · simp only [symS, vec3_2]; exact hy2
  -- a rotation brings the nearest of `A₀, A₁, A₂` to `A₀`
  have stepR : ∀ y : E3, 0 ≤ y 2 → ∃ i, ρ * ‖y‖ ≤ inner ℝ (jucovicVec t h i) y := by
    intro y hy2
    by_cases h01 : -(y 0) / 2 + √3 / 2 * y 1 ≤ y 0
    · by_cases h02 : -(y 0) / 2 - √3 / 2 * y 1 ≤ y 0
      · exact stepS y hy2 (by nlinarith) (by nlinarith)
      · push Not at h02
        refine support_of_sym inner_symR (perm_symR t h) y (stepS (symR y) ?_ ?_ ?_)
        · simp only [symR, vec3_2]; exact hy2
        · simp only [symR, vec3_0, vec3_1]; nlinarith
        · simp only [symR, vec3_0, vec3_1]; nlinarith
    · push Not at h01
      by_cases h12 : -(y 0) / 2 - √3 / 2 * y 1 ≤ -(y 0) / 2 + √3 / 2 * y 1
      · refine support_of_sym inner_symRi (perm_symRi t h) y (stepS (symRi y) ?_ ?_ ?_)
        · simp only [symRi, vec3_2]; exact hy2
        · simp only [symRi, vec3_0, vec3_1]; nlinarith
        · simp only [symRi, vec3_0, vec3_1]; nlinarith
      · push Not at h12
        refine support_of_sym inner_symR (perm_symR t h) y (stepS (symR y) ?_ ?_ ?_)
        · simp only [symR, vec3_2]; exact hy2
        · simp only [symR, vec3_0, vec3_1]; nlinarith
        · simp only [symR, vec3_0, vec3_1]; nlinarith
  by_cases hz : 0 ≤ x 2
  · exact stepR x hz
  · push Not at hz
    exact support_of_sym inner_symZ (perm_symZ t h) x
      (stepR (symZ x) (by simp only [symZ, vec3_2]; linarith))

/-! ## The covering radius of Jucovič's configuration -/

theorem jucovicStar_coe (i : Fin 9) : (jucovicStar i).1 = jucovicVec tStar hStar i := rfl

/-- Jucovič's configuration covers `S²` by caps of radius `arccos h⋆`. -/
theorem isCovering_jucovicStar : IsCovering jucovicStar (arccos hStar) := by
  have ht := tStar_mem
  have hq : 4 * tStar ^ 4 - 4 * tStar ^ 3 + 3 * tStar ^ 2 + 4 * tStar - 4 = 0 :=
    jucovicQuartic_tStar
  have h2 := hStar_sq
  have hpos := hStar_pos
  have hle : hStar ≤ 1 := by nlinarith [ht.1, ht.2]
  rw [isCovering_iff_inner _ (arccos_nonneg _) (arccos_le_pi _), cos_arccos (by linarith) hle]
  intro x
  obtain ⟨i, hi⟩ := jucovic_support (t := tStar) (h := hStar) (ρ := hStar)
    (by linarith [ht.1]) hpos le_rfl
    (by rw [h2]; linarith [hq])
    (by rw [h2]; nlinarith [ht.1, ht.2]) x.1
  refine ⟨i, ?_⟩
  rw [x.2, mul_one] at hi
  exact hi

/-- The north pole is a hole of depth `arccos h⋆`. -/
theorem jucovicStar_hole (i : Fin 9) : inner ℝ (jucovicStar i).1 (vec3 0 0 1) ≤ hStar := by
  have hpos := hStar_pos
  rw [jucovicStar_coe]
  fin_cases i <;> simp [jucovicVec, inner_vec3] <;> linarith

/-- The covering radius of Jucovič's configuration is exactly `arccos h⋆`, where
`h⋆ = √(1 - t⋆²)` and `t⋆` is the root of `4t⁴ - 4t³ + 3t² + 4t - 4` in
`(2/3, 1)` (numerically `45.8788…°`; not used in any proof). -/
theorem coveringRadius_jucovicStar :
    coveringRadius (by norm_num : 1 ≤ 9) jucovicStar = arccos hStar := by
  refine le_antisymm ((coveringRadius_le_iff _ _ _).2 isCovering_jucovicStar) ?_
  have hN : ‖vec3 (0 : ℝ) 0 1‖ = 1 :=
    (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [norm_vec3_sq]; norm_num)
  exact arccos_le_coveringRadius_of_hole _ _ ⟨vec3 0 0 1, hN⟩ jucovicStar_hole

/-! ## The fourteen faces

The hull of the nine points is the triaugmented triangular prism: two triangles
`B₀B₁B₂`, `C₀C₁C₂`, six slopes `AₖBₖ₋₁Bₖ`, `AₖCₖ₋₁Cₖ` and six sides `AₖBₖCₖ`,
`Aₖ₊₁BₖCₖ` (`9 - 21 + 14 = 2`). Each face is given by an outward normal `N`, an
offset `κ` and its three vertices; `jucovic_face_on` puts the vertices on the
plane `⟪N, ·⟫ = κ` and `jucovic_face_supporting` puts all nine points on the
inner side, for `1/2 ≤ t ≤ 1`. The distances `κ / ‖N‖` are `h` (triangles),
`h / √(h² + (1 - t/2)²)` (slopes) and `√3 t / (2 √(t² - t + 1))` (sides). That
the faces close up (every direction lies over one of them) is used in the form
`jucovic_support`: every direction sees a vertex at inner product at least
`ρ ‖x‖`. -/

/-- Outward normals of the fourteen faces. -/
noncomputable def jucovicFaceNormal (t h : ℝ) : Fin 14 → E3 :=
  ![vec3 0 0 1, vec3 0 0 (-1),
    vec3 h 0 (1 - t / 2), vec3 (-h / 2) (√3 / 2 * h) (1 - t / 2),
    vec3 (-h / 2) (-(√3 / 2 * h)) (1 - t / 2),
    vec3 h 0 (-(1 - t / 2)), vec3 (-h / 2) (√3 / 2 * h) (-(1 - t / 2)),
    vec3 (-h / 2) (-(√3 / 2 * h)) (-(1 - t / 2)),
    vec3 (√3 * t) (2 - t) 0, vec3 (-√3) (2 * t - 1) 0, vec3 (√3 * (1 - t)) (-(1 + t)) 0,
    vec3 (√3 * (1 - t)) (1 + t) 0, vec3 (-√3) (1 - 2 * t) 0, vec3 (√3 * t) (-(2 - t)) 0]

/-- Offsets of the fourteen face planes. -/
noncomputable def jucovicFaceOffset (t h : ℝ) : Fin 14 → ℝ :=
  ![h, h, h, h, h, h, h, h, √3 * t, √3 * t, √3 * t, √3 * t, √3 * t, √3 * t]

/-- Vertices of the fourteen faces (indices into `jucovicVec`). -/
def jucovicFaceVerts : Fin 14 → Fin 9 × Fin 9 × Fin 9 :=
  ![(3, 4, 5), (6, 7, 8), (0, 5, 3), (1, 3, 4), (2, 4, 5), (0, 8, 6), (1, 6, 7), (2, 7, 8),
    (0, 3, 6), (1, 4, 7), (2, 5, 8), (1, 3, 6), (2, 4, 7), (0, 5, 8)]

/-- The three vertices of each face lie on its plane. -/
theorem jucovic_face_on (t h : ℝ) (f : Fin 14) :
    inner ℝ (jucovicFaceNormal t h f) (jucovicVec t h (jucovicFaceVerts f).1) =
        jucovicFaceOffset t h f ∧
      inner ℝ (jucovicFaceNormal t h f) (jucovicVec t h (jucovicFaceVerts f).2.1) =
        jucovicFaceOffset t h f ∧
      inner ℝ (jucovicFaceNormal t h f) (jucovicVec t h (jucovicFaceVerts f).2.2) =
        jucovicFaceOffset t h f := by
  have h3 := sqrt3_sq
  fin_cases f <;>
    simp [jucovicFaceNormal, jucovicFaceOffset, jucovicFaceVerts, jucovicVec, inner_vec3] <;>
    (try refine ⟨?_, ?_, ?_⟩) <;> (try refine ⟨?_, ?_⟩) <;> ring_nf <;> (try simp only [h3]) <;>
    ring_nf

set_option maxHeartbeats 2000000 in
/-- Every face plane is a supporting plane of the nine points, for `1/2 ≤ t ≤ 1`.
(126 small polynomial inequalities; the heartbeat limit is raised for this one
declaration.) -/
theorem jucovic_face_supporting {t h : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t ≤ 1) (hh : 0 < h)
    (f : Fin 14) (i : Fin 9) :
    inner ℝ (jucovicFaceNormal t h f) (jucovicVec t h i) ≤ jucovicFaceOffset t h f := by
  have h3 := sqrt3_sq
  have hs : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have ht0 : 0 ≤ t := by linarith
  have a1 := mul_nonneg hs.le ht0
  have a2 := mul_nonneg hs.le (by linarith : (0 : ℝ) ≤ t - 1 / 2)
  have a3 := mul_nonneg a1 (by linarith : (0 : ℝ) ≤ 1 - t)
  have a4 := mul_nonneg a1 ht0
  have a5 := mul_nonneg hh.le ht0
  have a6 := mul_nonneg hh.le (by linarith : (0 : ℝ) ≤ 1 - t)
  have a7 := mul_nonneg hs.le (by linarith : (0 : ℝ) ≤ 1 - t)
  fin_cases f <;> fin_cases i <;>
    simp [jucovicFaceNormal, jucovicFaceOffset, jucovicVec, inner_vec3] <;>
    ring_nf <;> (try simp only [h3]) <;> nlinarith

/-! ## Optimality within the symmetric family -/

/-- The top face `B₀B₁B₂` is a supporting plane: `⟪(0,0,1), p⟫ ≤ h`. -/
theorem jucovic_top_valid {t h : ℝ} (hh : 0 < h) (i : Fin 9) :
    inner ℝ (vec3 0 0 1) (jucovicVec t h i) ≤ h := by
  fin_cases i <;> simp [jucovicVec, inner_vec3] <;> linarith

/-- The side face `A₀B₀C₀` is a supporting plane exactly when `t ≥ 1/2`; this is
the direction used: `⟪(√3 t, 2 - t, 0), p⟫ ≤ √3 t` for `1/2 ≤ t ≤ 1`. -/
theorem jucovic_side_valid {t h : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t ≤ 1) (i : Fin 9) :
    inner ℝ (vec3 (√3 * t) (2 - t) 0) (jucovicVec t h i) ≤ √3 * t := by
  have hs : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have ht0 : 0 ≤ t := by linarith
  have a1 := mul_nonneg hs.le ht0
  have a2 := mul_nonneg hs.le (by linarith : (0 : ℝ) ≤ t - 1 / 2)
  have a3 := mul_nonneg a1 (by linarith : (0 : ℝ) ≤ 1 - t)
  have a4 := mul_nonneg a1 ht0
  fin_cases i <;> simp [jucovicVec, inner_vec3] <;> nlinarith

/-- For `t ≤ 1/2` the equatorial direction between `A₀` and `A₁` is a hole of
depth `60°`: every point has `⟪p, (1/2, √3/2, 0)⟫ ≤ 1/2`. -/
theorem jucovic_equator_hole {t h : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (i : Fin 9) :
    inner ℝ (jucovicVec t h i) (vec3 (1 / 2) (√3 / 2) 0) ≤ 1 / 2 := by
  have h3 := sqrt3_sq
  have h3t : √3 ^ 2 * t = 3 * t := by rw [h3]
  fin_cases i <;> simp [jucovicVec, inner_vec3] <;> ring_nf <;> nlinarith

/-- The side distance grows with `t`: for `t ≤ t⋆`, `3t² ≤ h⋆² (4t² - 4t + 4)`. -/
theorem jucovic_side_mono {t : ℝ} (ht0 : 0 ≤ t) (htt : t ≤ tStar) :
    3 * t ^ 2 ≤ hStar ^ 2 * (4 * t ^ 2 - 4 * t + 4) := by
  have hts := tStar_mem
  have hq : 4 * tStar ^ 4 - 4 * tStar ^ 3 + 3 * tStar ^ 2 + 4 * tStar - 4 = 0 :=
    jucovicQuartic_tStar
  rw [hStar_sq]
  set D := 4 * t ^ 2 - 4 * t + 4
  set Ds := 4 * tStar ^ 2 - 4 * tStar + 4
  have hDs : 0 < Ds := by nlinarith
  have hstar : (1 - tStar ^ 2) * Ds = 3 * tStar ^ 2 := by linear_combination -hq
  have hfac : 0 ≤ (tStar - t) * (tStar + t - t * tStar) :=
    mul_nonneg (by linarith) (by nlinarith [hts.1, hts.2])
  have e : 3 * tStar ^ 2 * D - 3 * t ^ 2 * Ds = 12 * ((tStar - t) * (tStar + t - t * tStar)) := by
    ring
  have key : 3 * t ^ 2 * Ds ≤ (1 - tStar ^ 2) * D * Ds := by
    have : (1 - tStar ^ 2) * D * Ds = 3 * tStar ^ 2 * D := by
      rw [mul_right_comm, hstar]
    linarith
  exact le_of_mul_le_mul_right key hDs

/-- Within the family `jucovic t` (`0 < t < 1`, `h = √(1 - t²)`), no member covers
with a smaller radius than `t = t⋆`. This is a statement about this one-parameter
family of `D₃h`-symmetric configurations, not about all 9-point
configurations. -/
theorem coveringRadius_jucovicStar_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    coveringRadius (by norm_num : 1 ≤ 9) jucovicStar ≤
      coveringRadius (by norm_num : 1 ≤ 9) (jucovic t (by nlinarith)) := by
  rw [coveringRadius_jucovicStar]
  set p := jucovic t (by nlinarith)
  set r := coveringRadius (by norm_num : 1 ≤ 9) p
  have h0 := coveringRadius_nonneg (by norm_num : 1 ≤ 9) p
  have hπ := coveringRadius_le_pi (by norm_num : 1 ≤ 9) p
  have hcov : IsCovering p r := isCovering_coveringRadius _ p
  have hts := tStar_mem
  have hbr := tStar_bracket
  have h2 := hStar_sq
  have hps := hStar_pos
  set h := √(1 - t ^ 2) with hh_def
  have hhpos : 0 < h := Real.sqrt_pos.2 (by nlinarith)
  have hh2 : h ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  have h3 := sqrt3_sq
  have hpc : ∀ i, (p i).1 = jucovicVec t h i := fun i => rfl
  suffices hc : cos r ≤ hStar by
    calc arccos hStar ≤ arccos (cos r) := arccos_le_arccos_of_le hc
      _ = r := arccos_cos h0 hπ
  by_cases htt : tStar ≤ t
  · have hc := cos_mul_norm_le_of_halfSpace h0 hπ hcov (vec3 0 0 1) (c := h)
      (fun i => by rw [hpc]; exact jucovic_top_valid hhpos i)
    have hN : ‖vec3 (0 : ℝ) 0 1‖ = 1 :=
      (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [norm_vec3_sq]; norm_num)
    rw [hN, mul_one] at hc
    have : h ≤ hStar := by
      have : h ^ 2 ≤ hStar ^ 2 := by rw [hh2, h2]; nlinarith
      exact le_of_pow_le_pow_left₀ two_ne_zero hps.le this
    linarith
  · push Not at htt
    by_cases hhalf : 1 / 2 ≤ t
    · have hc := cos_mul_norm_le_of_halfSpace h0 hπ hcov (vec3 (√3 * t) (2 - t) 0)
        (c := √3 * t) (fun i => by rw [hpc]; exact jucovic_side_valid hhalf ht1.le i)
      have hN2 : ‖vec3 (√3 * t) (2 - t) 0‖ ^ 2 = 4 * t ^ 2 - 4 * t + 4 := by
        rw [norm_vec3_sq, mul_pow, h3]; ring
      have hmono := jucovic_side_mono ht0.le htt.le
      have hden : 0 < 4 * t ^ 2 - 4 * t + 4 := by nlinarith
      by_contra hgt
      push Not at hgt
      have hcr : 0 < cos r := lt_trans hps hgt
      have hsq : cos r ^ 2 * (4 * t ^ 2 - 4 * t + 4) ≤ 3 * t ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hc 2
        rw [mul_pow, hN2, mul_pow, h3] at this
        linarith
      have hgt2 : hStar ^ 2 < cos r ^ 2 := pow_lt_pow_left₀ hgt hps.le two_ne_zero
      have := mul_lt_mul_of_pos_right hgt2 hden
      linarith
    · push Not at hhalf
      have hu : ‖vec3 (1 / 2 : ℝ) (√3 / 2) 0‖ = 1 :=
        (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by
          rw [norm_vec3_sq]; linear_combination (1 / 4 : ℝ) * h3)
      have hc := cos_le_of_supportPlane h0 hπ hcov ⟨vec3 (1 / 2) (√3 / 2) 0, hu⟩ (c := 1 / 2)
        (fun i => by
          show inner ℝ (p i).1 (vec3 (1 / 2) (√3 / 2) 0) ≤ 1 / 2
          rw [hpc]; exact jucovic_equator_hole ht0.le hhalf.le i)
      have : 1 / 2 < hStar := by
        have : (1 / 2 : ℝ) ^ 2 < hStar ^ 2 := by rw [h2]; nlinarith
        exact lt_of_pow_lt_pow_left₀ 2 hps.le this
      linarith

/-- The ball of radius `h⋆` lies in the hull of Jucovič's configuration. -/
theorem closedBall_subset_hullOf_jucovicStar :
    Metric.closedBall (0 : E3) hStar ⊆ hullOf jucovicStar := by
  have hps := hStar_pos
  have hle : hStar ≤ 1 := by nlinarith [hStar_sq, tStar_mem.1, tStar_mem.2]
  have h := (isCovering_iff_closedBall_subset_hullOf jucovicStar (arccos_nonneg _)
    (arccos_le_pi_div_two.2 hps.le)).1 isCovering_jucovicStar
  rwa [cos_arccos (by linarith) hle] at h

/-! ## What remains: a conditional statement

Global optimality of Jucovič's configuration among all 9-point configurations
is not proved here. It would follow from the reduction below, which is an
explicit hypothesis, not an axiom and not a theorem of this file. It is not
Wimmer's theorem either: Wimmer (2017, abstract) determines the combinatorial
type of an optimal 9-point covering, and a combinatorial type does not fix the
symmetry. The reduction combines two steps, (1) an optimal configuration has
the combinatorial type of the triaugmented triangular prism, and (2) within
that type the optimum is attained in the `D₃h`-symmetric family `jucovic t`.
Step (1) is what the abstract of Wimmer 2017 reports (its proof is unread
here); step (2) is open. -/

/-- The reduction of the 9-point covering problem to the symmetric family. -/
def NinePointReduction : Prop :=
  ∀ p : Fin 9 → UnitSphere, ∃ t : ℝ, ∃ ht0 : 0 < t, ∃ ht1 : t < 1,
    coveringRadius (by norm_num : 1 ≤ 9) (jucovic t (by nlinarith)) ≤
      coveringRadius (by norm_num : 1 ≤ 9) p

/-- Conditional global optimality: if `NinePointReduction` holds, Jucovič's
configuration is an optimal 9-point covering. The hypothesis is an ordinary
argument; nothing here proves it. -/
theorem coveringRadius_jucovicStar_le_of_reduction (hred : NinePointReduction)
    (p : Fin 9 → UnitSphere) :
    coveringRadius (by norm_num : 1 ≤ 9) jucovicStar ≤ coveringRadius (by norm_num : 1 ≤ 9) p := by
  obtain ⟨t, ht0, ht1, h⟩ := hred p
  exact (coveringRadius_jucovicStar_le ht0 ht1).trans h

end Geodesy.Spherical
