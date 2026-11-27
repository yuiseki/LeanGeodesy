import LeanGeodesy.Spherical.Packing
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Three-point geometry on the unit sphere `S²`

This module formalizes the three-point inner-product geometry needed for the
Bachoc–Vallentin semidefinite programming bound on `S²`:

- `gramMatrix3 x y z`: the `3 × 3` Gram matrix of three unit vectors `x, y, z ∈ S²`,
  proved positive semidefinite (`gramMatrix3_posSemidef`);
- `gramDet3 u v t := 1 + 2 * u * v * t - u ^ 2 - v ^ 2 - t ^ 2`: the determinant of
  the `3 × 3` unit Gram matrix (`det_gramMatrix3`), proved nonnegative for all
  `x, y, z ∈ S²` (`gramDet3_nonneg`) and symmetric under all permutations of `(u, v, t)`;
- `InThreePointDomain s u v t`: the admissible region
  `{(u, v, t) ∈ [-1, s]³ : 1 + 2 u v t - u² - v² - t² ≥ 0}` for pairwise inner
  products of three distinct points in a spherical code with threshold `s`;
- `sum_offDiag_triples_split`: decomposes a double sum over `y, z ∈ C \ {x}` into
  the diagonal pairs (`y = z ≠ x`) and the pairwise distinct triples (`x, y, z` distinct).
-/

namespace Geodesy.Spherical

open scoped Matrix

/-! ## Three-point Gram matrix and determinant -/

/-- The `3 × 3` Gram matrix of three points `x, y, z ∈ UnitSphere`. -/
noncomputable def gramMatrix3 (x y z : UnitSphere) : Matrix (Fin 3) (Fin 3) ℝ :=
  let v : Fin 3 → E3 := ![x.1, y.1, z.1]
  Matrix.of fun i j => inner ℝ (v i) (v j)

/-- The `3 × 3` Gram matrix of any three points on `S²` is positive semidefinite. -/
theorem gramMatrix3_posSemidef (x y z : UnitSphere) :
    (gramMatrix3 x y z).PosSemidef := by
  let v : Fin 3 → E3 := ![x.1, y.1, z.1]
  refine ⟨?_, ?_⟩
  · ext i j
    simp [gramMatrix3, real_inner_comm]
  · intro c
    have hnonneg : 0 ≤ ‖∑ i : Fin 3, c i • v i‖ ^ 2 := sq_nonneg _
    have hexpand : ‖∑ i : Fin 3, c i • v i‖ ^ 2 =
        c.sum fun i ci => c.sum fun j cj => star ci * gramMatrix3 x y z i j * cj := by
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right]
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [star_trivial, gramMatrix3, Matrix.of_apply]
      ring
    linarith

/-- Determinant of the `3 × 3` unit Gram matrix with off-diagonal entries `u, v, t`:
`Δ(u, v, t) = 1 + 2 u v t - u² - v² - t²`. -/
def gramDet3 (u v t : ℝ) : ℝ :=
  1 + 2 * u * v * t - u ^ 2 - v ^ 2 - t ^ 2

theorem gramDet3_eq_factor (u v t : ℝ) :
    gramDet3 u v t = (1 - u ^ 2) * (1 - v ^ 2) - (t - u * v) ^ 2 := by
  unfold gramDet3
  ring

theorem gramDet3_swap_uv (u v t : ℝ) : gramDet3 v u t = gramDet3 u v t := by
  unfold gramDet3; ring

theorem gramDet3_swap_vt (u v t : ℝ) : gramDet3 u t v = gramDet3 u v t := by
  unfold gramDet3; ring

theorem gramDet3_swap_ut (u v t : ℝ) : gramDet3 t v u = gramDet3 u v t := by
  unfold gramDet3; ring

theorem gramDet3_cyc (u v t : ℝ) : gramDet3 v t u = gramDet3 u v t := by
  unfold gramDet3; ring

/-- The determinant of `gramMatrix3 x y z` equals `gramDet3 ⟪x, y⟫ ⟪x, z⟫ ⟪y, z⟫`. -/
theorem det_gramMatrix3 (x y z : UnitSphere) :
    (gramMatrix3 x y z).det =
      gramDet3 (inner ℝ x.1 y.1) (inner ℝ x.1 z.1) (inner ℝ y.1 z.1) := by
  rw [Matrix.det_fin_three]
  have hx : inner ℝ x.1 x.1 = 1 := Geodesic.inner_self_of_norm_one x.2
  have hy : inner ℝ y.1 y.1 = 1 := Geodesic.inner_self_of_norm_one y.2
  have hz : inner ℝ z.1 z.1 = 1 := Geodesic.inner_self_of_norm_one z.2
  have hyx : inner ℝ y.1 x.1 = inner ℝ x.1 y.1 := real_inner_comm x.1 y.1
  have hzx : inner ℝ z.1 x.1 = inner ℝ x.1 z.1 := real_inner_comm x.1 z.1
  have hzy : inner ℝ z.1 y.1 = inner ℝ y.1 z.1 := real_inner_comm y.1 z.1
  simp only [gramMatrix3, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hx, hy, hz, hyx, hzx, hzy, gramDet3]
  ring

/-- For any three points `x, y, z ∈ S²`,
`1 + 2 ⟪x,y⟫ ⟪x,z⟫ ⟪y,z⟫ - ⟪x,y⟫² - ⟪x,z⟫² - ⟪y,z⟫² ≥ 0`. -/
theorem gramDet3_nonneg (x y z : UnitSphere) :
    0 ≤ gramDet3 (inner ℝ x.1 y.1) (inner ℝ x.1 z.1) (inner ℝ y.1 z.1) := by
  rw [gramDet3_eq_factor]
  set u := inner ℝ x.1 y.1
  set v := inner ℝ x.1 z.1
  set t := inner ℝ y.1 z.1
  set yp : E3 := y.1 - u • x.1
  set zp : E3 := z.1 - v • x.1
  have hx : inner ℝ x.1 x.1 = 1 := Geodesic.inner_self_of_norm_one x.2
  have hy : inner ℝ y.1 y.1 = 1 := Geodesic.inner_self_of_norm_one y.2
  have hz : inner ℝ z.1 z.1 = 1 := Geodesic.inner_self_of_norm_one z.2
  have hyp : ‖yp‖ ^ 2 = 1 - u ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    have hyx : inner ℝ y.1 x.1 = u := real_inner_comm x.1 y.1
    simp only [yp, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hx, hy, hyx]
    change 1 - u * u - (u * u - u * (u * 1)) = 1 - u ^ 2
    ring
  have hzp : ‖zp‖ ^ 2 = 1 - v ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    have hzx : inner ℝ z.1 x.1 = v := real_inner_comm x.1 z.1
    simp only [zp, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hx, hz, hzx]
    change 1 - v * v - (v * v - v * (v * 1)) = 1 - v ^ 2
    ring
  have hinner : inner ℝ yp zp = t - u * v := by
    have hyx : inner ℝ y.1 x.1 = u := real_inner_comm x.1 y.1
    simp only [yp, zp, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hx, hyx]
    change t - u * v - (v * u - v * (u * 1)) = t - u * v
    ring
  have hcs : |inner ℝ yp zp| ≤ ‖yp‖ * ‖zp‖ := abs_real_inner_le_norm yp zp
  have hsq : (inner ℝ yp zp) ^ 2 ≤ (‖yp‖ * ‖zp‖) ^ 2 := by
    nlinarith [sq_abs (inner ℝ yp zp), abs_nonneg (inner ℝ yp zp), norm_nonneg yp, norm_nonneg zp]
  rw [mul_pow, hyp, hzp, hinner] at hsq
  linarith

/-- Nonnegativity of the Gram matrix determinant for any three points on `S²`. -/
theorem det_gramMatrix3_nonneg (x y z : UnitSphere) :
    0 ≤ (gramMatrix3 x y z).det := by
  rw [det_gramMatrix3]
  exact gramDet3_nonneg x y z

/-! ## Admissible domain for three-point inner products of a spherical code -/

/-- The admissible region `Δ(s)` for the pairwise inner products `(u, v, t)` of
three distinct points in a spherical code on `S²` with maximum inner product `s`. -/
def InThreePointDomain (s u v t : ℝ) : Prop :=
  -1 ≤ u ∧ u ≤ s ∧ -1 ≤ v ∧ v ≤ s ∧ -1 ≤ t ∧ t ≤ s ∧ 0 ≤ gramDet3 u v t

theorem InThreePointDomain.swap_uv {s u v t : ℝ} (h : InThreePointDomain s u v t) :
    InThreePointDomain s v u t := by
  rcases h with ⟨hu1, hu2, hv1, hv2, ht1, ht2, hd⟩
  exact ⟨hv1, hv2, hu1, hu2, ht1, ht2, by rwa [gramDet3_swap_uv]⟩

theorem InThreePointDomain.swap_vt {s u v t : ℝ} (h : InThreePointDomain s u v t) :
    InThreePointDomain s u t v := by
  rcases h with ⟨hu1, hu2, hv1, hv2, ht1, ht2, hd⟩
  exact ⟨hu1, hu2, ht1, ht2, hv1, hv2, by rwa [gramDet3_swap_vt]⟩

theorem InThreePointDomain.cyc {s u v t : ℝ} (h : InThreePointDomain s u v t) :
    InThreePointDomain s v t u := by
  rcases h with ⟨hu1, hu2, hv1, hv2, ht1, ht2, hd⟩
  exact ⟨hv1, hv2, ht1, ht2, hu1, hu2, by rwa [gramDet3_cyc]⟩

/-- Any three pairwise distinct points of a spherical code with threshold `s`
have pairwise inner products in `InThreePointDomain s`. -/
theorem inThreePointDomain_of_isSphericalCode {n : ℕ} {p : Fin n → UnitSphere} {s : ℝ}
    (hp : IsSphericalCode p s) {ℓ i j : Fin n} (hℓi : ℓ ≠ i) (hℓj : ℓ ≠ j) (hij : i ≠ j) :
    InThreePointDomain s (inner ℝ (p ℓ).1 (p i).1) (inner ℝ (p ℓ).1 (p j).1)
      (inner ℝ (p i).1 (p j).1) :=
  ⟨neg_one_le_inner (p ℓ) (p i), hp ℓ i hℓi,
   neg_one_le_inner (p ℓ) (p j), hp ℓ j hℓj,
   neg_one_le_inner (p i) (p j), hp i j hij,
   gramDet3_nonneg (p ℓ) (p i) (p j)⟩

/-- Basic nonnegative SOS multipliers on `InThreePointDomain s`. -/
theorem InThreePointDomain.g1_nonneg {s u v t : ℝ} (h : InThreePointDomain s u v t) :
    0 ≤ (s - u) * (u + 1) := by
  rcases h with ⟨hu1, hu2, _⟩
  exact mul_nonneg (by linarith) (by linarith)

theorem InThreePointDomain.g2_nonneg {s u v t : ℝ} (h : InThreePointDomain s u v t) :
    0 ≤ (s - v) * (s - t) := by
  rcases h with ⟨_, _, _, hv2, _, ht2, _⟩
  exact mul_nonneg (by linarith) (by linarith)

/-! ## Decomposition of triple sums into pairs and distinct triples -/

/-- For any function `g : Fin n → Fin n → Fin n → ℝ`, summing `g ℓ i j` over
`i ≠ ℓ` and `j ≠ ℓ` splits cleanly into the diagonal pairs `i = j ≠ ℓ` and
the pairwise distinct triples `(ℓ, i, j)`. -/
theorem sum_offDiag_triples_split {n : ℕ} (g : Fin n → Fin n → Fin n → ℝ) :
    (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ Finset.univ.erase ℓ, g ℓ i j) =
      (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, g ℓ i i) +
      (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ (Finset.univ.erase ℓ).erase i, g ℓ i j) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact (Finset.add_sum_erase (Finset.univ.erase ℓ) (fun j => g ℓ i j) hi).symm

/-- Symmetrization of a 3-variable function over all 6 permutations in `S₃`. -/
noncomputable def sym3 (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) : ℝ :=
  (f u v t + f u t v + f v u t + f v t u + f t u v + f t v u) / 6

theorem sym3_swap_uv (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    sym3 f v u t = sym3 f u v t := by
  unfold sym3; ring

theorem sym3_swap_vt (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    sym3 f u t v = sym3 f u v t := by
  unfold sym3; ring

theorem sym3_cyc (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    sym3 f v t u = sym3 f u v t := by
  unfold sym3; ring

/-- Summing a function of `(⟪p ℓ, p i⟫, ⟪p ℓ, p j⟫, ⟪p i, p j⟫)` over all
pairwise distinct triples `(ℓ, i, j)` equals summing its `S₃`-symmetrization `sym3 f`. -/
theorem sum_distinct_triples_eq_sym3 {n : ℕ} (p : Fin n → UnitSphere)
    (f : ℝ → ℝ → ℝ → ℝ) :
    (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ (Finset.univ.erase ℓ).erase i,
        f (inner ℝ (p ℓ).1 (p i).1) (inner ℝ (p ℓ).1 (p j).1) (inner ℝ (p i).1 (p j).1)) =
      (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ (Finset.univ.erase ℓ).erase i,
        sym3 f (inner ℝ (p ℓ).1 (p i).1) (inner ℝ (p ℓ).1 (p j).1) (inner ℝ (p i).1 (p j).1)) := by
  -- Express both sums over the `S₃`-invariant finset of pairwise distinct triples `T`.
  let T : Finset (Fin n × Fin n × Fin n) :=
    Finset.univ.filter fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2
  have hT : ∀ h : Fin n → Fin n → Fin n → ℝ,
      (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ (Finset.univ.erase ℓ).erase i, h ℓ i j) =
      ∑ t ∈ T, h t.1 t.2.1 t.2.2 := by
    intro h
    rw [Finset.sum_filter]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    have h1 : ∑ i : Fin n, (∑ j : Fin n, if ℓ ≠ i ∧ ℓ ≠ j ∧ i ≠ j then h ℓ i j else 0) =
        ∑ i : Fin n, if ℓ ≠ i then ∑ j ∈ (Finset.univ.erase ℓ).erase i, h ℓ i j else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hℓi : ℓ = i
      · subst hℓi; simp
      · simp only [hℓi, ne_eq, not_false_eq_true, true_and, ↓reduceIte]
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        tauto
    rw [h1, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfilt : Finset.univ.filter (fun i : Fin n => ℓ ≠ i) = Finset.univ.erase ℓ := by
      ext i; simp [ne_comm]
    rw [hfilt]
  rw [hT, hT]
  let g : Fin n × Fin n × Fin n → ℝ := fun t =>
    f (inner ℝ (p t.1).1 (p t.2.1).1) (inner ℝ (p t.1).1 (p t.2.2).1)
      (inner ℝ (p t.2.1).1 (p t.2.2).1)
  have hperm : ∀ (σ : Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n),
      (∀ t, t ∈ T ↔ σ t ∈ T) → ∑ t ∈ T, g (σ t) = ∑ t ∈ T, g t := by
    intro σ hσ
    refine Finset.sum_bij (fun t _ => σ t) (fun t ht => (hσ t).mp ht)
      (fun _ _ _ _ h => σ.injective h)
      (fun t ht => ⟨σ.symm t, (hσ (σ.symm t)).mpr (by simpa using ht), by simp⟩)
      (fun _ _ => rfl)
  -- The 6 permutations of `(ℓ, i, j)` induce the 6 permutations of `(u, v, t)`.
  have h1 : ∑ t ∈ T, f (inner ℝ (p t.1).1 (p t.2.1).1) (inner ℝ (p t.1).1 (p t.2.2).1)
      (inner ℝ (p t.2.1).1 (p t.2.2).1) = ∑ t ∈ T, g t := rfl
  have h2 : ∑ t ∈ T, f (inner ℝ (p t.1).1 (p t.2.1).1) (inner ℝ (p t.2.1).1 (p t.2.2).1)
      (inner ℝ (p t.1).1 (p t.2.2).1) = ∑ t ∈ T, g t := by
    let σ : Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n :=
      ⟨fun t => (t.2.1, t.1, t.2.2), fun t => (t.2.1, t.1, t.2.2),
       fun ⟨_, _, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩
    have := hperm σ (fun ⟨a, b, c⟩ => by
      simp only [T, σ, Equiv.coe_fn_mk, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩, fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩⟩)
    rw [← this]
    refine Finset.sum_congr rfl fun ⟨a, b, c⟩ _ => ?_
    simp only [g, σ, Equiv.coe_fn_mk, real_inner_comm (p b).1 (p a).1]
  have h3 : ∑ t ∈ T, f (inner ℝ (p t.1).1 (p t.2.2).1) (inner ℝ (p t.1).1 (p t.2.1).1)
      (inner ℝ (p t.2.1).1 (p t.2.2).1) = ∑ t ∈ T, g t := by
    let σ : Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n :=
      ⟨fun t => (t.1, t.2.2, t.2.1), fun t => (t.1, t.2.2, t.2.1),
       fun ⟨_, _, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩
    have := hperm σ (fun ⟨a, b, c⟩ => by
      simp only [T, σ, Equiv.coe_fn_mk, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩, fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩⟩)
    rw [← this]
    refine Finset.sum_congr rfl fun ⟨a, b, c⟩ _ => ?_
    simp only [g, σ, Equiv.coe_fn_mk, real_inner_comm (p c).1 (p b).1]
  have h4 : ∑ t ∈ T, f (inner ℝ (p t.1).1 (p t.2.2).1) (inner ℝ (p t.2.1).1 (p t.2.2).1)
      (inner ℝ (p t.1).1 (p t.2.1).1) = ∑ t ∈ T, g t := by
    let σ : Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n :=
      ⟨fun t => (t.2.2, t.1, t.2.1), fun t => (t.2.1, t.2.2, t.1),
       fun ⟨_, _, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩
    have := hperm σ (fun ⟨a, b, c⟩ => by
      simp only [T, σ, Equiv.coe_fn_mk, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2.symm, h3.symm, h1⟩, fun ⟨h1, h2, h3⟩ => ⟨h3, h1.symm, h2.symm⟩⟩)
    rw [← this]
    refine Finset.sum_congr rfl fun ⟨a, b, c⟩ _ => ?_
    simp only [g, σ, Equiv.coe_fn_mk, real_inner_comm (p c).1 (p a).1, real_inner_comm (p c).1 (p b).1]
  have h5 : ∑ t ∈ T, f (inner ℝ (p t.2.1).1 (p t.2.2).1) (inner ℝ (p t.1).1 (p t.2.1).1)
      (inner ℝ (p t.1).1 (p t.2.2).1) = ∑ t ∈ T, g t := by
    let σ : Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n :=
      ⟨fun t => (t.2.1, t.2.2, t.1), fun t => (t.2.2, t.1, t.2.1),
       fun ⟨_, _, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩
    have := hperm σ (fun ⟨a, b, c⟩ => by
      simp only [T, σ, Equiv.coe_fn_mk, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h3, h1.symm, h2.symm⟩, fun ⟨h1, h2, h3⟩ => ⟨h2.symm, h3.symm, h1⟩⟩)
    rw [← this]
    refine Finset.sum_congr rfl fun ⟨a, b, c⟩ _ => ?_
    simp only [g, σ, Equiv.coe_fn_mk, real_inner_comm (p b).1 (p a).1, real_inner_comm (p c).1 (p a).1]
  have h6 : ∑ t ∈ T, f (inner ℝ (p t.2.1).1 (p t.2.2).1) (inner ℝ (p t.1).1 (p t.2.2).1)
      (inner ℝ (p t.1).1 (p t.2.1).1) = ∑ t ∈ T, g t := by
    let σ : Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n :=
      ⟨fun t => (t.2.2, t.2.1, t.1), fun t => (t.2.2, t.2.1, t.1),
       fun ⟨_, _, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩
    have := hperm σ (fun ⟨a, b, c⟩ => by
      simp only [T, σ, Equiv.coe_fn_mk, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h3.symm, h2.symm, h1.symm⟩, fun ⟨h1, h2, h3⟩ => ⟨h3.symm, h2.symm, h1.symm⟩⟩)
    rw [← this]
    refine Finset.sum_congr rfl fun ⟨a, b, c⟩ _ => ?_
    simp only [g, σ, Equiv.coe_fn_mk, real_inner_comm (p c).1 (p b).1, real_inner_comm (p c).1 (p a).1,
      real_inner_comm (p b).1 (p a).1]
  simp only [sym3]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2, h3, h4, h5, h6]
  ring

end Geodesy.Spherical
