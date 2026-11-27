import LeanGeodesy.Spherical.Packing

/-!
# Delsarte linear programming bound on `S²` and Tammes `N = 12`

This module formalizes the Delsarte–Goethals–Seidel linear programming bound on
the two-sphere `S²` for polynomials of degree `≤ 4` in the Legendre basis, and
applies it to prove unconditional exact optimality of the regular icosahedron
for the Tammes problem at `N = 12`:

- `legendreP`: Legendre polynomials `P₀, P₁, P₂, P₃, P₄`;
- `sum_legendreP_nonneg`: positive semidefiniteness
  `∑ i, ∑ j, Pₖ(⟪p i, p j⟫) ≥ 0` for `k = 0, 1, 2, 3, 4`, proved directly via
  traceless symmetric harmonic tensors on `E3`;
- `delsarte_bound`: reusable spherical code upper bound `n ≤ f(1) / c₀` for any
  Legendre combination `f(t) = ∑ k, c k * Pₖ(t)` with `c 0 > 0`, `c k ≥ 0`, and
  `f(t) ≤ 0` on `[-1, s]`;
- `delsarte_offdiag_zero_of_tight`: equality characterization — when
  `(n : ℝ) * c 0 = f 1`, every distinct pair `i ≠ j` satisfies `f(⟪p i, p j⟫) = 0`;
- `icosahedron12`: exact algebraic coordinates of the 12 vertices of the regular
  icosahedron on `S²`;
- `tammes_12_optimal`:
  `(∃ p : Fin 12 → UnitSphere, IsSeparated p θ) ↔ θ ≤ arccos (1 / √5)`.
-/

namespace Geodesy.Spherical

open Real Geodesic

/-! ## Legendre polynomials `P₀, ..., P₄` -/

/-- The Legendre polynomials `P₀, P₁, P₂, P₃, P₄` (zonal spherical harmonics on `S²`). -/
noncomputable def legendreP : Fin 5 → ℝ → ℝ
  | ⟨0, _⟩, _ => 1
  | ⟨1, _⟩, t => t
  | ⟨2, _⟩, t => (3 * t ^ 2 - 1) / 2
  | ⟨3, _⟩, t => (5 * t ^ 3 - 3 * t) / 2
  | ⟨4, _⟩, t => (35 * t ^ 4 - 30 * t ^ 2 + 3) / 8

@[simp] theorem legendreP_one (k : Fin 5) : legendreP k 1 = 1 := by
  fin_cases k <;> norm_num [legendreP]

/-- Evaluate a linear combination `∑ k, c k * Pₖ(t)`. -/
noncomputable def legendreEval (c : Fin 5 → ℝ) (t : ℝ) : ℝ :=
  ∑ k : Fin 5, c k * legendreP k t

theorem legendreEval_one (c : Fin 5 → ℝ) : legendreEval c 1 = ∑ k : Fin 5, c k := by
  simp [legendreEval]

/-! ## Positive semidefiniteness of `P₀, ..., P₄` on `S²` -/

private def kronecker (a b : Fin 3) : ℝ := if a = b then 1 else 0

private theorem sum_coord_mul (x y : E3) : ∑ a : Fin 3, x a * y a = inner ℝ x y := by
  rw [← vec3_eta x, ← vec3_eta y, inner_vec3, Fin.sum_univ_three]
  simp only [vec3_0, vec3_1, vec3_2]

private theorem sum_coord_sq (x : UnitSphere) : ∑ a : Fin 3, x.1 a * x.1 a = 1 := by
  rw [sum_coord_mul, Geodesic.inner_self_of_norm_one x.2]

private theorem sum_kronecker_mul (f : Fin 3 → ℝ) (a : Fin 3) :
    ∑ b : Fin 3, kronecker a b * f b = f a := by
  fin_cases a <;> simp [kronecker]

private theorem sum_kronecker_mul_left (f : Fin 3 → ℝ) (b : Fin 3) :
    ∑ a : Fin 3, kronecker a b * f a = f b := by
  fin_cases b <;> simp [kronecker]

private theorem sum_pair_nonneg_of_feature {n : ℕ} {ι : Type*} [Fintype ι]
    (p : Fin n → UnitSphere) (g : UnitSphere → UnitSphere → ℝ)
    (φ : UnitSphere → ι → ℝ) {α : ℝ} (hα : 0 < α)
    (hfeat : ∀ x y : UnitSphere, ∑ a : ι, φ x a * φ y a = α * g x y) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, g (p i) (p j) := by
  have hsq : 0 ≤ ∑ a : ι, (∑ i : Fin n, φ (p i) a) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have heq : ∑ a : ι, (∑ i : Fin n, φ (p i) a) ^ 2 =
      α * ∑ i : Fin n, ∑ j : Fin n, g (p i) (p j) := by
    calc ∑ a : ι, (∑ i : Fin n, φ (p i) a) ^ 2
        = ∑ a : ι, ∑ i : Fin n, ∑ j : Fin n, φ (p i) a * φ (p j) a := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [sq, Finset.sum_mul_sum]
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ a : ι, φ (p i) a * φ (p j) a := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i : Fin n, ∑ j : Fin n, α * g (p i) (p j) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hfeat (p i) (p j)
      _ = α * ∑ i : Fin n, ∑ j : Fin n, g (p i) (p j) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  nlinarith

/-- Degree-2 harmonic (traceless symmetric) tensor on `E3`. -/
private noncomputable def tensor2 (x : E3) (ab : Fin 3 × Fin 3) : ℝ :=
  x ab.1 * x ab.2 - (1 / 3) * kronecker ab.1 ab.2

private theorem sum_tensor2_mul (x y : UnitSphere) :
    ∑ ab : Fin 3 × Fin 3, tensor2 x.1 ab * tensor2 y.1 ab =
      (2 / 3) * legendreP 2 (inner ℝ x.1 y.1) := by
  rw [Fintype.sum_prod_type]
  have hx := norm_sq_eq x.1
  rw [x.2, one_pow] at hx
  have hy := norm_sq_eq y.1
  rw [y.2, one_pow] at hy
  have hxy : inner ℝ x.1 y.1 = x.1 0 * y.1 0 + x.1 1 * y.1 1 + x.1 2 * y.1 2 := by
    rw [← sum_coord_mul, Fin.sum_univ_three]
  simp only [tensor2, kronecker, legendreP, Fin.sum_univ_three, hxy, ↓reduceIte, Fin.isValue,
    Fin.reduceEq]
  linear_combination (1 / 3 : ℝ) * hx + (1 / 3 : ℝ) * hy

/-- Degree-3 harmonic (traceless symmetric) tensor on `E3`. -/
private noncomputable def tensor3 (x : E3) (abc : Fin 3 × Fin 3 × Fin 3) : ℝ :=
  x abc.1 * x abc.2.1 * x abc.2.2 -
    (1 / 5) * (kronecker abc.1 abc.2.1 * x abc.2.2 +
               kronecker abc.2.1 abc.2.2 * x abc.1 +
               kronecker abc.2.2 abc.1 * x abc.2.1)

private theorem sum_tensor3_diag_12 (x : UnitSphere) (c : Fin 3) :
    ∑ a : Fin 3, tensor3 x.1 (a, a, c) = 0 := by
  have hkr : ∑ a : Fin 3, kronecker a a = 3 := by simp [kronecker]
  have h1 : ∑ a : Fin 3, x.1 a * x.1 a * x.1 c = x.1 c := by
    rw [← Finset.sum_mul, sum_coord_sq x, one_mul]
  have h2 : ∑ a : Fin 3, kronecker a a * x.1 c = 3 * x.1 c := by
    rw [← Finset.sum_mul, hkr]
  have h3 : ∑ a : Fin 3, kronecker a c * x.1 a = x.1 c :=
    sum_kronecker_mul_left (fun a => x.1 a) c
  have h4 : ∑ a : Fin 3, kronecker c a * x.1 a = x.1 c :=
    sum_kronecker_mul (fun a => x.1 a) c
  have hsplit : ∀ a : Fin 3, tensor3 x.1 (a, a, c) =
      x.1 a * x.1 a * x.1 c -
      (1 / 5) * (kronecker a a * x.1 c + kronecker a c * x.1 a + kronecker c a * x.1 a) :=
    fun a => by simp only [tensor3]
  simp_rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
    h1, h2, h3, h4]
  ring

private theorem tensor3_swap12 (x : E3) (a b c : Fin 3) :
    tensor3 x (b, a, c) = tensor3 x (a, b, c) := by
  simp only [tensor3, kronecker, eq_comm]; ring

private theorem tensor3_swap23 (x : E3) (a b c : Fin 3) :
    tensor3 x (a, c, b) = tensor3 x (a, b, c) := by
  simp only [tensor3, kronecker, eq_comm]; ring

private theorem sum_tensor3_mul (x y : UnitSphere) :
    ∑ abc : Fin 3 × Fin 3 × Fin 3, tensor3 x.1 abc * tensor3 y.1 abc =
      (2 / 5) * legendreP 3 (inner ℝ x.1 y.1) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  -- Contractions of `tensor3 x` against `kronecker` terms in `tensor3 y` vanish by tracelessness.
  have hvan12 : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      tensor3 x.1 (a, b, c) * (kronecker a b * y.1 c) = 0 := by
    have hstep : ∀ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        tensor3 x.1 (a, b, c) * (kronecker a b * y.1 c) =
        ∑ c : Fin 3, tensor3 x.1 (a, a, c) * y.1 c := fun a => by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have := sum_kronecker_mul (fun b => tensor3 x.1 (a, b, c) * y.1 c) a
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    simp_rw [hstep]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun c _ => by rw [← Finset.sum_mul, sum_tensor3_diag_12 x c, zero_mul]
  have hvan23 : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      tensor3 x.1 (a, b, c) * (kronecker b c * y.1 a) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    have : ∀ b : Fin 3, ∑ c : Fin 3, tensor3 x.1 (a, b, c) * (kronecker b c * y.1 a) =
        tensor3 x.1 (b, b, a) * y.1 a := fun b => by
      have := sum_kronecker_mul (fun c => tensor3 x.1 (a, b, c) * y.1 a) b
      have hsym : tensor3 x.1 (a, b, b) = tensor3 x.1 (b, b, a) := by
        rw [tensor3_swap12, tensor3_swap23]
      simpa [hsym, mul_comm, mul_left_comm, mul_assoc] using this
    simp_rw [this, ← Finset.sum_mul, sum_tensor3_diag_12 x a, zero_mul]
  have hvan31 : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      tensor3 x.1 (a, b, c) * (kronecker c a * y.1 b) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : ∀ a : Fin 3, ∑ c : Fin 3, tensor3 x.1 (a, b, c) * (kronecker c a * y.1 b) =
        tensor3 x.1 (a, a, b) * y.1 b := fun a => by
      have := sum_kronecker_mul_left (fun c => tensor3 x.1 (a, b, c) * y.1 b) a
      have hsym : tensor3 x.1 (a, b, a) = tensor3 x.1 (a, a, b) := tensor3_swap23 x.1 a a b
      simpa [hsym, mul_comm, mul_left_comm, mul_assoc] using this
    simp_rw [this, ← Finset.sum_mul, sum_tensor3_diag_12 x b, zero_mul]
  -- Reduce `⟨T₃(x), T₃(y)⟩` to `⟨T₃(x), y^{\otimes 3}⟩`.
  have hred : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      tensor3 x.1 (a, b, c) * tensor3 y.1 (a, b, c) =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        tensor3 x.1 (a, b, c) * (y.1 a * y.1 b * y.1 c) := by
    have hsplit : ∀ a b c : Fin 3,
        tensor3 x.1 (a, b, c) * tensor3 y.1 (a, b, c) =
          tensor3 x.1 (a, b, c) * (y.1 a * y.1 b * y.1 c) -
          (1 / 5) * (tensor3 x.1 (a, b, c) * (kronecker a b * y.1 c) +
                     tensor3 x.1 (a, b, c) * (kronecker b c * y.1 a) +
                     tensor3 x.1 (a, b, c) * (kronecker c a * y.1 b)) := fun a b c => by
      simp only [tensor3]; ring
    simp_rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
      hvan12, hvan23, hvan31]
    ring
  rw [hred]
  -- Evaluate `⟨T₃(x), y^{\otimes 3}⟩ = t³ - (3/5) t`.
  have h1 : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      (x.1 a * x.1 b * x.1 c) * (y.1 a * y.1 b * y.1 c) = inner ℝ x.1 y.1 ^ 3 := by
    have : ∀ a b c : Fin 3, (x.1 a * x.1 b * x.1 c) * (y.1 a * y.1 b * y.1 c) =
        (x.1 a * y.1 a) * ((x.1 b * y.1 b) * (x.1 c * y.1 c)) := fun _ _ _ => by ring
    simp_rw [this, ← Finset.mul_sum, sum_coord_mul, ← Finset.sum_mul, sum_coord_mul]
    ring
  have h2 : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      (kronecker a b * x.1 c) * (y.1 a * y.1 b * y.1 c) = inner ℝ x.1 y.1 := by
    have : ∀ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        (kronecker a b * x.1 c) * (y.1 a * y.1 b * y.1 c) =
        (y.1 a * y.1 a) * inner ℝ x.1 y.1 := fun a => by
      have hb : ∀ b : Fin 3, ∑ c : Fin 3, (kronecker a b * x.1 c) * (y.1 a * y.1 b * y.1 c) =
          kronecker a b * (y.1 a * y.1 b * inner ℝ x.1 y.1) := fun b => by
        rw [← sum_coord_mul, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
      simp_rw [hb]
      exact sum_kronecker_mul (fun b => y.1 a * y.1 b * inner ℝ x.1 y.1) a
    simp_rw [this, ← Finset.sum_mul, sum_coord_sq y, one_mul]
  have h3 : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      (kronecker b c * x.1 a) * (y.1 a * y.1 b * y.1 c) = inner ℝ x.1 y.1 := by
    have : ∀ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        (kronecker b c * x.1 a) * (y.1 a * y.1 b * y.1 c) = x.1 a * y.1 a := fun a => by
      have hb : ∀ b : Fin 3, ∑ c : Fin 3, (kronecker b c * x.1 a) * (y.1 a * y.1 b * y.1 c) =
          (y.1 b * y.1 b) * (x.1 a * y.1 a) := fun b => by
        have := sum_kronecker_mul (fun c => x.1 a * y.1 a * y.1 b * y.1 c) b
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      simp_rw [hb, ← Finset.sum_mul, sum_coord_sq y, one_mul]
    simp_rw [this, sum_coord_mul]
  have h4 : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      (kronecker c a * x.1 b) * (y.1 a * y.1 b * y.1 c) = inner ℝ x.1 y.1 := by
    rw [Finset.sum_comm]
    have : ∀ b : Fin 3, ∑ a : Fin 3, ∑ c : Fin 3,
        (kronecker c a * x.1 b) * (y.1 a * y.1 b * y.1 c) = x.1 b * y.1 b := fun b => by
      have ha : ∀ a : Fin 3, ∑ c : Fin 3, (kronecker c a * x.1 b) * (y.1 a * y.1 b * y.1 c) =
          (y.1 a * y.1 a) * (x.1 b * y.1 b) := fun a => by
        have := sum_kronecker_mul_left (fun c => x.1 b * y.1 a * y.1 b * y.1 c) a
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      simp_rw [ha, ← Finset.sum_mul, sum_coord_sq y, one_mul]
    simp_rw [this, sum_coord_mul]
  have hsplit' : ∀ a b c : Fin 3,
      tensor3 x.1 (a, b, c) * (y.1 a * y.1 b * y.1 c) =
        (x.1 a * x.1 b * x.1 c) * (y.1 a * y.1 b * y.1 c) -
        (1 / 5) * ((kronecker a b * x.1 c) * (y.1 a * y.1 b * y.1 c) +
                   (kronecker b c * x.1 a) * (y.1 a * y.1 b * y.1 c) +
                   (kronecker c a * x.1 b) * (y.1 a * y.1 b * y.1 c)) := fun a b c => by
    simp only [tensor3]; ring
  simp_rw [hsplit', Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
    h1, h2, h3, h4]
  simp only [legendreP]
  ring

/-- Degree-4 harmonic (traceless symmetric) tensor on `E3`. -/
private noncomputable def tensor4 (x : E3) (abcd : Fin 3 × Fin 3 × Fin 3 × Fin 3) : ℝ :=
  let a := abcd.1; let b := abcd.2.1; let c := abcd.2.2.1; let d := abcd.2.2.2
  x a * x b * x c * x d -
    (1 / 7) * (kronecker a b * x c * x d + kronecker a c * x b * x d +
               kronecker a d * x b * x c + kronecker b c * x a * x d +
               kronecker b d * x a * x c + kronecker c d * x a * x b) +
    (1 / 35) * (kronecker a b * kronecker c d + kronecker a c * kronecker b d +
                kronecker a d * kronecker b c)

private theorem sum_tensor4_diag_12 (x : UnitSphere) (c d : Fin 3) :
    ∑ a : Fin 3, tensor4 x.1 (a, a, c, d) = 0 := by
  have hkr : ∑ a : Fin 3, kronecker a a = 3 := by simp [kronecker]
  have h1 : ∑ a : Fin 3, x.1 a * x.1 a * x.1 c * x.1 d = x.1 c * x.1 d := by
    have : ∀ a : Fin 3, x.1 a * x.1 a * x.1 c * x.1 d = (x.1 a * x.1 a) * (x.1 c * x.1 d) :=
      fun _ => by ring
    simp_rw [this, ← Finset.sum_mul, sum_coord_sq x, one_mul]
  have h2 : ∑ a : Fin 3, kronecker a a * x.1 c * x.1 d = 3 * (x.1 c * x.1 d) := by
    have : ∀ a : Fin 3, kronecker a a * x.1 c * x.1 d = kronecker a a * (x.1 c * x.1 d) :=
      fun _ => by ring
    simp_rw [this, ← Finset.sum_mul, hkr]
  have h3 : ∑ a : Fin 3, kronecker a c * x.1 a * x.1 d = x.1 c * x.1 d := by
    have := sum_kronecker_mul_left (fun a => x.1 a * x.1 d) c
    simpa [mul_assoc] using this
  have h4 : ∑ a : Fin 3, kronecker a d * x.1 a * x.1 c = x.1 c * x.1 d := by
    have := sum_kronecker_mul_left (fun a => x.1 a * x.1 c) d
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have h5 : ∑ a : Fin 3, kronecker c d * x.1 a * x.1 a = kronecker c d := by
    have : ∀ a : Fin 3, kronecker c d * x.1 a * x.1 a = (x.1 a * x.1 a) * kronecker c d :=
      fun _ => by ring
    simp_rw [this, ← Finset.sum_mul, sum_coord_sq x, one_mul]
  have h6 : ∑ a : Fin 3, kronecker a a * kronecker c d = 3 * kronecker c d := by
    rw [← Finset.sum_mul, hkr]
  have h7 : ∑ a : Fin 3, kronecker a c * kronecker a d = kronecker c d :=
    sum_kronecker_mul_left (fun a => kronecker a d) c
  have hsplit : ∀ a : Fin 3, tensor4 x.1 (a, a, c, d) =
      x.1 a * x.1 a * x.1 c * x.1 d -
      (1 / 7) * (kronecker a a * x.1 c * x.1 d + 2 * (kronecker a c * x.1 a * x.1 d) +
                 2 * (kronecker a d * x.1 a * x.1 c) + kronecker c d * x.1 a * x.1 a) +
      (1 / 35) * (kronecker a a * kronecker c d + 2 * (kronecker a c * kronecker a d)) := fun a => by
    simp only [tensor4]; ring
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, h3, h4, h5, h6, h7]
  ring

private theorem tensor4_swap12 (x : E3) (a b c d : Fin 3) :
    tensor4 x (b, a, c, d) = tensor4 x (a, b, c, d) := by
  simp only [tensor4, kronecker, eq_comm]; ring

private theorem tensor4_swap23 (x : E3) (a b c d : Fin 3) :
    tensor4 x (a, c, b, d) = tensor4 x (a, b, c, d) := by
  simp only [tensor4, kronecker, eq_comm]; ring

private theorem tensor4_swap34 (x : E3) (a b c d : Fin 3) :
    tensor4 x (a, b, d, c) = tensor4 x (a, b, c, d) := by
  have hcd : kronecker d c = kronecker c d := by simp only [kronecker, eq_comm]
  simp only [tensor4, hcd]
  ring

private theorem sum_tensor4_mul (x y : UnitSphere) :
    ∑ abcd : Fin 3 × Fin 3 × Fin 3 × Fin 3, tensor4 x.1 abcd * tensor4 y.1 abcd =
      (8 / 35) * legendreP 4 (inner ℝ x.1 y.1) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  -- Any contraction of `tensor4 x` against a Kronecker delta vanishes by tracelessness.
  have hvan_ab : ∀ g : Fin 3 → Fin 3 → ℝ,
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (kronecker a b * g c d) = 0 := by
    intro g
    have hstep : ∀ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (kronecker a b * g c d) =
        ∑ c : Fin 3, ∑ d : Fin 3, tensor4 x.1 (a, a, c, d) * g c d := fun a => by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      have := sum_kronecker_mul (fun b => tensor4 x.1 (a, b, c, d) * g c d) a
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    simp_rw [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [← Finset.sum_mul, sum_tensor4_diag_12 x c d, zero_mul]
  have hvan_ac : ∀ g : Fin 3 → Fin 3 → ℝ,
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (kronecker a c * g b d) = 0 := by
    intro g
    have heq : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (kronecker a c * g b d) =
        ∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, c, b, d) * (kronecker a c * g b d) :=
      Finset.sum_congr rfl fun a _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun d _ => by rw [tensor4_swap23]
    rw [heq]
    exact hvan_ab g
  have hvan_ad : ∀ g : Fin 3 → Fin 3 → ℝ,
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (kronecker a d * g b c) = 0 := by
    intro g
    have heq : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (kronecker a d * g b c) =
        ∑ a : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3, ∑ c : Fin 3,
        tensor4 x.1 (a, b, d, c) * (kronecker a d * g b c) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by
          rw [tensor4_swap34]
    rw [heq]
    exact hvan_ac g
  have hvan_bc : ∀ g : Fin 3 → Fin 3 → ℝ,
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (kronecker b c * g a d) = 0 := by
    intro g
    rw [Finset.sum_comm]
    have heq : ∑ b : Fin 3, ∑ a : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (kronecker b c * g a d) =
        ∑ b : Fin 3, ∑ a : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (b, a, c, d) * (kronecker b c * g a d) :=
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
          rw [tensor4_swap12]
    rw [heq]
    exact hvan_ac g
  have hvan_bd : ∀ g : Fin 3 → Fin 3 → ℝ,
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (kronecker b d * g a c) = 0 := by
    intro g
    rw [Finset.sum_comm]
    have heq : ∑ b : Fin 3, ∑ a : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (kronecker b d * g a c) =
        ∑ b : Fin 3, ∑ a : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (b, a, c, d) * (kronecker b d * g a c) :=
      Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
          rw [tensor4_swap12]
    rw [heq]
    exact hvan_ad g
  have hvan_cd : ∀ g : Fin 3 → Fin 3 → ℝ,
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (kronecker c d * g a b) = 0 := by
    intro g
    have heq : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (kronecker c d * g a b) =
        ∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, c, b, d) * (kronecker c d * g a b) :=
      Finset.sum_congr rfl fun a _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun d _ => by rw [tensor4_swap23]
    rw [heq]
    exact hvan_bd (fun a b => g a b)
  -- Reduce `⟨T₄(x), T₄(y)⟩` to `⟨T₄(x), y^{\otimes 4}⟩`.
  have hred : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      tensor4 x.1 (a, b, c, d) * tensor4 y.1 (a, b, c, d) =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        tensor4 x.1 (a, b, c, d) * (y.1 a * y.1 b * y.1 c * y.1 d) := by
    have hsplit : ∀ a b c d : Fin 3,
        tensor4 x.1 (a, b, c, d) * tensor4 y.1 (a, b, c, d) =
          tensor4 x.1 (a, b, c, d) * (y.1 a * y.1 b * y.1 c * y.1 d) -
          (1 / 7) * (tensor4 x.1 (a, b, c, d) * (kronecker a b * (y.1 c * y.1 d)) +
                     tensor4 x.1 (a, b, c, d) * (kronecker a c * (y.1 b * y.1 d)) +
                     tensor4 x.1 (a, b, c, d) * (kronecker a d * (y.1 b * y.1 c)) +
                     tensor4 x.1 (a, b, c, d) * (kronecker b c * (y.1 a * y.1 d)) +
                     tensor4 x.1 (a, b, c, d) * (kronecker b d * (y.1 a * y.1 c)) +
                     tensor4 x.1 (a, b, c, d) * (kronecker c d * (y.1 a * y.1 b))) +
          (1 / 35) * (tensor4 x.1 (a, b, c, d) * (kronecker a b * kronecker c d) +
                      tensor4 x.1 (a, b, c, d) * (kronecker a c * kronecker b d) +
                      tensor4 x.1 (a, b, c, d) * (kronecker a d * kronecker b c)) := fun a b c d => by
      simp only [tensor4]; ring
    simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_add_distrib]
    rw [hvan_ab (fun c d => y.1 c * y.1 d), hvan_ac (fun b d => y.1 b * y.1 d),
      hvan_ad (fun b c => y.1 b * y.1 c), hvan_bc (fun a d => y.1 a * y.1 d),
      hvan_bd (fun a c => y.1 a * y.1 c), hvan_cd (fun a b => y.1 a * y.1 b),
      hvan_ab kronecker, hvan_ac kronecker, hvan_ad kronecker]
    ring
  rw [hred]
  -- Evaluate `⟨T₄(x), y^{\otimes 4}⟩ = t⁴ - (6/7) t² + 3/35`.
  have h4pow : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (x.1 a * x.1 b * x.1 c * x.1 d) * (y.1 a * y.1 b * y.1 c * y.1 d) =
      inner ℝ x.1 y.1 ^ 4 := by
    have : ∀ a b c d : Fin 3,
        (x.1 a * x.1 b * x.1 c * x.1 d) * (y.1 a * y.1 b * y.1 c * y.1 d) =
          (x.1 a * y.1 a) * ((x.1 b * y.1 b) * ((x.1 c * y.1 c) * (x.1 d * y.1 d))) :=
      fun _ _ _ _ => by ring
    simp_rw [this, ← Finset.mul_sum, sum_coord_mul, ← Finset.sum_mul, sum_coord_mul]
    ring
  have h2pair : ∀ (p q : E3) (r s : Fin 3 → ℝ),
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        kronecker a b * (p a * q b * (r c * s d)) =
        inner ℝ p q * (∑ c : Fin 3, r c) * (∑ d : Fin 3, s d) := by
    intro p q r s
    have : ∀ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        kronecker a b * (p a * q b * (r c * s d)) =
        (p a * q a) * ((∑ c : Fin 3, r c) * (∑ d : Fin 3, s d)) := fun a => by
      have hb : ∀ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3, kronecker a b * (p a * q b * (r c * s d)) =
          kronecker a b * ((p a * q b) * ((∑ c : Fin 3, r c) * (∑ d : Fin 3, s d))) := fun b => by
        have hc : ∀ c : Fin 3, ∑ d : Fin 3, kronecker a b * (p a * q b * (r c * s d)) =
            (kronecker a b * (p a * q b)) * (r c * ∑ d : Fin 3, s d) := fun c => by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun d _ => by ring
        simp_rw [hc, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
      simp_rw [hb]
      exact sum_kronecker_mul (fun b => p a * q b * ((∑ c : Fin 3, r c) * ∑ d : Fin 3, s d)) a
    simp_rw [this, ← Finset.sum_mul, sum_coord_mul]
    ring
  have hpair_xy : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      kronecker a b * (y.1 a * y.1 b * ((x.1 c * y.1 c) * (x.1 d * y.1 d))) =
      inner ℝ x.1 y.1 ^ 2 := by
    rw [h2pair y.1 y.1 (fun c => x.1 c * y.1 c) (fun d => x.1 d * y.1 d),
      Geodesic.inner_self_of_norm_one y.2, sum_coord_mul, one_mul, sq]
  have hdd_one : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (kronecker a b * kronecker c d) * (y.1 a * y.1 b * y.1 c * y.1 d) = 1 := by
    have : ∀ a b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        (kronecker a b * kronecker c d) * (y.1 a * y.1 b * y.1 c * y.1 d) =
        kronecker a b * (y.1 a * y.1 b) := fun a b => by
      have hc : ∀ c : Fin 3, ∑ d : Fin 3,
          (kronecker a b * kronecker c d) * (y.1 a * y.1 b * y.1 c * y.1 d) =
          (y.1 c * y.1 c) * (kronecker a b * (y.1 a * y.1 b)) := fun c => by
        have := sum_kronecker_mul (fun d => kronecker a b * (y.1 a * y.1 b) * y.1 c * y.1 d) c
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      simp_rw [hc, ← Finset.sum_mul, sum_coord_sq y, one_mul]
    simp_rw [this]
    have ha : ∀ a : Fin 3, ∑ b : Fin 3, kronecker a b * (y.1 a * y.1 b) = y.1 a * y.1 a :=
      fun a => sum_kronecker_mul (fun b => y.1 a * y.1 b) a
    simp_rw [ha, sum_coord_sq y]
  -- All 6 single-delta terms equal `inner x y ^ 2`, and all 3 double-delta terms equal `1`.
  have h_ab : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (kronecker a b * x.1 c * x.1 d) * (y.1 a * y.1 b * y.1 c * y.1 d) = inner ℝ x.1 y.1 ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpair_xy
  have h_ac : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (kronecker a c * x.1 b * x.1 d) * (y.1 a * y.1 b * y.1 c * y.1 d) = inner ℝ x.1 y.1 ^ 2 := by
    have : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        (kronecker a c * x.1 b * x.1 d) * (y.1 a * y.1 b * y.1 c * y.1 d) =
        ∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3,
        kronecker a c * (y.1 a * y.1 c * ((x.1 b * y.1 b) * (x.1 d * y.1 d))) :=
      Finset.sum_congr rfl fun a _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun d _ => by ring
    rw [this, hpair_xy]
  have h_ad : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (kronecker a d * x.1 b * x.1 c) * (y.1 a * y.1 b * y.1 c * y.1 d) = inner ℝ x.1 y.1 ^ 2 := by
    have : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        (kronecker a d * x.1 b * x.1 c) * (y.1 a * y.1 b * y.1 c * y.1 d) =
        ∑ a : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3, ∑ c : Fin 3,
        (kronecker a d * x.1 b * x.1 c) * (y.1 a * y.1 b * y.1 d * y.1 c) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by ring
    rw [this, h_ac]
  have h_bc : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (kronecker b c * x.1 a * x.1 d) * (y.1 a * y.1 b * y.1 c * y.1 d) = inner ℝ x.1 y.1 ^ 2 := by
    rw [Finset.sum_comm]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_ac
  have h_bd : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (kronecker b d * x.1 a * x.1 c) * (y.1 a * y.1 b * y.1 c * y.1 d) = inner ℝ x.1 y.1 ^ 2 := by
    rw [Finset.sum_comm]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_ad
  have h_cd : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (kronecker c d * x.1 a * x.1 b) * (y.1 a * y.1 b * y.1 c * y.1 d) = inner ℝ x.1 y.1 ^ 2 := by
    have : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        (kronecker c d * x.1 a * x.1 b) * (y.1 a * y.1 b * y.1 c * y.1 d) =
        ∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3,
        (kronecker c d * x.1 a * x.1 b) * (y.1 a * y.1 c * y.1 b * y.1 d) :=
      Finset.sum_congr rfl fun a _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun d _ => by ring
    rw [this, h_bd]
  have h_ac_bd : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (kronecker a c * kronecker b d) * (y.1 a * y.1 b * y.1 c * y.1 d) = 1 := by
    have : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        (kronecker a c * kronecker b d) * (y.1 a * y.1 b * y.1 c * y.1 d) =
        ∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3,
        (kronecker a c * kronecker b d) * (y.1 a * y.1 c * y.1 b * y.1 d) :=
      Finset.sum_congr rfl fun a _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun d _ => by ring
    rw [this, hdd_one]
  have h_ad_bc : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (kronecker a d * kronecker b c) * (y.1 a * y.1 b * y.1 c * y.1 d) = 1 := by
    have : ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        (kronecker a d * kronecker b c) * (y.1 a * y.1 b * y.1 c * y.1 d) =
        ∑ a : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3, ∑ c : Fin 3,
        (kronecker a d * kronecker b c) * (y.1 a * y.1 b * y.1 d * y.1 c) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by ring
    rw [this, h_ac_bd]
  have hsplit' : ∀ a b c d : Fin 3,
      tensor4 x.1 (a, b, c, d) * (y.1 a * y.1 b * y.1 c * y.1 d) =
        (x.1 a * x.1 b * x.1 c * x.1 d) * (y.1 a * y.1 b * y.1 c * y.1 d) -
        (1 / 7) * ((kronecker a b * x.1 c * x.1 d) * (y.1 a * y.1 b * y.1 c * y.1 d) +
                   (kronecker a c * x.1 b * x.1 d) * (y.1 a * y.1 b * y.1 c * y.1 d) +
                   (kronecker a d * x.1 b * x.1 c) * (y.1 a * y.1 b * y.1 c * y.1 d) +
                   (kronecker b c * x.1 a * x.1 d) * (y.1 a * y.1 b * y.1 c * y.1 d) +
                   (kronecker b d * x.1 a * x.1 c) * (y.1 a * y.1 b * y.1 c * y.1 d) +
                   (kronecker c d * x.1 a * x.1 b) * (y.1 a * y.1 b * y.1 c * y.1 d)) +
        (1 / 35) * ((kronecker a b * kronecker c d) * (y.1 a * y.1 b * y.1 c * y.1 d) +
                    (kronecker a c * kronecker b d) * (y.1 a * y.1 b * y.1 c * y.1 d) +
                    (kronecker a d * kronecker b c) * (y.1 a * y.1 b * y.1 c * y.1 d)) :=
    fun a b c d => by simp only [tensor4]; ring
  simp_rw [hsplit', Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib, h4pow, h_ab, h_ac, h_ad, h_bc, h_bd, h_cd, hdd_one, h_ac_bd, h_ad_bc]
  simp only [legendreP]
  ring

/-- Positive semidefiniteness of the Legendre kernels `P₀, P₁, P₂, P₃, P₄` on `S²`:
for every finite configuration `p : Fin n → UnitSphere`,
`∑ i, ∑ j, Pₖ(⟪p i, p j⟫) ≥ 0`. -/
theorem sum_legendreP_nonneg {n : ℕ} (p : Fin n → UnitSphere) (k : Fin 5) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP k (inner ℝ (p i).1 (p j).1) := by
  fin_cases k
  · -- P₀(t) = 1
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by norm_num [legendreP]
  · -- P₁(t) = t
    exact sum_pair_nonneg_of_feature p (fun x y => legendreP 1 (inner ℝ x.1 y.1))
      (fun x a => x.1 a) one_pos (fun x y => by simp [legendreP, sum_coord_mul])
  · -- P₂(t) = (3t² - 1)/2
    exact sum_pair_nonneg_of_feature p (fun x y => legendreP 2 (inner ℝ x.1 y.1))
      (fun x ab => tensor2 x.1 ab) (by norm_num) sum_tensor2_mul
  · -- P₃(t) = (5t³ - 3t)/2
    exact sum_pair_nonneg_of_feature p (fun x y => legendreP 3 (inner ℝ x.1 y.1))
      (fun x abc => tensor3 x.1 abc) (by norm_num) sum_tensor3_mul
  · -- P₄(t) = (35t⁴ - 30t² + 3)/8
    exact sum_pair_nonneg_of_feature p (fun x y => legendreP 4 (inner ℝ x.1 y.1))
      (fun x abcd => tensor4 x.1 abcd) (by norm_num) sum_tensor4_mul

/-! ## Reusable Delsarte linear programming bound -/

/-- Core double-sum inequality behind Delsarte's LP bound:
for any `c : Fin 5 → ℝ` with `∀ k, 0 ≤ c k` and any `p : Fin n → UnitSphere`,
`c 0 * n² ≤ ∑ i, ∑ j, legendreEval c ⟪p i, p j⟫`. -/
theorem delsarte_double_sum_ge {n : ℕ} (p : Fin n → UnitSphere) {c : Fin 5 → ℝ}
    (hc : ∀ k : Fin 5, 0 ≤ c k) :
    c 0 * (n : ℝ) ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreEval c (inner ℝ (p i).1 (p j).1) := by
  have hswap : ∑ i : Fin n, ∑ j : Fin n, legendreEval c (inner ℝ (p i).1 (p j).1) =
      ∑ k : Fin 5, c k * ∑ i : Fin n, ∑ j : Fin n, legendreP k (inner ℝ (p i).1 (p j).1) := by
    simp only [legendreEval]
    calc ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin 5, c k * legendreP k (inner ℝ (p i).1 (p j).1)
        = ∑ i : Fin n, ∑ k : Fin 5, ∑ j : Fin n, c k * legendreP k (inner ℝ (p i).1 (p j).1) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k : Fin 5, ∑ i : Fin n, ∑ j : Fin n, c k * legendreP k (inner ℝ (p i).1 (p j).1) :=
            Finset.sum_comm
      _ = ∑ k : Fin 5, c k * ∑ i : Fin n, ∑ j : Fin n, legendreP k (inner ℝ (p i).1 (p j).1) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  rw [hswap]
  have hterm0 : c 0 * (n : ℝ) ^ 2 =
      c 0 * ∑ i : Fin n, ∑ j : Fin n, legendreP 0 (inner ℝ (p i).1 (p j).1) := by
    have hP0 : ∀ t : ℝ, legendreP 0 t = 1 := fun _ => rfl
    simp only [hP0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  rw [hterm0]
  exact Finset.single_le_sum (fun k _ => mul_nonneg (hc k) (sum_legendreP_nonneg p k))
    (Finset.mem_univ (0 : Fin 5))

/-- Delsarte–Goethals–Seidel linear programming upper bound on `S²`:
if `f(t) = ∑ k, c k * Pₖ(t)` satisfies `c 0 > 0`, `∀ k, c k ≥ 0`, and
`f(t) ≤ 0` on `[-1, s]`, then every `(n, s)`-spherical code satisfies
`n ≤ f(1) / c 0`. -/
theorem delsarte_bound {n : ℕ} {p : Fin n → UnitSphere} {s : ℝ} {c : Fin 5 → ℝ}
    (hp : IsSphericalCode p s)
    (hc0 : 0 < c 0)
    (hc : ∀ k : Fin 5, 0 ≤ c k)
    (hf : ∀ t : ℝ, -1 ≤ t → t ≤ s → legendreEval c t ≤ 0) :
    (n : ℝ) ≤ legendreEval c 1 / c 0 := by
  have hlow := delsarte_double_sum_ge p hc
  have hdiag : ∀ i : Fin n,
      ∑ j : Fin n, legendreEval c (inner ℝ (p i).1 (p j).1) ≤ legendreEval c 1 := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Geodesic.inner_self_of_norm_one (p i).2]
    have hoff : ∑ j ∈ Finset.univ.erase i, legendreEval c (inner ℝ (p i).1 (p j).1) ≤ 0 :=
      Finset.sum_nonpos fun j hj =>
        hf _ (neg_one_le_inner (p i) (p j)) (hp i j (Finset.ne_of_mem_erase hj).symm)
    linarith
  have hup : ∑ i : Fin n, ∑ j : Fin n, legendreEval c (inner ℝ (p i).1 (p j).1) ≤
      (n : ℝ) * legendreEval c 1 := by
    calc ∑ i : Fin n, ∑ j : Fin n, legendreEval c (inner ℝ (p i).1 (p j).1)
        ≤ ∑ _i : Fin n, legendreEval c 1 := Finset.sum_le_sum fun i _ => hdiag i
      _ = (n : ℝ) * legendreEval c 1 := by simp
  have hmul : c 0 * (n : ℝ) ^ 2 ≤ (n : ℝ) * legendreEval c 1 := hlow.trans hup
  rw [le_div_iff₀ hc0]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_mul]
    have h1 : 0 ≤ legendreEval c 1 := by
      rw [legendreEval_one]
      exact Finset.sum_nonneg fun k _ => hc k
    exact h1
  · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    nlinarith

/-- Equality condition of Delsarte's bound: when `(n : ℝ) * c 0 = f(1)`, every
distinct pair `(i, j)` must satisfy `f(⟪p i, p j⟫) = 0`. -/
theorem delsarte_offdiag_zero_of_tight {n : ℕ} {p : Fin n → UnitSphere} {s : ℝ} {c : Fin 5 → ℝ}
    (hp : IsSphericalCode p s)
    (hc : ∀ k : Fin 5, 0 ≤ c k)
    (hf : ∀ t : ℝ, -1 ≤ t → t ≤ s → legendreEval c t ≤ 0)
    (htight : (n : ℝ) * c 0 = legendreEval c 1)
    {i j : Fin n} (hij : i ≠ j) :
    legendreEval c (inner ℝ (p i).1 (p j).1) = 0 := by
  have hlow := delsarte_double_sum_ge p hc
  have hsplit : ∑ a : Fin n, ∑ b : Fin n, legendreEval c (inner ℝ (p a).1 (p b).1) =
      (n : ℝ) * legendreEval c 1 +
        ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, legendreEval c (inner ℝ (p a).1 (p b).1) := by
    have hrow : ∀ a : Fin n,
        ∑ b : Fin n, legendreEval c (inner ℝ (p a).1 (p b).1) =
          legendreEval c 1 +
            ∑ b ∈ Finset.univ.erase a, legendreEval c (inner ℝ (p a).1 (p b).1) := fun a => by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), Geodesic.inner_self_of_norm_one (p a).2]
    simp_rw [hrow, Finset.sum_add_distrib]
    simp
  have hcn2 : c 0 * (n : ℝ) ^ 2 = (n : ℝ) * legendreEval c 1 := by
    calc c 0 * (n : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) * c 0) := by ring
      _ = (n : ℝ) * legendreEval c 1 := by rw [htight]
  have hoff_ge : 0 ≤ ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a,
      legendreEval c (inner ℝ (p a).1 (p b).1) := by linarith
  have hterm_le : ∀ a : Fin n, ∀ b ∈ Finset.univ.erase a,
      legendreEval c (inner ℝ (p a).1 (p b).1) ≤ 0 := fun a b hb =>
    hf _ (neg_one_le_inner (p a) (p b)) (hp a b (Finset.ne_of_mem_erase hb).symm)
  have hrow_le : ∀ a : Fin n,
      ∑ b ∈ Finset.univ.erase a, legendreEval c (inner ℝ (p a).1 (p b).1) ≤ 0 := fun a =>
    Finset.sum_nonpos fun b hb => hterm_le a b hb
  have hrow_eq : ∑ b ∈ Finset.univ.erase i, legendreEval c (inner ℝ (p i).1 (p b).1) = 0 := by
    by_contra hne
    have hlt : ∑ b ∈ Finset.univ.erase i, legendreEval c (inner ℝ (p i).1 (p b).1) < 0 :=
      lt_of_le_of_ne (hrow_le i) hne
    have hsum_lt : ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a,
        legendreEval c (inner ℝ (p a).1 (p b).1) < 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have hrest : ∑ a ∈ Finset.univ.erase i,
          ∑ b ∈ Finset.univ.erase a, legendreEval c (inner ℝ (p a).1 (p b).1) ≤ 0 :=
        Finset.sum_nonpos fun a _ => hrow_le a
      linarith
    linarith
  have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  by_contra hne
  have hlt : legendreEval c (inner ℝ (p i).1 (p j).1) < 0 :=
    lt_of_le_of_ne (hterm_le i j hjmem) hne
  rw [← Finset.add_sum_erase _ _ hjmem] at hrow_eq
  have hrest : ∑ b ∈ (Finset.univ.erase i).erase j, legendreEval c (inner ℝ (p i).1 (p b).1) ≤ 0 :=
    Finset.sum_nonpos fun b hb => hterm_le i b (Finset.mem_of_mem_erase hb)
  linarith

/-! ## Regular icosahedron and exact Tammes optimality for `N = 12` -/

/-- The golden ratio `φ = (1 + √5) / 2`. -/
private noncomputable def phi : ℝ := (1 + √5) / 2

private theorem phi_sq : phi ^ 2 = phi + 1 := by
  have h5 : √5 ^ 2 = 5 := sq_sqrt (by norm_num)
  unfold phi
  linear_combination (1 / 4 : ℝ) * h5

private theorem phi_pos : 0 < phi := by
  have h5 : 0 < √5 := sqrt_pos.mpr (by norm_num)
  unfold phi
  linarith

/-- Norm of the unnormalized icosahedron vertices `(0, ±1, ±φ)`: `r = √(1 + φ²)`. -/
private noncomputable def icoR : ℝ := √(1 + phi ^ 2)

private theorem icoR_sq : icoR ^ 2 = 1 + phi ^ 2 :=
  sq_sqrt (by positivity)

private theorem icoR_pos : 0 < icoR :=
  sqrt_pos.mpr (by positivity)

private theorem phi_div_icoR_sq : phi / icoR ^ 2 = 1 / √5 := by
  have h5 : √5 ^ 2 = 5 := sq_sqrt (by norm_num)
  have h5pos : (0 : ℝ) < √5 := sqrt_pos.mpr (by norm_num)
  have hr2 : icoR ^ 2 = √5 * phi := by
    rw [icoR_sq, phi_sq]
    unfold phi
    linear_combination -(1 / 2 : ℝ) * h5
  rw [hr2]
  have hφne : phi ≠ 0 := phi_pos.ne'
  have h5ne : √5 ≠ 0 := h5pos.ne'
  field_simp

private theorem ico_unit {x y z : ℝ} (h : x ^ 2 + y ^ 2 + z ^ 2 = 1 + phi ^ 2) :
    ‖vec3 (x / icoR) (y / icoR) (z / icoR)‖ = 1 := by
  have hr : icoR ≠ 0 := icoR_pos.ne'
  have hsq : ‖vec3 (x / icoR) (y / icoR) (z / icoR)‖ ^ 2 = 1 := by
    rw [norm_vec3_sq]
    have h1 : (x / icoR) ^ 2 + (y / icoR) ^ 2 + (z / icoR) ^ 2 =
        (x ^ 2 + y ^ 2 + z ^ 2) / icoR ^ 2 := by ring
    rw [h1, h, ← icoR_sq, div_self (pow_ne_zero 2 hr)]
  nlinarith [norm_nonneg (vec3 (x / icoR) (y / icoR) (z / icoR))]

/-- The 12 vertices of the regular icosahedron on `S²`: cyclic permutations of
`(0, ±1, ±φ) / √(1 + φ²)`. -/
noncomputable def icosahedron12 : Fin 12 → UnitSphere
  | ⟨0, _⟩  => ⟨vec3 (0 / icoR) (1 / icoR) (phi / icoR),        ico_unit (by ring)⟩
  | ⟨1, _⟩  => ⟨vec3 (0 / icoR) (1 / icoR) ((-phi) / icoR),     ico_unit (by ring)⟩
  | ⟨2, _⟩  => ⟨vec3 (0 / icoR) ((-1) / icoR) (phi / icoR),     ico_unit (by ring)⟩
  | ⟨3, _⟩  => ⟨vec3 (0 / icoR) ((-1) / icoR) ((-phi) / icoR),  ico_unit (by ring)⟩
  | ⟨4, _⟩  => ⟨vec3 (1 / icoR) (phi / icoR) (0 / icoR),        ico_unit (by ring)⟩
  | ⟨5, _⟩  => ⟨vec3 (1 / icoR) ((-phi) / icoR) (0 / icoR),     ico_unit (by ring)⟩
  | ⟨6, _⟩  => ⟨vec3 ((-1) / icoR) (phi / icoR) (0 / icoR),     ico_unit (by ring)⟩
  | ⟨7, _⟩  => ⟨vec3 ((-1) / icoR) ((-phi) / icoR) (0 / icoR),  ico_unit (by ring)⟩
  | ⟨8, _⟩  => ⟨vec3 (phi / icoR) (0 / icoR) (1 / icoR),        ico_unit (by ring)⟩
  | ⟨9, _⟩  => ⟨vec3 ((-phi) / icoR) (0 / icoR) (1 / icoR),     ico_unit (by ring)⟩
  | ⟨10, _⟩ => ⟨vec3 (phi / icoR) (0 / icoR) ((-1) / icoR),     ico_unit (by ring)⟩
  | ⟨11, _⟩ => ⟨vec3 ((-phi) / icoR) (0 / icoR) ((-1) / icoR),  ico_unit (by ring)⟩

private theorem icosahedron12_inner_le {i j : Fin 12} (hij : i ≠ j) :
    inner ℝ (icosahedron12 i).1 (icosahedron12 j).1 ≤ 1 / √5 := by
  have hpos : 0 < icoR ^ 2 := sq_pos_of_pos icoR_pos
  have h1 : 1 / √5 = phi / icoR ^ 2 := phi_div_icoR_sq.symm
  have hφ : 0 < phi := phi_pos
  have hφ2 : phi ^ 2 = phi + 1 := phi_sq
  have hdot : ∀ a b c a' b' c' : ℝ,
      a * a' + b * b' + c * c' ≤ phi →
      inner ℝ (vec3 (a / icoR) (b / icoR) (c / icoR))
        (vec3 (a' / icoR) (b' / icoR) (c' / icoR)) ≤ phi / icoR ^ 2 := by
    intro a b c a' b' c' hle
    rw [inner_vec3]
    have heq : a / icoR * (a' / icoR) + b / icoR * (b' / icoR) + c / icoR * (c' / icoR) =
        (a * a' + b * b' + c * c') / icoR ^ 2 := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right hle hpos.le
  rw [h1]
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | exact hdot _ _ _ _ _ _ (by nlinarith)

/-- Delsarte certificate polynomial for `N = 12`:
`f(t) = (t + 1)(t + a)²(t - a)` with `a = 1 / √5`. -/
private noncomputable def icoCertCoeff : Fin 5 → ℝ
  | ⟨0, _⟩ => (2 / 15) * (1 + 1 / √5)
  | ⟨1, _⟩ => (2 / 5) * (1 + 1 / √5)
  | ⟨2, _⟩ => 46 / 105 + (2 / 3) * (1 / √5)
  | ⟨3, _⟩ => (2 / 5) * (1 + 1 / √5)
  | ⟨4, _⟩ => 8 / 35

private theorem icoCert_eval (t : ℝ) :
    legendreEval icoCertCoeff t = (t + 1) * (t + 1 / √5) ^ 2 * (t - 1 / √5) := by
  set a : ℝ := 1 / √5
  have ha2 : a ^ 2 = 1 / 5 := by
    simp only [a]
    rw [div_pow, one_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  simp only [legendreEval, Fin.sum_univ_five, icoCertCoeff, legendreP]
  change (2 / 15) * (1 + a) * 1 + (2 / 5) * (1 + a) * t +
      (46 / 105 + (2 / 3) * a) * ((3 * t ^ 2 - 1) / 2) +
      (2 / 5) * (1 + a) * ((5 * t ^ 3 - 3 * t) / 2) +
      (8 / 35) * ((35 * t ^ 4 - 30 * t ^ 2 + 3) / 8) =
    (t + 1) * (t + a) ^ 2 * (t - a)
  linear_combination (t ^ 2 + (1 + a) * t + a) * ha2

private theorem icoCert_coeff_nonneg (k : Fin 5) : 0 ≤ icoCertCoeff k := by
  have h5 : (0 : ℝ) < 1 / √5 := div_pos one_pos (sqrt_pos.mpr (by norm_num))
  fin_cases k <;> simp only [icoCertCoeff] <;> positivity

private theorem icoCert_c0_pos : 0 < icoCertCoeff 0 := by
  have h5 : (0 : ℝ) < 1 / √5 := div_pos one_pos (sqrt_pos.mpr (by norm_num))
  simp only [icoCertCoeff]
  positivity

private theorem icoCert_tight : 12 * icoCertCoeff 0 = legendreEval icoCertCoeff 1 := by
  rw [icoCert_eval]
  have h5 : (1 / √5 : ℝ) ^ 2 = 1 / 5 := by
    rw [div_pow, one_pow, sq_sqrt (by norm_num)]
  simp only [icoCertCoeff]
  linear_combination (2 * (1 + 1 / √5)) * h5

private theorem icoCert_nonpos {t : ℝ} (hlo : -1 ≤ t) (hhi : t ≤ 1 / √5) :
    legendreEval icoCertCoeff t ≤ 0 := by
  rw [icoCert_eval]
  have h1 : 0 ≤ (t + 1) * (t + 1 / √5) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : t - 1 / √5 ≤ 0 := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos h1 h2

/-- No 12-point configuration on `S²` can have all pairwise inner products
strictly less than `1 / √5`. -/
theorem not_isSphericalCode_12_lt {p : Fin 12 → UnitSphere} {s : ℝ}
    (hs : s < 1 / √5) (hp : IsSphericalCode p s) : False := by
  have hp' : IsSphericalCode p (1 / √5) := fun i j hij => (hp i j hij).trans hs.le
  -- Tightness of the Delsarte bound forces `f(⟪p i, p j⟫) = 0` for all `i ≠ j`.
  have hneg : ∀ i j : Fin 12, i ≠ j → inner ℝ (p i).1 (p j).1 < 0 := by
    intro i j hij
    have hzero := delsarte_offdiag_zero_of_tight hp' icoCert_coeff_nonneg
      (fun _ hlo hhi => icoCert_nonpos hlo hhi) (by simpa using icoCert_tight) hij
    rw [icoCert_eval] at hzero
    have hlt : inner ℝ (p i).1 (p j).1 < 1 / √5 := lt_of_le_of_lt (hp i j hij) hs
    have hne : inner ℝ (p i).1 (p j).1 - 1 / √5 ≠ 0 := by linarith
    have hprod : (inner ℝ (p i).1 (p j).1 + 1) * (inner ℝ (p i).1 (p j).1 + 1 / √5) ^ 2 = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hne
    have h5pos : (0 : ℝ) < 1 / √5 := div_pos one_pos (sqrt_pos.mpr (by norm_num))
    rcases mul_eq_zero.mp hprod with h1 | h2
    · linarith
    · have h2' : inner ℝ (p i).1 (p j).1 + 1 / √5 = 0 := sq_eq_zero_iff.mp h2
      linarith
  -- Twelve points on `S²` cannot all have strictly negative inner products (Rankin's bound).
  obtain ⟨i, j, hij, hge⟩ := rankin_orthoplex_bound (by norm_num : 5 ≤ 12) p
  exact not_lt_of_ge hge (hneg i j hij)

/-- Unconditional exact optimality of the regular icosahedron for the Tammes
problem at `N = 12`: `12` points on `S²` can be `θ`-separated if and only if
`θ ≤ arccos (1 / √5)`. -/
theorem tammes_12_optimal (θ : ℝ) :
    (∃ p : Fin 12 → UnitSphere, IsSeparated p θ) ↔ θ ≤ arccos (1 / √5) := by
  constructor
  · rintro ⟨p, hp⟩
    by_contra hgt
    push Not at hgt
    have h5pos : (0 : ℝ) < 1 / √5 := div_pos one_pos (sqrt_pos.mpr (by norm_num))
    have h5lt1 : 1 / √5 < 1 := by
      have : (1 : ℝ) < √5 := by
        have hsq : (1 : ℝ) ^ 2 < √5 ^ 2 := by rw [sq_sqrt (by norm_num)]; norm_num
        nlinarith [sqrt_nonneg 5]
      exact (div_lt_one (sqrt_pos.mpr (by norm_num))).mpr this
    have hθπ : θ ≤ π := (hp 0 1 (by decide)).trans (geoDist_le_pi _ _)
    have hθ0 : 0 ≤ θ :=
      le_trans (arccos_nonneg _) hgt.le
    have hcos_lt : cos θ < 1 / √5 := by
      have h1 : cos θ < cos (arccos (1 / √5)) :=
        strictAntiOn_cos ⟨arccos_nonneg _, arccos_le_pi _⟩ ⟨hθ0, hθπ⟩ hgt
      rwa [cos_arccos (by linarith) h5lt1.le] at h1
    have hcode : IsSphericalCode p (cos θ) :=
      (isSeparated_iff_isSphericalCode p hθ0 hθπ).mp hp
    exact not_isSphericalCode_12_lt hcos_lt hcode
  · intro hθ
    refine ⟨icosahedron12, fun i j hij => ?_⟩
    calc θ ≤ arccos (1 / √5) := hθ
      _ ≤ arccos (inner ℝ (icosahedron12 i).1 (icosahedron12 j).1) :=
          arccos_le_arccos_of_le (icosahedron12_inner_le hij)
      _ = geoDist (icosahedron12 i) (icosahedron12 j) := (geoDist_eq_arccos_inner _ _).symm

end Geodesy.Spherical
