import LeanGeodesy.Spherical.BachocVallentin

/-!
# Exact rational Bachoc–Vallentin SDP certificate verifier on `S²`

This module implements a self-contained, kernel-checkable verifier for degree-5
Bachoc–Vallentin three-point SDP certificates on `S²` (Priority 3).

An external SDP solver + rational rounding script produces a `BVCert5` containing:
- rational inner-product threshold `s = sNum / sDen` (`sDen > 0`, `-1 < s`),
- common integer denominators `dK` (for the 6 Bachoc–Vallentin kernel matrices
  `A₀, F₁, …, F₅`), `dS` (for the 2 univariate and 10 `S₃`-reduced trivariate
  SOS Gram matrices), and `dR` (for the upper-triangular Cholesky witnesses),
- integer-scaled matrices `A₀ (7×7), F₁ (5×5), …, F₅ (1×1)`, `S₂₀ (6×6), S₂₁ (5×5)`,
  and the 10 `S₃`-reduced SOS matrices (`one_triv`, `one_std`, `one_sign`,
  `delta_triv`, `delta_std`, `delta_sign`, `g1_even`, `g1_odd`, `g2_even`, `g2_odd`),
  each paired with its integer-scaled Cholesky witness `R`.

`BVCert5.isValid` checks every requirement purely in exact integer arithmetic:
1. Positive denominators and `-1 < s`,
2. Symmetry and positive semidefiniteness of all 18 matrices via exact Cholesky
   plus diagonal dominance (`D_R² · M - D_M · Rᵀ R` is symmetric diagonally dominant),
3. Exact univariate polynomial identity `-G₂(t) = SOS₀(t) + (t + 1)(s - t) SOS₁(t)`,
4. Exact `S₃`-symmetrized trivariate polynomial identity
   `-sym3(G₃)(u, v, t) = sym3(SOS_one + Δ·SOS_delta + g₁·SOS_g1 + g₂·SOS_g2)`.

The soundness theorem `BVCert5.sound` proves that any certificate with
`cert.isValid = true` unconditionally certifies `(n : ℝ) ≤ (cert.bound : ℝ)`
for every `(n, cert.s)`-spherical code on `S²`, with zero trust in external
solvers or floating-point arithmetic.
-/

namespace Geodesy.Spherical

open scoped Matrix

/-! ## Exact integer matrix representation and Cholesky + DD verification -/

/-- Entry `(i, j)` of a matrix stored as `List (List ℤ)`, defaulting to `0`. -/
def matGet (M : List (List ℤ)) (i j : ℕ) : ℤ :=
  (M.getD i []).getD j 0

/-- Interpret an integer-scaled `m × m` matrix with denominator `D` as a real matrix. -/
noncomputable def toRealMat (m : ℕ) (D : ℕ) (M : List (List ℤ)) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => (matGet M i.val j.val : ℝ) / (D : ℝ)

/-- Check that `M` is symmetric on `Fin m × Fin m`. -/
def isSymmInt (m : ℕ) (M : List (List ℤ)) : Bool :=
  (List.range m).all fun i =>
    (List.range m).all fun j =>
      matGet M i j == matGet M j i

/-- Entry `(i, j)` of `Rᵀ * R` for an `m × m` integer matrix `R`. -/
def rtrEntry (m : ℕ) (R : List (List ℤ)) (i j : ℕ) : ℤ :=
  (List.range m).foldl (fun acc k => acc + matGet R k i * matGet R k j) 0

/-- Check that `M` is symmetric and `dR² · M - dM · (Rᵀ R)` is diagonally dominant
on `Fin m × Fin m`. -/
def isCholeskyDDValid (m dM dR : ℕ) (M R : List (List ℤ)) : Bool :=
  decide (0 < dM) &&
  decide (0 < dR) &&
  isSymmInt m M &&
  (List.range m).all fun i =>
    let dR2 : ℤ := (dR : ℤ) * (dR : ℤ)
    let dMi : ℤ := (dM : ℤ)
    let diag : ℤ := dR2 * matGet M i i - dMi * rtrEntry m R i i
    let offSum : ℤ := (List.range m).foldl (fun acc j =>
      if j == i then acc
      else acc + Int.natAbs (dR2 * matGet M i j - dMi * rtrEntry m R i j)) 0
    decide (offSum ≤ diag)

private theorem foldl_add_eq_sum {α : Type*} (l : List α) (f : α → ℤ) (init : ℤ) :
    l.foldl (fun acc x => acc + f x) init = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    ring

private theorem list_map_finRange_eq_range {α : Type*} (m : ℕ) (f : ℕ → α) :
    (List.finRange m).map (fun k : Fin m => f k.val) = (List.range m).map f := by
  apply List.ext_getElem <;> simp

private theorem sum_range_eq_fin {m : ℕ} (f : ℕ → ℤ) :
    ((List.range m).map f).sum = ∑ k : Fin m, f k.val := by
  rw [Fin.sum_univ_def, list_map_finRange_eq_range]

private theorem rtrEntry_cast (m : ℕ) (R : List (List ℤ)) (i j : ℕ) :
    (rtrEntry m R i j : ℝ) = ∑ k : Fin m, (matGet R k.val i : ℝ) * (matGet R k.val j : ℝ) := by
  unfold rtrEntry
  rw [foldl_add_eq_sum, zero_add, sum_range_eq_fin]
  push_cast
  rfl

/-- Soundness of `isCholeskyDDValid`: any matrix passing the integer check is
positive semidefinite as a real matrix `(1 / dM) • M`. -/
theorem isCholeskyDDValid_sound {m dM dR : ℕ} {M R : List (List ℤ)}
    (h : isCholeskyDDValid m dM dR M R = true) :
    (toRealMat m dM M).PosSemidef := by
  simp only [isCholeskyDDValid, Bool.and_eq_true, decide_eq_true_eq, isSymmInt,
    List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨hdM, hdR⟩, hsym⟩, hdd⟩ := h
  have hdM_pos : (0 : ℝ) < (dM : ℝ) := Nat.cast_pos.mpr hdM
  have hdR_pos : (0 : ℝ) < (dR : ℝ) := Nat.cast_pos.mpr hdR
  have hsymR : (toRealMat m dM M).IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, toRealMat, Matrix.of_apply]
    rw [hsym j.val j.isLt i.val i.isLt]
  refine posSemidef_of_cholesky_dd (toRealMat m dM M) (toRealMat m dR R) hsymR fun i => ?_
  have hdd_i := hdd i.val i.isLt
  have hscale_pos : (0 : ℝ) < (dM : ℝ) * ((dR : ℝ) * (dR : ℝ)) := by positivity
  have hoff_eq :
      (((List.range m).foldl (fun (acc : ℤ) j =>
        if j = i.val then acc
        else acc + (Int.natAbs (((dR : ℤ) * (dR : ℤ)) * matGet M i.val j -
          (dM : ℤ) * rtrEntry m R i.val j) : ℤ)) 0 : ℤ) : ℝ) =
      ((dM : ℝ) * ((dR : ℝ) * (dR : ℝ))) *
        ∑ j ∈ Finset.univ.erase i,
          |(toRealMat m dM M - (toRealMat m dR R)ᵀ * toRealMat m dR R) i j| := by
    have hfold : (List.range m).foldl (fun (acc : ℤ) j =>
        if j = i.val then acc
        else acc + (Int.natAbs (((dR : ℤ) * (dR : ℤ)) * matGet M i.val j -
          (dM : ℤ) * rtrEntry m R i.val j) : ℤ)) 0 =
        (List.range m).foldl (fun (acc : ℤ) j =>
          acc + if j = i.val then 0
                else (Int.natAbs (((dR : ℤ) * (dR : ℤ)) * matGet M i.val j -
                  (dM : ℤ) * rtrEntry m R i.val j) : ℤ)) 0 := by
      congr 1
      funext acc j
      split_ifs <;> omega
    rw [hfold, foldl_add_eq_sum, zero_add, sum_range_eq_fin]
    push_cast
    rw [Finset.mul_sum]
    have herase : ∑ j ∈ Finset.univ.erase i,
        ((dM : ℝ) * ((dR : ℝ) * (dR : ℝ))) *
          |(toRealMat m dM M - (toRealMat m dR R)ᵀ * toRealMat m dR R) i j| =
        ∑ j : Fin m, if j.val = i.val then (0 : ℝ) else
          ((dM : ℝ) * ((dR : ℝ) * (dR : ℝ))) *
            |(toRealMat m dM M - (toRealMat m dR R)ᵀ * toRealMat m dR R) i j| := by
      have h1 : ∑ j : Fin m, (if j.val = i.val then (0 : ℝ) else
          ((dM : ℝ) * ((dR : ℝ) * (dR : ℝ))) *
            |(toRealMat m dM M - (toRealMat m dR R)ᵀ * toRealMat m dR R) i j|) =
          ∑ j : Fin m, if j.val ≠ i.val then
            ((dM : ℝ) * ((dR : ℝ) * (dR : ℝ))) *
              |(toRealMat m dM M - (toRealMat m dR R)ᵀ * toRealMat m dR R) i j| else 0 :=
        Finset.sum_congr rfl fun j _ => by by_cases h : j.val = i.val <;> simp [h]
      rw [h1, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext j
      simp [Finset.mem_erase, Fin.ext_iff]
    rw [herase]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hji : j.val = i.val
    · simp [hji]
    · simp only [hji, ↓reduceIte, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
        toRealMat, Matrix.of_apply]
      rw [← abs_of_pos hscale_pos, ← abs_mul]
      congr 1
      have hrtr := rtrEntry_cast m R i.val j.val
      rw [hrtr]
      have hdM_ne : (dM : ℝ) ≠ 0 := hdM_pos.ne'
      have hdR_ne : (dR : ℝ) ≠ 0 := hdR_pos.ne'
      symm
      rw [mul_sub]
      congr 1
      · field_simp [hdM_ne]
      · rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        field_simp [hdR_ne]
  have hdiag_eq :
      ((((dR : ℤ) * (dR : ℤ)) * matGet M i.val i.val -
        (dM : ℤ) * rtrEntry m R i.val i.val : ℤ) : ℝ) =
      ((dM : ℝ) * ((dR : ℝ) * (dR : ℝ))) *
        (toRealMat m dM M - (toRealMat m dR R)ᵀ * toRealMat m dR R) i i := by
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
      toRealMat, Matrix.of_apply]
    push_cast
    rw [rtrEntry_cast m R i.val i.val]
    have hdM_ne : (dM : ℝ) ≠ 0 := hdM_pos.ne'
    have hdR_ne : (dR : ℝ) ≠ 0 := hdR_pos.ne'
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · field_simp [hdM_ne]
    · refine Finset.sum_congr rfl fun k _ => ?_
      field_simp [hdR_ne]
  have hineq : (((List.range m).foldl (fun (acc : ℤ) j =>
        if j = i.val then acc
        else acc + (Int.natAbs (((dR : ℤ) * (dR : ℤ)) * matGet M i.val j -
          (dM : ℤ) * rtrEntry m R i.val j) : ℤ)) 0 : ℤ) : ℝ) ≤
      ((((dR : ℤ) * (dR : ℤ)) * matGet M i.val i.val -
        (dM : ℤ) * rtrEntry m R i.val i.val : ℤ) : ℝ) := by
    exact_mod_cast hdd_i
  rw [hoff_eq, hdiag_eq] at hineq
  exact le_of_mul_le_mul_left hineq hscale_pos

/-! ## Computable univariate integer polynomials (`Poly1`) -/

/-- A univariate integer polynomial `∑ k, p[k] t^k`. -/
abbrev Poly1 := List ℤ

def evalPoly1 (p : Poly1) (t : ℝ) : ℝ :=
  (List.range p.length).foldl (fun acc k => acc + (p.getD k 0 : ℝ) * t ^ k) 0

private theorem evalPoly1_eq_sum (p : Poly1) (t : ℝ) :
    evalPoly1 p t = ∑ k : Fin p.length, (p.getD k.val 0 : ℝ) * t ^ k.val := by
  unfold evalPoly1
  have hfold : ∀ (l : List ℕ) (init : ℝ),
      l.foldl (fun acc k => acc + (p.getD k 0 : ℝ) * t ^ k) init =
      init + (l.map fun k => (p.getD k 0 : ℝ) * t ^ k).sum := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons a s ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      ring
  rw [hfold, zero_add, ← list_map_finRange_eq_range, ← Fin.sum_univ_def]

/-- Fixed-length degree-10 univariate polynomial arithmetic (`List ℤ` of length 11). -/
def poly1Zero : Poly1 := List.replicate 11 0

def poly1Add (p q : Poly1) : Poly1 :=
  (List.range 11).map fun k => p.getD k 0 + q.getD k 0

def poly1Scale (c : ℤ) (p : Poly1) : Poly1 :=
  (List.range 11).map fun k => c * p.getD k 0

def poly1Mul (p q : Poly1) : Poly1 :=
  (List.range 11).map fun k =>
    (List.range (k + 1)).foldl (fun acc i => acc + p.getD i 0 * q.getD (k - i) 0) 0

/-- Exact evaluation of `evalPoly1` when `p` has length 11. -/
theorem evalPoly1_len11 {p : Poly1} (hp : p.length = 11) (t : ℝ) :
    evalPoly1 p t = ∑ k : Fin 11, (p.getD k.val 0 : ℝ) * t ^ k.val := by
  rw [evalPoly1_eq_sum]
  have hcast : ∀ (m : ℕ) (_ : p.length = m),
      (∑ k : Fin p.length, (p.getD k.val 0 : ℝ) * t ^ k.val) =
      ∑ k : Fin m, (p.getD k.val 0 : ℝ) * t ^ k.val := by
    rintro _ rfl; rfl
  exact hcast 11 hp

/-- Compute the degree-10 univariate polynomial of a symmetric quadratic form
`∑ i, ∑ j, M[i][j] * t^(i + j)` (for `i, j < m`, `2 * (m - 1) ≤ 10`). -/
def quadPoly1Monomial (m : ℕ) (M : List (List ℤ)) : Poly1 :=
  (List.range 11).map fun d =>
    (List.range m).foldl (fun acc i =>
      if i ≤ d ∧ d - i < m then acc + matGet M i (d - i) else acc) 0

private theorem quadPoly1Monomial_eval {m : ℕ} (hm : m ≤ 6) (M : List (List ℤ)) (t : ℝ) :
    evalPoly1 (quadPoly1Monomial m M) t =
      ∑ i : Fin m, ∑ j : Fin m, (matGet M i.val j.val : ℝ) * t ^ (i.val + j.val) := by
  have hlen : (quadPoly1Monomial m M).length = 11 := by simp [quadPoly1Monomial]
  rw [evalPoly1_len11 hlen]
  have hget : ∀ k : Fin 11, ((quadPoly1Monomial m M).getD k.val 0 : ℝ) =
      ∑ i : Fin m, ∑ j : Fin m, if i.val + j.val = k.val then (matGet M i.val j.val : ℝ) else 0 := by
    intro k
    simp only [quadPoly1Monomial, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range k.isLt, Option.map_some, Option.getD_some]
    have hfold : (List.range m).foldl (fun acc i =>
        if i ≤ k.val ∧ k.val - i < m then acc + matGet M i (k.val - i) else acc) 0 =
        (List.range m).foldl (fun acc i =>
          acc + if i ≤ k.val ∧ k.val - i < m then matGet M i (k.val - i) else 0) 0 := by
      congr 1; ext acc i; split_ifs <;> omega
    rw [hfold, foldl_add_eq_sum, zero_add, sum_range_eq_fin]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hcond : i.val ≤ k.val ∧ k.val - i.val < m
    · simp only [hcond]
      let j0 : Fin m := ⟨k.val - i.val, hcond.2⟩
      rw [Finset.sum_eq_single j0]
      · have hj0 : i.val + j0.val = k.val := by simp [j0]; omega
        simp [hj0, j0]
      · intro j _ hne
        have : i.val + j.val ≠ k.val := by
          intro heq
          apply hne
          ext; simp [j0]; omega
        simp [this]
      · intro h; exact absurd (Finset.mem_univ j0) h
    · simp only [hcond, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have : i.val + j.val ≠ k.val := by
        intro heq
        apply hcond
        exact ⟨by omega, by omega⟩
      simp [this]
  simp_rw [hget, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  let k0 : Fin 11 := ⟨i.val + j.val, by omega⟩
  rw [Finset.sum_eq_single k0]
  · simp [k0]
  · intro k _ hne
    have : i.val + j.val ≠ k.val := fun heq => hne (Fin.ext heq.symm)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ k0) h

/-- Polynomial `(1 - t²) ^ k` as a degree-10 `Poly1` (for `k ≤ 5`). -/
def oneMinusT2Pow : ℕ → Poly1
  | 0 => [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => [1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => [1, 0, -2, 0, 1, 0, 0, 0, 0, 0, 0]
  | 3 => [1, 0, -3, 0, 3, 0, -1, 0, 0, 0, 0]
  | 4 => [1, 0, -4, 0, 6, 0, -4, 0, 1, 0, 0]
  | 5 => [1, 0, -5, 0, 10, 0, -10, 0, 5, 0, -1]
  | _ => poly1Zero

/-! ## Computable trivariate `S₃`-symmetric integer polynomials (`Poly3`) -/

/-- Canonical sorted exponent triple `(a, b, c)` with `a ≥ b ≥ c`. -/
def sortTriple (a b c : ℕ) : ℕ × ℕ × ℕ :=
  let (x, y) := if a ≥ b then (a, b) else (b, a)
  if c ≥ x then (c, x, y)
  else if c ≥ y then (x, c, y)
  else (x, y, c)

/-- Sparse trivariate integer polynomial: list of `(a, b, c, coeff)` terms. -/
abbrev Poly3 := List (ℕ × ℕ × ℕ × ℤ)

/-- Evaluate a sparse `Poly3` at `(u, v, t) ∈ ℝ³`. -/
def evalPoly3 (p : Poly3) (u v t : ℝ) : ℝ :=
  p.foldl (fun acc term => acc + (term.2.2.2 : ℝ) * (u ^ term.1 * v ^ term.2.1 * t ^ term.2.2.1)) 0

private theorem evalPoly3_eq_sum (p : Poly3) (u v t : ℝ) :
    evalPoly3 p u v t =
      (p.map fun term => (term.2.2.2 : ℝ) * (u ^ term.1 * v ^ term.2.1 * t ^ term.2.2.1)).sum := by
  unfold evalPoly3
  have h : ∀ (l : Poly3) (init : ℝ),
      l.foldl (fun acc term => acc + (term.2.2.2 : ℝ) * (u ^ term.1 * v ^ term.2.1 * t ^ term.2.2.1)) init =
      init + (l.map fun term => (term.2.2.2 : ℝ) * (u ^ term.1 * v ^ term.2.1 * t ^ term.2.2.1)).sum := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons a s ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      ring
  rw [h, zero_add]

theorem evalPoly3_nil (u v t : ℝ) : evalPoly3 [] u v t = 0 := rfl

theorem evalPoly3_append (p q : Poly3) (u v t : ℝ) :
    evalPoly3 (p ++ q) u v t = evalPoly3 p u v t + evalPoly3 q u v t := by
  simp [evalPoly3_eq_sum]

/-- Scale a `Poly3` by an integer `c`. -/
def poly3Scale (c : ℤ) (p : Poly3) : Poly3 :=
  if c == 0 then []
  else p.map fun ⟨a, b, d, v⟩ => (a, b, d, c * v)

theorem evalPoly3_scale (c : ℤ) (p : Poly3) (u v t : ℝ) :
    evalPoly3 (poly3Scale c p) u v t = (c : ℝ) * evalPoly3 p u v t := by
  unfold poly3Scale
  by_cases hc : c == 0
  · have hc0 : c = 0 := by simpa using hc
    subst hc0; simp [evalPoly3_eq_sum]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, evalPoly3_eq_sum, List.map_map]
    induction p with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, Int.cast_mul, mul_add]
      rw [ih]; ring

/-- Multiply two sparse `Poly3` polynomials. -/
def poly3Mul (p q : Poly3) : Poly3 :=
  p.flatMap fun ⟨a1, b1, c1, v1⟩ =>
    q.map fun ⟨a2, b2, c2, v2⟩ => (a1 + a2, b1 + b2, c1 + c2, v1 * v2)

theorem evalPoly3_mul (p q : Poly3) (u v t : ℝ) :
    evalPoly3 (poly3Mul p q) u v t = evalPoly3 p u v t * evalPoly3 q u v t := by
  have hhead : ∀ (a1 b1 c1 : ℕ) (v1 : ℤ),
      evalPoly3 (q.map fun ⟨a2, b2, c2, v2⟩ => (a1 + a2, b1 + b2, c1 + c2, v1 * v2)) u v t =
        ((v1 : ℝ) * (u ^ a1 * v ^ b1 * t ^ c1)) * evalPoly3 q u v t := by
    intro a1 b1 c1 v1
    simp only [evalPoly3_eq_sum, List.map_map]
    induction q with
    | nil => simp
    | cons y ys ihy =>
      rcases y with ⟨a2, b2, c2, v2⟩
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, mul_add, Int.cast_mul, pow_add]
      rw [ihy]; ring
  unfold poly3Mul
  induction p with
  | nil => simp [evalPoly3_eq_sum]
  | cons x xs ih =>
    rcases x with ⟨a1, b1, c1, v1⟩
    simp only [List.flatMap_cons, evalPoly3_append, ih, hhead]
    simp only [evalPoly3_eq_sum, List.map_cons, List.sum_cons]
    ring

/-- Primitive lexicographic strict order on exponent triples using `Nat.blt`/`Nat.beq`. -/
def tripleLt (a b c a' b' c' : ℕ) : Bool :=
  Nat.blt a a' || (Nat.beq a a' && (Nat.blt b b' || (Nat.beq b b' && Nat.blt c c')))

/-- Structurally recursive inner step of `mergePoly3`: merges head `x` and tail `r1`
(via continuation `mergeTail = mergePoly3 r1`) into `q`. Pure `List.rec` for kernel reduction. -/
def mergeStep (x : ℕ × ℕ × ℕ × ℤ) (r1 : Poly3) (mergeTail : Poly3 → Poly3) : Poly3 → Poly3
  | [] => x :: r1
  | y :: r2 =>
    if Nat.beq x.1 y.1 && Nat.beq x.2.1 y.2.1 && Nat.beq x.2.2.1 y.2.2.1 then
      let s := x.2.2.2 + y.2.2.2
      if s == 0 then mergeTail r2
      else (x.1, x.2.1, x.2.2.1, s) :: mergeTail r2
    else if tripleLt x.1 x.2.1 x.2.2.1 y.1 y.2.1 y.2.2.1 then
      x :: mergeTail (y :: r2)
    else
      y :: mergeStep x r1 mergeTail r2

private theorem evalPoly3_mergeStep (x : ℕ × ℕ × ℕ × ℤ) (r1 : Poly3) (mergeTail : Poly3 → Poly3)
    (u v t : ℝ)
    (hTail : ∀ q, evalPoly3 (mergeTail q) u v t = evalPoly3 r1 u v t + evalPoly3 q u v t)
    (q : Poly3) :
    evalPoly3 (mergeStep x r1 mergeTail q) u v t =
      evalPoly3 (x :: r1) u v t + evalPoly3 q u v t := by
  induction q with
  | nil => simp [mergeStep, evalPoly3_nil]
  | cons y r2 ih =>
    rcases x with ⟨a1, b1, c1, v1⟩
    rcases y with ⟨a2, b2, c2, v2⟩
    unfold mergeStep
    dsimp only
    by_cases heq : (Nat.beq a1 a2 && Nat.beq b1 b2 && Nat.beq c1 c2) = true
    · simp only [heq, ↓reduceIte]
      have h1 : (a1 = a2 ∧ b1 = b2) ∧ c1 = c2 := by
        simpa [Bool.and_eq_true, Nat.beq_eq] using heq
      rcases h1 with ⟨⟨rfl, rfl⟩, rfl⟩
      by_cases hs : (v1 + v2 == 0) = true
      · simp only [hs, ↓reduceIte, hTail]
        have hs0 : v1 + v2 = 0 := by simpa using hs
        have hs0R : (v1 : ℝ) + (v2 : ℝ) = 0 := by exact_mod_cast hs0
        simp only [evalPoly3_eq_sum, List.map_cons, List.sum_cons]
        linear_combination -(u ^ a1 * v ^ b1 * t ^ c1) * hs0R
      · simp only [hs, Bool.false_eq_true, ↓reduceIte]
        simp only [evalPoly3_eq_sum, List.map_cons, List.sum_cons] at hTail ⊢
        rw [hTail r2]; push_cast; ring
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      by_cases hlt : tripleLt a1 b1 c1 a2 b2 c2 = true
      · simp only [hlt, ↓reduceIte]
        simp only [evalPoly3_eq_sum, List.map_cons, List.sum_cons] at hTail ⊢
        rw [hTail ((a2, b2, c2, v2) :: r2)]
        simp only [List.map_cons, List.sum_cons]
        ring
      · simp only [hlt, Bool.false_eq_true, ↓reduceIte]
        simp only [evalPoly3_eq_sum, List.map_cons, List.sum_cons] at ih ⊢
        rw [ih]; ring

/-- Structurally recursive linear-time merge of two `Poly3` lists (kernel-reducible,
unconditionally preserves `evalPoly3`). -/
def mergePoly3 : Poly3 → Poly3 → Poly3
  | [], q => q
  | x :: r1, q => mergeStep x r1 (mergePoly3 r1) q

theorem evalPoly3_mergePoly3 (p q : Poly3) (u v t : ℝ) :
    evalPoly3 (mergePoly3 p q) u v t = evalPoly3 p u v t + evalPoly3 q u v t := by
  induction p generalizing q with
  | nil => simp [mergePoly3, evalPoly3_nil]
  | cons x r1 ih =>
    unfold mergePoly3
    exact evalPoly3_mergeStep x r1 (mergePoly3 r1) u v t ih q

/-- Multiply `p` and `q` by shifting `q` per term of `p` and merging in linear time. -/
def mulPoly3Sorted (p q : Poly3) : Poly3 :=
  p.foldl (fun acc ⟨a1, b1, c1, v1⟩ =>
    if v1 == 0 then acc
    else mergePoly3 (q.map fun ⟨a2, b2, c2, v2⟩ => (a1 + a2, b1 + b2, c1 + c2, v1 * v2)) acc) []

theorem evalPoly3_mulPoly3Sorted (p q : Poly3) (u v t : ℝ) :
    evalPoly3 (mulPoly3Sorted p q) u v t = evalPoly3 p u v t * evalPoly3 q u v t := by
  have hterm : ∀ (a1 b1 c1 : ℕ) (v1 : ℤ),
      evalPoly3 (q.map fun ⟨a2, b2, c2, v2⟩ => (a1 + a2, b1 + b2, c1 + c2, v1 * v2)) u v t =
        ((v1 : ℝ) * (u ^ a1 * v ^ b1 * t ^ c1)) * evalPoly3 q u v t := by
    intro a1 b1 c1 v1
    simp only [evalPoly3_eq_sum, List.map_map]
    induction q with
    | nil => simp
    | cons y ys ih =>
      rcases y with ⟨a2, b2, c2, v2⟩
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, mul_add, Int.cast_mul, pow_add]
      rw [ih]; ring
  unfold mulPoly3Sorted
  have hfold : ∀ (l acc : Poly3),
      evalPoly3 (l.foldl (fun acc ⟨a1, b1, c1, v1⟩ =>
        if v1 == 0 then acc
        else mergePoly3 (q.map fun ⟨a2, b2, c2, v2⟩ => (a1 + a2, b1 + b2, c1 + c2, v1 * v2)) acc) acc) u v t =
      evalPoly3 l u v t * evalPoly3 q u v t + evalPoly3 acc u v t := by
    intro l
    induction l with
    | nil => intro acc; simp [evalPoly3_nil]
    | cons x xs ih =>
      intro acc
      rcases x with ⟨a1, b1, c1, v1⟩
      simp only [List.foldl_cons, ih]
      by_cases hv : v1 == 0
      · have h0 : v1 = 0 := by simpa using hv
        subst h0
        simp only [beq_self_eq_true, ↓reduceIte, evalPoly3_eq_sum, List.map_cons, List.sum_cons,
          Int.cast_zero, zero_mul, zero_add]
      · simp only [hv, Bool.false_eq_true, ↓reduceIte]
        rw [evalPoly3_mergePoly3, hterm]
        simp only [evalPoly3_eq_sum, List.map_cons, List.sum_cons]
        ring
  simpa [evalPoly3_nil] using hfold p []

/-- Insert `(k, coeff)` into a sorted association list keyed by `ℕ × ℕ × ℕ`, merging like keys. -/
def insertTerm3 (a b c : ℕ) (v : ℤ) : Poly3 → Poly3
  | [] => if v == 0 then [] else [(a, b, c, v)]
  | (a', b', c', v') :: rest =>
    if (a, b, c) == (a', b', c') then
      let s := v + v'
      if s == 0 then rest else (a', b', c', s) :: rest
    else if tripleLt a b c a' b' c' then
      if v == 0 then (a', b', c', v') :: rest
      else (a, b, c, v) :: (a', b', c', v') :: rest
    else
      (a', b', c', v') :: insertTerm3 a b c v rest

private theorem evalPoly3_insertTerm3 (a b c : ℕ) (val : ℤ) (p : Poly3) (u v t : ℝ) :
    evalPoly3 (insertTerm3 a b c val p) u v t =
      (val : ℝ) * (u ^ a * v ^ b * t ^ c) + evalPoly3 p u v t := by
  induction p with
  | nil =>
    unfold insertTerm3
    by_cases hv : val == 0
    · have h0 : val = 0 := by simpa using hv
      subst h0; simp [evalPoly3_eq_sum]
    · simp [hv, evalPoly3_eq_sum]
  | cons x xs ih =>
    rcases x with ⟨a', b', c', v'⟩
    unfold insertTerm3
    by_cases heq : (a, b, c) == (a', b', c')
    · have h1 : a = a' ∧ b = b' ∧ c = c' := by simpa [Prod.ext_iff] using heq
      rcases h1 with ⟨rfl, rfl, rfl⟩
      simp only [heq, ↓reduceIte]
      by_cases hs : val + v' == 0
      · have hs0 : val + v' = 0 := by simpa using hs
        have hs0R : (val : ℝ) + (v' : ℝ) = 0 := by exact_mod_cast hs0
        simp only [hs, ↓reduceIte, evalPoly3_eq_sum, List.map_cons, List.sum_cons]
        linear_combination -(u ^ a * v ^ b * t ^ c) * hs0R
      · simp only [hs, Bool.false_eq_true, ↓reduceIte, evalPoly3_eq_sum, List.map_cons,
          List.sum_cons, Int.cast_add]
        ring
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      split_ifs with hlt hv
      · have h0 : val = 0 := by simpa using hv
        subst h0; simp [evalPoly3_eq_sum]
      · simp [evalPoly3_eq_sum]
      · simp only [evalPoly3_eq_sum, List.map_cons, List.sum_cons] at ih ⊢
        linarith

/-- Combine like monomials in a `Poly3` without symmetrizing. -/
def normalizePoly3 (p : Poly3) : Poly3 :=
  p.foldl (fun acc ⟨a, b, c, v⟩ => insertTerm3 a b c v acc) []

theorem evalPoly3_normalize (p : Poly3) (u v t : ℝ) :
    evalPoly3 (normalizePoly3 p) u v t = evalPoly3 p u v t := by
  unfold normalizePoly3
  have h : ∀ (l acc : Poly3),
      evalPoly3 (l.foldl (fun acc ⟨a, b, c, v⟩ => insertTerm3 a b c v acc) acc) u v t =
      evalPoly3 l u v t + evalPoly3 acc u v t := by
    intro l
    induction l with
    | nil => intro acc; simp [evalPoly3_eq_sum]
    | cons x xs ih =>
      intro acc
      rcases x with ⟨a, b, c, val⟩
      simp only [List.foldl_cons, ih, evalPoly3_insertTerm3]
      simp only [evalPoly3_eq_sum, List.map_cons, List.sum_cons]
      ring
  simpa [evalPoly3_nil] using h p []

/-- `S₃`-canonicalization of a `Poly3`: sorts each monomial's exponent triple `(a, b, c)`
descending and merges like terms. Preserves `sym3 (evalPoly3 ·)` identically! -/
def sym3Canon (p : Poly3) : Poly3 :=
  p.foldl (fun acc ⟨a, b, c, v⟩ =>
    let (a', b', c') := sortTriple a b c
    insertTerm3 a' b' c' v acc) []

private theorem sym3_evalMono_sortTriple (a b c : ℕ) (u v t : ℝ) :
    let (a', b', c') := sortTriple a b c
    sym3 (fun u v t => u ^ a' * v ^ b' * t ^ c') u v t =
      sym3 (fun u v t => u ^ a * v ^ b * t ^ c) u v t := by
  unfold sortTriple
  split_ifs <;> dsimp only <;> split_ifs <;> unfold sym3 <;> ring

private theorem sym3_linear_add (f g : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    sym3 (fun u v t => f u v t + g u v t) u v t = sym3 f u v t + sym3 g u v t := by
  unfold sym3; ring

private theorem sym3_linear_mul (c : ℝ) (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    sym3 (fun u v t => c * f u v t) u v t = c * sym3 f u v t := by
  unfold sym3; ring

theorem sym3_evalPoly3_sym3Canon (p : Poly3) (u v t : ℝ) :
    sym3 (evalPoly3 (sym3Canon p)) u v t = sym3 (evalPoly3 p) u v t := by
  unfold sym3Canon
  have h : ∀ (l acc : Poly3),
      sym3 (evalPoly3 (l.foldl (fun acc ⟨a, b, c, v⟩ =>
        let (a', b', c') := sortTriple a b c
        insertTerm3 a' b' c' v acc) acc)) u v t =
      sym3 (evalPoly3 l) u v t + sym3 (evalPoly3 acc) u v t := by
    intro l
    induction l with
    | nil => intro acc; simp [evalPoly3_nil, sym3]
    | cons x xs ih =>
      intro acc
      rcases x with ⟨a, b, c, val⟩
      simp only [List.foldl_cons, ih]
      have hins : sym3 (evalPoly3 (insertTerm3 (sortTriple a b c).1 (sortTriple a b c).2.1
          (sortTriple a b c).2.2 val acc)) u v t =
          (val : ℝ) * sym3 (fun u v t => u ^ a * v ^ b * t ^ c) u v t +
          sym3 (evalPoly3 acc) u v t := by
        have heq : evalPoly3 (insertTerm3 (sortTriple a b c).1 (sortTriple a b c).2.1
            (sortTriple a b c).2.2 val acc) =
            fun u v t => (val : ℝ) * (u ^ (sortTriple a b c).1 * v ^ (sortTriple a b c).2.1 *
              t ^ (sortTriple a b c).2.2) + evalPoly3 acc u v t := by
          ext u' v' t'
          exact evalPoly3_insertTerm3 _ _ _ _ _ u' v' t'
        rw [heq, sym3_linear_add, sym3_linear_mul]
        have hst := sym3_evalMono_sortTriple a b c u v t
        simp only at hst
        rw [hst]
      have hcons : evalPoly3 ((a, b, c, val) :: xs) =
          fun u v t => (val : ℝ) * (u ^ a * v ^ b * t ^ c) + evalPoly3 xs u v t := by
        ext u' v' t'
        simp [evalPoly3_eq_sum]
      rw [hcons, sym3_linear_add, sym3_linear_mul, hins]
      ring
  have h0 : sym3 (evalPoly3 []) u v t = 0 := by simp [evalPoly3_nil, sym3]
  simpa [h0] using h p []

/-- Insert all terms of `p` into a sorted `Poly3` accumulator `acc`. -/
def addPoly3 (p acc : Poly3) : Poly3 :=
  p.foldl (fun a ⟨i, j, k, v⟩ => insertTerm3 i j k v a) acc

private theorem evalPoly3_addPoly3 (p acc : Poly3) (u v t : ℝ) :
    evalPoly3 (addPoly3 p acc) u v t = evalPoly3 p u v t + evalPoly3 acc u v t := by
  unfold addPoly3
  induction p generalizing acc with
  | nil => simp [evalPoly3_nil]
  | cons x xs ih =>
    rcases x with ⟨a, b, c, val⟩
    simp only [List.foldl_cons, ih, evalPoly3_insertTerm3]
    simp only [evalPoly3_eq_sum, List.map_cons, List.sum_cons]
    ring

/-- Insert `c • p` directly into a sorted `Poly3` accumulator `acc`. -/
def addScaledPoly3 (c : ℤ) (p acc : Poly3) : Poly3 :=
  if c == 0 then acc
  else p.foldl (fun a ⟨i, j, k, v⟩ => insertTerm3 i j k (c * v) a) acc

private theorem evalPoly3_addScaledPoly3 (c : ℤ) (p acc : Poly3) (u v t : ℝ) :
    evalPoly3 (addScaledPoly3 c p acc) u v t = (c : ℝ) * evalPoly3 p u v t + evalPoly3 acc u v t := by
  unfold addScaledPoly3
  by_cases hc : c == 0
  · have h0 : c = 0 := by simpa using hc
    subst h0; simp
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    induction p generalizing acc with
    | nil => simp [evalPoly3_nil]
    | cons x xs ih =>
      rcases x with ⟨a, b, d, val⟩
      simp only [List.foldl_cons, ih, evalPoly3_insertTerm3]
      simp only [evalPoly3_eq_sum, List.map_cons, List.sum_cons, Int.cast_mul]
      ring

/-- Fast `O(m)`-multiplication quadratic form `∑ i < m, b[i] * (∑ j < m, M[i][j] * b[j])`
as a `Poly3` using linear-time `mergePoly3` and `mulPoly3Sorted`. -/
def quadPoly3 (m : ℕ) (M : List (List ℤ)) (basis : List Poly3) : Poly3 :=
  (List.range m).foldl (fun acc i =>
    let bi := basis.getD i []
    let qi := (List.range m).foldl (fun qacc j =>
      mergePoly3 (poly3Scale (matGet M i j) (basis.getD j [])) qacc) []
    mergePoly3 (mulPoly3Sorted bi qi) acc) []

theorem evalPoly3_quadPoly3 (m : ℕ) (M : List (List ℤ)) (basis : List Poly3) (u v t : ℝ) :
    evalPoly3 (quadPoly3 m M basis) u v t =
      ∑ i : Fin m, ∑ j : Fin m,
        (matGet M i.val j.val : ℝ) *
          (evalPoly3 (basis.getD i.val []) u v t * evalPoly3 (basis.getD j.val []) u v t) := by
  unfold quadPoly3
  have hinner : ∀ i : ℕ,
      evalPoly3 ((List.range m).foldl (fun qacc j =>
        mergePoly3 (poly3Scale (matGet M i j) (basis.getD j [])) qacc) []) u v t =
      ∑ j : Fin m, (matGet M i j.val : ℝ) * evalPoly3 (basis.getD j.val []) u v t := by
    intro i
    have hfold : ∀ (l : List ℕ) (qacc : Poly3),
        evalPoly3 (l.foldl (fun qacc j =>
          mergePoly3 (poly3Scale (matGet M i j) (basis.getD j [])) qacc) qacc) u v t =
        evalPoly3 qacc u v t +
        (l.map fun j => (matGet M i j : ℝ) * evalPoly3 (basis.getD j []) u v t).sum := by
      intro l
      induction l with
      | nil => intro qacc; simp
      | cons j js ih =>
        intro qacc
        simp only [List.foldl_cons, ih, evalPoly3_mergePoly3, evalPoly3_scale, List.map_cons,
          List.sum_cons]
        ring
    rw [hfold, evalPoly3_nil, zero_add, ← list_map_finRange_eq_range, ← Fin.sum_univ_def]
  have houter : ∀ (l : List ℕ) (acc : Poly3),
      evalPoly3 (l.foldl (fun acc i =>
        let bi := basis.getD i []
        let qi := (List.range m).foldl (fun qacc j =>
          mergePoly3 (poly3Scale (matGet M i j) (basis.getD j [])) qacc) []
        mergePoly3 (mulPoly3Sorted bi qi) acc) acc) u v t =
      evalPoly3 acc u v t +
      (l.map fun i => evalPoly3 (basis.getD i []) u v t *
        ∑ j : Fin m, (matGet M i j.val : ℝ) * evalPoly3 (basis.getD j.val []) u v t).sum := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons i is ih =>
      intro acc
      simp only [List.foldl_cons, ih, evalPoly3_mergePoly3, evalPoly3_mulPoly3Sorted,
        hinner, List.map_cons, List.sum_cons]
      ring
  rw [houter, evalPoly3_nil, zero_add, ← list_map_finRange_eq_range, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Nonnegativity of `evalPoly3 (quadPoly3 m M basis)` when `toRealMat m D M` is PSD. -/
theorem evalPoly3_quadPoly3_nonneg {m D : ℕ} (hD : 0 < D) {M : List (List ℤ)}
    (hM : (toRealMat m D M).PosSemidef) (basis : List Poly3) (u v t : ℝ) :
    0 ≤ evalPoly3 (quadPoly3 m M basis) u v t := by
  rw [evalPoly3_quadPoly3]
  let vec : Fin m → ℝ := fun i => evalPoly3 (basis.getD i.val []) u v t
  have hq := posSemidef_quad_nonneg hM vec
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hmul : (D : ℝ) * (∑ a : Fin m, ∑ b : Fin m, vec a * toRealMat m D M a b * vec b) =
      ∑ i : Fin m, ∑ j : Fin m,
        (matGet M i.val j.val : ℝ) * (vec i * vec j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [toRealMat, Matrix.of_apply]
    field_simp [hD_pos.ne']
  have : 0 ≤ (D : ℝ) * ∑ a : Fin m, ∑ b : Fin m, vec a * toRealMat m D M a b * vec b :=
    mul_nonneg hD_pos.le hq
  linarith

/-! ## Exact `S₃`-reduced SOS bases and Bachoc–Vallentin `bvQ` as `Poly3` -/

def bvQPoly3 : ℕ → Poly3
  | 0 => [(0, 0, 0, 1)]
  | 1 => [(0, 0, 1, 1), (1, 1, 0, -1)]
  | k + 2 =>
    let two_t_uv : Poly3 := [(0, 0, 1, 2), (1, 1, 0, -2)]
    let prod_uv : Poly3 := [(0, 0, 0, 1), (2, 0, 0, -1), (0, 2, 0, -1), (2, 2, 0, 1)]
    normalizePoly3 (poly3Mul two_t_uv (bvQPoly3 (k + 1)) ++
      poly3Scale (-1) (poly3Mul prod_uv (bvQPoly3 k)))

theorem evalPoly3_bvQPoly3 (k : ℕ) (u v t : ℝ) :
    evalPoly3 (bvQPoly3 k) u v t = bvQ k u v t := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [bvQPoly3, bvQ, evalPoly3_eq_sum]
    | 1 => simp [bvQPoly3, bvQ, evalPoly3_eq_sum]; ring
    | k + 2 =>
      simp only [bvQPoly3, bvQ, evalPoly3_normalize, evalPoly3_append, evalPoly3_scale,
        evalPoly3_mul, ih (k + 1) (by omega), ih k (by omega)]
      simp only [evalPoly3_eq_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      ring

/-- Elementary symmetric polynomials `e₁, e₂, e₃` and `S₃`-reduced SOS bases. -/
def polyE1 : Poly3 := [(1, 0, 0, 1), (0, 1, 0, 1), (0, 0, 1, 1)]
def polyE2 : Poly3 := [(1, 1, 0, 1), (1, 0, 1, 1), (0, 1, 1, 1)]
def polyE3 : Poly3 := [(1, 1, 1, 1)]

def poly3Pow (p : Poly3) : ℕ → Poly3
  | 0 => [(0, 0, 0, 1)]
  | n + 1 => normalizePoly3 (poly3Mul p (poly3Pow p n))

def eMons (maxDeg : ℕ) : List Poly3 :=
  (List.range (maxDeg + 1)).flatMap fun a =>
    (List.range ((maxDeg - a) / 2 + 1)).flatMap fun b =>
      (List.range ((maxDeg - a - 2 * b) / 3 + 1)).map fun c =>
        normalizePoly3 (poly3Mul (poly3Pow polyE1 a)
          (normalizePoly3 (poly3Mul (poly3Pow polyE2 b) (poly3Pow polyE3 c))))

def vtMons (maxDeg : ℕ) : List Poly3 :=
  let vpt : Poly3 := [(0, 1, 0, 1), (0, 0, 1, 1)]
  let vt  : Poly3 := [(0, 1, 1, 1)]
  (List.range (maxDeg + 1)).flatMap fun a =>
    (List.range (maxDeg - a + 1)).flatMap fun b =>
      (List.range ((maxDeg - a - b) / 2 + 1)).map fun c =>
        normalizePoly3 (poly3Mul [(a, 0, 0, 1)]
          (normalizePoly3 (poly3Mul (poly3Pow vpt b) (poly3Pow vt c))))

def basisOneTriv : List Poly3 := eMons 5
def basisOneStd : List Poly3 :=
  let umv : Poly3 := [(1, 0, 0, 1), (0, 1, 0, -1)]
  let u2mv2 : Poly3 := [(2, 0, 0, 1), (0, 2, 0, -1)]
  (eMons 4).map (fun p => normalizePoly3 (poly3Mul umv p)) ++
  (eMons 3).map (fun p => normalizePoly3 (poly3Mul u2mv2 p))
def basisOneSign : List Poly3 :=
  let disc : Poly3 := normalizePoly3 (poly3Mul
    (normalizePoly3 (poly3Mul [(1, 0, 0, 1), (0, 1, 0, -1)] [(0, 1, 0, 1), (0, 0, 1, -1)]))
    [(0, 0, 1, 1), (1, 0, 0, -1)])
  (eMons 2).map (fun p => normalizePoly3 (poly3Mul disc p))

def basisDeltaTriv : List Poly3 := eMons 3
def basisDeltaStd : List Poly3 :=
  let umv : Poly3 := [(1, 0, 0, 1), (0, 1, 0, -1)]
  let u2mv2 : Poly3 := [(2, 0, 0, 1), (0, 2, 0, -1)]
  (eMons 2).map (fun p => normalizePoly3 (poly3Mul umv p)) ++
  (eMons 1).map (fun p => normalizePoly3 (poly3Mul u2mv2 p))
def basisDeltaSign : List Poly3 :=
  let disc : Poly3 := normalizePoly3 (poly3Mul
    (normalizePoly3 (poly3Mul [(1, 0, 0, 1), (0, 1, 0, -1)] [(0, 1, 0, 1), (0, 0, 1, -1)]))
    [(0, 0, 1, 1), (1, 0, 0, -1)])
  (eMons 0).map (fun p => normalizePoly3 (poly3Mul disc p))

def basisG1Even : List Poly3 := vtMons 4
def basisG1Odd : List Poly3 :=
  let vmt : Poly3 := [(0, 1, 0, 1), (0, 0, 1, -1)]
  (vtMons 3).map (fun p => normalizePoly3 (poly3Mul vmt p))

def multDelta : Poly3 := [(0, 0, 0, 1), (1, 1, 1, 2), (2, 0, 0, -1), (0, 2, 0, -1), (0, 0, 2, -1)]
def multG1 (sNum sDen : ℤ) : Poly3 := [(0, 0, 0, sNum), (1, 0, 0, sNum - sDen), (2, 0, 0, -sDen)]
def multG2 (sNum sDen : ℤ) : Poly3 :=
  [(0, 0, 0, sNum * sNum), (0, 1, 0, -sNum * sDen), (0, 0, 1, -sNum * sDen), (0, 1, 1, sDen * sDen)]

private theorem evalPoly3_multDelta (u v t : ℝ) :
    evalPoly3 multDelta u v t = gramDet3 u v t := by
  simp only [multDelta, evalPoly3_eq_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    gramDet3]
  push_cast; ring

private theorem evalPoly3_multG1 (sNum sDen : ℤ) (u v t : ℝ) :
    evalPoly3 (multG1 sNum sDen) u v t = ((sDen : ℝ) * ((sNum : ℝ) / (sDen : ℝ) - u) * (u + 1)) ∨
    sDen = 0 := by
  by_cases h : sDen = 0
  · exact Or.inr h
  · left
    have hR : (sDen : ℝ) ≠ 0 := by exact_mod_cast h
    simp only [multG1, evalPoly3_eq_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast; field_simp [hR]; ring

private theorem evalPoly3_multG2 (sNum sDen : ℤ) (u v t : ℝ) :
    evalPoly3 (multG2 sNum sDen) u v t =
      ((sDen : ℝ) ^ 2 * (((sNum : ℝ) / (sDen : ℝ) - v) * ((sNum : ℝ) / (sDen : ℝ) - t))) ∨
    sDen = 0 := by
  by_cases h : sDen = 0
  · exact Or.inr h
  · left
    have hR : (sDen : ℝ) ≠ 0 := by exact_mod_cast h
    simp only [multG2, evalPoly3_eq_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast; field_simp [hR]; ring

/-! ## Degree-5 Bachoc–Vallentin rational SDP certificate (`BVCert5`) -/

/-- A degree-5 exact rational Bachoc–Vallentin SDP certificate on `S²`.
All matrices are stored as integer matrices scaled by common positive denominators
`dK` (kernel matrices `A₀, F₁, …, F₅`), `dS` (SOS Gram matrices), and `dR`
(upper-triangular Cholesky witnesses). -/
structure BVCert5 where
  sNum : ℤ
  sDen : ℕ
  dK : ℕ
  dS : ℕ
  dR : ℕ
  -- Kernel matrices and Cholesky witnesses
  A0 : List (List ℤ)
  R_A0 : List (List ℤ)
  F1 : List (List ℤ)
  R_F1 : List (List ℤ)
  F2 : List (List ℤ)
  R_F2 : List (List ℤ)
  F3 : List (List ℤ)
  R_F3 : List (List ℤ)
  F4 : List (List ℤ)
  R_F4 : List (List ℤ)
  F5 : List (List ℤ)
  R_F5 : List (List ℤ)
  -- Univariate SOS matrices on [-1, s]
  S2_0 : List (List ℤ)
  R_S2_0 : List (List ℤ)
  S2_1 : List (List ℤ)
  R_S2_1 : List (List ℤ)
  -- 10 S₃-reduced trivariate SOS matrices on Δ(s)
  M_one_triv : List (List ℤ)
  R_one_triv : List (List ℤ)
  M_one_std : List (List ℤ)
  R_one_std : List (List ℤ)
  M_one_sign : List (List ℤ)
  R_one_sign : List (List ℤ)
  M_delta_triv : List (List ℤ)
  R_delta_triv : List (List ℤ)
  M_delta_std : List (List ℤ)
  R_delta_std : List (List ℤ)
  M_delta_sign : List (List ℤ)
  R_delta_sign : List (List ℤ)
  M_g1_even : List (List ℤ)
  R_g1_even : List (List ℤ)
  M_g1_odd : List (List ℤ)
  R_g1_odd : List (List ℤ)
  M_g2_even : List (List ℤ)
  R_g2_even : List (List ℤ)
  M_g2_odd : List (List ℤ)
  R_g2_odd : List (List ℤ)

namespace BVCert5

/-- Rational inner-product threshold `s = sNum / sDen`. -/
def sRat (c : BVCert5) : ℚ := (c.sNum : ℚ) / (c.sDen : ℚ)

/-- Rational upper bound `1 + A₀(0, 0) / dK`. -/
def bound (c : BVCert5) : ℚ := 1 + (matGet c.A0 0 0 : ℚ) / (c.dK : ℚ)

/-- Extract the 6×6 submatrix `A₀[1..6, 1..6]`. -/
def A0Sub (c : BVCert5) : List (List ℤ) :=
  (List.range 6).map fun i => (List.range 6).map fun j => matGet c.A0 (i + 1) (j + 1)

/-- Degree-10 univariate polynomial `sDen * dK * G₂(t)` (Wait: scaled by `sDen * dS` on LHS
and `sDen * dK` on RHS to compare over `ℤ`!). Specifically:
`polyG2Scaled c` computes `dK * G₂(t)` as a `Poly1`. -/
def polyG2 (c : BVCert5) : Poly1 :=
  let constP : Poly1 := [(c.dK : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  let crossP : Poly1 := (List.range 11).map fun i => if i < 6 then 2 * matGet c.A0 0 (i + 1) else 0
  let a0P : Poly1 := quadPoly1Monomial 6 c.A0Sub
  let f1P : Poly1 := poly1Mul (quadPoly1Monomial 5 c.F1) (oneMinusT2Pow 1)
  let f2P : Poly1 := poly1Mul (quadPoly1Monomial 4 c.F2) (oneMinusT2Pow 2)
  let f3P : Poly1 := poly1Mul (quadPoly1Monomial 3 c.F3) (oneMinusT2Pow 3)
  let f4P : Poly1 := poly1Mul (quadPoly1Monomial 2 c.F4) (oneMinusT2Pow 4)
  let f5P : Poly1 := poly1Mul (quadPoly1Monomial 1 c.F5) (oneMinusT2Pow 5)
  poly1Add constP (poly1Add crossP (poly1Add a0P
    (poly1Add f1P (poly1Add f2P (poly1Add f3P (poly1Add f4P f5P))))))

/-- Univariate SOS RHS scaled by `sDen * dS`:
`sDen * S₂₀(t) + (sNum + (sNum - sDen) t - sDen t²) * S₂₁(t)`. -/
def polyRHS2 (c : BVCert5) : Poly1 :=
  let sDenI : ℤ := (c.sDen : ℤ)
  let p0 := poly1Scale sDenI (quadPoly1Monomial 6 c.S2_0)
  let g1 : Poly1 := [c.sNum, c.sNum - sDenI, -sDenI, 0, 0, 0, 0, 0, 0, 0, 0]
  let p1 := poly1Mul g1 (quadPoly1Monomial 5 c.S2_1)
  poly1Add p0 p1

/-- Trivariate `G₃(u, v, t)` scaled by `dK` as a `Poly3`. -/
def polyG3 (c : BVCert5) : Poly3 :=
  let monU : ℕ → List Poly3 := fun m => (List.range m).map fun a => [(a, 0, 0, 1)]
  let monV : ℕ → List Poly3 := fun m => (List.range m).map fun b => [(0, b, 0, 1)]
  let buildUV (m : ℕ) (M : List (List ℤ)) : Poly3 :=
    (List.range m).foldl (fun acc i =>
      let bi := (monU m).getD i []
      let qi := (List.range m).foldl (fun qacc j =>
        normalizePoly3 (qacc ++ poly3Scale (matGet M i j) ((monV m).getD j []))) []
      normalizePoly3 (acc ++ poly3Mul bi qi)) []
  let p0 := buildUV 6 c.A0Sub
  let p1 := normalizePoly3 (poly3Mul (buildUV 5 c.F1) (bvQPoly3 1))
  let p2 := normalizePoly3 (poly3Mul (buildUV 4 c.F2) (bvQPoly3 2))
  let p3 := normalizePoly3 (poly3Mul (buildUV 3 c.F3) (bvQPoly3 3))
  let p4 := normalizePoly3 (poly3Mul (buildUV 2 c.F4) (bvQPoly3 4))
  let p5 := normalizePoly3 (poly3Mul (buildUV 1 c.F5) (bvQPoly3 5))
  sym3Canon (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5)

/-- Trivariate SOS RHS scaled by `sDen² * dS`, canonicalized under `S₃`. -/
def polyRHS3 (c : BVCert5) : Poly3 :=
  let sDenI : ℤ := (c.sDen : ℤ)
  let sDen2 : ℤ := sDenI * sDenI
  let pOne := poly3Scale sDen2 (mergePoly3
    (quadPoly3 16 c.M_one_triv basisOneTriv)
    (mergePoly3 (quadPoly3 18 c.M_one_std basisOneStd)
      (quadPoly3 4 c.M_one_sign basisOneSign)))
  let pDelta := poly3Scale sDen2 (mulPoly3Sorted multDelta (mergePoly3
    (quadPoly3 7 c.M_delta_triv basisDeltaTriv)
    (mergePoly3 (quadPoly3 6 c.M_delta_std basisDeltaStd)
      (quadPoly3 1 c.M_delta_sign basisDeltaSign))))
  let pG1 := poly3Scale sDenI (mulPoly3Sorted (multG1 c.sNum sDenI) (mergePoly3
    (quadPoly3 22 c.M_g1_even basisG1Even)
    (quadPoly3 13 c.M_g1_odd basisG1Odd)))
  let pG2 := mulPoly3Sorted (multG2 c.sNum sDenI) (mergePoly3
    (quadPoly3 22 c.M_g2_even basisG1Even)
    (quadPoly3 13 c.M_g2_odd basisG1Odd))
  sym3Canon (mergePoly3 pOne (mergePoly3 pDelta (mergePoly3 pG1 pG2)))

/-- Complete computable verifier for `BVCert5`:
1. Positive denominators and `-1 < s`,
2. Symmetry and PSD of all 18 matrices (Cholesky + diagonal dominance),
3. Exact univariate polynomial identity `-sDen * dS * G₂ = dK * RHS₂`,
4. Exact `S₃`-symmetrized trivariate polynomial identity `-sDen² * dS * G₃ = dK * RHS₃`. -/
def isValid (c : BVCert5) : Bool :=
  let sDenI : ℤ := (c.sDen : ℤ)
  decide (0 < c.sDen) &&
  decide (-sDenI < c.sNum) &&
  decide (0 < c.dK) &&
  decide (0 < c.dS) &&
  decide (0 < c.dR) &&
  -- 6 Bachoc-Vallentin kernel matrices
  isCholeskyDDValid 7 c.dK c.dR c.A0 c.R_A0 &&
  isCholeskyDDValid 5 c.dK c.dR c.F1 c.R_F1 &&
  isCholeskyDDValid 4 c.dK c.dR c.F2 c.R_F2 &&
  isCholeskyDDValid 3 c.dK c.dR c.F3 c.R_F3 &&
  isCholeskyDDValid 2 c.dK c.dR c.F4 c.R_F4 &&
  isCholeskyDDValid 1 c.dK c.dR c.F5 c.R_F5 &&
  -- 2 univariate SOS matrices
  isCholeskyDDValid 6 c.dS c.dR c.S2_0 c.R_S2_0 &&
  isCholeskyDDValid 5 c.dS c.dR c.S2_1 c.R_S2_1 &&
  -- 10 S₃-reduced trivariate SOS matrices
  isCholeskyDDValid 16 c.dS c.dR c.M_one_triv c.R_one_triv &&
  isCholeskyDDValid 18 c.dS c.dR c.M_one_std c.R_one_std &&
  isCholeskyDDValid 4  c.dS c.dR c.M_one_sign c.R_one_sign &&
  isCholeskyDDValid 7  c.dS c.dR c.M_delta_triv c.R_delta_triv &&
  isCholeskyDDValid 6  c.dS c.dR c.M_delta_std c.R_delta_std &&
  isCholeskyDDValid 1  c.dS c.dR c.M_delta_sign c.R_delta_sign &&
  isCholeskyDDValid 22 c.dS c.dR c.M_g1_even c.R_g1_even &&
  isCholeskyDDValid 13 c.dS c.dR c.M_g1_odd c.R_g1_odd &&
  isCholeskyDDValid 22 c.dS c.dR c.M_g2_even c.R_g2_even &&
  isCholeskyDDValid 13 c.dS c.dR c.M_g2_odd c.R_g2_odd &&
  -- Exact univariate identity: -(sDen * dS) * (dK * G₂) == dK * (sDen * dS * RHS₂)
  (poly1Scale (-(sDenI * (c.dS : ℤ))) c.polyG2 == poly1Scale (c.dK : ℤ) c.polyRHS2) &&
  -- Exact trivariate S₃-symmetric identity: -(sDen² * dS) * (dK * G₃) == dK * (sDen² * dS * RHS₃)
  (sym3Canon (poly3Scale (-(sDenI * sDenI * (c.dS : ℤ))) c.polyG3) ==
    sym3Canon (poly3Scale (c.dK : ℤ) c.polyRHS3))

/-! ### Helper lemmas connecting `Poly1` / `Poly3` to `bvG2` / `bvG3` -/

private theorem evalPoly1_add {p q : Poly1} (hp : p.length = 11) (hq : q.length = 11) (t : ℝ) :
    evalPoly1 (poly1Add p q) t = evalPoly1 p t + evalPoly1 q t := by
  have hlen : (poly1Add p q).length = 11 := by simp [poly1Add]
  rw [evalPoly1_len11 hlen, evalPoly1_len11 hp, evalPoly1_len11 hq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [poly1Add, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range k.isLt,
    Option.map_some, Option.getD_some, Int.cast_add]
  ring

private theorem evalPoly1_scale {p : Poly1} (hp : p.length = 11) (c : ℤ) (t : ℝ) :
    evalPoly1 (poly1Scale c p) t = (c : ℝ) * evalPoly1 p t := by
  have hlen : (poly1Scale c p).length = 11 := by simp [poly1Scale]
  rw [evalPoly1_len11 hlen, evalPoly1_len11 hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [poly1Scale, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range k.isLt,
    Option.map_some, Option.getD_some, Int.cast_mul]
  ring

private theorem evalPoly1_mul {p q : Poly1} (hp : p.length = 11) (hq : q.length = 11)
    (hdeg : ∀ i j : Fin 11, 11 ≤ i.val + j.val → p.getD i.val 0 * q.getD j.val 0 = 0) (t : ℝ) :
    evalPoly1 (poly1Mul p q) t = evalPoly1 p t * evalPoly1 q t := by
  have hlen : (poly1Mul p q).length = 11 := by simp [poly1Mul]
  rw [evalPoly1_len11 hlen, evalPoly1_len11 hp, evalPoly1_len11 hq]
  have hcoeff : ∀ k : Fin 11, ((poly1Mul p q).getD k.val 0 : ℝ) =
      ∑ i : Fin 11, ∑ j : Fin 11,
        if i.val + j.val = k.val then (p.getD i.val 0 : ℝ) * (q.getD j.val 0 : ℝ) else 0 := by
    intro k
    simp only [poly1Mul, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range k.isLt,
      Option.map_some, Option.getD_some]
    rw [foldl_add_eq_sum, zero_add, sum_range_eq_fin]
    push_cast
    have hsplit : ∑ i : Fin (k.val + 1), (p.getD i.val 0 : ℝ) * (q.getD (k.val - i.val) 0 : ℝ) =
        ∑ i : Fin 11, if i.val ≤ k.val then
          (p.getD i.val 0 : ℝ) * (q.getD (k.val - i.val) 0 : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun i _ => ⟨i.val, by have := i.isLt; omega⟩)
        (fun i _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Nat.lt_succ_iff.mp i.isLt)
        (fun _ _ _ _ h => Fin.ext (by simpa using congr_arg Fin.val h))
        (fun i hi => ⟨⟨i.val, by have hi' : i.val ≤ k.val := (Finset.mem_filter.mp hi).2; omega⟩,
          Finset.mem_univ _, by ext; rfl⟩)
        (fun _ _ => rfl)
    simp only [← List.getD_eq_getElem?_getD]
    rw [hsplit]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hik : i.val ≤ k.val
    · simp only [hik, ↓reduceIte]
      let j0 : Fin 11 := ⟨k.val - i.val, by omega⟩
      rw [Finset.sum_eq_single j0]
      · have : i.val + j0.val = k.val := by simp [j0]; omega
        simp [this, j0]
      · intro j _ hne
        have : i.val + j.val ≠ k.val := fun heq => hne (Fin.ext (by simp [j0]; omega))
        simp [this]
      · intro h; exact absurd (Finset.mem_univ j0) h
    · simp only [hik, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have : i.val + j.val ≠ k.val := by omega
      simp [this]
  simp_rw [hcoeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hlt : i.val + j.val < 11
  · let k0 : Fin 11 := ⟨i.val + j.val, hlt⟩
    rw [Finset.sum_eq_single k0]
    · simp only [k0, ↓reduceIte, pow_add]; ring
    · intro k _ hne
      have : i.val + j.val ≠ k.val := fun heq => hne (Fin.ext heq.symm)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ k0) h
  · have hzero : (p.getD i.val 0 : ℝ) * (q.getD j.val 0 : ℝ) = 0 := by
      have := hdeg i j (by omega)
      exact_mod_cast this
    have hsum0 : (∑ x : Fin 11, (if i.val + j.val = x.val then
        (p.getD i.val 0 : ℝ) * (q.getD j.val 0 : ℝ) else 0) * t ^ x.val) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have : i.val + j.val ≠ k.val := by omega
      simp [this]
    rw [hsum0]
    linear_combination -(t ^ i.val * t ^ j.val) * hzero

private theorem oneMinusT2Pow_eval (k : Fin 5) (t : ℝ) :
    evalPoly1 (oneMinusT2Pow (k.val + 1)) t = (1 - t ^ 2) ^ (k.val + 1) := by
  fin_cases k <;>
  · simp [oneMinusT2Pow, evalPoly1_eq_sum, Fin.sum_univ_succ]
    ring

private theorem quadPoly1Monomial_zero_of_ge {m : ℕ} (M : List (List ℤ)) {k : ℕ} (hk : 2 * m - 1 ≤ k) :
    (quadPoly1Monomial m M).getD k 0 = 0 := by
  by_cases hk11 : k < 11
  · simp only [quadPoly1Monomial, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk11, Option.map_some, Option.getD_some]
    have hfold : ∀ (l : List ℕ), (∀ i ∈ l, ¬(i ≤ k ∧ k - i < m)) →
        l.foldl (fun acc i => if i ≤ k ∧ k - i < m then acc + matGet M i (k - i) else acc) 0 = 0 := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a s ih =>
        have ha : ¬(a ≤ k ∧ k - a < m) := hl a (by simp)
        simp only [List.foldl_cons, ha, ↓reduceIte]
        exact ih fun x hx => hl x (by simp [hx])
    exact hfold (List.range m) fun i hi => by
      simp only [List.mem_range] at hi
      omega
  · have hnone : (List.range 11)[k]? = none := List.getElem?_eq_none (by rw [List.length_range]; omega)
    simp [quadPoly1Monomial, List.getD_eq_getElem?_getD, hnone]

/-- Construct the degree-5 family `F : (k : Fin 5) → Matrix (Fin (5 - k.val)) (Fin (5 - k.val)) ℝ`. -/
noncomputable def toF5 (c : BVCert5) :
    (k : Fin 5) → Matrix (Fin (5 - k.val)) (Fin (5 - k.val)) ℝ
  | ⟨0, _⟩ => toRealMat 5 c.dK c.F1
  | ⟨1, _⟩ => toRealMat 4 c.dK c.F2
  | ⟨2, _⟩ => toRealMat 3 c.dK c.F3
  | ⟨3, _⟩ => toRealMat 2 c.dK c.F4
  | ⟨4, _⟩ => toRealMat 1 c.dK c.F5

set_option maxHeartbeats 800000 in
/-- **Soundness of the exact rational Bachoc–Vallentin SDP certificate verifier**:
if `cert.isValid = true`, then for every `(n, cert.sRat)`-spherical code on `S²`,
`(n : ℝ) ≤ (cert.bound : ℝ)`. -/
theorem sound {c : BVCert5} (hval : c.isValid = true)
    {n : ℕ} {p : Fin n → UnitSphere} (hp : IsSphericalCode p (c.sRat : ℝ)) :
    (n : ℝ) ≤ (c.bound : ℝ) := by
  simp only [isValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hval
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsDen, _hsLo⟩, hdK⟩, hdS⟩, _hdR⟩,
    hA0⟩, hF1⟩, hF2⟩, hF3⟩, hF4⟩, hF5⟩,
    hS2_0⟩, hS2_1⟩,
    hM1⟩, hM2⟩, hM3⟩, hM4⟩, hM5⟩, hM6⟩, hM7⟩, hM8⟩, hM9⟩, hM10⟩,
    hEq2⟩, hEq3⟩ := hval
  have hsDen_pos : (0 : ℝ) < (c.sDen : ℝ) := Nat.cast_pos.mpr hsDen
  have hdK_pos : (0 : ℝ) < (c.dK : ℝ) := Nat.cast_pos.mpr hdK
  have hdS_pos : (0 : ℝ) < (c.dS : ℝ) := Nat.cast_pos.mpr hdS
  -- 1. PSD of kernel matrices A0 and F1..F5
  have hA0_psd : (toRealMat 7 c.dK c.A0).PosSemidef := isCholeskyDDValid_sound hA0
  have hF_psd : ∀ k : Fin 5, (c.toF5 k).PosSemidef := fun k => by
    fin_cases k
    · exact isCholeskyDDValid_sound hF1
    · exact isCholeskyDDValid_sound hF2
    · exact isCholeskyDDValid_sound hF3
    · exact isCholeskyDDValid_sound hF4
    · exact isCholeskyDDValid_sound hF5
  -- 2. Univariate sign condition: ∀ t ∈ [-1, s], bvG2 (toRealMat 7 dK A0) c.toF5 t ≤ 0
  have hG2 : ∀ t : ℝ, -1 ≤ t → t ≤ (c.sRat : ℝ) →
      bvG2 (toRealMat 7 c.dK c.A0) c.toF5 t ≤ 0 := by
    intro t hlo hhi
    -- Show `evalPoly1 c.polyG2 t = dK * bvG2 ... t`
    have hG2_eval : evalPoly1 c.polyG2 t = (c.dK : ℝ) * bvG2 (toRealMat 7 c.dK c.A0) c.toF5 t := by
      have hlen_c : ([(c.dK : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Poly1).length = 11 := rfl
      have hlen_x : ((List.range 11).map fun i => if i < 6 then 2 * matGet c.A0 0 (i + 1) else 0).length = 11 := by simp
      have hlen_q : ∀ m M, (quadPoly1Monomial m M).length = 11 := fun _ _ => by simp [quadPoly1Monomial]
      have hlen_p : ∀ k : Fin 5, (oneMinusT2Pow (k.val + 1)).length = 11 := fun k => by fin_cases k <;> rfl
      have hlen_add : ∀ p q, (poly1Add p q).length = 11 := fun _ _ => by simp [poly1Add]
      have hlen_mul : ∀ p q, (poly1Mul p q).length = 11 := fun _ _ => by simp [poly1Mul]
      unfold polyG2
      rw [evalPoly1_add hlen_c (hlen_add _ _), evalPoly1_add hlen_x (hlen_add _ _),
        evalPoly1_add (hlen_q _ _) (hlen_add _ _), evalPoly1_add (hlen_mul _ _) (hlen_add _ _),
        evalPoly1_add (hlen_mul _ _) (hlen_add _ _), evalPoly1_add (hlen_mul _ _) (hlen_add _ _),
        evalPoly1_add (hlen_mul _ _) (hlen_mul _ _)]
      have hmul_F : ∀ (k : Fin 5) (M : List (List ℤ)),
          evalPoly1 (poly1Mul (quadPoly1Monomial (5 - k.val) M) (oneMinusT2Pow (k.val + 1))) t =
          (∑ a : Fin (5 - k.val), ∑ b : Fin (5 - k.val),
            (matGet M a.val b.val : ℝ) * t ^ (a.val + b.val)) * (1 - t ^ 2) ^ (k.val + 1) := by
        intro k M
        rw [evalPoly1_mul (hlen_q _ _) (hlen_p k), quadPoly1Monomial_eval (by omega),
          oneMinusT2Pow_eval k]
        intro i j hij
        by_cases hi : 2 * (5 - k.val) - 1 ≤ i.val
        · rw [quadPoly1Monomial_zero_of_ge M hi, zero_mul]
        · have hj : 2 * (k.val + 1) < j.val := by omega
          have hq0 : (oneMinusT2Pow (k.val + 1)).getD j.val 0 = 0 := by
            fin_cases k <;> fin_cases j <;> simp_all [oneMinusT2Pow]
          rw [hq0, mul_zero]
      have hf1 := hmul_F ⟨0, by omega⟩ c.F1; dsimp at hf1
      have hf2 := hmul_F ⟨1, by omega⟩ c.F2; dsimp at hf2
      have hf3 := hmul_F ⟨2, by omega⟩ c.F3; dsimp at hf3
      have hf4 := hmul_F ⟨3, by omega⟩ c.F4; dsimp at hf4
      have hf5 := hmul_F ⟨4, by omega⟩ c.F5; dsimp at hf5
      rw [hf1, hf2, hf3, hf4, hf5]
      rw [quadPoly1Monomial_eval (by omega)]
      have hconst : evalPoly1 [(c.dK : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] t = (c.dK : ℝ) := by
        simp [evalPoly1_eq_sum, Fin.sum_univ_succ]
      have hcross : evalPoly1 ((List.range 11).map fun i => if i < 6 then 2 * matGet c.A0 0 (i + 1) else 0) t =
          2 * ∑ a : Fin 6, (matGet c.A0 0 (a.val + 1) : ℝ) * t ^ a.val := by
        rw [evalPoly1_len11 hlen_x]
        simp only [Fin.sum_univ_succ, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range, Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, Option.map_some,
          Option.getD_some, Fin.is_lt, ↓reduceIte]
        push_cast; ring
      have ha0sub : ∀ a b : Fin 6, matGet c.A0Sub a.val b.val = matGet c.A0 (a.val + 1) (b.val + 1) := by
        intro a b
        simp [A0Sub, matGet, List.getD_eq_getElem?_getD]
      have hbvG2 : bvG2 (toRealMat 7 c.dK c.A0) c.toF5 t =
          1 +
          2 * (∑ a : Fin 6, (matGet c.A0 0 (a.val + 1) : ℝ) / (c.dK : ℝ) * t ^ a.val) +
          (∑ a : Fin 6, ∑ b : Fin 6, (matGet c.A0 (a.val + 1) (b.val + 1) : ℝ) / (c.dK : ℝ) * t ^ (a.val + b.val)) +
          ((∑ a : Fin 5, ∑ b : Fin 5, (matGet c.F1 a.val b.val : ℝ) / (c.dK : ℝ) * (t ^ (a.val + b.val) * (1 - t ^ 2) ^ 1)) +
           (∑ a : Fin 4, ∑ b : Fin 4, (matGet c.F2 a.val b.val : ℝ) / (c.dK : ℝ) * (t ^ (a.val + b.val) * (1 - t ^ 2) ^ 2)) +
           (∑ a : Fin 3, ∑ b : Fin 3, (matGet c.F3 a.val b.val : ℝ) / (c.dK : ℝ) * (t ^ (a.val + b.val) * (1 - t ^ 2) ^ 3)) +
           (∑ a : Fin 2, ∑ b : Fin 2, (matGet c.F4 a.val b.val : ℝ) / (c.dK : ℝ) * (t ^ (a.val + b.val) * (1 - t ^ 2) ^ 4)) +
           (∑ a : Fin 1, ∑ b : Fin 1, (matGet c.F5 a.val b.val : ℝ) / (c.dK : ℝ) * (t ^ (a.val + b.val) * (1 - t ^ 2) ^ 5))) := by
        unfold bvG2
        rw [Fin.sum_univ_five (f := fun k : Fin 5 => ∑ a : Fin (5 - k.val), ∑ b : Fin (5 - k.val),
          c.toF5 k a b * (t ^ (a.val + b.val) * (1 - t ^ 2) ^ (k.val + 1)))]
        simp only [toF5, toRealMat, Matrix.of_apply, Fin.val_succ, Fin.val_zero, Fin.val_one,
          Fin.val_two]
        rfl
      rw [hconst, hcross, hbvG2]
      have hdiv : ∀ (x y : ℝ), (c.dK : ℝ) * (x / (c.dK : ℝ) * y) = x * y := fun x y => by
        field_simp [hdK_pos.ne']
      have hpullA : (c.dK : ℝ) * (∑ a : Fin 6, ∑ b : Fin 6, (matGet c.A0 (a.val + 1) (b.val + 1) : ℝ) / (c.dK : ℝ) * t ^ (a.val + b.val)) =
          ∑ a : Fin 6, ∑ b : Fin 6, (matGet c.A0 (a.val + 1) (b.val + 1) : ℝ) * t ^ (a.val + b.val) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => hdiv _ _
      have hpull2 : (c.dK : ℝ) * (2 * ∑ a : Fin 6, (matGet c.A0 0 (a.val + 1) : ℝ) / (c.dK : ℝ) * t ^ a.val) =
          2 * ∑ a : Fin 6, (matGet c.A0 0 (a.val + 1) : ℝ) * t ^ a.val := by
        rw [← mul_assoc, mul_comm (c.dK : ℝ) 2, mul_assoc, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun a _ => hdiv _ _
      have hpullF : ∀ {m : ℕ} (M : List (List ℤ)) (p : ℝ),
          (c.dK : ℝ) * (∑ a : Fin m, ∑ b : Fin m, (matGet M a.val b.val : ℝ) / (c.dK : ℝ) * (t ^ (a.val + b.val) * p)) =
          (∑ a : Fin m, ∑ b : Fin m, (matGet M a.val b.val : ℝ) * t ^ (a.val + b.val)) * p := by
        intro m M p
        rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun b _ => ?_
        rw [hdiv]; ring
      simp_rw [ha0sub, mul_add, mul_one, hpull2, hpullA, hpullF]
      ring
    -- Show `evalPoly1 c.polyRHS2 t ≥ 0`
    have hRHS2_nonneg : 0 ≤ evalPoly1 c.polyRHS2 t := by
      have hlen_s0 : (poly1Scale (c.sDen : ℤ) (quadPoly1Monomial 6 c.S2_0)).length = 11 := by simp [poly1Scale]
      have hlen_g1 : ([c.sNum, c.sNum - (c.sDen : ℤ), -(c.sDen : ℤ), 0, 0, 0, 0, 0, 0, 0, 0] : Poly1).length = 11 := rfl
      have hlen_q5 : (quadPoly1Monomial 5 c.S2_1).length = 11 := by simp [quadPoly1Monomial]
      have hlen_q6 : (quadPoly1Monomial 6 c.S2_0).length = 11 := by simp [quadPoly1Monomial]
      have hlen_m1 : (poly1Mul [c.sNum, c.sNum - (c.sDen : ℤ), -(c.sDen : ℤ), 0, 0, 0, 0, 0, 0, 0, 0]
          (quadPoly1Monomial 5 c.S2_1)).length = 11 := by simp [poly1Mul]
      unfold polyRHS2
      rw [evalPoly1_add hlen_s0 hlen_m1, evalPoly1_scale hlen_q6, quadPoly1Monomial_eval (by omega)]
      rw [evalPoly1_mul hlen_g1 hlen_q5, quadPoly1Monomial_eval (by omega)]
      · have hS0_psd : (toRealMat 6 c.dS c.S2_0).PosSemidef := isCholeskyDDValid_sound hS2_0
        have hS1_psd : (toRealMat 5 c.dS c.S2_1).PosSemidef := isCholeskyDDValid_sound hS2_1
        have hq0 : 0 ≤ ∑ i : Fin 6, ∑ j : Fin 6, (matGet c.S2_0 i.val j.val : ℝ) * t ^ (i.val + j.val) := by
          have h := posSemidef_quad_nonneg hS0_psd (fun i : Fin 6 => t ^ i.val)
          have hmul : (c.dS : ℝ) * ∑ a : Fin 6, ∑ b : Fin 6, t ^ a.val * toRealMat 6 c.dS c.S2_0 a b * t ^ b.val =
              ∑ i : Fin 6, ∑ j : Fin 6, (matGet c.S2_0 i.val j.val : ℝ) * t ^ (i.val + j.val) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
            simp only [toRealMat, Matrix.of_apply, pow_add]; field_simp [hdS_pos.ne']
          have := mul_nonneg hdS_pos.le h; linarith
        have hq1 : 0 ≤ ∑ i : Fin 5, ∑ j : Fin 5, (matGet c.S2_1 i.val j.val : ℝ) * t ^ (i.val + j.val) := by
          have h := posSemidef_quad_nonneg hS1_psd (fun i : Fin 5 => t ^ i.val)
          have hmul : (c.dS : ℝ) * ∑ a : Fin 5, ∑ b : Fin 5, t ^ a.val * toRealMat 5 c.dS c.S2_1 a b * t ^ b.val =
              ∑ i : Fin 5, ∑ j : Fin 5, (matGet c.S2_1 i.val j.val : ℝ) * t ^ (i.val + j.val) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
            simp only [toRealMat, Matrix.of_apply, pow_add]; field_simp [hdS_pos.ne']
          have := mul_nonneg hdS_pos.le h; linarith
        have hg1_nonneg : 0 ≤ evalPoly1 [c.sNum, c.sNum - (c.sDen : ℤ), -(c.sDen : ℤ),
            0, 0, 0, 0, 0, 0, 0, 0] t := by
          have hsRat_eq : (c.sRat : ℝ) = (c.sNum : ℝ) / (c.sDen : ℝ) := by
            simp [sRat]
          have hfac : evalPoly1 [c.sNum, c.sNum - (c.sDen : ℤ), -(c.sDen : ℤ),
              0, 0, 0, 0, 0, 0, 0, 0] t = (c.sDen : ℝ) * (((c.sRat : ℝ) - t) * (t + 1)) := by
            rw [hsRat_eq]
            simp only [evalPoly1_eq_sum, Fin.sum_univ_succ, List.length_cons, List.length_nil,
              List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
              Option.getD_some, Fin.val_zero, Fin.val_succ]
            push_cast; field_simp [hsDen_pos.ne']; ring
          rw [hfac]
          exact mul_nonneg hsDen_pos.le (mul_nonneg (by linarith) (by linarith))
        exact add_nonneg (mul_nonneg (by exact_mod_cast hsDen_pos.le) hq0)
          (mul_nonneg hg1_nonneg hq1)
      · intro i j hij
        by_cases hi : i.val ≤ 2
        · rw [quadPoly1Monomial_zero_of_ge c.S2_1 (by omega), mul_zero]
        · have hp0 : ([c.sNum, c.sNum - (c.sDen : ℤ), -(c.sDen : ℤ),
              0, 0, 0, 0, 0, 0, 0, 0] : Poly1).getD i.val 0 = 0 := by
            fin_cases i <;> simp_all
          rw [hp0, zero_mul]
    -- Combine `hEq2`
    have hlenG2 : c.polyG2.length = 11 := by simp [polyG2, poly1Add]
    have hlenR2 : c.polyRHS2.length = 11 := by simp [polyRHS2, poly1Add]
    have heval_eq := congr_arg (fun q => evalPoly1 q t) hEq2
    rw [evalPoly1_scale hlenG2, evalPoly1_scale hlenR2, hG2_eval] at heval_eq
    push_cast at heval_eq
    have hprod_pos : (0 : ℝ) < (c.sDen : ℝ) * (c.dS : ℝ) * (c.dK : ℝ) := by positivity
    have hnonpos : -((c.sDen : ℝ) * (c.dS : ℝ) * (c.dK : ℝ)) *
        bvG2 (toRealMat 7 c.dK c.A0) c.toF5 t ≥ 0 := by
      have : 0 ≤ (c.dK : ℝ) * evalPoly1 c.polyRHS2 t := mul_nonneg hdK_pos.le hRHS2_nonneg
      linarith
    nlinarith
  -- 3. Trivariate sign condition: ∀ (u, v, t) ∈ Δ(s), sym3 (bvG3 ...) u v t ≤ 0
  have hG3 : ∀ u v t : ℝ, InThreePointDomain (c.sRat : ℝ) u v t →
      sym3 (bvG3 (toRealMat 7 c.dK c.A0) c.toF5) u v t ≤ 0 := by
    intro u v t hdom
    have hG3_eval : sym3 (evalPoly3 c.polyG3) u v t =
        (c.dK : ℝ) * sym3 (bvG3 (toRealMat 7 c.dK c.A0) c.toF5) u v t := by
      have hbuildUV : ∀ (m : ℕ) (M : List (List ℤ)) (u' v' t' : ℝ),
          let monU : List Poly3 := (List.range m).map fun a => [(a, 0, 0, 1)]
          let monV : List Poly3 := (List.range m).map fun b => [(0, b, 0, 1)]
          evalPoly3 ((List.range m).foldl (fun acc i =>
            let bi := monU.getD i []
            let qi := (List.range m).foldl (fun qacc j =>
              normalizePoly3 (qacc ++ poly3Scale (matGet M i j) (monV.getD j []))) []
            normalizePoly3 (acc ++ poly3Mul bi qi)) []) u' v' t' =
          ∑ a : Fin m, ∑ b : Fin m, (matGet M a.val b.val : ℝ) * (u' ^ a.val * v' ^ b.val) := by
        intro m M u' v' t' monU monV
        have hmonU : ∀ i : Fin m, evalPoly3 (monU.getD i.val []) u' v' t' = u' ^ i.val := fun i => by
          simp [monU, List.getD_eq_getElem?_getD, evalPoly3_eq_sum]
        have hmonV : ∀ j : Fin m, evalPoly3 (monV.getD j.val []) u' v' t' = v' ^ j.val := fun j => by
          simp [monV, List.getD_eq_getElem?_getD, evalPoly3_eq_sum]
        have hinner : ∀ i : ℕ,
            evalPoly3 ((List.range m).foldl (fun qacc j =>
              normalizePoly3 (qacc ++ poly3Scale (matGet M i j) (monV.getD j []))) []) u' v' t' =
            ∑ j : Fin m, (matGet M i j.val : ℝ) * v' ^ j.val := by
          intro i
          have hf : ∀ (l : List ℕ) (qacc : Poly3),
              evalPoly3 (l.foldl (fun qacc j =>
                normalizePoly3 (qacc ++ poly3Scale (matGet M i j) (monV.getD j []))) qacc) u' v' t' =
              evalPoly3 qacc u' v' t' +
              (l.map fun j => (matGet M i j : ℝ) * evalPoly3 (monV.getD j []) u' v' t').sum := by
            intro l; induction l with
            | nil => intro qacc; simp
            | cons j js ih =>
              intro qacc
              simp only [List.foldl_cons, ih, evalPoly3_normalize, evalPoly3_append, evalPoly3_scale,
                List.map_cons, List.sum_cons]
              ring
          rw [hf, evalPoly3_nil, zero_add, ← list_map_finRange_eq_range, ← Fin.sum_univ_def]
          exact Finset.sum_congr rfl fun j _ => by rw [hmonV j]
        have houter : ∀ (l : List ℕ) (acc : Poly3),
            evalPoly3 (l.foldl (fun acc i =>
              let bi := monU.getD i []
              let qi := (List.range m).foldl (fun qacc j =>
                normalizePoly3 (qacc ++ poly3Scale (matGet M i j) (monV.getD j []))) []
              normalizePoly3 (acc ++ poly3Mul bi qi)) acc) u' v' t' =
            evalPoly3 acc u' v' t' +
            (l.map fun i => evalPoly3 (monU.getD i []) u' v' t' *
              ∑ j : Fin m, (matGet M i j.val : ℝ) * v' ^ j.val).sum := by
          intro l; induction l with
          | nil => intro acc; simp
          | cons i is ih =>
            intro acc
            simp only [List.foldl_cons, ih, evalPoly3_normalize, evalPoly3_append, evalPoly3_mul,
              hinner, List.map_cons, List.sum_cons]
            ring
        rw [houter, evalPoly3_nil, zero_add, ← list_map_finRange_eq_range, ← Fin.sum_univ_def]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmonU i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      unfold polyG3
      rw [sym3_evalPoly3_sym3Canon]
      have hfn : evalPoly3 (
          ((List.range 6).foldl (fun acc i =>
            let bi := ((List.range 6).map fun a => [(a, 0, 0, 1)]).getD i []
            let qi := (List.range 6).foldl (fun qacc j =>
              normalizePoly3 (qacc ++ poly3Scale (matGet c.A0Sub i j)
                (((List.range 6).map fun b => [(0, b, 0, 1)]).getD j []))) []
            normalizePoly3 (acc ++ poly3Mul bi qi)) []) ++
          normalizePoly3 (poly3Mul ((List.range 5).foldl (fun acc i =>
            let bi := ((List.range 5).map fun a => [(a, 0, 0, 1)]).getD i []
            let qi := (List.range 5).foldl (fun qacc j =>
              normalizePoly3 (qacc ++ poly3Scale (matGet c.F1 i j)
                (((List.range 5).map fun b => [(0, b, 0, 1)]).getD j []))) []
            normalizePoly3 (acc ++ poly3Mul bi qi)) []) (bvQPoly3 1)) ++
          normalizePoly3 (poly3Mul ((List.range 4).foldl (fun acc i =>
            let bi := ((List.range 4).map fun a => [(a, 0, 0, 1)]).getD i []
            let qi := (List.range 4).foldl (fun qacc j =>
              normalizePoly3 (qacc ++ poly3Scale (matGet c.F2 i j)
                (((List.range 4).map fun b => [(0, b, 0, 1)]).getD j []))) []
            normalizePoly3 (acc ++ poly3Mul bi qi)) []) (bvQPoly3 2)) ++
          normalizePoly3 (poly3Mul ((List.range 3).foldl (fun acc i =>
            let bi := ((List.range 3).map fun a => [(a, 0, 0, 1)]).getD i []
            let qi := (List.range 3).foldl (fun qacc j =>
              normalizePoly3 (qacc ++ poly3Scale (matGet c.F3 i j)
                (((List.range 3).map fun b => [(0, b, 0, 1)]).getD j []))) []
            normalizePoly3 (acc ++ poly3Mul bi qi)) []) (bvQPoly3 3)) ++
          normalizePoly3 (poly3Mul ((List.range 2).foldl (fun acc i =>
            let bi := ((List.range 2).map fun a => [(a, 0, 0, 1)]).getD i []
            let qi := (List.range 2).foldl (fun qacc j =>
              normalizePoly3 (qacc ++ poly3Scale (matGet c.F4 i j)
                (((List.range 2).map fun b => [(0, b, 0, 1)]).getD j []))) []
            normalizePoly3 (acc ++ poly3Mul bi qi)) []) (bvQPoly3 4)) ++
          normalizePoly3 (poly3Mul ((List.range 1).foldl (fun acc i =>
            let bi := ((List.range 1).map fun a => [(a, 0, 0, 1)]).getD i []
            let qi := (List.range 1).foldl (fun qacc j =>
              normalizePoly3 (qacc ++ poly3Scale (matGet c.F5 i j)
                (((List.range 1).map fun b => [(0, b, 0, 1)]).getD j []))) []
            normalizePoly3 (acc ++ poly3Mul bi qi)) []) (bvQPoly3 5))) =
          fun u' v' t' => (c.dK : ℝ) * bvG3 (toRealMat 7 c.dK c.A0) c.toF5 u' v' t' := by
        ext u' v' t'
        simp only [evalPoly3_append, evalPoly3_normalize, evalPoly3_mul, hbuildUV,
          evalPoly3_bvQPoly3]
        have ha0sub : ∀ a b : Fin 6, matGet c.A0Sub a.val b.val = matGet c.A0 (a.val + 1) (b.val + 1) := by
          intro a b
          simp [A0Sub, matGet, List.getD_eq_getElem?_getD]
        have hbvG3 : bvG3 (toRealMat 7 c.dK c.A0) c.toF5 u' v' t' =
            (∑ a : Fin 6, ∑ b : Fin 6, (matGet c.A0 (a.val + 1) (b.val + 1) : ℝ) / (c.dK : ℝ) * (u' ^ a.val * v' ^ b.val)) +
            ((∑ a : Fin 5, ∑ b : Fin 5, (matGet c.F1 a.val b.val : ℝ) / (c.dK : ℝ) * (u' ^ a.val * v' ^ b.val * bvQ 1 u' v' t')) +
             (∑ a : Fin 4, ∑ b : Fin 4, (matGet c.F2 a.val b.val : ℝ) / (c.dK : ℝ) * (u' ^ a.val * v' ^ b.val * bvQ 2 u' v' t')) +
             (∑ a : Fin 3, ∑ b : Fin 3, (matGet c.F3 a.val b.val : ℝ) / (c.dK : ℝ) * (u' ^ a.val * v' ^ b.val * bvQ 3 u' v' t')) +
             (∑ a : Fin 2, ∑ b : Fin 2, (matGet c.F4 a.val b.val : ℝ) / (c.dK : ℝ) * (u' ^ a.val * v' ^ b.val * bvQ 4 u' v' t')) +
             (∑ a : Fin 1, ∑ b : Fin 1, (matGet c.F5 a.val b.val : ℝ) / (c.dK : ℝ) * (u' ^ a.val * v' ^ b.val * bvQ 5 u' v' t'))) := by
          unfold bvG3
          rw [Fin.sum_univ_five (f := fun k : Fin 5 => ∑ a : Fin (5 - k.val), ∑ b : Fin (5 - k.val),
            c.toF5 k a b * (u' ^ a.val * v' ^ b.val * bvQ (k.val + 1) u' v' t'))]
          simp only [toF5, toRealMat, Matrix.of_apply, Fin.val_succ, Fin.val_zero, Fin.val_one,
            Fin.val_two]
          rfl
        rw [hbvG3]
        have hdiv : ∀ (x y : ℝ), (c.dK : ℝ) * (x / (c.dK : ℝ) * y) = x * y := fun x y => by
          field_simp [hdK_pos.ne']
        have hpullA : (c.dK : ℝ) * (∑ a : Fin 6, ∑ b : Fin 6, (matGet c.A0 (a.val + 1) (b.val + 1) : ℝ) / (c.dK : ℝ) * (u' ^ a.val * v' ^ b.val)) =
            ∑ a : Fin 6, ∑ b : Fin 6, (matGet c.A0 (a.val + 1) (b.val + 1) : ℝ) * (u' ^ a.val * v' ^ b.val) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => hdiv _ _
        have hpullF : ∀ {m : ℕ} (M : List (List ℤ)) (q : ℝ),
            (c.dK : ℝ) * (∑ a : Fin m, ∑ b : Fin m, (matGet M a.val b.val : ℝ) / (c.dK : ℝ) * (u' ^ a.val * v' ^ b.val * q)) =
            (∑ a : Fin m, ∑ b : Fin m, (matGet M a.val b.val : ℝ) * (u' ^ a.val * v' ^ b.val)) * q := by
          intro m M q
          rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun b _ => ?_
          rw [hdiv]; ring
        simp_rw [ha0sub, mul_add, hpullA, hpullF]
        ring
      rw [hfn, sym3_linear_mul]
    -- Show `sym3 (evalPoly3 c.polyRHS3) u v t ≥ 0` on `InThreePointDomain (c.sRat : ℝ)`
    have hRHS3_pointwise : ∀ u' v' t' : ℝ, InThreePointDomain (c.sRat : ℝ) u' v' t' →
        0 ≤ evalPoly3 (mergePoly3
          (poly3Scale ((c.sDen : ℤ) * (c.sDen : ℤ)) (mergePoly3
            (quadPoly3 16 c.M_one_triv basisOneTriv)
            (mergePoly3 (quadPoly3 18 c.M_one_std basisOneStd)
              (quadPoly3 4 c.M_one_sign basisOneSign))))
          (mergePoly3
            (poly3Scale ((c.sDen : ℤ) * (c.sDen : ℤ)) (mulPoly3Sorted multDelta (mergePoly3
              (quadPoly3 7 c.M_delta_triv basisDeltaTriv)
              (mergePoly3 (quadPoly3 6 c.M_delta_std basisDeltaStd)
                (quadPoly3 1 c.M_delta_sign basisDeltaSign)))))
            (mergePoly3
              (poly3Scale (c.sDen : ℤ) (mulPoly3Sorted (multG1 c.sNum (c.sDen : ℤ)) (mergePoly3
                (quadPoly3 22 c.M_g1_even basisG1Even)
                (quadPoly3 13 c.M_g1_odd basisG1Odd))))
              (mulPoly3Sorted (multG2 c.sNum (c.sDen : ℤ)) (mergePoly3
                (quadPoly3 22 c.M_g2_even basisG1Even)
                (quadPoly3 13 c.M_g2_odd basisG1Odd)))))) u' v' t' := by
      intro u' v' t' hdom'
      simp only [evalPoly3_mergePoly3, evalPoly3_scale, evalPoly3_mulPoly3Sorted, evalPoly3_multDelta]
      have h1 := evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM1) basisOneTriv u' v' t'
      have h2 := evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM2) basisOneStd u' v' t'
      have h3 := evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM3) basisOneSign u' v' t'
      have h4 := evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM4) basisDeltaTriv u' v' t'
      have h5 := evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM5) basisDeltaStd u' v' t'
      have h6 := evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM6) basisDeltaSign u' v' t'
      have h7 := evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM7) basisG1Even u' v' t'
      have h8 := evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM8) basisG1Odd u' v' t'
      have h9 := evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM9) basisG1Even u' v' t'
      have h10 := evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM10) basisG1Odd u' v' t'
      have hD_nn : 0 ≤ gramDet3 u' v' t' := hdom'.2.2.2.2.2.2
      have hg1_nn : 0 ≤ evalPoly3 (multG1 c.sNum (c.sDen : ℤ)) u' v' t' := by
        rcases evalPoly3_multG1 c.sNum (c.sDen : ℤ) u' v' t' with h | h
        · rw [h]
          push_cast
          have hsRat_eq : (c.sRat : ℝ) = (c.sNum : ℝ) / (c.sDen : ℝ) := by simp [sRat]
          have := hdom'.g1_nonneg
          rw [hsRat_eq] at this
          have hmul_eq : (c.sDen : ℝ) * ((c.sNum : ℝ) / (c.sDen : ℝ) - u') * (u' + 1) =
              (c.sDen : ℝ) * (((c.sNum : ℝ) / (c.sDen : ℝ) - u') * (u' + 1)) := by ring
          rw [hmul_eq]
          exact mul_nonneg hsDen_pos.le this
        · omega
      have hg2_nn : 0 ≤ evalPoly3 (multG2 c.sNum (c.sDen : ℤ)) u' v' t' := by
        rcases evalPoly3_multG2 c.sNum (c.sDen : ℤ) u' v' t' with h | h
        · rw [h]
          push_cast
          have hsRat_eq : (c.sRat : ℝ) = (c.sNum : ℝ) / (c.sDen : ℝ) := by simp [sRat]
          have := hdom'.g2_nonneg
          rw [hsRat_eq] at this
          exact mul_nonneg (sq_nonneg _) this
        · omega
      have hsDen_nn : (0 : ℝ) ≤ ((c.sDen : ℤ) : ℝ) := by exact_mod_cast hsDen_pos.le
      have hsDen2_nn : (0 : ℝ) ≤ (((c.sDen : ℤ) * (c.sDen : ℤ) : ℤ) : ℝ) := by
        push_cast; positivity
      exact add_nonneg
        (mul_nonneg hsDen2_nn (add_nonneg h1 (add_nonneg h2 h3)))
        (add_nonneg
          (mul_nonneg hsDen2_nn (mul_nonneg hD_nn (add_nonneg h4 (add_nonneg h5 h6))))
          (add_nonneg
            (mul_nonneg hsDen_nn (mul_nonneg hg1_nn (add_nonneg h7 h8)))
            (mul_nonneg hg2_nn (add_nonneg h9 h10))))
    have hRHS3_nonneg : 0 ≤ sym3 (evalPoly3 c.polyRHS3) u v t := by
      unfold polyRHS3
      rw [sym3_evalPoly3_sym3Canon]
      unfold sym3
      have h1 := hRHS3_pointwise u v t hdom
      have h2 := hRHS3_pointwise u t v hdom.swap_vt
      have h3 := hRHS3_pointwise v u t hdom.swap_uv
      have h4 := hRHS3_pointwise v t u hdom.cyc
      have h5 := hRHS3_pointwise t u v hdom.cyc.cyc
      have h6 := hRHS3_pointwise t v u hdom.cyc.swap_uv
      linarith
    -- Combine `hEq3`
    have heval3 := congr_arg (fun q => sym3 (evalPoly3 q) u v t) hEq3
    rw [sym3_evalPoly3_sym3Canon, sym3_evalPoly3_sym3Canon] at heval3
    have hscale_sym : ∀ (k : ℤ) (q : Poly3),
        sym3 (evalPoly3 (poly3Scale k q)) u v t = (k : ℝ) * sym3 (evalPoly3 q) u v t := by
      intro k q
      have : evalPoly3 (poly3Scale k q) = fun u' v' t' => (k : ℝ) * evalPoly3 q u' v' t' := by
        ext u' v' t'; exact evalPoly3_scale k q u' v' t'
      rw [this, sym3_linear_mul]
    rw [hscale_sym, hscale_sym, hG3_eval] at heval3
    push_cast at heval3
    have hprod_pos : (0 : ℝ) < (c.sDen : ℝ) * (c.sDen : ℝ) * (c.dS : ℝ) * (c.dK : ℝ) := by positivity
    have hnonneg_rhs : 0 ≤ (c.dK : ℝ) * sym3 (evalPoly3 c.polyRHS3) u v t :=
      mul_nonneg hdK_pos.le hRHS3_nonneg
    nlinarith
  -- 4. Apply `bachocVallentin_bound`!
  have hbound := bachocVallentin_bound hp hA0_psd hF_psd hG2 hG3
  have heq_bound : 1 + toRealMat 7 c.dK c.A0 0 0 = (c.bound : ℝ) := by
    simp [toRealMat, bound]
  rwa [heq_bound] at hbound

end BVCert5

end Geodesy.Spherical
