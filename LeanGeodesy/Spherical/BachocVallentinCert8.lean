import LeanGeodesy.Spherical.BachocVallentinCert
import LeanGeodesy.Spherical.Legendre16

/-!
# Exact rational degree-8 Chebyshev-basis Bachoc–Vallentin + Legendre (`P₁..P₁₆`) SDP verifier

This module provides a minimal, kernel-checkable verifier (`BVCert8`) for degree
`d₃ = 8, d₂ = 16` Bachoc–Vallentin three-point SDP certificates on `S²`, using:
- Chebyshev basis `T₀..T₈` for the 9 three-point kernel matrices `F₀..F₈` and
  univariate SOS matrices `S₀ (9×9), S₁ (8×8)`,
- two-point Legendre terms `P₁..P₁₆` scaled by `32768 = 2¹⁵` (`legendreP16Int`),
- the mathematically reduced 7-block `S₃`-symmetric trivariate SOS decomposition
  (`one_triv`, `one_std`, `one_sign`, `delta_triv`, `delta_std`, `delta_sign`, `g1_even`;
  no `g2` multiplier and no `g1_odd` block), with per-block local denominators `dM₀..dM₆`.

Soundness (`BVCert8.sound`) unconditionally certifies `(n : ℝ) ≤ cert.bound` for
every `(n, cert.s)`-spherical code on `S²`.
-/

namespace Geodesy.Spherical

open scoped BigOperators Matrix

/-! ## Univariate degree-16 integer polynomials (scaled by `32768` for `P₁..P₁₆`) -/

/-- Evaluate a univariate integer polynomial `List ℤ` (ascending powers of `t`) at `t : ℝ`. -/
def evalPoly17 (p : List ℤ) (t : ℝ) : ℝ :=
  (List.range p.length).foldl (fun acc d => acc + (p.getD d 0 : ℝ) * t ^ d) 0

private theorem range_17_eq :
    List.range 17 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := by
  decide

private theorem evalPoly17_eq_sum (p : List ℤ) (t : ℝ) :
    evalPoly17 p t = ∑ d : Fin p.length, (p.getD d.val 0 : ℝ) * t ^ d.val := by
  unfold evalPoly17
  have hfold : ∀ (l : List ℕ) (init : ℝ),
      l.foldl (fun acc d => acc + (p.getD d 0 : ℝ) * t ^ d) init =
      init + (l.map fun d => (p.getD d 0 : ℝ) * t ^ d).sum := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons a s ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      ring
  rw [hfold, zero_add, Fin.sum_univ_def]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.getElem_finRange, Fin.val_cast]

private theorem evalPoly17_len17 {p : List ℤ} (h : p.length = 17) (t : ℝ) :
    evalPoly17 p t = ∑ d : Fin 17, (p.getD d.val 0 : ℝ) * t ^ d.val := by
  rw [evalPoly17_eq_sum]
  refine Finset.sum_bij (fun d _ => ⟨d.val, by omega⟩) (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ hab => Fin.ext (by simpa using congrArg Fin.val hab))
    (fun b _ => ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun _ _ => rfl)

def poly17Zero : List ℤ := List.replicate 17 0

def poly17Add (p q : List ℤ) : List ℤ :=
  (List.range 17).map fun d => p.getD d 0 + q.getD d 0

def poly17Scale (c : ℤ) (p : List ℤ) : List ℤ :=
  (List.range 17).map fun d => c * p.getD d 0

def poly17Mul (p q : List ℤ) : List ℤ :=
  (List.range 17).map fun d =>
    (List.range (d + 1)).foldl (fun acc i => acc + p.getD i 0 * q.getD (d - i) 0) 0

private theorem poly17Zero_len : poly17Zero.length = 17 := by rfl
private theorem poly17Add_len (p q : List ℤ) : (poly17Add p q).length = 17 := by simp [poly17Add]
private theorem poly17Scale_len (c : ℤ) (p : List ℤ) : (poly17Scale c p).length = 17 := by simp [poly17Scale]
private theorem poly17Mul_len (p q : List ℤ) : (poly17Mul p q).length = 17 := by simp [poly17Mul]

private theorem evalPoly17_zero (t : ℝ) : evalPoly17 poly17Zero t = 0 := by
  rw [evalPoly17_len17 poly17Zero_len]
  refine Finset.sum_eq_zero fun d _ => ?_
  have : poly17Zero.getD d.val 0 = 0 := by
    have hlt : d.val < 17 := d.isLt
    interval_cases d.val <;> rfl
  rw [this]; simp

private theorem evalPoly17_add {p q : List ℤ} (hp : p.length = 17) (hq : q.length = 17) (t : ℝ) :
    evalPoly17 (poly17Add p q) t = evalPoly17 p t + evalPoly17 q t := by
  rw [evalPoly17_len17 (poly17Add_len p q), evalPoly17_len17 hp, evalPoly17_len17 hq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [poly17Add, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range d.isLt, Option.map_some, Option.getD_some, Int.cast_add]
  ring

private theorem evalPoly17_scale {p : List ℤ} (hp : p.length = 17) (c : ℤ) (t : ℝ) :
    evalPoly17 (poly17Scale c p) t = (c : ℝ) * evalPoly17 p t := by
  rw [evalPoly17_len17 (poly17Scale_len c p), evalPoly17_len17 hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [poly17Scale, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range d.isLt, Option.map_some, Option.getD_some, Int.cast_mul]
  ring

private theorem foldl_add_int17 (l : List ℕ) (f : ℕ → ℤ) (init : ℤ) :
    l.foldl (fun acc x => acc + f x) init = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a s ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; ring

private theorem sum_range_int17 {m : ℕ} (f : ℕ → ℤ) :
    ((List.range m).map f).sum = ∑ k : Fin m, f k.val := by
  rw [Fin.sum_univ_def]
  congr 1
  apply List.ext_getElem <;> simp

private theorem evalPoly17_mul_deg {p q : List ℤ} (dp dq : ℕ)
    (hdp : ∀ d, dp < d → p.getD d 0 = 0)
    (hdq : ∀ d, dq < d → q.getD d 0 = 0)
    (hdeg : dp + dq ≤ 16) (hp : p.length = 17) (hq : q.length = 17) (t : ℝ) :
    evalPoly17 (poly17Mul p q) t = evalPoly17 p t * evalPoly17 q t := by
  rw [evalPoly17_len17 (poly17Mul_len p q), evalPoly17_len17 hp, evalPoly17_len17 hq]
  have hget : ∀ d : Fin 17, ((poly17Mul p q).getD d.val 0 : ℝ) =
      ∑ i : Fin 17, ∑ j : Fin 17,
        if i.val + j.val = d.val then (p.getD i.val 0 : ℝ) * (q.getD j.val 0 : ℝ) else 0 := by
    intro d
    simp only [poly17Mul, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range d.isLt, Option.map_some, Option.getD_some]
    rw [foldl_add_int17, zero_add, sum_range_int17]
    push_cast
    have hsplit : ∑ i : Fin (d.val + 1), (p.getD i.val 0 : ℝ) * (q.getD (d.val - i.val) 0 : ℝ) =
        ∑ i : Fin 17, if i.val ≤ d.val then (p.getD i.val 0 : ℝ) * (q.getD (d.val - i.val) 0 : ℝ) else 0 := by
      have h1 : ∑ i : Fin 17, (if i.val ≤ d.val then (p.getD i.val 0 : ℝ) * (q.getD (d.val - i.val) 0 : ℝ) else 0) =
          ∑ i ∈ Finset.univ.filter (fun i : Fin 17 => i.val ≤ d.val),
            (p.getD i.val 0 : ℝ) * (q.getD (d.val - i.val) 0 : ℝ) := by
        rw [Finset.sum_filter]
      rw [h1]
      refine Finset.sum_bij (fun (i : Fin (d.val + 1)) _ => (⟨i.val, Nat.lt_of_lt_of_le i.isLt d.isLt⟩ : Fin 17))
        (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_lt_succ i.isLt⟩)
        (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun b hb => ⟨⟨b.val, Nat.lt_succ_of_le (Finset.mem_filter.mp hb).2⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        (fun _ _ => rfl)
    simp_rw [← List.getD_eq_getElem?_getD]
    rw [hsplit]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.val ≤ d.val
    · simp only [hi, ↓reduceIte]
      let j0 : Fin 17 := ⟨d.val - i.val, by omega⟩
      rw [Finset.sum_eq_single j0]
      · have hj0 : i.val + j0.val = d.val := by simp [j0]; omega
        simp [hj0, j0]
      · intro j _ hne
        have : i.val + j.val ≠ d.val := fun heq => hne (by ext; simp [j0]; omega)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ j0) h
    · simp only [hi, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have : i.val + j.val ≠ d.val := by omega
      simp [this]
  simp_rw [hget, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i.val + j.val < 17
  · let d0 : Fin 17 := ⟨i.val + j.val, hij⟩
    rw [Finset.sum_eq_single d0]
    · simp [d0, pow_add]; ring
    · intro d _ hne
      have : i.val + j.val ≠ d.val := fun heq => hne (Fin.ext heq.symm)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ d0) h
  · have hzero : (p.getD i.val 0 : ℝ) * (q.getD j.val 0 : ℝ) = 0 := by
      by_cases hi : dp < i.val
      · rw [hdp i.val hi]; simp
      · have hj : dq < j.val := by omega
        rw [hdq j.val hj]; simp
    have hsum0 : ∑ d : Fin 17, (if i.val + j.val = d.val then (p.getD i.val 0 : ℝ) * (q.getD j.val 0 : ℝ) else 0) * t ^ d.val = 0 := by
      refine Finset.sum_eq_zero fun d _ => ?_
      have : i.val + j.val ≠ d.val := by omega
      simp [this]
    rw [hsum0]
    linear_combination -(t ^ i.val * t ^ j.val) * hzero

private theorem list_getD_of_le_len {α : Type*} (l : List α) (d : ℕ) (a : α) (h : l.length ≤ d) :
    l.getD d a = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

private theorem poly17Add_getD_zero {p q : List ℤ} {D d : ℕ}
    (hp : ∀ k, D < k → p.getD k 0 = 0) (hq : ∀ k, D < k → q.getD k 0 = 0)
    (hd : D < d) : (poly17Add p q).getD d 0 = 0 := by
  by_cases h17 : d < 17
  · simp only [poly17Add, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range h17, Option.map_some, Option.getD_some]
    rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, hp d hd, hq d hd]; rfl
  · exact list_getD_of_le_len _ _ _ (by rw [poly17Add_len]; omega)

private theorem poly17Scale_getD_zero {p : List ℤ} {D d : ℕ} (c : ℤ)
    (hp : ∀ k, D < k → p.getD k 0 = 0) (hd : D < d) : (poly17Scale c p).getD d 0 = 0 := by
  by_cases h17 : d < 17
  · simp only [poly17Scale, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range h17, Option.map_some, Option.getD_some]
    rw [← List.getD_eq_getElem?_getD, hp d hd]; simp
  · exact list_getD_of_le_len _ _ _ (by rw [poly17Scale_len]; omega)

private theorem poly17Mul_getD_zero {p q : List ℤ} {dp dq d : ℕ}
    (hp : ∀ k, dp < k → p.getD k 0 = 0) (hq : ∀ k, dq < k → q.getD k 0 = 0)
    (hd : dp + dq < d) : (poly17Mul p q).getD d 0 = 0 := by
  by_cases h17 : d < 17
  · simp only [poly17Mul, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range h17, Option.map_some, Option.getD_some]
    rw [foldl_add_int17, zero_add, sum_range_int17]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [← List.getD_eq_getElem?_getD]
    by_cases hi : dp < i.val
    · rw [hp i.val hi]; simp
    · have hj : dq < d - i.val := by omega
      rw [hq (d - i.val) hj]; simp
  · exact list_getD_of_le_len _ _ _ (by rw [poly17Mul_len]; omega)

/-- Chebyshev polynomials `T₀..T₈` as length-17 `List ℤ`. -/
def chebT17 : ℕ → List ℤ
  | 0 => [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => [-1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 3 => [0, -3, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 4 => [1, 0, -8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 5 => [0, 5, 0, -20, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 6 => [-1, 0, 18, 0, -48, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 7 => [0, -7, 0, 56, 0, -112, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 8 => [1, 0, -32, 0, 160, 0, -256, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0]
  | _ => poly17Zero

private theorem chebT17_len (k : ℕ) : (chebT17 k).length = 17 := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

private theorem chebT17_getD_zero {k d : ℕ} (hk : k ≤ 8) (hd : k < d) :
    (chebT17 k).getD d 0 = 0 := by
  by_cases h17 : d < 17
  · interval_cases k <;> interval_cases d <;> rfl
  · exact list_getD_of_le_len _ _ _ (by rw [chebT17_len]; omega)

private theorem evalPoly17_chebT17 {k : ℕ} (hk : k ≤ 8) (t : ℝ) :
    evalPoly17 (chebT17 k) t = chebT k t := by
  interval_cases k <;>
    simp [chebT17, evalPoly17, range_17_eq, chebT] <;> ring

/-- Quadratic form `∑ i < m, ∑ j < m, M[i][j] * T_i(t) * T_j(t)` as a length-17 `List ℤ` (for `m ≤ 9`). -/
def quadCheb17 (m : ℕ) (M : List (List ℤ)) : List ℤ :=
  (List.range m).foldl (fun acc i =>
    let qi := (List.range m).foldl (fun qacc j =>
      poly17Add qacc (poly17Scale (matGet M i j) (chebT17 j))) poly17Zero
    poly17Add acc (poly17Mul (chebT17 i) qi)) poly17Zero

private theorem quadCheb17_len (m : ℕ) (M : List (List ℤ)) : (quadCheb17 m M).length = 17 := by
  unfold quadCheb17
  have h : ∀ (l : List ℕ) (acc : List ℤ), acc.length = 17 →
      (l.foldl (fun acc i =>
        let qi := (List.range m).foldl (fun qacc j =>
          poly17Add qacc (poly17Scale (matGet M i j) (chebT17 j))) poly17Zero
        poly17Add acc (poly17Mul (chebT17 i) qi)) acc).length = 17 := by
    intro l; induction l with
    | nil => intro acc hacc; exact hacc
    | cons a s ih => intro acc _; exact ih _ (poly17Add_len _ _)
  exact h _ _ poly17Zero_len

private theorem quadCheb17_inner_props {m : ℕ} (hm : m ≤ 9) (M : List (List ℤ)) (i : ℕ) :
    let qi := (List.range m).foldl (fun qacc j =>
      poly17Add qacc (poly17Scale (matGet M i j) (chebT17 j))) poly17Zero
    qi.length = 17 ∧ (∀ d, m - 1 < d → qi.getD d 0 = 0) ∧
    (∀ t : ℝ, evalPoly17 qi t = ∑ j : Fin m, (matGet M i j.val : ℝ) * chebT j.val t) := by
  have hgen : ∀ (l : List ℕ), (∀ j ∈ l, j < m) →
      ∀ (acc : List ℤ), acc.length = 17 → (∀ d, m - 1 < d → acc.getD d 0 = 0) →
      let q := l.foldl (fun qacc j => poly17Add qacc (poly17Scale (matGet M i j) (chebT17 j))) acc
      q.length = 17 ∧ (∀ d, m - 1 < d → q.getD d 0 = 0) ∧
      (∀ t : ℝ, evalPoly17 q t = evalPoly17 acc t + (l.map fun j => (matGet M i j : ℝ) * chebT j t).sum) := by
    intro l
    induction l with
    | nil =>
      intro _ acc hlen hdeg
      refine ⟨hlen, hdeg, fun t => by simp⟩
    | cons a s ih =>
      intro hl acc hlen hdeg
      have ha : a < m := hl a (List.mem_cons_self ..)
      have hs : ∀ j ∈ s, j < m := fun j hj => hl j (List.mem_cons_of_mem a hj)
      have hstep_len : (poly17Add acc (poly17Scale (matGet M i a) (chebT17 a))).length = 17 :=
        poly17Add_len _ _
      have hstep_deg : ∀ d, m - 1 < d → (poly17Add acc (poly17Scale (matGet M i a) (chebT17 a))).getD d 0 = 0 :=
        fun d hd => poly17Add_getD_zero hdeg
          (fun k hk => poly17Scale_getD_zero _ (fun r hr => chebT17_getD_zero (by omega) (by omega)) hk) hd
      obtain ⟨h1, h2, h3⟩ := ih hs _ hstep_len hstep_deg
      refine ⟨h1, h2, fun t => ?_⟩
      rw [List.foldl_cons, h3 t, evalPoly17_add hlen (poly17Scale_len _ _),
        evalPoly17_scale (chebT17_len a), evalPoly17_chebT17 (by omega),
        List.map_cons, List.sum_cons]
      ring
  have hzero_deg : ∀ d, m - 1 < d → poly17Zero.getD d 0 = 0 := by
    intro d _
    by_cases h17 : d < 17
    · interval_cases d <;> rfl
    · exact list_getD_of_le_len _ _ _ (by rw [poly17Zero_len]; omega)
  obtain ⟨h1, h2, h3⟩ := hgen (List.range m) (fun j hj => List.mem_range.mp hj) poly17Zero poly17Zero_len hzero_deg
  refine ⟨h1, h2, fun t => ?_⟩
  rw [h3 t, evalPoly17_zero, zero_add, Fin.sum_univ_def]
  congr 1
  apply List.ext_getElem <;> simp

private theorem quadCheb17_props {m : ℕ} (hm : m ≤ 9) (M : List (List ℤ)) :
    (∀ d, 2 * (m - 1) < d → (quadCheb17 m M).getD d 0 = 0) ∧
    (∀ t : ℝ, evalPoly17 (quadCheb17 m M) t =
      ∑ i : Fin m, ∑ j : Fin m, (matGet M i.val j.val : ℝ) * chebT i.val t * chebT j.val t) := by
  have hgen : ∀ (l : List ℕ), (∀ i ∈ l, i < m) →
      ∀ (acc : List ℤ), acc.length = 17 → (∀ d, 2 * (m - 1) < d → acc.getD d 0 = 0) →
      let q := l.foldl (fun acc i =>
        let qi := (List.range m).foldl (fun qacc j =>
          poly17Add qacc (poly17Scale (matGet M i j) (chebT17 j))) poly17Zero
        poly17Add acc (poly17Mul (chebT17 i) qi)) acc
      q.length = 17 ∧ (∀ d, 2 * (m - 1) < d → q.getD d 0 = 0) ∧
      (∀ t : ℝ, evalPoly17 q t = evalPoly17 acc t +
        (l.map fun i => chebT i t * ∑ j : Fin m, (matGet M i j.val : ℝ) * chebT j.val t).sum) := by
    intro l
    induction l with
    | nil => intro _ acc hlen hdeg; exact ⟨hlen, hdeg, fun t => by simp⟩
    | cons a s ih =>
      intro hl acc hlen hdeg
      have ha : a < m := hl a (List.mem_cons_self ..)
      have hs : ∀ i ∈ s, i < m := fun i hi => hl i (List.mem_cons_of_mem a hi)
      let qi := (List.range m).foldl (fun qacc j =>
        poly17Add qacc (poly17Scale (matGet M a j) (chebT17 j))) poly17Zero
      obtain ⟨hqi_len, hqi_deg, hqi_ev⟩ := quadCheb17_inner_props hm M a
      have hstep_len : (poly17Add acc (poly17Mul (chebT17 a) qi)).length = 17 := poly17Add_len _ _
      have hstep_deg : ∀ d, 2 * (m - 1) < d →
          (poly17Add acc (poly17Mul (chebT17 a) qi)).getD d 0 = 0 := by
        intro d hd
        refine poly17Add_getD_zero hdeg (fun k hk => ?_) hd
        exact poly17Mul_getD_zero (dp := m - 1) (dq := m - 1)
          (fun r hr => chebT17_getD_zero (by omega) (by omega)) hqi_deg (by omega)
      obtain ⟨h1, h2, h3⟩ := ih hs _ hstep_len hstep_deg
      refine ⟨h1, h2, fun t => ?_⟩
      rw [List.foldl_cons, h3 t, evalPoly17_add hlen (poly17Mul_len _ _),
        evalPoly17_mul_deg (m - 1) (m - 1)
          (fun r hr => chebT17_getD_zero (by omega) (by omega)) hqi_deg (by omega)
          (chebT17_len a) hqi_len t,
        evalPoly17_chebT17 (by omega), hqi_ev t, List.map_cons, List.sum_cons]
      ring
  have hzero_deg : ∀ d, 2 * (m - 1) < d → poly17Zero.getD d 0 = 0 := by
    intro d _
    by_cases h17 : d < 17
    · interval_cases d <;> rfl
    · exact list_getD_of_le_len _ _ _ (by rw [poly17Zero_len]; omega)
  obtain ⟨_, hdeg, hev⟩ := hgen (List.range m) (fun i hi => List.mem_range.mp hi) poly17Zero poly17Zero_len hzero_deg
  refine ⟨hdeg, fun t => ?_⟩
  unfold quadCheb17
  rw [hev t, evalPoly17_zero, zero_add]
  have hmap : ((List.range m).map fun i => chebT i t * ∑ j : Fin m, (matGet M i j.val : ℝ) * chebT j.val t).sum =
      ∑ i : Fin m, chebT i.val t * ∑ j : Fin m, (matGet M i.val j.val : ℝ) * chebT j.val t := by
    rw [Fin.sum_univ_def]; congr 1; apply List.ext_getElem <;> simp
  rw [hmap]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- Linear Chebyshev sum `∑ i < m, (∑ j < m, M[i][j]) * T_i(t)` as a length-17 `List ℤ`. -/
def linearCheb17 (m : ℕ) (M : List (List ℤ)) : List ℤ :=
  (List.range m).foldl (fun acc i =>
    let rowSum := (List.range m).foldl (fun s j => s + matGet M i j) 0
    poly17Add acc (poly17Scale rowSum (chebT17 i))) poly17Zero

private theorem linearCheb17_len (m : ℕ) (M : List (List ℤ)) : (linearCheb17 m M).length = 17 := by
  unfold linearCheb17
  have h : ∀ (l : List ℕ) (acc : List ℤ), acc.length = 17 →
      (l.foldl (fun acc i =>
        let rowSum := (List.range m).foldl (fun s j => s + matGet M i j) 0
        poly17Add acc (poly17Scale rowSum (chebT17 i))) acc).length = 17 := by
    intro l; induction l with
    | nil => intro acc hacc; exact hacc
    | cons a s ih => intro acc _; exact ih _ (poly17Add_len _ _)
  exact h _ _ poly17Zero_len

private theorem evalPoly17_linearCheb17 {m : ℕ} (hm : m ≤ 9) (M : List (List ℤ)) (t : ℝ) :
    evalPoly17 (linearCheb17 m M) t =
      ∑ i : Fin m, ∑ j : Fin m, (matGet M i.val j.val : ℝ) * chebT i.val t := by
  have hgen : ∀ (l : List ℕ), (∀ i ∈ l, i < m) →
      ∀ (acc : List ℤ), acc.length = 17 →
      evalPoly17 (l.foldl (fun acc i =>
        let rowSum := (List.range m).foldl (fun s j => s + matGet M i j) 0
        poly17Add acc (poly17Scale rowSum (chebT17 i))) acc) t =
      evalPoly17 acc t +
        (l.map fun i => (∑ j : Fin m, (matGet M i j.val : ℝ)) * chebT i t).sum := by
    intro l
    induction l with
    | nil => intro _ acc _; simp
    | cons a s ih =>
      intro hl acc hlen
      have ha : a < m := hl a (List.mem_cons_self ..)
      have hs : ∀ i ∈ s, i < m := fun i hi => hl i (List.mem_cons_of_mem a hi)
      rw [List.foldl_cons, ih hs _ (poly17Add_len _ _),
        evalPoly17_add hlen (poly17Scale_len _ _), evalPoly17_scale (chebT17_len a),
        evalPoly17_chebT17 (by omega), List.map_cons, List.sum_cons]
      have hrow : (((List.range m).foldl (fun s j => s + matGet M a j) 0 : ℤ) : ℝ) =
          ∑ j : Fin m, (matGet M a j.val : ℝ) := by
        rw [foldl_add_int17, zero_add, sum_range_int17]; push_cast; rfl
      rw [hrow]; ring
  unfold linearCheb17
  rw [hgen (List.range m) (fun i hi => List.mem_range.mp hi) poly17Zero poly17Zero_len,
    evalPoly17_zero, zero_add]
  have hmap : ((List.range m).map fun i => (∑ j : Fin m, (matGet M i j.val : ℝ)) * chebT i t).sum =
      ∑ i : Fin m, (∑ j : Fin m, (matGet M i.val j.val : ℝ)) * chebT i.val t := by
    rw [Fin.sum_univ_def]; congr 1; apply List.ext_getElem <;> simp
  rw [hmap]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_mul ..

/-- Polynomial `(1 - t²) ^ k` as a length-17 `List ℤ` (for `k ≤ 8`). -/
def oneMinusT2Pow17 : ℕ → List ℤ
  | 0 => [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => [1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => [1, 0, -2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 3 => [1, 0, -3, 0, 3, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 4 => [1, 0, -4, 0, 6, 0, -4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 5 => [1, 0, -5, 0, 10, 0, -10, 0, 5, 0, -1, 0, 0, 0, 0, 0, 0]
  | 6 => [1, 0, -6, 0, 15, 0, -20, 0, 15, 0, -6, 0, 1, 0, 0, 0, 0]
  | 7 => [1, 0, -7, 0, 21, 0, -35, 0, 35, 0, -21, 0, 7, 0, -1, 0, 0]
  | 8 => [1, 0, -8, 0, 28, 0, -56, 0, 70, 0, -56, 0, 28, 0, -8, 0, 1]
  | _ => poly17Zero

private theorem oneMinusT2Pow17_len (k : ℕ) : (oneMinusT2Pow17 k).length = 17 := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

private theorem oneMinusT2Pow17_getD_zero {k d : ℕ} (hk : k ≤ 8) (hd : 2 * k < d) :
    (oneMinusT2Pow17 k).getD d 0 = 0 := by
  by_cases h17 : d < 17
  · interval_cases k <;> interval_cases d <;> rfl
  · exact list_getD_of_le_len _ _ _ (by rw [oneMinusT2Pow17_len]; omega)

private theorem evalPoly17_oneMinusT2Pow17 {k : ℕ} (hk : k ≤ 8) (t : ℝ) :
    evalPoly17 (oneMinusT2Pow17 k) t = (1 - t ^ 2) ^ k := by
  interval_cases k <;>
    simp [oneMinusT2Pow17, evalPoly17, range_17_eq] <;> ring

/-- Exact integer polynomials `32768 * P_k(t)` for `1 ≤ k ≤ 16` (as length-17 `List ℤ`). -/
def legendreP16Int : ℕ → List ℤ
  | 1 => [0, 32768, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => [-16384, 0, 49152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 3 => [0, -49152, 0, 81920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 4 => [12288, 0, -122880, 0, 143360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 5 => [0, 61440, 0, -286720, 0, 258048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 6 => [-10240, 0, 215040, 0, -645120, 0, 473088, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 7 => [0, -71680, 0, 645120, 0, -1419264, 0, 878592, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 8 => [8960, 0, -322560, 0, 1774080, 0, -3075072, 0, 1647360, 0, 0, 0, 0, 0, 0, 0, 0]
  | 9 => [0, 80640, 0, -1182720, 0, 4612608, 0, -6589440, 0, 3111680, 0, 0, 0, 0, 0, 0, 0]
  | 10 => [-8064, 0, 443520, 0, -3843840, 0, 11531520, 0, -14002560, 0, 5912192, 0, 0, 0, 0, 0, 0]
  | 11 => [0, -88704, 0, 1921920, 0, -11531520, 0, 28005120, 0, -29560960, 0, 11286912, 0, 0, 0, 0, 0]
  | 12 => [7392, 0, -576576, 0, 7207200, 0, -32672640, 0, 66512160, 0, -62078016, 0, 21633248, 0, 0, 0, 0]
  | 13 => [0, 96096, 0, -2882880, 0, 24504480, 0, -88682880, 0, 155195040, 0, -129799488, 0, 41602400, 0, 0, 0]
  | 14 => [-6864, 0, 720720, 0, -12252240, 0, 77597520, 0, -232792560, 0, 356948592, 0, -270415600, 0, 80233200, 0, 0]
  | 15 => [0, -102960, 0, 4084080, 0, -46558512, 0, 232792560, 0, -594914320, 0, 811246800, 0, -561632400, 0, 155117520, 0]
  | 16 => [6435, 0, -875160, 0, 19399380, 0, -162954792, 0, 669278610, 0, -1487285800, 0, 1825305300, 0, -1163381400, 0, 300540195]
  | _ => poly17Zero

private theorem legendreP16Int_len (k : ℕ) : (legendreP16Int k).length = 17 := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

private theorem evalPoly17_legendreP16Int {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 16) (t : ℝ) :
    evalPoly17 (legendreP16Int k) t = 32768 * legendreP16 k t := by
  interval_cases k <;>
    simp [legendreP16Int, evalPoly17, range_17_eq, legendreP16, legendreP12] <;> ring

/-! ## Trivariate Chebyshev polynomials `T_k(u)` and `T_k(v)` as `Poly3` -/

def chebT3U : ℕ → Poly3
  | 0 => [(0, 0, 0, 1)]
  | 1 => [(1, 0, 0, 1)]
  | 2 => [(0, 0, 0, -1), (2, 0, 0, 2)]
  | 3 => [(1, 0, 0, -3), (3, 0, 0, 4)]
  | 4 => [(0, 0, 0, 1), (2, 0, 0, -8), (4, 0, 0, 8)]
  | 5 => [(1, 0, 0, 5), (3, 0, 0, -20), (5, 0, 0, 16)]
  | 6 => [(0, 0, 0, -1), (2, 0, 0, 18), (4, 0, 0, -48), (6, 0, 0, 32)]
  | 7 => [(1, 0, 0, -7), (3, 0, 0, 56), (5, 0, 0, -112), (7, 0, 0, 64)]
  | 8 => [(0, 0, 0, 1), (2, 0, 0, -32), (4, 0, 0, 160), (6, 0, 0, -256), (8, 0, 0, 128)]
  | _ => []

def chebT3V : ℕ → Poly3
  | 0 => [(0, 0, 0, 1)]
  | 1 => [(0, 1, 0, 1)]
  | 2 => [(0, 0, 0, -1), (0, 2, 0, 2)]
  | 3 => [(0, 1, 0, -3), (0, 3, 0, 4)]
  | 4 => [(0, 0, 0, 1), (0, 2, 0, -8), (0, 4, 0, 8)]
  | 5 => [(0, 1, 0, 5), (0, 3, 0, -20), (0, 5, 0, 16)]
  | 6 => [(0, 0, 0, -1), (0, 2, 0, 18), (0, 4, 0, -48), (0, 6, 0, 32)]
  | 7 => [(0, 1, 0, -7), (0, 3, 0, 56), (0, 5, 0, -112), (0, 7, 0, 64)]
  | 8 => [(0, 0, 0, 1), (0, 2, 0, -32), (0, 4, 0, 160), (0, 6, 0, -256), (0, 8, 0, 128)]
  | _ => []

private theorem evalPoly3_chebT3U {k : ℕ} (hk : k ≤ 8) (u v t : ℝ) :
    evalPoly3 (chebT3U k) u v t = chebT k u := by
  interval_cases k <;> simp [chebT3U, evalPoly3, chebT] <;> ring

private theorem evalPoly3_chebT3V {k : ℕ} (hk : k ≤ 8) (u v t : ℝ) :
    evalPoly3 (chebT3V k) u v t = chebT k v := by
  interval_cases k <;> simp [chebT3V, evalPoly3, chebT] <;> ring

/-- Fast dot product of two integer row lists (zero `List.getD` overhead). -/
def dotList : List ℤ → List ℤ → ℤ
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => a * b + dotList as bs

private theorem dotList_eq_sum : ∀ (m : ℕ) (u v : List ℤ), u.length ≤ m →
    (dotList u v : ℝ) = ∑ k : Fin m, (u.getD k.val 0 : ℝ) * (v.getD k.val 0 : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro u v hu
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu0; simp [dotList]
  | succ m ih =>
    intro u v hu
    rw [Fin.sum_univ_succ]
    cases u with
    | nil => simp [dotList]
    | cons a as =>
      cases v with
      | nil => simp [dotList]
      | cons b bs =>
        simp only [dotList, Int.cast_add, Int.cast_mul, Fin.val_zero, List.getD_cons_zero,
          Fin.val_succ, List.getD_cons_succ]
        rw [ih as bs (by simp at hu; omega)]

/-- Inner column loop for `isCholeskyDDLower`. -/
def choleskyCheckCols (dR2 dMi : ℤ) (i : ℕ) (lRow : List ℤ) :
    ℕ → ℤ → ℤ → List ℤ → List (List ℤ) → Bool
  | _, diag, offSum, [], _ => decide (offSum ≤ diag)
  | _, diag, offSum, _, [] => decide (offSum ≤ diag)
  | j, diag, offSum, mij :: mTail, lj :: lTail =>
    let eij := dR2 * mij - dMi * dotList lRow lj
    if j == i then choleskyCheckCols dR2 dMi i lRow (j + 1) eij offSum mTail lTail
    else choleskyCheckCols dR2 dMi i lRow (j + 1) diag (offSum + Int.natAbs eij) mTail lTail

/-- Outer row loop for `isCholeskyDDLower`. -/
def choleskyCheckRows (m : ℕ) (dR2 dMi : ℤ) (L : List (List ℤ)) :
    ℕ → List (List ℤ) → List (List ℤ) → Bool
  | _, [], _ => true
  | _, _, [] => true
  | i, mRow :: mRest, lRow :: lRest =>
    decide (mRow.length = m) && choleskyCheckCols dR2 dMi i lRow 0 0 0 mRow L &&
      choleskyCheckRows m dR2 dMi L (i + 1) mRest lRest

/-- Fast row-by-row Cholesky + DD check using lower-triangular `L = Rᵀ`
(each row `L[i]` has length `≤ i + 1 ≤ m`, eliminating `O(m⁴)` `List.getD` traversals). -/
def isCholeskyDDLower (m dM dR : ℕ) (M L : List (List ℤ)) : Bool :=
  decide (0 < dM) &&
  decide (0 < dR) &&
  decide (L.length = m) &&
  L.all (fun row => decide (row.length ≤ m)) &&
  isSymmInt m M &&
  decide (M.length = m) &&
  choleskyCheckRows m ((dR : ℤ) * (dR : ℤ)) (dM : ℤ) L 0 M L

private theorem checkCols_sound (m : ℕ) (dR2 dMi : ℤ) (i : ℕ) (lRow : List ℤ) (L : List (List ℤ))
    (mRow : List ℤ) (hmRow : mRow.length = m) (hL : L.length = m) :
    ∀ (j : ℕ) (diag offSum : ℤ) (mSub : List ℤ) (lSub : List (List ℤ)),
      mSub = mRow.drop j → lSub = L.drop j → j ≤ m →
      choleskyCheckCols dR2 dMi i lRow j diag offSum mSub lSub = true →
      (offSum : ℝ) + (∑ k : Fin (m - j),
        if j + k.val = i then (0 : ℝ)
        else |((dR2 * mRow.getD (j + k.val) 0 - dMi * dotList lRow (L.getD (j + k.val) []) : ℤ) : ℝ)|) ≤
      (if i < j then (diag : ℝ) else if i < m then ((dR2 * mRow.getD i 0 - dMi * dotList lRow (L.getD i []) : ℤ) : ℝ) else (diag : ℝ)) := by
  intro j diag offSum mSub lSub hmSub hlSub hjm hchk
  induction hlen : m - j generalizing j diag offSum mSub lSub with
  | zero =>
    have hj : j = m := by omega
    subst hj
    have hm0 : mSub = [] := by rw [hmSub, List.drop_eq_nil_iff]; omega
    have hl0 : lSub = [] := by rw [hlSub, List.drop_eq_nil_iff]; omega
    subst hm0; subst hl0
    simp only [choleskyCheckCols, decide_eq_true_eq] at hchk
    simp only [Fin.sum_univ_zero, add_zero]
    split_ifs <;> exact_mod_cast hchk
  | succ k ih =>
    have hjm' : j < m := by omega
    have hmCons : mSub = mRow[j]'(by omega) :: mRow.drop (j + 1) := by
      rw [hmSub, List.cons_getElem_drop_succ]
    have hlCons : lSub = L[j]'(by omega) :: L.drop (j + 1) := by
      rw [hlSub, List.cons_getElem_drop_succ]
    rw [hmCons, hlCons] at hchk
    unfold choleskyCheckCols at hchk
    have hmget : mRow.getD j 0 = mRow[j]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hlget : L.getD j [] = L[j]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hsum_split :
        (∑ r : Fin (k + 1),
          if j + r.val = i then (0 : ℝ)
          else |((dR2 * mRow.getD (j + r.val) 0 - dMi * dotList lRow (L.getD (j + r.val) []) : ℤ) : ℝ)|) =
        (if j = i then (0 : ℝ) else |((dR2 * mRow.getD j 0 - dMi * dotList lRow (L.getD j []) : ℤ) : ℝ)|) +
        (∑ r : Fin k,
          if j + 1 + r.val = i then (0 : ℝ)
          else |((dR2 * mRow.getD (j + 1 + r.val) 0 - dMi * dotList lRow (L.getD (j + 1 + r.val) []) : ℤ) : ℝ)|) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, add_zero, Fin.val_succ]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      have : j + (r.val + 1) = j + 1 + r.val := by omega
      simp [this]
    rw [hsum_split]
    by_cases hji : j = i
    · subst hji
      simp only [beq_self_eq_true, ↓reduceIte] at hchk
      have hrec := ih (j + 1) (dR2 * mRow[j]'(by omega) - dMi * dotList lRow (L[j]'(by omega))) offSum
        (mRow.drop (j + 1)) (L.drop (j + 1)) rfl rfl (by omega) hchk (by omega)
      have hlt1 : j < j + 1 := by omega
      simp only [hlt1, ↓reduceIte] at hrec
      simp only [↓reduceIte, zero_add, Nat.lt_irrefl, hjm']
      rw [← hmget, ← hlget] at hrec
      exact hrec
    · have hbeq : (j == i) = false := beq_false_of_ne hji
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hchk
      have hrec := ih (j + 1) diag (offSum + Int.natAbs (dR2 * mRow[j]'(by omega) - dMi * dotList lRow (L[j]'(by omega))))
        (mRow.drop (j + 1)) (L.drop (j + 1)) rfl rfl (by omega) hchk (by omega)
      have hnatAbs : ((Int.natAbs (dR2 * mRow[j]'(by omega) - dMi * dotList lRow (L[j]'(by omega))) : ℤ) : ℝ) =
          |((dR2 * mRow.getD j 0 - dMi * dotList lRow (L.getD j []) : ℤ) : ℝ)| := by
        rw [hmget, hlget, Int.natCast_natAbs, Int.cast_abs]
      have hlt_eq : (i < j + 1) ↔ (i < j) := by omega
      simp only [hji, ↓reduceIte]
      simp only [hlt_eq, Int.cast_add, hnatAbs] at hrec
      linarith

theorem isCholeskyDDLower_sound {m dM dR : ℕ} {M L : List (List ℤ)}
    (h : isCholeskyDDLower m dM dR M L = true) :
    (toRealMat m dM M).PosSemidef := by
  unfold isCholeskyDDLower at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, isSymmInt, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hdM, hdR⟩, hLlen⟩, hLrows⟩, hsym⟩, hMlen⟩, hrows⟩ := h
  have hdM_pos : (0 : ℝ) < (dM : ℝ) := Nat.cast_pos.mpr hdM
  have hdR_pos : (0 : ℝ) < (dR : ℝ) := Nat.cast_pos.mpr hdR
  have hsymR : (toRealMat m dM M).IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, toRealMat, Matrix.of_apply]
    rw [hsym j.val j.isLt i.val i.isLt]
  refine posSemidef_of_cholesky_dd (toRealMat m dM M) (toRealMat m dR L)ᵀ hsymR fun i => ?_
  have hrow_i : ∀ (idx : ℕ) (mSub lSub : List (List ℤ)),
      mSub = M.drop idx → lSub = L.drop idx → idx ≤ i.val →
      choleskyCheckRows m ((dR : ℤ) * (dR : ℤ)) (dM : ℤ) L idx mSub lSub = true →
      (M.getD i.val []).length = m ∧
      choleskyCheckCols ((dR : ℤ) * (dR : ℤ)) (dM : ℤ) i.val (L.getD i.val []) 0 0 0 (M.getD i.val []) L = true := by
    intro idx mSub lSub hmSub hlSub hle hchk
    induction hdiff : i.val - idx generalizing idx mSub lSub with
    | zero =>
      have hidx : idx = i.val := by omega
      subst hidx
      have hmCons : mSub = M[i.val]'(by omega) :: M.drop (i.val + 1) := by
        rw [hmSub, List.cons_getElem_drop_succ]
      have hlCons : lSub = L[i.val]'(by omega) :: L.drop (i.val + 1) := by
        rw [hlSub, List.cons_getElem_drop_succ]
      rw [hmCons, hlCons] at hchk
      unfold choleskyCheckRows at hchk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
      have hmget : M.getD i.val [] = M[i.val]'(by omega) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      have hlget : L.getD i.val [] = L[i.val]'(by omega) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      rw [hmget, hlget]
      exact ⟨hchk.1.1, hchk.1.2⟩
    | succ d ih =>
      have hidx_lt : idx < m := by omega
      have hmCons : mSub = M[idx]'(by omega) :: M.drop (idx + 1) := by
        rw [hmSub, List.cons_getElem_drop_succ]
      have hlCons : lSub = L[idx]'(by omega) :: L.drop (idx + 1) := by
        rw [hlSub, List.cons_getElem_drop_succ]
      rw [hmCons, hlCons] at hchk
      unfold choleskyCheckRows at hchk
      simp only [Bool.and_eq_true] at hchk
      exact ih (idx + 1) (M.drop (idx + 1)) (L.drop (idx + 1)) rfl rfl (by omega) hchk.2 (by omega)
  obtain ⟨hMi_len, hcols⟩ := hrow_i 0 M L rfl rfl (Nat.zero_le _) hrows
  have hcc := checkCols_sound m ((dR : ℤ) * (dR : ℤ)) (dM : ℤ) i.val (L.getD i.val []) L
    (M.getD i.val []) hMi_len hLlen 0 0 0 (M.getD i.val []) L rfl rfl (Nat.zero_le _) hcols
  have hLi_len : (L.getD i.val []).length ≤ m := by
    have hmem : L[i.val]'(by omega) ∈ L := List.getElem_mem (by omega)
    have hlget : L.getD i.val [] = L[i.val]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [hlget]; exact hLrows _ hmem
  have hentry : ∀ j : Fin m,
      (((dR : ℤ) * (dR : ℤ) * (M.getD i.val []).getD j.val 0 - (dM : ℤ) * dotList (L.getD i.val []) (L.getD j.val []) : ℤ) : ℝ) =
      ((dM : ℝ) * ((dR : ℝ) * (dR : ℝ))) *
        (toRealMat m dM M - ((toRealMat m dR L)ᵀ)ᵀ * (toRealMat m dR L)ᵀ) i j := by
    intro j
    simp only [Matrix.sub_apply, Matrix.transpose_transpose, Matrix.mul_apply, Matrix.transpose_apply,
      toRealMat, Matrix.of_apply, matGet, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [dotList_eq_sum m (L.getD i.val []) (L.getD j.val []) hLi_len]
    have hsum : (dM : ℝ) * ((dR : ℝ) * (dR : ℝ)) *
        (∑ k : Fin m, ((L.getD i.val []).getD k.val 0 : ℝ) / (dR : ℝ) * (((L.getD j.val []).getD k.val 0 : ℝ) / (dR : ℝ))) =
        (dM : ℝ) * ∑ k : Fin m, ((L.getD i.val []).getD k.val 0 : ℝ) * ((L.getD j.val []).getD k.val 0 : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp [hdR_pos.ne']
    have h1 : (dM : ℝ) * ((dR : ℝ) * (dR : ℝ)) * (((M.getD i.val []).getD j.val 0 : ℝ) / (dM : ℝ)) =
        (dR : ℝ) * (dR : ℝ) * ((M.getD i.val []).getD j.val 0 : ℝ) := by
      field_simp [hdM_pos.ne']
    rw [mul_sub, h1, hsum]
  have hscale_pos : (0 : ℝ) < (dM : ℝ) * ((dR : ℝ) * (dR : ℝ)) := by positivity
  simp only [Int.cast_zero, zero_add, Nat.sub_zero, Nat.not_lt_zero, ↓reduceIte, i.isLt] at hcc
  have hcc_sum :
      (∑ k : Fin m, if k.val = i.val then (0 : ℝ)
        else abs (((dR : ℤ) * (dR : ℤ) * (M.getD i.val []).getD k.val 0 -
                (dM : ℤ) * dotList (L.getD i.val []) (L.getD k.val []) : ℤ) : ℝ)) =
      ((dM : ℝ) * ((dR : ℝ) * (dR : ℝ))) *
        ∑ j ∈ Finset.univ.erase i,
          |(toRealMat m dM M - ((toRealMat m dR L)ᵀ)ᵀ * (toRealMat m dR L)ᵀ) i j| := by
    have hfilt : ∑ k : Fin m, (if k.val = i.val then (0 : ℝ)
        else abs (((dR : ℤ) * (dR : ℤ) * (M.getD i.val []).getD k.val 0 -
                (dM : ℤ) * dotList (L.getD i.val []) (L.getD k.val []) : ℤ) : ℝ)) =
        ∑ k ∈ Finset.univ.erase i,
          abs (((dR : ℤ) * (dR : ℤ) * (M.getD i.val []).getD k.val 0 -
                (dM : ℤ) * dotList (L.getD i.val []) (L.getD k.val []) : ℤ) : ℝ) := by
      have h1 := Finset.add_sum_erase (Finset.univ : Finset (Fin m))
        (fun k : Fin m => if k.val = i.val then (0 : ℝ)
          else abs (((dR : ℤ) * (dR : ℤ) * (M.getD i.val []).getD k.val 0 -
                  (dM : ℤ) * dotList (L.getD i.val []) (L.getD k.val []) : ℤ) : ℝ)) (Finset.mem_univ i)
      simp only [↓reduceIte, zero_add] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hne : k.val ≠ i.val := fun heq => (Finset.mem_erase.mp hk).1 (Fin.ext heq)
      simp [hne]
    rw [hfilt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hentry k, abs_mul, abs_of_pos hscale_pos]
  rw [hcc_sum, hentry i] at hcc
  nlinarith

/-- Fast structural linear combination `∑_j row[j] * basis[j]` (zero `List.getD` overhead). -/
def linCombPoly3 : List ℤ → List Poly3 → Poly3
  | [], _ => []
  | _, [] => []
  | c :: cs, b :: bs =>
    if c == 0 then linCombPoly3 cs bs
    else mergePoly3 (poly3Scale c b) (linCombPoly3 cs bs)

/-- Fast structural quadratic form `∑_{i,j} M[i][j] * basis[i] * basis[j]`. -/
def quadPoly3FastAux : List (List ℤ) → List Poly3 → List Poly3 → Poly3
  | [], _, _ => []
  | _, [], _ => []
  | row :: rows, b :: bs, allB =>
    mergePoly3 (mulPoly3Sorted b (linCombPoly3 row allB)) (quadPoly3FastAux rows bs allB)

def quadPoly3Fast (M : List (List ℤ)) (basis : List Poly3) : Poly3 :=
  quadPoly3FastAux M basis basis

private theorem evalPoly3_linCombPoly3 : ∀ (m : ℕ) (row : List ℤ) (bs : List Poly3) (u v t : ℝ),
    row.length = m → bs.length = m →
    evalPoly3 (linCombPoly3 row bs) u v t =
      ∑ j : Fin m, (row.getD j.val 0 : ℝ) * evalPoly3 (bs.getD j.val []) u v t := by
  intro m
  induction m with
  | zero =>
    intro row bs u v t hr hbs
    have hr0 : row = [] := List.eq_nil_of_length_eq_zero hr
    subst hr0; simp [linCombPoly3, evalPoly3_nil]
  | succ m ih =>
    intro row bs u v t hr hbs
    cases row with
    | nil => simp at hr
    | cons c cs =>
      cases bs with
      | nil => simp at hbs
      | cons b bs' =>
        rw [Fin.sum_univ_succ]
        simp only [linCombPoly3, Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
        by_cases hc : c == 0
        · have hc0 : c = 0 := by simpa using hc
          subst hc0
          simp only [beq_self_eq_true, ↓reduceIte, Int.cast_zero, zero_mul, zero_add]
          exact ih cs bs' u v t (by simp at hr; omega) (by simp at hbs; omega)
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, evalPoly3_mergePoly3, evalPoly3_scale]
          rw [ih cs bs' u v t (by simp at hr; omega) (by simp at hbs; omega)]

private theorem evalPoly3_quadPoly3FastAux (m : ℕ) (allB : List Poly3) (hall : allB.length = m) (u v t : ℝ) :
    ∀ (k : ℕ) (rows : List (List ℤ)) (bs : List Poly3),
      rows.length = k → bs.length = k → (∀ r ∈ rows, r.length = m) →
      evalPoly3 (quadPoly3FastAux rows bs allB) u v t =
        ∑ i : Fin k, ∑ j : Fin m,
          ((rows.getD i.val []).getD j.val 0 : ℝ) *
            (evalPoly3 (bs.getD i.val []) u v t * evalPoly3 (allB.getD j.val []) u v t) := by
  intro k
  induction k with
  | zero =>
    intro rows bs hr _ _
    have hr0 : rows = [] := List.eq_nil_of_length_eq_zero hr
    subst hr0; simp [quadPoly3FastAux, evalPoly3_nil]
  | succ k ih =>
    intro rows bs hr hbs hrows
    cases rows with
    | nil => simp at hr
    | cons r rs =>
      cases bs with
      | nil => simp at hbs
      | cons b bs' =>
        rw [Fin.sum_univ_succ]
        simp only [quadPoly3FastAux, evalPoly3_mergePoly3, evalPoly3_mulPoly3Sorted,
          Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
        rw [evalPoly3_linCombPoly3 m r allB u v t (hrows r (List.mem_cons_self ..)) hall,
          ih rs bs' (by simp at hr; omega) (by simp at hbs; omega)
            (fun r' hr' => hrows r' (List.mem_cons_of_mem r hr')), Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => by ring

theorem evalPoly3_quadPoly3Fast_nonneg {m D : ℕ} (hD : 0 < D) {M : List (List ℤ)}
    (hM : (toRealMat m D M).PosSemidef) (basis : List Poly3)
    (hMlen : M.length = m) (hblen : basis.length = m) (hMrows : ∀ r ∈ M, r.length = m)
    (u v t : ℝ) :
    0 ≤ evalPoly3 (quadPoly3Fast M basis) u v t := by
  unfold quadPoly3Fast
  rw [evalPoly3_quadPoly3FastAux m basis hblen u v t m M basis hMlen hblen hMrows]
  let vec : Fin m → ℝ := fun i => evalPoly3 (basis.getD i.val []) u v t
  have hq := posSemidef_quad_nonneg hM vec
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hmul : (D : ℝ) * (∑ a : Fin m, ∑ b : Fin m, vec a * toRealMat m D M a b * vec b) =
      ∑ i : Fin m, ∑ j : Fin m, ((M.getD i.val []).getD j.val 0 : ℝ) * (vec i * vec j) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    simp only [toRealMat, Matrix.of_apply, matGet]; field_simp [hD_pos.ne']
  have : 0 ≤ (D : ℝ) * ∑ a : Fin m, ∑ b : Fin m, vec a * toRealMat m D M a b * vec b :=
    mul_nonneg hD_pos.le hq
  linarith

/-! ## Degree-8 + Legendre `P₁..P₁₆` rational SDP certificate (`BVCert8`) -/

/-- Exact rational Chebyshev-basis Bachoc–Vallentin degree-8 SDP certificate with
two-point Legendre terms `P₁..P₁₆` and 7 reduced `S₃`-symmetric trivariate SOS blocks. -/
structure BVCert8 where
  sNum : ℤ
  sDen : ℕ
  dK : ℕ
  dS0 : ℕ
  dS : ℕ
  dR : ℕ
  -- 9 Chebyshev-basis kernel matrices F_0 (9×9) .. F_8 (1×1), scaled by dK
  F0 : List (List ℤ)
  R_F0 : List (List ℤ)
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
  F6 : List (List ℤ)
  R_F6 : List (List ℤ)
  F7 : List (List ℤ)
  R_F7 : List (List ℤ)
  F8 : List (List ℤ)
  R_F8 : List (List ℤ)
  -- 16 nonnegative Legendre weights c2[0..15] for P_1..P_16, scaled by dK
  c2 : List ℤ
  -- Univariate Chebyshev-basis SOS matrices: S0 (9×9, scaled by dS0) and S1 (8×8, scaled by dK)
  S0 : List (List ℤ)
  R_S0 : List (List ℤ)
  S1 : List (List ℤ)
  R_S1 : List (List ℤ)
  -- 7 trivariate S3-reduced SOS blocks with per-block denominators dM_i and scales sc_i (dM_i * sc_i = dS):
  -- 0,1,2: mult 1 (one_triv, one_std, one_sign);
  -- 3,4,5: mult Delta (delta_triv, delta_std, delta_sign);
  -- 6: mult g1 = (s - u)(u + 1) (g1_even).
  m0 : ℕ
  dM0 : ℕ
  sc0 : ℕ
  M0 : List (List ℤ)
  R0 : List (List ℤ)
  b0 : List Poly3
  m1 : ℕ
  dM1 : ℕ
  sc1 : ℕ
  M1 : List (List ℤ)
  R1 : List (List ℤ)
  b1 : List Poly3
  m2 : ℕ
  dM2 : ℕ
  sc2 : ℕ
  M2 : List (List ℤ)
  R2 : List (List ℤ)
  b2 : List Poly3
  m3 : ℕ
  dM3 : ℕ
  sc3 : ℕ
  M3 : List (List ℤ)
  R3 : List (List ℤ)
  b3 : List Poly3
  m4 : ℕ
  dM4 : ℕ
  sc4 : ℕ
  M4 : List (List ℤ)
  R4 : List (List ℤ)
  b4 : List Poly3
  m5 : ℕ
  dM5 : ℕ
  sc5 : ℕ
  M5 : List (List ℤ)
  R5 : List (List ℤ)
  b5 : List Poly3
  m6 : ℕ
  dM6 : ℕ
  sc6 : ℕ
  M6 : List (List ℤ)
  R6 : List (List ℤ)
  b6 : List Poly3

namespace BVCert8

/-- Rational inner-product threshold `s = sNum / sDen`. -/
noncomputable def s (c : BVCert8) : ℝ := (c.sNum : ℝ) / (c.sDen : ℝ)

/-- Integer numerator of the certified upper bound `bound = boundNum / dK`. -/
def boundNum (c : BVCert8) : ℤ :=
  (c.dK : ℤ) +
  (List.range 9).foldl (fun acc i =>
    acc + (List.range 9).foldl (fun acc2 j => acc2 + matGet c.F0 i j) 0) 0 +
  (List.range 16).foldl (fun acc k => acc + c.c2.getD k 0) 0

/-- Real-valued certified upper bound `boundNum / dK`. -/
noncomputable def bound (c : BVCert8) : ℝ := (c.boundNum : ℝ) / (c.dK : ℝ)

/-- Real kernel matrix family `F_0 (9×9), …, F_8 (1×1)`. -/
noncomputable def toRealF (c : BVCert8) :
    (k : Fin 9) → Matrix (Fin (8 - k.val + 1)) (Fin (8 - k.val + 1)) ℝ
  | ⟨0, _⟩ => toRealMat 9 c.dK c.F0
  | ⟨1, _⟩ => toRealMat 8 c.dK c.F1
  | ⟨2, _⟩ => toRealMat 7 c.dK c.F2
  | ⟨3, _⟩ => toRealMat 6 c.dK c.F3
  | ⟨4, _⟩ => toRealMat 5 c.dK c.F4
  | ⟨5, _⟩ => toRealMat 4 c.dK c.F5
  | ⟨6, _⟩ => toRealMat 3 c.dK c.F6
  | ⟨7, _⟩ => toRealMat 2 c.dK c.F7
  | ⟨8, _⟩ => toRealMat 1 c.dK c.F8

/-- Real Legendre weights `c2_k = c.c2[k] / dK` for `k = 0..15` (`P_1..P_16`). -/
noncomputable def toRealC2 (c : BVCert8) (k : Fin 16) : ℝ :=
  (c.c2.getD k.val 0 : ℝ) / (c.dK : ℝ)

/-- Univariate polynomial `32768 * dK * (bvChebG2Unaug F t + ∑_{k=1}^{16} c2_k P_k(t))`. -/
def polyG2 (c : BVCert8) : List ℤ :=
  let g3 :=
    poly17Add (poly17Scale 2 (linearCheb17 9 c.F0))
      (poly17Add (poly17Mul (quadCheb17 9 c.F0) (oneMinusT2Pow17 0))
      (poly17Add (poly17Mul (quadCheb17 8 c.F1) (oneMinusT2Pow17 1))
      (poly17Add (poly17Mul (quadCheb17 7 c.F2) (oneMinusT2Pow17 2))
      (poly17Add (poly17Mul (quadCheb17 6 c.F3) (oneMinusT2Pow17 3))
      (poly17Add (poly17Mul (quadCheb17 5 c.F4) (oneMinusT2Pow17 4))
      (poly17Add (poly17Mul (quadCheb17 4 c.F5) (oneMinusT2Pow17 5))
      (poly17Add (poly17Mul (quadCheb17 3 c.F6) (oneMinusT2Pow17 6))
      (poly17Add (poly17Mul (quadCheb17 2 c.F7) (oneMinusT2Pow17 7))
                 (poly17Mul (quadCheb17 1 c.F8) (oneMinusT2Pow17 8))))))))))
  let g2 := (List.range 16).foldl (fun acc k =>
    poly17Add acc (poly17Scale (c.c2.getD k 0) (legendreP16Int (k + 1)))) poly17Zero
  poly17Add (poly17Scale 32768 g3) g2

/-- Univariate multiplier `sDen * (s - t)(t + 1) = sNum + (sNum - sDen) t - sDen t²`. -/
def poly17G1 (sNum : ℤ) (sDen : ℕ) : List ℤ :=
  [sNum, sNum - (sDen : ℤ), -(sDen : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Univariate polynomial identity check:
`32768 * sDen * dS0 * dK * (-1 - G2(t)) = 32768 * sDen * dK * S0(t) + 32768 * dS0 * (sDen * (s-t)(t+1)) * S1(t)`. -/
def checkEq2 (c : BVCert8) : Bool :=
  let constNeg := [-32768 * (c.dK : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  let lhs := poly17Scale ((c.sDen : ℤ) * (c.dS0 : ℤ))
    (poly17Add constNeg (poly17Scale (-1) c.polyG2))
  let rhs := poly17Add
    (poly17Scale (32768 * (c.sDen : ℤ) * (c.dK : ℤ)) (quadCheb17 9 c.S0))
    (poly17Scale (32768 * (c.dS0 : ℤ)) (poly17Mul (poly17G1 c.sNum c.sDen) (quadCheb17 8 c.S1)))
  lhs == rhs

/-- Trivariate kernel block `∑_{i,j} F_k[i,j] T_i(u) T_j(v) bvQ k`. -/
def kernelChebPoly3 (k m : ℕ) (Fk : List (List ℤ)) : Poly3 :=
  let qk := bvQPoly3 k
  let matPoly := (List.range m).foldl (fun acc i =>
    let ti := chebT3U i
    let qi := (List.range m).foldl (fun qacc j =>
      mergePoly3 (poly3Scale (matGet Fk i j) (chebT3V j)) qacc) []
    mergePoly3 (mulPoly3Sorted ti qi) acc) []
  mulPoly3Sorted matPoly qk

/-- Unsymmetrized trivariate polynomial `dK * bvChebG3Unaug F`. -/
def polyG3 (c : BVCert8) : Poly3 :=
  mergePoly3 (kernelChebPoly3 0 9 c.F0)
  (mergePoly3 (kernelChebPoly3 1 8 c.F1)
  (mergePoly3 (kernelChebPoly3 2 7 c.F2)
  (mergePoly3 (kernelChebPoly3 3 6 c.F3)
  (mergePoly3 (kernelChebPoly3 4 5 c.F4)
  (mergePoly3 (kernelChebPoly3 5 4 c.F5)
  (mergePoly3 (kernelChebPoly3 6 3 c.F6)
  (mergePoly3 (kernelChebPoly3 7 2 c.F7)
              (kernelChebPoly3 8 1 c.F8))))))))

/-- Trivariate multiplier `Δ(u, v, t) = 1 + 2uvt - u² - v² - t²`. -/
def polyDelta8 : Poly3 :=
  [(0, 0, 0, 1), (1, 1, 1, 2), (2, 0, 0, -1), (0, 2, 0, -1), (0, 0, 2, -1)]

/-- Trivariate multiplier `sDen * (s - u)(u + 1)`. -/
def polyG1_8 (sNum : ℤ) (sDen : ℕ) : Poly3 :=
  [(0, 0, 0, sNum), (1, 0, 0, sNum - (sDen : ℤ)), (2, 0, 0, -(sDen : ℤ))]

/-- Canonicalized trivariate SOS RHS (scaled by `sDen * dS`), using per-block scales `sc0..sc6`. -/
def polyRHS3Canon (c : BVCert8) : Poly3 :=
  let sD : ℤ := (c.sDen : ℤ)
  let q0 := sym3Canon (quadPoly3Fast c.M0 c.b0)
  let q1 := sym3Canon (quadPoly3Fast c.M1 c.b1)
  let q2 := sym3Canon (quadPoly3Fast c.M2 c.b2)
  let q3 := sym3Canon (mulPoly3Sorted polyDelta8 (quadPoly3Fast c.M3 c.b3))
  let q4 := sym3Canon (mulPoly3Sorted polyDelta8 (quadPoly3Fast c.M4 c.b4))
  let q5 := sym3Canon (mulPoly3Sorted polyDelta8 (quadPoly3Fast c.M5 c.b5))
  let q6 := sym3Canon (mulPoly3Sorted (polyG1_8 c.sNum c.sDen) (quadPoly3Fast c.M6 c.b6))
  sym3Canon (
    poly3Scale (sD * (c.sc0 : ℤ)) q0 ++
    poly3Scale (sD * (c.sc1 : ℤ)) q1 ++
    poly3Scale (sD * (c.sc2 : ℤ)) q2 ++
    poly3Scale (sD * (c.sc3 : ℤ)) q3 ++
    poly3Scale (sD * (c.sc4 : ℤ)) q4 ++
    poly3Scale (sD * (c.sc5 : ℤ)) q5 ++
    poly3Scale (c.sc6 : ℤ) q6)

/-- Complete Boolean validity check for a degree-8 + Legendre `P₁..P₁₆` certificate.
Note: `R0..R6` store the lower-triangular Cholesky factors `L_i = R_iᵀ` (each row of length `≤ m_i`). -/
def isValid (c : BVCert8) : Bool :=
  decide (0 < c.sDen) &&
  decide (0 < c.dK) &&
  decide (0 < c.dS0) &&
  decide (0 < c.dS) &&
  decide (0 < c.dR) &&
  decide (-(c.sDen : ℤ) < c.sNum) &&
  (List.range 16).all (fun k => decide (0 ≤ c.c2.getD k 0)) &&
  decide (c.dM0 * c.sc0 = c.dS) &&
  decide (c.dM1 * c.sc1 = c.dS) &&
  decide (c.dM2 * c.sc2 = c.dS) &&
  decide (c.dM3 * c.sc3 = c.dS) &&
  decide (c.dM4 * c.sc4 = c.dS) &&
  decide (c.dM5 * c.sc5 = c.dS) &&
  decide (c.dM6 * c.sc6 = c.dS) &&
  decide (c.b0.length = c.m0) &&
  decide (c.b1.length = c.m1) &&
  decide (c.b2.length = c.m2) &&
  decide (c.b3.length = c.m3) &&
  decide (c.b4.length = c.m4) &&
  decide (c.b5.length = c.m5) &&
  decide (c.b6.length = c.m6) &&
  isCholeskyDDValid 9 c.dK c.dR c.F0 c.R_F0 &&
  isCholeskyDDValid 8 c.dK c.dR c.F1 c.R_F1 &&
  isCholeskyDDValid 7 c.dK c.dR c.F2 c.R_F2 &&
  isCholeskyDDValid 6 c.dK c.dR c.F3 c.R_F3 &&
  isCholeskyDDValid 5 c.dK c.dR c.F4 c.R_F4 &&
  isCholeskyDDValid 4 c.dK c.dR c.F5 c.R_F5 &&
  isCholeskyDDValid 3 c.dK c.dR c.F6 c.R_F6 &&
  isCholeskyDDValid 2 c.dK c.dR c.F7 c.R_F7 &&
  isCholeskyDDValid 1 c.dK c.dR c.F8 c.R_F8 &&
  isCholeskyDDValid 9 c.dS0 c.dR c.S0 c.R_S0 &&
  isCholeskyDDValid 8 c.dK c.dR c.S1 c.R_S1 &&
  isCholeskyDDLower c.m0 c.dM0 c.dR c.M0 c.R0 &&
  isCholeskyDDLower c.m1 c.dM1 c.dR c.M1 c.R1 &&
  isCholeskyDDLower c.m2 c.dM2 c.dR c.M2 c.R2 &&
  isCholeskyDDLower c.m3 c.dM3 c.dR c.M3 c.R3 &&
  isCholeskyDDLower c.m4 c.dM4 c.dR c.M4 c.R4 &&
  isCholeskyDDLower c.m5 c.dM5 c.dR c.M5 c.R5 &&
  isCholeskyDDLower c.m6 c.dM6 c.dR c.M6 c.R6 &&
  c.checkEq2 &&
  (sym3Canon (poly3Scale (-((c.sDen : ℤ) * (c.dS : ℤ))) c.polyG3) ==
    sym3Canon (poly3Scale (c.dK : ℤ) c.polyRHS3Canon))

/-! ## Soundness lemmas -/

private theorem evalPoly3_kernelChebPoly3 {k m : ℕ} (hm : m ≤ 9) (Fk : List (List ℤ)) (u v t : ℝ) :
    evalPoly3 (kernelChebPoly3 k m Fk) u v t =
      (∑ i : Fin m, ∑ j : Fin m,
        (matGet Fk i.val j.val : ℝ) * chebT i.val u * chebT j.val v) * bvQ k u v t := by
  unfold kernelChebPoly3
  rw [evalPoly3_mulPoly3Sorted, evalPoly3_bvQPoly3]
  congr 1
  have hinner : ∀ i : ℕ,
      evalPoly3 ((List.range m).foldl (fun qacc j =>
        mergePoly3 (poly3Scale (matGet Fk i j) (chebT3V j)) qacc) []) u v t =
      ∑ j : Fin m, (matGet Fk i j.val : ℝ) * chebT j.val v := by
    intro i
    have hfold : ∀ (l : List ℕ), (∀ j ∈ l, j < m) → ∀ (qacc : Poly3),
        evalPoly3 (l.foldl (fun qacc j =>
          mergePoly3 (poly3Scale (matGet Fk i j) (chebT3V j)) qacc) qacc) u v t =
        evalPoly3 qacc u v t +
        (l.map fun j => (matGet Fk i j : ℝ) * chebT j v).sum := by
      intro l
      induction l with
      | nil => intro _ qacc; simp
      | cons j js ih =>
        intro hl qacc
        have hj : j < m := hl j (List.mem_cons_self ..)
        have hj8 : j ≤ 8 := by omega
        have hjs : ∀ r ∈ js, r < m := fun r hr => hl r (List.mem_cons_of_mem j hr)
        simp only [List.foldl_cons, ih hjs, evalPoly3_mergePoly3, evalPoly3_scale,
          evalPoly3_chebT3V hj8, List.map_cons, List.sum_cons]
        ring
    rw [hfold (List.range m) (fun j hj => List.mem_range.mp hj) [], evalPoly3_nil, zero_add, Fin.sum_univ_def]
    congr 1; apply List.ext_getElem <;> simp
  have houter : ∀ (l : List ℕ), (∀ i ∈ l, i < m) → ∀ (acc : Poly3),
      evalPoly3 (l.foldl (fun acc i =>
        let ti := chebT3U i
        let qi := (List.range m).foldl (fun qacc j =>
          mergePoly3 (poly3Scale (matGet Fk i j) (chebT3V j)) qacc) []
        mergePoly3 (mulPoly3Sorted ti qi) acc) acc) u v t =
      evalPoly3 acc u v t +
      (l.map fun i => chebT i u * ∑ j : Fin m, (matGet Fk i j.val : ℝ) * chebT j.val v).sum := by
    intro l
    induction l with
    | nil => intro _ acc; simp
    | cons i is ih =>
      intro hl acc
      have hi : i < m := hl i (List.mem_cons_self ..)
      have hi8 : i ≤ 8 := by omega
      have his : ∀ r ∈ is, r < m := fun r hr => hl r (List.mem_cons_of_mem i hr)
      simp only [List.foldl_cons, ih his, evalPoly3_mergePoly3, evalPoly3_mulPoly3Sorted,
        evalPoly3_chebT3U hi8, hinner, List.map_cons, List.sum_cons]
      ring
  rw [houter (List.range m) (fun i hi => List.mem_range.mp hi) [], evalPoly3_nil, zero_add]
  have hmap : ((List.range m).map fun i => chebT i u * ∑ j : Fin m, (matGet Fk i j.val : ℝ) * chebT j.val v).sum =
      ∑ i : Fin m, chebT i.val u * ∑ j : Fin m, (matGet Fk i.val j.val : ℝ) * chebT j.val v := by
    rw [Fin.sum_univ_def]; congr 1; apply List.ext_getElem <;> simp
  rw [hmap]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

private theorem evalPoly3_polyG3 (c : BVCert8) (hdK : 0 < c.dK) (u v t : ℝ) :
    evalPoly3 c.polyG3 u v t = (c.dK : ℝ) * bvChebG3Unaug c.toRealF u v t := by
  have hdK_ne : (c.dK : ℝ) ≠ 0 := (Nat.cast_pos.mpr hdK).ne'
  have hblk : ∀ (k m : ℕ) (hm : m ≤ 9) (M : List (List ℤ)),
      evalPoly3 (kernelChebPoly3 k m M) u v t =
      (c.dK : ℝ) * ((∑ i : Fin m, ∑ j : Fin m,
        toRealMat m c.dK M i j * chebT i.val u * chebT j.val v) * bvQ k u v t) := by
    intro k m hm M
    rw [evalPoly3_kernelChebPoly3 hm M u v t]
    have hsum : ∑ i : Fin m, ∑ j : Fin m,
        (matGet M i.val j.val : ℝ) * chebT i.val u * chebT j.val v =
        (c.dK : ℝ) * ∑ i : Fin m, ∑ j : Fin m,
          toRealMat m c.dK M i j * chebT i.val u * chebT j.val v := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [toRealMat, Matrix.of_apply]
      field_simp [hdK_ne]
    rw [hsum]; ring
  unfold polyG3 bvChebG3Unaug
  simp only [evalPoly3_mergePoly3]
  have hfin9 : List.finRange 9 = [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
      ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩] := rfl
  rw [Fin.sum_univ_def, hfin9]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, toRealF]
  rw [hblk 0 9 (by omega) c.F0, hblk 1 8 (by omega) c.F1, hblk 2 7 (by omega) c.F2,
    hblk 3 6 (by omega) c.F3, hblk 4 5 (by omega) c.F4, hblk 5 4 (by omega) c.F5,
    hblk 6 3 (by omega) c.F6, hblk 7 2 (by omega) c.F7, hblk 8 1 (by omega) c.F8]
  ring

private theorem polyG2_len (c : BVCert8) : c.polyG2.length = 17 := by
  unfold polyG2; exact poly17Add_len _ _

private theorem evalPoly17_polyG2 (c : BVCert8) (hdK : 0 < c.dK) (t : ℝ) :
    evalPoly17 c.polyG2 t =
      32768 * (c.dK : ℝ) *
        (bvChebG2Unaug c.toRealF t + ∑ k : Fin 16, c.toRealC2 k * legendreP16 (k.val + 1) t) := by
  have hdK_ne : (c.dK : ℝ) ≠ 0 := (Nat.cast_pos.mpr hdK).ne'
  have hg2_fold : ∀ (l : List ℕ), (∀ k ∈ l, k < 16) →
      ∀ (acc : List ℤ), acc.length = 17 →
      evalPoly17 (l.foldl (fun acc k =>
        poly17Add acc (poly17Scale (c.c2.getD k 0) (legendreP16Int (k + 1)))) acc) t =
      evalPoly17 acc t +
        (l.map fun k => (c.c2.getD k 0 : ℝ) * (32768 * legendreP16 (k + 1) t)).sum := by
    intro l
    induction l with
    | nil => intro _ acc _; simp
    | cons a s ih =>
      intro hl acc hlen
      have ha : a < 16 := hl a (List.mem_cons_self ..)
      have hs : ∀ k ∈ s, k < 16 := fun k hk => hl k (List.mem_cons_of_mem a hk)
      rw [List.foldl_cons, ih hs _ (poly17Add_len _ _),
        evalPoly17_add hlen (poly17Scale_len _ _), evalPoly17_scale (legendreP16Int_len _),
        evalPoly17_legendreP16Int (by omega) (by omega), List.map_cons, List.sum_cons]
      ring
  have hg2_len : ((List.range 16).foldl (fun acc k =>
      poly17Add acc (poly17Scale (c.c2.getD k 0) (legendreP16Int (k + 1)))) poly17Zero).length = 17 := by
    have h : ∀ (l : List ℕ) (acc : List ℤ), acc.length = 17 →
        (l.foldl (fun acc k => poly17Add acc (poly17Scale (c.c2.getD k 0) (legendreP16Int (k + 1)))) acc).length = 17 := by
      intro l; induction l with
      | nil => intro acc hacc; exact hacc
      | cons _ _ ih => intro acc _; exact ih _ (poly17Add_len _ _)
    exact h _ _ poly17Zero_len
  have hg2_ev : evalPoly17 ((List.range 16).foldl (fun acc k =>
      poly17Add acc (poly17Scale (c.c2.getD k 0) (legendreP16Int (k + 1)))) poly17Zero) t =
      32768 * (c.dK : ℝ) * ∑ k : Fin 16, c.toRealC2 k * legendreP16 (k.val + 1) t := by
    rw [hg2_fold (List.range 16) (fun k hk => List.mem_range.mp hk) poly17Zero poly17Zero_len,
      evalPoly17_zero, zero_add]
    have hmap : ((List.range 16).map fun k => (c.c2.getD k 0 : ℝ) * (32768 * legendreP16 (k + 1) t)).sum =
        ∑ k : Fin 16, (c.c2.getD k.val 0 : ℝ) * (32768 * legendreP16 (k.val + 1) t) := by
      rw [Fin.sum_univ_def]; congr 1
    rw [hmap, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [toRealC2]
    field_simp [hdK_ne]
  have hmul_k : ∀ (k m : ℕ) (hk : k ≤ 8) (hm : m = 8 - k + 1) (M : List (List ℤ)),
      evalPoly17 (poly17Mul (quadCheb17 m M) (oneMinusT2Pow17 k)) t =
      (c.dK : ℝ) * ((∑ i : Fin m, ∑ j : Fin m,
        toRealMat m c.dK M i j * chebT i.val t * chebT j.val t) * (1 - t ^ 2) ^ k) := by
    intro k m hk hm M
    obtain ⟨hdeg, hev⟩ := quadCheb17_props (by omega : m ≤ 9) M
    rw [evalPoly17_mul_deg (2 * (m - 1)) (2 * k) hdeg
        (fun d hd => oneMinusT2Pow17_getD_zero hk hd) (by omega)
        (quadCheb17_len m M) (oneMinusT2Pow17_len k) t,
      hev t, evalPoly17_oneMinusT2Pow17 hk t]
    have hsum : ∑ i : Fin m, ∑ j : Fin m,
        (matGet M i.val j.val : ℝ) * chebT i.val t * chebT j.val t =
        (c.dK : ℝ) * ∑ i : Fin m, ∑ j : Fin m,
          toRealMat m c.dK M i j * chebT i.val t * chebT j.val t := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [toRealMat, Matrix.of_apply]
      field_simp [hdK_ne]
    rw [hsum]; ring
  have hlin0 : evalPoly17 (linearCheb17 9 c.F0) t =
      (c.dK : ℝ) * ∑ i : Fin 9, ∑ j : Fin 9, toRealMat 9 c.dK c.F0 i j * chebT i.val t := by
    rw [evalPoly17_linearCheb17 (by omega) c.F0 t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [toRealMat, Matrix.of_apply]
    field_simp [hdK_ne]
  have hfin9 : List.finRange 9 = [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
      ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩] := rfl
  unfold polyG2 bvChebG2Unaug
  rw [evalPoly17_add (poly17Scale_len _ _) hg2_len, hg2_ev,
    evalPoly17_scale (poly17Add_len _ _),
    evalPoly17_add (poly17Scale_len _ _) (poly17Add_len _ _),
    evalPoly17_scale (linearCheb17_len _ _), hlin0,
    evalPoly17_add (poly17Mul_len _ _) (poly17Add_len _ _),
    evalPoly17_add (poly17Mul_len _ _) (poly17Add_len _ _),
    evalPoly17_add (poly17Mul_len _ _) (poly17Add_len _ _),
    evalPoly17_add (poly17Mul_len _ _) (poly17Add_len _ _),
    evalPoly17_add (poly17Mul_len _ _) (poly17Add_len _ _),
    evalPoly17_add (poly17Mul_len _ _) (poly17Add_len _ _),
    evalPoly17_add (poly17Mul_len _ _) (poly17Add_len _ _),
    evalPoly17_add (poly17Mul_len _ _) (poly17Mul_len _ _),
    hmul_k 0 9 (by omega) rfl c.F0, hmul_k 1 8 (by omega) rfl c.F1,
    hmul_k 2 7 (by omega) rfl c.F2, hmul_k 3 6 (by omega) rfl c.F3,
    hmul_k 4 5 (by omega) rfl c.F4, hmul_k 5 4 (by omega) rfl c.F5,
    hmul_k 6 3 (by omega) rfl c.F6, hmul_k 7 2 (by omega) rfl c.F7,
    hmul_k 8 1 (by omega) rfl c.F8]
  have hsum_k : (∑ k : Fin 9, (∑ i : Fin (8 - k.val + 1), ∑ j : Fin (8 - k.val + 1),
      c.toRealF k i j * chebT i.val t * chebT j.val t) * (1 - t ^ 2) ^ k.val) =
      (∑ i : Fin 9, ∑ j : Fin 9, toRealMat 9 c.dK c.F0 i j * chebT i.val t * chebT j.val t) * (1 - t ^ 2) ^ 0 +
      (∑ i : Fin 8, ∑ j : Fin 8, toRealMat 8 c.dK c.F1 i j * chebT i.val t * chebT j.val t) * (1 - t ^ 2) ^ 1 +
      (∑ i : Fin 7, ∑ j : Fin 7, toRealMat 7 c.dK c.F2 i j * chebT i.val t * chebT j.val t) * (1 - t ^ 2) ^ 2 +
      (∑ i : Fin 6, ∑ j : Fin 6, toRealMat 6 c.dK c.F3 i j * chebT i.val t * chebT j.val t) * (1 - t ^ 2) ^ 3 +
      (∑ i : Fin 5, ∑ j : Fin 5, toRealMat 5 c.dK c.F4 i j * chebT i.val t * chebT j.val t) * (1 - t ^ 2) ^ 4 +
      (∑ i : Fin 4, ∑ j : Fin 4, toRealMat 4 c.dK c.F5 i j * chebT i.val t * chebT j.val t) * (1 - t ^ 2) ^ 5 +
      (∑ i : Fin 3, ∑ j : Fin 3, toRealMat 3 c.dK c.F6 i j * chebT i.val t * chebT j.val t) * (1 - t ^ 2) ^ 6 +
      (∑ i : Fin 2, ∑ j : Fin 2, toRealMat 2 c.dK c.F7 i j * chebT i.val t * chebT j.val t) * (1 - t ^ 2) ^ 7 +
      (∑ i : Fin 1, ∑ j : Fin 1, toRealMat 1 c.dK c.F8 i j * chebT i.val t * chebT j.val t) * (1 - t ^ 2) ^ 8 := by
    rw [Fin.sum_univ_def, hfin9]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, toRealF]
    ring
  rw [hsum_k]
  dsimp only [toRealF]
  push_cast
  ring

private theorem bound_eq_sum (c : BVCert8) (hdK : 0 < c.dK) :
    c.bound = 1 + (∑ i : Fin 9, ∑ j : Fin 9, c.toRealF ⟨0, by omega⟩ i j) +
      ∑ k : Fin 16, c.toRealC2 k := by
  have hdK_ne : (c.dK : ℝ) ≠ 0 := (Nat.cast_pos.mpr hdK).ne'
  have hF0 : ((List.range 9).foldl (fun acc i =>
      acc + (List.range 9).foldl (fun acc2 j => acc2 + matGet c.F0 i j) 0) 0 : ℤ) =
      ∑ i : Fin 9, ∑ j : Fin 9, matGet c.F0 i.val j.val := by
    rw [foldl_add_int17, zero_add, sum_range_int17]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [foldl_add_int17, zero_add, sum_range_int17]
  have hc2 : ((List.range 16).foldl (fun acc k => acc + c.c2.getD k 0) 0 : ℤ) =
      ∑ k : Fin 16, c.c2.getD k.val 0 := by
    rw [foldl_add_int17, zero_add, sum_range_int17]
  unfold bound boundNum
  rw [hF0, hc2]
  have hsumF : (∑ i : Fin 9, ∑ j : Fin 9, c.toRealF ⟨0, by omega⟩ i j) =
      (∑ i : Fin 9, ∑ j : Fin 9, (matGet c.F0 i.val j.val : ℝ)) / (c.dK : ℝ) := by
    simp only [toRealF, toRealMat, Matrix.of_apply, Finset.sum_div]
  have hsumC : (∑ k : Fin 16, c.toRealC2 k) =
      (∑ k : Fin 16, (c.c2.getD k.val 0 : ℝ)) / (c.dK : ℝ) := by
    simp only [toRealC2, Finset.sum_div]
  rw [hsumF, hsumC]
  push_cast
  field_simp [hdK_ne]

private theorem isCholeskyDDLower_dims {m dM dR : ℕ} {M L : List (List ℤ)}
    (h : isCholeskyDDLower m dM dR M L = true) :
    M.length = m ∧ (∀ r ∈ M, r.length = m) := by
  unfold isCholeskyDDLower at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hLlen⟩, _⟩, _⟩, hMlen⟩, hrows⟩ := h
  refine ⟨hMlen, ?_⟩
  have haux : ∀ (i : ℕ) (ms ls : List (List ℤ)),
      ms.length = ls.length →
      choleskyCheckRows m ((dR : ℤ) * (dR : ℤ)) (dM : ℤ) L i ms ls = true →
      ∀ r ∈ ms, r.length = m := by
    intro i ms ls hlen hchk
    induction ms generalizing i ls with
    | nil => intro r hr; cases hr
    | cons mRow mRest ih =>
      cases ls with
      | nil => simp at hlen
      | cons lRow lRest =>
        unfold choleskyCheckRows at hchk
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact hchk.1.1
        · exact ih (i + 1) lRest (by simp at hlen; omega) hchk.2 r hr'
  exact haux 0 M L (by omega) hrows

set_option maxHeartbeats 1200000 in
/-- **Soundness of `BVCert8`**: any certificate with `c.isValid = true` unconditionally
certifies `(n : ℝ) ≤ c.bound` for every `(n, c.s)`-spherical code on `S²`. -/
theorem sound (c : BVCert8) (hvalid : c.isValid = true)
    {n : ℕ} {p : Fin n → UnitSphere} (hp : IsSphericalCode p c.s) :
    (n : ℝ) ≤ c.bound := by
  simp only [isValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at hvalid
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsDen, hdK⟩, hdS0⟩, hdS⟩, hdR⟩, _hsGt⟩,
    hc2_nn⟩, hsc0⟩, hsc1⟩, hsc2⟩, hsc3⟩, hsc4⟩, hsc5⟩, hsc6⟩,
    hb0⟩, hb1⟩, hb2⟩, hb3⟩, hb4⟩, hb5⟩, hb6⟩,
    hF0⟩, hF1⟩, hF2⟩, hF3⟩, hF4⟩, hF5⟩, hF6⟩, hF7⟩, hF8⟩,
    hS0⟩, hS1⟩,
    hM0⟩, hM1⟩, hM2⟩, hM3⟩, hM4⟩, hM5⟩, hM6⟩, heq2⟩, heq3⟩ := hvalid
  have hsDen_pos : (0 : ℝ) < (c.sDen : ℝ) := Nat.cast_pos.mpr hsDen
  have hdK_pos : (0 : ℝ) < (c.dK : ℝ) := Nat.cast_pos.mpr hdK
  have hdS0_pos : (0 : ℝ) < (c.dS0 : ℝ) := Nat.cast_pos.mpr hdS0
  have hdS_pos : (0 : ℝ) < (c.dS : ℝ) := Nat.cast_pos.mpr hdS
  have hdM_pos : ∀ {dM sc : ℕ}, dM * sc = c.dS → 0 < dM := by
    intro dM sc hmul
    by_contra h
    have h0 : dM = 0 := by omega
    rw [h0, zero_mul] at hmul
    omega
  have hdM0 : 0 < c.dM0 := hdM_pos hsc0
  have hdM1 : 0 < c.dM1 := hdM_pos hsc1
  have hdM2 : 0 < c.dM2 := hdM_pos hsc2
  have hdM3 : 0 < c.dM3 := hdM_pos hsc3
  have hdM4 : 0 < c.dM4 := hdM_pos hsc4
  have hdM5 : 0 < c.dM5 := hdM_pos hsc5
  have hdM6 : 0 < c.dM6 := hdM_pos hsc6
  have hF : ∀ k : Fin 9, (c.toRealF k).PosSemidef := fun k => by
    fin_cases k
    · exact isCholeskyDDValid_sound hF0
    · exact isCholeskyDDValid_sound hF1
    · exact isCholeskyDDValid_sound hF2
    · exact isCholeskyDDValid_sound hF3
    · exact isCholeskyDDValid_sound hF4
    · exact isCholeskyDDValid_sound hF5
    · exact isCholeskyDDValid_sound hF6
    · exact isCholeskyDDValid_sound hF7
    · exact isCholeskyDDValid_sound hF8
  have hc2 : ∀ k : Fin 16, 0 ≤ c.toRealC2 k := fun k =>
    div_nonneg (by exact_mod_cast (hc2_nn k.val k.isLt)) hdK_pos.le
  have hS0_psd : (toRealMat 9 c.dS0 c.S0).PosSemidef := isCholeskyDDValid_sound hS0
  have hS1_psd : (toRealMat 8 c.dK c.S1).PosSemidef := isCholeskyDDValid_sound hS1
  -- Univariate inequality h2
  have h2 : ∀ t : ℝ, -1 ≤ t → t ≤ c.s →
      bvChebG2Unaug c.toRealF t + ∑ k : Fin 16, c.toRealC2 k * legendreP16 (k.val + 1) t ≤ -1 := by
    intro t ht_lo ht_hi
    unfold checkEq2 at heq2
    simp only [beq_iff_eq] at heq2
    have hev := congrArg (fun q => evalPoly17 q t) heq2
    have hconst_len : ([-32768 * (c.dK : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).length = 17 := rfl
    have hconst_ev : evalPoly17 [-32768 * (c.dK : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] t =
        -32768 * (c.dK : ℝ) := by
      rw [evalPoly17, hconst_len, range_17_eq]
      simp [List.foldl]
    have hg1_len : (poly17G1 c.sNum c.sDen).length = 17 := rfl
    have hg1_deg : ∀ d, 2 < d → (poly17G1 c.sNum c.sDen).getD d 0 = 0 := by
      intro d hd
      by_cases h17 : d < 17
      · interval_cases d <;> rfl
      · exact list_getD_of_le_len _ _ _ (by rw [hg1_len]; omega)
    have hg1_ev : evalPoly17 (poly17G1 c.sNum c.sDen) t = (c.sDen : ℝ) * (c.s - t) * (t + 1) := by
      rw [evalPoly17, hg1_len, range_17_eq]
      simp only [poly17G1, s, List.foldl_cons, List.foldl_nil, List.getD_cons_zero,
        List.getD_cons_succ, Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_zero,
        pow_zero, pow_one, mul_one, zero_mul, add_zero, zero_add]
      field_simp [hsDen_pos.ne']; ring
    obtain ⟨_, hS0_ev⟩ := quadCheb17_props (by omega : 9 ≤ 9) c.S0
    obtain ⟨hS1_deg, hS1_ev⟩ := quadCheb17_props (by omega : 8 ≤ 9) c.S1
    rw [evalPoly17_scale (poly17Add_len _ _), evalPoly17_add hconst_len (poly17Scale_len _ _),
      hconst_ev, evalPoly17_scale (polyG2_len c), evalPoly17_polyG2 c hdK t,
      evalPoly17_add (poly17Scale_len _ _) (poly17Scale_len _ _),
      evalPoly17_scale (quadCheb17_len 9 c.S0), hS0_ev t,
      evalPoly17_scale (poly17Mul_len _ _),
      evalPoly17_mul_deg 2 14 hg1_deg hS1_deg (by omega) hg1_len (quadCheb17_len 8 c.S1) t,
      hg1_ev, hS1_ev t] at hev
    have hq0_nn : 0 ≤ ∑ i : Fin 9, ∑ j : Fin 9, (matGet c.S0 i.val j.val : ℝ) * chebT i.val t * chebT j.val t := by
      have h := posSemidef_quad_nonneg hS0_psd (fun i : Fin 9 => chebT i.val t)
      have hmul : (c.dS0 : ℝ) * (∑ a : Fin 9, ∑ b : Fin 9, chebT a.val t * toRealMat 9 c.dS0 c.S0 a b * chebT b.val t) =
          ∑ i : Fin 9, ∑ j : Fin 9, (matGet c.S0 i.val j.val : ℝ) * chebT i.val t * chebT j.val t := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
        simp only [toRealMat, Matrix.of_apply]; field_simp [hdS0_pos.ne']
      nlinarith [mul_nonneg hdS0_pos.le h]
    have hq1_nn : 0 ≤ ∑ i : Fin 8, ∑ j : Fin 8, (matGet c.S1 i.val j.val : ℝ) * chebT i.val t * chebT j.val t := by
      have h := posSemidef_quad_nonneg hS1_psd (fun i : Fin 8 => chebT i.val t)
      have hmul : (c.dK : ℝ) * (∑ a : Fin 8, ∑ b : Fin 8, chebT a.val t * toRealMat 8 c.dK c.S1 a b * chebT b.val t) =
          ∑ i : Fin 8, ∑ j : Fin 8, (matGet c.S1 i.val j.val : ℝ) * chebT i.val t * chebT j.val t := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
        simp only [toRealMat, Matrix.of_apply]; field_simp [hdK_pos.ne']
      nlinarith [mul_nonneg hdK_pos.le h]
    have hfac_nn : 0 ≤ (c.sDen : ℝ) * (c.s - t) * (t + 1) := by
      have h1 : 0 ≤ c.s - t := by linarith
      have h2' : 0 ≤ t + 1 := by linarith
      positivity
    have hrhs_nn : 0 ≤ ((32768 * (c.sDen : ℤ) * (c.dK : ℤ) : ℤ) : ℝ) *
        (∑ i : Fin 9, ∑ j : Fin 9, (matGet c.S0 i.val j.val : ℝ) * chebT i.val t * chebT j.val t) +
        ((32768 * (c.dS0 : ℤ) : ℤ) : ℝ) *
        ((c.sDen : ℝ) * (c.s - t) * (t + 1) *
          ∑ i : Fin 8, ∑ j : Fin 8, (matGet c.S1 i.val j.val : ℝ) * chebT i.val t * chebT j.val t) := by
      push_cast; positivity
    have hlhs_nn : 0 ≤ ((c.sDen : ℝ) * (c.dS0 : ℝ)) *
        (-32768 * (c.dK : ℝ) + (-1 : ℝ) * (32768 * (c.dK : ℝ) *
          (bvChebG2Unaug c.toRealF t + ∑ k : Fin 16, c.toRealC2 k * legendreP16 (k.val + 1) t))) := by
      have hcast : (((c.sDen : ℤ) * (c.dS0 : ℤ) : ℤ) : ℝ) = (c.sDen : ℝ) * (c.dS0 : ℝ) := by push_cast; rfl
      rw [← hcast]
      have hneg1 : ((-1 : ℤ) : ℝ) = (-1 : ℝ) := by norm_num
      rw [← hneg1]
      exact hrhs_nn.trans_eq hev.symm
    have hcoeff_pos : (0 : ℝ) < 32768 * (c.sDen : ℝ) * (c.dS0 : ℝ) * (c.dK : ℝ) := by positivity
    nlinarith
  -- Trivariate inequality h3
  have h3 : ∀ u v t : ℝ, InThreePointDomain c.s u v t → sym3 (bvChebG3Unaug c.toRealF) u v t ≤ 0 := by
    intro u v t hdom
    have hsym_eq := congrArg (fun q => sym3 (evalPoly3 q) u v t) heq3
    simp only [sym3_evalPoly3_sym3Canon] at hsym_eq
    have hlhs_eval : sym3 (evalPoly3 (poly3Scale (-((c.sDen : ℤ) * (c.dS : ℤ))) c.polyG3)) u v t =
        -((c.sDen : ℝ) * (c.dS : ℝ) * (c.dK : ℝ)) * sym3 (bvChebG3Unaug c.toRealF) u v t := by
      have hf : evalPoly3 (poly3Scale (-((c.sDen : ℤ) * (c.dS : ℤ))) c.polyG3) =
          fun a b d => -((c.sDen : ℝ) * (c.dS : ℝ) * (c.dK : ℝ)) * bvChebG3Unaug c.toRealF a b d := by
        ext a b d
        rw [evalPoly3_scale, evalPoly3_polyG3 c hdK a b d]
        push_cast; ring
      rw [hf]; unfold sym3; ring
    have hrhs_nn : 0 ≤ sym3 (evalPoly3 (poly3Scale (c.dK : ℤ) c.polyRHS3Canon)) u v t := by
      have hscale_rhs : sym3 (evalPoly3 (poly3Scale (c.dK : ℤ) c.polyRHS3Canon)) u v t =
          (c.dK : ℝ) * sym3 (evalPoly3 c.polyRHS3Canon) u v t := by
        have hf : evalPoly3 (poly3Scale (c.dK : ℤ) c.polyRHS3Canon) =
            fun a b d => (c.dK : ℝ) * evalPoly3 c.polyRHS3Canon a b d := by
          ext a b d; exact evalPoly3_scale _ _ a b d
        rw [hf]; unfold sym3; ring
      rw [hscale_rhs]
      refine mul_nonneg hdK_pos.le ?_
      have hswap12 : ∀ a b d, InThreePointDomain c.s a b d → InThreePointDomain c.s b a d := by
        intro a b d hd
        refine ⟨hd.2.2.1, hd.2.2.2.1, hd.1, hd.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, ?_⟩
        have := hd.2.2.2.2.2.2; unfold gramDet3 at this ⊢; linarith
      have hswap23 : ∀ a b d, InThreePointDomain c.s a b d → InThreePointDomain c.s a d b := by
        intro a b d hd
        refine ⟨hd.1, hd.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.1, hd.2.2.2.1, ?_⟩
        have := hd.2.2.2.2.2.2; unfold gramDet3 at this ⊢; linarith
      have hsym_nn : ∀ (f : ℝ → ℝ → ℝ → ℝ),
          (∀ a b d, InThreePointDomain c.s a b d → 0 ≤ f a b d) →
          0 ≤ sym3 f u v t := by
        intro f hf; unfold sym3
        have h1 := hf u v t hdom
        have h2' := hf u t v (hswap23 _ _ _ hdom)
        have h3' := hf v u t (hswap12 _ _ _ hdom)
        have h4 := hf v t u (hswap23 _ _ _ (hswap12 _ _ _ hdom))
        have h5 := hf t u v (hswap12 _ _ _ (hswap23 _ _ _ hdom))
        have h6 := hf t v u (hswap23 _ _ _ (hswap12 _ _ _ (hswap23 _ _ _ hdom)))
        linarith
      have hterm_nn : ∀ (p : Poly3),
          (∀ a b d, InThreePointDomain c.s a b d → 0 ≤ evalPoly3 p a b d) →
          0 ≤ sym3 (evalPoly3 (sym3Canon p)) u v t := by
        intro p hp'; rw [sym3_evalPoly3_sym3Canon]; exact hsym_nn (evalPoly3 p) hp'
      have hDelta_nn : ∀ a b d, InThreePointDomain c.s a b d → 0 ≤ evalPoly3 polyDelta8 a b d := by
        intro a b d hd
        have hev : evalPoly3 polyDelta8 a b d = gramDet3 a b d := by
          simp [polyDelta8, evalPoly3, gramDet3]; ring
        rw [hev]; exact hd.2.2.2.2.2.2
      have hg1_nn : ∀ a b d, InThreePointDomain c.s a b d → 0 ≤ evalPoly3 (polyG1_8 c.sNum c.sDen) a b d := by
        intro a b d hd
        have hev : evalPoly3 (polyG1_8 c.sNum c.sDen) a b d = (c.sDen : ℝ) * (c.s - a) * (a + 1) := by
          simp only [polyG1_8, evalPoly3, List.foldl_cons, List.foldl_nil, s,
            Int.cast_sub, Int.cast_neg, Int.cast_natCast, pow_zero, pow_one, mul_one, zero_add]
          field_simp [hsDen_pos.ne']; ring
        rw [hev]
        have h1 : 0 ≤ c.s - a := by linarith [hd.2.1]
        have h2' : 0 ≤ a + 1 := by linarith [hd.1]
        positivity
      have hadd : ∀ p q : Poly3, sym3 (evalPoly3 (p ++ q)) u v t =
          sym3 (evalPoly3 p) u v t + sym3 (evalPoly3 q) u v t := by
        intro p q
        have hf : evalPoly3 (p ++ q) = fun a b d => evalPoly3 p a b d + evalPoly3 q a b d := by
          ext a b d; exact evalPoly3_append p q a b d
        rw [hf]; unfold sym3; ring
      have hsc : ∀ (k : ℤ) (p : Poly3), sym3 (evalPoly3 (poly3Scale k p)) u v t =
          (k : ℝ) * sym3 (evalPoly3 p) u v t := by
        intro k p
        have hf : evalPoly3 (poly3Scale k p) = fun a b d => (k : ℝ) * evalPoly3 p a b d := by
          ext a b d; exact evalPoly3_scale k p a b d
        rw [hf]; unfold sym3; ring
      unfold polyRHS3Canon
      rw [sym3_evalPoly3_sym3Canon]
      repeat rw [hadd]
      repeat rw [hsc]
      have hq0 := hterm_nn _ (fun a b d _ =>
        evalPoly3_quadPoly3Fast_nonneg hdM0 (isCholeskyDDLower_sound hM0) c.b0
          (isCholeskyDDLower_dims hM0).1 hb0 (isCholeskyDDLower_dims hM0).2 a b d)
      have hq1 := hterm_nn _ (fun a b d _ =>
        evalPoly3_quadPoly3Fast_nonneg hdM1 (isCholeskyDDLower_sound hM1) c.b1
          (isCholeskyDDLower_dims hM1).1 hb1 (isCholeskyDDLower_dims hM1).2 a b d)
      have hq2 := hterm_nn _ (fun a b d _ =>
        evalPoly3_quadPoly3Fast_nonneg hdM2 (isCholeskyDDLower_sound hM2) c.b2
          (isCholeskyDDLower_dims hM2).1 hb2 (isCholeskyDDLower_dims hM2).2 a b d)
      have hq3 := hterm_nn _ (fun a b d hd => by
        rw [evalPoly3_mulPoly3Sorted]
        exact mul_nonneg (hDelta_nn a b d hd)
          (evalPoly3_quadPoly3Fast_nonneg hdM3 (isCholeskyDDLower_sound hM3) c.b3
            (isCholeskyDDLower_dims hM3).1 hb3 (isCholeskyDDLower_dims hM3).2 a b d))
      have hq4 := hterm_nn _ (fun a b d hd => by
        rw [evalPoly3_mulPoly3Sorted]
        exact mul_nonneg (hDelta_nn a b d hd)
          (evalPoly3_quadPoly3Fast_nonneg hdM4 (isCholeskyDDLower_sound hM4) c.b4
            (isCholeskyDDLower_dims hM4).1 hb4 (isCholeskyDDLower_dims hM4).2 a b d))
      have hq5 := hterm_nn _ (fun a b d hd => by
        rw [evalPoly3_mulPoly3Sorted]
        exact mul_nonneg (hDelta_nn a b d hd)
          (evalPoly3_quadPoly3Fast_nonneg hdM5 (isCholeskyDDLower_sound hM5) c.b5
            (isCholeskyDDLower_dims hM5).1 hb5 (isCholeskyDDLower_dims hM5).2 a b d))
      have hq6 := hterm_nn _ (fun a b d hd => by
        rw [evalPoly3_mulPoly3Sorted]
        exact mul_nonneg (hg1_nn a b d hd)
          (evalPoly3_quadPoly3Fast_nonneg hdM6 (isCholeskyDDLower_sound hM6) c.b6
            (isCholeskyDDLower_dims hM6).1 hb6 (isCholeskyDDLower_dims hM6).2 a b d))
      push_cast
      have hsD_nn : (0 : ℝ) ≤ (c.sDen : ℝ) := by positivity
      have h0 : (0 : ℝ) ≤ (c.sDen : ℝ) * (c.sc0 : ℝ) * sym3 (evalPoly3 (sym3Canon (quadPoly3Fast c.M0 c.b0))) u v t := by positivity
      have h1 : (0 : ℝ) ≤ (c.sDen : ℝ) * (c.sc1 : ℝ) * sym3 (evalPoly3 (sym3Canon (quadPoly3Fast c.M1 c.b1))) u v t := by positivity
      have h2' : (0 : ℝ) ≤ (c.sDen : ℝ) * (c.sc2 : ℝ) * sym3 (evalPoly3 (sym3Canon (quadPoly3Fast c.M2 c.b2))) u v t := by positivity
      have h3' : (0 : ℝ) ≤ (c.sDen : ℝ) * (c.sc3 : ℝ) * sym3 (evalPoly3 (sym3Canon (mulPoly3Sorted polyDelta8 (quadPoly3Fast c.M3 c.b3)))) u v t := by positivity
      have h4 : (0 : ℝ) ≤ (c.sDen : ℝ) * (c.sc4 : ℝ) * sym3 (evalPoly3 (sym3Canon (mulPoly3Sorted polyDelta8 (quadPoly3Fast c.M4 c.b4)))) u v t := by positivity
      have h5 : (0 : ℝ) ≤ (c.sDen : ℝ) * (c.sc5 : ℝ) * sym3 (evalPoly3 (sym3Canon (mulPoly3Sorted polyDelta8 (quadPoly3Fast c.M5 c.b5)))) u v t := by positivity
      have h6 : (0 : ℝ) ≤ (c.sc6 : ℝ) * sym3 (evalPoly3 (sym3Canon (mulPoly3Sorted (polyG1_8 c.sNum c.sDen) (quadPoly3Fast c.M6 c.b6)))) u v t := by positivity
      linarith
    have hcoeff_pos : (0 : ℝ) < (c.sDen : ℝ) * (c.dS : ℝ) * (c.dK : ℝ) := by positivity
    rw [hlhs_eval] at hsym_eq
    nlinarith
  have hbound := bachocVallentin_cheb_bound_with_legendre16 c.toRealF hF c.toRealC2 hc2 h2 h3 hp
  rw [bound_eq_sum c hdK]
  exact hbound

end BVCert8

end Geodesy.Spherical
