import LeanGeodesy.Spherical.BachocVallentinCert
import LeanGeodesy.Spherical.Legendre12

/-!
# Exact rational degree-6 Bachoc–Vallentin + Legendre (`P₁..P₁₂`) SDP certificate verifier

This module generalizes `BVCert5` minimally to degree `d₃ = 6` with two-point
Legendre polynomial terms `P₁, …, P₁₂` (`d₂ = 12`), reusing `isCholeskyDDValid`,
`Poly3`, `mergePoly3`, `mulPoly3Sorted`, `quadPoly3`, `sym3Canon`, and `bvQPoly3`
from `BachocVallentinCert.lean` together with `bachocVallentin_bound_with_legendre`
from `Legendre12.lean`.

Key design choices for fast Lean 4 kernel verification (no `native_decide`):
- All 12 Legendre polynomials `P₁..P₁₂` have denominators dividing `1024`, so
  `1024 * P_k(t)` is an exact integer polynomial (`legendreP12Int`).
- The 10 trivariate SOS bases `b0..b9 : List Poly3` are stored pre-expanded in
  the certificate; `evalPoly3_quadPoly3_nonneg` is valid for any `List Poly3`.
- Soundness (`BVCert6.sound`) certifies `(n : ℝ) ≤ (cert.boundNum : ℝ) / (cert.dK : ℝ)`
  for every `(n, cert.s)`-spherical code on `S²`.
-/

namespace Geodesy.Spherical

open scoped BigOperators Matrix

/-! ## Univariate degree-12 integer polynomials (scaled by `1024` for `P₁..P₁₂`) -/

/-- Evaluate a univariate integer polynomial `List ℤ` (ascending powers of `t`) at `t : ℝ`. -/
def evalPoly13 (p : List ℤ) (t : ℝ) : ℝ :=
  (List.range p.length).foldl (fun acc d => acc + (p.getD d 0 : ℝ) * t ^ d) 0

private theorem range_13_eq : List.range 13 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] := by
  decide

private theorem evalPoly13_eq_sum (p : List ℤ) (t : ℝ) :
    evalPoly13 p t = ∑ d : Fin p.length, (p.getD d.val 0 : ℝ) * t ^ d.val := by
  unfold evalPoly13
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

private theorem evalPoly13_len13 {p : List ℤ} (h : p.length = 13) (t : ℝ) :
    evalPoly13 p t = ∑ d : Fin 13, (p.getD d.val 0 : ℝ) * t ^ d.val := by
  rw [evalPoly13_eq_sum]
  refine Finset.sum_bij (fun d _ => ⟨d.val, by omega⟩) (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ hab => Fin.ext (by simpa using congrArg Fin.val hab))
    (fun b _ => ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun _ _ => rfl)

/-- Pad or truncate a `List ℤ` to length 13. -/
def pad13 (p : List ℤ) : List ℤ :=
  (List.range 13).map fun d => p.getD d 0

def poly13Add (p q : List ℤ) : List ℤ :=
  (List.range 13).map fun d => p.getD d 0 + q.getD d 0

def poly13Scale (c : ℤ) (p : List ℤ) : List ℤ :=
  (List.range 13).map fun d => c * p.getD d 0

def poly13Mul (p q : List ℤ) : List ℤ :=
  (List.range 13).map fun d =>
    (List.range (d + 1)).foldl (fun acc i => acc + p.getD i 0 * q.getD (d - i) 0) 0

private theorem poly13Add_len (p q : List ℤ) : (poly13Add p q).length = 13 := by simp [poly13Add]
private theorem poly13Scale_len (c : ℤ) (p : List ℤ) : (poly13Scale c p).length = 13 := by simp [poly13Scale]
private theorem poly13Mul_len (p q : List ℤ) : (poly13Mul p q).length = 13 := by simp [poly13Mul]

private theorem evalPoly13_add {p q : List ℤ} (hp : p.length = 13) (hq : q.length = 13) (t : ℝ) :
    evalPoly13 (poly13Add p q) t = evalPoly13 p t + evalPoly13 q t := by
  rw [evalPoly13_len13 (poly13Add_len p q), evalPoly13_len13 hp, evalPoly13_len13 hq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [poly13Add, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range d.isLt, Option.map_some, Option.getD_some, Int.cast_add]
  ring

private theorem evalPoly13_scale {p : List ℤ} (hp : p.length = 13) (c : ℤ) (t : ℝ) :
    evalPoly13 (poly13Scale c p) t = (c : ℝ) * evalPoly13 p t := by
  rw [evalPoly13_len13 (poly13Scale_len c p), evalPoly13_len13 hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [poly13Scale, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range d.isLt, Option.map_some, Option.getD_some, Int.cast_mul]
  ring

/-- Quadratic form `∑ i < m, ∑ j < m, M[i][j] * t^(i + j)` as a length-13 `List ℤ` (for `m ≤ 7`). -/
def quadPoly13 (m : ℕ) (M : List (List ℤ)) : List ℤ :=
  (List.range 13).map fun d =>
    (List.range m).foldl (fun acc i =>
      if i ≤ d ∧ d - i < m then acc + matGet M i (d - i) else acc) 0

private theorem quadPoly13_len (m : ℕ) (M : List (List ℤ)) : (quadPoly13 m M).length = 13 := by
  simp [quadPoly13]

private theorem foldl_add_int (l : List ℕ) (f : ℕ → ℤ) (init : ℤ) :
    l.foldl (fun acc x => acc + f x) init = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a s ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; ring

private theorem sum_range_int {m : ℕ} (f : ℕ → ℤ) :
    ((List.range m).map f).sum = ∑ k : Fin m, f k.val := by
  rw [Fin.sum_univ_def]
  congr 1
  apply List.ext_getElem <;> simp

private theorem evalPoly13_quadPoly13 {m : ℕ} (hm : m ≤ 7) (M : List (List ℤ)) (t : ℝ) :
    evalPoly13 (quadPoly13 m M) t =
      ∑ i : Fin m, ∑ j : Fin m, (matGet M i.val j.val : ℝ) * t ^ (i.val + j.val) := by
  rw [evalPoly13_len13 (quadPoly13_len m M)]
  have hget : ∀ k : Fin 13, ((quadPoly13 m M).getD k.val 0 : ℝ) =
      ∑ i : Fin m, ∑ j : Fin m, if i.val + j.val = k.val then (matGet M i.val j.val : ℝ) else 0 := by
    intro k
    simp only [quadPoly13, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range k.isLt, Option.map_some, Option.getD_some]
    have hfold : (List.range m).foldl (fun acc i =>
        if i ≤ k.val ∧ k.val - i < m then acc + matGet M i (k.val - i) else acc) 0 =
        (List.range m).foldl (fun acc i =>
          acc + if i ≤ k.val ∧ k.val - i < m then matGet M i (k.val - i) else 0) 0 := by
      congr 1; ext acc i; split_ifs <;> omega
    rw [hfold, foldl_add_int, zero_add, sum_range_int]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hcond : i.val ≤ k.val ∧ k.val - i.val < m
    · simp only [hcond]
      let j0 : Fin m := ⟨k.val - i.val, hcond.2⟩
      rw [Finset.sum_eq_single j0]
      · have hj0 : i.val + j0.val = k.val := by simp [j0]; omega
        simp [hj0, j0]
      · intro j _ hne
        have : i.val + j.val ≠ k.val := fun heq => hne (by ext; simp [j0]; omega)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ j0) h
    · simp only [hcond, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have : i.val + j.val ≠ k.val := fun heq => hcond ⟨by omega, by omega⟩
      simp [this]
  simp_rw [hget, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  let k0 : Fin 13 := ⟨i.val + j.val, by omega⟩
  rw [Finset.sum_eq_single k0]
  · simp [k0]
  · intro k _ hne
    have : i.val + j.val ≠ k.val := fun heq => hne (Fin.ext heq.symm)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ k0) h

/-- Polynomial `(1 - t²) ^ k` as a length-13 `List ℤ` (for `k ≤ 6`). -/
def oneMinusT2Pow13 : ℕ → List ℤ
  | 0 => [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => [1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => [1, 0, -2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
  | 3 => [1, 0, -3, 0, 3, 0, -1, 0, 0, 0, 0, 0, 0]
  | 4 => [1, 0, -4, 0, 6, 0, -4, 0, 1, 0, 0, 0, 0]
  | 5 => [1, 0, -5, 0, 10, 0, -10, 0, 5, 0, -1, 0, 0]
  | 6 => [1, 0, -6, 0, 15, 0, -20, 0, 15, 0, -6, 0, 1]
  | _ => List.replicate 13 0

private theorem evalPoly13_oneMinusT2Pow13 {k : ℕ} (hk : k ≤ 6) (t : ℝ) :
    evalPoly13 (oneMinusT2Pow13 k) t = (1 - t ^ 2) ^ k := by
  interval_cases k <;>
    simp [oneMinusT2Pow13, evalPoly13, range_13_eq] <;> ring

/-- Exact integer polynomials `1024 * P_k(t)` for `1 ≤ k ≤ 12` (as length-13 `List ℤ`). -/
def legendreP12Int : ℕ → List ℤ
  | 1 => [0, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 2 => [-512, 0, 1536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 3 => [0, -1536, 0, 2560, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 4 => [384, 0, -3840, 0, 4480, 0, 0, 0, 0, 0, 0, 0, 0]
  | 5 => [0, 1920, 0, -8960, 0, 8064, 0, 0, 0, 0, 0, 0, 0]
  | 6 => [-320, 0, 6720, 0, -20160, 0, 14784, 0, 0, 0, 0, 0, 0]
  | 7 => [0, -2240, 0, 20160, 0, -44352, 0, 27456, 0, 0, 0, 0, 0]
  | 8 => [280, 0, -10080, 0, 55440, 0, -96096, 0, 51480, 0, 0, 0, 0]
  | 9 => [0, 2520, 0, -36960, 0, 144144, 0, -205920, 0, 97240, 0, 0, 0]
  | 10 => [-252, 0, 13860, 0, -120120, 0, 360360, 0, -437580, 0, 184756, 0, 0]
  | 11 => [0, -2772, 0, 60060, 0, -360360, 0, 875160, 0, -923780, 0, 352716, 0]
  | 12 => [231, 0, -18018, 0, 225225, 0, -1021020, 0, 2078505, 0, -1939938, 0, 676039]
  | _ => List.replicate 13 0

private theorem legendreP12Int_len (k : ℕ) : (legendreP12Int k).length = 13 := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

private theorem evalPoly13_legendreP12Int {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ 12) (t : ℝ) :
    evalPoly13 (legendreP12Int k) t = 1024 * legendreP12 k t := by
  interval_cases k <;>
    simp [legendreP12Int, evalPoly13, range_13_eq, legendreP12] <;> ring

private theorem evalPoly13_mul_deg {p q : List ℤ} (dp dq : ℕ)
    (hdp : ∀ d, dp < d → p.getD d 0 = 0)
    (hdq : ∀ d, dq < d → q.getD d 0 = 0)
    (hdeg : dp + dq ≤ 12) (hp : p.length = 13) (hq : q.length = 13) (t : ℝ) :
    evalPoly13 (poly13Mul p q) t = evalPoly13 p t * evalPoly13 q t := by
  rw [evalPoly13_len13 (poly13Mul_len p q), evalPoly13_len13 hp, evalPoly13_len13 hq]
  have hget : ∀ d : Fin 13, ((poly13Mul p q).getD d.val 0 : ℝ) =
      ∑ i : Fin 13, ∑ j : Fin 13,
        if i.val + j.val = d.val then (p.getD i.val 0 : ℝ) * (q.getD j.val 0 : ℝ) else 0 := by
    intro d
    simp only [poly13Mul, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range d.isLt, Option.map_some, Option.getD_some]
    rw [foldl_add_int, zero_add, sum_range_int]
    push_cast
    have hsplit : ∑ i : Fin (d.val + 1), (p.getD i.val 0 : ℝ) * (q.getD (d.val - i.val) 0 : ℝ) =
        ∑ i : Fin 13, if i.val ≤ d.val then (p.getD i.val 0 : ℝ) * (q.getD (d.val - i.val) 0 : ℝ) else 0 := by
      have h1 : ∑ i : Fin 13, (if i.val ≤ d.val then (p.getD i.val 0 : ℝ) * (q.getD (d.val - i.val) 0 : ℝ) else 0) =
          ∑ i ∈ Finset.univ.filter (fun i : Fin 13 => i.val ≤ d.val),
            (p.getD i.val 0 : ℝ) * (q.getD (d.val - i.val) 0 : ℝ) := by
        rw [Finset.sum_filter]
      rw [h1]
      refine Finset.sum_bij (fun (i : Fin (d.val + 1)) _ => (⟨i.val, Nat.lt_of_lt_of_le i.isLt d.isLt⟩ : Fin 13))
        (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_lt_succ i.isLt⟩)
        (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun b hb => ⟨⟨b.val, Nat.lt_succ_of_le (Finset.mem_filter.mp hb).2⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        (fun _ _ => rfl)
    simp_rw [← List.getD_eq_getElem?_getD]
    rw [hsplit]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.val ≤ d.val
    · simp only [hi, ↓reduceIte]
      let j0 : Fin 13 := ⟨d.val - i.val, by omega⟩
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
  by_cases hij : i.val + j.val < 13
  · let d0 : Fin 13 := ⟨i.val + j.val, hij⟩
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
    have hsum0 : ∑ d : Fin 13, (if i.val + j.val = d.val then (p.getD i.val 0 : ℝ) * (q.getD j.val 0 : ℝ) else 0) * t ^ d.val = 0 := by
      refine Finset.sum_eq_zero fun d _ => ?_
      have : i.val + j.val ≠ d.val := by omega
      simp [this]
    rw [hsum0]
    linear_combination - (t ^ i.val * t ^ j.val) * hzero

/-! ## Degree-6 + Legendre `P₁..P₁₂` rational SDP certificate (`BVCert6`) -/

/-- Exact rational Bachoc–Vallentin degree-6 SDP certificate with two-point Legendre
terms `P₁..P₁₂` and pre-expanded `S₃`-reduced trivariate SOS bases. -/
structure BVCert6 where
  sNum : ℤ
  sDen : ℕ
  dK : ℕ
  dS0 : ℕ
  dS : ℕ
  dR : ℕ
  -- 7 kernel matrices F_0 (7×7) .. F_6 (1×1), scaled by dK
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
  -- 12 nonnegative Legendre weights c2[0..11] for P_1..P_12, scaled by dK
  c2 : List ℤ
  -- Univariate SOS matrices: S0 (7×7, scaled by dS0) and S1 (6×6, scaled by dK)
  S0 : List (List ℤ)
  R_S0 : List (List ℤ)
  S1 : List (List ℤ)
  R_S1 : List (List ℤ)
  -- 10 trivariate S3-reduced SOS blocks (scaled by dS) with dimensions and pre-expanded bases:
  -- 0,1,2: mult 1;  3,4,5: mult Delta;  6,7: mult g1=(s-u)(u+1);  8,9: mult g2=(s-v)(s-t)
  m0 : ℕ
  M0 : List (List ℤ)
  R0 : List (List ℤ)
  b0 : List Poly3
  m1 : ℕ
  M1 : List (List ℤ)
  R1 : List (List ℤ)
  b1 : List Poly3
  m2 : ℕ
  M2 : List (List ℤ)
  R2 : List (List ℤ)
  b2 : List Poly3
  m3 : ℕ
  M3 : List (List ℤ)
  R3 : List (List ℤ)
  b3 : List Poly3
  m4 : ℕ
  M4 : List (List ℤ)
  R4 : List (List ℤ)
  b4 : List Poly3
  m5 : ℕ
  M5 : List (List ℤ)
  R5 : List (List ℤ)
  b5 : List Poly3
  m6 : ℕ
  M6 : List (List ℤ)
  R6 : List (List ℤ)
  b6 : List Poly3
  m7 : ℕ
  M7 : List (List ℤ)
  R7 : List (List ℤ)
  b7 : List Poly3
  m8 : ℕ
  M8 : List (List ℤ)
  R8 : List (List ℤ)
  b8 : List Poly3
  m9 : ℕ
  M9 : List (List ℤ)
  R9 : List (List ℤ)
  b9 : List Poly3

namespace BVCert6

/-- Rational threshold `s = sNum / sDen`. -/
noncomputable def s (c : BVCert6) : ℝ := (c.sNum : ℝ) / (c.sDen : ℝ)

/-- Integer numerator of the certified upper bound `boundNum / dK`. -/
def boundNum (c : BVCert6) : ℤ :=
  (c.dK : ℤ) +
  (List.range 7).foldl (fun acc i =>
    (List.range 7).foldl (fun acc2 j => acc2 + matGet c.F0 i j) acc) 0 +
  (List.range 12).foldl (fun acc k => acc + c.c2.getD k 0) 0

/-- Certified real upper bound `boundNum / dK`. -/
noncomputable def bound (c : BVCert6) : ℝ := (c.boundNum : ℝ) / (c.dK : ℝ)

/-- Kernel matrix family `F : (k : Fin 7) → Matrix (Fin (6 - k + 1)) (Fin (6 - k + 1)) ℝ`. -/
noncomputable def toRealF (c : BVCert6) :
    (k : Fin 7) → Matrix (Fin (6 - k.val + 1)) (Fin (6 - k.val + 1)) ℝ
  | ⟨0, _⟩ => toRealMat 7 c.dK c.F0
  | ⟨1, _⟩ => toRealMat 6 c.dK c.F1
  | ⟨2, _⟩ => toRealMat 5 c.dK c.F2
  | ⟨3, _⟩ => toRealMat 4 c.dK c.F3
  | ⟨4, _⟩ => toRealMat 3 c.dK c.F4
  | ⟨5, _⟩ => toRealMat 2 c.dK c.F5
  | ⟨6, _⟩ => toRealMat 1 c.dK c.F6

/-- Legendre weights `c2 : Fin 12 → ℝ`. -/
noncomputable def toRealC2 (c : BVCert6) (k : Fin 12) : ℝ :=
  (c.c2.getD k.val 0 : ℝ) / (c.dK : ℝ)

/-- Degree-12 integer polynomial `1024 * dK * (bvG2Unaug F t + ∑ c2_k P_{k+1}(t))`. -/
def polyG2 (c : BVCert6) : List ℤ :=
  let lin0 : List ℤ := (List.range 13).map fun i =>
    if i < 7 then 2 * (List.range 7).foldl (fun acc j => acc + matGet c.F0 i j) 0 else 0
  let q0 := poly13Mul (quadPoly13 7 c.F0) (oneMinusT2Pow13 0)
  let q1 := poly13Mul (quadPoly13 6 c.F1) (oneMinusT2Pow13 1)
  let q2 := poly13Mul (quadPoly13 5 c.F2) (oneMinusT2Pow13 2)
  let q3 := poly13Mul (quadPoly13 4 c.F3) (oneMinusT2Pow13 3)
  let q4 := poly13Mul (quadPoly13 3 c.F4) (oneMinusT2Pow13 4)
  let q5 := poly13Mul (quadPoly13 2 c.F5) (oneMinusT2Pow13 5)
  let q6 := poly13Mul (quadPoly13 1 c.F6) (oneMinusT2Pow13 6)
  let g2_unaug := poly13Add lin0 (poly13Add q0 (poly13Add q1 (poly13Add q2 (poly13Add q3 (poly13Add q4 (poly13Add q5 q6))))))
  let leg := (List.range 12).foldl (fun acc k =>
    poly13Add acc (poly13Scale (c.c2.getD k 0) (legendreP12Int (k + 1)))) (List.replicate 13 0)
  poly13Add (poly13Scale 1024 g2_unaug) leg

/-- Univariate polynomial `(sDen * (s - t) * (t + 1))` = `sNum + (sNum - sDen) t - sDen t²`. -/
def poly13G1 (sNum : ℤ) (sDen : ℕ) : List ℤ :=
  [sNum, sNum - (sDen : ℤ), -(sDen : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Univariate identity check:
`sDen * dS0 * (-1024 * dK - polyG2) = 1024 * sDen * dK * S0(t) + 1024 * dS0 * (sDen*(s-t)(t+1)) * S1(t)`. -/
def checkEq2 (c : BVCert6) : Bool :=
  let constNeg : List ℤ := [-1024 * (c.dK : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  let lhs := poly13Scale ((c.sDen : ℤ) * (c.dS0 : ℤ))
    (poly13Add constNeg (poly13Scale (-1) c.polyG2))
  let rhs0 := poly13Scale (1024 * (c.sDen : ℤ) * (c.dK : ℤ)) (quadPoly13 7 c.S0)
  let rhs1 := poly13Scale (1024 * (c.dS0 : ℤ)) (poly13Mul (poly13G1 c.sNum c.sDen) (quadPoly13 6 c.S1))
  lhs == poly13Add rhs0 rhs1

/-- Helper: `∑ i < m, ∑ j < m, M[i][j] * u^i * v^j * bvQPoly3 k` as a `Poly3`. -/
def bvKernelBlockPoly3 (k m : ℕ) (M : List (List ℤ)) : Poly3 :=
  let qk := bvQPoly3 k
  (List.range m).foldl (fun acc i =>
    (List.range m).foldl (fun acc2 j =>
      let v := matGet M i j
      if v == 0 then acc2
      else mergePoly3 (qk.map fun ⟨a, b, d, w⟩ => (a + i, b + j, d, v * w)) acc2) acc) []

/-- Trivariate `dK * bvG3Unaug F` as a `Poly3`. -/
def polyG3 (c : BVCert6) : Poly3 :=
  mergePoly3 (bvKernelBlockPoly3 0 7 c.F0)
    (mergePoly3 (bvKernelBlockPoly3 1 6 c.F1)
      (mergePoly3 (bvKernelBlockPoly3 2 5 c.F2)
        (mergePoly3 (bvKernelBlockPoly3 3 4 c.F3)
          (mergePoly3 (bvKernelBlockPoly3 4 3 c.F4)
            (mergePoly3 (bvKernelBlockPoly3 5 2 c.F5)
              (bvKernelBlockPoly3 6 1 c.F6))))))

/-- Multiplier `Δ(u, v, t) = 1 + 2 u v t - u² - v² - t²`. -/
def polyDelta6 : Poly3 :=
  [(0, 0, 0, 1), (0, 0, 2, -1), (0, 2, 0, -1), (1, 1, 1, 2), (2, 0, 0, -1)]

/-- Multiplier `sDen * (s - u)(u + 1) = sNum + (sNum - sDen) u - sDen u²`. -/
def polyG1_6 (sNum : ℤ) (sDen : ℕ) : Poly3 :=
  [(0, 0, 0, sNum), (1, 0, 0, sNum - (sDen : ℤ)), (2, 0, 0, -(sDen : ℤ))]

/-- Multiplier `sDen² * (s - v)(s - t) = sNum² - sNum sDen v - sNum sDen t + sDen² v t`. -/
def polyG2_6 (sNum : ℤ) (sDen : ℕ) : Poly3 :=
  [(0, 0, 0, sNum * sNum), (0, 0, 1, -sNum * (sDen : ℤ)),
   (0, 1, 0, -sNum * (sDen : ℤ)), (0, 1, 1, (sDen : ℤ) * (sDen : ℤ))]

/-- `S₃`-canonicalized trivariate RHS polynomial (scaled by `sDen² * dS`). -/
def polyRHS3Canon (c : BVCert6) : Poly3 :=
  let sD2 : ℤ := (c.sDen : ℤ) * (c.sDen : ℤ)
  let sD : ℤ := (c.sDen : ℤ)
  let t0 := poly3Scale sD2 (sym3Canon (quadPoly3 c.m0 c.M0 c.b0))
  let t1 := poly3Scale sD2 (sym3Canon (quadPoly3 c.m1 c.M1 c.b1))
  let t2 := poly3Scale sD2 (sym3Canon (quadPoly3 c.m2 c.M2 c.b2))
  let t3 := poly3Scale sD2 (sym3Canon (mulPoly3Sorted polyDelta6 (quadPoly3 c.m3 c.M3 c.b3)))
  let t4 := poly3Scale sD2 (sym3Canon (mulPoly3Sorted polyDelta6 (quadPoly3 c.m4 c.M4 c.b4)))
  let t5 := poly3Scale sD2 (sym3Canon (mulPoly3Sorted polyDelta6 (quadPoly3 c.m5 c.M5 c.b5)))
  let t6 := poly3Scale sD (sym3Canon (mulPoly3Sorted (polyG1_6 c.sNum c.sDen) (quadPoly3 c.m6 c.M6 c.b6)))
  let t7 := poly3Scale sD (sym3Canon (mulPoly3Sorted (polyG1_6 c.sNum c.sDen) (quadPoly3 c.m7 c.M7 c.b7)))
  let t8 := sym3Canon (mulPoly3Sorted (polyG2_6 c.sNum c.sDen) (quadPoly3 c.m8 c.M8 c.b8))
  let t9 := sym3Canon (mulPoly3Sorted (polyG2_6 c.sNum c.sDen) (quadPoly3 c.m9 c.M9 c.b9))
  sym3Canon (t0 ++ t1 ++ t2 ++ t3 ++ t4 ++ t5 ++ t6 ++ t7 ++ t8 ++ t9)

/-- Complete kernel-decidable validity predicate for a `BVCert6`. -/
def isValid (c : BVCert6) : Bool :=
  decide (0 < c.sDen) &&
  decide (0 < c.dK) &&
  decide (0 < c.dS0) &&
  decide (0 < c.dS) &&
  decide (0 < c.dR) &&
  decide (-(c.sDen : ℤ) < c.sNum) &&
  ((List.range 12).all fun k => decide (0 ≤ c.c2.getD k 0)) &&
  isCholeskyDDValid 7 c.dK c.dR c.F0 c.R_F0 &&
  isCholeskyDDValid 6 c.dK c.dR c.F1 c.R_F1 &&
  isCholeskyDDValid 5 c.dK c.dR c.F2 c.R_F2 &&
  isCholeskyDDValid 4 c.dK c.dR c.F3 c.R_F3 &&
  isCholeskyDDValid 3 c.dK c.dR c.F4 c.R_F4 &&
  isCholeskyDDValid 2 c.dK c.dR c.F5 c.R_F5 &&
  isCholeskyDDValid 1 c.dK c.dR c.F6 c.R_F6 &&
  isCholeskyDDValid 7 c.dS0 c.dR c.S0 c.R_S0 &&
  isCholeskyDDValid 6 c.dK c.dR c.S1 c.R_S1 &&
  isCholeskyDDValid c.m0 c.dS c.dR c.M0 c.R0 &&
  isCholeskyDDValid c.m1 c.dS c.dR c.M1 c.R1 &&
  isCholeskyDDValid c.m2 c.dS c.dR c.M2 c.R2 &&
  isCholeskyDDValid c.m3 c.dS c.dR c.M3 c.R3 &&
  isCholeskyDDValid c.m4 c.dS c.dR c.M4 c.R4 &&
  isCholeskyDDValid c.m5 c.dS c.dR c.M5 c.R5 &&
  isCholeskyDDValid c.m6 c.dS c.dR c.M6 c.R6 &&
  isCholeskyDDValid c.m7 c.dS c.dR c.M7 c.R7 &&
  isCholeskyDDValid c.m8 c.dS c.dR c.M8 c.R8 &&
  isCholeskyDDValid c.m9 c.dS c.dR c.M9 c.R9 &&
  c.checkEq2 &&
  (sym3Canon (poly3Scale (-((c.sDen : ℤ) * (c.sDen : ℤ) * (c.dS : ℤ))) c.polyG3) ==
    sym3Canon (poly3Scale (c.dK : ℤ) c.polyRHS3Canon))

private theorem evalPoly3_bvKernelBlockPoly3 (k m : ℕ) (M : List (List ℤ)) (u v t : ℝ) :
    evalPoly3 (bvKernelBlockPoly3 k m M) u v t =
      (∑ i : Fin m, ∑ j : Fin m, (matGet M i.val j.val : ℝ) * u ^ i.val * v ^ j.val) * bvQ k u v t := by
  unfold bvKernelBlockPoly3
  have hshift : ∀ (i j : ℕ) (val : ℤ),
      evalPoly3 ((bvQPoly3 k).map fun ⟨a, b, d, w⟩ => (a + i, b + j, d, val * w)) u v t =
        ((val : ℝ) * u ^ i * v ^ j) * bvQ k u v t := by
    intro i j val
    rw [← evalPoly3_bvQPoly3 k u v t]
    have hsum : ∀ (l : Poly3),
        evalPoly3 (l.map fun ⟨a, b, d, w⟩ => (a + i, b + j, d, val * w)) u v t =
          ((val : ℝ) * u ^ i * v ^ j) * evalPoly3 l u v t := by
      intro l
      induction l with
      | nil => simp [evalPoly3_nil]
      | cons x xs ih =>
        rcases x with ⟨a, b, d, w⟩
        have hcons1 : evalPoly3 ((a + i, b + j, d, val * w) :: xs.map fun ⟨a, b, d, w⟩ => (a + i, b + j, d, val * w)) u v t =
            ((val * w : ℤ) : ℝ) * (u ^ (a + i) * v ^ (b + j) * t ^ d) +
            evalPoly3 (xs.map fun ⟨a, b, d, w⟩ => (a + i, b + j, d, val * w)) u v t := by
          have h := evalPoly3_append [(a + i, b + j, d, val * w)] (xs.map fun ⟨a, b, d, w⟩ => (a + i, b + j, d, val * w)) u v t
          simpa [evalPoly3] using h
        have hcons2 : evalPoly3 ((a, b, d, w) :: xs) u v t =
            (w : ℝ) * (u ^ a * v ^ b * t ^ d) + evalPoly3 xs u v t := by
          have h := evalPoly3_append [(a, b, d, w)] xs u v t
          simpa [evalPoly3] using h
        simp only [List.map_cons, hcons1, hcons2, ih, Int.cast_mul, pow_add]
        ring
    exact hsum (bvQPoly3 k)
  have hinner : ∀ (i : ℕ) (l : List ℕ) (acc : Poly3),
      evalPoly3 (l.foldl (fun acc2 j =>
        let val := matGet M i j
        if val == 0 then acc2
        else mergePoly3 ((bvQPoly3 k).map fun ⟨a, b, d, w⟩ => (a + i, b + j, d, val * w)) acc2) acc) u v t =
      evalPoly3 acc u v t +
      (l.map fun j => ((matGet M i j : ℝ) * u ^ i * v ^ j) * bvQ k u v t).sum := by
    intro i l
    induction l with
    | nil => intro acc; simp
    | cons j js ih =>
      intro acc
      simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      by_cases hv : (matGet M i j == 0) = true
      · have h0 : matGet M i j = 0 := by simpa using hv
        simp [h0]
      · simp only [hv, Bool.false_eq_true, ↓reduceIte, evalPoly3_mergePoly3, hshift]
        ring
  have houter : ∀ (l : List ℕ) (acc : Poly3),
      evalPoly3 (l.foldl (fun acc1 i =>
        (List.range m).foldl (fun acc2 j =>
          let val := matGet M i j
          if val == 0 then acc2
          else mergePoly3 ((bvQPoly3 k).map fun ⟨a, b, d, w⟩ => (a + i, b + j, d, val * w)) acc2) acc1) acc) u v t =
      evalPoly3 acc u v t +
      (l.map fun i =>
        ((List.range m).map fun j => ((matGet M i j : ℝ) * u ^ i * v ^ j) * bvQ k u v t).sum).sum := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons i is ih =>
      intro acc
      simp only [List.foldl_cons, ih, hinner, List.map_cons, List.sum_cons]
      ring
  rw [houter, evalPoly3_nil, zero_add]
  have hrm : ∀ (f : ℕ → ℝ), ((List.range m).map f).sum = ∑ j : Fin m, f j.val := fun f => by
    rw [Fin.sum_univ_def]; congr 1; apply List.ext_getElem <;> simp
  rw [hrm]
  simp_rw [hrm, ← Finset.sum_mul]

private theorem finRange_7_eq : List.finRange 7 =
    [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
     ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩] := by decide

private theorem evalPoly3_polyG3 (c : BVCert6) (hdK : 0 < c.dK) (u v t : ℝ) :
    evalPoly3 c.polyG3 u v t = (c.dK : ℝ) * bvG3Unaug c.toRealF u v t := by
  have hdK_pos : (0 : ℝ) < (c.dK : ℝ) := Nat.cast_pos.mpr hdK
  have hsum7 : ∀ f : Fin 7 → ℝ, ∑ k : Fin 7, f k =
      f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ + f ⟨3, by omega⟩ +
      f ⟨4, by omega⟩ + f ⟨5, by omega⟩ + f ⟨6, by omega⟩ := by
    intro f
    rw [Fin.sum_univ_def, finRange_7_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  simp only [polyG3, evalPoly3_mergePoly3, evalPoly3_bvKernelBlockPoly3, bvG3Unaug]
  rw [hsum7 (fun k : Fin 7 => (∑ i : Fin (6 - k.val + 1), ∑ j : Fin (6 - k.val + 1),
    c.toRealF k i j * u ^ i.val * v ^ j.val) * bvQ k.val u v t)]
  simp only [toRealF, toRealMat, Matrix.of_apply]
  have hscale : ∀ (m : ℕ) (M : List (List ℤ)) (q : ℝ),
      (c.dK : ℝ) * ((∑ i : Fin m, ∑ j : Fin m, ((matGet M i.val j.val : ℝ) / (c.dK : ℝ)) * u ^ i.val * v ^ j.val) * q) =
      (∑ i : Fin m, ∑ j : Fin m, (matGet M i.val j.val : ℝ) * u ^ i.val * v ^ j.val) * q := by
    intro m M q
    rw [← mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hdK_pos.ne']
  rw [mul_add, mul_add, mul_add, mul_add, mul_add, mul_add,
    hscale, hscale, hscale, hscale, hscale, hscale, hscale]
  ring

private theorem quadPoly13_getD_zero_of_gt {m : ℕ} (M : List (List ℤ)) {d : ℕ} (hd : 2 * (m - 1) < d) :
    (quadPoly13 m M).getD d 0 = 0 := by
  by_cases hd13 : d < 13
  · simp only [quadPoly13, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hd13, Option.map_some, Option.getD_some]
    have hfold : ∀ (l : List ℕ), (∀ i ∈ l, ¬(i ≤ d ∧ d - i < m)) →
        l.foldl (fun acc i => if i ≤ d ∧ d - i < m then acc + matGet M i (d - i) else acc) 0 = 0 := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a s ih =>
        have ha : ¬(a ≤ d ∧ d - a < m) := hl a (by simp)
        simp only [List.foldl_cons, ha, ↓reduceIte]
        exact ih (fun i hi => hl i (by simp [hi]))
    exact hfold (List.range m) (fun i hi => by simp at hi; omega)
  · have hle : (quadPoly13 m M).length ≤ d := by simp [quadPoly13]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
    rfl

private theorem oneMinusT2Pow13_getD_zero {k : ℕ} (hk : k ≤ 6) {d : ℕ} (hd : 2 * k < d) :
    (oneMinusT2Pow13 k).getD d 0 = 0 := by
  by_cases hd13 : d < 13
  · interval_cases k <;> interval_cases d <;> rfl
  · have hlen : (oneMinusT2Pow13 k).length = 13 := by interval_cases k <;> rfl
    have hle : (oneMinusT2Pow13 k).length ≤ d := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
    rfl

private theorem evalPoly13_polyG2 (c : BVCert6) (hdK : 0 < c.dK) (t : ℝ) :
    evalPoly13 c.polyG2 t =
      1024 * (c.dK : ℝ) *
        (bvG2Unaug c.toRealF t + ∑ k : Fin 12, c.toRealC2 k * legendreP12 (k.val + 1) t) := by
  have hdK_pos : (0 : ℝ) < (c.dK : ℝ) := Nat.cast_pos.mpr hdK
  unfold polyG2
  have hlin_len : ((List.range 13).map fun i =>
      if i < 7 then 2 * (List.range 7).foldl (fun acc j => acc + matGet c.F0 i j) 0 else 0).length = 13 := by
    simp
  have hleg_len : ∀ (l : List ℕ) (acc : List ℤ), acc.length = 13 →
      (l.foldl (fun acc k => poly13Add acc (poly13Scale (c.c2.getD k 0) (legendreP12Int (k + 1)))) acc).length = 13 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons a s ih => intro acc _; exact ih _ (poly13Add_len _ _)
  have hleg_eval : ∀ (l : List ℕ) (acc : List ℤ), acc.length = 13 → (∀ k ∈ l, k < 12) →
      evalPoly13 (l.foldl (fun acc k => poly13Add acc (poly13Scale (c.c2.getD k 0) (legendreP12Int (k + 1)))) acc) t =
      evalPoly13 acc t + (l.map fun k => (c.c2.getD k 0 : ℝ) * (1024 * legendreP12 (k + 1) t)).sum := by
    intro l
    induction l with
    | nil => intro acc _ _; simp
    | cons a s ih =>
      intro acc hacc hl
      have ha : a < 12 := hl a (by simp)
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih _ (poly13Add_len _ _) (fun k hk => hl k (by simp [hk])),
        evalPoly13_add hacc (poly13Scale_len _ _),
        evalPoly13_scale (legendreP12Int_len (a + 1)),
        evalPoly13_legendreP12Int (by omega) (by omega)]
      ring
  have hq_eval : ∀ (k m : ℕ) (M : List (List ℤ)), k ≤ 6 → m = 6 - k + 1 →
      evalPoly13 (poly13Mul (quadPoly13 m M) (oneMinusT2Pow13 k)) t =
      (∑ i : Fin m, ∑ j : Fin m, (matGet M i.val j.val : ℝ) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ k := by
    intro k m M hk hm
    have h1 : (oneMinusT2Pow13 k).length = 13 := by interval_cases k <;> rfl
    rw [evalPoly13_mul_deg (2 * (m - 1)) (2 * k)
        (fun d hd => quadPoly13_getD_zero_of_gt M hd)
        (fun d hd => oneMinusT2Pow13_getD_zero hk hd)
        (by omega) (quadPoly13_len m M) h1 t,
      evalPoly13_quadPoly13 (by omega), evalPoly13_oneMinusT2Pow13 hk]
  have hlin_eval : evalPoly13 ((List.range 13).map fun i =>
      if i < 7 then 2 * (List.range 7).foldl (fun acc j => acc + matGet c.F0 i j) 0 else 0) t =
      2 * ∑ i : Fin 7, ∑ j : Fin 7, (matGet c.F0 i.val j.val : ℝ) * t ^ i.val := by
    rw [evalPoly13_len13 hlin_len]
    have hsplit : ∑ d : Fin 13, (((List.range 13).map fun i =>
        if i < 7 then 2 * (List.range 7).foldl (fun acc j => acc + matGet c.F0 i j) 0 else 0).getD d.val 0 : ℝ) * t ^ d.val =
        ∑ d : Fin 13, if d.val < 7 then
          2 * (∑ j : Fin 7, (matGet c.F0 d.val j.val : ℝ) * t ^ d.val) else 0 := by
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range d.isLt,
        Option.map_some, Option.getD_some]
      by_cases hd7 : d.val < 7
      · simp only [hd7, ↓reduceIte, Int.cast_mul, Int.cast_ofNat]
        rw [foldl_add_int, zero_add, sum_range_int]
        push_cast
        rw [mul_assoc, Finset.sum_mul]
      · simp [hd7]
    rw [hsplit, ← Finset.sum_filter]
    have hbij : ∑ d ∈ Finset.univ.filter (fun d : Fin 13 => d.val < 7),
        2 * ∑ j : Fin 7, (matGet c.F0 d.val j.val : ℝ) * t ^ d.val =
        ∑ i : Fin 7, 2 * ∑ j : Fin 7, (matGet c.F0 i.val j.val : ℝ) * t ^ i.val := by
      refine Finset.sum_bij (fun d hd => ⟨d.val, (Finset.mem_filter.mp hd).2⟩) (fun _ _ => Finset.mem_univ _)
        (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun b _ => ⟨⟨b.val, by omega⟩, by simp, Fin.ext rfl⟩)
        (fun _ _ => rfl)
    rw [hbij, ← Finset.mul_sum]
  rw [evalPoly13_add (poly13Scale_len _ _) (hleg_len _ _ (by simp)),
    evalPoly13_scale (poly13Add_len _ _),
    evalPoly13_add hlin_len (poly13Add_len _ _),
    evalPoly13_add (poly13Mul_len _ _) (poly13Add_len _ _),
    evalPoly13_add (poly13Mul_len _ _) (poly13Add_len _ _),
    evalPoly13_add (poly13Mul_len _ _) (poly13Add_len _ _),
    evalPoly13_add (poly13Mul_len _ _) (poly13Add_len _ _),
    evalPoly13_add (poly13Mul_len _ _) (poly13Add_len _ _),
    evalPoly13_add (poly13Mul_len _ _) (poly13Mul_len _ _),
    hlin_eval,
    hq_eval 0 7 c.F0 (by omega) rfl,
    hq_eval 1 6 c.F1 (by omega) rfl,
    hq_eval 2 5 c.F2 (by omega) rfl,
    hq_eval 3 4 c.F3 (by omega) rfl,
    hq_eval 4 3 c.F4 (by omega) rfl,
    hq_eval 5 2 c.F5 (by omega) rfl,
    hq_eval 6 1 c.F6 (by omega) rfl,
    hleg_eval _ _ (by simp) (fun k hk => by simpa using hk)]
  have hrep0 : evalPoly13 (List.replicate 13 (0 : ℤ)) t = 0 := by
    simp [evalPoly13, range_13_eq]
  rw [hrep0, zero_add]
  have hleg_fin : ((List.range 12).map fun k => (c.c2.getD k 0 : ℝ) * (1024 * legendreP12 (k + 1) t)).sum =
      1024 * (c.dK : ℝ) * ∑ k : Fin 12, c.toRealC2 k * legendreP12 (k.val + 1) t := by
    rw [Finset.mul_sum, Fin.sum_univ_def]
    have hmap : (List.range 12).map (fun k => (c.c2.getD k 0 : ℝ) * (1024 * legendreP12 (k + 1) t)) =
        (List.finRange 12).map (fun k : Fin 12 => 1024 * (c.dK : ℝ) * (c.toRealC2 k * legendreP12 (k.val + 1) t)) := by
      apply List.ext_getElem
      · simp
      · intro i hi _
        simp only [List.getElem_map, List.getElem_range, List.getElem_finRange, Fin.val_cast, toRealC2]
        field_simp [hdK_pos.ne']
    rw [hmap]
  rw [hleg_fin]
  have hsum7 : ∀ f : Fin 7 → ℝ, ∑ k : Fin 7, f k =
      f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ + f ⟨3, by omega⟩ +
      f ⟨4, by omega⟩ + f ⟨5, by omega⟩ + f ⟨6, by omega⟩ := by
    intro f
    rw [Fin.sum_univ_def, finRange_7_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  simp only [bvG2Unaug]
  rw [hsum7 (fun k : Fin 7 => (∑ i : Fin (6 - k.val + 1), ∑ j : Fin (6 - k.val + 1),
    c.toRealF k i j * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ k.val)]
  simp only [toRealF, toRealMat, Matrix.of_apply]
  have hdiv : ∀ (m : ℕ) (M : List (List ℤ)) (f : Fin m → Fin m → ℝ),
      (c.dK : ℝ) * (∑ i : Fin m, ∑ j : Fin m, ((matGet M i.val j.val : ℝ) / (c.dK : ℝ)) * f i j) =
      ∑ i : Fin m, ∑ j : Fin m, (matGet M i.val j.val : ℝ) * f i j := by
    intro m M f
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hdK_pos.ne']
  have hdiv' : ∀ (m : ℕ) (M : List (List ℤ)) (f : Fin m → Fin m → ℝ) (q : ℝ),
      (c.dK : ℝ) * ((∑ i : Fin m, ∑ j : Fin m, ((matGet M i.val j.val : ℝ) / (c.dK : ℝ)) * f i j) * q) =
      (∑ i : Fin m, ∑ j : Fin m, (matGet M i.val j.val : ℝ) * f i j) * q := by
    intro m M f q
    rw [← mul_assoc, hdiv]
  have h2_eq : 1024 * (c.dK : ℝ) * (2 * ∑ i : Fin 7, ∑ j : Fin 7, ((matGet c.F0 i.val j.val : ℝ) / (c.dK : ℝ)) * t ^ i.val) =
      1024 * (2 * ∑ i : Fin 7, ∑ j : Fin 7, (matGet c.F0 i.val j.val : ℝ) * t ^ i.val) := by
    have := hdiv 7 c.F0 (fun i _ => t ^ i.val)
    linear_combination 2048 * this
  have hsum_eq : 1024 * (c.dK : ℝ) * (
      (∑ i : Fin 7, ∑ j : Fin 7, ((matGet c.F0 i.val j.val : ℝ) / (c.dK : ℝ)) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 0 +
      (∑ i : Fin 6, ∑ j : Fin 6, ((matGet c.F1 i.val j.val : ℝ) / (c.dK : ℝ)) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 1 +
      (∑ i : Fin 5, ∑ j : Fin 5, ((matGet c.F2 i.val j.val : ℝ) / (c.dK : ℝ)) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 2 +
      (∑ i : Fin 4, ∑ j : Fin 4, ((matGet c.F3 i.val j.val : ℝ) / (c.dK : ℝ)) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 3 +
      (∑ i : Fin 3, ∑ j : Fin 3, ((matGet c.F4 i.val j.val : ℝ) / (c.dK : ℝ)) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 4 +
      (∑ i : Fin 2, ∑ j : Fin 2, ((matGet c.F5 i.val j.val : ℝ) / (c.dK : ℝ)) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 5 +
      (∑ i : Fin 1, ∑ j : Fin 1, ((matGet c.F6 i.val j.val : ℝ) / (c.dK : ℝ)) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 6) =
      1024 * (
      (∑ i : Fin 7, ∑ j : Fin 7, (matGet c.F0 i.val j.val : ℝ) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 0 +
      (∑ i : Fin 6, ∑ j : Fin 6, (matGet c.F1 i.val j.val : ℝ) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 1 +
      (∑ i : Fin 5, ∑ j : Fin 5, (matGet c.F2 i.val j.val : ℝ) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 2 +
      (∑ i : Fin 4, ∑ j : Fin 4, (matGet c.F3 i.val j.val : ℝ) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 3 +
      (∑ i : Fin 3, ∑ j : Fin 3, (matGet c.F4 i.val j.val : ℝ) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 4 +
      (∑ i : Fin 2, ∑ j : Fin 2, (matGet c.F5 i.val j.val : ℝ) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 5 +
      (∑ i : Fin 1, ∑ j : Fin 1, (matGet c.F6 i.val j.val : ℝ) * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ 6) := by
    rw [mul_assoc]
    congr 1
    rw [mul_add, mul_add, mul_add, mul_add, mul_add, mul_add,
      hdiv', hdiv', hdiv', hdiv', hdiv', hdiv', hdiv']
  simp only [Int.cast_ofNat]
  linear_combination -h2_eq - hsum_eq

private theorem bound_eq_sum (c : BVCert6) (hdK : 0 < c.dK) :
    c.bound = 1 + (∑ i : Fin 7, ∑ j : Fin 7, c.toRealF ⟨0, by omega⟩ i j) + ∑ k : Fin 12, c.toRealC2 k := by
  have hdK_pos : (0 : ℝ) < (c.dK : ℝ) := Nat.cast_pos.mpr hdK
  unfold bound boundNum
  have hF0 : ((List.range 7).foldl (fun acc i =>
      (List.range 7).foldl (fun acc2 j => acc2 + matGet c.F0 i j) acc) 0 : ℤ) =
      ∑ i : Fin 7, ∑ j : Fin 7, matGet c.F0 i.val j.val := by
    have houter : ∀ (l : List ℕ) (acc : ℤ),
        l.foldl (fun acc i => (List.range 7).foldl (fun acc2 j => acc2 + matGet c.F0 i j) acc) acc =
        acc + (l.map fun i => ∑ j : Fin 7, matGet c.F0 i j.val).sum := by
      intro l
      induction l with
      | nil => intro acc; simp
      | cons a s ih =>
        intro acc
        simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldl_add_int, sum_range_int]
        ring
    rw [houter, zero_add, sum_range_int]
  have hc2 : ((List.range 12).foldl (fun acc k => acc + c.c2.getD k 0) 0 : ℤ) =
      ∑ k : Fin 12, c.c2.getD k.val 0 := by
    rw [foldl_add_int, zero_add, sum_range_int]
  rw [hF0, hc2]
  simp only [toRealF, toRealMat, Matrix.of_apply, toRealC2]
  push_cast
  have h1 : (∑ i : Fin 7, ∑ j : Fin 7, (matGet c.F0 i.val j.val : ℝ) / (c.dK : ℝ)) =
      (∑ i : Fin 7, ∑ j : Fin 7, (matGet c.F0 i.val j.val : ℝ)) / (c.dK : ℝ) := by
    simp_rw [← Finset.sum_div]
  have h2 : (∑ k : Fin 12, (c.c2.getD k.val 0 : ℝ) / (c.dK : ℝ)) =
      (∑ k : Fin 12, (c.c2.getD k.val 0 : ℝ)) / (c.dK : ℝ) := by
    rw [Finset.sum_div]
  rw [h1, h2]
  field_simp [hdK_pos.ne']

/-- **Soundness of `BVCert6`**: any degree-6 + Legendre `P₁..P₁₂` rational SDP
certificate passing `BVCert6.isValid` unconditionally proves
`(n : ℝ) ≤ cert.bound` for every `(n, cert.s)`-spherical code on `S²`. -/
theorem sound (c : BVCert6) (hvalid : c.isValid = true)
    {n : ℕ} {p : Fin n → UnitSphere} (hp : IsSphericalCode p c.s) :
    (n : ℝ) ≤ c.bound := by
  simp only [isValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at hvalid
  rcases hvalid with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsDen, hdK⟩, hdS0⟩, hdS⟩, hdR⟩, hsgt⟩, hc2_nn⟩,
    hF0⟩, hF1⟩, hF2⟩, hF3⟩, hF4⟩, hF5⟩, hF6⟩, hS0⟩, hS1⟩,
    hM0⟩, hM1⟩, hM2⟩, hM3⟩, hM4⟩, hM5⟩, hM6⟩, hM7⟩, hM8⟩, hM9⟩, heq2⟩, heq3⟩
  have hsDen_pos : (0 : ℝ) < (c.sDen : ℝ) := Nat.cast_pos.mpr hsDen
  have hdK_pos : (0 : ℝ) < (c.dK : ℝ) := Nat.cast_pos.mpr hdK
  have hdS0_pos : (0 : ℝ) < (c.dS0 : ℝ) := Nat.cast_pos.mpr hdS0
  have hdS_pos : (0 : ℝ) < (c.dS : ℝ) := Nat.cast_pos.mpr hdS
  have hF : ∀ k : Fin 7, (c.toRealF k).PosSemidef := by
    intro k
    fin_cases k
    · exact isCholeskyDDValid_sound hF0
    · exact isCholeskyDDValid_sound hF1
    · exact isCholeskyDDValid_sound hF2
    · exact isCholeskyDDValid_sound hF3
    · exact isCholeskyDDValid_sound hF4
    · exact isCholeskyDDValid_sound hF5
    · exact isCholeskyDDValid_sound hF6
  have hc2 : ∀ k : Fin 12, 0 ≤ c.toRealC2 k := fun k =>
    div_nonneg (by exact_mod_cast (hc2_nn k.val k.isLt)) hdK_pos.le
  have hS0_psd : (toRealMat 7 c.dS0 c.S0).PosSemidef := isCholeskyDDValid_sound hS0
  have hS1_psd : (toRealMat 6 c.dK c.S1).PosSemidef := isCholeskyDDValid_sound hS1
  -- Univariate inequality h2
  have h2 : ∀ t : ℝ, -1 ≤ t → t ≤ c.s →
      bvG2Unaug c.toRealF t + ∑ k : Fin 12, c.toRealC2 k * legendreP12 (k.val + 1) t ≤ -1 := by
    intro t ht1 ht2
    simp only [checkEq2, beq_iff_eq] at heq2
    have hev := congrArg (fun q => evalPoly13 q t) heq2
    have hlenG2 : c.polyG2.length = 13 := by
      unfold polyG2; exact poly13Add_len _ _
    have hconst_len : ([-1024 * (c.dK : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).length = 13 := rfl
    have hconst_ev : evalPoly13 [-1024 * (c.dK : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] t =
        -1024 * (c.dK : ℝ) := by
      simp [evalPoly13, range_13_eq]
    have hg1_len : (poly13G1 c.sNum c.sDen).length = 13 := rfl
    have hg1_deg : ∀ d, 2 < d → (poly13G1 c.sNum c.sDen).getD d 0 = 0 := by
      intro d hd
      by_cases hd13 : d < 13
      · interval_cases d <;> rfl
      · have hle : (poly13G1 c.sNum c.sDen).length ≤ d := by simp [poly13G1]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]; rfl
    have hg1_ev : evalPoly13 (poly13G1 c.sNum c.sDen) t =
        (c.sDen : ℝ) * (c.s - t) * (t + 1) := by
      rw [evalPoly13, hg1_len, range_13_eq]
      simp only [poly13G1, s, List.foldl_cons, List.foldl_nil, List.getD_cons_zero,
        List.getD_cons_succ, Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_zero,
        pow_zero, pow_one, mul_one, zero_mul, add_zero, zero_add]
      field_simp [hsDen_pos.ne']
      ring
    rw [evalPoly13_scale (poly13Add_len _ _), evalPoly13_add hconst_len (poly13Scale_len _ _),
      hconst_ev, evalPoly13_scale hlenG2, evalPoly13_polyG2 c hdK t,
      evalPoly13_add (poly13Scale_len _ _) (poly13Scale_len _ _),
      evalPoly13_scale (quadPoly13_len 7 c.S0), evalPoly13_quadPoly13 (by omega),
      evalPoly13_scale (poly13Mul_len _ _),
      evalPoly13_mul_deg 2 10 hg1_deg (fun d hd => quadPoly13_getD_zero_of_gt c.S1 hd)
        (by omega) hg1_len (quadPoly13_len 6 c.S1),
      hg1_ev, evalPoly13_quadPoly13 (by omega)] at hev
    have hq0_nn : 0 ≤ ∑ i : Fin 7, ∑ j : Fin 7, (matGet c.S0 i.val j.val : ℝ) * t ^ (i.val + j.val) := by
      have h := posSemidef_quad_nonneg hS0_psd (fun i : Fin 7 => t ^ i.val)
      have hmul : (c.dS0 : ℝ) * (∑ a : Fin 7, ∑ b : Fin 7, t ^ a.val * toRealMat 7 c.dS0 c.S0 a b * t ^ b.val) =
          ∑ i : Fin 7, ∑ j : Fin 7, (matGet c.S0 i.val j.val : ℝ) * t ^ (i.val + j.val) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [toRealMat, Matrix.of_apply, pow_add]
        field_simp [hdS0_pos.ne']
      nlinarith [mul_nonneg hdS0_pos.le h]
    have hq1_nn : 0 ≤ ∑ i : Fin 6, ∑ j : Fin 6, (matGet c.S1 i.val j.val : ℝ) * t ^ (i.val + j.val) := by
      have h := posSemidef_quad_nonneg hS1_psd (fun i : Fin 6 => t ^ i.val)
      have hmul : (c.dK : ℝ) * (∑ a : Fin 6, ∑ b : Fin 6, t ^ a.val * toRealMat 6 c.dK c.S1 a b * t ^ b.val) =
          ∑ i : Fin 6, ∑ j : Fin 6, (matGet c.S1 i.val j.val : ℝ) * t ^ (i.val + j.val) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [toRealMat, Matrix.of_apply, pow_add]
        field_simp [hdK_pos.ne']
      nlinarith [mul_nonneg hdK_pos.le h]
    have hfac_nn : 0 ≤ (c.sDen : ℝ) * (c.s - t) * (t + 1) := by
      have h1 : 0 ≤ c.s - t := by linarith
      have h2' : 0 ≤ t + 1 := by linarith
      positivity
    have hrhs_nn : 0 ≤ ((1024 * (c.sDen : ℤ) * (c.dK : ℤ) : ℤ) : ℝ) *
        (∑ i : Fin 7, ∑ j : Fin 7, (matGet c.S0 i.val j.val : ℝ) * t ^ (i.val + j.val)) +
        ((1024 * (c.dS0 : ℤ) : ℤ) : ℝ) *
        ((c.sDen : ℝ) * (c.s - t) * (t + 1) *
          ∑ i : Fin 6, ∑ j : Fin 6, (matGet c.S1 i.val j.val : ℝ) * t ^ (i.val + j.val)) := by
      push_cast; positivity
    have hlhs_nn : 0 ≤ ((c.sDen : ℝ) * (c.dS0 : ℝ)) *
        (-1024 * (c.dK : ℝ) + (-1 : ℝ) * (1024 * (c.dK : ℝ) *
          (bvG2Unaug c.toRealF t + ∑ k : Fin 12, c.toRealC2 k * legendreP12 (k.val + 1) t))) := by
      have hcast : (((c.sDen : ℤ) * (c.dS0 : ℤ) : ℤ) : ℝ) = (c.sDen : ℝ) * (c.dS0 : ℝ) := by push_cast; rfl
      rw [← hcast]
      have hneg1 : ((-1 : ℤ) : ℝ) = (-1 : ℝ) := by norm_num
      rw [← hneg1]
      exact hrhs_nn.trans_eq hev.symm
    have hcoeff_pos : (0 : ℝ) < 1024 * (c.sDen : ℝ) * (c.dS0 : ℝ) * (c.dK : ℝ) := by positivity
    nlinarith
  -- Trivariate inequality h3
  have h3 : ∀ u v t : ℝ, InThreePointDomain c.s u v t → sym3 (bvG3Unaug c.toRealF) u v t ≤ 0 := by
    intro u v t hdom
    have hsym_eq := congrArg (fun q => sym3 (evalPoly3 q) u v t) heq3
    simp only [sym3_evalPoly3_sym3Canon] at hsym_eq
    have hlhs_eval : sym3 (evalPoly3 (poly3Scale (-((c.sDen : ℤ) * (c.sDen : ℤ) * (c.dS : ℤ))) c.polyG3)) u v t =
        -((c.sDen : ℝ) * (c.sDen : ℝ) * (c.dS : ℝ) * (c.dK : ℝ)) * sym3 (bvG3Unaug c.toRealF) u v t := by
      have hf : evalPoly3 (poly3Scale (-((c.sDen : ℤ) * (c.sDen : ℤ) * (c.dS : ℤ))) c.polyG3) =
          fun a b d => -((c.sDen : ℝ) * (c.sDen : ℝ) * (c.dS : ℝ) * (c.dK : ℝ)) * bvG3Unaug c.toRealF a b d := by
        ext a b d
        rw [evalPoly3_scale, evalPoly3_polyG3 c hdK a b d]
        push_cast; ring
      rw [hf]
      unfold sym3; ring
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
        intro f hf
        unfold sym3
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
        intro p hp'
        rw [sym3_evalPoly3_sym3Canon]
        exact hsym_nn (evalPoly3 p) hp'
      have hDelta_ev : ∀ a b d : ℝ, evalPoly3 polyDelta6 a b d = gramDet3 a b d := by
        intro a b d; simp [polyDelta6, evalPoly3, gramDet3]; ring
      have hg1_ev : ∀ a b d : ℝ, evalPoly3 (polyG1_6 c.sNum c.sDen) a b d =
          (c.sDen : ℝ) * (c.s - a) * (a + 1) := by
        intro a b d
        simp only [polyG1_6, evalPoly3, List.foldl_cons, List.foldl_nil, s,
          Int.cast_sub, Int.cast_neg, Int.cast_natCast, pow_zero, pow_one, mul_one, zero_add]
        field_simp [hsDen_pos.ne']; ring
      have hg2_ev : ∀ a b d : ℝ, evalPoly3 (polyG2_6 c.sNum c.sDen) a b d =
          (c.sDen : ℝ) * (c.sDen : ℝ) * (c.s - b) * (c.s - d) := by
        intro a b d
        simp only [polyG2_6, evalPoly3, List.foldl_cons, List.foldl_nil, s,
          Int.cast_mul, Int.cast_neg, Int.cast_natCast, pow_zero, pow_one, mul_one, zero_add]
        field_simp [hsDen_pos.ne']; ring
      have hDelta_nn : ∀ a b d, InThreePointDomain c.s a b d → 0 ≤ evalPoly3 polyDelta6 a b d := by
        intro a b d hd; rw [hDelta_ev]; exact hd.2.2.2.2.2.2
      have hg1_nn : ∀ a b d, InThreePointDomain c.s a b d → 0 ≤ evalPoly3 (polyG1_6 c.sNum c.sDen) a b d := by
        intro a b d hd; rw [hg1_ev]
        have h1 : 0 ≤ c.s - a := by linarith [hd.2.1]
        have h2' : 0 ≤ a + 1 := by linarith [hd.1]
        positivity
      have hg2_nn : ∀ a b d, InThreePointDomain c.s a b d → 0 ≤ evalPoly3 (polyG2_6 c.sNum c.sDen) a b d := by
        intro a b d hd; rw [hg2_ev]
        have h1 : 0 ≤ c.s - b := by linarith [hd.2.2.2.1]
        have h2' : 0 ≤ c.s - d := by linarith [hd.2.2.2.2.2.1]
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
      have hq0 := hterm_nn _ (fun a b d _ => evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM0) c.b0 a b d)
      have hq1 := hterm_nn _ (fun a b d _ => evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM1) c.b1 a b d)
      have hq2 := hterm_nn _ (fun a b d _ => evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM2) c.b2 a b d)
      have hq3 := hterm_nn _ (fun a b d hd => by
        rw [evalPoly3_mulPoly3Sorted]
        exact mul_nonneg (hDelta_nn a b d hd) (evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM3) c.b3 a b d))
      have hq4 := hterm_nn _ (fun a b d hd => by
        rw [evalPoly3_mulPoly3Sorted]
        exact mul_nonneg (hDelta_nn a b d hd) (evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM4) c.b4 a b d))
      have hq5 := hterm_nn _ (fun a b d hd => by
        rw [evalPoly3_mulPoly3Sorted]
        exact mul_nonneg (hDelta_nn a b d hd) (evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM5) c.b5 a b d))
      have hq6 := hterm_nn _ (fun a b d hd => by
        rw [evalPoly3_mulPoly3Sorted]
        exact mul_nonneg (hg1_nn a b d hd) (evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM6) c.b6 a b d))
      have hq7 := hterm_nn _ (fun a b d hd => by
        rw [evalPoly3_mulPoly3Sorted]
        exact mul_nonneg (hg1_nn a b d hd) (evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM7) c.b7 a b d))
      have hq8 := hterm_nn _ (fun a b d hd => by
        rw [evalPoly3_mulPoly3Sorted]
        exact mul_nonneg (hg2_nn a b d hd) (evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM8) c.b8 a b d))
      have hq9 := hterm_nn _ (fun a b d hd => by
        rw [evalPoly3_mulPoly3Sorted]
        exact mul_nonneg (hg2_nn a b d hd) (evalPoly3_quadPoly3_nonneg hdS (isCholeskyDDValid_sound hM9) c.b9 a b d))
      push_cast
      have hsD2_nn : (0 : ℝ) ≤ (c.sDen : ℝ) * (c.sDen : ℝ) := by positivity
      have hsD_nn : (0 : ℝ) ≤ (c.sDen : ℝ) := by positivity
      nlinarith
    have hcoeff_pos : (0 : ℝ) < (c.sDen : ℝ) * (c.sDen : ℝ) * (c.dS : ℝ) * (c.dK : ℝ) := by positivity
    rw [hlhs_eval] at hsym_eq
    nlinarith
  have hbound := bachocVallentin_bound_with_legendre c.toRealF hF c.toRealC2 hc2 h2 h3 hp
  rw [bound_eq_sum c hdK]
  exact hbound

end BVCert6

end Geodesy.Spherical
