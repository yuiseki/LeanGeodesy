import LeanGeodesy.Spherical.BachocVallentin

/-!
# Legendre polynomials `P₀..P₁₂` and positive semidefiniteness on `S²`

We prove positive semidefiniteness of the Legendre polynomials `P₀..P₁₂` on `S²`
via the algebraic addition theorem in terms of the already-formalized Chebyshev
three-point kernel `bvQ`:

```
P_k(t) = P_k(u) P_k(v) + ∑_{m=1}^k (2 (k-m)! / (k+m)!) P_k^{(m)}(u) P_k^{(m)}(v) bvQ m u v t
```

Since `bvQ m ⟪x₀, y⟫ ⟪x₀, z⟫ ⟪y, z⟫ = Re((w_{x₀} y)^m * conj(w_{x₀} z)^m)` for any
base point `x₀ ∈ S²` (already proved in `BachocVallentin.lean`), each summand is a
nonnegative sum of squares over any finite configuration `p : Fin n → UnitSphere`.

We also provide `bachocVallentin_bound_with_legendre`, combining arbitrary-degree
three-point SDP kernels `bvQ` with nonnegative two-point Legendre terms `P₁..P₁₂`.
-/

namespace Geodesy.Spherical

open scoped BigOperators RealInnerProductSpace

/-- Explicit Legendre polynomials `P_k(t)` for `0 ≤ k ≤ 12` (and `0` for `k > 12`). -/
noncomputable def legendreP12 : ℕ → ℝ → ℝ
  | 0, _ => (1 : ℝ)
  | 1, t => (1 : ℝ) * t
  | 2, t => (3 / 2 : ℝ) * t ^ 2 + (-1 / 2 : ℝ)
  | 3, t => (5 / 2 : ℝ) * t ^ 3 + (-3 / 2 : ℝ) * t
  | 4, t => (35 / 8 : ℝ) * t ^ 4 + (-15 / 4 : ℝ) * t ^ 2 + (3 / 8 : ℝ)
  | 5, t => (63 / 8 : ℝ) * t ^ 5 + (-35 / 4 : ℝ) * t ^ 3 + (15 / 8 : ℝ) * t
  | 6, t => (231 / 16 : ℝ) * t ^ 6 + (-315 / 16 : ℝ) * t ^ 4 + (105 / 16 : ℝ) * t ^ 2 + (-5 / 16 : ℝ)
  | 7, t => (429 / 16 : ℝ) * t ^ 7 + (-693 / 16 : ℝ) * t ^ 5 + (315 / 16 : ℝ) * t ^ 3 + (-35 / 16 : ℝ) * t
  | 8, t => (6435 / 128 : ℝ) * t ^ 8 + (-3003 / 32 : ℝ) * t ^ 6 + (3465 / 64 : ℝ) * t ^ 4 + (-315 / 32 : ℝ) * t ^ 2 + (35 / 128 : ℝ)
  | 9, t => (12155 / 128 : ℝ) * t ^ 9 + (-6435 / 32 : ℝ) * t ^ 7 + (9009 / 64 : ℝ) * t ^ 5 + (-1155 / 32 : ℝ) * t ^ 3 + (315 / 128 : ℝ) * t
  | 10, t => (46189 / 256 : ℝ) * t ^ 10 + (-109395 / 256 : ℝ) * t ^ 8 + (45045 / 128 : ℝ) * t ^ 6 + (-15015 / 128 : ℝ) * t ^ 4 + (3465 / 256 : ℝ) * t ^ 2 + (-63 / 256 : ℝ)
  | 11, t => (88179 / 256 : ℝ) * t ^ 11 + (-230945 / 256 : ℝ) * t ^ 9 + (109395 / 128 : ℝ) * t ^ 7 + (-45045 / 128 : ℝ) * t ^ 5 + (15015 / 256 : ℝ) * t ^ 3 + (-693 / 256 : ℝ) * t
  | 12, t => (676039 / 1024 : ℝ) * t ^ 12 + (-969969 / 512 : ℝ) * t ^ 10 + (2078505 / 1024 : ℝ) * t ^ 8 + (-255255 / 256 : ℝ) * t ^ 6 + (225225 / 1024 : ℝ) * t ^ 4 + (-9009 / 512 : ℝ) * t ^ 2 + (231 / 1024 : ℝ)
  | _, _ => 0

/-- Every `legendreP12 k` evaluates to `1` at `t = 1` for `k ≤ 12`. -/
theorem legendreP12_one {k : ℕ} (hk : k ≤ 12) : legendreP12 k 1 = 1 := by
  interval_cases k <;> simp [legendreP12] <;> norm_num

/-- Nonnegativity of `∑ i, ∑ j, c * (f(⟪x₀, p i⟫) * f(⟪x₀, p j⟫) * bvQ m ⟪x₀, p i⟫ ⟪x₀, p j⟫ ⟪p i, p j⟫)`
for `0 ≤ c`, any base point `x₀ ∈ S²`, any function `f : ℝ → ℝ`, and any `m : ℕ`. -/
private theorem sum_bvQ_weighted_nonneg {n : ℕ} (p : Fin n → UnitSphere)
    (x0 : UnitSphere) (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ) (m : ℕ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      c * (f ⟪x0.val, (p i).val⟫ * f ⟪x0.val, (p j).val⟫ *
        bvQ m ⟪x0.val, (p i).val⟫ ⟪x0.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫) := by
  simp_rw [← Finset.mul_sum]
  refine mul_nonneg hc ?_
  obtain ⟨e1, e2, hframe⟩ := exists_tangent_frame x0
  let w : UnitSphere → ℂ := fun y => ⟨⟪y.val, e1⟫, ⟪y.val, e2⟫⟩
  have hterm : ∀ i j : Fin n,
      f ⟪x0.val, (p i).val⟫ * f ⟪x0.val, (p j).val⟫ *
        bvQ m ⟪x0.val, (p i).val⟫ ⟪x0.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫ =
      (f ⟪x0.val, (p i).val⟫ * ((w (p i)) ^ m).re) * (f ⟪x0.val, (p j).val⟫ * ((w (p j)) ^ m).re) +
      (f ⟪x0.val, (p i).val⟫ * ((w (p i)) ^ m).im) * (f ⟪x0.val, (p j).val⟫ * ((w (p j)) ^ m).im) := by
    intro i j
    have hq := bvQ_eq_re_complex x0 (p i) (p j) e1 e2 hframe m
    rw [hq]
    simp only [w, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [hterm, Finset.sum_add_distrib]
  have hsq : ∀ (g : Fin n → ℝ), 0 ≤ ∑ i : Fin n, ∑ j : Fin n, g i * g j := fun g => by
    have : ∑ i : Fin n, ∑ j : Fin n, g i * g j = (∑ i : Fin n, g i) ^ 2 := by
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    rw [this]; exact sq_nonneg _
  exact add_nonneg (hsq _) (hsq _)

private theorem sum_prod_sq_nonneg {n : ℕ} (g : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, g i * g j := by
  have : ∑ i : Fin n, ∑ j : Fin n, g i * g j = (∑ i : Fin n, g i) ^ 2 := by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [this]; exact sq_nonneg _

private def northPoleS2 : UnitSphere :=
  ⟨WithLp.toLp 2 (fun i : Fin 3 => if i = (2 : Fin 3) then (1 : ℝ) else 0), by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    norm_num⟩

private theorem legendreP12_add_0 (_u _v t : ℝ) :
    legendreP12 0 t =
      ((1 : ℝ)) * ((1 : ℝ)) := by
  simp only [legendreP12]
  ring

private theorem sum_legendreP12_nonneg_0 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 0 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_0 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h]
  exact sum_prod_sq_nonneg (fun _ => (1 : ℝ))

private theorem legendreP12_add_1 (u v t : ℝ) :
    legendreP12 1 t =
      ((1 : ℝ) * u) * ((1 : ℝ) * v)
      + (1 : ℝ) * (((1 : ℝ)) * ((1 : ℝ)) * bvQ 1 u v t) := by
  simp only [legendreP12, bvQ]
  ring

private theorem sum_legendreP12_nonneg_1 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 1 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_1 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h, Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((1 : ℝ) * ⟪northPoleS2.val, (p i).val⟫) *
      ((1 : ℝ) * ⟪northPoleS2.val, (p j).val⟫) :=
    sum_prod_sq_nonneg (fun i => (1 : ℝ) * ⟪northPoleS2.val, (p i).val⟫)
  have h1 := sum_bvQ_weighted_nonneg p northPoleS2 (1 : ℝ) (by norm_num) (fun u => (1 : ℝ)) 1
  exact add_nonneg (h0) h1

private theorem legendreP12_add_2 (u v t : ℝ) :
    legendreP12 2 t =
      ((3 / 2 : ℝ) * u ^ 2 + (-1 / 2 : ℝ)) * ((3 / 2 : ℝ) * v ^ 2 + (-1 / 2 : ℝ))
      + (1 / 3 : ℝ) * (((3 : ℝ) * u) * ((3 : ℝ) * v) * bvQ 1 u v t)
      + (1 / 12 : ℝ) * (((3 : ℝ)) * ((3 : ℝ)) * bvQ 2 u v t) := by
  simp only [legendreP12, bvQ]
  ring

private theorem sum_legendreP12_nonneg_2 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 2 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_2 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h, Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((3 / 2 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 2 + (-1 / 2 : ℝ)) *
      ((3 / 2 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 2 + (-1 / 2 : ℝ)) :=
    sum_prod_sq_nonneg (fun i => (3 / 2 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 2 + (-1 / 2 : ℝ))
  have h1 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 3 : ℝ) (by norm_num) (fun u => (3 : ℝ) * u) 1
  have h2 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 12 : ℝ) (by norm_num) (fun u => (3 : ℝ)) 2
  exact add_nonneg (add_nonneg (h0) h1) h2

private theorem legendreP12_add_3 (u v t : ℝ) :
    legendreP12 3 t =
      ((5 / 2 : ℝ) * u ^ 3 + (-3 / 2 : ℝ) * u) * ((5 / 2 : ℝ) * v ^ 3 + (-3 / 2 : ℝ) * v)
      + (1 / 6 : ℝ) * (((15 / 2 : ℝ) * u ^ 2 + (-3 / 2 : ℝ)) * ((15 / 2 : ℝ) * v ^ 2 + (-3 / 2 : ℝ)) * bvQ 1 u v t)
      + (1 / 60 : ℝ) * (((15 : ℝ) * u) * ((15 : ℝ) * v) * bvQ 2 u v t)
      + (1 / 360 : ℝ) * (((15 : ℝ)) * ((15 : ℝ)) * bvQ 3 u v t) := by
  simp only [legendreP12, bvQ]
  ring

private theorem sum_legendreP12_nonneg_3 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 3 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_3 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h, Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((5 / 2 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 3 + (-3 / 2 : ℝ) * ⟪northPoleS2.val, (p i).val⟫) *
      ((5 / 2 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 3 + (-3 / 2 : ℝ) * ⟪northPoleS2.val, (p j).val⟫) :=
    sum_prod_sq_nonneg (fun i => (5 / 2 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 3 + (-3 / 2 : ℝ) * ⟪northPoleS2.val, (p i).val⟫)
  have h1 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 6 : ℝ) (by norm_num) (fun u => (15 / 2 : ℝ) * u ^ 2 + (-3 / 2 : ℝ)) 1
  have h2 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 60 : ℝ) (by norm_num) (fun u => (15 : ℝ) * u) 2
  have h3 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 360 : ℝ) (by norm_num) (fun u => (15 : ℝ)) 3
  exact add_nonneg (add_nonneg (add_nonneg (h0) h1) h2) h3

private theorem legendreP12_add_4 (u v t : ℝ) :
    legendreP12 4 t =
      ((35 / 8 : ℝ) * u ^ 4 + (-15 / 4 : ℝ) * u ^ 2 + (3 / 8 : ℝ)) * ((35 / 8 : ℝ) * v ^ 4 + (-15 / 4 : ℝ) * v ^ 2 + (3 / 8 : ℝ))
      + (1 / 10 : ℝ) * (((35 / 2 : ℝ) * u ^ 3 + (-15 / 2 : ℝ) * u) * ((35 / 2 : ℝ) * v ^ 3 + (-15 / 2 : ℝ) * v) * bvQ 1 u v t)
      + (1 / 180 : ℝ) * (((105 / 2 : ℝ) * u ^ 2 + (-15 / 2 : ℝ)) * ((105 / 2 : ℝ) * v ^ 2 + (-15 / 2 : ℝ)) * bvQ 2 u v t)
      + (1 / 2520 : ℝ) * (((105 : ℝ) * u) * ((105 : ℝ) * v) * bvQ 3 u v t)
      + (1 / 20160 : ℝ) * (((105 : ℝ)) * ((105 : ℝ)) * bvQ 4 u v t) := by
  simp only [legendreP12, bvQ]
  ring

private theorem sum_legendreP12_nonneg_4 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 4 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_4 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h, Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((35 / 8 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 4 + (-15 / 4 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 2 + (3 / 8 : ℝ)) *
      ((35 / 8 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 4 + (-15 / 4 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 2 + (3 / 8 : ℝ)) :=
    sum_prod_sq_nonneg (fun i => (35 / 8 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 4 + (-15 / 4 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 2 + (3 / 8 : ℝ))
  have h1 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 10 : ℝ) (by norm_num) (fun u => (35 / 2 : ℝ) * u ^ 3 + (-15 / 2 : ℝ) * u) 1
  have h2 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 180 : ℝ) (by norm_num) (fun u => (105 / 2 : ℝ) * u ^ 2 + (-15 / 2 : ℝ)) 2
  have h3 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 2520 : ℝ) (by norm_num) (fun u => (105 : ℝ) * u) 3
  have h4 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 20160 : ℝ) (by norm_num) (fun u => (105 : ℝ)) 4
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (h0) h1) h2) h3) h4

private theorem legendreP12_add_5 (u v t : ℝ) :
    legendreP12 5 t =
      ((63 / 8 : ℝ) * u ^ 5 + (-35 / 4 : ℝ) * u ^ 3 + (15 / 8 : ℝ) * u) * ((63 / 8 : ℝ) * v ^ 5 + (-35 / 4 : ℝ) * v ^ 3 + (15 / 8 : ℝ) * v)
      + (1 / 15 : ℝ) * (((315 / 8 : ℝ) * u ^ 4 + (-105 / 4 : ℝ) * u ^ 2 + (15 / 8 : ℝ)) * ((315 / 8 : ℝ) * v ^ 4 + (-105 / 4 : ℝ) * v ^ 2 + (15 / 8 : ℝ)) * bvQ 1 u v t)
      + (1 / 420 : ℝ) * (((315 / 2 : ℝ) * u ^ 3 + (-105 / 2 : ℝ) * u) * ((315 / 2 : ℝ) * v ^ 3 + (-105 / 2 : ℝ) * v) * bvQ 2 u v t)
      + (1 / 10080 : ℝ) * (((945 / 2 : ℝ) * u ^ 2 + (-105 / 2 : ℝ)) * ((945 / 2 : ℝ) * v ^ 2 + (-105 / 2 : ℝ)) * bvQ 3 u v t)
      + (1 / 181440 : ℝ) * (((945 : ℝ) * u) * ((945 : ℝ) * v) * bvQ 4 u v t)
      + (1 / 1814400 : ℝ) * (((945 : ℝ)) * ((945 : ℝ)) * bvQ 5 u v t) := by
  simp only [legendreP12, bvQ]
  ring

private theorem sum_legendreP12_nonneg_5 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 5 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_5 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h, Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((63 / 8 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 5 + (-35 / 4 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 3 + (15 / 8 : ℝ) * ⟪northPoleS2.val, (p i).val⟫) *
      ((63 / 8 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 5 + (-35 / 4 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 3 + (15 / 8 : ℝ) * ⟪northPoleS2.val, (p j).val⟫) :=
    sum_prod_sq_nonneg (fun i => (63 / 8 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 5 + (-35 / 4 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 3 + (15 / 8 : ℝ) * ⟪northPoleS2.val, (p i).val⟫)
  have h1 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 15 : ℝ) (by norm_num) (fun u => (315 / 8 : ℝ) * u ^ 4 + (-105 / 4 : ℝ) * u ^ 2 + (15 / 8 : ℝ)) 1
  have h2 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 420 : ℝ) (by norm_num) (fun u => (315 / 2 : ℝ) * u ^ 3 + (-105 / 2 : ℝ) * u) 2
  have h3 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 10080 : ℝ) (by norm_num) (fun u => (945 / 2 : ℝ) * u ^ 2 + (-105 / 2 : ℝ)) 3
  have h4 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 181440 : ℝ) (by norm_num) (fun u => (945 : ℝ) * u) 4
  have h5 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 1814400 : ℝ) (by norm_num) (fun u => (945 : ℝ)) 5
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (h0) h1) h2) h3) h4) h5

private theorem legendreP12_add_6 (u v t : ℝ) :
    legendreP12 6 t =
      ((231 / 16 : ℝ) * u ^ 6 + (-315 / 16 : ℝ) * u ^ 4 + (105 / 16 : ℝ) * u ^ 2 + (-5 / 16 : ℝ)) * ((231 / 16 : ℝ) * v ^ 6 + (-315 / 16 : ℝ) * v ^ 4 + (105 / 16 : ℝ) * v ^ 2 + (-5 / 16 : ℝ))
      + (1 / 21 : ℝ) * (((693 / 8 : ℝ) * u ^ 5 + (-315 / 4 : ℝ) * u ^ 3 + (105 / 8 : ℝ) * u) * ((693 / 8 : ℝ) * v ^ 5 + (-315 / 4 : ℝ) * v ^ 3 + (105 / 8 : ℝ) * v) * bvQ 1 u v t)
      + (1 / 840 : ℝ) * (((3465 / 8 : ℝ) * u ^ 4 + (-945 / 4 : ℝ) * u ^ 2 + (105 / 8 : ℝ)) * ((3465 / 8 : ℝ) * v ^ 4 + (-945 / 4 : ℝ) * v ^ 2 + (105 / 8 : ℝ)) * bvQ 2 u v t)
      + (1 / 30240 : ℝ) * (((3465 / 2 : ℝ) * u ^ 3 + (-945 / 2 : ℝ) * u) * ((3465 / 2 : ℝ) * v ^ 3 + (-945 / 2 : ℝ) * v) * bvQ 3 u v t)
      + (1 / 907200 : ℝ) * (((10395 / 2 : ℝ) * u ^ 2 + (-945 / 2 : ℝ)) * ((10395 / 2 : ℝ) * v ^ 2 + (-945 / 2 : ℝ)) * bvQ 4 u v t)
      + (1 / 19958400 : ℝ) * (((10395 : ℝ) * u) * ((10395 : ℝ) * v) * bvQ 5 u v t)
      + (1 / 239500800 : ℝ) * (((10395 : ℝ)) * ((10395 : ℝ)) * bvQ 6 u v t) := by
  simp only [legendreP12, bvQ]
  ring

private theorem sum_legendreP12_nonneg_6 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 6 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_6 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h, Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((231 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 6 + (-315 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 4 + (105 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 2 + (-5 / 16 : ℝ)) *
      ((231 / 16 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 6 + (-315 / 16 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 4 + (105 / 16 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 2 + (-5 / 16 : ℝ)) :=
    sum_prod_sq_nonneg (fun i => (231 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 6 + (-315 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 4 + (105 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 2 + (-5 / 16 : ℝ))
  have h1 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 21 : ℝ) (by norm_num) (fun u => (693 / 8 : ℝ) * u ^ 5 + (-315 / 4 : ℝ) * u ^ 3 + (105 / 8 : ℝ) * u) 1
  have h2 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 840 : ℝ) (by norm_num) (fun u => (3465 / 8 : ℝ) * u ^ 4 + (-945 / 4 : ℝ) * u ^ 2 + (105 / 8 : ℝ)) 2
  have h3 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 30240 : ℝ) (by norm_num) (fun u => (3465 / 2 : ℝ) * u ^ 3 + (-945 / 2 : ℝ) * u) 3
  have h4 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 907200 : ℝ) (by norm_num) (fun u => (10395 / 2 : ℝ) * u ^ 2 + (-945 / 2 : ℝ)) 4
  have h5 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 19958400 : ℝ) (by norm_num) (fun u => (10395 : ℝ) * u) 5
  have h6 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 239500800 : ℝ) (by norm_num) (fun u => (10395 : ℝ)) 6
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (h0) h1) h2) h3) h4) h5) h6

private theorem legendreP12_add_7 (u v t : ℝ) :
    legendreP12 7 t =
      ((429 / 16 : ℝ) * u ^ 7 + (-693 / 16 : ℝ) * u ^ 5 + (315 / 16 : ℝ) * u ^ 3 + (-35 / 16 : ℝ) * u) * ((429 / 16 : ℝ) * v ^ 7 + (-693 / 16 : ℝ) * v ^ 5 + (315 / 16 : ℝ) * v ^ 3 + (-35 / 16 : ℝ) * v)
      + (1 / 28 : ℝ) * (((3003 / 16 : ℝ) * u ^ 6 + (-3465 / 16 : ℝ) * u ^ 4 + (945 / 16 : ℝ) * u ^ 2 + (-35 / 16 : ℝ)) * ((3003 / 16 : ℝ) * v ^ 6 + (-3465 / 16 : ℝ) * v ^ 4 + (945 / 16 : ℝ) * v ^ 2 + (-35 / 16 : ℝ)) * bvQ 1 u v t)
      + (1 / 1512 : ℝ) * (((9009 / 8 : ℝ) * u ^ 5 + (-3465 / 4 : ℝ) * u ^ 3 + (945 / 8 : ℝ) * u) * ((9009 / 8 : ℝ) * v ^ 5 + (-3465 / 4 : ℝ) * v ^ 3 + (945 / 8 : ℝ) * v) * bvQ 2 u v t)
      + (1 / 75600 : ℝ) * (((45045 / 8 : ℝ) * u ^ 4 + (-10395 / 4 : ℝ) * u ^ 2 + (945 / 8 : ℝ)) * ((45045 / 8 : ℝ) * v ^ 4 + (-10395 / 4 : ℝ) * v ^ 2 + (945 / 8 : ℝ)) * bvQ 3 u v t)
      + (1 / 3326400 : ℝ) * (((45045 / 2 : ℝ) * u ^ 3 + (-10395 / 2 : ℝ) * u) * ((45045 / 2 : ℝ) * v ^ 3 + (-10395 / 2 : ℝ) * v) * bvQ 4 u v t)
      + (1 / 119750400 : ℝ) * (((135135 / 2 : ℝ) * u ^ 2 + (-10395 / 2 : ℝ)) * ((135135 / 2 : ℝ) * v ^ 2 + (-10395 / 2 : ℝ)) * bvQ 5 u v t)
      + (1 / 3113510400 : ℝ) * (((135135 : ℝ) * u) * ((135135 : ℝ) * v) * bvQ 6 u v t)
      + (1 / 43589145600 : ℝ) * (((135135 : ℝ)) * ((135135 : ℝ)) * bvQ 7 u v t) := by
  simp only [legendreP12, bvQ]
  ring

private theorem sum_legendreP12_nonneg_7 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 7 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_7 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h, Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((429 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 7 + (-693 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 5 + (315 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 3 + (-35 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫) *
      ((429 / 16 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 7 + (-693 / 16 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 5 + (315 / 16 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 3 + (-35 / 16 : ℝ) * ⟪northPoleS2.val, (p j).val⟫) :=
    sum_prod_sq_nonneg (fun i => (429 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 7 + (-693 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 5 + (315 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 3 + (-35 / 16 : ℝ) * ⟪northPoleS2.val, (p i).val⟫)
  have h1 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 28 : ℝ) (by norm_num) (fun u => (3003 / 16 : ℝ) * u ^ 6 + (-3465 / 16 : ℝ) * u ^ 4 + (945 / 16 : ℝ) * u ^ 2 + (-35 / 16 : ℝ)) 1
  have h2 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 1512 : ℝ) (by norm_num) (fun u => (9009 / 8 : ℝ) * u ^ 5 + (-3465 / 4 : ℝ) * u ^ 3 + (945 / 8 : ℝ) * u) 2
  have h3 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 75600 : ℝ) (by norm_num) (fun u => (45045 / 8 : ℝ) * u ^ 4 + (-10395 / 4 : ℝ) * u ^ 2 + (945 / 8 : ℝ)) 3
  have h4 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 3326400 : ℝ) (by norm_num) (fun u => (45045 / 2 : ℝ) * u ^ 3 + (-10395 / 2 : ℝ) * u) 4
  have h5 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 119750400 : ℝ) (by norm_num) (fun u => (135135 / 2 : ℝ) * u ^ 2 + (-10395 / 2 : ℝ)) 5
  have h6 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 3113510400 : ℝ) (by norm_num) (fun u => (135135 : ℝ) * u) 6
  have h7 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 43589145600 : ℝ) (by norm_num) (fun u => (135135 : ℝ)) 7
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (h0) h1) h2) h3) h4) h5) h6) h7

private theorem legendreP12_add_8 (u v t : ℝ) :
    legendreP12 8 t =
      ((6435 / 128 : ℝ) * u ^ 8 + (-3003 / 32 : ℝ) * u ^ 6 + (3465 / 64 : ℝ) * u ^ 4 + (-315 / 32 : ℝ) * u ^ 2 + (35 / 128 : ℝ)) * ((6435 / 128 : ℝ) * v ^ 8 + (-3003 / 32 : ℝ) * v ^ 6 + (3465 / 64 : ℝ) * v ^ 4 + (-315 / 32 : ℝ) * v ^ 2 + (35 / 128 : ℝ))
      + (1 / 36 : ℝ) * (((6435 / 16 : ℝ) * u ^ 7 + (-9009 / 16 : ℝ) * u ^ 5 + (3465 / 16 : ℝ) * u ^ 3 + (-315 / 16 : ℝ) * u) * ((6435 / 16 : ℝ) * v ^ 7 + (-9009 / 16 : ℝ) * v ^ 5 + (3465 / 16 : ℝ) * v ^ 3 + (-315 / 16 : ℝ) * v) * bvQ 1 u v t)
      + (1 / 2520 : ℝ) * (((45045 / 16 : ℝ) * u ^ 6 + (-45045 / 16 : ℝ) * u ^ 4 + (10395 / 16 : ℝ) * u ^ 2 + (-315 / 16 : ℝ)) * ((45045 / 16 : ℝ) * v ^ 6 + (-45045 / 16 : ℝ) * v ^ 4 + (10395 / 16 : ℝ) * v ^ 2 + (-315 / 16 : ℝ)) * bvQ 2 u v t)
      + (1 / 166320 : ℝ) * (((135135 / 8 : ℝ) * u ^ 5 + (-45045 / 4 : ℝ) * u ^ 3 + (10395 / 8 : ℝ) * u) * ((135135 / 8 : ℝ) * v ^ 5 + (-45045 / 4 : ℝ) * v ^ 3 + (10395 / 8 : ℝ) * v) * bvQ 3 u v t)
      + (1 / 9979200 : ℝ) * (((675675 / 8 : ℝ) * u ^ 4 + (-135135 / 4 : ℝ) * u ^ 2 + (10395 / 8 : ℝ)) * ((675675 / 8 : ℝ) * v ^ 4 + (-135135 / 4 : ℝ) * v ^ 2 + (10395 / 8 : ℝ)) * bvQ 4 u v t)
      + (1 / 518918400 : ℝ) * (((675675 / 2 : ℝ) * u ^ 3 + (-135135 / 2 : ℝ) * u) * ((675675 / 2 : ℝ) * v ^ 3 + (-135135 / 2 : ℝ) * v) * bvQ 5 u v t)
      + (1 / 21794572800 : ℝ) * (((2027025 / 2 : ℝ) * u ^ 2 + (-135135 / 2 : ℝ)) * ((2027025 / 2 : ℝ) * v ^ 2 + (-135135 / 2 : ℝ)) * bvQ 6 u v t)
      + (1 / 653837184000 : ℝ) * (((2027025 : ℝ) * u) * ((2027025 : ℝ) * v) * bvQ 7 u v t)
      + (1 / 10461394944000 : ℝ) * (((2027025 : ℝ)) * ((2027025 : ℝ)) * bvQ 8 u v t) := by
  simp only [legendreP12, bvQ]
  ring

private theorem sum_legendreP12_nonneg_8 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 8 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_8 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h, Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((6435 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 8 + (-3003 / 32 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 6 + (3465 / 64 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 4 + (-315 / 32 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 2 + (35 / 128 : ℝ)) *
      ((6435 / 128 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 8 + (-3003 / 32 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 6 + (3465 / 64 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 4 + (-315 / 32 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 2 + (35 / 128 : ℝ)) :=
    sum_prod_sq_nonneg (fun i => (6435 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 8 + (-3003 / 32 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 6 + (3465 / 64 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 4 + (-315 / 32 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 2 + (35 / 128 : ℝ))
  have h1 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 36 : ℝ) (by norm_num) (fun u => (6435 / 16 : ℝ) * u ^ 7 + (-9009 / 16 : ℝ) * u ^ 5 + (3465 / 16 : ℝ) * u ^ 3 + (-315 / 16 : ℝ) * u) 1
  have h2 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 2520 : ℝ) (by norm_num) (fun u => (45045 / 16 : ℝ) * u ^ 6 + (-45045 / 16 : ℝ) * u ^ 4 + (10395 / 16 : ℝ) * u ^ 2 + (-315 / 16 : ℝ)) 2
  have h3 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 166320 : ℝ) (by norm_num) (fun u => (135135 / 8 : ℝ) * u ^ 5 + (-45045 / 4 : ℝ) * u ^ 3 + (10395 / 8 : ℝ) * u) 3
  have h4 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 9979200 : ℝ) (by norm_num) (fun u => (675675 / 8 : ℝ) * u ^ 4 + (-135135 / 4 : ℝ) * u ^ 2 + (10395 / 8 : ℝ)) 4
  have h5 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 518918400 : ℝ) (by norm_num) (fun u => (675675 / 2 : ℝ) * u ^ 3 + (-135135 / 2 : ℝ) * u) 5
  have h6 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 21794572800 : ℝ) (by norm_num) (fun u => (2027025 / 2 : ℝ) * u ^ 2 + (-135135 / 2 : ℝ)) 6
  have h7 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 653837184000 : ℝ) (by norm_num) (fun u => (2027025 : ℝ) * u) 7
  have h8 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 10461394944000 : ℝ) (by norm_num) (fun u => (2027025 : ℝ)) 8
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (h0) h1) h2) h3) h4) h5) h6) h7) h8

private theorem legendreP12_add_9 (u v t : ℝ) :
    legendreP12 9 t =
      ((12155 / 128 : ℝ) * u ^ 9 + (-6435 / 32 : ℝ) * u ^ 7 + (9009 / 64 : ℝ) * u ^ 5 + (-1155 / 32 : ℝ) * u ^ 3 + (315 / 128 : ℝ) * u) * ((12155 / 128 : ℝ) * v ^ 9 + (-6435 / 32 : ℝ) * v ^ 7 + (9009 / 64 : ℝ) * v ^ 5 + (-1155 / 32 : ℝ) * v ^ 3 + (315 / 128 : ℝ) * v)
      + (1 / 45 : ℝ) * (((109395 / 128 : ℝ) * u ^ 8 + (-45045 / 32 : ℝ) * u ^ 6 + (45045 / 64 : ℝ) * u ^ 4 + (-3465 / 32 : ℝ) * u ^ 2 + (315 / 128 : ℝ)) * ((109395 / 128 : ℝ) * v ^ 8 + (-45045 / 32 : ℝ) * v ^ 6 + (45045 / 64 : ℝ) * v ^ 4 + (-3465 / 32 : ℝ) * v ^ 2 + (315 / 128 : ℝ)) * bvQ 1 u v t)
      + (1 / 3960 : ℝ) * (((109395 / 16 : ℝ) * u ^ 7 + (-135135 / 16 : ℝ) * u ^ 5 + (45045 / 16 : ℝ) * u ^ 3 + (-3465 / 16 : ℝ) * u) * ((109395 / 16 : ℝ) * v ^ 7 + (-135135 / 16 : ℝ) * v ^ 5 + (45045 / 16 : ℝ) * v ^ 3 + (-3465 / 16 : ℝ) * v) * bvQ 2 u v t)
      + (1 / 332640 : ℝ) * (((765765 / 16 : ℝ) * u ^ 6 + (-675675 / 16 : ℝ) * u ^ 4 + (135135 / 16 : ℝ) * u ^ 2 + (-3465 / 16 : ℝ)) * ((765765 / 16 : ℝ) * v ^ 6 + (-675675 / 16 : ℝ) * v ^ 4 + (135135 / 16 : ℝ) * v ^ 2 + (-3465 / 16 : ℝ)) * bvQ 3 u v t)
      + (1 / 25945920 : ℝ) * (((2297295 / 8 : ℝ) * u ^ 5 + (-675675 / 4 : ℝ) * u ^ 3 + (135135 / 8 : ℝ) * u) * ((2297295 / 8 : ℝ) * v ^ 5 + (-675675 / 4 : ℝ) * v ^ 3 + (135135 / 8 : ℝ) * v) * bvQ 4 u v t)
      + (1 / 1816214400 : ℝ) * (((11486475 / 8 : ℝ) * u ^ 4 + (-2027025 / 4 : ℝ) * u ^ 2 + (135135 / 8 : ℝ)) * ((11486475 / 8 : ℝ) * v ^ 4 + (-2027025 / 4 : ℝ) * v ^ 2 + (135135 / 8 : ℝ)) * bvQ 5 u v t)
      + (1 / 108972864000 : ℝ) * (((11486475 / 2 : ℝ) * u ^ 3 + (-2027025 / 2 : ℝ) * u) * ((11486475 / 2 : ℝ) * v ^ 3 + (-2027025 / 2 : ℝ) * v) * bvQ 6 u v t)
      + (1 / 5230697472000 : ℝ) * (((34459425 / 2 : ℝ) * u ^ 2 + (-2027025 / 2 : ℝ)) * ((34459425 / 2 : ℝ) * v ^ 2 + (-2027025 / 2 : ℝ)) * bvQ 7 u v t)
      + (1 / 177843714048000 : ℝ) * (((34459425 : ℝ) * u) * ((34459425 : ℝ) * v) * bvQ 8 u v t)
      + (1 / 3201186852864000 : ℝ) * (((34459425 : ℝ)) * ((34459425 : ℝ)) * bvQ 9 u v t) := by
  simp only [legendreP12, bvQ]
  ring

private theorem sum_legendreP12_nonneg_9 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 9 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_9 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h, Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((12155 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 9 + (-6435 / 32 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 7 + (9009 / 64 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 5 + (-1155 / 32 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 3 + (315 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫) *
      ((12155 / 128 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 9 + (-6435 / 32 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 7 + (9009 / 64 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 5 + (-1155 / 32 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 3 + (315 / 128 : ℝ) * ⟪northPoleS2.val, (p j).val⟫) :=
    sum_prod_sq_nonneg (fun i => (12155 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 9 + (-6435 / 32 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 7 + (9009 / 64 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 5 + (-1155 / 32 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 3 + (315 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫)
  have h1 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 45 : ℝ) (by norm_num) (fun u => (109395 / 128 : ℝ) * u ^ 8 + (-45045 / 32 : ℝ) * u ^ 6 + (45045 / 64 : ℝ) * u ^ 4 + (-3465 / 32 : ℝ) * u ^ 2 + (315 / 128 : ℝ)) 1
  have h2 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 3960 : ℝ) (by norm_num) (fun u => (109395 / 16 : ℝ) * u ^ 7 + (-135135 / 16 : ℝ) * u ^ 5 + (45045 / 16 : ℝ) * u ^ 3 + (-3465 / 16 : ℝ) * u) 2
  have h3 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 332640 : ℝ) (by norm_num) (fun u => (765765 / 16 : ℝ) * u ^ 6 + (-675675 / 16 : ℝ) * u ^ 4 + (135135 / 16 : ℝ) * u ^ 2 + (-3465 / 16 : ℝ)) 3
  have h4 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 25945920 : ℝ) (by norm_num) (fun u => (2297295 / 8 : ℝ) * u ^ 5 + (-675675 / 4 : ℝ) * u ^ 3 + (135135 / 8 : ℝ) * u) 4
  have h5 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 1816214400 : ℝ) (by norm_num) (fun u => (11486475 / 8 : ℝ) * u ^ 4 + (-2027025 / 4 : ℝ) * u ^ 2 + (135135 / 8 : ℝ)) 5
  have h6 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 108972864000 : ℝ) (by norm_num) (fun u => (11486475 / 2 : ℝ) * u ^ 3 + (-2027025 / 2 : ℝ) * u) 6
  have h7 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 5230697472000 : ℝ) (by norm_num) (fun u => (34459425 / 2 : ℝ) * u ^ 2 + (-2027025 / 2 : ℝ)) 7
  have h8 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 177843714048000 : ℝ) (by norm_num) (fun u => (34459425 : ℝ) * u) 8
  have h9 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 3201186852864000 : ℝ) (by norm_num) (fun u => (34459425 : ℝ)) 9
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9

set_option maxHeartbeats 1200000 in
private theorem legendreP12_add_10 (u v t : ℝ) :
    legendreP12 10 t =
      ((46189 / 256 : ℝ) * u ^ 10 + (-109395 / 256 : ℝ) * u ^ 8 + (45045 / 128 : ℝ) * u ^ 6 + (-15015 / 128 : ℝ) * u ^ 4 + (3465 / 256 : ℝ) * u ^ 2 + (-63 / 256 : ℝ)) * ((46189 / 256 : ℝ) * v ^ 10 + (-109395 / 256 : ℝ) * v ^ 8 + (45045 / 128 : ℝ) * v ^ 6 + (-15015 / 128 : ℝ) * v ^ 4 + (3465 / 256 : ℝ) * v ^ 2 + (-63 / 256 : ℝ))
      + (1 / 55 : ℝ) * (((230945 / 128 : ℝ) * u ^ 9 + (-109395 / 32 : ℝ) * u ^ 7 + (135135 / 64 : ℝ) * u ^ 5 + (-15015 / 32 : ℝ) * u ^ 3 + (3465 / 128 : ℝ) * u) * ((230945 / 128 : ℝ) * v ^ 9 + (-109395 / 32 : ℝ) * v ^ 7 + (135135 / 64 : ℝ) * v ^ 5 + (-15015 / 32 : ℝ) * v ^ 3 + (3465 / 128 : ℝ) * v) * bvQ 1 u v t)
      + (1 / 5940 : ℝ) * (((2078505 / 128 : ℝ) * u ^ 8 + (-765765 / 32 : ℝ) * u ^ 6 + (675675 / 64 : ℝ) * u ^ 4 + (-45045 / 32 : ℝ) * u ^ 2 + (3465 / 128 : ℝ)) * ((2078505 / 128 : ℝ) * v ^ 8 + (-765765 / 32 : ℝ) * v ^ 6 + (675675 / 64 : ℝ) * v ^ 4 + (-45045 / 32 : ℝ) * v ^ 2 + (3465 / 128 : ℝ)) * bvQ 2 u v t)
      + (1 / 617760 : ℝ) * (((2078505 / 16 : ℝ) * u ^ 7 + (-2297295 / 16 : ℝ) * u ^ 5 + (675675 / 16 : ℝ) * u ^ 3 + (-45045 / 16 : ℝ) * u) * ((2078505 / 16 : ℝ) * v ^ 7 + (-2297295 / 16 : ℝ) * v ^ 5 + (675675 / 16 : ℝ) * v ^ 3 + (-45045 / 16 : ℝ) * v) * bvQ 3 u v t)
      + (1 / 60540480 : ℝ) * (((14549535 / 16 : ℝ) * u ^ 6 + (-11486475 / 16 : ℝ) * u ^ 4 + (2027025 / 16 : ℝ) * u ^ 2 + (-45045 / 16 : ℝ)) * ((14549535 / 16 : ℝ) * v ^ 6 + (-11486475 / 16 : ℝ) * v ^ 4 + (2027025 / 16 : ℝ) * v ^ 2 + (-45045 / 16 : ℝ)) * bvQ 4 u v t)
      + (1 / 5448643200 : ℝ) * (((43648605 / 8 : ℝ) * u ^ 5 + (-11486475 / 4 : ℝ) * u ^ 3 + (2027025 / 8 : ℝ) * u) * ((43648605 / 8 : ℝ) * v ^ 5 + (-11486475 / 4 : ℝ) * v ^ 3 + (2027025 / 8 : ℝ) * v) * bvQ 5 u v t)
      + (1 / 435891456000 : ℝ) * (((218243025 / 8 : ℝ) * u ^ 4 + (-34459425 / 4 : ℝ) * u ^ 2 + (2027025 / 8 : ℝ)) * ((218243025 / 8 : ℝ) * v ^ 4 + (-34459425 / 4 : ℝ) * v ^ 2 + (2027025 / 8 : ℝ)) * bvQ 6 u v t)
      + (1 / 29640619008000 : ℝ) * (((218243025 / 2 : ℝ) * u ^ 3 + (-34459425 / 2 : ℝ) * u) * ((218243025 / 2 : ℝ) * v ^ 3 + (-34459425 / 2 : ℝ) * v) * bvQ 7 u v t)
      + (1 / 1600593426432000 : ℝ) * (((654729075 / 2 : ℝ) * u ^ 2 + (-34459425 / 2 : ℝ)) * ((654729075 / 2 : ℝ) * v ^ 2 + (-34459425 / 2 : ℝ)) * bvQ 8 u v t)
      + (1 / 60822550204416000 : ℝ) * (((654729075 : ℝ) * u) * ((654729075 : ℝ) * v) * bvQ 9 u v t)
      + (1 / 1216451004088320000 : ℝ) * (((654729075 : ℝ)) * ((654729075 : ℝ)) * bvQ 10 u v t) := by
  simp only [legendreP12, bvQ]
  ring

private theorem sum_legendreP12_nonneg_10 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 10 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_10 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h, Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((46189 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 10 + (-109395 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 8 + (45045 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 6 + (-15015 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 4 + (3465 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 2 + (-63 / 256 : ℝ)) *
      ((46189 / 256 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 10 + (-109395 / 256 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 8 + (45045 / 128 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 6 + (-15015 / 128 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 4 + (3465 / 256 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 2 + (-63 / 256 : ℝ)) :=
    sum_prod_sq_nonneg (fun i => (46189 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 10 + (-109395 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 8 + (45045 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 6 + (-15015 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 4 + (3465 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 2 + (-63 / 256 : ℝ))
  have h1 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 55 : ℝ) (by norm_num) (fun u => (230945 / 128 : ℝ) * u ^ 9 + (-109395 / 32 : ℝ) * u ^ 7 + (135135 / 64 : ℝ) * u ^ 5 + (-15015 / 32 : ℝ) * u ^ 3 + (3465 / 128 : ℝ) * u) 1
  have h2 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 5940 : ℝ) (by norm_num) (fun u => (2078505 / 128 : ℝ) * u ^ 8 + (-765765 / 32 : ℝ) * u ^ 6 + (675675 / 64 : ℝ) * u ^ 4 + (-45045 / 32 : ℝ) * u ^ 2 + (3465 / 128 : ℝ)) 2
  have h3 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 617760 : ℝ) (by norm_num) (fun u => (2078505 / 16 : ℝ) * u ^ 7 + (-2297295 / 16 : ℝ) * u ^ 5 + (675675 / 16 : ℝ) * u ^ 3 + (-45045 / 16 : ℝ) * u) 3
  have h4 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 60540480 : ℝ) (by norm_num) (fun u => (14549535 / 16 : ℝ) * u ^ 6 + (-11486475 / 16 : ℝ) * u ^ 4 + (2027025 / 16 : ℝ) * u ^ 2 + (-45045 / 16 : ℝ)) 4
  have h5 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 5448643200 : ℝ) (by norm_num) (fun u => (43648605 / 8 : ℝ) * u ^ 5 + (-11486475 / 4 : ℝ) * u ^ 3 + (2027025 / 8 : ℝ) * u) 5
  have h6 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 435891456000 : ℝ) (by norm_num) (fun u => (218243025 / 8 : ℝ) * u ^ 4 + (-34459425 / 4 : ℝ) * u ^ 2 + (2027025 / 8 : ℝ)) 6
  have h7 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 29640619008000 : ℝ) (by norm_num) (fun u => (218243025 / 2 : ℝ) * u ^ 3 + (-34459425 / 2 : ℝ) * u) 7
  have h8 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 1600593426432000 : ℝ) (by norm_num) (fun u => (654729075 / 2 : ℝ) * u ^ 2 + (-34459425 / 2 : ℝ)) 8
  have h9 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 60822550204416000 : ℝ) (by norm_num) (fun u => (654729075 : ℝ) * u) 9
  have h10 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 1216451004088320000 : ℝ) (by norm_num) (fun u => (654729075 : ℝ)) 10
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10

set_option maxHeartbeats 1200000 in
private theorem legendreP12_add_11 (u v t : ℝ) :
    legendreP12 11 t =
      ((88179 / 256 : ℝ) * u ^ 11 + (-230945 / 256 : ℝ) * u ^ 9 + (109395 / 128 : ℝ) * u ^ 7 + (-45045 / 128 : ℝ) * u ^ 5 + (15015 / 256 : ℝ) * u ^ 3 + (-693 / 256 : ℝ) * u) * ((88179 / 256 : ℝ) * v ^ 11 + (-230945 / 256 : ℝ) * v ^ 9 + (109395 / 128 : ℝ) * v ^ 7 + (-45045 / 128 : ℝ) * v ^ 5 + (15015 / 256 : ℝ) * v ^ 3 + (-693 / 256 : ℝ) * v)
      + (1 / 66 : ℝ) * (((969969 / 256 : ℝ) * u ^ 10 + (-2078505 / 256 : ℝ) * u ^ 8 + (765765 / 128 : ℝ) * u ^ 6 + (-225225 / 128 : ℝ) * u ^ 4 + (45045 / 256 : ℝ) * u ^ 2 + (-693 / 256 : ℝ)) * ((969969 / 256 : ℝ) * v ^ 10 + (-2078505 / 256 : ℝ) * v ^ 8 + (765765 / 128 : ℝ) * v ^ 6 + (-225225 / 128 : ℝ) * v ^ 4 + (45045 / 256 : ℝ) * v ^ 2 + (-693 / 256 : ℝ)) * bvQ 1 u v t)
      + (1 / 8580 : ℝ) * (((4849845 / 128 : ℝ) * u ^ 9 + (-2078505 / 32 : ℝ) * u ^ 7 + (2297295 / 64 : ℝ) * u ^ 5 + (-225225 / 32 : ℝ) * u ^ 3 + (45045 / 128 : ℝ) * u) * ((4849845 / 128 : ℝ) * v ^ 9 + (-2078505 / 32 : ℝ) * v ^ 7 + (2297295 / 64 : ℝ) * v ^ 5 + (-225225 / 32 : ℝ) * v ^ 3 + (45045 / 128 : ℝ) * v) * bvQ 2 u v t)
      + (1 / 1081080 : ℝ) * (((43648605 / 128 : ℝ) * u ^ 8 + (-14549535 / 32 : ℝ) * u ^ 6 + (11486475 / 64 : ℝ) * u ^ 4 + (-675675 / 32 : ℝ) * u ^ 2 + (45045 / 128 : ℝ)) * ((43648605 / 128 : ℝ) * v ^ 8 + (-14549535 / 32 : ℝ) * v ^ 6 + (11486475 / 64 : ℝ) * v ^ 4 + (-675675 / 32 : ℝ) * v ^ 2 + (45045 / 128 : ℝ)) * bvQ 3 u v t)
      + (1 / 129729600 : ℝ) * (((43648605 / 16 : ℝ) * u ^ 7 + (-43648605 / 16 : ℝ) * u ^ 5 + (11486475 / 16 : ℝ) * u ^ 3 + (-675675 / 16 : ℝ) * u) * ((43648605 / 16 : ℝ) * v ^ 7 + (-43648605 / 16 : ℝ) * v ^ 5 + (11486475 / 16 : ℝ) * v ^ 3 + (-675675 / 16 : ℝ) * v) * bvQ 4 u v t)
      + (1 / 14529715200 : ℝ) * (((305540235 / 16 : ℝ) * u ^ 6 + (-218243025 / 16 : ℝ) * u ^ 4 + (34459425 / 16 : ℝ) * u ^ 2 + (-675675 / 16 : ℝ)) * ((305540235 / 16 : ℝ) * v ^ 6 + (-218243025 / 16 : ℝ) * v ^ 4 + (34459425 / 16 : ℝ) * v ^ 2 + (-675675 / 16 : ℝ)) * bvQ 5 u v t)
      + (1 / 1482030950400 : ℝ) * (((916620705 / 8 : ℝ) * u ^ 5 + (-218243025 / 4 : ℝ) * u ^ 3 + (34459425 / 8 : ℝ) * u) * ((916620705 / 8 : ℝ) * v ^ 5 + (-218243025 / 4 : ℝ) * v ^ 3 + (34459425 / 8 : ℝ) * v) * bvQ 6 u v t)
      + (1 / 133382785536000 : ℝ) * (((4583103525 / 8 : ℝ) * u ^ 4 + (-654729075 / 4 : ℝ) * u ^ 2 + (34459425 / 8 : ℝ)) * ((4583103525 / 8 : ℝ) * v ^ 4 + (-654729075 / 4 : ℝ) * v ^ 2 + (34459425 / 8 : ℝ)) * bvQ 7 u v t)
      + (1 / 10137091700736000 : ℝ) * (((4583103525 / 2 : ℝ) * u ^ 3 + (-654729075 / 2 : ℝ) * u) * ((4583103525 / 2 : ℝ) * v ^ 3 + (-654729075 / 2 : ℝ) * v) * bvQ 8 u v t)
      + (1 / 608225502044160000 : ℝ) * (((13749310575 / 2 : ℝ) * u ^ 2 + (-654729075 / 2 : ℝ)) * ((13749310575 / 2 : ℝ) * v ^ 2 + (-654729075 / 2 : ℝ)) * bvQ 9 u v t)
      + (1 / 25545471085854720000 : ℝ) * (((13749310575 : ℝ) * u) * ((13749310575 : ℝ) * v) * bvQ 10 u v t)
      + (1 / 562000363888803840000 : ℝ) * (((13749310575 : ℝ)) * ((13749310575 : ℝ)) * bvQ 11 u v t) := by
  simp only [legendreP12, bvQ]
  ring

private theorem sum_legendreP12_nonneg_11 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 11 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_11 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h, Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((88179 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 11 + (-230945 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 9 + (109395 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 7 + (-45045 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 5 + (15015 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 3 + (-693 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫) *
      ((88179 / 256 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 11 + (-230945 / 256 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 9 + (109395 / 128 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 7 + (-45045 / 128 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 5 + (15015 / 256 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 3 + (-693 / 256 : ℝ) * ⟪northPoleS2.val, (p j).val⟫) :=
    sum_prod_sq_nonneg (fun i => (88179 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 11 + (-230945 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 9 + (109395 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 7 + (-45045 / 128 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 5 + (15015 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 3 + (-693 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫)
  have h1 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 66 : ℝ) (by norm_num) (fun u => (969969 / 256 : ℝ) * u ^ 10 + (-2078505 / 256 : ℝ) * u ^ 8 + (765765 / 128 : ℝ) * u ^ 6 + (-225225 / 128 : ℝ) * u ^ 4 + (45045 / 256 : ℝ) * u ^ 2 + (-693 / 256 : ℝ)) 1
  have h2 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 8580 : ℝ) (by norm_num) (fun u => (4849845 / 128 : ℝ) * u ^ 9 + (-2078505 / 32 : ℝ) * u ^ 7 + (2297295 / 64 : ℝ) * u ^ 5 + (-225225 / 32 : ℝ) * u ^ 3 + (45045 / 128 : ℝ) * u) 2
  have h3 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 1081080 : ℝ) (by norm_num) (fun u => (43648605 / 128 : ℝ) * u ^ 8 + (-14549535 / 32 : ℝ) * u ^ 6 + (11486475 / 64 : ℝ) * u ^ 4 + (-675675 / 32 : ℝ) * u ^ 2 + (45045 / 128 : ℝ)) 3
  have h4 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 129729600 : ℝ) (by norm_num) (fun u => (43648605 / 16 : ℝ) * u ^ 7 + (-43648605 / 16 : ℝ) * u ^ 5 + (11486475 / 16 : ℝ) * u ^ 3 + (-675675 / 16 : ℝ) * u) 4
  have h5 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 14529715200 : ℝ) (by norm_num) (fun u => (305540235 / 16 : ℝ) * u ^ 6 + (-218243025 / 16 : ℝ) * u ^ 4 + (34459425 / 16 : ℝ) * u ^ 2 + (-675675 / 16 : ℝ)) 5
  have h6 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 1482030950400 : ℝ) (by norm_num) (fun u => (916620705 / 8 : ℝ) * u ^ 5 + (-218243025 / 4 : ℝ) * u ^ 3 + (34459425 / 8 : ℝ) * u) 6
  have h7 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 133382785536000 : ℝ) (by norm_num) (fun u => (4583103525 / 8 : ℝ) * u ^ 4 + (-654729075 / 4 : ℝ) * u ^ 2 + (34459425 / 8 : ℝ)) 7
  have h8 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 10137091700736000 : ℝ) (by norm_num) (fun u => (4583103525 / 2 : ℝ) * u ^ 3 + (-654729075 / 2 : ℝ) * u) 8
  have h9 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 608225502044160000 : ℝ) (by norm_num) (fun u => (13749310575 / 2 : ℝ) * u ^ 2 + (-654729075 / 2 : ℝ)) 9
  have h10 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 25545471085854720000 : ℝ) (by norm_num) (fun u => (13749310575 : ℝ) * u) 10
  have h11 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 562000363888803840000 : ℝ) (by norm_num) (fun u => (13749310575 : ℝ)) 11
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11

set_option maxHeartbeats 1200000 in
private theorem legendreP12_add_12 (u v t : ℝ) :
    legendreP12 12 t =
      ((676039 / 1024 : ℝ) * u ^ 12 + (-969969 / 512 : ℝ) * u ^ 10 + (2078505 / 1024 : ℝ) * u ^ 8 + (-255255 / 256 : ℝ) * u ^ 6 + (225225 / 1024 : ℝ) * u ^ 4 + (-9009 / 512 : ℝ) * u ^ 2 + (231 / 1024 : ℝ)) * ((676039 / 1024 : ℝ) * v ^ 12 + (-969969 / 512 : ℝ) * v ^ 10 + (2078505 / 1024 : ℝ) * v ^ 8 + (-255255 / 256 : ℝ) * v ^ 6 + (225225 / 1024 : ℝ) * v ^ 4 + (-9009 / 512 : ℝ) * v ^ 2 + (231 / 1024 : ℝ))
      + (1 / 78 : ℝ) * (((2028117 / 256 : ℝ) * u ^ 11 + (-4849845 / 256 : ℝ) * u ^ 9 + (2078505 / 128 : ℝ) * u ^ 7 + (-765765 / 128 : ℝ) * u ^ 5 + (225225 / 256 : ℝ) * u ^ 3 + (-9009 / 256 : ℝ) * u) * ((2028117 / 256 : ℝ) * v ^ 11 + (-4849845 / 256 : ℝ) * v ^ 9 + (2078505 / 128 : ℝ) * v ^ 7 + (-765765 / 128 : ℝ) * v ^ 5 + (225225 / 256 : ℝ) * v ^ 3 + (-9009 / 256 : ℝ) * v) * bvQ 1 u v t)
      + (1 / 12012 : ℝ) * (((22309287 / 256 : ℝ) * u ^ 10 + (-43648605 / 256 : ℝ) * u ^ 8 + (14549535 / 128 : ℝ) * u ^ 6 + (-3828825 / 128 : ℝ) * u ^ 4 + (675675 / 256 : ℝ) * u ^ 2 + (-9009 / 256 : ℝ)) * ((22309287 / 256 : ℝ) * v ^ 10 + (-43648605 / 256 : ℝ) * v ^ 8 + (14549535 / 128 : ℝ) * v ^ 6 + (-3828825 / 128 : ℝ) * v ^ 4 + (675675 / 256 : ℝ) * v ^ 2 + (-9009 / 256 : ℝ)) * bvQ 2 u v t)
      + (1 / 1801800 : ℝ) * (((111546435 / 128 : ℝ) * u ^ 9 + (-43648605 / 32 : ℝ) * u ^ 7 + (43648605 / 64 : ℝ) * u ^ 5 + (-3828825 / 32 : ℝ) * u ^ 3 + (675675 / 128 : ℝ) * u) * ((111546435 / 128 : ℝ) * v ^ 9 + (-43648605 / 32 : ℝ) * v ^ 7 + (43648605 / 64 : ℝ) * v ^ 5 + (-3828825 / 32 : ℝ) * v ^ 3 + (675675 / 128 : ℝ) * v) * bvQ 3 u v t)
      + (1 / 259459200 : ℝ) * (((1003917915 / 128 : ℝ) * u ^ 8 + (-305540235 / 32 : ℝ) * u ^ 6 + (218243025 / 64 : ℝ) * u ^ 4 + (-11486475 / 32 : ℝ) * u ^ 2 + (675675 / 128 : ℝ)) * ((1003917915 / 128 : ℝ) * v ^ 8 + (-305540235 / 32 : ℝ) * v ^ 6 + (218243025 / 64 : ℝ) * v ^ 4 + (-11486475 / 32 : ℝ) * v ^ 2 + (675675 / 128 : ℝ)) * bvQ 4 u v t)
      + (1 / 35286451200 : ℝ) * (((1003917915 / 16 : ℝ) * u ^ 7 + (-916620705 / 16 : ℝ) * u ^ 5 + (218243025 / 16 : ℝ) * u ^ 3 + (-11486475 / 16 : ℝ) * u) * ((1003917915 / 16 : ℝ) * v ^ 7 + (-916620705 / 16 : ℝ) * v ^ 5 + (218243025 / 16 : ℝ) * v ^ 3 + (-11486475 / 16 : ℝ) * v) * bvQ 5 u v t)
      + (1 / 4446092851200 : ℝ) * (((7027425405 / 16 : ℝ) * u ^ 6 + (-4583103525 / 16 : ℝ) * u ^ 4 + (654729075 / 16 : ℝ) * u ^ 2 + (-11486475 / 16 : ℝ)) * ((7027425405 / 16 : ℝ) * v ^ 6 + (-4583103525 / 16 : ℝ) * v ^ 4 + (654729075 / 16 : ℝ) * v ^ 2 + (-11486475 / 16 : ℝ)) * bvQ 6 u v t)
      + (1 / 506854585036800 : ℝ) * (((21082276215 / 8 : ℝ) * u ^ 5 + (-4583103525 / 4 : ℝ) * u ^ 3 + (654729075 / 8 : ℝ) * u) * ((21082276215 / 8 : ℝ) * v ^ 5 + (-4583103525 / 4 : ℝ) * v ^ 3 + (654729075 / 8 : ℝ) * v) * bvQ 7 u v t)
      + (1 / 50685458503680000 : ℝ) * (((105411381075 / 8 : ℝ) * u ^ 4 + (-13749310575 / 4 : ℝ) * u ^ 2 + (654729075 / 8 : ℝ)) * ((105411381075 / 8 : ℝ) * v ^ 4 + (-13749310575 / 4 : ℝ) * v ^ 2 + (654729075 / 8 : ℝ)) * bvQ 8 u v t)
      + (1 / 4257578514309120000 : ℝ) * (((105411381075 / 2 : ℝ) * u ^ 3 + (-13749310575 / 2 : ℝ) * u) * ((105411381075 / 2 : ℝ) * v ^ 3 + (-13749310575 / 2 : ℝ) * v) * bvQ 9 u v t)
      + (1 / 281000181944401920000 : ℝ) * (((316234143225 / 2 : ℝ) * u ^ 2 + (-13749310575 / 2 : ℝ)) * ((316234143225 / 2 : ℝ) * v ^ 2 + (-13749310575 / 2 : ℝ)) * bvQ 10 u v t)
      + (1 / 12926008369442488320000 : ℝ) * (((316234143225 : ℝ) * u) * ((316234143225 : ℝ) * v) * bvQ 11 u v t)
      + (1 / 310224200866619719680000 : ℝ) * (((316234143225 : ℝ)) * ((316234143225 : ℝ)) * bvQ 12 u v t) := by
  simp only [legendreP12, bvQ]
  ring

private theorem sum_legendreP12_nonneg_12 {n : ℕ} (p : Fin n → UnitSphere) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 12 ⟪(p i).val, (p j).val⟫ := by
  have h := fun i j : Fin n => legendreP12_add_12 ⟪northPoleS2.val, (p i).val⟫ ⟪northPoleS2.val, (p j).val⟫ ⟪(p i).val, (p j).val⟫
  simp_rw [h, Finset.sum_add_distrib]
  have h0 : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      ((676039 / 1024 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 12 + (-969969 / 512 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 10 + (2078505 / 1024 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 8 + (-255255 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 6 + (225225 / 1024 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 4 + (-9009 / 512 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 2 + (231 / 1024 : ℝ)) *
      ((676039 / 1024 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 12 + (-969969 / 512 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 10 + (2078505 / 1024 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 8 + (-255255 / 256 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 6 + (225225 / 1024 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 4 + (-9009 / 512 : ℝ) * ⟪northPoleS2.val, (p j).val⟫ ^ 2 + (231 / 1024 : ℝ)) :=
    sum_prod_sq_nonneg (fun i => (676039 / 1024 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 12 + (-969969 / 512 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 10 + (2078505 / 1024 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 8 + (-255255 / 256 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 6 + (225225 / 1024 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 4 + (-9009 / 512 : ℝ) * ⟪northPoleS2.val, (p i).val⟫ ^ 2 + (231 / 1024 : ℝ))
  have h1 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 78 : ℝ) (by norm_num) (fun u => (2028117 / 256 : ℝ) * u ^ 11 + (-4849845 / 256 : ℝ) * u ^ 9 + (2078505 / 128 : ℝ) * u ^ 7 + (-765765 / 128 : ℝ) * u ^ 5 + (225225 / 256 : ℝ) * u ^ 3 + (-9009 / 256 : ℝ) * u) 1
  have h2 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 12012 : ℝ) (by norm_num) (fun u => (22309287 / 256 : ℝ) * u ^ 10 + (-43648605 / 256 : ℝ) * u ^ 8 + (14549535 / 128 : ℝ) * u ^ 6 + (-3828825 / 128 : ℝ) * u ^ 4 + (675675 / 256 : ℝ) * u ^ 2 + (-9009 / 256 : ℝ)) 2
  have h3 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 1801800 : ℝ) (by norm_num) (fun u => (111546435 / 128 : ℝ) * u ^ 9 + (-43648605 / 32 : ℝ) * u ^ 7 + (43648605 / 64 : ℝ) * u ^ 5 + (-3828825 / 32 : ℝ) * u ^ 3 + (675675 / 128 : ℝ) * u) 3
  have h4 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 259459200 : ℝ) (by norm_num) (fun u => (1003917915 / 128 : ℝ) * u ^ 8 + (-305540235 / 32 : ℝ) * u ^ 6 + (218243025 / 64 : ℝ) * u ^ 4 + (-11486475 / 32 : ℝ) * u ^ 2 + (675675 / 128 : ℝ)) 4
  have h5 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 35286451200 : ℝ) (by norm_num) (fun u => (1003917915 / 16 : ℝ) * u ^ 7 + (-916620705 / 16 : ℝ) * u ^ 5 + (218243025 / 16 : ℝ) * u ^ 3 + (-11486475 / 16 : ℝ) * u) 5
  have h6 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 4446092851200 : ℝ) (by norm_num) (fun u => (7027425405 / 16 : ℝ) * u ^ 6 + (-4583103525 / 16 : ℝ) * u ^ 4 + (654729075 / 16 : ℝ) * u ^ 2 + (-11486475 / 16 : ℝ)) 6
  have h7 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 506854585036800 : ℝ) (by norm_num) (fun u => (21082276215 / 8 : ℝ) * u ^ 5 + (-4583103525 / 4 : ℝ) * u ^ 3 + (654729075 / 8 : ℝ) * u) 7
  have h8 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 50685458503680000 : ℝ) (by norm_num) (fun u => (105411381075 / 8 : ℝ) * u ^ 4 + (-13749310575 / 4 : ℝ) * u ^ 2 + (654729075 / 8 : ℝ)) 8
  have h9 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 4257578514309120000 : ℝ) (by norm_num) (fun u => (105411381075 / 2 : ℝ) * u ^ 3 + (-13749310575 / 2 : ℝ) * u) 9
  have h10 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 281000181944401920000 : ℝ) (by norm_num) (fun u => (316234143225 / 2 : ℝ) * u ^ 2 + (-13749310575 / 2 : ℝ)) 10
  have h11 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 12926008369442488320000 : ℝ) (by norm_num) (fun u => (316234143225 : ℝ) * u) 11
  have h12 := sum_bvQ_weighted_nonneg p northPoleS2 (1 / 310224200866619719680000 : ℝ) (by norm_num) (fun u => (316234143225 : ℝ)) 12
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12

/-- Positive semidefiniteness of `legendreP12 k` on `S²` for all `0 ≤ k ≤ 12`:
`∑ i, ∑ j, P_k(⟪p i, p j⟫) ≥ 0`. -/
theorem sum_legendreP12_nonneg {n : ℕ} (p : Fin n → UnitSphere) {k : ℕ} (hk : k ≤ 12) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, legendreP12 k ⟪(p i).val, (p j).val⟫ := by
  interval_cases k
  · exact sum_legendreP12_nonneg_0 p
  · exact sum_legendreP12_nonneg_1 p
  · exact sum_legendreP12_nonneg_2 p
  · exact sum_legendreP12_nonneg_3 p
  · exact sum_legendreP12_nonneg_4 p
  · exact sum_legendreP12_nonneg_5 p
  · exact sum_legendreP12_nonneg_6 p
  · exact sum_legendreP12_nonneg_7 p
  · exact sum_legendreP12_nonneg_8 p
  · exact sum_legendreP12_nonneg_9 p
  · exact sum_legendreP12_nonneg_10 p
  · exact sum_legendreP12_nonneg_11 p
  · exact sum_legendreP12_nonneg_12 p

private theorem bvQ_one_left (k : ℕ) (t : ℝ) :
    bvQ k 1 t t = if k = 0 then 1 else 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [bvQ]
    | 1 => simp [bvQ]
    | k + 2 =>
      rw [bvQ_succ_succ, ih (k + 1) (by omega), ih k (by omega)]
      simp

private theorem bvQ_one_mid (k : ℕ) (t : ℝ) :
    bvQ k t 1 t = if k = 0 then 1 else 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [bvQ]
    | 1 => simp [bvQ]
    | k + 2 =>
      rw [bvQ_succ_succ, ih (k + 1) (by omega), ih k (by omega)]
      simp

private theorem bvQ_diag_one (k : ℕ) :
    bvQ k 1 1 1 = if k = 0 then 1 else 0 := by
  simpa using bvQ_one_left k 1

/-- Two-point polynomial induced by an unaugmented family `F_0, …, F_d`. -/
def bvG2Unaug {d : ℕ}
    (F : (k : Fin (d + 1)) → Matrix (Fin (d - k.val + 1)) (Fin (d - k.val + 1)) ℝ) (t : ℝ) : ℝ :=
  2 * (∑ i : Fin (d + 1), ∑ j : Fin (d + 1), F ⟨0, Nat.zero_lt_succ d⟩ i j * t ^ i.val) +
  ∑ k : Fin (d + 1),
    (∑ i : Fin (d - k.val + 1), ∑ j : Fin (d - k.val + 1),
      F k i j * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ k.val

/-- Unsymmetrized three-point polynomial induced by an unaugmented family `F_0, …, F_d`. -/
def bvG3Unaug {d : ℕ}
    (F : (k : Fin (d + 1)) → Matrix (Fin (d - k.val + 1)) (Fin (d - k.val + 1)) ℝ) (u v t : ℝ) : ℝ :=
  ∑ k : Fin (d + 1),
    (∑ i : Fin (d - k.val + 1), ∑ j : Fin (d - k.val + 1),
      F k i j * u ^ i.val * v ^ j.val) * bvQ k.val u v t

/-- Reusable Bachoc–Vallentin three-point SDP bound on `S²` augmented with nonnegative
two-point Legendre polynomial terms `c₂(k) · P_k` (`1 ≤ k ≤ 12`). -/
theorem bachocVallentin_bound_with_legendre
    {d : ℕ} {s : ℝ}
    (F : (k : Fin (d + 1)) → Matrix (Fin (d - k.val + 1)) (Fin (d - k.val + 1)) ℝ)
    (hF : ∀ k, (F k).PosSemidef)
    (c2 : Fin 12 → ℝ) (hc2 : ∀ k, 0 ≤ c2 k)
    (h2 : ∀ t : ℝ, -1 ≤ t → t ≤ s →
      bvG2Unaug F t + ∑ k : Fin 12, c2 k * legendreP12 (k.val + 1) t ≤ -1)
    (h3 : ∀ u v t : ℝ, InThreePointDomain s u v t → sym3 (bvG3Unaug F) u v t ≤ 0)
    {n : ℕ} {p : Fin n → UnitSphere} (hp : IsSphericalCode p s) :
    (n : ℝ) ≤ 1 + (∑ i : Fin (d + 1), ∑ j : Fin (d + 1), F ⟨0, Nat.zero_lt_succ d⟩ i j) +
      ∑ k : Fin 12, c2 k := by
  by_cases hn : n = 0
  · subst hn
    have hF0 : 0 ≤ ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), F ⟨0, Nat.zero_lt_succ d⟩ i j := by
      have h := posSemidef_quad_nonneg (hF ⟨0, Nat.zero_lt_succ d⟩) (fun _ => (1 : ℝ))
      simpa using h
    have hc2s : 0 ≤ ∑ k : Fin 12, c2 k := Finset.sum_nonneg fun k _ => hc2 k
    simp only [Nat.cast_zero]
    linarith
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hS3 : 0 ≤ ∑ k : Fin (d + 1), ∑ x : Fin n, ∑ y : Fin n, ∑ z : Fin n,
      (∑ i : Fin (d - k.val + 1), ∑ j : Fin (d - k.val + 1),
        F k i j * ⟪(p x).val, (p y).val⟫ ^ i.val * ⟪(p x).val, (p z).val⟫ ^ j.val) *
      bvQ k.val ⟪(p x).val, (p y).val⟫ ⟪(p x).val, (p z).val⟫ ⟪(p y).val, (p z).val⟫ := by
    refine Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun x _ => ?_
    have h := sum_weighted_bvQ_nonneg (Finset.univ : Finset (Fin n)) (p x) p k.val (hF k)
    refine le_trans h (le_of_eq ?_)
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hS2 : 0 ≤ ∑ k : Fin 12, c2 k *
      (∑ i : Fin n, ∑ j : Fin n, legendreP12 (k.val + 1) ⟪(p i).val, (p j).val⟫) :=
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (hc2 k) (sum_legendreP12_nonneg p (by omega))
  have hS2_split : ∑ k : Fin 12, c2 k *
      (∑ i : Fin n, ∑ j : Fin n, legendreP12 (k.val + 1) ⟪(p i).val, (p j).val⟫) =
      (n : ℝ) * (∑ k : Fin 12, c2 k) +
      ∑ i : Fin n, ∑ j : Fin n, if i ≠ j then
        ∑ k : Fin 12, c2 k * legendreP12 (k.val + 1) ⟪(p i).val, (p j).val⟫ else 0 := by
    have hdiag_leg : ∀ k : Fin 12,
        ∑ i : Fin n, ∑ j : Fin n, legendreP12 (k.val + 1) ⟪(p i).val, (p j).val⟫ =
        (n : ℝ) + ∑ i : Fin n, ∑ j : Fin n,
          if i ≠ j then legendreP12 (k.val + 1) ⟪(p i).val, (p j).val⟫ else 0 := by
      intro k
      have h1 : ∀ i : Fin n,
          ∑ j : Fin n, legendreP12 (k.val + 1) ⟪(p i).val, (p j).val⟫ =
          1 + ∑ j : Fin n, if i ≠ j then legendreP12 (k.val + 1) ⟪(p i).val, (p j).val⟫ else 0 := by
        intro i
        have := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
          (fun j => legendreP12 (k.val + 1) ⟪(p i).val, (p j).val⟫) (Finset.mem_univ i)
        rw [← this, Geodesic.inner_self_of_norm_one (p i).2, legendreP12_one (by omega)]
        congr 1
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext j; simp [ne_comm]
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
    simp_rw [hdiag_leg, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_mul]; ring
    · simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i ≠ j
      · simp [hij]
      · simp only [hij, ↓reduceIte, mul_zero, Finset.sum_const_zero]
  let f3 : Fin n → Fin n → Fin n → ℝ := fun x y z =>
    bvG3Unaug F ⟪(p x).val, (p y).val⟫ ⟪(p x).val, (p z).val⟫ ⟪(p y).val, (p z).val⟫
  have hS3_eq : ∑ k : Fin (d + 1), ∑ x : Fin n, ∑ y : Fin n, ∑ z : Fin n,
      (∑ i : Fin (d - k.val + 1), ∑ j : Fin (d - k.val + 1),
        F k i j * ⟪(p x).val, (p y).val⟫ ^ i.val * ⟪(p x).val, (p z).val⟫ ^ j.val) *
      bvQ k.val ⟪(p x).val, (p y).val⟫ ⟪(p x).val, (p z).val⟫ ⟪(p y).val, (p z).val⟫ =
      ∑ x : Fin n, ∑ y : Fin n, ∑ z : Fin n, f3 x y z := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    rfl
  have hS3_split : ∑ x : Fin n, ∑ y : Fin n, ∑ z : Fin n, f3 x y z =
      (∑ x : Fin n, f3 x x x) +
      (∑ x : Fin n, ∑ y : Fin n, if x ≠ y then f3 x x y + f3 x y x + f3 x y y else 0) +
      (∑ x : Fin n, ∑ y ∈ Finset.univ.erase x, ∑ z ∈ (Finset.univ.erase x).erase y, f3 x y z) := by
    have hinner : ∀ x : Fin n,
        ∑ y : Fin n, ∑ z : Fin n, f3 x y z =
        f3 x x x +
        (∑ y ∈ Finset.univ.erase x, (f3 x x y + f3 x y x + f3 x y y)) +
        (∑ y ∈ Finset.univ.erase x, ∑ z ∈ (Finset.univ.erase x).erase y, f3 x y z) := by
      intro x
      have hy := (Finset.add_sum_erase (Finset.univ : Finset (Fin n))
        (fun y => ∑ z : Fin n, f3 x y z) (Finset.mem_univ x)).symm
      rw [hy]
      have hz0 := (Finset.add_sum_erase (Finset.univ : Finset (Fin n))
        (fun z => f3 x x z) (Finset.mem_univ x)).symm
      rw [hz0]
      have hzy : ∀ y ∈ Finset.univ.erase x,
          ∑ z : Fin n, f3 x y z =
          f3 x y x + f3 x y y + ∑ z ∈ (Finset.univ.erase x).erase y, f3 x y z := by
        intro y hy
        have h1 := (Finset.add_sum_erase (Finset.univ : Finset (Fin n))
          (fun z => f3 x y z) (Finset.mem_univ x)).symm
        have h2 := (Finset.add_sum_erase (Finset.univ.erase x)
          (fun z => f3 x y z) hy).symm
        rw [h1, h2]; ring
      rw [Finset.sum_congr rfl hzy]
      simp only [Finset.sum_add_distrib]
      ring
    simp_rw [hinner, Finset.sum_add_distrib]
    congr 1; congr 1
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext y; simp [ne_comm]
  rw [hS3_eq, hS3_split] at hS3
  have hdiag : ∑ x : Fin n, f3 x x x =
      (n : ℝ) * ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), F ⟨0, Nat.zero_lt_succ d⟩ i j := by
    have hpt : ∀ x : Fin n, f3 x x x =
        ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), F ⟨0, Nat.zero_lt_succ d⟩ i j := by
      intro x
      simp only [f3, bvG3Unaug, Geodesic.inner_self_of_norm_one (p x).2, one_pow, mul_one, bvQ_diag_one]
      rw [Finset.sum_eq_single ⟨0, Nat.zero_lt_succ d⟩]
      · simp
      · intro k _ hk
        have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
        simp [hk0]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hpt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpair : ∀ x y : Fin n,
      f3 x x y + f3 x y x + f3 x y y = bvG2Unaug F ⟪(p x).val, (p y).val⟫ := by
    intro x y
    set t := ⟪(p x).val, (p y).val⟫
    have hxy : ⟪(p y).val, (p x).val⟫ = t := real_inner_comm _ _
    have h1 : f3 x x y = ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        F ⟨0, Nat.zero_lt_succ d⟩ i j * t ^ j.val := by
      simp only [f3, bvG3Unaug, Geodesic.inner_self_of_norm_one (p x).2, one_pow, mul_one]
      rw [Finset.sum_eq_single ⟨0, Nat.zero_lt_succ d⟩]
      · simp [t, bvQ]
      · intro k _ hk
        have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
        simp [bvQ_one_left, hk0]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h2' : f3 x y x = ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        F ⟨0, Nat.zero_lt_succ d⟩ i j * t ^ i.val := by
      simp only [f3, bvG3Unaug, Geodesic.inner_self_of_norm_one (p x).2, one_pow, mul_one, hxy]
      rw [Finset.sum_eq_single ⟨0, Nat.zero_lt_succ d⟩]
      · simp [t, bvQ]
      · intro k _ hk
        have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
        change (∑ i, ∑ j, F k i j * t ^ i.val) * bvQ k.val t 1 t = 0
        simp [bvQ_one_mid, hk0]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h3' : f3 x y y = ∑ k : Fin (d + 1),
        (∑ i : Fin (d - k.val + 1), ∑ j : Fin (d - k.val + 1),
          F k i j * t ^ (i.val + j.val)) * (1 - t ^ 2) ^ k.val := by
      simp only [f3, bvG3Unaug, Geodesic.inner_self_of_norm_one (p y).2, bvQ_diag]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [pow_add]; ring
    have hsym0 : ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        F ⟨0, Nat.zero_lt_succ d⟩ i j * t ^ j.val =
        ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        F ⟨0, Nat.zero_lt_succ d⟩ i j * t ^ i.val := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hH := (hF ⟨0, Nat.zero_lt_succ d⟩).isHermitian
      have hij : F ⟨0, Nat.zero_lt_succ d⟩ j i = F ⟨0, Nat.zero_lt_succ d⟩ i j := by
        have h := congr_fun (congr_fun hH i) j
        change star (F ⟨0, Nat.zero_lt_succ d⟩ j i) = F ⟨0, Nat.zero_lt_succ d⟩ i j at h
        simpa using h
      rw [hij]
    rw [h1, h2', h3', hsym0, bvG2Unaug]
    ring
  have htriple : ∑ x : Fin n, ∑ y ∈ Finset.univ.erase x, ∑ z ∈ (Finset.univ.erase x).erase y,
      f3 x y z ≤ 0 := by
    have hsym := sum_distinct_triples_eq_sym3 p (bvG3Unaug F)
    rw [hsym]
    refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y hy => Finset.sum_nonpos fun z hz => ?_
    have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
    have hyz : y ≠ z := (Finset.mem_erase.mp hz).1.symm
    have hxz : x ≠ z := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1.symm
    exact h3 _ _ _ (inThreePointDomain_of_isSphericalCode hp hxy hxz hyz)
  have htot : 0 ≤ (n : ℝ) * (∑ i : Fin (d + 1), ∑ j : Fin (d + 1), F ⟨0, Nat.zero_lt_succ d⟩ i j) +
      (n : ℝ) * (∑ k : Fin 12, c2 k) +
      ∑ x : Fin n, ∑ y : Fin n, if x ≠ y then
        (bvG2Unaug F ⟪(p x).val, (p y).val⟫ + ∑ k : Fin 12, c2 k * legendreP12 (k.val + 1) ⟪(p x).val, (p y).val⟫)
      else 0 := by
    rw [hS2_split] at hS2
    have hcomb : (∑ x : Fin n, ∑ y : Fin n, if x ≠ y then f3 x x y + f3 x y x + f3 x y y else 0) +
        (∑ x : Fin n, ∑ y : Fin n, if x ≠ y then ∑ k : Fin 12, c2 k * legendreP12 (k.val + 1) ⟪(p x).val, (p y).val⟫ else 0) =
        ∑ x : Fin n, ∑ y : Fin n, if x ≠ y then
          (bvG2Unaug F ⟪(p x).val, (p y).val⟫ + ∑ k : Fin 12, c2 k * legendreP12 (k.val + 1) ⟪(p x).val, (p y).val⟫) else 0 := by
      simp_rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      by_cases hxy : x ≠ y <;> simp [hxy, hpair]
    linarith [hS3, hS2, hdiag, htriple, hcomb]
  have hoff_le : ∑ x : Fin n, ∑ y : Fin n,
      (if x ≠ y then
        (bvG2Unaug F ⟪(p x).val, (p y).val⟫ + ∑ k : Fin 12, c2 k * legendreP12 (k.val + 1) ⟪(p x).val, (p y).val⟫)
      else 0) ≤ -((n : ℝ) * ((n : ℝ) - 1)) := by
    have hle : ∑ x : Fin n, ∑ y : Fin n,
        (if x ≠ y then
          (bvG2Unaug F ⟪(p x).val, (p y).val⟫ + ∑ k : Fin 12, c2 k * legendreP12 (k.val + 1) ⟪(p x).val, (p y).val⟫)
        else 0) ≤ ∑ x : Fin n, ∑ y : Fin n, if x ≠ y then (-1 : ℝ) else 0 := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
      split_ifs with hxy
      · exact h2 _ (neg_one_le_inner (p x) (p y)) (hp x y hxy)
      · exact le_rfl
    have hcount : ∑ x : Fin n, ∑ y : Fin n, (if x ≠ y then (-1 : ℝ) else 0) = -((n : ℝ) * ((n : ℝ) - 1)) := by
      have hinner : ∀ x : Fin n, ∑ y : Fin n, (if x ≠ y then (-1 : ℝ) else 0) = -((n : ℝ) - 1) := by
        intro x
        have := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
          (fun y => if x ≠ y then (-1 : ℝ) else 0) (Finset.mem_univ x)
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_add] at this
        rw [← this]
        have hcongr : ∑ y ∈ Finset.univ.erase x, (if x ≠ y then (-1 : ℝ) else 0) =
            ∑ _y ∈ Finset.univ.erase x, (-1 : ℝ) :=
          Finset.sum_congr rfl fun y hy => by simp [(Finset.mem_erase.mp hy).1.symm]
        rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ x),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_sub (Nat.pos_of_ne_zero hn), Nat.cast_one]
        ring
      simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    linarith
  have hfinal : (n : ℝ) * ((n : ℝ) - 1) ≤
      (n : ℝ) * ((∑ i : Fin (d + 1), ∑ j : Fin (d + 1), F ⟨0, Nat.zero_lt_succ d⟩ i j) +
        ∑ k : Fin 12, c2 k) := by
    linarith
  nlinarith

end Geodesy.Spherical
