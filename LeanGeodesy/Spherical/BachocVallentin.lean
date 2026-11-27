import LeanGeodesy.Spherical.ThreePoint
import Mathlib.Basic.Complex.Basic

/-!
# Bachoc–Vallentin three-point semidefinite programming bound on `S²`

This module formalizes the Bachoc–Vallentin (2008) three-point SDP bound on the
two-sphere `S²` for arbitrary degree `d : ℕ`, with a completely elementary
complex-projection proof of positive semidefiniteness:

- `bvQ k u v t`: the `S²` Chebyshev-projected polynomial kernel
  `((1 - u²)(1 - v²))^{k/2} T_k((t - u v) / √((1 - u²)(1 - v²)))`,
  defined purely algebraically by the three-term recurrence
  `Q₀ = 1`, `Q₁ = t - u v`, `Q_{k+2} = 2 (t - u v) Q_{k+1} - (1 - u²)(1 - v²) Q_k`;
- `bvQ_eq_re_complex`: for any `x ∈ S²` and orthonormal tangent frame `{e₁, e₂}`
  of `x⊥`, `bvQ k ⟪x, y⟫ ⟪x, z⟫ ⟪y, z⟫ = Re((w_x y)^k · conj(w_x z)^k)` where
  `w_x y = ⟪y, e₁⟫ + i ⟪y, e₂⟫`;
- `sum_weighted_bvQ_nonneg`: for every `k : ℕ`, every PSD matrix `F`, and every
  finite configuration on `S²`, the weighted three-point correlation sum is `≥ 0`;
- `posSemidef_of_cholesky_dd`: certifies `M.PosSemidef` from a rational/real
  Cholesky approximation `R` whose remainder `E = M - Rᵀ R` is symmetric and
  diagonally dominant;
- `bachocVallentin_bound`: reusable soundness theorem deriving `(n : ℝ) ≤ 1 + A₀ 0 0`
  from PSD matrices `A₀` and `F₁, …, F_d` whose two-point polynomial `G₂` is `≤ 0`
  on `[-1, s]` and whose symmetrized three-point polynomial `sym3 G₃` is `≤ 0` on
  `InThreePointDomain s`.
-/

namespace Geodesy.Spherical

open scoped Matrix

/-! ## Elementary matrix PSD criteria -/

/-- For a real matrix `M : Matrix (Fin m) (Fin m) ℝ`, `M.PosSemidef` yields
nonnegativity of the real quadratic form `∑ a, ∑ b, v a * M a b * v b`. -/
theorem posSemidef_quad_nonneg {m : ℕ} {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M.PosSemidef) (v : Fin m → ℝ) :
    0 ≤ ∑ a : Fin m, ∑ b : Fin m, v a * M a b * v b := by
  have h := hM.2 (Finsupp.equivFunOnFinite.symm v)
  simpa [Finsupp.sum_fintype, star_trivial] using h

/-- `Rᵀ * R` is positive semidefinite for any real matrix `R`. -/
theorem posSemidef_transpose_mul_self {r m : ℕ} (R : Matrix (Fin r) (Fin m) ℝ) :
    (Rᵀ * R).PosSemidef := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp [Matrix.mul_apply, mul_comm]
  · intro x
    have hnonneg : 0 ≤ ∑ k : Fin r, (∑ i : Fin m, R k i * x i) ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    have hexp : ∑ k : Fin r, (∑ i : Fin m, R k i * x i) ^ 2 =
        x.sum fun i xi => x.sum fun j xj => star xi * (Rᵀ * R) i j * xj := by
      simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      have hrhs : (∑ i : Fin m, x.sum fun j xj => star (x i) * (Rᵀ * R) i j * xj) =
          ∑ i : Fin m, ∑ j : Fin m, x i * (∑ k : Fin r, R k i * R k j) * x j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [star_trivial, Matrix.mul_apply, Matrix.transpose_apply]
      rw [hrhs]
      calc ∑ k : Fin r, ∑ i : Fin m, ∑ j : Fin m, R k i * x i * (R k j * x j)
          = ∑ i : Fin m, ∑ k : Fin r, ∑ j : Fin m, R k i * x i * (R k j * x j) := Finset.sum_comm
        _ = ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin r, R k i * x i * (R k j * x j) :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ i : Fin m, ∑ j : Fin m, x i * (∑ k : Fin r, R k i * R k j) * x j := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum, Finset.sum_mul]
              exact Finset.sum_congr rfl fun k _ => by ring
    linarith

/-- Any symmetric diagonally dominant real matrix (`∀ i, ∑ j ≠ i, |E i j| ≤ E i i`)
is positive semidefinite. -/
theorem posSemidef_of_diagDom {m : ℕ} (E : Matrix (Fin m) (Fin m) ℝ)
    (hsym : E.IsSymm)
    (hdd : ∀ i : Fin m, (∑ j ∈ Finset.univ.erase i, |E i j|) ≤ E i i) :
    E.PosSemidef := by
  refine ⟨?_, ?_⟩
  · ext i j
    have := congr_fun (congr_fun hsym i) j
    simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using this
  · intro x
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    have hgoal : (∑ i : Fin m, x.sum fun j xj => star (x i) * E i j * xj) =
        ∑ i : Fin m, ∑ j : Fin m, x i * E i j * x j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      simp only [star_trivial]
    rw [hgoal]
    -- Use `2 E i j x i x j ≥ -|E i j| (x i² + x j²)`.
    have h2 : 0 ≤ 2 * ∑ i : Fin m, ∑ j : Fin m, x i * E i j * x j := by
      have hsplit : ∑ i : Fin m, ∑ j : Fin m, x i * E i j * x j =
          (∑ i : Fin m, E i i * (x i) ^ 2) +
          (∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, E i j * x i * x j) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.add_sum_erase Finset.univ (fun j => x i * E i j * x j) (Finset.mem_univ i)]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsplit]
      have hpair : ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i,
          (|E i j| * ((x i) ^ 2 + (x j) ^ 2) + 2 * (E i j * x i * x j)) ≥ 0 := by
        refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
        have h1 : -( |E i j| * (2 * |x i| * |x j|) ) ≤ 2 * (E i j * x i * x j) := by
          have := neg_abs_le (E i j * x i * x j)
          rw [abs_mul, abs_mul] at this
          linarith
        have h2' : 0 ≤ |E i j| * ((|x i| - |x j|) ^ 2) :=
          mul_nonneg (abs_nonneg _) (sq_nonneg _)
        have h3 : (|x i| - |x j|) ^ 2 = (x i) ^ 2 + (x j) ^ 2 - 2 * |x i| * |x j| := by
          rw [sub_sq, sq_abs, sq_abs]; ring
        rw [h3] at h2'
        linarith
      have hswap : ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, |E i j| * (x j) ^ 2 =
          ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, |E i j| * (x i) ^ 2 := by
        have h1 : ∀ f : Fin m → Fin m → ℝ,
            ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, f i j =
            ∑ i : Fin m, ∑ j : Fin m, if j ≠ i then f i j else 0 := by
          intro f
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext j; simp [Finset.mem_erase]
        rw [h1, h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        by_cases hij : j = i
        · subst hij; simp
        · have hji : i ≠ j := Ne.symm hij
          have heq : E j i = E i j := by
            have := congr_fun (congr_fun hsym i) j
            simpa [Matrix.transpose_apply] using this
          simp [hij, hji, heq]
      have hdiag : ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, |E i j| * (x i) ^ 2 ≤
          ∑ i : Fin m, E i i * (x i) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hdd i) (sq_nonneg _)
      have hexpand : ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i,
          (|E i j| * ((x i) ^ 2 + (x j) ^ 2) + 2 * (E i j * x i * x j)) =
          2 * (∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, |E i j| * (x i) ^ 2) +
          2 * (∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, E i j * x i * x j) := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hswap]
        ring
      rw [hexpand] at hpair
      linarith
    linarith

/-- Cholesky + diagonally dominant remainder criterion: if `M = Rᵀ * R + E` with
`E` symmetric and diagonally dominant, then `M.PosSemidef`. -/
theorem posSemidef_of_cholesky_dd {r m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (R : Matrix (Fin r) (Fin m) ℝ)
    (hsym : M.IsSymm)
    (hdd : ∀ i : Fin m, (∑ j ∈ Finset.univ.erase i, |(M - Rᵀ * R) i j|) ≤ (M - Rᵀ * R) i i) :
    M.PosSemidef := by
  have hE_sym : (M - Rᵀ * R).IsSymm := by
    ext i j
    have hm := congr_fun (congr_fun hsym i) j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.mul_apply] at hm ⊢
    rw [hm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hM : M = Rᵀ * R + (M - Rᵀ * R) := by abel
  rw [hM]
  exact (posSemidef_transpose_mul_self R).add (posSemidef_of_diagDom (M - Rᵀ * R) hE_sym hdd)

/-! ## Bachoc–Vallentin Chebyshev-projected kernel `bvQ` on `S²` -/

/-- The degree-`k` Chebyshev-projected kernel on `S²`:
`Q₀(u, v, t) = 1`, `Q₁(u, v, t) = t - u v`,
`Q_{k+2}(u, v, t) = 2 (t - u v) Q_{k+1}(u, v, t) - (1 - u²)(1 - v²) Q_k(u, v, t)`. -/
def bvQ : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _, _, _ => 1
  | 1, u, v, t => t - u * v
  | k + 2, u, v, t =>
      2 * (t - u * v) * bvQ (k + 1) u v t - (1 - u ^ 2) * (1 - v ^ 2) * bvQ k u v t

theorem bvQ_zero (u v t : ℝ) : bvQ 0 u v t = 1 := rfl
theorem bvQ_one (u v t : ℝ) : bvQ 1 u v t = t - u * v := rfl

theorem bvQ_succ_succ (k : ℕ) (u v t : ℝ) :
    bvQ (k + 2) u v t =
      2 * (t - u * v) * bvQ (k + 1) u v t - (1 - u ^ 2) * (1 - v ^ 2) * bvQ k u v t := rfl

/-- On diagonal pairs `(t, t, 1)`, `bvQ k t t 1 = (1 - t²) ^ k`. -/
theorem bvQ_diag (k : ℕ) (t : ℝ) : bvQ k t t 1 = (1 - t ^ 2) ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [bvQ]
    | 1 => simp [bvQ]; ring
    | k + 2 =>
      rw [bvQ_succ_succ, ih (k + 1) (by omega), ih k (by omega)]
      ring

/-- Every unit vector `x ∈ S²` admits an orthonormal tangent frame `{e₁, e₂}` in `x⊥`,
satisfying the projected Parseval identity
`⟪y, e₁⟫ ⟪z, e₁⟫ + ⟪y, e₂⟫ ⟪z, e₂⟫ = ⟪y, z⟫ - ⟪x, y⟫ ⟪x, z⟫`. -/
theorem exists_tangent_frame (x : UnitSphere) :
    ∃ e₁ e₂ : E3, ∀ y z : E3,
      inner ℝ y e₁ * inner ℝ z e₁ + inner ℝ y e₂ * inner ℝ z e₂ =
        inner ℝ y z - inner ℝ x.1 y * inner ℝ x.1 z := by
  have hx : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 = 1 := by
    have h := Geodesic.inner_self_of_norm_one x.2
    rw [PiLp.inner_apply, Fin.sum_univ_three] at h
    simp only [RCLike.inner_apply, conj_trivial] at h
    linarith
  have hinner3 : ∀ a b : E3, inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := fun a b => by
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  by_cases hr : x.1 0 ^ 2 + x.1 1 ^ 2 = 0
  · have hx0 : x.1 0 = 0 := by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
    have hx1 : x.1 1 = 0 := by nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
    have hx2 : x.1 2 ^ 2 = 1 := by linarith
    refine ⟨!₂[(1 : ℝ), 0, 0], !₂[(0 : ℝ), 1, 0], fun y z => ?_⟩
    simp only [hinner3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, hx0, hx1]
    linear_combination (y.1 2 * z.1 2) * hx2
  · have hr_pos : 0 < x.1 0 ^ 2 + x.1 1 ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hr)
    set r : ℝ := Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2)
    have hr_sq : r ^ 2 = x.1 0 ^ 2 + x.1 1 ^ 2 := Real.sq_sqrt hr_pos.le
    have hr_ne : r ≠ 0 := (Real.sqrt_pos.mpr hr_pos).ne'
    refine ⟨!₂[-x.1 1 / r, x.1 0 / r, 0],
            !₂[-x.1 0 * x.1 2 / r, -x.1 1 * x.1 2 / r, r], fun y z => ?_⟩
    simp only [hinner3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    field_simp [hr_ne]
    rw [hr_sq]
    linear_combination ((y.1 0 * x.1 0 + y.1 1 * x.1 1) * (z.1 0 * x.1 0 + z.1 1 * x.1 1) +
      (x.1 0 ^ 2 + x.1 1 ^ 2) * (y.1 2 * z.1 2)) * hx

/-- Complex-projection identity for `bvQ`: for any tangent frame `{e₁, e₂}` of `x⊥`
and `w y = ⟪y, e₁⟫ + i ⟪y, e₂⟫ ∈ ℂ`,
`bvQ k ⟪x, y⟫ ⟪x, z⟫ ⟪y, z⟫ = Re((w y)^k · conj(w z)^k)` for every `k : ℕ`. -/
theorem bvQ_eq_re_complex (x y z : UnitSphere) (e₁ e₂ : E3)
    (hframe : ∀ a b : E3,
      inner ℝ a e₁ * inner ℝ b e₁ + inner ℝ a e₂ * inner ℝ b e₂ =
        inner ℝ a b - inner ℝ x.1 a * inner ℝ x.1 b)
    (k : ℕ) :
    let wy : ℂ := ⟨inner ℝ y.1 e₁, inner ℝ y.1 e₂⟩
    let wz : ℂ := ⟨inner ℝ z.1 e₁, inner ℝ z.1 e₂⟩
    bvQ k (inner ℝ x.1 y.1) (inner ℝ x.1 z.1) (inner ℝ y.1 z.1) =
      (wy ^ k * star (wz ^ k)).re := by
  intro wy wz
  set ζ : ℂ := wy * star wz
  have hζ_re : ζ.re = inner ℝ y.1 z.1 - inner ℝ x.1 y.1 * inner ℝ x.1 z.1 := by
    have h := hframe y.1 z.1
    simp only [ζ, wy, wz, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    linarith
  have hwy_norm : wy.re ^ 2 + wy.im ^ 2 = 1 - inner ℝ x.1 y.1 ^ 2 := by
    have h := hframe y.1 y.1
    rw [Geodesic.inner_self_of_norm_one y.2] at h
    simp only [wy]
    linarith
  have hwz_norm : wz.re ^ 2 + wz.im ^ 2 = 1 - inner ℝ x.1 z.1 ^ 2 := by
    have h := hframe z.1 z.1
    rw [Geodesic.inner_self_of_norm_one z.2] at h
    simp only [wz]
    linarith
  have hζ_norm : ζ.re ^ 2 + ζ.im ^ 2 =
      (1 - inner ℝ x.1 y.1 ^ 2) * (1 - inner ℝ x.1 z.1 ^ 2) := by
    rw [← hwy_norm, ← hwz_norm]
    simp only [ζ, wy, wz, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  have hpow : ∀ n : ℕ, wy ^ n * star (wz ^ n) = ζ ^ n := fun n => by
    rw [star_pow, ← mul_pow]
  rw [hpow]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [bvQ]
    | 1 => simp [bvQ, hζ_re]
    | k + 2 =>
      rw [bvQ_succ_succ, ih (k + 1) (by omega), ih k (by omega), ← hζ_re, ← hζ_norm]
      have hrec : (ζ ^ (k + 2)).re =
          2 * ζ.re * (ζ ^ (k + 1)).re - (ζ.re ^ 2 + ζ.im ^ 2) * (ζ ^ k).re := by
        have h1 : ζ ^ (k + 2) = ζ ^ k * (ζ * ζ) := by ring
        have h2 : ζ ^ (k + 1) = ζ ^ k * ζ := by ring
        rw [h1, h2]
        simp only [Complex.mul_re, Complex.mul_im]
        ring
      linarith

/-- Positive semidefiniteness of the Bachoc–Vallentin kernel `Y_k^3` on `S²`:
for any `k : ℕ`, any PSD matrix `F : Matrix (Fin m) (Fin m) ℝ`, any anchor `x ∈ S²`,
and any finite set of points `s : Finset ι` with `q : ι → UnitSphere`,
`∑ i ∈ s, ∑ j ∈ s, ∑ a, ∑ b, F a b * ⟪x, q i⟫^a * ⟪x, q j⟫^b * bvQ k ⟪x, q i⟫ ⟪x, q j⟫ ⟪q i, q j⟫ ≥ 0`. -/
theorem sum_weighted_bvQ_nonneg {ι : Type*} {m : ℕ} (s : Finset ι)
    (x : UnitSphere) (q : ι → UnitSphere) (k : ℕ)
    {F : Matrix (Fin m) (Fin m) ℝ} (hF : F.PosSemidef) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, ∑ a : Fin m, ∑ b : Fin m,
      F a b * ((inner ℝ x.1 (q i).1) ^ a.val * (inner ℝ x.1 (q j).1) ^ b.val *
        bvQ k (inner ℝ x.1 (q i).1) (inner ℝ x.1 (q j).1) (inner ℝ (q i).1 (q j).1)) := by
  obtain ⟨e₁, e₂, hframe⟩ := exists_tangent_frame x
  let w : ι → ℂ := fun i => ⟨inner ℝ (q i).1 e₁, inner ℝ (q i).1 e₂⟩
  let zR : Fin m → ℝ := fun a => ∑ i ∈ s, (inner ℝ x.1 (q i).1) ^ a.val * ((w i) ^ k).re
  let zI : Fin m → ℝ := fun a => ∑ i ∈ s, (inner ℝ x.1 (q i).1) ^ a.val * ((w i) ^ k).im
  have hR : 0 ≤ ∑ a : Fin m, ∑ b : Fin m, zR a * F a b * zR b := posSemidef_quad_nonneg hF zR
  have hI : 0 ≤ ∑ a : Fin m, ∑ b : Fin m, zI a * F a b * zI b := posSemidef_quad_nonneg hF zI
  have heq :
      (∑ i ∈ s, ∑ j ∈ s, ∑ a : Fin m, ∑ b : Fin m,
        F a b * ((inner ℝ x.1 (q i).1) ^ a.val * (inner ℝ x.1 (q j).1) ^ b.val *
          bvQ k (inner ℝ x.1 (q i).1) (inner ℝ x.1 (q j).1) (inner ℝ (q i).1 (q j).1))) =
      (∑ a : Fin m, ∑ b : Fin m, zR a * F a b * zR b) +
      (∑ a : Fin m, ∑ b : Fin m, zI a * F a b * zI b) := by
    have hre : ∀ i j : ι,
        bvQ k (inner ℝ x.1 (q i).1) (inner ℝ x.1 (q j).1) (inner ℝ (q i).1 (q j).1) =
          ((w i) ^ k).re * ((w j) ^ k).re + ((w i) ^ k).im * ((w j) ^ k).im := fun i j => by
      have h := bvQ_eq_re_complex x (q i) (q j) e₁ e₂ hframe k
      simp only [w, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] at h ⊢
      linarith
    simp_rw [hre]
    rw [← Finset.sum_add_distrib]
    have hswap :
        (∑ i ∈ s, ∑ j ∈ s, ∑ a : Fin m, ∑ b : Fin m,
          F a b * ((inner ℝ x.1 (q i).1) ^ a.val * (inner ℝ x.1 (q j).1) ^ b.val *
            (((w i) ^ k).re * ((w j) ^ k).re + ((w i) ^ k).im * ((w j) ^ k).im))) =
        ∑ a : Fin m, ∑ b : Fin m, ∑ i ∈ s, ∑ j ∈ s,
          F a b * ((inner ℝ x.1 (q i).1) ^ a.val * (inner ℝ x.1 (q j).1) ^ b.val *
            (((w i) ^ k).re * ((w j) ^ k).re + ((w i) ^ k).im * ((w j) ^ k).im)) := by
      calc _ = ∑ i ∈ s, ∑ a : Fin m, ∑ j ∈ s, ∑ b : Fin m, _ :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ a : Fin m, ∑ i ∈ s, ∑ j ∈ s, ∑ b : Fin m, _ := Finset.sum_comm
        _ = ∑ a : Fin m, ∑ i ∈ s, ∑ b : Fin m, ∑ j ∈ s, _ :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ a : Fin m, ∑ b : Fin m, ∑ i ∈ s, ∑ j ∈ s, _ :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [hswap]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [zR, zI]
    have hmul_sum : ∀ (f g : ι → ℝ) (c : ℝ),
        (∑ i ∈ s, f i) * c * (∑ j ∈ s, g j) = ∑ i ∈ s, ∑ j ∈ s, f i * c * g j := fun f g c => by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    rw [hmul_sum, hmul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  linarith

/-! ## Reusable Bachoc–Vallentin three-point SDP bound -/

/-- The univariate (two-point) polynomial `G₂(t)` induced by an augmented `k = 0`
matrix `A₀ : Matrix (Fin (d + 2)) (Fin (d + 2)) ℝ` and matrices
`F : (k : Fin d) → Matrix (Fin (d - k.val)) (Fin (d - k.val)) ℝ` (for `k = 1, …, d`). -/
def bvG2 {d : ℕ} (A0 : Matrix (Fin (d + 2)) (Fin (d + 2)) ℝ)
    (F : (k : Fin d) → Matrix (Fin (d - k.val)) (Fin (d - k.val)) ℝ) (t : ℝ) : ℝ :=
  1 +
  2 * (∑ a : Fin (d + 1), A0 0 a.succ * t ^ a.val) +
  (∑ a : Fin (d + 1), ∑ b : Fin (d + 1), A0 a.succ b.succ * t ^ (a.val + b.val)) +
  (∑ k : Fin d, ∑ a : Fin (d - k.val), ∑ b : Fin (d - k.val),
    F k a b * (t ^ (a.val + b.val) * (1 - t ^ 2) ^ (k.val + 1)))

/-- The unsymmetrized three-point polynomial `G₃(u, v, t)` induced by `A₀` and `F₁, …, F_d`. -/
def bvG3 {d : ℕ} (A0 : Matrix (Fin (d + 2)) (Fin (d + 2)) ℝ)
    (F : (k : Fin d) → Matrix (Fin (d - k.val)) (Fin (d - k.val)) ℝ) (u v t : ℝ) : ℝ :=
  (∑ a : Fin (d + 1), ∑ b : Fin (d + 1), A0 a.succ b.succ * (u ^ a.val * v ^ b.val)) +
  (∑ k : Fin d, ∑ a : Fin (d - k.val), ∑ b : Fin (d - k.val),
    F k a b * (u ^ a.val * v ^ b.val * bvQ (k.val + 1) u v t))

/-- **Bachoc–Vallentin Three-Point SDP Bound on `S²`**:
for any degree `d : ℕ`, threshold `s : ℝ`, symmetric PSD matrix
`A₀ : Matrix (Fin (d + 2)) (Fin (d + 2)) ℝ`, and PSD family `F_k` (`k = 1, …, d`), if
1. `bvG2 A0 F t ≤ 0` for all `t ∈ [-1, s]`, and
2. `sym3 (bvG3 A0 F) u v t ≤ 0` for all `(u, v, t) ∈ InThreePointDomain s`,
then every `(n, s)`-spherical code on `S²` satisfies `(n : ℝ) ≤ 1 + A0 0 0`. -/
theorem bachocVallentin_bound {d n : ℕ} {p : Fin n → UnitSphere} {s : ℝ}
    (hp : IsSphericalCode p s)
    {A0 : Matrix (Fin (d + 2)) (Fin (d + 2)) ℝ} (hA0 : A0.PosSemidef)
    {F : (k : Fin d) → Matrix (Fin (d - k.val)) (Fin (d - k.val)) ℝ}
    (hF : ∀ k : Fin d, (F k).PosSemidef)
    (hG2 : ∀ t : ℝ, -1 ≤ t → t ≤ s → bvG2 A0 F t ≤ 0)
    (hG3 : ∀ u v t : ℝ, InThreePointDomain s u v t → sym3 (bvG3 A0 F) u v t ≤ 0) :
    (n : ℝ) ≤ 1 + A0 0 0 := by
  by_cases hn : n = 0
  · subst hn
    have h00 : 0 ≤ A0 0 0 := hA0.diag_nonneg
    simp only [Nat.cast_zero]
    linarith
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  -- 1. Augmented `k = 0` sum: `0 ≤ ∑ ℓ, v0(ℓ)ᵀ A0 v0(ℓ)`.
  have hA0_sym : ∀ i j : Fin (d + 2), A0 j i = A0 i j := fun i j => by
    have := congr_fun (congr_fun hA0.isHermitian i) j
    simpa [Matrix.conjTranspose_apply] using this
  have hsumA0 : 0 ≤
      (n : ℝ) * A0 0 0 +
      (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ,
        (2 * (∑ a : Fin (d + 1), A0 0 a.succ * (inner ℝ (p ℓ).1 (p i).1) ^ a.val) +
         ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
           A0 a.succ b.succ * (inner ℝ (p ℓ).1 (p i).1) ^ (a.val + b.val))) +
      (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ (Finset.univ.erase ℓ).erase i,
        ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
          A0 a.succ b.succ *
            ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val)) := by
    have hterm : ∀ ℓ : Fin n, 0 ≤
        A0 0 0 +
        (∑ i ∈ Finset.univ.erase ℓ,
          (2 * (∑ a : Fin (d + 1), A0 0 a.succ * (inner ℝ (p ℓ).1 (p i).1) ^ a.val) +
           ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
             A0 a.succ b.succ * (inner ℝ (p ℓ).1 (p i).1) ^ (a.val + b.val))) +
        (∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ (Finset.univ.erase ℓ).erase i,
          ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
            A0 a.succ b.succ *
              ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val)) := by
      intro ℓ
      let v : Fin (d + 2) → ℝ := Fin.cons 1 fun a =>
        ∑ i ∈ Finset.univ.erase ℓ, (inner ℝ (p ℓ).1 (p i).1) ^ a.val
      have hv := posSemidef_quad_nonneg hA0 v
      have hexp : (∑ x : Fin (d + 2), ∑ y : Fin (d + 2), v x * A0 x y * v y) =
          A0 0 0 +
          (∑ i ∈ Finset.univ.erase ℓ,
            2 * (∑ a : Fin (d + 1), A0 0 a.succ * (inner ℝ (p ℓ).1 (p i).1) ^ a.val)) +
          (∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ Finset.univ.erase ℓ,
            ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
              A0 a.succ b.succ *
                ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val)) := by
        rw [Fin.sum_univ_succ]
        rw [Fin.sum_univ_succ (f := fun y : Fin (d + 2) => v 0 * A0 0 y * v y)]
        simp_rw [Fin.sum_univ_succ (f := fun y : Fin (d + 2) => v _ * A0 _ y * v y)]
        simp only [v, Fin.cons_zero, Fin.cons_succ, one_mul, mul_one]
        have hcross : (∑ a : Fin (d + 1), A0 0 a.succ *
            ∑ i ∈ Finset.univ.erase ℓ, (inner ℝ (p ℓ).1 (p i).1) ^ a.val) +
            (∑ a : Fin (d + 1), (∑ i ∈ Finset.univ.erase ℓ,
              (inner ℝ (p ℓ).1 (p i).1) ^ a.val) * A0 a.succ 0) =
            ∑ i ∈ Finset.univ.erase ℓ,
              2 * ∑ a : Fin (d + 1), A0 0 a.succ * (inner ℝ (p ℓ).1 (p i).1) ^ a.val := by
          simp_rw [hA0_sym 0, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ), ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun a _ => by ring
        have hquad : (∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
            (∑ i ∈ Finset.univ.erase ℓ, (inner ℝ (p ℓ).1 (p i).1) ^ a.val) * A0 a.succ b.succ *
            (∑ j ∈ Finset.univ.erase ℓ, (inner ℝ (p ℓ).1 (p j).1) ^ b.val)) =
            ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ Finset.univ.erase ℓ,
              ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
                A0 a.succ b.succ *
                  ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val) := by
          have h1 : ∀ a b : Fin (d + 1),
              (∑ i ∈ Finset.univ.erase ℓ, (inner ℝ (p ℓ).1 (p i).1) ^ a.val) * A0 a.succ b.succ *
              (∑ j ∈ Finset.univ.erase ℓ, (inner ℝ (p ℓ).1 (p j).1) ^ b.val) =
              ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ Finset.univ.erase ℓ,
                A0 a.succ b.succ *
                  ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val) := by
            intro a b
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
          simp_rw [h1]
          calc _ = ∑ a : Fin (d + 1), ∑ i ∈ Finset.univ.erase ℓ, ∑ b : Fin (d + 1),
                    ∑ j ∈ Finset.univ.erase ℓ, _ :=
                  Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            _ = ∑ i ∈ Finset.univ.erase ℓ, ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
                  ∑ j ∈ Finset.univ.erase ℓ, _ := Finset.sum_comm
            _ = ∑ i ∈ Finset.univ.erase ℓ, ∑ a : Fin (d + 1), ∑ j ∈ Finset.univ.erase ℓ,
                  ∑ b : Fin (d + 1), _ :=
                  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            _ = ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ Finset.univ.erase ℓ, ∑ a : Fin (d + 1),
                  ∑ b : Fin (d + 1), _ :=
                  Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        rw [Finset.sum_add_distrib, ← add_assoc, add_right_comm (A0 0 0), add_assoc (A0 0 0),
          add_comm (∑ x : Fin (d + 1), _ * A0 x.succ 0), hcross, hquad]
      have hsplit_ℓ :
          (∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ Finset.univ.erase ℓ,
            ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
              A0 a.succ b.succ *
                ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val)) =
          (∑ i ∈ Finset.univ.erase ℓ,
            ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
              A0 a.succ b.succ * (inner ℝ (p ℓ).1 (p i).1) ^ (a.val + b.val)) +
          (∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ (Finset.univ.erase ℓ).erase i,
            ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
              A0 a.succ b.succ *
                ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← Finset.add_sum_erase (Finset.univ.erase ℓ) _ hi]
        congr 1
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [pow_add]
      rw [hexp, hsplit_ℓ] at hv
      have hcomb :
          (∑ i ∈ Finset.univ.erase ℓ,
            2 * ∑ a : Fin (d + 1), A0 0 a.succ * (inner ℝ (p ℓ).1 (p i).1) ^ a.val) +
          (∑ i ∈ Finset.univ.erase ℓ,
            ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
              A0 a.succ b.succ * (inner ℝ (p ℓ).1 (p i).1) ^ (a.val + b.val)) =
          ∑ i ∈ Finset.univ.erase ℓ,
            (2 * (∑ a : Fin (d + 1), A0 0 a.succ * (inner ℝ (p ℓ).1 (p i).1) ^ a.val) +
             ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
               A0 a.succ b.succ * (inner ℝ (p ℓ).1 (p i).1) ^ (a.val + b.val)) :=
        (Finset.sum_add_distrib).symm
      linarith
    have hsum := Finset.sum_nonneg fun ℓ (_ : ℓ ∈ Finset.univ) => hterm ℓ
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    exact hsum
  -- 2. Higher-degree `k = 1, …, d` sums: `0 ≤ ∑ k, ∑ ℓ, ∑ i ≠ ℓ, ∑ j ≠ ℓ, ⟨F_k, Y_k⟩`.
  have hsumF : 0 ≤
      (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ,
        ∑ k : Fin d, ∑ a : Fin (d - k.val), ∑ b : Fin (d - k.val),
          F k a b * ((inner ℝ (p ℓ).1 (p i).1) ^ (a.val + b.val) *
            (1 - (inner ℝ (p ℓ).1 (p i).1) ^ 2) ^ (k.val + 1))) +
      (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ (Finset.univ.erase ℓ).erase i,
        ∑ k : Fin d, ∑ a : Fin (d - k.val), ∑ b : Fin (d - k.val),
          F k a b * ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val *
            bvQ (k.val + 1) (inner ℝ (p ℓ).1 (p i).1) (inner ℝ (p ℓ).1 (p j).1)
              (inner ℝ (p i).1 (p j).1))) := by
    have hnonneg : 0 ≤ ∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ Finset.univ.erase ℓ,
        ∑ k : Fin d, ∑ a : Fin (d - k.val), ∑ b : Fin (d - k.val),
          F k a b * ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val *
            bvQ (k.val + 1) (inner ℝ (p ℓ).1 (p i).1) (inner ℝ (p ℓ).1 (p j).1)
              (inner ℝ (p i).1 (p j).1)) := by
      refine Finset.sum_nonneg fun ℓ _ => ?_
      have hcomm :
          (∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ Finset.univ.erase ℓ, ∑ k : Fin d,
            ∑ a : Fin (d - k.val), ∑ b : Fin (d - k.val),
              F k a b * ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val *
                bvQ (k.val + 1) (inner ℝ (p ℓ).1 (p i).1) (inner ℝ (p ℓ).1 (p j).1)
                  (inner ℝ (p i).1 (p j).1))) =
          ∑ k : Fin d, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ Finset.univ.erase ℓ,
            ∑ a : Fin (d - k.val), ∑ b : Fin (d - k.val),
              F k a b * ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val *
                bvQ (k.val + 1) (inner ℝ (p ℓ).1 (p i).1) (inner ℝ (p ℓ).1 (p j).1)
                  (inner ℝ (p i).1 (p j).1)) := by
        calc _ = ∑ i ∈ Finset.univ.erase ℓ, ∑ k : Fin d, ∑ j ∈ Finset.univ.erase ℓ, _ :=
                Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ k : Fin d, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ Finset.univ.erase ℓ, _ :=
                Finset.sum_comm
      rw [hcomm]
      exact Finset.sum_nonneg fun k _ =>
        sum_weighted_bvQ_nonneg (Finset.univ.erase ℓ) (p ℓ) p (k.val + 1) (hF k)
    rw [sum_offDiag_triples_split] at hnonneg
    have hdiag :
        (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ,
          ∑ k : Fin d, ∑ a : Fin (d - k.val), ∑ b : Fin (d - k.val),
            F k a b * ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p i).1) ^ b.val *
              bvQ (k.val + 1) (inner ℝ (p ℓ).1 (p i).1) (inner ℝ (p ℓ).1 (p i).1)
                (inner ℝ (p i).1 (p i).1))) =
        ∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ,
          ∑ k : Fin d, ∑ a : Fin (d - k.val), ∑ b : Fin (d - k.val),
            F k a b * ((inner ℝ (p ℓ).1 (p i).1) ^ (a.val + b.val) *
              (1 - (inner ℝ (p ℓ).1 (p i).1) ^ 2) ^ (k.val + 1)) := by
      refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => ?_
      rw [Geodesic.inner_self_of_norm_one (p i).2, bvQ_diag, ← pow_add]
    rwa [hdiag] at hnonneg
  -- 3. Constant identity: `n² = n + ∑ ℓ, ∑ i ≠ ℓ, 1`.
  have hconst : (n : ℝ) ^ 2 = (n : ℝ) + ∑ ℓ : Fin n, ∑ _i ∈ Finset.univ.erase ℓ, (1 : ℝ) := by
    have h1 : ∀ ℓ : Fin n, ∑ _i ∈ Finset.univ.erase ℓ, (1 : ℝ) = (n : ℝ) - 1 := fun ℓ => by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ ℓ), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_sub (Nat.pos_of_ne_zero hn)]
      simp
    simp_rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- 4. Combine into `n² ≤ n * (1 + A0 0 0) + ∑_{ℓ ≠ i} bvG2 + ∑_{distinct} sym3 bvG3`.
  have hcombine : (n : ℝ) ^ 2 ≤
      (n : ℝ) * (1 + A0 0 0) +
      (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, bvG2 A0 F (inner ℝ (p ℓ).1 (p i).1)) +
      (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ (Finset.univ.erase ℓ).erase i,
        bvG3 A0 F (inner ℝ (p ℓ).1 (p i).1) (inner ℝ (p ℓ).1 (p j).1)
          (inner ℝ (p i).1 (p j).1)) := by
    have hG2_sum :
        (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, bvG2 A0 F (inner ℝ (p ℓ).1 (p i).1)) =
        (∑ ℓ : Fin n, ∑ _i ∈ Finset.univ.erase ℓ, (1 : ℝ)) +
        (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ,
          (2 * (∑ a : Fin (d + 1), A0 0 a.succ * (inner ℝ (p ℓ).1 (p i).1) ^ a.val) +
           ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
             A0 a.succ b.succ * (inner ℝ (p ℓ).1 (p i).1) ^ (a.val + b.val))) +
        (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ,
          ∑ k : Fin d, ∑ a : Fin (d - k.val), ∑ b : Fin (d - k.val),
            F k a b * ((inner ℝ (p ℓ).1 (p i).1) ^ (a.val + b.val) *
              (1 - (inner ℝ (p ℓ).1 (p i).1) ^ 2) ^ (k.val + 1))) := by
      simp only [bvG2, Finset.sum_add_distrib]
      ring
    have hG3_sum :
        (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ (Finset.univ.erase ℓ).erase i,
          bvG3 A0 F (inner ℝ (p ℓ).1 (p i).1) (inner ℝ (p ℓ).1 (p j).1)
            (inner ℝ (p i).1 (p j).1)) =
        (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ (Finset.univ.erase ℓ).erase i,
          ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
            A0 a.succ b.succ *
              ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val)) +
        (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∑ j ∈ (Finset.univ.erase ℓ).erase i,
          ∑ k : Fin d, ∑ a : Fin (d - k.val), ∑ b : Fin (d - k.val),
            F k a b * ((inner ℝ (p ℓ).1 (p i).1) ^ a.val * (inner ℝ (p ℓ).1 (p j).1) ^ b.val *
              bvQ (k.val + 1) (inner ℝ (p ℓ).1 (p i).1) (inner ℝ (p ℓ).1 (p j).1)
                (inner ℝ (p i).1 (p j).1))) := by
      simp only [bvG3, Finset.sum_add_distrib]
    linarith
  -- 5. Apply `hG2 ≤ 0` on pairs and `sym3 bvG3 ≤ 0` on distinct triples.
  have hpair_le : (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ,
      bvG2 A0 F (inner ℝ (p ℓ).1 (p i).1)) ≤ 0 := by
    refine Finset.sum_nonpos fun ℓ _ => Finset.sum_nonpos fun i hi => ?_
    have hne : ℓ ≠ i := (Finset.mem_erase.mp hi).1.symm
    exact hG2 _ (neg_one_le_inner (p ℓ) (p i)) (hp ℓ i hne)
  have htriple_le : (∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ,
      ∑ j ∈ (Finset.univ.erase ℓ).erase i,
        bvG3 A0 F (inner ℝ (p ℓ).1 (p i).1) (inner ℝ (p ℓ).1 (p j).1)
          (inner ℝ (p i).1 (p j).1)) ≤ 0 := by
    rw [sum_distinct_triples_eq_sym3]
    refine Finset.sum_nonpos fun ℓ _ => Finset.sum_nonpos fun i hi =>
      Finset.sum_nonpos fun j hj => ?_
    have hℓi : ℓ ≠ i := (Finset.mem_erase.mp hi).1.symm
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    have hℓj : ℓ ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1.symm
    exact hG3 _ _ _ (inThreePointDomain_of_isSphericalCode hp hℓi hℓj hij)
  have hsq : (n : ℝ) ^ 2 ≤ (n : ℝ) * (1 + A0 0 0) := by linarith
  nlinarith

end Geodesy.Spherical
