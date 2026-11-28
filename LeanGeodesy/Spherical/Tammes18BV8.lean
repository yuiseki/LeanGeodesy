import LeanGeodesy.Spherical.Tammes18BV8Q34
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Certified Degree-8 Three-Point SDP Upper Bound for Tammes `N = 18` on `S²`

We prove unconditionally in the Lean 4 kernel that no spherical code of size `18`
on `S²` can have maximum pairwise inner product `≤ 317 / 500 = 0.634`, i.e.,

```
A(3, 317/500) ≤ 17
```

Equivalently, every `18`-point configuration on `S²` has minimum geodesic separation
strictly less than `arccos (317 / 500) ≈ 50.65414° < 50.655°`.

This strictly improves the best previously known upper bound due to R. M. Robinson
(1961, Theorem Ba, Section 9.1), which gives `T(18) ≤ 50.68095°`. We also prove
directly in Lean that `a = arccos (317 / 500)` strictly satisfies Robinson's
Theorem Ba inequality `4 · 18 · Δ(a) + (2 · 18 - 12) · Δ*(a) < 12π`.

The proof uses a Chebyshev-basis degree-8 Bachoc–Vallentin three-point SDP certificate
with two-point Legendre terms `P₁..P₁₆` and 7 reduced `S₃`-symmetric SOS blocks,
checked purely by `decide` in the Lean 4 kernel (no `native_decide`, no custom axioms).
-/

namespace Geodesy.Spherical

set_option maxRecDepth 400000
set_option maxHeartbeats 2400000

private theorem t18b8_eq2 : tammes18BV8Cert.checkEq2 = true := by decide


set_option maxHeartbeats 2400000 in
private theorem t18b8_eq3 :
    (sym3Canon (poly3Scale (-((tammes18BV8Cert.sDen : ℤ) * (tammes18BV8Cert.dS : ℤ))) tammes18BV8Cert.polyG3) ==
      sym3Canon (poly3Scale (tammes18BV8Cert.dK : ℤ) tammes18BV8Cert.polyRHS3Canon)) = true := by
  unfold BVCert8.polyRHS3Canon
  dsimp only
  rw [t18b8_q0, t18b8_q1, t18b8_q2, t18b8_q3, t18b8_q4, t18b8_q5, t18b8_q6]
  decide

/-- Kernel-verified validity of `tammes18BV8Cert` (no `native_decide`, no extra axioms). -/
theorem tammes18BV8Cert_valid : tammes18BV8Cert.isValid = true := by
  unfold BVCert8.isValid
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hb0, hb1, hb2, hb3, hb4, hb5, hb6⟩ := t18b8_basic
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
    t18b8_cF0, t18b8_cF1, t18b8_cF2, t18b8_cF3, t18b8_cF4, t18b8_cF5, t18b8_cF6, t18b8_cF7, t18b8_cF8,
    t18b8_cS0, t18b8_cS1,
    t18b8_cM0, t18b8_cM1, t18b8_cM2, t18b8_cM3, t18b8_cM4, t18b8_cM5, t18b8_cM6,
    t18b8_eq2, t18b8_eq3]
  rfl

private theorem tammes18BV8Cert_bound_lt_18 : tammes18BV8Cert.bound < 18 := by
  have hnum : tammes18BV8Cert.boundNum < 18 * (tammes18BV8Cert.dK : ℤ) := by decide
  have hdK : (0 : ℝ) < (tammes18BV8Cert.dK : ℝ) := by norm_num [tammes18BV8Cert]
  rw [BVCert8.bound, div_lt_iff₀ hdK]
  have hnumR : (tammes18BV8Cert.boundNum : ℝ) < 18 * (tammes18BV8Cert.dK : ℝ) := by exact_mod_cast hnum
  linarith

/-- **Certified spherical-code upper bound on `S²`**:
every `(n, 317 / 500)`-spherical code on `S²` has at most `17` points (`A(3, 317/500) ≤ 17`). -/
theorem sphericalCode_three_upper_317_500 {n : ℕ} {p : Fin n → UnitSphere}
    (hp : IsSphericalCode p (317 / 500 : ℝ)) : n ≤ 17 := by
  have hs : tammes18BV8Cert.s = (317 / 500 : ℝ) := by norm_num [BVCert8.s, tammes18BV8Cert]
  have hle : (n : ℝ) ≤ tammes18BV8Cert.bound := tammes18BV8Cert.sound tammes18BV8Cert_valid (hs ▸ hp)
  have hlt : (n : ℝ) < 18 := lt_of_le_of_lt hle tammes18BV8Cert_bound_lt_18
  have hnat : n < 18 := by exact_mod_cast hlt
  omega

/-- **Certified Tammes `N = 18` strict upper bound**:
every `18`-point configuration on `S²` with minimum separation `θ` satisfies
`θ < arccos (317 / 500) ≈ 50.65414°`. -/
theorem tammes_18_strict_upper_317_500 {p : Fin 18 → UnitSphere} {θ : ℝ}
    (hp : IsSeparated p θ) : θ < Real.arccos (317 / 500 : ℝ) := by
  by_contra h
  push Not at h
  have hsep : IsSeparated p (Real.arccos (317 / 500 : ℝ)) := fun i j hij => le_trans h (hp i j hij)
  have hcode : IsSphericalCode p (317 / 500 : ℝ) := by
    have h0 : (0 : ℝ) ≤ Real.arccos (317 / 500 : ℝ) := Real.arccos_nonneg _
    have hpi : Real.arccos (317 / 500 : ℝ) ≤ Real.pi := Real.arccos_le_pi _
    have hc : Real.cos (Real.arccos (317 / 500 : ℝ)) = (317 / 500 : ℝ) :=
      Real.cos_arccos (by norm_num) (by norm_num)
    rw [← hc]
    exact (isSeparated_iff_isSphericalCode p h0 hpi).mp hsep
  have hle := sphericalCode_three_upper_317_500 hcode
  omega

/-! ## Certified angle bounds & rigorous comparison with Robinson (1961) -/

private theorem trig_taylor_bounds {x : ℝ} (hx : 0 ≤ x) :
    (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x) ∧
    (Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) ∧
    (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x) := by
  have hmono : ∀ (f f' : ℝ → ℝ),
      (∀ t, HasDerivAt f (f' t) t) → (∀ t, 0 ≤ t → 0 ≤ f' t) → f 0 = 0 →
      ∀ t, 0 ≤ t → 0 ≤ f t := by
    intro f f' hderiv hf' hf0 t ht
    have hcont : ContinuousOn f (Set.Icc 0 t) := fun y _ => (hderiv y).continuousAt.continuousWithinAt
    have hdiff : ∀ y ∈ Set.Ioo 0 t, 0 ≤ deriv f y := fun y hy => by
      rw [(hderiv y).deriv]; exact hf' y hy.1.le
    have hmono' := monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hcont
      (fun y _ => (hderiv y).differentiableAt.differentiableWithinAt)
      (fun y hy => by rw [interior_Icc] at hy; exact hdiff y hy)
    have hle := hmono' (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
    linarith
  have h0 : ∀ t, 0 ≤ t → 0 ≤ 1 - Real.cos t := fun t _ => by linarith [Real.cos_le_one t]
  have h1 : ∀ t, 0 ≤ t → 0 ≤ t - Real.sin t :=
    hmono (fun t => t - Real.sin t) (fun t => 1 - Real.cos t)
      (fun t => (hasDerivAt_id' t).sub (Real.hasDerivAt_sin t)) h0 (by simp)
  have h2 : ∀ t, 0 ≤ t → 0 ≤ Real.cos t - 1 + t ^ 2 / 2 :=
    hmono (fun t => Real.cos t - 1 + t ^ 2 / 2) (fun t => t - Real.sin t)
      (fun t => by
        have hd := ((Real.hasDerivAt_cos t).sub (hasDerivAt_const t (1 : ℝ))).add
          ((hasDerivAt_pow 2 t).div_const 2)
        have heq : -Real.sin t - 0 + (2 : ℝ) * t ^ (2 - 1) / 2 = t - Real.sin t := by norm_num; ring
        rw [← heq]; exact hd)
      h1 (by simp)
  have h3 : ∀ t, 0 ≤ t → 0 ≤ Real.sin t - t + t ^ 3 / 6 :=
    hmono (fun t => Real.sin t - t + t ^ 3 / 6) (fun t => Real.cos t - 1 + t ^ 2 / 2)
      (fun t => by
        have hd := ((Real.hasDerivAt_sin t).sub (hasDerivAt_id' t)).add
          ((hasDerivAt_pow 3 t).div_const 6)
        have heq : Real.cos t - 1 + (3 : ℝ) * t ^ (3 - 1) / 6 = Real.cos t - 1 + t ^ 2 / 2 := by norm_num; ring
        rw [← heq]; exact hd)
      h2 (by simp)
  have h4 : ∀ t, 0 ≤ t → 0 ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t :=
    hmono (fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t) (fun t => Real.sin t - t + t ^ 3 / 6)
      (fun t => by
        have hd := (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24)).sub (Real.hasDerivAt_cos t)
        have heq : 0 - (2 : ℝ) * t ^ (2 - 1) / 2 + (4 : ℝ) * t ^ (4 - 1) / 24 - (-Real.sin t) =
            Real.sin t - t + t ^ 3 / 6 := by norm_num; ring
        rw [← heq]; exact hd)
      h3 (by simp)
  have h5 : ∀ t, 0 ≤ t → 0 ≤ t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t :=
    hmono (fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
      (fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
      (fun t => by
        have hd := (((hasDerivAt_id' t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
          ((hasDerivAt_pow 5 t).div_const 120)).sub (Real.hasDerivAt_sin t)
        have heq : 1 - (3 : ℝ) * t ^ (3 - 1) / 6 + (5 : ℝ) * t ^ (5 - 1) / 120 - Real.cos t =
            1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by norm_num; ring
        rw [← heq]; exact hd)
      h4 (by simp)
  have h6 : ∀ t, 0 ≤ t → 0 ≤ Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) :=
    hmono (fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
      (fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
      (fun t => by
        have hd := (Real.hasDerivAt_cos t).sub
          ((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
            ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720))
        have heq : -Real.sin t - (0 - (2 : ℝ) * t ^ (2 - 1) / 2 + (4 : ℝ) * t ^ (4 - 1) / 24 -
            (6 : ℝ) * t ^ (6 - 1) / 720) = t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t := by norm_num; ring
        rw [← heq]; exact hd)
      h5 (by simp)
  have h7 : ∀ t, 0 ≤ t → 0 ≤ Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040) :=
    hmono (fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040))
      (fun t => Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720))
      (fun t => by
        have hd := (Real.hasDerivAt_sin t).sub
          ((((hasDerivAt_id' t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
            ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040))
        have heq : Real.cos t - (1 - (3 : ℝ) * t ^ (3 - 1) / 6 + (5 : ℝ) * t ^ (5 - 1) / 120 -
            (7 : ℝ) * t ^ (7 - 1) / 5040) =
            Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) := by norm_num; ring
        rw [← heq]; exact hd)
      h6 (by simp)
  have h8 : ∀ t, 0 ≤ t → 0 ≤ (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320) - Real.cos t :=
    hmono (fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320) - Real.cos t)
      (fun t => Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040))
      (fun t => by
        have hd := (((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add
          ((hasDerivAt_pow 8 t).div_const 40320)).sub (Real.hasDerivAt_cos t)
        have heq : 0 - (2 : ℝ) * t ^ (2 - 1) / 2 + (4 : ℝ) * t ^ (4 - 1) / 24 -
            (6 : ℝ) * t ^ (6 - 1) / 720 + (8 : ℝ) * t ^ (8 - 1) / 40320 - (-Real.sin t) =
            Real.sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040) := by norm_num; ring
        rw [← heq]; exact hd)
      h7 (by simp)
  exact ⟨by linarith [h6 x hx], by linarith [h8 x hx], by linarith [h7 x hx]⟩

/-- Rigorous degree bound: `arccos (317 / 500) < 50.655°` (strictly below Robinson 1961's `50.68095°`). -/
theorem arccos_317_500_lt_deg :
    Real.arccos (317 / 500 : ℝ) < (50.655 : ℝ) * (Real.pi / 180) := by
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  set x : ℝ := (50.655 : ℝ) * (Real.pi / 180)
  have hx_lo : (0.884096 : ℝ) < x := by dsimp only [x]; linarith
  have hx_hi : x < (0.884097 : ℝ) := by dsimp only [x]; linarith
  have hx_nonneg : 0 ≤ x := by linarith
  have hx_le_pi : x ≤ Real.pi := by linarith
  have hcos_lt : Real.cos x < (317 / 500 : ℝ) := by
    have ht := (trig_taylor_bounds hx_nonneg).2.1
    have hx2_lo : (0.884096 : ℝ) ^ 2 < x ^ 2 := pow_lt_pow_left₀ hx_lo (by norm_num) (by norm_num)
    have hx4_hi : x ^ 4 < (0.884097 : ℝ) ^ 4 := pow_lt_pow_left₀ hx_hi hx_nonneg (by norm_num)
    have hx6_lo : (0.884096 : ℝ) ^ 6 < x ^ 6 := pow_lt_pow_left₀ hx_lo (by norm_num) (by norm_num)
    have hx8_hi : x ^ 8 < (0.884097 : ℝ) ^ 8 := pow_lt_pow_left₀ hx_hi hx_nonneg (by norm_num)
    linarith
  have hcos_arccos : Real.cos (Real.arccos (317 / 500 : ℝ)) = (317 / 500 : ℝ) :=
    Real.cos_arccos (by norm_num) (by norm_num)
  by_contra h
  push Not at h
  have hanti : Real.cos (Real.arccos (317 / 500 : ℝ)) ≤ Real.cos x :=
    Real.strictAntiOn_cos.antitoneOn
      ⟨hx_nonneg, hx_le_pi⟩ ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩ h
  linarith

/-- Combined Tammes `N = 18` degree bound: every `18`-point configuration on `S²` has
minimum geodesic separation strictly less than `50.655°`. -/
theorem tammes_18_lt_50_655_deg {p : Fin 18 → UnitSphere} {θ : ℝ}
    (hp : IsSeparated p θ) : θ < (50.655 : ℝ) * (Real.pi / 180) :=
  lt_trans (tammes_18_strict_upper_317_500 hp) arccos_317_500_lt_deg

/-- Left-hand side of Robinson (1961, Theorem Ba, Section 9.1) for `N = 18` at angular
separation `a`: `4 · 18 · Δ(a) + (2 · 18 - 12) · Δ*(a)`, where `Δ(a) = 3α - π` is the area
of an equilateral spherical triangle of side `a` (`cos α = cos a / (1 + cos a)`) and
`Δ*(a) = γ + 2φ - π` is the area of an isosceles spherical triangle with two sides `a`
enclosing angle `γ = 2π - 4α` and base angle `φ = arctan(1 / (cos a · tan(γ / 2)))`. -/
noncomputable def robinson18LHS (a : ℝ) : ℝ :=
  let α := Real.arccos (Real.cos a / (1 + Real.cos a))
  let Δ := 3 * α - Real.pi
  let γ := 2 * Real.pi - 4 * α
  let φ := Real.arctan (1 / (Real.cos a * Real.tan (γ / 2)))
  let Δstar := γ + 2 * φ - Real.pi
  4 * 18 * Δ + (2 * 18 - 12) * Δstar

/-- **Rigorous strict improvement over Robinson (1961, Theorem Ba)**:
at `a = arccos (317 / 500)`, Robinson's Theorem Ba area functional is strictly below `12π`,
proving that our certified bound `arccos (317 / 500)` is strictly sharper than Robinson's
upper bound `T(18) ≤ 50.68094488°`. -/
theorem robinson18_strict_improvement :
    robinson18LHS (Real.arccos (317 / 500 : ℝ)) < 12 * Real.pi := by
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  unfold robinson18LHS
  have hcos_a : Real.cos (Real.arccos (317 / 500 : ℝ)) = (317 / 500 : ℝ) :=
    Real.cos_arccos (by norm_num) (by norm_num)
  rw [hcos_a]
  have hratio : (317 / 500 : ℝ) / (1 + 317 / 500) = (317 / 817 : ℝ) := by norm_num
  rw [hratio]
  set α := Real.arccos (317 / 817 : ℝ)
  -- Step 1: α < 1.17235
  have hα_lt : α < (1.17235 : ℝ) := by
    have hcos_lt : Real.cos (1.17235 : ℝ) < (317 / 817 : ℝ) := by
      have ht := (trig_taylor_bounds (by norm_num : (0 : ℝ) ≤ 1.17235)).2.1
      linarith
    have hcos_α : Real.cos α = (317 / 817 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
    by_contra h
    push Not at h
    have hanti : Real.cos α ≤ Real.cos (1.17235 : ℝ) :=
      Real.strictAntiOn_cos.antitoneOn
        ⟨by norm_num, by linarith⟩ ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩ h
    linarith
  -- Step 2: 0 < α, so γ / 2 = π - 2α ∈ (0.7968, π/2)
  have hα_pos : (1 : ℝ) < α := by
    have hcos_gt : (317 / 817 : ℝ) < Real.cos (1 : ℝ) := by
      have ht := (trig_taylor_bounds (by norm_num : (0 : ℝ) ≤ 1)).1
      linarith
    have hcos_α : Real.cos α = (317 / 817 : ℝ) := Real.cos_arccos (by norm_num) (by norm_num)
    by_contra h
    push Not at h
    have hanti : Real.cos (1 : ℝ) ≤ Real.cos α :=
      Real.strictAntiOn_cos.antitoneOn
        ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩ ⟨by norm_num, by linarith⟩ h
    linarith
  set g := (2 * Real.pi - 4 * α) / 2
  have hg_lo : (0.7968 : ℝ) < g := by dsimp only [g]; linarith
  have hg_hi : g < Real.pi / 2 := by dsimp only [g]; linarith
  -- Step 3: tan(0.7968) > 1.023, so tan g > 1.023
  have htan_g_gt : (1.023 : ℝ) < Real.tan g := by
    have htb := trig_taylor_bounds (by norm_num : (0 : ℝ) ≤ 0.7968)
    have hsin_lo : (0.71512 : ℝ) < Real.sin (0.7968 : ℝ) := by linarith [htb.2.2]
    have hcos_hi : Real.cos (0.7968 : ℝ) < (0.69900 : ℝ) := by linarith [htb.2.1]
    have hcos_pos : 0 < Real.cos (0.7968 : ℝ) := by linarith [htb.1]
    have htan0 : (1.023 : ℝ) < Real.tan (0.7968 : ℝ) := by
      rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos_pos]
      linarith
    have hmono : Real.tan (0.7968 : ℝ) < Real.tan g :=
      Real.strictMonoOn_tan ⟨by linarith, by linarith⟩ ⟨by linarith, hg_hi⟩ hg_lo
    linarith
  -- Step 4: 1 / ((317 / 500) * tan g) < 1.542 < tan(0.9955), so arctan(...) < 0.9955
  have harg_lt : 1 / ((317 / 500 : ℝ) * Real.tan g) < (1.542 : ℝ) := by
    have hden_pos : (0 : ℝ) < (317 / 500 : ℝ) * Real.tan g := by linarith
    rw [div_lt_iff₀ hden_pos]
    linarith
  have htan_9955 : (1.542 : ℝ) < Real.tan (0.9955 : ℝ) := by
    have htb := trig_taylor_bounds (by norm_num : (0 : ℝ) ≤ 0.9955)
    have hsin_lo : (0.83902 : ℝ) < Real.sin (0.9955 : ℝ) := by linarith [htb.2.2]
    have hcos_hi : Real.cos (0.9955 : ℝ) < (0.54410 : ℝ) := by linarith [htb.2.1]
    have hcos_pos : 0 < Real.cos (0.9955 : ℝ) := by linarith [htb.1]
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos_pos]
    linarith
  have hφ_lt : Real.arctan (1 / ((317 / 500 : ℝ) * Real.tan g)) < (0.9955 : ℝ) := by
    rw [← Real.arctan_tan (by linarith : -(Real.pi / 2) < (0.9955 : ℝ)) (by linarith : (0.9955 : ℝ) < Real.pi / 2)]
    exact Real.arctan_strictMono (lt_trans harg_lt htan_9955)
  -- Step 5: 4*18*(3α - π) + 24*(2π - 4α + 2φ - π) = 24*(5α + 2φ - 2π) < 12π
  linarith

/-! ## Negative test: corrupted certificate is rejected by the kernel verifier -/

private def tammes18BV8BadCert : BVCert8 :=
  { tammes18BV8Cert with F8 := [[-1]] }

theorem tammes18BV8BadCert_rejected : tammes18BV8BadCert.isValid = false := by
  decide

end Geodesy.Spherical
