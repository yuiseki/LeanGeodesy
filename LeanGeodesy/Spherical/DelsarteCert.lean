import LeanGeodesy.Spherical.Delsarte

/-!
# Rational Delsarte certificate verifier on `S²`

This module separates external search from formal verification (Priority 3):
an external LP/SDP solver produces a rational certificate `DelsarteCert`
consisting of rational Legendre coefficients `c : Fin 5 → ℚ`, a rational
inner-product threshold `s : ℚ`, and a rational split point `m : ℚ` in `[-1, s]`.

The Lean verifier `DelsarteCert.isValid` checks:
1. `-1 < s` and `-1 ≤ m ≤ s`,
2. `0 < c 0` and `∀ k, 0 ≤ c k`,
3. all five degree-4 Bernstein coefficients of `f(t) = ∑ k, c k * Pₖ(t)` on
   `[-1, m]` and on `[m, s]` are `≤ 0` (which certifies `f(t) ≤ 0` for all
   `t ∈ [-1, s]`, including polynomials with an interior double root at `m`).

Every check is purely rational arithmetic, verified in Lean's kernel by
`norm_num` (no `native_decide`, no extra axioms). The soundness theorem
`DelsarteCert.sound` proves that any accepted certificate yields a valid upper
bound `(n : ℝ) ≤ (cert.bound : ℝ)` on every `(n, s)`-spherical code on `S²`,
without trusting the external searcher.

Worked examples reproduce `N ≤ 3` (`s = -1/2`), `N ≤ 4` (`s = -1/3`), `N ≤ 6`
(`s = 0`), and `N ≤ 11` (`s = 11/25 < 1/√5`), and negative tests confirm that
invalid certificates are rejected.
-/

namespace Geodesy.Spherical

/-- A rational degree-4 Delsarte LP certificate on `S²` with a rational
Bernstein subdivision point `m ∈ [-1, s]`. -/
structure DelsarteCert where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  c3 : ℚ
  c4 : ℚ
  s  : ℚ
  m  : ℚ
  deriving DecidableEq

namespace DelsarteCert

/-- View the rational coefficients as `Fin 5 → ℝ`. -/
def toRealCoeff (cert : DelsarteCert) : Fin 5 → ℝ
  | ⟨0, _⟩ => cert.c0
  | ⟨1, _⟩ => cert.c1
  | ⟨2, _⟩ => cert.c2
  | ⟨3, _⟩ => cert.c3
  | ⟨4, _⟩ => cert.c4

/-- Power-basis coefficients `a₀ + a₁ t + a₂ t² + a₃ t³ + a₄ t⁴` of
`∑ k, c k * Pₖ(t)`. -/
def powerCoeffs (cert : DelsarteCert) : ℚ × ℚ × ℚ × ℚ × ℚ :=
  let a0 := cert.c0 - cert.c2 / 2 + 3 * cert.c4 / 8
  let a1 := cert.c1 - 3 * cert.c3 / 2
  let a2 := 3 * cert.c2 / 2 - 30 * cert.c4 / 8
  let a3 := 5 * cert.c3 / 2
  let a4 := 35 * cert.c4 / 8
  (a0, a1, a2, a3, a4)

/-- Degree-4 Bernstein coefficients of `f(lo + (hi - lo) u)` on `u ∈ [0, 1]`. -/
def bernsteinOn (cert : DelsarteCert) (lo hi : ℚ) : ℚ × ℚ × ℚ × ℚ × ℚ :=
  let (a0, a1, a2, a3, a4) := cert.powerCoeffs
  let h := hi - lo
  let d0 := a0 + a1 * lo + a2 * lo ^ 2 + a3 * lo ^ 3 + a4 * lo ^ 4
  let d1 := h * (a1 + 2 * a2 * lo + 3 * a3 * lo ^ 2 + 4 * a4 * lo ^ 3)
  let d2 := h ^ 2 * (a2 + 3 * a3 * lo + 6 * a4 * lo ^ 2)
  let d3 := h ^ 3 * (a3 + 4 * a4 * lo)
  let d4 := h ^ 4 * a4
  let b0 := d0
  let b1 := d0 + d1 / 4
  let b2 := d0 + d1 / 2 + d2 / 6
  let b3 := d0 + 3 * d1 / 4 + d2 / 2 + d3 / 4
  let b4 := d0 + d1 + d2 + d3 + d4
  (b0, b1, b2, b3, b4)

/-- Check that all five Bernstein coefficients on `[lo, hi]` are `≤ 0`. -/
def bernsteinNonpos (cert : DelsarteCert) (lo hi : ℚ) : Bool :=
  let (b0, b1, b2, b3, b4) := cert.bernsteinOn lo hi
  decide (b0 ≤ 0) &&
  decide (b1 ≤ 0) &&
  decide (b2 ≤ 0) &&
  decide (b3 ≤ 0) &&
  decide (b4 ≤ 0)

/-- The rational upper bound `f(1) / c₀ = (c₀ + c₁ + c₂ + c₃ + c₄) / c₀`. -/
def bound (cert : DelsarteCert) : ℚ :=
  (cert.c0 + cert.c1 + cert.c2 + cert.c3 + cert.c4) / cert.c0

/-- Computable certificate checker: verifies `-1 < s`, `-1 ≤ m ≤ s`, `c₀ > 0`,
`cₖ ≥ 0`, and nonpositivity of all degree-4 Bernstein coefficients on `[-1, m]`
and on `[m, s]`. -/
def isValid (cert : DelsarteCert) : Bool :=
  decide (-1 < cert.s) &&
  decide (-1 ≤ cert.m) &&
  decide (cert.m ≤ cert.s) &&
  decide (0 < cert.c0) &&
  decide (0 ≤ cert.c1) &&
  decide (0 ≤ cert.c2) &&
  decide (0 ≤ cert.c3) &&
  decide (0 ≤ cert.c4) &&
  cert.bernsteinNonpos (-1) cert.m &&
  cert.bernsteinNonpos cert.m cert.s

/-- Algebraic identity: evaluating `legendreEval` at `t = lo + (hi - lo) u`
matches the degree-4 Bernstein polynomial on `[lo, hi]`. -/
theorem eval_eq_bernsteinOn (cert : DelsarteCert) (lo hi : ℚ) (u : ℝ) :
    legendreEval cert.toRealCoeff ((lo : ℝ) + ((hi : ℝ) - (lo : ℝ)) * u) =
      ((cert.bernsteinOn lo hi).1 : ℝ) * (1 - u) ^ 4 +
      4 * ((cert.bernsteinOn lo hi).2.1 : ℝ) * (1 - u) ^ 3 * u +
      6 * ((cert.bernsteinOn lo hi).2.2.1 : ℝ) * (1 - u) ^ 2 * u ^ 2 +
      4 * ((cert.bernsteinOn lo hi).2.2.2.1 : ℝ) * (1 - u) * u ^ 3 +
      ((cert.bernsteinOn lo hi).2.2.2.2 : ℝ) * u ^ 4 := by
  simp only [bernsteinOn, powerCoeffs, legendreEval, Fin.sum_univ_five, toRealCoeff, legendreP]
  push_cast
  ring

private theorem eval_nonpos_of_bernsteinNonpos (cert : DelsarteCert) {lo hi : ℚ}
    (hb : cert.bernsteinNonpos lo hi = true) {t : ℝ} (hlo : (lo : ℝ) ≤ t) (hhi : t ≤ (hi : ℝ)) :
    legendreEval cert.toRealCoeff t ≤ 0 := by
  simp only [bernsteinNonpos, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨hb0, hb1⟩, hb2⟩, hb3⟩, hb4⟩ := hb
  have hb0R : ((cert.bernsteinOn lo hi).1 : ℝ) ≤ 0 := by exact_mod_cast hb0
  have hb1R : ((cert.bernsteinOn lo hi).2.1 : ℝ) ≤ 0 := by exact_mod_cast hb1
  have hb2R : ((cert.bernsteinOn lo hi).2.2.1 : ℝ) ≤ 0 := by exact_mod_cast hb2
  have hb3R : ((cert.bernsteinOn lo hi).2.2.2.1 : ℝ) ≤ 0 := by exact_mod_cast hb3
  have hb4R : ((cert.bernsteinOn lo hi).2.2.2.2 : ℝ) ≤ 0 := by exact_mod_cast hb4
  rcases eq_or_lt_of_le (hlo.trans hhi) with hdeg | hlt
  · have ht : t = (lo : ℝ) + ((hi : ℝ) - (lo : ℝ)) * 0 := by linarith
    rw [ht, eval_eq_bernsteinOn]
    norm_num
    exact hb0
  · set u : ℝ := (t - (lo : ℝ)) / ((hi : ℝ) - (lo : ℝ))
    have hden : (0 : ℝ) < (hi : ℝ) - (lo : ℝ) := by linarith
    have hu0 : 0 ≤ u := div_nonneg (by linarith) hden.le
    have hu1 : u ≤ 1 := (div_le_one hden).mpr (by linarith)
    have h1u : 0 ≤ 1 - u := by linarith
    have ht : t = (lo : ℝ) + ((hi : ℝ) - (lo : ℝ)) * u := by
      simp only [u]
      field_simp [hden.ne']
      ring
    rw [ht, eval_eq_bernsteinOn]
    have t0 : ((cert.bernsteinOn lo hi).1 : ℝ) * (1 - u) ^ 4 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hb0R (pow_nonneg h1u 4)
    have t1 : 4 * ((cert.bernsteinOn lo hi).2.1 : ℝ) * (1 - u) ^ 3 * u ≤ 0 := by
      have : 0 ≤ (1 - u) ^ 3 * u := mul_nonneg (pow_nonneg h1u 3) hu0
      nlinarith
    have t2 : 6 * ((cert.bernsteinOn lo hi).2.2.1 : ℝ) * (1 - u) ^ 2 * u ^ 2 ≤ 0 := by
      have : 0 ≤ (1 - u) ^ 2 * u ^ 2 := mul_nonneg (pow_nonneg h1u 2) (pow_nonneg hu0 2)
      nlinarith
    have t3 : 4 * ((cert.bernsteinOn lo hi).2.2.2.1 : ℝ) * (1 - u) * u ^ 3 ≤ 0 := by
      have : 0 ≤ (1 - u) * u ^ 3 := mul_nonneg h1u (pow_nonneg hu0 3)
      nlinarith
    have t4 : ((cert.bernsteinOn lo hi).2.2.2.2 : ℝ) * u ^ 4 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hb4R (pow_nonneg hu0 4)
    linarith

/-- Soundness of the rational Delsarte certificate verifier:
any certificate passing `cert.isValid = true` certifies `(n : ℝ) ≤ cert.bound`
for every `(n, cert.s)`-spherical code on `S²`. -/
theorem sound {cert : DelsarteCert} (hval : cert.isValid = true)
    {n : ℕ} {p : Fin n → UnitSphere} (hp : IsSphericalCode p (cert.s : ℝ)) :
    (n : ℝ) ≤ (cert.bound : ℝ) := by
  simp only [isValid, Bool.and_eq_true, decide_eq_true_eq] at hval
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_hs, _hm1⟩, _hm2⟩, hc0⟩, hc1⟩, hc2⟩, hc3⟩, hc4⟩, hleft⟩, hright⟩ := hval
  have hc0R : (0 : ℝ) < cert.toRealCoeff 0 := by
    simpa [toRealCoeff] using (show (0 : ℝ) < cert.c0 by exact_mod_cast hc0)
  have hcR : ∀ k : Fin 5, 0 ≤ cert.toRealCoeff k := by
    intro k
    fin_cases k
    · exact hc0R.le
    · simp only [toRealCoeff]; exact_mod_cast hc1
    · simp only [toRealCoeff]; exact_mod_cast hc2
    · simp only [toRealCoeff]; exact_mod_cast hc3
    · simp only [toRealCoeff]; exact_mod_cast hc4
  have hf : ∀ t : ℝ, -1 ≤ t → t ≤ (cert.s : ℝ) → legendreEval cert.toRealCoeff t ≤ 0 := by
    intro t hlo hhi
    by_cases htm : t ≤ (cert.m : ℝ)
    · exact eval_nonpos_of_bernsteinNonpos cert hleft (by exact_mod_cast hlo) htm
    · exact eval_nonpos_of_bernsteinNonpos cert hright (le_of_not_ge htm) hhi
  have hbound := delsarte_bound hp hc0R hcR hf
  have heq : legendreEval cert.toRealCoeff 1 / cert.toRealCoeff 0 = (cert.bound : ℝ) := by
    rw [legendreEval_one, Fin.sum_univ_five]
    simp only [toRealCoeff, bound]
    push_cast
    ring
  rwa [heq] at hbound

/-! ## Verified certificates and rejection tests -/

/-- Valid certificate for `s = -1/2` reproducing `N ≤ 3`. -/
def cert3 : DelsarteCert := ⟨1 / 2, 1, 0, 0, 0, -1 / 2, -1 / 2⟩

theorem cert3_valid : cert3.isValid = true := by
  norm_num [isValid, bernsteinNonpos, bernsteinOn, powerCoeffs, cert3]
theorem cert3_bound : cert3.bound = 3 := by
  norm_num [bound, cert3]

/-- Valid certificate for `s = -1/3` reproducing `N ≤ 4`. -/
def cert4 : DelsarteCert := ⟨1 / 3, 1, 0, 0, 0, -1 / 3, -1 / 3⟩

theorem cert4_valid : cert4.isValid = true := by
  norm_num [isValid, bernsteinNonpos, bernsteinOn, powerCoeffs, cert4]
theorem cert4_bound : cert4.bound = 4 := by
  norm_num [bound, cert4]

/-- Valid certificate for `s = 0` reproducing `N ≤ 6`: `f(t) = t(t + 1)`. -/
def cert6 : DelsarteCert := ⟨1 / 3, 1, 2 / 3, 0, 0, 0, 0⟩

theorem cert6_valid : cert6.isValid = true := by
  norm_num [isValid, bernsteinNonpos, bernsteinOn, powerCoeffs, cert6]
theorem cert6_bound : cert6.bound = 6 := by
  norm_num [bound, cert6]

/-- Valid rational certificate for `s = 11/25 = 0.44` (`< 1/√5`), certifying
`N ≤ 11.79... < 12` (hence `N ≤ 11`) purely over `ℚ`, with subdivision at
the double root `m = -11/25`. -/
def cert11 : DelsarteCert :=
  ⟨1 / 5 + (11 / 25 - (11 / 25) ^ 2) / 3 - (11 / 25) ^ 3,
   3 * (1 + 11 / 25) / 5 - (1 + 11 / 25) * (11 / 25) ^ 2,
   4 / 7 + 2 * (11 / 25 - (11 / 25) ^ 2) / 3,
   2 * (1 + 11 / 25) / 5,
   8 / 35,
   11 / 25,
   -11 / 25⟩

theorem cert11_valid : cert11.isValid = true := by
  norm_num [isValid, bernsteinNonpos, bernsteinOn, powerCoeffs, cert11]
theorem cert11_bound_lt_12 : cert11.bound < 12 := by
  norm_num [bound, cert11]

/-- Negative test 1: certificate with `c₀ ≤ 0` is rejected. -/
def badCertZeroC0 : DelsarteCert := ⟨0, 1, 0, 0, 0, -1 / 2, -1 / 2⟩
theorem badCertZeroC0_rejected : badCertZeroC0.isValid = false := by
  norm_num [isValid, bernsteinNonpos, bernsteinOn, powerCoeffs, badCertZeroC0]

/-- Negative test 2: certificate with negative Legendre coefficient `c₂ < 0` is rejected. -/
def badCertNegCoeff : DelsarteCert := ⟨1, 0, -1, 0, 0, 0, 0⟩
theorem badCertNegCoeff_rejected : badCertNegCoeff.isValid = false := by
  norm_num [isValid, bernsteinNonpos, bernsteinOn, powerCoeffs, badCertNegCoeff]

/-- Negative test 3: certificate positive on `[-1, s]` (violating `f(t) ≤ 0`) is rejected. -/
def badCertPositive : DelsarteCert := ⟨1, 1, 0, 0, 0, 0, 0⟩
theorem badCertPositive_rejected : badCertPositive.isValid = false := by
  norm_num [isValid, bernsteinNonpos, bernsteinOn, powerCoeffs, badCertPositive]

end DelsarteCert

end Geodesy.Spherical
