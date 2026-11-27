# A Machine-Checked Three-Point Semidefinite Upper Bound for Tammes `N = 18` on `S²`

> **Status:** Unconditional Lean 4 kernel-verified degree-8 three-point SDP upper
> bound for Tammes `N = 18` (`Tammes18BV8.lean`), strictly improving R. M. Robinson's
> (1961, Theorem Ba, Section 9.1) classical bound $T(18) \le 50.68095^\circ$.

## 1. Main Mathematical Statements (`Tammes18BV8.lean`)

We formalize and verify unconditionally in the Lean 4 kernel the following upper
bound on spherical codes and the Tammes problem on the unit 2-sphere
$S^2 \subset \mathbb{R}^3$:

**Theorem 1 (`sphericalCode_three_upper_317_500`).**
Every finite configuration $p_1, \dots, p_n \in S^2$ with pairwise inner products
$\langle p_i, p_j \rangle \le \frac{317}{500} = 0.634$ for all $i \ne j$ satisfies
$$n \le 17.$$
In standard spherical-code notation, $A(3, 317/500) \le 17$.

**Corollary 2 (`tammes_18_strict_upper_317_500`, `tammes_18_lt_50_655_deg`).**
For any $18$ points on $S^2$, their minimum geodesic separation $\theta$ satisfies
$$\theta < \arccos\!\left(\frac{317}{500}\right) \approx 50.65414^\circ < 50.655^\circ.$$

**Theorem 3 (`robinson18_strict_improvement`).**
At $a = \arccos(317/500)$, R. M. Robinson's (1961, Theorem Ba, Section 9.1)
area inequality LHS $4 \cdot 18 \cdot \Delta(a) + (2 \cdot 18 - 12) \cdot \Delta^*(a)$
satisfies
$$\mathrm{robinson18LHS}\!\left(\arccos\!\left(\frac{317}{500}\right)\right) < 12\pi.$$
Because $\mathrm{robinson18LHS}(a)$ is strictly increasing in $a \in (0, \pi/2)$
and equals $12\pi$ at Robinson's bound $a_{\mathrm{Rob}} \approx 50.68094488^\circ$,
this formally certifies that $\arccos(317/500)$ strictly improves Robinson (1961).

## 2. Comparison with Known Literature Bounds

Let $T(N)$ denote the maximum possible minimum geodesic angle among $N$ points on $S^2$.

| Source / Method | Bound on $T(18)$ | Cosine threshold $s$ | Proof status |
| --- | --- | --- | --- |
| Tarnai–Gáspár (1983) / Cohn (`spherical-codes.org`) | $\ge 49.55665^\circ$ (lower bound) | $0.648695832223$ | Explicit algebraic configuration (degree-11 minimal poly) |
| **This work (`Tammes18BV8.lean`, `BV(8, 16)`)** | **$< \arccos(317/500) \approx 50.65414^\circ < 50.655^\circ$** | **$317 / 500 = 0.634$** | **Unconditional Lean 4 kernel proof (`decide`, no `native_decide`)** |
| R. M. Robinson (1961), Theorem Ba (Section 9.1) (`leapsinbounds.org/constants/tammes-18/`) | $\le 50.68095^\circ$ (previous best known upper bound) | $0.63363820$ | Classical geometric area inequality $4n\Delta + (2n-12)\Delta^* \le 12\pi$ ($n > 12$) |
| Earlier `BV(6, 12)` certificate (`Tammes18.lean`, retained) | $< \arccos(313/500) \approx 51.24438^\circ < 51.25^\circ$ | $313 / 500 = 0.626$ | Unconditional Lean 4 kernel proof (`BVCert6`) |
| L. Fejes Tóth (1943) (`leapsinbounds.org/constants/tammes-18/`) | $\le 51.69012^\circ$ | $0.619914$ | Classical geometric area proof |
| Bachoc–Vallentin (2008), Table 5.3 via monotonicity $T(18) \le T(17)$ | $\le 51.69^\circ$ | $0.619916$ | 3-point SDP for $N = 17$ |

## 3. Mathematical Proof Structure (`BV(8, 16)`)

1. **Three-point geometry and arbitrary-degree Bachoc–Vallentin kernel**
   (`LeanGeodesy/Spherical/ThreePoint.lean`, `LeanGeodesy/Spherical/BachocVallentin.lean`):
   positive semidefiniteness of the $3 \times 3$ Gram matrix, determinant identity
   $\Delta(u, v, t) = 1 + 2uvt - u^2 - v^2 - t^2 \ge 0$, $S_3$ symmetries, and the
   Chebyshev kernel $Q_k(u, v, t)$ via tangent-plane complex projection.
2. **Legendre PSD for $P_0 \dots P_{16}$ and Chebyshev-basis three-point bound**
   (`LeanGeodesy/Spherical/Legendre16.lean`):
   proves $\sum_{i,j} P_k(\langle p_i, p_j \rangle) \ge 0$ for $k = 0 \dots 16$ via
   the exact `bvQ` addition theorem at the north pole, and proves
   `bachocVallentin_cheb_bound_with_legendre16` using Chebyshev polynomials
   $T_i(u) T_j(v) Q_k(u, v, t)$ (improved numerical conditioning over monomials).
3. **Reduced-size exact rational certificate verifier**
   (`LeanGeodesy/Spherical/BachocVallentinCert8.lean`):
   for $d_3 = 8, d_2 = 16$, we mathematically eliminate the degree-4 multiplier
   $g_2(u, v) = (s - u)(s - v)$ and the odd parity block of $g_1(u) = (s - u)(u + 1)$,
   reducing the $S_3$-invariant SOS certificate from 10 blocks (`sum(m²) = 20,960`)
   to **7 blocks** (`[41, 54, 16, 23, 27, 7, 70]`, `sum(m²) = 11,060`) and reducing
   the trivariate polynomial denominator factor from $500^2$ to $500$.
   The kernel verifier `BVCert8.isValid` checks in exact integer arithmetic:
   - symmetry and PSD of all **18 matrices** ($F_0 \dots F_8$, $S_0, S_1$, and
     $M_0 \dots M_6$) via trimmed lower-triangular Cholesky + diagonal dominance
     (`isCholeskyDDLower`, $O(m^3/6)$ with structural recursion),
   - exact univariate degree-16 polynomial identity (scaled by $2^{15} = 32768$ so
     all $P_1 \dots P_{16}$ are integer polynomials),
   - exact $S_3$-canonicalized trivariate degree-16 polynomial identity over the
     204 canonical monomials.
   Because integer-multiplier blocks `M0..M5` already span full rank `204 / 204`,
   exact rational residual projection produces a common denominator `dS` of only
   **52 digits**, and the largest block `M6` ($70 \times 70$) keeps a local
   denominator of only **13 digits** (`10¹²`).
4. **Certified angle and Robinson (1961) comparison** (`Tammes18BV8.lean`):
   proves $\arccos(317/500) < 50.655^\circ$ and proves directly that
   `robinson18LHS (Real.arccos (317 / 500)) < 12 * Real.pi` via elementary Taylor
   bounds on $\cos$ and $\arctan$.

## 4. Trust Boundary & Axiom Audit

No external solver (Clarabel, CVXPY, NumPy, SciPy) is part of the trusted
computing base. Every claim is independently checked in the Lean 4 kernel
(`v4.34.0`, Mathlib `v4.34.0`) with zero unfinished proofs, no `native_decide`,
and no custom axioms (`LeanGeodesy/Axioms.lean`):

- `Geodesy.Spherical.tammes18BV8Cert_valid` → `[propext]`
- `Geodesy.Spherical.tammes18BV8BadCert_rejected` → `[propext]`
- `Geodesy.Spherical.sphericalCode_three_upper_317_500` → `[propext, Classical.choice, Quot.sound]`
- `Geodesy.Spherical.tammes_18_strict_upper_317_500` → `[propext, Classical.choice, Quot.sound]`
- `Geodesy.Spherical.arccos_317_500_lt_deg` → `[propext, Classical.choice, Quot.sound]`
- `Geodesy.Spherical.tammes_18_lt_50_655_deg` → `[propext, Classical.choice, Quot.sound]`
- `Geodesy.Spherical.robinson18_strict_improvement` → `[propext, Classical.choice, Quot.sound]`

## 5. Reproduction & Compute Metrics (`BV(8, 16)`)

- **Reduced 7-block numerical `BV(8, 16)` optimum at $s = 317/500$:** `17.87327 < 18` (Clarabel, Chebyshev basis)
- **Interiority-maximized solve (`bound <= 17.98`):** Clarabel ~61 s; post-projection SPD margin `min_eig = +1.296e-7` vs projection shift `‖ΔM‖₂ ≤ 2.36e-10` (~550× safety margin)
- **Exact rational certificate:** `dK = 10⁹`, `dR = 10¹⁰`, `dS0 = 33554432000000000000` (20 digits), `dS` 52 digits, `dM6 = 10¹²` (13 digits), exact bound `17979999983 / 10⁹ = 17.979999983 < 18`, zero polynomial residual, all 18 matrices strictly diagonally dominant after Cholesky subtraction
- **Lean 4 kernel verification:** `cd LeanGeodesy && LEAN_NUM_THREADS=4 lake build LeanGeodesy.Spherical.Tammes18BV8 LeanGeodesy.Axioms` (~19m 49s on Apple Silicon, `Tammes18BV8.lean` 554 lines / ~550 KB)
- **Script reproduction (untrusted generator):**
  ```bash
  uv run --with cvxpy --with clarabel --with numpy --with scipy \
    python LeanGeodesy/scripts/bv_sdp/round_bv8_18.py
  uv run --with cvxpy --with clarabel --with numpy --with scipy \
    python LeanGeodesy/scripts/bv_sdp/export_tammes18_bv8_lean.py
  ```

## 6. References

- L. Fejes Tóth, *Über die Abschätzung des kürzesten Abstandes zweier Punkte eines auf einer Kugelfläche liegenden Punktsystems*, Jber. Deutsch. Math.-Verein. 53 (1943), 66–68.
- R. M. Robinson, *Arrangement of 24 points on a sphere*, Mathematische Annalen 144 (1961), 17–48 (`https://doi.org/10.1007/BF01396539`).
- P. Delsarte, J. M. Goethals, J. J. Seidel, *Spherical codes and designs*, Geom. Dedicata 6 (1977), 363–388.
- C. Bachoc, F. Vallentin, *New upper bounds for kissing numbers from semidefinite programming*, J. Amer. Math. Soc. 21 (2008), 909–924 (`arXiv:math/0608426`).
- M. Dostert, D. de Laat, P. Moustrou, *Exact semidefinite programming bounds for packing problems*, SIAM J. Optim. 31 (2021), 1433–1458.
- H. Cohn, D. de Laat, N. Leijenhorst, *Optimality of spherical codes via exact semidefinite programming bounds*, `arXiv:2403.16874` (2024).
- N. Leijenhorst, *On the computation of three and four-point bounds in discrete geometry and analytic number theory*, PhD Thesis, TU Delft (2025).
- H. Cohn, *Table of Spherical Codes*, `https://spherical-codes.org/`.
- *Leaps in Bounds*, `https://leapsinbounds.org/constants/tammes-18/`.
