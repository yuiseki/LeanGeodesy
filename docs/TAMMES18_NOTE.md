# A Machine-Checked Three-Point Semidefinite Upper Bound for Tammes `N = 18` on `S²`

> **Status:** Draft research note prepared for independent technical review.
> Not submitted externally.

## 1. Mathematical Claim

We establish the following unconditional upper bound on spherical codes and the
Tammes problem on the unit 2-sphere $S^2 \subset \mathbb{R}^3$:

**Theorem 1 (`sphericalCode_three_upper_313_500`).**
Every finite configuration $p_1, \dots, p_n \in S^2$ with pairwise inner products
$\langle p_i, p_j \rangle \le \frac{313}{500} = 0.626$ for all $i \ne j$ satisfies
$$n \le 17.$$
In standard spherical-code notation, $A(3, 313/500) \le 17$.

**Corollary 2 (`tammes_18_strict_upper`, `tammes_18_lt_51_25_deg`).**
For any $18$ points on $S^2$, their minimum geodesic separation $\theta$ satisfies
$$\theta < \arccos\!\left(\frac{313}{500}\right) \approx 51.24438^\circ < 51.25^\circ.$$

## 2. Comparison with Prior Bounds

Let $T(N)$ denote the maximum possible minimum geodesic angle among $N$ points on $S^2$.

| Source / Method | Bound on $T(18)$ | Cosine threshold $s$ | Proof status |
| --- | --- | --- | --- |
| Tarnai–Gáspár (1983) / Cohn (`spherical-codes.org`) | $\ge 49.55665^\circ$ (lower bound) | $0.648695832223$ | Explicit algebraic configuration (degree-11 minimal poly) |
| L. Fejes Tóth (1943) (`leapsinbounds.org/constants/tammes-18/`) | $\le 51.69012^\circ$ | $0.619914$ | Classical geometric area proof |
| Bachoc–Vallentin (2008), Table 5.3 via monotonicity $T(18) \le T(17)$ | $\le 51.69^\circ$ | $0.619916$ | 3-point SDP for $N = 17$ |
| Delsarte 2-point LP limit ($d_2 \to \infty$, numerical `LP(20)`–`LP(26)`) | $\approx 51.2827^\circ$ | $\approx 0.62548$ | At $s = 313/500$, `LP(20) ≈ 18.0269 > 18` (provably unreachable by 2-point LP) |
| **This work (`Tammes18.lean`)** | **$< \arccos(313/500) \approx 51.24438^\circ < 51.25^\circ$** | **$313 / 500 = 0.626$** | **Unconditional Lean 4 kernel proof (`decide`, no `native_decide`)** |

**Strict improvement:**
- Improves L. Fejes Tóth (1943) by $> 0.4457^\circ$,
- Improves monotonicity from Bachoc–Vallentin (2008) Table 5.3 by $> 0.4456^\circ$,
- Strictly crosses the infinite-degree Delsarte two-point linear programming barrier ($51.2827^\circ$), demonstrating genuine three-point SDP strength.

## 3. Mathematical Proof Structure

The proof combines:
1. **Three-point geometry on $S^2$** (`LeanGeodesy/Spherical/ThreePoint.lean`):
   positive semidefiniteness of the $3 \times 3$ Gram matrix, determinant identity
   $\Delta(u, v, t) = 1 + 2uvt - u^2 - v^2 - t^2 \ge 0$, $S_3$ symmetries, and
   decomposition of triple sums into diagonal, two-point, and distinct-triple terms.
2. **Arbitrary-degree Bachoc–Vallentin kernel** (`LeanGeodesy/Spherical/BachocVallentin.lean`):
   via an explicit tangent frame $\{e_1, e_2\} \subset x^\perp$ and complex projection
   $w_x(y) = \langle y, e_1 \rangle + i \langle y, e_2 \rangle$, the Chebyshev kernel
   satisfies $Q_k(\langle x,y\rangle, \langle x,z\rangle, \langle y,z\rangle) = \mathrm{Re}(w_x(y)^k \overline{w_x(z)}^k)$
   for all $k \in \mathbb{N}$, yielding positive semidefiniteness of weighted triple sums.
3. **Legendre PSD for $P_0 \dots P_{12}$** (`LeanGeodesy/Spherical/Legendre12.lean`):
   proved via the exact trivariate polynomial addition theorem
   $$P_k(t) = P_k(u) P_k(v) + \sum_{m=1}^{k} \frac{2(k-m)!}{(k+m)!} P_k^{(m)}(u) P_k^{(m)}(v) Q_m(u, v, t)$$
   applied at the north pole, combined with `bachocVallentin_bound_with_legendre`.
4. **Exact rational SDP certificate verifier** (`LeanGeodesy/Spherical/BachocVallentinCert6.lean`):
   for $d_3 = 6, d_2 = 12$, verifies in exact integer arithmetic:
   - symmetry and positive semidefiniteness of all 19 rational matrices
     ($F_0 \dots F_6$, $S_0, S_1$, and 10 $S_3$-reduced SOS matrices $M_0 \dots M_9$,
     max size $34 \times 34$) via Cholesky + diagonal dominance
     ($d_R^2 M - d_M R^\top R$ is symmetric diagonally dominant),
   - exact univariate degree-12 polynomial identity (scaled by $1024$ so all $P_1 \dots P_{12}$ are integer polynomials),
   - exact $S_3$-canonicalized trivariate degree-12 polynomial identity over the 102 canonical monomials.
5. **Certified angle comparison** (`Tammes18.lean`):
   proves $\cos x \le 1 - \frac{x^2}{2} + \frac{x^4}{24} - \frac{x^6}{720} + \frac{x^8}{40320}$ on $x \ge 0$
   by repeated monotonicity, yielding $\arccos(313/500) < 51.25^\circ$ from Mathlib's `Real.pi_gt_d6` / `Real.pi_lt_d6`.

## 4. Trust Boundary & Axiom Audit

No external solver (Clarabel, CVXPY, NumPy, SciPy) is part of the trusted computing base.
Every claim is independently checked in the Lean 4 kernel (`v4.34.0`, Mathlib `v4.34.0`) with
no `sorry`, no `admit`, no `native_decide`, and no custom axioms (`LeanGeodesy/Axioms.lean`):

- `Geodesy.Spherical.tammes18Cert_valid` → `[propext]`
- `Geodesy.Spherical.sphericalCode_three_upper_313_500` → `[propext, Classical.choice, Quot.sound]`
- `Geodesy.Spherical.tammes_18_strict_upper` → `[propext, Classical.choice, Quot.sound]`
- `Geodesy.Spherical.tammes_18_lt_51_25_deg` → `[propext, Classical.choice, Quot.sound]`

## 5. Reproduction & Compute Metrics

- **Unconstrained numerical `BV(6, 12)` optimum at $s = 313/500$:** `17.950311 < 18` (Clarabel, 12.8 s, 185.6 MB)
- **Interiority-maximized solve (`bound <= 17.99`):** `eps = 8.721e-7`, 7.9 s
- **Exact rational certificate:** `dK = 10^9`, `dR = 10^9`, `dS0 = 13440000000000000`, `dS` 147 digits, exact bound `17989990959 / 10^9 ≈ 17.989991 < 18`, zero polynomial residual, all 19 matrices strictly diagonally dominant after Cholesky subtraction
- **Lean 4 kernel verification:** `cd LeanGeodesy && LEAN_NUM_THREADS=4 lake build LeanGeodesy.Spherical.Tammes18 LeanGeodesy.Axioms` (~150 s on Apple Silicon)
- **Script reproduction (untrusted generator):**
  ```bash
  uv run --with cvxpy --with clarabel --with numpy --with scipy \
    python LeanGeodesy/scripts/bv_sdp/export_tammes18_lean.py
  ```

## 6. References

- L. Fejes Tóth, *Über die Abschätzung des kürzesten Abstandes zweier Punkte eines auf einer Kugelfläche liegenden Punktsystems*, Jber. Deutsch. Math.-Verein. 53 (1943), 66–68.
- P. Delsarte, J. M. Goethals, J. J. Seidel, *Spherical codes and designs*, Geom. Dedicata 6 (1977), 363–388.
- C. Bachoc, F. Vallentin, *New upper bounds for kissing numbers from semidefinite programming*, J. Amer. Math. Soc. 21 (2008), 909–924 (`arXiv:math/0608426`).
- M. Dostert, D. de Laat, P. Moustrou, *Exact semidefinite programming bounds for packing problems*, SIAM J. Optim. 31 (2021), 1433–1458.
- H. Cohn, D. de Laat, N. Leijenhorst, *Optimality of spherical codes via exact semidefinite programming bounds*, `arXiv:2403.16874` (2024).
- N. Leijenhorst, *On the computation of three and four-point bounds in discrete geometry and analytic number theory*, PhD Thesis, TU Delft (2025).
- H. Cohn, *Table of Spherical Codes*, `https://spherical-codes.org/`.
- *Leaps in Bounds*, `https://leapsinbounds.org/constants/tammes-18/`.
