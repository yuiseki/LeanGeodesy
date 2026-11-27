# Reproducibility: Certified Bachoc–Vallentin 3-Point SDP for `K(3) = 12`

This directory preserves the untrusted numerical exploration, rational rounding,
and Lean certificate generation scripts that produced
[`LeanGeodesy/Spherical/KissingNumber3.lean`](../../LeanGeodesy/Spherical/KissingNumber3.lean).

**Trust boundary:** None of the scripts in this directory are part of Lean's
trusted computing base (TCB). Every mathematical claim in `KissingNumber3.lean`
is independently checked by the Lean 4 kernel (`decide` + `BVCert5.sound`,
axioms `[propext, Classical.choice, Quot.sound]`, with `kissing3Cert_valid`
depending only on `[propext]`).

## Files

| Script | Role |
| --- | --- |
| `bv_k3.py` | Initial unreduced 3-point SDP exploration on $S^2$ at $s = 1/2$ |
| `bv_k3_s3.py` | $S_3$-symmetry-reduced 3-point SDP formulation (4 multipliers, 10 SOS blocks) |
| `round_k3_cert.py` | Interiority maximization (`bound <= 12.99`), rational rounding, exact $S_3$ polynomial residual elimination, and $M = R^\top R + E$ decomposition |
| `export_k3_lean.py` | Generates `LeanGeodesy/Spherical/KissingNumber3.lean` from the exact rational certificate |
| `export_tammes18_lean.py` | Generates `LeanGeodesy/Spherical/Tammes18.lean` (`BV(6, 12)` at $s = 313/500$) |
| `round_bv8_18.py` | Reduced 7-block Chebyshev-basis `BV(8, 16)` solve at $s = 317/500$, exact rational QR-pivot projection, and exact integer Cholesky + DD verification (`bv8_18_cert.json`) |
| `export_tammes18_bv8_lean.py` | Generates `LeanGeodesy/Spherical/Tammes18BV8.lean` from `bv8_18_cert.json` |

## Environment & Reproduction

Run with [`uv`](https://docs.astral.sh/uv/) (no system Python modification):

```bash
# 1. Explore S3-reduced degree-5 3-point SDP at s = 1/2
uv run --with cvxpy --with clarabel --with numpy --with scipy \
  python LeanGeodesy/scripts/bv_sdp/bv_k3_s3.py

# 2. Generate exact rational certificate & Lean source
uv run --with cvxpy --with clarabel --with numpy --with scipy \
  python LeanGeodesy/scripts/bv_sdp/export_k3_lean.py

# 3. Independently verify in the Lean 4 kernel
cd LeanGeodesy && LEAN_NUM_THREADS=4 lake build LeanGeodesy.Spherical.KissingNumber3 LeanGeodesy.Axioms
```

## Recorded Metrics (`K(3) = 12`, commit `1e26a34`)

- **Problem:** $S^2$ kissing number ($s = 1/2$, $\theta = 60^\circ$)
- **SDP degrees:** $d_2 = 0$ (pure 3-point, no $P_1 \dots P_{10}$ terms), $d_3 = 5$
- **Solver:** Clarabel via CVXPY (`eps` interiority maximization subject to `bound <= 12.99`)
- **Unconstrained numerical optimum ($d_3 = 5$):** `12.852629 < 13`
- **Interior-maximized numerical optimum:** `12.99` (min eigenvalue margin $\approx 3.59 \times 10^{-5}$)
- **Exact rational certificate:** 18 integer matrices (max size $22 \times 22$), denominators $d_K = 10^6$, $d_R = 10^6$, exact bound $< 12.99 < 13$, polynomial identity residual $= 0$
- **Lean 4 kernel verification time:** ~60 s (`LEAN_NUM_THREADS=4`, Lean `v4.34.0`)
- **Axioms:** `kissing3Cert_valid` → `[propext]`; `kissingNumber_three_upper` / `kissingNumber_three_exact` → `[propext, Classical.choice, Quot.sound]`
