# ADR-001: Separate Research Proof Verification from Routine CI

- **Status:** Accepted
- **Date:** 2026-11-28
- **Target Repository:** `LeanGeodesy` (with 3-repository impact audit across `LeanGeospatial` and `LeanComputationalGeometry`)
- **Preserved Peer-Review Commit:** `b48321c` on `main` (untouched; no history rewrite)

## 1. Context & Dependency Analysis

### 1.1 Observed CI Bottleneck

Before `Tammes18BV8` was added, `LeanGeodesy` routine CI completed in ~4–6 minutes (and `LeanGeospatial` / `LeanComputationalGeometry` complete in 4–5.5 minutes). After adding the computer-assisted `BV(8, 16)` certificate (`Tammes18BV8*`, 11 modules) alongside `KissingNumber3` and `Tammes18`:

- **Commit `b48321c` (`Tammes18BV8` monolithic):** `Lean Action CI` (`build` + `joint`) and `Pages` all crashed with `exit code 143` (OOM on `ubuntu-latest`, 16 GB RAM).
- **Commit `5cb5b38` (11-module chunked + `Legendre16` optimized + `LEAN_NUM_THREADS=2`):** avoided OOM, but `build`, `joint`, and `Pages` each ran for **19+ minutes** because all three jobs re-verified the entire research certificate chain (`KissingNumber3`, `Tammes18`, `Tammes18BV8*`) from scratch or near-scratch.

### 1.2 Current Import & Build-Target Graph

`LeanGeodesy/lakefile.toml` currently specifies:

```toml
defaultTargets = ["LeanGeodesy"]

[[lean_lib]]
name = "LeanGeodesy"
globs = ["LeanGeodesy.*"]
```

Because `globs = ["LeanGeodesy.*"]` matches **every** `.lean` file under `LeanGeodesy/`, simply removing imports from `LeanGeodesy.lean` does **not** exclude heavy research certificates from `lake build`. Moreover:

```
Core Geodesy (Angle, Surface, WGS84, Geodesic, Projections, Tiles, CRS)
  └── Spherical Foundations & Reusable Verifiers:
        Packing → Topology
        Packing → Delsarte (incl. analytic Tammes N=12) → DelsarteCert
        Packing → ThreePoint → BachocVallentin → BachocVallentinCert (BVCert5)
                                               → Legendre12 → BachocVallentinCert6 (BVCert6)
                                                            → Legendre16 → BachocVallentinCert8 (BVCert8)
  └── Heavy Concrete Research Certificates (leaf modules, imported by nothing else):
        ├── KissingNumber3          (depends on BachocVallentinCert, Delsarte)       [~60s]
        ├── Tammes18                (depends on BachocVallentinCert6)                [~150s]
        └── Tammes18BV8Data → Check → Q6a → Q6b → Q1a → Q1b → Q1c → Q0a → Q0b → Q34 → Tammes18BV8
                                    (depends on BachocVallentinCert8)                [~650s+]
```

Key finding: `manual/`, `blueprint/`, `blueprint-yaruo/`, `LeanGeospatial`, and `LeanComputationalGeometry` do **not** import any of the three concrete heavy research certificates (`KissingNumber3`, `Tammes18`, `Tammes18BV8*`).

### 1.3 Three-Repository Audit

| Repository | Routine CI Time | Heavy Research Proofs? | Impact of `LeanGeodesy` Separation | Concurrency / Joint Cache Status |
| --- | --- | --- | --- | --- |
| `LeanGeodesy` | 19+ min (was ~4–6 min) | Yes (`KissingNumber3`, `Tammes18`, `Tammes18BV8*`) | Primary target of this ADR | Adding `concurrency`, `joint` cache, `Pages` restore-keys |
| `LeanGeospatial` | 4m–5m 23s | None | Its `joint` job clones `LeanGeodesy` `main`; automatically drops heavy cert rebuilds once `LeanGeodesy` separates targets | No `concurrency` or `joint` cache yet (noted for follow-up parity PR) |
| `LeanComputationalGeometry` | 4m 38s–5m 23s | None | Same: its `joint` job clones `LeanGeodesy` `main` | No `concurrency` or `joint` cache yet (noted for follow-up parity PR) |

## 2. Decision

### 2.1 Separate `LeanGeodesy` (Core + Reusable Verifiers) from `LeanGeodesyResearch` (Concrete Heavy Certificates)

1. **`lakefile.toml`:**
   - Keep `defaultTargets = ["LeanGeodesy"]`.
   - Restrict `[[lean_lib]] name = "LeanGeodesy"` to `globs = ["LeanGeodesy", "LeanGeodesy.Axioms"]` so `lake build` builds `LeanGeodesy.lean` (all core geodesy, spherical foundations, and reusable certificate verifiers `DelsarteCert`, `BachocVallentinCert`, `Legendre12`, `BachocVallentinCert6`, `Legendre16`, `BachocVallentinCert8`) plus the core axiom audit `LeanGeodesy.Axioms`.
   - Add an independent library target:
     ```toml
     [[lean_lib]]
     name = "LeanGeodesyResearch"
     globs = ["LeanGeodesyResearch", "LeanGeodesyResearch.Axioms"]
     ```
2. **Root Modules & Axiom Audits:**
   - `LeanGeodesy.lean`: removes only the 3 leaf research certificate imports (`KissingNumber3`, `Tammes18`, `Tammes18BV8`). All reusable definitions, general theorems, and verifiers remain in `LeanGeodesy`.
   - `LeanGeodesy/Axioms.lean`: audits all core + reusable verifier theorems (including `DelsarteCert.sound`, `BVCert5.sound`, `sum_legendreP12_nonneg`, `BVCert6.sound`, `sum_legendreP16_nonneg`, `BVCert8.sound`).
   - `LeanGeodesyResearch.lean`: imports `LeanGeodesy`, `LeanGeodesy.Spherical.KissingNumber3`, `LeanGeodesy.Spherical.Tammes18`, and `LeanGeodesy.Spherical.Tammes18BV8`.
   - `LeanGeodesyResearch/Axioms.lean`: audits all concrete research certificate theorems (`kissing3Cert_valid`, `kissingNumber_three_exact`, `tammes18Cert_valid`, `sphericalCode_three_upper_313_500`, `tammes18BV8Cert_valid`, `sphericalCode_three_upper_317_500`, `tammes_18_strict_upper_317_500`, `tammes_18_lt_50_655_deg`, `robinson18_strict_improvement`, `tammes18BV8BadCert_rejected`).
3. **Backward Compatibility Strategy:**
   - All existing module paths (`LeanGeodesy.Spherical.KissingNumber3`, `LeanGeodesy.Spherical.Tammes18`, `LeanGeodesy.Spherical.Tammes18BV8`) and namespaces (`Geodesy.Spherical`) are preserved unchanged.
   - Downstream callers that previously relied on `import LeanGeodesy` transitively importing concrete research certificates should switch to `import LeanGeodesyResearch` (or import the specific certificate module directly).
   - `lake build LeanGeodesyResearch` unconditionally builds and kernel-verifies all research certificates and their axiom audits.

### 2.2 Dedicated `Research Proofs CI` with Exact Transitive Dependency Detection

Create `.github/workflows/research_proofs.yml` and `scripts/check_research_deps.py`:

- **No fragile path filters:** `scripts/check_research_deps.py` parses `import` statements recursively starting from `LeanGeodesyResearch.lean` and `LeanGeodesyResearch/Axioms.lean` to compute the **exact transitive closure** of local `.lean` files, plus toolchain/build files (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `.github/workflows/research_proofs.yml`, `scripts/check_research_deps.py`).
- **Trigger policy:**
  - On `push` / `pull_request`: runs `lake build LeanGeodesyResearch` whenever **any** file in the exact transitive closure changed (including upstream foundations like `Geodesic.lean`, `Packing.lean`, `BachocVallentin.lean`, `Legendre16.lean`, `BachocVallentinCert8.lean`). Skips cleanly when only unrelated modules (e.g., projections, tiles, CRS, docs) changed.
  - On `schedule` (weekly cron), `push` of release tags (`v*`), or `workflow_dispatch`: **always runs unconditionally**, with a `no_cache` boolean input (default `true` on `schedule` and release tags) to force a zero-cache kernel verification from scratch.
- **Checks included:** `lake build LeanGeodesyResearch`, `No sorry or admit` across both `LeanGeodesy` and `LeanGeodesyResearch`, and `EPSG` independence.

### 2.3 Routine CI, Joint Check, Pages Caching & Concurrency

- **Concurrency:** Add `concurrency: { group: "${{ github.workflow }}-${{ github.ref }}", cancel-in-progress: "${{ github.ref != 'refs/heads/main' }}" }` to both `lean_action_ci.yml` and `research_proofs.yml` so stale PR/branch runs are cancelled automatically while `main` runs always complete.
- **`Lean Action CI` (`build` + `joint`):**
  - `build` runs `lake build` (default target `LeanGeodesy` + `LeanGeodesy.Axioms`) via `leanprover/lean-action@v1` with `LEAN_NUM_THREADS: 2`.
  - `joint` caches `joint/.lake`, `joint/lake-manifest.json`, `LeanGeodesy/.lake`, `LeanGeospatial/.lake`, and `LeanComputationalGeometry/.lake` keyed on toolchain + manifest + `${{ github.sha }}` with `restore-keys` on toolchain + manifest, so unchanged `.olean`s are reused across runs while fresh builds stay updated.
- **`Pages` (`pages.yml`):**
  - Uses `actions/cache@v5` keyed on toolchain + manifests + `${{ github.sha }}` with `restore-keys` on toolchain + manifests, so `.lake` cache updates on every `main` push instead of going stale.
  - Only builds `LeanGeodesy` (default target), `manual`, `blueprint`, and `blueprint-yaruo`.

## 3. Trust & Reproducibility Guarantees

- No mathematical definition, theorem, or certificate is weakened or removed.
- No `native_decide` or custom axioms are introduced.
- Axiom audits remain enforced for both core (`LeanGeodesy/Axioms.lean`) and research (`LeanGeodesyResearch/Axioms.lean`).
- Commit `b48321c` on `main` is never modified.
- All reproduction commands (`round_bv8_18.py`, `export_tammes18_bv8_lean.py`, `lake build LeanGeodesyResearch`) remain intact and documented.
