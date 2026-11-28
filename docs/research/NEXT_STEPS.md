# Which problem next, and why

Written 2026-11-28 after the covering foundations (`docs/COVERING.md`) and the
two surveys in this folder. Status labels follow the surveys; nothing here is
a new mathematical claim.

## What each problem needs, against what exists

| Problem | State of the art (survey label) | What the libraries already give | First independently checkable piece | Cost |
| --- | --- | --- | --- | --- |
| Spherical covering, `N = 9, 11, 13` | `N ≤ 8`, `10`, `12` proved; `N = 9` type determined (Wimmer 2017, body not read); `11`, `13` numerical, flagged as possible local minima (Rathbun 2020) | `IsCovering`, `coveringRadius`, existence of minimizers, and now the inner-product, hull and Voronoi reformulations and an exact rational upper-bound checker | certified upper bounds for the best known configurations; a Delaunay-area lower bound lemma | small to medium |
| Coulomb / Riesz energy, `N = 4, 6, 12` first | proved (Yudin, Andreev; Cohn–Kumar for sharp configurations); `N = 5` computer-assisted (Schwartz), `N = 7`, `8` claimed in Lean in 2026, unreviewed | unit sphere, caps, Delsarte LP and three-point SDP exact certificates (the same technique the `N = 7`, `8` proofs use) | LP certificate for `N = 4, 6, 12` | small |
| Smale's 7th, Thomson in general | open | none beyond the above | none that is not conditional | not feasible now |
| Gromov filling area | open for genus ≥ 2; 2026 preprints improve lower bounds (Chen–Li–Zhong, Zust) and one has a Lean companion on Lean/Mathlib 4.29 | none (no Riemannian geometry beyond Mathlib's) | the arithmetic of the last step of Chen–Li–Zhong (Givens identities, bounds on `ζ(3)` and `π`, an interval check) | arithmetic: small; geometry: months |
| Boundary rigidity, Calabi–Croke | open | none | toy models only | not feasible now |

## Recommendation

1. Spherical covering, starting at `N = 9`, as the research target, because
   * it is the one problem here where the proved and the open parts meet at a
     small, finite object: the combinatorial type is determined, the radius
     within that type is an algebraic number, and `11` and `13` are the first
     cases with no proof at all;
   * the new checker turns the tables' numbers from NUMERICAL into proved upper
     bounds. That is useful immediately and settles disagreements that the
     literature leaves open: for `N = 18` and `N = 19` the three published tables
     give different radii (survey), so at least two are not optimal, and a
     certified upper bound says which configurations really achieve what is
     claimed;
   * it separates search from proof by construction: configurations and trees
     come from any program, Lean re-checks them, and nothing a solver says is
     trusted.
   First steps, each independent of the next: (a) certify upper bounds for the
   best known `N = 9, 11, 13` configurations (needs the configurations: they
   have to be recomputed or obtained, since Sloane's page returned an empty
   body); (b) read Wimmer 2017 to see whether the `N = 9` radius is already
   proved, which needs access to the paywalled text; (c) formalize the
   Delaunay-area lower bound (L. Fejes Tóth), which is tight exactly for
   `N = 4, 6, 12` and would give the first lower bounds valid for every
   configuration.
   Limits to keep in view: a certificate bounds one configuration from above,
   so it can never prove optimality; the `N = 13` optimum has a free cap, so a
   proof there is about a set of optima, not a point.
2. In parallel and independent, the Coulomb LP certificates for `N = 4, 6, 12`
   on top of the existing Delsarte machinery. It is the cheapest honest step
   toward Thomson and Smale, and it reproduces cases that are already proved,
   so it is a check on the method.
3. Gromov: only the arithmetic piece, and only if the external theorem is kept
   as an explicit hypothesis. Do not port the Lean companion; it is pinned to a
   different Mathlib.
4. Defer the rest until a Riemannian library exists.

Not recommended: stating any result of the 2026 preprints as established. Each
is a single preprint or blog post; the Gromov companion already shows drift
between its README, the paper and its ledger.
