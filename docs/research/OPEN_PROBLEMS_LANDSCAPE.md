<!-- Literature survey compiled 2026-11-28 by delegated research agents. Sources were read through web tools, several only as abstracts or via a summarising fetcher; claims marked UNVERIFIED were not confirmed against a primary source, and nothing here has been re-derived. Do not cite a number from this file without opening the source. -->

# Open problems landscape for a Lean 4 / Mathlib v4.34.0 project (as of 2026-11-28)

Labels: THEOREM, CONDITIONAL, NUMERICAL, FORMAL (system, repo), UNVERIFIED (reason).
Method: pages were read through a summarising fetch tool, not verbatim, except the two arXiv PDFs
(2609.08251, 2611.15783), which I converted to text and read directly ("read in source"). Lean files of the
Gromov repo were read only through the summariser. No clone, build or run was done.

## 0. Corrections to the task's premises

1. The 24-cell is NOT universally optimal: Cohn-Conway-Elkies-Kumar (Experiment. Math. 16 (2007), arXiv
   math/0607447) give a numerical competitor and conjecture no universally optimal 24-point code in S^3.
   UNVERIFIED (search snippet only). Proved: 600-cell, all sharp configurations, E8, Leech (B.3).
2. Thomson N=7 and N=8 are claimed solved in Lean (Sept 2026), see B.2. Wikipedia lists them; I opened primaries.
3. Hexagon 2611.00218v2 has no Lean artefact and its statement is login-gated (A.3).
4. The Gromov Lean repo is on Lean/Mathlib 4.29.0, not 4.34.0 (A.2).
5. Kabra et al. (2611.15783) is not a solution of Smale's 7th problem: its guarantee is conditional twice (B.1).

---------------------------------------------------------------------------------------------------
## PART A. Gromov filling area conjecture

### A.1 arXiv 2609.08251, Chen-Li-Zhong, "A Fourier approach to Gromov's filling area conjecture"
Submitted 8 Sep 2026, math.DG, 20 pp, v1, no journal ref, no peer review shown. https://arxiv.org/abs/2609.08251
Claims (read in source). Label for all three: THEOREM (claimed analytic proof; one preprint; Lean artefact in A.2).
- Thm 1.1: every compact connected Riemannian isometric filling of a circle of length 2 pi, orientable or not,
  of any topology, has Area >= 14 zeta(3)/pi ~ 5.35677.
- Thm 1.2: orientable fillings have Area > 5.40154. Final step is "a direct interval computation":
  5.401544 < B(1/25)/C(1/25) < 5.401545, constants (4.1) built from pi, zeta(3), sqrt 2 and nested radicals.
- Thm 4.1: Area >= (C0 + b l + d l^2) / (denominator with C*, D*, Q*), 0 <= l < pi^2/32. The text extraction of
  the denominator is garbled; read it in the PDF before formalising.
Authors' caveats: Remark 4.8 says the bound is "not expected to be sharp" and that closing to 2 pi is open; they leave
open other nonlinear couplings and use of topology. AI disclosure: OpenAI models used while developing and checking.
It is not a proof of the conjecture (5.40 < 2 pi ~ 6.283).
Proof skeleton (read in source):
1. u_theta(x) = d_M(x, gamma(theta)), a_theta = (u_theta - u_{theta+pi})/2; eikonal |grad u| = 1 a.e. (Rademacher).
2. A_n, B_n = odd Fourier coefficients of a_theta, F_n = (A_n, B_n): M -> R^2; boundary trace
   z_n(gamma(s)) = -rho_n e^{ins}, rho_n = 4/(pi n^2) for odd n (one integral).
3. Prop 2.4: for distinct odd m_k and U in O(N), sum_j J_2 G_j <= 1 a.e., G = U F.
4. Sec 3: Givens product U_N = R_2...R_N, c_k = 1/sqrt(1 + 4/m_k^2), m_k = 2k-1. Lemma 3.2
   (|u_j1| > sum_{k>=2} |u_jk|/m_k) makes each boundary trace a Jordan curve; enclosed area = pi sum m_k |a_k|^2.
5. Lemma 3.4: a Lipschitz G: M -> R^2 embedding the single boundary circle covers the bounded component Omega
   (Z_2 relative fundamental class, so no orientability), then the area formula gives int J_2 G >= |Omega|.
6. Prop 3.5: Area >= (16/pi) sum_{k<=N} (2k-1)^-3; N -> inf and sum_odd m^-3 = (7/8) zeta(3).
7. Sec 4 (orientable): cubic resonant perturbation of Phi = (z_n) in l^2, symplectic form, Stokes, comass 1 + O(l^2).
Prior results as cited there (not opened by me unless noted):
- Gromov, J. Differential Geom. 18 (1983) 1-147: disk case via Pu 1952 (Pacific J. Math. 2). THEOREM.
- Bangert-Croke-Ivanov-Katz, Geom. Funct. Anal. 15 (2005) 577-597: orientable genus one. THEOREM. (Wikipedia
  describes the hyperelliptic mechanism; I did not verify a separate Gromov hyperelliptic statement.)
- Ivanov, Proc. Steklov Inst. 273 (2011): Finsler disks, Holmes-Thompson area. Burago-Ivanov (Annals 2010): almost
  flat metrics (C.1). Cossarini arXiv:2009.02415. Chambers, J. Topol. Anal. (2026). Zust, Calc. Var. 64(9) (2025) 297:
  Area >= pi^2/2 ~ 4.935, orientable. Ambi arXiv:2301.08503. All UNVERIFIED (citations only).
- Briggs-Wells arXiv:2602.17859 (Feb 2026), all fillings incl. nonorientable: Area >= (3 sqrt 2/4) pi ~ 4.274
  (abstract summary says 1.36 pi). THEOREM per abstract; discrete route, UNVERIFIED beyond abstract.
- Sabourau: I found no Sabourau paper on this conjecture; his related work is C.2.
- Mueller arXiv:2009.03172 (local systolic inequality) was WITHDRAWN for a computational error: do not cite.
- Zust arXiv:2610.29593 (21 Oct 2026), n=4 polyhedral calibration in l_inf: lower bound 11 pi^2/20 ~ 5.42828,
  ABOVE both CLZ constants. Orientability scope not stated in the abstract. UNVERIFIED (abstract only).
- He arXiv:2605.08909: discrete filling constant <= 1/6 < 1/(pi sqrt 3), so the discrete relaxation cannot settle
  Gromov's conjecture. THEOREM per abstract.
Conjecture status: OPEN for orientable Riemannian fillings of genus >= 2. Proved: disk, genus one, Finsler disks
(Holmes-Thompson), almost flat. Variant with rational 2-chains is false (Finsler counterexample, Wikipedia, secondary).
Lower bounds now: 5.35677 (all fillings) and 5.40154 (orientable) claimed by CLZ, 5.42828 claimed by Zust. Target 2 pi.

### A.2 GitHub lowrank/gromov-filling-lower-bound (Lean formalization of A.1)
Label: FORMAL (Lean 4 + Mathlib; the preprint's own companion; no independent review seen). MIT, 761 commits, 0 stars.
- Toolchain (raw lean-toolchain): leanprover/lean4:v4.29.0. Mathlib v4.29.0, commit 8a178386ffc0f5fef0b77738bb5449d50efeea95.
  Also EPFL LARA JordanCurveTheorem (e442525a...), and vendored ClassificationOfSurfaces (132 modules), Wikipedia/,
  SchoenfliesCompat/. It does NOT target v4.34.0; a 4.29 -> 4.34 rebuild on the manifold/Riemannian API
  (IsRiemannianManifold, mfderiv, RiemannianBundle) is UNVERIFIED and probably needs porting.
- Main declarations (README): riemannian_universal_fourier_bound (Thm 1.1);
  riemannianSurfaceArea_gt_one_div_twenty_five_of_conventionally_oriented_isometric_filling (Thm 1.2, l = 1/25);
  riemannianSharpenedNonlinearCertificate_le_surfaceArea_of_conventionally_oriented_isometric_filling (revised 4.1).
- Do the statements say what the title says? For Thm 1.1 I read Audit/UniversalFourierBound (Challenge, Defs,
  Solution) via summary. Hypotheses: S pseudometric, T2, Borel, connected, compact, charted over the Euclidean
  half-plane (dim 2), C^1 manifold, continuous Riemannian bundle, IsRiemannianManifold; boundary : UnitAddCircle -> S with
  dist (b s) (b t) = 2 pi dist s t and range b = manifold boundary. Conclusion: a controlled interior atlas exists and
  every such atlas gives area >= ENNReal.ofReal (14 * zetaThree / pi), with zetaThree = tsum 1/n^3 (n=0 term is 0).
  So yes, with two definitional choices: area is a Jacobian-weighted push-forward over a finite controlled atlas (Mathlib
  has no Riemannian volume), and the metric is only continuous on a C^1 manifold (more general than smooth).
  Thm 1.2 and 4.1 use the project's own RiemannianSurfaceOrientation (no proved equivalence to any Mathlib API).
- sorry/axiom/native_decide/opaque: Challenge.lean states the theorem as `by sorry` BY DESIGN (fixed challenge);
  Solution.lean (~100 lines) proves it through GromovFilling.riemannian_universal_fourier_bound and has none.
  Defs.lean and RiemannianUniversalFourierBound.lean show none (summary). I could not grep the whole repo, so
  repo-wide absence is UNVERIFIED by me. README claim: live axiom audit over 6,762 declarations, only propext,
  Classical.choice, Quot.sound; proof-escape scan with injected-sorry control; CI run 34177156896.
- External hypotheses: none custom. Stated gaps: raw-distance eikonal and a global Stokes/comass API are "independently
  partial" and not dependencies of the three theorems. Mathlib lacks orientation of manifolds with boundary, surface
  classification, relative Jordan-Schoenflies and manifold Stokes; the repo supplies its own.
- Version drift (FORMALIZATION.md via summary): 6,762 vs 6,677 declarations; a historical ledger says Thm 1.2 > 5.38982446
  (l = 0.03 draft) while README and paper say 5.40154 (l = 1/25). Treat the repo as moving.
- Compiles against v4.34.0? UNVERIFIED (not tried); pinned to 4.29.0.

### A.3 hexagonmath.org/2611.00218v2, "A Lower Bound for the Filling Area of the Circle"
Resolves to a Hexagon preprint page (v2, 10 Nov 2026, 15 pp, CC BY 4.0, math.DG/math.MG, MSC 53C23/53C20/49Q20, contributor
Qiyue Tang). Abstract: universal lower bound for ORIENTABLE Riemannian fillings; the constant is not visible. The PDF needs
ORCID sign-in, so I read no theorem or proof. Self-description: "primarily AI-generated text", GPT-6-Pro (runs of ~2 h and
~5.5 h), contributor disclaims ownership, asks for independent review, an audit by "Rethlas-OSV" promised but not posted,
v1 superseded, no Lean or formalization. Label: UNVERIFIED (gated; self-declared unreviewed AI text). Do not build on it.

### A.4 Decomposition into independently checkable finite facts
Pure arithmetic of CLZ, separable from geometry:
(a) For every N, U_N in O(N) (Givens, c_k^2 + s_k^2 = 1) and sum_{j,k} m_k u_jk^2 rho_k^2 = sum_k m_k rho_k^2.
(b) Row dominance (Lemma 3.2) for 1 <= j <= N: entries in the algebraic numbers sqrt(1 + 4/m_k^2); exact per N by
    squaring, or for all N by the paper's telescoping argument.
(c) pi sum m_k rho_k^2 = (16/pi) sum m_k^-3, limit 14 zeta(3)/pi via sum_odd m^-3 = (7/8) zeta(3).
(d) 14 zeta(3)/pi > 5.35677 needs only rigorous rational bounds on zeta(3) and pi.
(e) B(1/25)/C(1/25) in (5.401544, 5.401545) from the closed forms (4.1); exact rational bounds on pi, zeta(3), radicals.
Smallest independent piece: (e) with (a)-(d), a finite real-arithmetic check of a few hundred Lean lines, no geometry. It
certifies the arithmetic of the last step only, not that B and C are the right quantities.
Unavoidable Riemannian content: definition of an isometric filling (intrinsic distance on a surface with boundary), Riemannian
area and 2-Jacobian; Rademacher/eikonal and a.e. differentiability of the Fourier coefficients (Lemma 2.3, Prop 2.4); the area
formula for Lipschitz maps from a surface; Z_2 relative fundamental class; Jordan curve/Schoenflies; for Thm 1.2/4.1
orientation, Stokes for Lipschitz forms and Hilbert-valued comass estimates. The Lean repo supplies vendored versions of these.
Dependencies on existing libraries: LeanGeodesy can host the hemisphere (area 2 pi) as the extremal witness only;
LeanComputationalGeometry could give a discrete winding check for (b) but not the continuous Jordan theorem.
Feasibility: first piece (a)-(e) HIGH (days, exact arithmetic) but low value alone; re-proving Thm 1.1 LOW (months, needs
manifold-with-boundary distance, area formula, Z_2 homology). Practical path: use the repo at its own 4.29 pin as an external
check instead of porting.

---------------------------------------------------------------------------------------------------
## PART B. Energy minimisation on spheres (Thomson, Smale 7)

### B.1 arXiv 2611.15783, Kabra-Dehaen-Karlova-Hamilton-Carreira-Ovsjanikov-Barron
"A Linear-Time Construction on S^2 Achieving a Sublinear Energy Gap on Smale's Seventh Problem", 11 Nov 2026, cs.CG (+math.MG),
v1, not peer reviewed. Read in source. Three separate things:
1. Locality assumption (A), Sec 4.3: for the Stage-1 populations m, heights z_zonal and phases (10),
   E(X_N) - E_BHS(N) = sum_k psi_stretch(m_k, y_k) + c_seam * sum_{k: m_k != m_{k-1}} (y_{k-1} + y_k)/2 + o(N^{2/3}),
   i.e. the excess equals the cost the 1-D dynamic program minimises, with c_seam ~ 0.0042867 (not c_step ~ 0.0043241).
   Authors: "We do not prove this locality; we assume it." Evidence: residual falls from 17.5% (N=1e3) to 1.0% (N=1e8).
   Label: UNVERIFIED assumption, NUMERICAL support.
2. Conjectured coefficient: Brauchart-Hardin-Saff (2012) conjecture C_log = C_BHS/2 (single-counted energy),
   C_BHS = 2 log 2 + (1/2) log(2/3) + 3 log(sqrt(pi)/Gamma(1/3)) ~ -0.05560530494339252 (eq. 18);
   E_BHS(N) = (1/2)(1/2 - log 2) N^2 - (1/4) N log N + (1/2) C_BHS N. Label: CONDITIONAL (open conjecture; Betermin-Sandier
   showed C_BHS/2 is an upper bound and that the conjecture is equivalent to triangular-lattice optimality of the renormalised energy).
3. Proven error guarantee, CONDITIONAL on (A): Thm 4.3: E(X_N) - E_BHS(N) = C_1 N^{2/3} + o(N^{2/3}), C_1 ~ 0.026225, for
   TerracedZonal0 (before relaxation). Cor 4.4: E(X_N) - E_min(N) <= 6.24e-4 N + C_1 N^{2/3} + o(N^{2/3}), using the unconditional
   lower bound C_log >= (log 2 - 3/4)/2 (Lauritsen; Beltran-Lizarte). The linear slack cannot be removed without settling BHS: the
   distance to the true minimum is o(N) iff BHS holds, and C_1 N^{2/3} only if also E_min = E_BHS + O(log N) (also conjectured).
   So Smale's O(log N) is not reached. Exact evaluation to N = 1e9 (coaxial-ring formula, Lemma 4.1) is NUMERICAL; the
   integration-rule rate N^-4 is empirical.
My hand check: C_BHS = -0.0556053 and log 2 - 3/4 = -0.0568528; half the gap is 6.24e-4, as claimed. Marzo (arXiv:2506.01660,
June 2025) raises the lower bound by ~7e-6 (to -0.0568456, double-counted): THEOREM per abstract page and HTML.

### B.2 Thomson problem (Coulomb, s = 1 on S^2), status by N (Wikipedia plus primaries where noted)
- N=2 antipodal, N=3 equilateral triangle (Foeppl 1912 per Wikipedia): elementary; venues UNVERIFIED.
- N=4 tetrahedron, N=6 octahedron (Yudin 1992/93, Discrete Math. Appl.), N=12 icosahedron (Andreev 1996, East J. Approx. 2):
  THEOREM. All three are sharp configurations, hence also covered by Cohn-Kumar 2007 (inference from its abstract).
- N=5 triangular bipyramid: Schwartz, Experiment. Math. 22(2) (2013) 157-186, arXiv:1001.3702. THEOREM, computer-assisted
  (interval arithmetic), not formal; journal pages from a search snippet (UNVERIFIED), arXiv version opened via search. Also
  arXiv:1512.04628 (power laws) and arXiv:2301.05090 (distributed redo). Needs care: the bipyramid is not sharp, not
  universally optimal and not an LP-bound case; for other s the minimiser changes.
- N=7 pentagonal bipyramid: Hung Tran / Vals AI, blog 2026-09-28, repo github.com/huwngtran/thomson-n7-lean (README 2026-09-27),
  ten Claude Sonnet 5.5 agents, ~15 h. Label: FORMAL (Lean 4 v4.34.1, Mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612,
  only dependency). Theorems ThomsonN7.thomson_seven (E(pentBipyramid) <= E(x) for all x in SphereConfig 7) and
  thomson_seven_unique (equality iff x = g(P(sigma i)) with g a linear isometry, sigma a permutation). SphereConfig = injective maps
  Fin n -> unit sphere of R^3; energy = sum_{i<j} 1/|x_i - x_j|. One file Solution.lean, 17,895 lines, imports only Mathlib. Axioms
  propext, Classical.choice, Quot.sound. native_decide: not stated, not checked by me (UNVERIFIED). Comparator accepted it against the
  fixed challenge file (statement `sorry` by design); nanoda re-checked 47,854 declarations. Method: split by smallest pairwise inner
  product, three-point SDP bounds with numerically found, exactly rounded certificates checked in-kernel, interval arithmetic for a
  rigidity step, exact second-order test for uniqueness. Margins: cap bound ~2.3e-16 below E(P), slabs ~2.6e-6. README: "Statement not
  human-certified. Not peer reviewed." Lean 4.34.1 is one patch from the project's v4.34.0.
  Independent claim: Li Shen arXiv:2611.09925 (23 Sep 2026), exact PBP uniqueness for N=7 Thomson and Lennard-Jones;
  computer assistance not stated. UNVERIFIED.
- N=8 square antiprism: Kryvonos-Liehr-Taylor arXiv:2609.22077 (18 Sep 2026): log and Coulomb, computer-assisted and "fully verified
  in Lean" (abstract); Riesz: large s without computer assistance, all s >= 0 with; completely monotonic potentials for which the
  antiprism is not optimal (negative answer to a Cohn-Woo question). No repo or Mathlib version on the arXiv page. Label: FORMAL
  (Lean 4 + Mathlib; repo not located, axioms UNVERIFIED).
- N = 9, 10, 11 and N >= 13: open; numerical best-known energies to N = 480 (NUMERICAL).

### B.3 Universal optimality
- Cohn-Kumar, J. Amer. Math. Soc. 20 (2007) 99-148, doi 10.1090/S0894-0347-06-00546-7, arXiv:math/0607446 (abstract read). THEOREM:
  every sharp configuration (m distances, (2m-1)-design) minimises energy for all completely monotonic potentials of squared distance
  (E8 and Leech minimal vectors included), and the 600-cell too (not sharp); uniqueness for strictly CM potentials in most cases.
- Cohn-Kumar-Miller-Radchenko-Viazovska, arXiv:1902.05438 (v3 Jun 2022): THEOREM, E8 and Leech lattices universally optimal in
  R^8 and R^24 (Euclidean, not the sphere). Journal ref not on the arXiv page (Annals 2022 from memory: UNVERIFIED).
- 24-cell: not universally optimal (section 0). No formalization of any of these found.

### B.4 Smale's 7th problem
Smale, Math. Intelligencer 20(2) (1998); wording not opened: UNVERIFIED. Status OPEN (MathWorld; proofatlas.ai page checked
2026-08-30, next review 2026-11-30).
- Armentano-Beltran-Shub, Trans. AMS 363 (2011): random polynomial roots as starting configurations. UNVERIFIED (memory plus
  search summary). CLT for that energy: arXiv:2304.02898 (search only).
- Beltran 2013 (bounded-bit rational points, exponential time), Beltran-Etayo-Lopez-Gomez 2023 (explicit low-energy family),
  Beltran-Lizarte 2023 (arXiv:2205.02755, Constr. Approx. doi 10.1007/s00365-023-09642-4): citations from proofatlas.ai and a
  search snippet, UNVERIFIED.
- Betermin-Sandier, Constr. Approx. 47 (2018), arXiv:1404.4485: C_log exists and C_log <= C_BHS/2. THEOREM per 2611.15783 App. A.1
  and search; paper not opened (UNVERIFIED primary).
- Lauritsen 2021 and Beltran-Lizarte: C_log >= (log 2 - 3/4)/2. THEOREM (secondary). Rakhmanov-Saff-Zhou 1994/95: leading terms
  (1/2)(1/2 - log 2) N^2 - (1/4) N log N + O(N). THEOREM (as quoted in 2611.15783).
- Bilyk et al.: no specific paper on Smale 7 found; I make no claim.
- Kabra et al.: CONDITIONAL as in B.1. Nothing reaches O(log N), even conditionally.
Formal status: none (proofatlas.ai reports no Lean or other formal proof; its bounded search is not evidence of absence).

### B.5 Riesz energy definitions, existence, expansions
- E_s = sum_{i<j} |x_i - x_j|^-s (s > 0), E_log = sum_{i<j} log(1/|x_i - x_j|) (s = 0), Coulomb = s = 1 on S^2. Single vs double counting
  differs by 2 (trap flagged in 2611.15783 App. A.1).
- Existence of minimisers for fixed N: elementary compactness plus blow-up at collisions; THEOREM, no reference opened (UNVERIFIED).
- Kuijlaars-Saff, Trans. AMS 350 (1998) 523-538: separation bounds for s >= d >= 2 and the log-energy upper bound (venue and gist from a
  search snippet): THEOREM (secondary). Brauchart-Hardin-Saff, Contemp. Math. 578 (2012) 31-61, arXiv:1202.4037: survey with conjectures
  on the next-order term: CONDITIONAL. Exact next-order coefficients for s = 1 on S^2: not read, UNVERIFIED.
- No formalised asymptotics found; formal energy results exist only for fixed N (N = 7, 8).

### B.6 What Lean needs to start (my assessment)
1. Configurations Fin N -> unit sphere of EuclideanSpace R 3, collision-free (injective) for log and Riesz energies.
2. Riesz and log energies as finite pair sums, fixed single-counting convention, lemma for the double-counted form.
3. Existence of minimisers: lower semicontinuity with value +inf at collisions, compactness of the sphere power.
4. A verified exact-arithmetic bound: Delsarte/Yudin LP certificate (polynomial of degree <= 2m-1 with nonnegative Gegenbauer
   coefficients lying below the potential), giving E >= N^2 * constant exactly in rationals. Later: three-point SDP and interval
   arithmetic for non-LP cases (N = 5, 7, 8).
Dependencies and feasibility: LeanGeodesy (unit sphere, geodesic distance, caps, Delsarte and three-point SDP exact certificates)
is the natural base and uses the same technique as the N=7/8 Lean proofs.
- First independent piece, Coulomb N = 4, 6 or 12 via an LP certificate: HIGH (days to two weeks), assuming LeanGeodesy exposes
  Gegenbauer positive-definiteness (UNVERIFIED, I did not read it).
- Audit-port of the N=7 Lean proof to v4.34.0 plus a human check of its statement: MEDIUM; a verification task, not new maths.
- Formal N=5: LOW-MEDIUM. Smale 7 or BHS: not feasible; even a faithful formal statement is a research task.
- Exact check of 2611.15783 closed forms (C_BHS bound, c_step, c_seam, C_1): MEDIUM; only the unconditional Lemmas 4.1, 4.2 are
  checkable, Thm 4.3 is conditional on (A).

---------------------------------------------------------------------------------------------------
## PART C. Michel's boundary rigidity and the Calabi-Croke conjecture

### C.1 Michel's boundary rigidity conjecture
Statement (Michel 1981, as described in Alvarez-Lefeuve-Lowe-Smith and search summaries): a compact simple Riemannian manifold with
boundary (strictly convex boundary, no conjugate points, unique geodesics) is boundary distance rigid: if d_g = d_g' on boundary pairs
then g' = phi^* g for a diffeomorphism phi fixing the boundary. OPEN in dimension >= 3.
- Dim 2: Pestov-Uhlmann, Ann. of Math. 161 (2005) 1093-1110, arXiv:math/0305280. THEOREM (venue confirmed by search; proof not opened).
- Burago-Ivanov, Ann. of Math. 171(2) (2010) 1183-1211, doi 10.4007/annals.2010.171.1183: metrics C^2-close to Euclidean on a region with
  connected boundary are minimal fillings and boundary rigid. THEOREM. Almost hyperbolic case: arXiv:1011.1570, Duke Math. J. 162(7)
  (2013). THEOREM (search).
- Stefanov-Uhlmann-Vasy, arXiv:1702.03638 (v3 May 2021): THEOREM (abstract read): local rigidity near strictly convex boundary points;
  lens rigidity for simply connected manifolds with strictly convex boundary and a strictly convex foliating function (covers K <= 0,
  K >= 0 or no focal points). Journal venue (Annals 2021, from memory) UNVERIFIED. The passage from lens to boundary rigidity for
  simple metrics is from memory: UNVERIFIED.
- Gromov 1983 (Euclidean domains are boundary rigid), Besson-Courtois-Gallot (GAFA 1995), Croke (JDG 1991), Mukhometov, Otal,
  Paternain-Salo-Uhlmann (Invent. 2013; Math. Ann. 2015), Guillarmou (JAMS 2017): UNVERIFIED (named from memory, none opened).
- 2023-2026 seen: Alvarez-Lefeuvre-Lowe-Smith, arXiv:2609.29470 (24 Sep 2026), boundary AREA rigidity in dimension 3 (a different problem,
  modelled on Michel): THEOREM for generic area-simple metrics locally (C^14-small conformal factor) and for real-analytic conformal
  factors globally (I read about 100k of 226k characters; UNVERIFIED beyond abstract and theorem list). Also arXiv:2510.27085 (2D lens
  rigidity, title only) and Alexakis arXiv:1711.09379 (minimal areas, title only): UNVERIFIED.
- Formalization: none found (searches for Lean/Isabelle/Coq boundary rigidity or systolic inequalities returned nothing). Mathlib has
  IsRiemannianManifold and mfderiv (the Gromov repo uses them at 4.29.0) but, as far as I know, no exponential map, geodesic flow or
  conjugate points (UNVERIFIED for v4.34.0).
Dependencies and feasibility: nothing in the three libraries applies. "Simple manifold" cannot even be stated without geodesics and the
exponential map. First piece: LOW (months, needs a Riemannian library beyond Mathlib's); only a toy model computation (hemisphere,
hyperbolic disk) is cheap. Not recommended as a first target.

### C.2 Calabi-Croke conjecture (Croke's inequality on S^2)
Statement (Beach-Rotman, arXiv:1912.07711, read in source): for a Riemannian 2-sphere of area A, the shortest closed geodesic obeys
l <= 12^(1/4) sqrt(A) (l^2 <= 2 sqrt 3 A), equality for the Calabi-Croke sphere, the double of a flat equilateral triangle (flat sphere with
three conical points). Label: CONDITIONAL (open conjecture, called "conjectured" there).
Proved bounds on l/sqrt(A) for S^2 (Beach-Rotman introduction, read in source):
- Croke: l <= 31 sqrt(A) (JDG 1988 from memory, UNVERIFIED venue). THEOREM.
- Nabutovsky-Rotman (2002), Sabourau (2004), Rotman (2006): l <= 4 sqrt(2A) ~ 5.66 sqrt(A). THEOREM per Beach-Rotman; individual years and
  venues from memory (UNVERIFIED).
- Hebda and Burago-Zalgaller: l <= sqrt(2A) for non-simply-connected closed orientable surfaces. THEOREM (cited there).
- Beach-Rotman (arXiv Dec 2019): l <= 4 sqrt(2A) for once-punctured spheres, l <= 2 sqrt(2A) for >= 2 ends. THEOREM per its abstract; refereeing
  status unknown.
Local extremality: Balacheff (2010) and Sabourau arXiv:0907.2223 (abstract read): conical-singular metrics near the Calabi-Croke metric satisfy
the sharp bound, written there with diastole diasZ, area >= (1/(2 sqrt 3)) diasZ^2, equality iff homothetic. THEOREM (local only; I did not check
how diastole relates to the shortest closed geodesic). arXiv:1410.7790 (geodesic flows on S^2) seen in search only: UNVERIFIED.
Open: the global inequality; the best proven constant (5.66) is about 3 times the conjectured 1.86. No 2023-2026 progress on closed S^2 found
beyond Beach-Rotman for punctured cases. No formalization found.
Dependencies and feasibility: LeanGeodesy gives the round sphere (l = 2 pi, A = 4 pi, l^2/A = pi ~ 3.14, below 2 sqrt 3 ~ 3.46). A finite piece:
the Calabi-Croke model has area (sqrt 3/2) s^2 and the ratio 2 sqrt 3 once its shortest closed geodesic is known; doable with
LeanComputationalGeometry in exact arithmetic but needs a definition of closed geodesic on a conical surface: MEDIUM-LOW. The real inequality
needs min-max geodesic theory: not feasible soon.

---------------------------------------------------------------------------------------------------
## Recommended order (assessment)
1. LP/Delsarte certificates for the sharp Coulomb cases N = 4, 6, 12 on top of LeanGeodesy.
2. Audit-port of the N=7 Lean proof to v4.34.0 with a human check of the statement.
3. CLZ arithmetic (A.4) as an independent check, keeping the geometric theorem as an explicit external hypothesis.
4. Everything else waits for a Riemannian library.
Caveat: all 2026 sources are single preprints or blog posts and may change; the Gromov repo already shows drift between README, paper and
FORMALIZATION.md. Several items are UNVERIFIED on purpose rather than filled from memory.
