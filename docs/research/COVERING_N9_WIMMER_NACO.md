<!-- Literature survey compiled 2026-11-28 by a delegated research agent. The body of Wimmer 2017 could not be read (paywalled); the NACO paper was read through its arXiv preprint. Claims marked UNVERIFIED were not confirmed against a primary source, the algebraic data for N = 9 come from Rathbun 2020 and are numerical identifications, and nothing here has been re-derived. Do not cite a number from this file without opening the source. -->

# Spherical covering by N equal caps: Wimmer 2017, the case N = 9, and the NACO 2025 SDP hierarchy

Research date 2026-11-28. Labels: THEOREM / CONDITIONAL / NUMERICAL / FORMAL / UNVERIFIED. "Assessment" = own reasoning, labelled UNVERIFIED.

## 0. Corrections to the previous pass

- The author is Lienhard Wimmer, not "Lars". OpenAlex gives his affiliation as "Natural Science and Technical
  Academy Isny" (https://api.openalex.org/works/doi:10.1007/s00454-017-9891-x). [THEOREM: bibliographic fact]
- The keywords on the Springer page are "Covering, Sphere, Equal circles, Schütte arrangement, Spherical
  arrangement". Received 16 Aug 2013, revised 7 Feb 2017, published 12 Apr 2017, 8 figures, 10 references,
  MSC 52C15, 52C17, 51M16. [THEOREM: bibliographic fact from the Springer landing page]
- N = 10 and 14: the 1969 paper is by Gábor Fejes Tóth (zbMATH 0197.18602, Stud. Sci. Math. Hung. 4 (1969)
  225-247). Hardin-Petrache-Saff (Potential Anal. 56 (2022) 21-64, arXiv:1902.08497) and Wimmer's 2017
  reference list (via Crossref) both say "G. Fejes Tóth". Borodachov (arXiv:2210.12472) lists it under
  L. Fejes Tóth, which is a citation slip. The attribution of N = 10, 14 to G. Fejes Tóth 1969 now has three
  independent secondary sources (OEIS A401549, Hardin-Petrache-Saff 2022 Sec. 8.1, Wimmer's own note, see 1.4).
  I could not open the 1969 paper (no free copy; zbMATH has no review). [UNVERIFIED: primary not read]
- N = 8: Tarnai-Gáspár's value as quoted by Rathbun is 48.138529 deg, but Rathbun, Sloane's table (via Rolfes's
  thesis, Table 5.1) and Pfoertner all give 48.1395291 deg. The 48.1385 figure is most likely a transcription
  slip in Rathbun's table or in Tarnai-Gáspár. [NUMERICAL]

## 1. Wimmer 2017 (Discrete Comput Geom 57 (2017) 763-781, doi:10.1007/s00454-017-9891-x)

### 1.1 Access attempts
- Springer: "a preview of subscription content". No open-access version. Body text, theorems and figures not
  visible. [UNVERIFIED: paywalled]
- Semantic Scholar: openAccessPdf "CLOSED", 0 citations listed. OpenAlex: oa_status "closed",
  any_repository_has_fulltext false. No arXiv version. Google Scholar not queried directly; CORE needs an API
  key and was not queried. [UNVERIFIED]
- Wimmer's site lienhard-wimmer.com is partly parked (IONOS/Sedo). The 1998 Salzburg dissertation chapters are
  online (http://lienhard-wimmer.com/source/stud/diss.html), but the dissertation is about maximum-volume
  inscribed polyhedra, "Das maximale Volumen der konvexen Hülle von Punkten auf der Einheitskugel", not about
  covering. Wayback captures of lienhard-wimmer.de/geometrie/tmath/covpkt1.html and covpkt2.html (2017) are
  only Java test applets: "Überdeckung der Kugel durch 9 kongruente Kreise ... 9 Kreise mit demselben Radius
  46 Grad". No archived copy of a covering preprint was found. [UNVERIFIED]

### 1.2 What is publicly stated
- Abstract (Springer, verbatim first sentence): "How has a sphere to be covered by n equal circles so that the
  angular radius of the circles will be as small as possible?" It goes on to say the problem is solved for
  n = 8 and the combinatorial type of the solution for n = 9 is determined. [THEOREM: claim in a refereed paper;
  proof not read]
- zbMATH review 1370.52036 (Egon Schulte): "The author proves that an arrangement of eight circles found by
  Schütte is optimal and provides the solution for n=8 ... Also determined is the combinatorial type of a
  solution for n=9." So for N = 8 the optimum is Schütte's 1955 candidate (Math. Ann. 129, 181-186).
  [THEOREM: refereed paper plus independent review; proof not read]
- Exact theorem statements, the proof method, and whether the N = 9 radius is determined: not visible.
  [UNVERIFIED: paywalled]

### 1.3 Indirect evidence on the method (reference list via Crossref api.crossref.org/works/10.1007/s00454-017-9891-x)
The 10 references are: Brinkmann-McKay, plantri (software, accessed 01 Oct 2016); Brückner, Vielecke und
Vielflache (1900); Engel, On the enumeration of polyhedra (Discrete Math. 1982); G. Fejes Tóth 1969;
L. Fejes Tóth, Lagerungen (1972); Heppes 2003 (thinnest covering of the elliptic plane by 4 circles); Jucovič
1960; Schütte 1955; Sigl, Ebene und sphärische Trigonometrie (1977); Tarnai-Gáspár 1991.
- Assessment: citing plantri (planar triangulation generator), Engel and Brückner (polyhedron enumeration)
  strongly suggests a computer-assisted enumeration of combinatorial types of triangulations (the Delaunay
  triangulation of the centres, with 2N-4 triangles) followed by elimination with spherical-trigonometric
  estimates (Sigl). Whether elimination is by hand inequalities or by computer, and whether it uses area or
  angle sums, cannot be confirmed. [UNVERIFIED: inference from the reference list only]
- Corroboration: Hoehner-Ledford (arXiv:2608.04392v2, 6 Nov 2026) describe Wimmer's 1998 method for the
  analogous max-volume N = 9 problem: "vertex-star volume bounds and exclusions of local configurations ...
  his estimates exclude trivalent vertices and eliminate the other combinatorial types", leaving one type
  (triaugmented triangular prism) whose optimisation he did only "under symmetry assumptions". This shows his
  style (type reduction, then a symmetric calculation). It is not evidence about the 2017 covering proof.
  [UNVERIFIED as a description of the 2017 paper]

### 1.4 Conflicting claim by the author
- Wimmer's undated web note (http://lienhard-wimmer.com/source/downl/teichmann.pdf, archived 2020-2021) lists
  "N = 8, 9 Lienhard Wimmer [5]" among exactly solved cases, citing "[5] Wimmer, Lienhard: Covering the Sphere
  with Eight or Nine Equal Circles, preprint". The refereed 2017 version claims only the combinatorial type for
  n = 9. Treat N = 9 as not proved. (The same note also lists N = 5, 6, 7 under Schütte and N = 2, 3, 4, 12
  under L. Fejes Tóth.) [UNVERIFIED: unrefereed author claim, superseded by the refereed abstract]
- The same note proves an equivalence: minimising the covering radius is the same as choosing N points on S^2
  to maximise the minimal distance from the origin to a facet of the convex hull. The covering radius is the
  largest spherical circumradius of the hull's triangular faces. [THEOREM: elementary, the argument is given in
  the note and I checked it]

## 2. N = 9

### 2.1 What is proved
- Wimmer 2017: the combinatorial type of an optimal covering for n = 9 is determined. [THEOREM; proof not read]
- Which type it is: not visible in any accessible source. Assessment: it is presumably the type of the
  D3h configuration below, but no source says so. [UNVERIFIED]
- The optimal radius and the optimal configuration for N = 9 are not proved in any source found. OEIS A401549
  (Pfoertner, Nov 2026): "For n = 9 Wimmer determined the combinatorial type of the solution. The remaining
  terms are conjectural". [UNVERIFIED that no proof exists; none found up to 2026-11-28]

### 2.2 Best known configuration (Rathbun, arXiv:2008.04441, 2020, "Some spherical coverings on S2 and their algebraic numbers")
- Structure, quoted: "the caps at the vertices of 3 equilateral triangles, all co-planar, with one triangle at
  the equator, and the other 2 triangles equidistant above and below the equator. The smaller triangles are
  arranged exactly at 180° rotation with respect to the triangle on the equator." Symmetry order 12 (D3h),
  A401549 a(9) = 12. [NUMERICAL]
- Exact coordinates (Rathbun, Table 2). Let a = 0.6961773622954127151... be a root of
      16x^8 - 72x^6 + 129x^4 - 66x^2 + 9.
  Then, with s = sqrt(1 - a^2):
      upper:   (s, 0, a), (-s/2,  (sqrt3/2)s, a), (-s/2, -(sqrt3/2)s, a)
      equator: (1/2, sqrt3/2, 0), (-1, 0, 0), (1/2, -sqrt3/2, 0)
      lower:   (s, 0, -a), (-s/2,  (sqrt3/2)s, -a), (-s/2, -(sqrt3/2)s, -a)
  Rathbun defines "height" h = cos(rho) and "radius" r = sqrt(1-h^2) = sin(rho), where rho is the angular radius:
      height = 0.6961773622954127151... root of 16x^8 - 72x^6 + 129x^4 - 66x^2 + 9   (same a)
      radius = 0.7178698212262454947... root of 4x^4 - 4x^3 + 3x^2 + 4x - 4
      rho = 45.8788878287 deg   (Rathbun Table 17; Tarnai-Gáspár 45.878888; Pfoertner 45.8788878287)
  The root selection is by the decimal value; the minimal polynomials are as Rathbun printed them (found from
  high-precision numerics, not proved). [NUMERICAL]
- Structural remark derived from the table: cos(rho) equals the z-coordinate of the upper triangle. So the
  north pole is at angular distance exactly rho from all three upper centres; the poles are deep holes
  (triple points) of the covering. [NUMERICAL: read off Rathbun's table, not separately stated by him]
- Pfoertner's independent check (OEIS A401549, a401549.txt, Nov 2026; minimax by Voronoi relaxation plus
  sequential LP, 60 random starts): rho = 45.8788878287, hits 34/60, sym 12, "active= 8 stressed= 8",
  distinct_local=3, kktres=1.1e-07. Numerical evidence for global optimality and a non-degenerate KKT point.
  [NUMERICAL]

### 2.3 Best proved lower bound: L. Fejes Tóth 1943
- Musin, "Five Essays on the Geometry of László Fejes Tóth", arXiv:1604.02776v6 (2017), Theorem 1.1, quoting
  L. Fejes Tóth 1943: "If Ω is the density of a covering of S2 by N congruent spherical caps then
  Ω ≥ (N/2)(1 - (1/sqrt3) cot ω_N)", where ω_N := Nπ/(6N-12). [THEOREM]
- In radius form: Ω = N(1 - cos rho)/2, so the bound is equivalent to
      cos(rho_N) <= cot(ω_N)/sqrt3,  i.e.  rho_N >= arccos( cot(Nπ/(6N-12)) / sqrt3 ).
  [THEOREM: algebraic rearrangement I did. It agrees with Rolfes 2019 thesis eq. on p. 6:
   N(S^2,r) >= 2 arccot(sqrt3(1-2ω_r)) / (arccot(sqrt3(1-2ω_r)) - π/6), where 1-2ω_r = cos rho.]
  The bound is tight exactly for N = 3, 4, 6, 12 (Musin, for the packing analogue; for covering N = 4, 6, 12 it
  reproduces 70.53, 54.74, 37.38 deg). [THEOREM for 4, 6, 12]
- N = 9: ω_9 = 3π/14, and cot(3π/14) = tan(2π/7), so rho_9 >= arccos( tan(2π/7)/sqrt3 ). By hand,
  tan(2π/7) ≈ 1.25396, divided by sqrt3 ≈ 0.72397, so rho_9 >= ≈ 43.61 deg. The gap to 45.879 deg is about
  2.27 deg. [THEOREM for the closed form; NUMERICAL (hand) for 43.61]
  Cross-check: Rolfes's thesis Table 5.1 (kups.ub.uni-koeln.de/9917) evaluates the Fejes Tóth bound at
  rho = 45.8788878 deg as N >= 8.205, so the density bound cannot reach 9 at the conjectured radius. [NUMERICAL]
- No better lower bound specific to N = 9 was found. Wimmer's combinatorial-type result is a structural
  statement, not a numerical lower bound. [UNVERIFIED that none exists]

### 2.4 What is unproved, and the reduction to a finite problem (assessment)
Unproved: (i) within Wimmer's combinatorial type, that the D3h configuration is the global minimiser of the
radius; (ii) uniqueness up to isometry; (iii) the exact algebraic value (Rathbun's polynomials are guessed by
integer-relation-style fitting). [UNVERIFIED: no source claims them proved]

Assessment [UNVERIFIED]:
- With the triangulation type T fixed (9 vertices, 14 triangles), the radius is the maximum over 14 triangles of
  the spherical circumradius, provided T stays Delaunay. That leaves a min-max over (S^2)^9 / SO(3), i.e. 15
  real parameters. It can be written as a polynomial program: minimise t subject to
  <c_f, p_i> >= t' for i in face f, with |c_f| = 1 (c_f the circumcentre and t' = cos rho), and all p_i on the
  sphere. That is roughly 27 + 42 variables with equalities, or fewer if the circumcentres are eliminated.
  This is a finite semialgebraic problem.
- If Wimmer's type comes with "local" inequalities (e.g. each Delaunay triangle has circumradius <= rho), the
  feasible set near the optimum is compact. The D3h point has 8 active triple points (Pfoertner "active=8").
  A certificate needs: (a) local optimality via a strict second-order KKT certificate, provable exactly in
  Q(a) because all data are algebraic of degree <= 8; (b) global optimality in the 15-dimensional box, by
  interval branch-and-bound (Hales/Flyspeck-style; verifiable in Lean with interval arithmetic) or by a
  Positivstellensatz/SOS certificate. SOS at 15+ variables of moderate degree is borderline large but
  plausible if D3h symmetry is not assumed and the domain is split by cases. Interval B&B is the more
  realistic route; it is what proved comparable small-N packing and covering results.
- What must come from Wimmer's paper first: the exact type, and whether his proof already has a computer part
  (plantri enumeration) that would also need formalisation. Without the body this cannot be planned in detail.

## 3. Follow-up work up to November 2026 (N = 8, 9, 10, 11, 13, 14)

- Citations of Wimmer 2017: OpenAlex lists 3. (1) Hardin, Petrache, Saff, "Unconstrained polarization
  (Chebyshev) problems", Potential Anal. 56 (2022) 21-64, doi:10.1007/s11118-020-09875-z, arXiv:1902.08497,
  Sec. 8.1, which states optimal coverings are known "for N = 8 by L. Wimmer [40] and for N = 10 and 14 by
  G. Fejes Tóth [23]" (N = 9 not listed). (2) Borodachov, arXiv:2210.12472 (2022), "on S2 for N = 1 - 8, 10,
  12, and 14". (3) a 2021 MDPI Symmetry paper on partial circle covering (not relevant). zbMATH lists only (1).
  None of them gives new results for N = 9. [THEOREM for what they state; their N lists are secondary]
- Rathbun 2020: 0 citations in OpenAlex. He claims structures for 11, 13, 17, 20 that "definitely" are local,
  not global, minima, and a "new lower value" for N = 19 (30.3749 vs 30.382284). Pfoertner later found 30.3687
  for N = 19. [NUMERICAL]
- OEIS A401549 (Pfoertner, created 17 Nov 2026): symmetry orders for n = 4..15: 24, 12, 48, 20, 8, 12, 16, 2,
  120, 4, 24, 12. It says optimality is proved for 4, 6, 12 (L. Fejes Tóth), 5, 7 (Schütte), 8 (Wimmer),
  10, 14 (G. Fejes Tóth). For N = 13 one cap is a "rattler" (free point), so the configuration is not unique.
  N = 11: the best known configuration has symmetry order 2 (Tarnai-Gáspár, Elem. Math. 41 (1986) 35-38).
  [NUMERICAL for the values; secondary for the proof attributions]
- Hoehner-Ledford, arXiv:2608.04392 (2026), finish the N = 9 maximum-volume inscribed polytope problem using
  Wimmer's 1998 reduction. That is a different problem (volume, not covering) but the same author and the same
  "type reduction, then optimise one type" pattern; it shows such two-stage proofs get completed.
  [THEOREM (preprint, not refereed): their result]
- No paper found (arXiv searches, OpenAlex, zbMATH, web search) proving N = 9, 11, 13 or re-proving 10 or 14
  between 2017 and 2026-11-28. [UNVERIFIED: absence of evidence]
- No formalisation of any spherical covering optimality result (any N) was found. [UNVERIFIED]

## 4. Riener-Rolfes-Vallentin, doi:10.3934/naco.2025015

Bibliographic: C. Riener, J. Rolfes, F. Vallentin, "A semidefinite programming hierarchy for covering problems
in discrete geometry", Numerical Algebra, Control and Optimization 16 (2026) 157-170. Online 4 June 2025;
received Jan 2024. Open preprint arXiv:2312.11267v2 (23 May 2025), which I read in full (14 pp.). Based on
Rolfes's PhD thesis, "Convex Optimization Techniques for Geometric Covering Problems", Cologne 2019
(https://kups.ub.uni-koeln.de/9917/1/DissertationRolfes.pdf, also read in the relevant parts). [THEOREM: bibliographic]

### 4.1 What it does
- Problem: the covering number N(X, r) = min |Z| with the union of closed balls B(z, r) equal to X, for a
  compact metric space X. This is the dual formulation (fix r, minimise the count). It is the domination number
  of the covering graph C(X, r), where x ~ x' iff d(x, x') <= r. [THEOREM]
- Method: a Lasserre-type moment hierarchy for the dominating-set 0/1 ILP, lifted to infinite X in the style of
  the de Laat-Vallentin packing hierarchy (Math. Program. 151 (2015)). The variables are a Radon measure lambda
  on I_2t, the subsets of size <= 2t that are ε-separated (independent in the packing graph P(X, ε)). The
  constraints are a moment constraint A_t* lambda PSD and localizing constraints (B_{t-1}^z)* lambda PSD for
  every z in X, encoding "every z is covered". It is a moment relaxation; the dual has PSD kernels K, K' (an
  SOS-like certificate). [THEOREM]
- Theorem 4.2: las_1 <= las_2 <= ... <= las_{α(P(X,ε))} = N(X, r). These are lower bounds converging in finitely
  many steps. [THEOREM] It needs an a priori ε > 0 such that some optimal covering is ε-separated. The authors
  say "Determining an appropriate α involves additional geometric considerations which usually are challenging
  to establish", and that experiments by Nando Leijenhorst "indicate that the hierarchy is quite sensitive to
  the choice of ε". [THEOREM / NUMERICAL (unpublished experiments)]
- Theorem 5.1: if Aut(X) acts transitively, then las_1 = las_1^dual = 1/ω_r, which is just the volume bound.
  So on S^2 the first level is weaker than Fejes Tóth's bound. Strong duality is shown in Rolfes's thesis.
  [THEOREM]
- Computations: none. The paper proves no numerical bound. The thesis (Sec. 5.7) derives a finite-dimensional
  symmetry-reduced SDP for level t = 2 on S^2, using Bochner/Peter-Weyl zonal matrices (as in de Laat's energy
  work) for the O(3)-invariant kernel K, and Bachoc-Vallentin's stabiliser-invariant kernels for K'. It states
  that choosing the truncation degree d "is a challenging task for future research". It also states that
  sampling constraints gives only "almost feasible" solutions, and that the repair kernels needed for a
  rigorous bound "are still to be found for the covering number". So: no SDP size, no numbers, no rigorous
  certificate. [THEOREM for the statements; NUMERICAL results: none exist]

### 4.2 Reusability of an exact-rational SDP pipeline (Delsarte LP / Bachoc-Vallentin three-point, Lean-kernel checked)
Assessment [UNVERIFIED]:
- Shared parts: the t = 2 covering SDP on S^2 uses the same algebra as the packing three-point bound: Gegenbauer
  / Legendre zonal functions for O(3), Bachoc-Vallentin's Stab(e)-invariant matrices Y_k(u, v, t), and PSD
  blocks. The exact-rational PSD checking (LDL^T or Cholesky over Q in the kernel) and the polynomial
  nonnegativity checks on [-1, 1]^k reuse directly.
- Differences:
  (1) Direction. Covering gives lower bounds on a count, N(S^2, r) >= las_t. For a radius statement
      ("9 caps of radius < rho* cannot cover") one needs las_t(r) > 9 for all r < rho*, i.e. a certificate
      that holds uniformly in r. The cap indicator 1_{B(e,r)} enters the localizing operator, so r appears
      inside the constraint functions (polynomials restricted to cos d <= cos r), not just as a parameter of
      the domain like the packing angle. The domain splits at u = cos r. That fits existing "nonnegative on an
      interval" machinery, but certificates must be produced per r or parametrically.
  (2) Extra constraint families. The localizing kernel K' lives on I_1 x I_1 with Stab(e) symmetry, and the
      constraint 1_{I=1} - B_2 K - B_2^id K' >= 0 must hold on all orbits Q of ε-separated sets of size <= 4
      (t = 2). That is a semialgebraic domain in several angular variables with an ε-separation condition.
      Packing BV needs triples only; here quadruples of points enter (I_{2t} with t = 2). That means new
      invariant-theory parametrisations and positivity certificates on higher-dimensional orbit spaces.
  (3) ε. The hierarchy is only valid if an optimal covering is ε-separated, so a separate, formally proved
      lemma giving ε for N = 9 caps of radius ~46 deg is needed (e.g. from a density/area argument). Packing
      has no analogue.
  (4) Strength. Level 1 equals the volume bound (Thm 5.1) and is useless. Level 2 is untested numerically, so
      it is unknown whether it beats Fejes Tóth (43.61 deg for N = 9), let alone reaches 45.88 deg. Sharpness
      at N = 9 is unlikely at t = 2 (the analogous packing bounds are sharp only in rare cases).
  (5) Min-max vs packing. Optimality of a specific covering (upper = lower) needs a sharp lower bound, which
      SDP is unlikely to give here. The realistic Lean route for N = 9 is the one in Sec. 2.4: Wimmer's type
      reduction, then interval/SOS verification of a 15-parameter min-max. An SDP pipeline could at most
      supply a non-sharp global lower bound and would be new research (no numbers exist yet).

## 5. Summary table

| N | Status | Source |
|---|---|---|
| 2-7, 12 | THEOREM | L. Fejes Tóth 1943/1953; Schütte 1955 (5, 7) |
| 8 | THEOREM (Schütte's arrangement optimal; proof not read) | Wimmer 2017 + zbMATH 1370.52036 |
| 9 | combinatorial type THEOREM (type not visible); radius and configuration NUMERICAL, 45.8788878287 deg, sin rho root of 4x^4-4x^3+3x^2+4x-4 | Wimmer 2017; Rathbun 2020; Pfoertner 2026 |
| 9 lower bound | THEOREM rho_9 >= arccos(tan(2π/7)/sqrt3) ≈ 43.61 deg (hand) | L. Fejes Tóth 1943 via Musin 2017 |
| 10, 14 | THEOREM by secondary attribution, primary unread | G. Fejes Tóth 1969 |
| 11, 13 | NUMERICAL only (13 has a rattler) | Tarnai-Gáspár 1986/1991; OEIS A401549 |
| SDP covering hierarchy | THEOREM (convergence, level 1 = volume bound); no computations | Riener-Rolfes-Vallentin 2025/26; Rolfes 2019 |
