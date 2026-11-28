<!-- Literature survey compiled 2026-11-28 by delegated research agents. Sources were read through web tools, several only as abstracts or via a summarising fetcher; claims marked UNVERIFIED were not confirmed against a primary source, and nothing here has been re-derived. Do not cite a number from this file without opening the source. -->

# Covering S^2 by N equal closed caps: literature status (as of 2026-11-28)

Conventions. rho_N = minimal cap angular radius (degrees). Labels: THEOREM, CONDITIONAL, NUMERICAL, FORMAL,
UNVERIFIED (could not open the source, reason given). "Secondary" = I read a page that reports a result, not the
primary paper. Per instructions I ran no computation, so no number below was computed by me.
Working files (downloads) are in the scratchpad dir "dl/", not part of the report.

## 0. Access log (what I could and could not open)

- Wimmer, DCG 57 (2017) 763-781, doi 10.1007/s00454-017-9891-x: Springer landing page (hybrid access) opened via curl:
  ABSTRACT, keywords, and the reference list only. Body is paywalled. No arXiv version exists (arXiv API query
  au:Wimmer + "covering the sphere" returned 0 hits; web search found none). So I did NOT see any table in the paper.
  Possibly the paper has no table (it is called "a note" in its own abstract), but that is UNVERIFIED.
- Sloane, https://neilsloane.com/coverings/index.html (and http://, /coverings/): server answers HTTP 200 with a
  0-byte body to curl and WebFetch; web.archive.org is blocked for the fetch tool. UNVERIFIED (empty response).
  What I know about that page comes only from (a) Pfoertner's mirror/visualisation page, (b) OEIS A401549 and
  (c) Rathbun 2020, all secondary.
- spherical-codes.org: opened; first 100,000 of 576,951 characters read. It is a PACKING (Tammes / spherical code)
  table. Its text: "maximizing the minimal angle between the points", rigorous upper bounds on cosines rounded up to 12
  decimals, optimal cases starred. No covering data seen in what I read; the remaining 477k characters were not read.
  Label for "has covering data": not found in the portion read.
- Tarnai-Gaspar 1991 (Math Proc Camb Phil Soc 110, 71-89): Cambridge page shows abstract + references only; the table
  "Proven and conjectured best coverings" is on ResearchGate (HTTP 403). Its values were read only through
  Rathbun's Table 17 (secondary).
- Gabor Fejes Toth 1969 (Stud. Sci. Math. Hung. 4, 225-247) and Dalla Volta, Schutte 1955, Jucovic 1960,
  L. Fejes Toth 1943: not opened (old, not online). UNVERIFIED primary; secondary attributions below.

## 1. Sources actually read

### 1.1 Wimmer 2017 (abstract, verified verbatim from Springer page)
"How has a sphere to be covered by n equal circles so that the angular radius of the circles will be as small as
possible? In this note the problem is solved for n=8 and the combinatorial type of the solution for n=9 is
determined."  MSC 52C15, 52C17, 51M16. Keywords: Schutte arrangement.
Reference list (verified, only 6 entries): G. Fejes Toth, Kreisueberdeckungen der Sphaere, Stud. Sci. Math. Hung.
(1969); L. Fejes Toth, Lagerungen... (2nd ed. 1972); Heppes, Az elliptikus sik legritkabb fedese negy egybevago
korrel, Mat. Lapok 8/9 (2003) 4-6; Jucovic, Mat.-Fyz. Cas. 10 (1960) 99-104; Schutte, Math. Ann. 129 (1955)
181-186 ("Ueberdeckungen der Kugel mit hoechstens acht Kreisen"); Tarnai-Gaspar 1991.
  - Claim: N=8 optimum determined.   Status: THEOREM (author's claim in abstract; proof body not read).
  - Claim: for N=9 only the combinatorial type of the optimum is determined, so the N=9 radius is not claimed
    proved by this paper. Status: THEOREM for the type (abstract); the radius value itself is NUMERICAL.
  - Method: UNVERIFIED (body paywalled). Reference list suggests Schutte-style contact-graph case analysis plus
    Heppes's elliptic-plane 4-circle result (that is my inference from the references only).

### 1.2 OEIS A401549 (secondary, entry dated Nov 17 2026, by H. Pfoertner)
Title: order of the symmetry group of the minimising arrangement. Data a(4..15) = 24,12,48,20,8,12,16,2,120,4,24,12.
Comments (as fetched): optimality proven for N=4,6,12 (L. Fejes Toth), N=5,7 (Schutte), N=8 (Wimmer), N=10,14
(G. Fejes Toth, Studia Sci Math Hungar 4 (1969) 225-247); for N=9 Wimmer determined the combinatorial type;
"The remaining terms are conjectural" (N=11,13,15 within the listed range), matching Hardin-Sloane-Smith and
Tarnai-Gaspar. For N=13 the optimal RADIUS does not fix the configuration: one point moves freely in an open region
(so a(13)=4 is the max-symmetry representative, generic position gives order 1). For N<=20 values were
re-confirmed by independent numerical minimax and agree with the Hardin-Sloane-Smith table to 7 decimals.
Caveats: (i) the fetch tool paraphrases, so exact wording unverified; (ii) the entry credits its Python program to an
AI model, so treat the attribution list as a lead, not as a checked citation; (iii) "N=10,14 by G. Fejes Toth 1969" is
NOT confirmed by any primary I read. Rathbun (below) independently says N=10,12 are known and does not list 14.
Status of these attributions: UNVERIFIED primary (secondary report only).

### 1.3 Rathbun 2020, arXiv:2008.04441 (read in full text via pdftotext)
"Some spherical coverings on S2 and their algebraic numbers", Randall L. Rathbun, math.MG, 10 Aug 2020, no journal ref.
Says: global solutions n=2-6 and n=10,12 "already known"; putatively global for n=2-10,12,14,15,16,22,32,38 with
closed-form algebraic numbers; n=11,13,17,20 have 500-2000 digit spherical codes with NO algebraic numbers recovered
and are "a local minimum" (13: "Most likely a local minimum has been found"; closing section says the global
minimum for 11, 13, 17, 20 "needs to be found"). n=9: three coplanar equilateral triangles of caps (equator + two
symmetric ones). Table 17 compares Tarnai-Gaspar (TG) with Rathbun values; radii in degrees:
  N: TG / Rathbun
  8: 48.138529 / 48.1395290861 (TG differs at 4th decimal; Pfoertner and OEIS agree with Rathbun)
  9: 45.878888 / 45.8788878287
 10: 42.307827 / 42.3078266301
 11: 41.427196 / 41.4271959586 (flag: local minimum)
 12: 37.377368 / 37.3773681406
 13: 37.068543 / 37.0685427025 (flag: local minimum)
 14: 34.937927 / 34.9379269231
 15: 34.039900 / 34.0399001237
 16: 32.898812 / 32.8988127601
 17: 32.092933 / 32.0929327861 (local minimum)
 18: 31.013172 / 31.0132851551 (needs investigation; Pfoertner lists 31.0131718)
 19: 30.382284 / 30.3749090533 (new lower value; Pfoertner lists 30.3686748, lower again)
 20: 29.623096 / 29.6230957838 (local minimum)
 22: 27.810059 ; 32: 22.690480 ; 38: 21.069858 ; 42: 20.153842 (TG) vs 20.2572026800 (Rathbun, local min, large gap).
Status: NUMERICAL for all of these (no proof; Rathbun's own labels are "putatively").
Observation: N=18 and N=19 disagree across Pfoertner / Rathbun / TG, so the "best known" there is itself unsettled.

### 1.4 Pfoertner, "Coverings of the sphere with n equal caps" (randomwalk.de/sphere/caps, Jan 2017)
Tables for n=4..50 labelled "known best", coordinates "only approximations of moderate accuracy" intended for
visualisation, defers to Sloane's coordinates for high accuracy, states nothing about proof. Values (deg, 7 dp):
 n=4 70.5287794; 5 63.4349488; 6 54.7356103; 7 51.0265527; 8 48.1395291; 9 45.8788878; 10 42.3078266;
 11 41.4271960 (symmetry order 2); 12 37.3773681; 13 37.0685427 (order 4); 14 34.9379270; 15 34.0399001;
 16 32.8988128; 17 32.0929328; 18 31.0131718; 19 30.3686748; 20 29.6230958.
It describes Sloane's page as "his collection of spherical codes ... library of 3-d coverings". Status: NUMERICAL.
The description of the Sloane tables' provenance (Hardin-Sloane-Smith, numerical minimax) comes from the OEIS entry
only; I could not read Sloane's own page. UNVERIFIED.

### 1.5 L. Fejes Toth density bound (read in Musin, arXiv:1604.02776, Thm 1.1; extraction slightly garbled)
Covering density Omega of S^2 by N congruent caps satisfies Omega >= (N/2)(1 - cot(omega_N)/sqrt(3)) with
omega_N = N*pi/(6N-12) (my reading of the garbled line; check against the PDF before relying on it). Reference
given there: L. Fejes Toth 1943, Mat. Fiz. Lapok 50, 40-46 and the 1972 book. Status: THEOREM. A secondary source
(Brauchart et al., arXiv:1407.8311, via search snippet only) says this is tight only for N=3,4,6,12. UNVERIFIED
beyond the snippet.
Also verified (G. Fejes Toth, MSRI Publ. 52 (2005), disc covering paper, read): "the argument used by Schutte
[1955] for the determination of the thinnest covering of the sphere by 5 and 7 congruent caps". That is a primary
confirmation that Schutte 1955 proved N=5 and N=7. Status: THEOREM (as reported by a primary author in a
refereed volume). That paper itself covers a DISK by 8, 9, 10 disks, not the sphere. Do not conflate.

## 2. Classical claims requested, with status

- N=4, 6, 12 (L. Fejes Toth 1943): THEOREM, consistent with 1.5 and 1.2 (OEIS). Equality cases of the density bound.
- N=2, 3: trivial (radius 90 deg). THEOREM (Rathbun states known).
- N=5, 7 (Schutte 1955, Math. Ann. 129, 181-186): THEOREM (confirmed in 1.5, G. Fejes Toth 2005).
- N=5 "Dalla Volta / Fejes Toth": I found NO source mentioning Dalla Volta and N=5 covering. UNVERIFIED; what I
  can say is that Schutte 1955 is the attribution confirmed for N=5. Radius 63.434949 deg = arctan(2).
- N=8: Wimmer 2017 THEOREM (abstract). Value 48.139529 deg (Rathbun/Pfoertner; TG's 48.138529 looks like a
  transcription slip; I did not see TG's original, so call this an observation, not a finding).
- N=10: Rathbun says "already known". OEIS attributes to G. Fejes Toth 1969. Primary not read. UNVERIFIED primary,
  treat as THEOREM only on the strength of two independent secondary reports.
- N=14: only OEIS claims proof (G. Fejes Toth 1969); Rathbun lists 14 as putative. Conflict: UNVERIFIED.
- Danzer (1963 Habilitation) and Schutte-van der Waerden (1951): these are TAMMES (packing / max-min distance)
  results (N=5..9 resp. 10, 11), per search snippets and Musin's survey footnote. They are NOT covering results.
  Do not cite them for covering.
- Musin-Tarasov: "The strong thirteen spheres problem", DCG 2012, arXiv:1002.1439; "The Tammes problem for N=14",
  arXiv:1410.2536. Both PACKING (irreducible contact graph enumeration). I found no covering analogue by them or
  anyone; the search results did not mention one. Status for "a covering N=13 or N=14 proof exists": not found.
- Tarnai-Gaspar 1991: NUMERICAL conjectures N=15..20 and sporadic 22, 26, 38, 42, 50 (abstract, verified), method a
  cooling technique / cable-net rigidity heuristic. No proofs.
- Heppes 2003 (elliptic plane, 4 circles): title only, via Wimmer's reference list; content UNVERIFIED.
- Bohdanowicz: no relevant covering source found. UNVERIFIED / not found.
- Dumer, "Covering spheres with spheres", arXiv:math/0606002 (rev. 2018): the PDF was binary to my tool; the
  title and search snippets point to high-dimensional asymptotic covering densities, not S^2 small N. UNVERIFIED.
- Hardin-Sloane-Smith (Sloane's covering tables): UNVERIFIED primary (page empty). Secondary: OEIS says they are
  numerical, agree to 7 decimals with independent minimax runs for N<=20.
- 2018-2026 follow-ups on S^2 covering by equal caps: only Rathbun 2020 (NUMERICAL) and the OEIS/Pfoertner
  re-computation (Nov 2026, NUMERICAL) turned up in several searches. No new optimality proof found for any N.
  Absence of evidence from a handful of searches, not a proof of absence.

## 3. Formal / computer-assisted proofs
- Machine-checked proof of ANY spherical covering instance (Lean, Isabelle, Coq, HOL Light): none found in two
  web searches (the second searched Lean/Isabelle/Coq/HOL Light jointly). Status: not found.
- Adjacent, not covering of S^2: arXiv:2606.09600 (Lean 4, q-ary covering codes, Hamming space); arXiv:2604.23468
  (formalising dimension-8 sphere packing, Lean); arXiv:2609.25120 (dim-4 sphere packing / 24-cell conjecture;
  Voronoi cell volume >= 8 via "covering estimate" for <=22 contacts, exact volume identity + SDP certificate at 23,
  parts checked in Lean 4; abstract only read, the 10 MB PDF was too large for the fetch). None addresses covering
  S^2, and I did not open any repo. Label for these as evidence for a covering proof: none.

## 4. Answers

### (1) Best known upper bound (configuration) and best proved lower bound

Upper bounds are all NUMERICAL (putative optima), values in degrees to 6 decimals, source in brackets.
- N=9: 45.878888. Configuration: 3 coplanar equilateral triangles of caps (one on the equator, two symmetric above and
  below), symmetry order 12 [Rathbun 2020 Table 17 + text; Pfoertner 2017; OEIS]. Wimmer 2017 proves the combinatorial
  type of the optimum (THEOREM, abstract), so the remaining gap is between "optimal type" and a certified radius
  for that type; whether Wimmer's body already closes it is UNVERIFIED.
  Proved lower bound: the only proved bound I can cite is the L. Fejes Toth density bound (1.5). Numerical value
  not computed by me (no-code rule); see (2) for a way to get it. I found no better proved lower bound.
- N=11: 41.427196. Symmetry order 2, a pole cap plus five "dipoles" about the polar axis (Rathbun text, scanned
  fragment) [Rathbun; Pfoertner order 2]. Rathbun flags it a LOCAL minimum, global minimum "needs to be found".
  Proved lower bound: Fejes Toth density bound only; none better found. Nothing proved.
- N=13: 37.068543. Order 4 representative; the radius value has one free cap (OEIS), which means the optimum
  is not rigid, an unusual and informative fact. Rathbun: "Most likely a local minimum". Lower bound: same.
- Other unproved N where the best known is unsettled: N=18 (31.013172 vs 31.013285), N=19 (30.368675 per
  Pfoertner vs 30.374909 Rathbun vs 30.382284 TG), N=42 (20.153842 TG vs 20.257203 Rathbun), N=15-17, 20, 22 etc.
  all NUMERICAL. N=14 proven only per OEIS (UNVERIFIED primary), N=10 proven per Rathbun + OEIS.
- Proved values: N=2,3 (90), 4 (70.528779), 5 (63.434949), 6 (54.735610), 7 (51.026553), 8 (48.139529),
  12 (37.377368); 10 (42.307827) and 14 (34.937927) with the primary-source caveats in section 2.
  The N=8 and N=7 values are as printed by Rathbun/Pfoertner, not re-derived.

### (2) What would be needed to close or improve each

General frame (my reading of how the classical proofs work; the primaries for Schutte/Wimmer/G. Fejes Toth
were not read, so this is a plan, not a citation).
- Lower bound by Delaunay-triangle area. A covering by N caps of radius r induces a Delaunay triangulation
  with 2N-4 triangles, each with circumradius <= r. Max area of a spherical triangle of circumradius <= r is that of the
  equilateral one, so 4*pi <= (2N-4)*A_eq(r). This is the L. Fejes Toth bound and is tight only when an
  equilateral triangulation exists (N=4,6,12). For all other N it gives a gap; closing it needs non-equilateral-aware
  inequalities.
- Contact (Delaunay-edge) graph case analysis as in Schutte 1955 / Wimmer / the disc case of G. Fejes Toth 2005:
  at the optimum every vertex of the Delaunay triangulation has degree >= 3, most triangles have circumradius = r
  ("critical" triangles), and the optimal graph is rigid or locally minimal. Classify candidate graphs by degree
  sequence (excess 6*... constraint sum(6-deg)=12), prove local rigidity/optimality for each, and exclude the rest
  by an area or angle-sum inequality with strict slack. This is exactly what Wimmer reports for N=9 (type) and N=8
  (full). For N=9 the missing step is (a) the radius within the proved type and (b) possibly a gap to
  non-generic types; for N=11 the missing step is an exhaustive enumeration of graphs with 22 triangles; for N=13 the
  free cap makes the optimum a non-isolated minimum: any proof must be done on a set of optima, not a single
  configuration, which is harder than Tammes N=13 where uniqueness holds (Musin-Tarasov do not give anything for covering).
- Local-to-global. Numerical minimax gives only local minima; Rathbun explicitly says N=11,13,17,20 may not be global.
  A proof needs a certified global search, e.g. branch and bound over Delaunay combinatorial types with interval
  arithmetic on the vertex positions and circumradii.
- Improvement (finding better coverings) for N=18, 19, 42: a computer search with more restarts; the discrepancy among
  three tables shows at least two of them are not optimal. This is NUMERICAL work, not a proof.

### (3) What an exact-arithmetic certificate checker (rational vertices, supporting planes) could and could not do

Could address:
- UPPER bounds, rigorously: given N rational (or algebraic) centres and a rational r_hat, check that the caps
  cover S^2, i.e. every Voronoi/Delaunay vertex is within r_hat. With rational centres c_i (not unit; use
  directions), cover check = for each triple of the convex hull of the centres, circumcentre direction q, and
  check <q, c_i> >= cos(r_hat) with exact rationals (cos(r_hat) replaced by a rational lower bound, giving a rigorous
  r_hat slightly above the true radius). Hull facets and supporting planes are exactly the certificate: a facet
  plane n.x = d with all other centres on one side, so the hull is the claimed triangulation and the covering radius
  is the max over facets of the angle between facet normal and the facet vertices. This certifies "radius <= r_hat"
  for N=9, 11, 13 and any N, and certifies the upper bounds above to arbitrary rational precision. Good fit for Lean:
  decidable over Q, checking by `norm_num`/`decide` on explicit data.
- It can also certify claims like "this configuration is a local covering minimum" only partially (see below).
- The Fejes Toth lower bound for each N is an explicit trigonometric inequality; evaluating it with interval or
  rational bounds on arccos/cot is within reach of an exact certificate (needs rational enclosures of pi and
  trigonometric values, a Lean library task, not a geometric one).

Could NOT address:
- LOWER bounds beyond the density bound, i.e. optimality. Optimality is a universally quantified statement over all
  configurations of N points, not witnessed by one finite point set. A supporting-plane certificate on a given
  configuration proves nothing about other configurations.
- Exhaustiveness of a case analysis over contact/Delaunay graphs (needs enumeration + a per-case inequality
  proof; the enumeration can be certified by a verified generator, but that is a separate checker).
- Local optimality of N=11, 13 (rigidity: positive stress / infinitesimal rigidity certificate on the contact graph)
  is partially certifiable with exact linear algebra over Q (stress matrix PSD, rank), but only if the optimum has
  rational or checkable algebraic coordinates, and Rathbun reports no algebraic numbers for N=11, 13. Would need
  algebraic-number or interval arithmetic rather than rational vertices.
- The N=13 free cap: a rational certificate cannot represent a family of optima, only samples.

## 5. Open questions for a follow-up (things I could not do)
- Read Wimmer's full text (paywall: needs institutional access) to see whether N=9 radius is proven and what method
  was used, and the exact N=8 lower-bound lemma.
- Read Sloane's covering page and Hardin-Sloane-Smith data (server returns an empty body; try another network or
  the Wayback Machine from a browser).
- Read G. Fejes Toth 1969 (Stud. Sci. Math. Hungar. 4) to confirm the OEIS claim for N=10, 14.
- Evaluate the Fejes Toth lower bound numerically for N=9, 11, 13 (deliberately not done here).
