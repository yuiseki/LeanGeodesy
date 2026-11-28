<!-- Literature survey compiled 2026-11-28 by a delegated research agent (Hoehner-Ledford read from the arXiv LaTeX source; the Sloane page through Internet Archive snapshots). Labels as given; nothing re-derived except where docs/research/COVERING_GLOBAL_PLAN.md says so. Volume maximisation is a different problem from covering. -->

# Hoehner-Ledford (N=9 max volume), Wimmer thesis, Sloane coverings: source notes

Fetched 2026-11-28. Sources opened: arXiv abs page, PDF and LaTeX source of arXiv:2608.04392
(v2, file REVISED.tex/REVISED.bib, source tarball dated 2026-11-09); v1 abstract page; Wimmer's
own homepage and chapter PDFs; neilsloane.com (live) and its Internet Archive snapshots.
Labels: THEOREM (proved in the cited source, read by me), CONDITIONAL (proved assuming a cited
result), NUMERICAL, FORMAL, UNVERIFIED.

## 1. Hoehner, Ledford, arXiv:2608.04392

Bibliographic: S. Hoehner, J. Ledford, "The maximum volume polytope with nine vertices inscribed in
the sphere", arXiv:2608.04392. v1 submitted 5 Aug 2026; v2 is current ("18 pages, 2 figures,
version 2"; arXiv online date 2026-11-06). MSC 52A40; 52A38; 52B10. Longwood University.

### 1.1 Main theorem (v2, Theorem 1.1, verbatim content)
"Let P in P_9. Then vol(P) <= 3 sqrt(2 sqrt3 - 3) ~ 2.04375. Equality holds if and only if, up to
rotation, P is the triaugmented triangular prism with vertices"
a1=(1,0,0), a2=(-1/2, sqrt3/2, 0), a3=(-1/2, -sqrt3/2, 0),
x1=(r/2, sqrt3 r/2, h), x2=(-r,0,h), x3=(r/2, -sqrt3 r/2, h),
y1=(r/2, sqrt3 r/2, -h), y2=(-r,0,-h), y3=(r/2, -sqrt3 r/2, -h),
with h_* = sqrt(2 sqrt3 - 3) (~0.681), r_* = sqrt(1-h_*^2) = sqrt(4-2 sqrt3) = sqrt3 - 1 (~0.732).
P_9 = convex polytopes with at most nine vertices, all on S^2.
Label: CONDITIONAL on Wimmer's combinatorial reduction (Lemma 3.1 below); the restricted result
(Theorem 4.1, maximizer within the triaugmented-triangular-prism class T, no symmetry assumed) is
THEOREM (hand proof, read in full).

### 1.2 How Wimmer's dissertation is used
- Stated as Lemma 3.1: "Let P in P_9 have maximum volume. Then P is combinatorially equivalent to
  the triaugmented triangular prism." Attributed to "[Wimmer1998, Chapter I, Section 7; Chapter II,
  Section 1, pp. 16-17]".
- Used as a hypothesis, not re-proved: "We use his reduction as stated, and devote the rest of the
  paper to optimizing the remaining type." Description given: Wimmer "obtains this conclusion using
  vertex-star volume bounds and exclusions of local configurations. In particular, his estimates
  exclude trivalent vertices and eliminate the other combinatorial types."
- Wimmer's symmetric computation [Chapter III, Section 4, pp. 33-34] "identifies the equality
  configuration which our unrestricted estimate will recover."
- Acknowledgment: Wimmer read "the first version of this paper and [brought] our attention to his
  Ph.D. thesis". Version history matters: the v1 abstract says the authors themselves reduced via
  Berman-Hanes simpliciality ("reducing the 2,606 combinatorial types of 9-vertex polyhedra to 50"),
  then "We prove that a maximizer cannot have a trivalent vertex, leaving only five combinatorial
  types". v2 drops this and cites Wimmer instead (a commented-out overview in the v2 source still
  mentions "the five remaining combinatorial classes"). v1 full text NOT read: UNVERIFIED whether
  v1's own reduction was complete.
- My check of the thesis (Wimmer, Kap. I, (I.7), p. ~12; Kap. II, (II.1)): Table "Fuer n = 9"
  with column heads 3, 6/6, 7, 4/6 and "max" 2.00894, 2.00617, 1.98826, 2.04222; text: "Da ein
  9-eckiges Polyeder mit Volumen 2.04375 existiert, kann das fuer n = 9 optimale Polyeder weder
  eine Ecke vom Grad 3 noch eine Ecke vom Grad 7 besitzen"; this leaves "Nr. 32 und Nr. 33 der
  Brueckner'schen Liste"; Kap. II then excludes two non-adjacent "Doppelvierecke", concluding "Somit
  ist das fuer n = 9 optimale Polyeder vom Typ Nr. 33". Label of the reduction: THEOREM as claimed
  in the thesis; I did not audit how the tabulated maxima (2.00894 etc.) were obtained (rigorous
  bound vs. numerical maximisation), so their rigour is UNVERIFIED by me. Note Kap. III also writes
  "des fuer n = 9 vermutlich optimalen Polyeders" (the shape, not the type, was only conjectural).

### 1.3 Proof strategy for the class T (Section 4), no symmetry assumed
1. Existence: volume continuous on compact (S^2)^9; maximizer has exactly 9 vertices (else add a
   point outside the hull). THEOREM.
2. Oriented volume formula (Lemma 3.2, divergence theorem): 6 vol(P) = sum over outward-oriented
   facets of det(a,b,c); holds even if o not in P. THEOREM.
3. For T (9 vertices, 14 facets; degree-5 vertices x_i, y_i; degree-4 apices a_i augmenting the
   quadrilateral (x_i, x_{i+1}, y_{i+1}, y_i)): Lemma 4.2,
   6 vol = det(x1,x2,x3) - det(y1,y2,y3) - sum_i <a_i, W_i>, W_i = (x_i - y_{i+1}) x (x_{i+1} - y_i).
4. Cauchy-Schwarz eliminates the apices: -<a_i,W_i> <= ||W_i||, equality iff a_i = -W_i/||W_i||.
   Leaves a six-vector problem E(x,y) = D + sum ||W_i||.
5. Coordinates m_i=(x_i+y_i)/2, d_i=(x_i-y_i)/2 (<m_i,d_i>=0, |m_i|^2+|d_i|^2=1), means and centred
   parts, invariants U,R,V,S with U^2+R^2+V^2+S^2=3. Determinant difference bounded by
   V(R^2+S^2)+2URS via multilinearity, ||a x b|| <= ||a|| ||b||, Cauchy-Schwarz; sum ||W_i|| <=
   2 sqrt3 R sqrt(4V^2+S^2).
6. Completing squares reduces to G(R,T) = T R^2 + 4 sqrt3 R T + (8/3)(3-R^2-T^2) on the quarter disk
   R,T>=0, R^2+T^2<=3. Interior critical points: only nonpositive roots; axes give <=8; on the arc,
   phi(r)=3 sqrt3 (r^2+4r) sqrt(1-r^2), phi'=0 iff 3r^3+8r^2-2r-4=0 with roots -2/3, -1+-sqrt3; max
   phi(sqrt3-1)=18 sqrt(2 sqrt3-3) ~ 12.263.
7. Equality tracing forces U=S=0: m_i form a centred equilateral triangle in d^perp, d_i all equal;
   bases are parallel congruent equilateral triangles; apices a_i = (u_{i+1}-u_i) x n / sqrt3, an
   equilateral triangle on the equator offset by pi/3.
8. Combinatorial type of the extremal hull verified by explicit supporting linear functionals for
   all 14 facets (X, Y, A_i, B_i, C_i, D_i) plus Euler count f2 <= 14 for f0 = 9.
- No KKT/Lagrange multipliers on the sphere constraints, no case list of types inside T, no interval
  arithmetic, no algebraic elimination software. The only calculus is on the 2-variable G and the
  1-variable phi, done by hand. Searching the v2 source finds no use of computer, numerics,
  interval, Mathematica/Maple/Sage, or formal proof. Computer assistance: none in v2 (THEOREM-level
  hand proof). Formal verification: none (no FORMAL claim anywhere).
- Possible check point for a formaliser: Step 6 asserts G has a unique maximiser on the quarter disk
  and equality in each Cauchy-Schwarz step; the paper states but does not spell out every equality
  case of the chain (e.g. triangle inequality in Step 2). Not an error claim, just where to look.

### 1.4 Volume maximisation vs covering-radius minimisation
These are different problems: the volume functional is a sum of facet determinants (smooth, additive
over facets); the covering radius of N points is the maximum over Delaunay (= convex hull) facets of
the facet circumradius on S^2 (a minimax, nonsmooth), and the N=9 covering optimum need not have
the same combinatorics or coordinates. No theorem of this paper transfers to coverings.
Ingredients that could in principle be reused (techniques only):
- Compactness/existence argument and "exactly N distinct points" style reasoning.
- Euler counting for 3-polytopes (f1 = f2 + 7, f2 <= 14 for f0 = 9).
- Certifying the facet structure of an explicit configuration by supporting functionals
  (Step 8) - directly usable to certify the hull combinatorics of a candidate covering.
- The organising pattern "reduce to one combinatorial type, then optimise within the type".
- Exact algebraic coordinates (sqrt3 - 1, sqrt(2 sqrt3 - 3)) as a template for exact statements.
Ingredients that cannot transfer: the determinant volume formula and Lemma 4.2 decomposition;
the Cauchy-Schwarz apex elimination; the U,R,V,S / G(R,T) reduction (tailored to the volume of
type T); Wimmer's vertex-star volume bounds and Berman-Hanes local volume optimality conditions;
the identification of the maximiser.

## 2. Wimmer references in the bibliography
Only one Wimmer item is cited (bib key Wimmer1998); no other Wimmer works.
- L. Wimmer, "Das maximale Volumen der konvexen Huelle von Punkten auf der Einheitskugel",
  PhD thesis (Dissertation), Universitaet Salzburg, 1998. Bib note: "Chapter files available at
  http://lienhard-wimmer.com/source/stud/diss.html".
- Verified: that URL loads (page dated 2004-04-21): "DISSERTATION eingereicht von Mag. Lienhard
  Wimmer, Salzburg, 23. September 1998". Chapter PDFs (all HTTP 200, author-hosted):
  diss/einleit.pdf (Einleitung); kap_1.pdf "I. Flaeche und Eckensinus eines sphaerischen Dreiecks";
  kap_2.pdf "II. Das Doppelviereck"; kap_3.pdf "III. Die antiprismatische Doppelpyramide und weitere
  Polyedertypen"; kap_4.pdf "IV. Morphologie optimaler Polyeder"; kap_5.pdf "V. Numerische
  Methoden"; kap_6.pdf "VI. Numerische Resultate"; lit.pdf "Literatur".
  Base: http://lienhard-wimmer.com/source/stud/diss/ . Only Kap. I-III were text-searched.

## 3. Sloane coverings page
- Live https://neilsloane.com/coverings/index.html (and /coverings/, http variant, /coverings/dim3/,
  dim3/cover.3.9.txt): still HTTP 200 with an empty body (0 bytes) on 2026-11-28.
  Live content: UNVERIFIED (empty response).
- Internet Archive snapshot 2026-05-08
  (web.archive.org/web/20260508084025/https://neilsloane.com/coverings/index.html): "Spherical
  Coverings", R. H. Hardin, N. J. A. Sloane and W. D. Smith, "A library of putatively optimal
  coverings of the sphere with n equal caps", n = 4..130, "Last modified Oct 31 2015"; summary table
  "Copyright ... Feb 1994": "3 9 45.8788878" (covering radius in degrees). Label: NUMERICAL.
- Snapshot of dim3/ (2025-11-09): file "cover.3.9" (link cover.3.9.txt), "Found in 1994 by R. H.
  Hardin, N. J. A. Sloane & W. D. Smith", "contains the coords of the putatively optimal covering of
  sphere in 3 dimensions by 9 spherical caps". Reference given as Hardin-Sloane-Smith, "Spherical
  Codes, book in preparation".
- Archived cover.3.9.txt (snapshot 2023-11-19, 27 numbers, read as 9 points x 3 coords, one number
  per line; grouping by triples is my reading of the format):
  (-0.038754502311, -0.077654208988, 0.996226836927)
  (0.870293049142, 0.265505472198, 0.414845576510)
  (-0.012787828222, -0.637020409107, -0.770740856417)
  (-0.672691613436, -0.725550302304, 0.145130113699)
  (-0.576822615229, 0.344353577122, -0.740740361623)
  (0.057114495896, 0.992249669507, 0.110356360674)
  (-0.857505218126, 0.371514949948, 0.355895267799)
  (0.663511617109, 0.268252572045, -0.698421713896)
  (0.567642617971, -0.801651307382, 0.187448762357)
  Label: NUMERICAL ("putatively optimal"; no proof of optimality on the page). Other CDX captures
  exist (2013-06-05, 701 bytes; 2023-09-26, 827 bytes) with different sizes; I did not compare them,
  so whether the file content changed between captures is UNVERIFIED. No numerical check of the
  coordinates or radius was run (per instructions).
