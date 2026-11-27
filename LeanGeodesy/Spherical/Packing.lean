import LeanGeodesy.Geodesic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Spherical discrete geometry: codes, packings, coverings, and Rankin bounds

Foundations for discrete geometry on the unit sphere `S² ⊂ E3`, built directly
on `Geodesy.E3`, `Geodesy.sphere 1`, and `Geodesy.Geodesic`:

## Phase 1: Core definitions and algebraic equivalences
- `UnitSphere`: `{x : E3 // ‖x‖ = 1}` (the unit sphere `sphere 1`);
- `geoDist`, `chordDist`: great-circle (central-angle) distance and Euclidean
  chord distance, with exact equivalences to inner products:
  - `geoDist_eq_arccos_inner`, `cos_geoDist`, `chordDist_sq_eq`,
    `chordDist_eq_two_sin_half`;
  - `geoDist_ge_iff_inner_le`, `geoDist_ge_iff_chordDist_ge`;
- `openCap`, `closedCap`, `IsSphericalCode`, `IsSeparated`, `IsCovering`,
  `contactGraph`;
- `isSeparated_iff_pairwise_disjoint_openCap`: exact equivalence between
  `θ`-separated point configurations (Tammes problem) and pairwise disjoint
  open spherical caps of radius `θ / 2`;
- orthogonal isometry invariance (`LinearIsometryEquiv` preserves `inner`,
  `geoDist`, `chordDist`, `IsSphericalCode`, `IsSeparated`, and `IsCovering`).

## Phase 2: Classical optimality theorems
- `rankin_simplex_bound` / `isSeparated_simplex_bound`: Rankin's simplex bound
  for all `n ≥ 2` (`∃ i ≠ j, -1 / (n - 1) ≤ ⟪p i, p j⟫`);
- `rankin_orthoplex_bound_finrank` / `rankin_orthoplex_bound`: Rankin's
  dimension bound (`n > d + 1` nonzero vectors in a `d`-dimensional inner
  product space cannot all have strictly negative pairwise inner products, so
  on `S²` every `n ≥ 5` configuration has a pair at angle `≤ π / 2`);
- Exact Tammes optimality for `N = 2, 3, 4, 5, 6` (`tammes_2_optimal`,
  `tammes_3_optimal`, `tammes_4_optimal`, `tammes_5_optimal`,
  `tammes_6_optimal`), combining universal upper bounds over all configurations
  with explicit optimal witnesses.
-/

namespace Geodesy.Spherical

open Real InnerProductGeometry Geodesic

/-! ## Unit sphere, geodesic distance, chord distance, and inner products -/

/-- The unit sphere `S²` in `E3 = EuclideanSpace ℝ (Fin 3)`. -/
abbrev UnitSphere := {x : E3 // ‖x‖ = 1}

theorem mem_sphere_one_iff (x : E3) : x ∈ sphere 1 ↔ ‖x‖ = 1 := by
  simp [sphere]

/-- Great-circle (geodesic) distance on the unit sphere: the central angle. -/
noncomputable def geoDist (x y : UnitSphere) : ℝ :=
  angle x.1 y.1

/-- Euclidean chord distance in `E3` between two points of the unit sphere. -/
noncomputable def chordDist (x y : UnitSphere) : ℝ :=
  dist x.1 y.1

theorem geoDist_eq_arccos_inner (x y : UnitSphere) :
    geoDist x y = arccos (inner ℝ x.1 y.1) :=
  angle_eq_arccos_inner x.2 y.2

theorem cos_geoDist (x y : UnitSphere) :
    cos (geoDist x y) = inner ℝ x.1 y.1 := by
  rw [geoDist, cos_angle, x.2, y.2, mul_one, div_one]

theorem geoDist_nonneg (x y : UnitSphere) : 0 ≤ geoDist x y :=
  angle_nonneg x.1 y.1

theorem geoDist_le_pi (x y : UnitSphere) : geoDist x y ≤ π :=
  angle_le_pi x.1 y.1

theorem geoDist_comm (x y : UnitSphere) : geoDist x y = geoDist y x :=
  angle_comm x.1 y.1

theorem geoDist_self (x : UnitSphere) : geoDist x x = 0 := by
  rw [geoDist_eq_arccos_inner, inner_self_of_norm_one x.2, arccos_one]

theorem geoDist_triangle (x y z : UnitSphere) :
    geoDist x z ≤ geoDist x y + geoDist y z :=
  angle_le_angle_add_angle x.2 y.2 z.2

theorem inner_le_one (x y : UnitSphere) : inner ℝ x.1 y.1 ≤ 1 := by
  have h := abs_real_inner_le_norm x.1 y.1
  rw [x.2, y.2, mul_one] at h
  exact (abs_le.mp h).2

theorem neg_one_le_inner (x y : UnitSphere) : -1 ≤ inner ℝ x.1 y.1 := by
  have h := abs_real_inner_le_norm x.1 y.1
  rw [x.2, y.2, mul_one] at h
  exact (abs_le.mp h).1

theorem chordDist_sq_eq (x y : UnitSphere) :
    chordDist x y ^ 2 = 2 * (1 - inner ℝ x.1 y.1) := by
  rw [chordDist, dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_sub_right, inner_self_of_norm_one x.2, inner_self_of_norm_one y.2, real_inner_comm y.1 x.1]
  ring

theorem chordDist_eq_two_sin_half (x y : UnitSphere) :
    chordDist x y = 2 * sin (geoDist x y / 2) := by
  have hsq : chordDist x y ^ 2 = (2 * sin (geoDist x y / 2)) ^ 2 := by
    rw [chordDist_sq_eq, ← cos_geoDist]
    have h2 : cos (geoDist x y) = 1 - 2 * sin (geoDist x y / 2) ^ 2 := by
      have := cos_two_mul' (geoDist x y / 2)
      rw [show 2 * (geoDist x y / 2) = geoDist x y by ring] at this
      linarith [this, sin_sq_add_cos_sq (geoDist x y / 2)]
    linarith
  have hs : 0 ≤ sin (geoDist x y / 2) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith [geoDist_nonneg x y])
      (by linarith [geoDist_le_pi x y, pi_pos])
  have hch : 0 ≤ chordDist x y := dist_nonneg
  nlinarith

theorem geoDist_eq_zero_iff (x y : UnitSphere) : geoDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hch : chordDist x y = 0 := by
      rw [chordDist_eq_two_sin_half, h, zero_div, sin_zero, mul_zero]
    exact Subtype.ext (dist_eq_zero.mp hch)
  · rintro rfl
    exact geoDist_self x

/-- Geodesic separation `θ ≤ geoDist x y` is equivalent to the algebraic
inner-product bound `⟪x, y⟫ ≤ cos θ`. -/
theorem geoDist_ge_iff_inner_le {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) (x y : UnitSphere) :
    θ ≤ geoDist x y ↔ inner ℝ x.1 y.1 ≤ cos θ := by
  constructor
  · intro h
    rw [← cos_geoDist]
    exact antitoneOn_cos ⟨h0, hπ⟩ ⟨geoDist_nonneg x y, geoDist_le_pi x y⟩ h
  · intro h
    rw [geoDist_eq_arccos_inner, ← arccos_cos h0 hπ]
    exact arccos_le_arccos_of_le h

/-- Geodesic separation `θ ≤ geoDist x y` is equivalent to the chord-distance
bound `2 sin (θ / 2) ≤ chordDist x y`. -/
theorem geoDist_ge_iff_chordDist_ge {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) (x y : UnitSphere) :
    θ ≤ geoDist x y ↔ 2 * sin (θ / 2) ≤ chordDist x y := by
  rw [chordDist_eq_two_sin_half]
  constructor
  · intro h
    have hsin : sin (θ / 2) ≤ sin (geoDist x y / 2) :=
      strictMonoOn_sin.monotoneOn
        ⟨by linarith [pi_pos], by linarith⟩
        ⟨by linarith [geoDist_nonneg x y, pi_pos], by linarith [geoDist_le_pi x y]⟩
        (by linarith)
    linarith
  · intro h
    by_contra hlt
    push Not at hlt
    have hsin : sin (geoDist x y / 2) < sin (θ / 2) :=
      strictMonoOn_sin
        ⟨by linarith [geoDist_nonneg x y, pi_pos], by linarith [geoDist_le_pi x y]⟩
        ⟨by linarith [pi_pos], by linarith⟩
        (by linarith)
    linarith

/-! ## Spherical caps, codes, packings, coverings, and contact graphs -/

/-- Open spherical cap of geodesic radius `r` centred at `c`. -/
def openCap (c : UnitSphere) (r : ℝ) : Set UnitSphere :=
  {x | geoDist c x < r}

/-- Closed spherical cap of geodesic radius `r` centred at `c`. -/
def closedCap (c : UnitSphere) (r : ℝ) : Set UnitSphere :=
  {x | geoDist c x ≤ r}

/-- An `(n, t)`-spherical code: `n` unit vectors whose pairwise inner products
are at most `t`. -/
def IsSphericalCode {n : ℕ} (p : Fin n → UnitSphere) (t : ℝ) : Prop :=
  ∀ i j : Fin n, i ≠ j → inner ℝ (p i).1 (p j).1 ≤ t

/-- A `θ`-separated configuration on `S²` (Tammes admissibility). -/
def IsSeparated {n : ℕ} (p : Fin n → UnitSphere) (θ : ℝ) : Prop :=
  ∀ i j : Fin n, i ≠ j → θ ≤ geoDist (p i) (p j)

/-- A spherical covering of `S²` by `n` closed caps of radius `r`. -/
def IsCovering {n : ℕ} (p : Fin n → UnitSphere) (r : ℝ) : Prop :=
  ∀ x : UnitSphere, ∃ i : Fin n, x ∈ closedCap (p i) r

/-- The contact graph of a configuration at inner-product threshold `t`. -/
def contactGraph {n : ℕ} (p : Fin n → UnitSphere) (t : ℝ) (i j : Fin n) : Prop :=
  i ≠ j ∧ inner ℝ (p i).1 (p j).1 = t

theorem isSeparated_iff_isSphericalCode {n : ℕ} (p : Fin n → UnitSphere) {θ : ℝ}
    (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    IsSeparated p θ ↔ IsSphericalCode p (cos θ) := by
  simp only [IsSeparated, IsSphericalCode, geoDist_ge_iff_inner_le h0 hπ]

/-- Equivalence between the Tammes problem (`IsSeparated p θ`) and packing `n`
equal-radius open spherical caps of radius `θ / 2` on `S²`. -/
theorem isSeparated_iff_pairwise_disjoint_openCap {n : ℕ} (p : Fin n → UnitSphere) {θ : ℝ}
    (hπ : θ ≤ π) :
    IsSeparated p θ ↔ Pairwise fun i j => Disjoint (openCap (p i) (θ / 2)) (openCap (p j) (θ / 2)) := by
  constructor
  · intro hsep i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have htri := geoDist_triangle (p i) x (p j)
    rw [geoDist_comm x (p j)] at htri
    have hge := hsep i j hij
    have h1 : geoDist (p i) x < θ / 2 := hxi
    have h2 : geoDist (p j) x < θ / 2 := hxj
    linarith
  · intro hdisj i j hij
    by_contra hlt
    push Not at hlt
    have hθpos : 0 < θ := lt_of_le_of_lt (geoDist_nonneg _ _) hlt
    by_cases heq : p i = p j
    · have hmem : p i ∈ openCap (p i) (θ / 2) := by
        show geoDist (p i) (p i) < θ / 2
        rw [geoDist_self]
        linarith
      have hmem' : p i ∈ openCap (p j) (θ / 2) := by rwa [← heq]
      exact Set.disjoint_left.mp (hdisj hij) hmem hmem'
    · have hpos : 0 < geoDist (p i) (p j) :=
        lt_of_le_of_ne (geoDist_nonneg _ _) (Ne.symm fun h => heq ((geoDist_eq_zero_iff _ _).mp h))
      have hltπ : geoDist (p i) (p j) < π := lt_of_lt_of_le hlt hπ
      have hsin : 0 < sin (geoDist (p i) (p j)) := sin_pos_of_pos_of_lt_pi hpos hltπ
      let m : UnitSphere := ⟨greatArc (p i).1 (p j).1 (1 / 2), norm_greatArc (p i).2 (p j).2 hsin (1 / 2)⟩
      have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
      have h11 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
      have hm1 : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
      have hmi : geoDist (p i) m = geoDist (p i) (p j) / 2 := by
        have h := angle_greatArc (p i).2 (p j).2 hsin h01 hm1
        rw [greatArc_zero] at h
        change angle (p i).1 (greatArc (p i).1 (p j).1 (1 / 2)) = angle (p i).1 (p j).1 / 2
        rw [h]
        norm_num
        ring
      have hmj : geoDist (p j) m = geoDist (p i) (p j) / 2 := by
        have h := angle_greatArc (p i).2 (p j).2 hsin hm1 h11
        rw [greatArc_one (p i).2 (p j).2 hsin] at h
        change angle (p j).1 (greatArc (p i).1 (p j).1 (1 / 2)) = angle (p i).1 (p j).1 / 2
        rw [angle_comm, h]
        norm_num
        ring
      have hmem1 : m ∈ openCap (p i) (θ / 2) := by
        show geoDist (p i) m < θ / 2
        linarith
      have hmem2 : m ∈ openCap (p j) (θ / 2) := by
        show geoDist (p j) m < θ / 2
        linarith
      exact Set.disjoint_left.mp (hdisj hij) hmem1 hmem2

/-! ## Invariance under orthogonal isometries of `E3` -/

/-- Apply an orthogonal linear isometry `Q : E3 ≃ₗᵢ[ℝ] E3` to `UnitSphere`. -/
noncomputable def mapUnitSphere (Q : E3 ≃ₗᵢ[ℝ] E3) (x : UnitSphere) : UnitSphere :=
  ⟨Q x.1, by rw [Q.norm_map, x.2]⟩

theorem inner_mapUnitSphere (Q : E3 ≃ₗᵢ[ℝ] E3) (x y : UnitSphere) :
    inner ℝ (mapUnitSphere Q x).1 (mapUnitSphere Q y).1 = inner ℝ x.1 y.1 :=
  Q.inner_map_map x.1 y.1

theorem geoDist_mapUnitSphere (Q : E3 ≃ₗᵢ[ℝ] E3) (x y : UnitSphere) :
    geoDist (mapUnitSphere Q x) (mapUnitSphere Q y) = geoDist x y := by
  rw [geoDist_eq_arccos_inner, geoDist_eq_arccos_inner, inner_mapUnitSphere]

theorem chordDist_mapUnitSphere (Q : E3 ≃ₗᵢ[ℝ] E3) (x y : UnitSphere) :
    chordDist (mapUnitSphere Q x) (mapUnitSphere Q y) = chordDist x y :=
  Q.dist_map x.1 y.1

theorem isSeparated_mapUnitSphere {n : ℕ} (Q : E3 ≃ₗᵢ[ℝ] E3) (p : Fin n → UnitSphere) (θ : ℝ) :
    IsSeparated (fun i => mapUnitSphere Q (p i)) θ ↔ IsSeparated p θ := by
  simp only [IsSeparated, geoDist_mapUnitSphere]

theorem isCovering_mapUnitSphere {n : ℕ} (Q : E3 ≃ₗᵢ[ℝ] E3) (p : Fin n → UnitSphere) (r : ℝ) :
    IsCovering (fun i => mapUnitSphere Q (p i)) r ↔ IsCovering p r := by
  constructor
  · intro h x
    obtain ⟨i, hi⟩ := h (mapUnitSphere Q x)
    refine ⟨i, ?_⟩
    simpa only [closedCap, Set.mem_ofPred_eq, geoDist_mapUnitSphere] using hi
  · intro h x
    obtain ⟨i, hi⟩ := h (mapUnitSphere Q.symm x)
    refine ⟨i, ?_⟩
    have hsym : mapUnitSphere Q (mapUnitSphere Q.symm x) = x := Subtype.ext (Q.apply_symm_apply x.1)
    have hdist : geoDist (mapUnitSphere Q (p i)) x = geoDist (p i) (mapUnitSphere Q.symm x) := by
      conv_lhs => rw [← hsym]
      exact geoDist_mapUnitSphere Q (p i) (mapUnitSphere Q.symm x)
    simpa only [closedCap, Set.mem_ofPred_eq, hdist] using hi

/-! ## Rankin's simplex bound -/

/-- Rankin's simplex bound: among any `n ≥ 2` unit vectors on `S²`, some distinct
pair has inner product at least `-1 / (n - 1)`. -/
theorem rankin_simplex_bound {n : ℕ} (hn : 2 ≤ n) (p : Fin n → UnitSphere) :
    ∃ i j : Fin n, i ≠ j ∧ -1 / ((n : ℝ) - 1) ≤ inner ℝ (p i).1 (p j).1 := by
  by_contra h
  push Not at h
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnorm : 0 ≤ ‖∑ i : Fin n, (p i).1‖ ^ 2 := sq_nonneg _
  have hexpand : ‖∑ i : Fin n, (p i).1‖ ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, inner ℝ (p i).1 (p j).1 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
  have hrow : ∀ i : Fin n, ∑ j : Fin n, inner ℝ (p i).1 (p j).1 < 0 := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), inner_self_of_norm_one (p i).2]
    have hne : (Finset.univ.erase i).Nonempty := by
      have hcard : 1 ≤ (Finset.univ.erase i).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
        omega
      exact Finset.card_pos.mp (by omega)
    have hlt : ∑ j ∈ Finset.univ.erase i, inner ℝ (p i).1 (p j).1 <
        ∑ _j ∈ Finset.univ.erase i, (-1 / ((n : ℝ) - 1)) := by
      refine Finset.sum_lt_sum_of_nonempty hne fun j hj => ?_
      exact h i j (Finset.ne_of_mem_erase hj).symm
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hlt
    have hcancel : ((n : ℝ) - 1) * (-1 / ((n : ℝ) - 1)) = -1 := by
      field_simp [hn1.ne']
    linarith
  have htotal : ∑ i : Fin n, ∑ j : Fin n, inner ℝ (p i).1 (p j).1 < 0 := by
    have huniv : (Finset.univ : Finset (Fin n)).Nonempty := by
      rw [Finset.univ_nonempty_iff]
      exact ⟨⟨0, by omega⟩⟩
    simpa using Finset.sum_lt_sum_of_nonempty huniv (fun i _ => hrow i)
  linarith

theorem isSphericalCode_simplex_bound {n : ℕ} (hn : 2 ≤ n) {p : Fin n → UnitSphere} {t : ℝ}
    (h : IsSphericalCode p t) :
    -1 / ((n : ℝ) - 1) ≤ t := by
  obtain ⟨i, j, hij, hge⟩ := rankin_simplex_bound hn p
  exact hge.trans (h i j hij)

theorem isSeparated_simplex_bound {n : ℕ} (hn : 2 ≤ n) {p : Fin n → UnitSphere} {θ : ℝ}
    (h : IsSeparated p θ) :
    θ ≤ arccos (-1 / ((n : ℝ) - 1)) := by
  obtain ⟨i, j, hij, hge⟩ := rankin_simplex_bound hn p
  calc θ ≤ geoDist (p i) (p j) := h i j hij
    _ = arccos (inner ℝ (p i).1 (p j).1) := geoDist_eq_arccos_inner (p i) (p j)
    _ ≤ arccos (-1 / ((n : ℝ) - 1)) := arccos_le_arccos_of_le hge

/-! ## Rankin's orthoplex (dimension) bound -/

/-- Rankin's acute-angle / orthoplex lemma in any finite-dimensional real inner
product space: `n > d + 1` nonzero vectors in a space of dimension `≤ d`
cannot have all pairwise inner products strictly negative. -/
theorem rankin_orthoplex_bound_finrank :
    ∀ (d : ℕ) {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V],
      Module.finrank ℝ V ≤ d →
      ∀ {n : ℕ}, d + 1 < n →
      ∀ (v : Fin n → V), (∀ i, v i ≠ 0) →
      ∃ i j : Fin n, i ≠ j ∧ 0 ≤ inner ℝ (v i) (v j)
  | 0, V, _, _, _, hdim, n, hn, v, hv => by
    have h0 : Module.finrank ℝ V = 0 := Nat.eq_zero_of_le_zero hdim
    have hsub : Subsingleton V := Module.finrank_zero_iff.mp h0
    exact absurd (Subsingleton.elim (v ⟨0, by omega⟩) 0) (hv ⟨0, by omega⟩)
  | d + 1, V, _, _, _, hdim, n, hn, v, hv => by
    by_contra hneg
    push Not at hneg
    let i0 : Fin n := ⟨0, by omega⟩
    let u : V := (‖v i0‖)⁻¹ • v i0
    have hu_norm : ‖u‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (norm_pos_iff.mpr (hv i0)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hv i0))]
    have hu_ne : u ≠ 0 := fun h => by rw [h, norm_zero] at hu_norm; norm_num at hu_norm
    have huu : (inner ℝ u u : ℝ) = 1 := inner_self_of_norm_one hu_norm
    let S : Submodule ℝ V := (Submodule.span ℝ {u})ᗮ
    have hfinS : Module.finrank ℝ S ≤ d := by
      have hadd := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {u})
      have hspan : Module.finrank ℝ (Submodule.span ℝ {u}) = 1 := finrank_span_singleton hu_ne
      dsimp only [S]
      omega
    have hm : d + 1 < n - 1 := by omega
    let idx : Fin (n - 1) → Fin n := fun k => ⟨k.1 + 1, by omega⟩
    have hidx_ne0 : ∀ k : Fin (n - 1), idx k ≠ i0 := fun k h => by
      have := congrArg Fin.val h
      simp only [idx, i0] at this
      omega
    have hidx_inj : Function.Injective idx := fun a b h => by
      apply Fin.ext
      have := congrArg Fin.val h
      simp only [idx] at this
      omega
    have hinner_u : ∀ k : Fin (n - 1), inner ℝ (v (idx k)) u < 0 := by
      intro k
      rw [real_inner_smul_right]
      exact mul_neg_of_pos_of_neg (inv_pos.mpr (norm_pos_iff.mpr (hv i0)))
        (hneg (idx k) i0 (hidx_ne0 k))
    let w : Fin (n - 1) → S := fun k =>
      ⟨v (idx k) - (inner ℝ (v (idx k)) u : ℝ) • u, by
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
        rw [inner_sub_right, real_inner_smul_right, huu, mul_one, real_inner_comm, sub_self]⟩
    have hw_ne : ∀ k : Fin (n - 1), w k ≠ 0 := by
      intro k hwk
      have hv_eq : v (idx k) = (inner ℝ (v (idx k)) u : ℝ) • u :=
        sub_eq_zero.mp (congrArg Subtype.val hwk)
      let k' : Fin (n - 1) := if k.1 = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hkk' : k' ≠ k := by
        intro h
        have hv' := congrArg Fin.val h
        by_cases hk0 : k.1 = 0
        · simp only [k', hk0, ↓reduceIte] at hv'
          omega
        · simp only [k', hk0, ↓reduceIte] at hv'
          exact hk0 hv'.symm
      have hpos : 0 < inner ℝ (v (idx k')) (v (idx k)) := by
        rw [hv_eq, real_inner_smul_right]
        exact mul_pos_of_neg_of_neg (hinner_u k) (hinner_u k')
      exact not_lt_of_ge hpos.le (hneg (idx k') (idx k) (fun e => hkk' (hidx_inj e)))
    obtain ⟨a, b, hab, hge⟩ := rankin_orthoplex_bound_finrank d hfinS hm w hw_ne
    have hwij : (inner ℝ (w a) (w b) : ℝ) =
        inner ℝ (v (idx a)) (v (idx b)) -
          inner ℝ (v (idx a)) u * inner ℝ (v (idx b)) u := by
      have haux : ∀ (u' x y : V), inner ℝ u' u' = 1 →
          inner ℝ (x - (inner ℝ x u' : ℝ) • u') (y - (inner ℝ y u' : ℝ) • u') =
            inner ℝ x y - inner ℝ x u' * inner ℝ y u' := by
        intro u' x y hu'
        rw [inner_sub_left, inner_sub_right, inner_sub_right,
          real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
          hu', real_inner_comm u' y]
        ring
      exact haux u (v (idx a)) (v (idx b)) huu
    have hprod : 0 < inner ℝ (v (idx a)) u * inner ℝ (v (idx b)) u :=
      mul_pos_of_neg_of_neg (hinner_u a) (hinner_u b)
    have hlt : inner ℝ (v (idx a)) (v (idx b)) < 0 :=
      hneg (idx a) (idx b) (fun e => hab (hidx_inj e))
    linarith

/-- On `S²` (`dim E3 = 3`), every configuration of `n ≥ 5` points has a distinct
pair with nonnegative inner product (geodesic angle `≤ π / 2`). -/
theorem rankin_orthoplex_bound {n : ℕ} (hn : 5 ≤ n) (p : Fin n → UnitSphere) :
    ∃ i j : Fin n, i ≠ j ∧ 0 ≤ inner ℝ (p i).1 (p j).1 := by
  have hdim : Module.finrank ℝ E3 ≤ 3 := by
    rw [finrank_euclideanSpace_fin]
  have hne : ∀ i : Fin n, (p i).1 ≠ 0 := fun i h => by
    have := (p i).2
    rw [h, norm_zero] at this
    norm_num at this
  exact rankin_orthoplex_bound_finrank 3 hdim (by omega) (fun i => (p i).1) hne

theorem isSeparated_orthoplex_bound {n : ℕ} (hn : 5 ≤ n) {p : Fin n → UnitSphere} {θ : ℝ}
    (h : IsSeparated p θ) :
    θ ≤ π / 2 := by
  obtain ⟨i, j, hij, hge⟩ := rankin_orthoplex_bound hn p
  calc θ ≤ geoDist (p i) (p j) := h i j hij
    _ = arccos (inner ℝ (p i).1 (p j).1) := geoDist_eq_arccos_inner (p i) (p j)
    _ ≤ arccos 0 := arccos_le_arccos_of_le hge
    _ = π / 2 := arccos_zero

/-! ## Exact Tammes optimality for N = 2, 3, 4, 5, 6 -/

private theorem unit_vec3 {x y z : ℝ} (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : ‖vec3 x y z‖ = 1 := by
  have hsq : ‖vec3 x y z‖ ^ 2 = 1 := by rw [norm_vec3_sq, h]
  nlinarith [norm_nonneg (vec3 x y z)]

/-- Optimal 2-point configuration: north and south poles (angle `π`). -/
noncomputable def poles2 : Fin 2 → UnitSphere
  | ⟨0, _⟩ => ⟨vec3 0 0 1, unit_vec3 (by norm_num)⟩
  | ⟨1, _⟩ => ⟨vec3 0 0 (-1), unit_vec3 (by norm_num)⟩

theorem tammes_2_optimal (θ : ℝ) :
    (∃ p : Fin 2 → UnitSphere, IsSeparated p θ) ↔ θ ≤ π := by
  constructor
  · rintro ⟨p, hp⟩
    exact (hp 0 1 (by decide)).trans (geoDist_le_pi _ _)
  · intro hθ
    refine ⟨poles2, fun i j hij => ?_⟩
    have hinner : inner ℝ (poles2 i).1 (poles2 j).1 = -1 := by
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | (simp only [poles2, inner_vec3]; norm_num)
    rw [geoDist_eq_arccos_inner, hinner, arccos_neg_one]
    exact hθ

/-- Optimal 3-point configuration: equilateral triangle on the equator
(angle `2π / 3`). -/
noncomputable def eqTriangle3 : Fin 3 → UnitSphere
  | ⟨0, _⟩ => ⟨vec3 1 0 0, unit_vec3 (by norm_num)⟩
  | ⟨1, _⟩ => ⟨vec3 (-1 / 2) (√3 / 2) 0, unit_vec3 (by
      have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
      linear_combination (1 / 4 : ℝ) * h3)⟩
  | ⟨2, _⟩ => ⟨vec3 (-1 / 2) (-(√3 / 2)) 0, unit_vec3 (by
      have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
      linear_combination (1 / 4 : ℝ) * h3)⟩

theorem tammes_3_optimal (θ : ℝ) :
    (∃ p : Fin 3 → UnitSphere, IsSeparated p θ) ↔ θ ≤ 2 * π / 3 := by
  have harc : arccos (-1 / 2 : ℝ) = 2 * π / 3 := by
    rw [show (-1 / 2 : ℝ) = cos (2 * π / 3) by
      rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]; ring]
    exact arccos_cos (by linarith [pi_pos]) (by linarith [pi_pos])
  constructor
  · rintro ⟨p, hp⟩
    have h := isSeparated_simplex_bound (by norm_num : 2 ≤ 3) hp
    norm_num at h
    linarith [h, harc]
  · intro hθ
    refine ⟨eqTriangle3, fun i j hij => ?_⟩
    have hinner : inner ℝ (eqTriangle3 i).1 (eqTriangle3 j).1 = -1 / 2 := by
      have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | (simp only [eqTriangle3, inner_vec3]; linear_combination -(1 / 4 : ℝ) * h3)
        | (simp only [eqTriangle3, inner_vec3]; ring)
    rw [geoDist_eq_arccos_inner, hinner, harc]
    exact hθ

/-- Optimal 4-point configuration: regular tetrahedron (angle `arccos (-1/3)`). -/
noncomputable def tetrahedron4 : Fin 4 → UnitSphere
  | ⟨0, _⟩ => ⟨vec3 (1 / √3) (1 / √3) (1 / √3), unit_vec3 (by
      have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
      field_simp; linarith)⟩
  | ⟨1, _⟩ => ⟨vec3 (1 / √3) (-(1 / √3)) (-(1 / √3)), unit_vec3 (by
      have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
      field_simp; linarith)⟩
  | ⟨2, _⟩ => ⟨vec3 (-(1 / √3)) (1 / √3) (-(1 / √3)), unit_vec3 (by
      have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
      field_simp; linarith)⟩
  | ⟨3, _⟩ => ⟨vec3 (-(1 / √3)) (-(1 / √3)) (1 / √3), unit_vec3 (by
      have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
      field_simp; linarith)⟩

theorem tammes_4_optimal (θ : ℝ) :
    (∃ p : Fin 4 → UnitSphere, IsSeparated p θ) ↔ θ ≤ arccos (-1 / 3) := by
  constructor
  · rintro ⟨p, hp⟩
    have h := isSeparated_simplex_bound (by norm_num : 2 ≤ 4) hp
    norm_num at h
    simpa [neg_div] using h
  · intro hθ
    refine ⟨tetrahedron4, fun i j hij => ?_⟩
    have hinner : inner ℝ (tetrahedron4 i).1 (tetrahedron4 j).1 = -1 / 3 := by
      have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
      have h3ne : √3 ≠ 0 := (sqrt_pos.mpr (by norm_num)).ne'
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | (simp only [tetrahedron4, inner_vec3]; field_simp; linarith)
    rw [geoDist_eq_arccos_inner, hinner]
    exact hθ

/-- Optimal 6-point configuration: regular octahedron `±e₁, ±e₂, ±e₃`
(minimum angle `π / 2`). -/
noncomputable def octahedron6 : Fin 6 → UnitSphere
  | ⟨0, _⟩ => ⟨vec3 1 0 0, unit_vec3 (by norm_num)⟩
  | ⟨1, _⟩ => ⟨vec3 (-1) 0 0, unit_vec3 (by norm_num)⟩
  | ⟨2, _⟩ => ⟨vec3 0 1 0, unit_vec3 (by norm_num)⟩
  | ⟨3, _⟩ => ⟨vec3 0 (-1) 0, unit_vec3 (by norm_num)⟩
  | ⟨4, _⟩ => ⟨vec3 0 0 1, unit_vec3 (by norm_num)⟩
  | ⟨5, _⟩ => ⟨vec3 0 0 (-1), unit_vec3 (by norm_num)⟩

private theorem octahedron6_inner_le_zero {i j : Fin 6} (hij : i ≠ j) :
    inner ℝ (octahedron6 i).1 (octahedron6 j).1 ≤ 0 := by
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | (simp only [octahedron6, inner_vec3]; norm_num)

theorem tammes_6_optimal (θ : ℝ) :
    (∃ p : Fin 6 → UnitSphere, IsSeparated p θ) ↔ θ ≤ π / 2 := by
  constructor
  · rintro ⟨p, hp⟩
    exact isSeparated_orthoplex_bound (by norm_num : 5 ≤ 6) hp
  · intro hθ
    refine ⟨octahedron6, fun i j hij => ?_⟩
    calc θ ≤ π / 2 := hθ
      _ = arccos 0 := arccos_zero.symm
      _ ≤ arccos (inner ℝ (octahedron6 i).1 (octahedron6 j).1) :=
          arccos_le_arccos_of_le (octahedron6_inner_le_zero hij)
      _ = geoDist (octahedron6 i) (octahedron6 j) := (geoDist_eq_arccos_inner _ _).symm

/-- Exact Tammes optimality for `N = 5`: also `π / 2`, attained by deleting one
vertex of the regular octahedron. -/
theorem tammes_5_optimal (θ : ℝ) :
    (∃ p : Fin 5 → UnitSphere, IsSeparated p θ) ↔ θ ≤ π / 2 := by
  constructor
  · rintro ⟨p, hp⟩
    exact isSeparated_orthoplex_bound (by norm_num : 5 ≤ 5) hp
  · intro hθ
    refine ⟨fun i => octahedron6 i.castSucc, fun i j hij => ?_⟩
    have hne : i.castSucc ≠ j.castSucc := (Fin.castSucc_injective 5).ne hij
    calc θ ≤ π / 2 := hθ
      _ = arccos 0 := arccos_zero.symm
      _ ≤ arccos (inner ℝ (octahedron6 i.castSucc).1 (octahedron6 j.castSucc).1) :=
          arccos_le_arccos_of_le (octahedron6_inner_le_zero hne)
      _ = geoDist (octahedron6 i.castSucc) (octahedron6 j.castSucc) :=
          (geoDist_eq_arccos_inner _ _).symm

end Geodesy.Spherical
