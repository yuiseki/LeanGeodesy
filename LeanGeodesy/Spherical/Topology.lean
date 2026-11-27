import LeanGeodesy.Spherical.Packing
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Topology of `UnitSphere` and existence of optimal packings and coverings

This module supplies the topological foundations for extremal problems on `S²`:

- `isCompact_unitSphere` / `CompactSpace UnitSphere`: the unit sphere in `E3`
  is compact;
- `continuous_geoDist`, `continuous_chordDist`: continuity of geodesic and
  chordal distances;
- `geoDist_topology_equiv_chordDist`: the geodesic balls and chordal balls
  induce the exact same topology on `UnitSphere` (in fact `chordDist x y ≤ geoDist x y`
  and `geoDist x y ≤ (π / 2) * chordDist x y`, giving bi-Lipschitz equivalence);
- `minGeoDist`, `exists_optimal_packing`: for every `n ≥ 2`, there exists an
  `n`-point configuration on `S²` maximizing the minimum pairwise geodesic
  distance;
- `coveringRadius`, `exists_optimal_covering`: for every `n ≥ 1`, there exists
  an `n`-point configuration on `S²` minimizing the covering radius.
-/

namespace Geodesy.Spherical

open Real Topology

/-! ## Compactness and continuity -/

/-- `sphere 1` is compact in `E3`. -/
theorem isCompact_sphere_one : IsCompact (sphere 1) :=
  isCompact_sphere (0 : E3) 1

/-- `UnitSphere` is a compact topological space. -/
instance : CompactSpace UnitSphere := by
  have h : IsCompact {x : E3 | ‖x‖ = 1} := by
    convert isCompact_sphere_one using 1
    ext x
    exact (mem_sphere_one_iff x).symm
  exact isCompact_iff_compactSpace.mp h

/-- `UnitSphere` is nonempty (contains the north pole). -/
instance : Nonempty UnitSphere :=
  ⟨poles2 0⟩

theorem continuous_chordDist : Continuous fun p : UnitSphere × UnitSphere => chordDist p.1 p.2 :=
  continuous_dist.comp (continuous_subtype_val.prodMap continuous_subtype_val)

theorem continuous_geoDist : Continuous fun p : UnitSphere × UnitSphere => geoDist p.1 p.2 := by
  have heq : (fun p : UnitSphere × UnitSphere => geoDist p.1 p.2) =
      fun p => arccos (inner ℝ p.1.1 p.2.1) := by
    ext p
    exact geoDist_eq_arccos_inner p.1 p.2
  rw [heq]
  exact continuous_arccos.comp
    (continuous_inner.comp (continuous_subtype_val.prodMap continuous_subtype_val))

/-! ## Bi-Lipschitz and topological equivalence of `chordDist` and `geoDist` -/

/-- Chordal distance is at most geodesic distance: `‖x - y‖ ≤ θ`. -/
theorem chordDist_le_geoDist (x y : UnitSphere) : chordDist x y ≤ geoDist x y := by
  rw [chordDist_eq_two_sin_half]
  have hsin : sin (geoDist x y / 2) ≤ geoDist x y / 2 :=
    sin_le (by linarith [geoDist_nonneg x y])
  linarith

/-- Geodesic distance is at most `(π / 2)` times chordal distance:
`θ ≤ (π / 2) * ‖x - y‖`. -/
theorem geoDist_le_pi_div_two_mul_chordDist (x y : UnitSphere) :
    geoDist x y ≤ (π / 2) * chordDist x y := by
  rw [chordDist_eq_two_sin_half]
  have hsin : (2 / π) * (geoDist x y / 2) ≤ sin (geoDist x y / 2) :=
    mul_le_sin (by linarith [geoDist_nonneg x y]) (by linarith [geoDist_le_pi x y])
  have hpi : 0 < π := pi_pos
  have h1 : geoDist x y / π ≤ sin (geoDist x y / 2) := by
    have : (2 / π) * (geoDist x y / 2) = geoDist x y / π := by ring
    linarith
  have h2 : geoDist x y ≤ sin (geoDist x y / 2) * π := (div_le_iff₀ hpi).mp h1
  linarith

/-- The geodesic and chordal metrics induce the exact same neighborhood bases
(and hence the exact same topology) on `UnitSphere`. -/
theorem geoDist_topology_equiv_chordDist (x : UnitSphere) (s : Set UnitSphere) :
    (∃ ε > 0, {y | geoDist x y < ε} ⊆ s) ↔ (∃ δ > 0, {y | chordDist x y < δ} ⊆ s) := by
  constructor
  · rintro ⟨ε, hε, hs⟩
    refine ⟨(2 / π) * ε, by positivity, fun y hy => hs ?_⟩
    show geoDist x y < ε
    have hle := geoDist_le_pi_div_two_mul_chordDist x y
    have hy' : chordDist x y < (2 / π) * ε := hy
    have hpi : π ≠ 0 := pi_pos.ne'
    have hmul : (π / 2) * chordDist x y < (π / 2) * ((2 / π) * ε) :=
      mul_lt_mul_of_pos_left hy' (by positivity)
    have hcancel : (π / 2) * ((2 / π) * ε) = ε := by field_simp
    linarith
  · rintro ⟨δ, hδ, hs⟩
    exact ⟨δ, hδ, fun y hy => hs (lt_of_le_of_lt (chordDist_le_geoDist x y) hy)⟩

/-! ## Existence of optimal packing and covering configurations -/

private theorem continuous_finset_inf' {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → X → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous fun x => s.inf' hs fun i => f i x := by
  induction s using Finset.cons_induction with
  | empty => simp at hs
  | cons a s ha ih =>
    by_cases hs' : s.Nonempty
    · have heq : (fun x => (Finset.cons a s ha).inf' hs fun i => f i x) =
          fun x => min (f a x) (s.inf' hs' fun i => f i x) := by
        ext x
        exact Finset.inf'_cons (f := fun i => f i x) hs'
      rw [heq]
      exact (hf a (Finset.mem_cons_self a s)).min
        (ih hs' fun i hi => hf i (Finset.mem_cons_of_mem hi))
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hs'
      simpa using hf a (Finset.mem_cons_self a ∅)

/-- The distinct pairs of indices in `Fin n`. -/
def offDiagPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ij => ij.1 ≠ ij.2

theorem offDiagPairs_nonempty {n : ℕ} (hn : 2 ≤ n) : (offDiagPairs n).Nonempty := by
  refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
  simp [offDiagPairs]

/-- Minimum pairwise geodesic distance of an `n`-point configuration (`n ≥ 2`). -/
noncomputable def minGeoDist {n : ℕ} (hn : 2 ≤ n) (p : Fin n → UnitSphere) : ℝ :=
  (offDiagPairs n).inf' (offDiagPairs_nonempty hn) fun ij => geoDist (p ij.1) (p ij.2)

theorem isSeparated_minGeoDist {n : ℕ} (hn : 2 ≤ n) (p : Fin n → UnitSphere) :
    IsSeparated p (minGeoDist hn p) := by
  intro i j hij
  unfold minGeoDist
  exact Finset.inf'_le (s := offDiagPairs n) (f := fun ij : Fin n × Fin n => geoDist (p ij.1) (p ij.2))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hij⟩)

theorem le_minGeoDist_iff {n : ℕ} (hn : 2 ≤ n) (p : Fin n → UnitSphere) (θ : ℝ) :
    θ ≤ minGeoDist hn p ↔ IsSeparated p θ := by
  constructor
  · intro h i j hij
    exact h.trans (isSeparated_minGeoDist hn p i j hij)
  · intro h
    refine Finset.le_inf' _ _ fun ij hij => ?_
    exact h ij.1 ij.2 (Finset.mem_filter.mp hij).2

private theorem continuous_geoDist_comp {X : Type*} [TopologicalSpace X] {f g : X → UnitSphere}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => geoDist (f x) (g x) := by
  have heq : (fun x => geoDist (f x) (g x)) = fun x => arccos (inner ℝ (f x).1 (g x).1) := by
    ext x
    exact geoDist_eq_arccos_inner (f x) (g x)
  rw [heq]
  exact continuous_arccos.comp
    ((continuous_subtype_val.comp hf).inner (continuous_subtype_val.comp hg))

theorem continuous_minGeoDist {n : ℕ} (hn : 2 ≤ n) :
    Continuous (minGeoDist hn) := by
  unfold minGeoDist
  refine continuous_finset_inf' (X := Fin n → UnitSphere) (offDiagPairs n) (offDiagPairs_nonempty hn)
    (fun ij p => geoDist (p ij.1) (p ij.2)) fun ij _ => ?_
  exact continuous_geoDist_comp (continuous_apply ij.1) (continuous_apply ij.2)

/-- Existence of an optimal Tammes (packing) configuration on `S²` for every `n ≥ 2`. -/
theorem exists_optimal_packing {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : Fin n → UnitSphere, ∀ q : Fin n → UnitSphere, minGeoDist hn q ≤ minGeoDist hn p := by
  have hcomp : IsCompact (Set.univ : Set (Fin n → UnitSphere)) := isCompact_univ
  have hne : (Set.univ : Set (Fin n → UnitSphere)).Nonempty := Set.univ_nonempty
  obtain ⟨p, -, hp⟩ := hcomp.exists_isMaxOn hne (continuous_minGeoDist hn).continuousOn
  exact ⟨p, fun q => hp (Set.mem_univ q)⟩

/-- Distance from a point `x ∈ S²` to the nearest point of a configuration `p` (`n ≥ 1`). -/
noncomputable def distToConfig {n : ℕ} (hn : 1 ≤ n) (p : Fin n → UnitSphere) (x : UnitSphere) : ℝ :=
  Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩) fun i => geoDist (p i) x

theorem continuous_distToConfig {n : ℕ} (hn : 1 ≤ n) :
    Continuous fun px : (Fin n → UnitSphere) × UnitSphere => distToConfig hn px.1 px.2 := by
  unfold distToConfig
  refine continuous_finset_inf' (X := (Fin n → UnitSphere) × UnitSphere) Finset.univ _
    (fun i px => geoDist (px.1 i) px.2) fun i _ => ?_
  exact continuous_geoDist_comp ((continuous_apply i).comp continuous_fst) continuous_snd

/-- Covering radius of an `n`-point configuration on `S²` (`n ≥ 1`):
`sup_{x ∈ S²} min_i geoDist (p i) x`. -/
noncomputable def coveringRadius {n : ℕ} (hn : 1 ≤ n) (p : Fin n → UnitSphere) : ℝ :=
  sSup (Set.range (distToConfig hn p))

theorem distToConfig_le_coveringRadius {n : ℕ} (hn : 1 ≤ n) (p : Fin n → UnitSphere)
    (x : UnitSphere) :
    distToConfig hn p x ≤ coveringRadius hn p := by
  have hbdd : BddAbove (Set.range (distToConfig hn p)) := by
    refine ⟨π, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact (Finset.inf'_le (f := fun i : Fin n => geoDist (p i) y)
      (Finset.mem_univ (⟨0, by omega⟩ : Fin n))).trans (geoDist_le_pi _ _)
  exact le_csSup hbdd ⟨x, rfl⟩

theorem isCovering_coveringRadius {n : ℕ} (hn : 1 ≤ n) (p : Fin n → UnitSphere) :
    IsCovering p (coveringRadius hn p) := by
  intro x
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩) (fun i : Fin n => geoDist (p i) x)
  refine ⟨i, ?_⟩
  show geoDist (p i) x ≤ coveringRadius hn p
  rw [← hi]
  exact distToConfig_le_coveringRadius hn p x

theorem coveringRadius_le_iff {n : ℕ} (hn : 1 ≤ n) (p : Fin n → UnitSphere) (r : ℝ) :
    coveringRadius hn p ≤ r ↔ IsCovering p r := by
  constructor
  · intro h x
    obtain ⟨i, hi⟩ := isCovering_coveringRadius hn p x
    exact ⟨i, le_trans hi h⟩
  · intro h
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := h x
    exact (Finset.inf'_le (f := fun j : Fin n => geoDist (p j) x) (Finset.mem_univ i)).trans hi

theorem continuous_coveringRadius {n : ℕ} (hn : 1 ≤ n) :
    Continuous (coveringRadius hn) := by
  rw [Metric.continuous_iff]
  intro p ε hε
  -- By compactness of `UnitSphere`, `distToConfig` is uniformly close in `p` uniformly over `x`.
  have hlip : ∀ q : Fin n → UnitSphere, ∀ x : UnitSphere,
      |distToConfig hn q x - distToConfig hn p x| ≤
        (π / 2) * dist q p := by
    intro q x
    have hstep : ∀ (a b : Fin n → UnitSphere),
        distToConfig hn a x ≤ distToConfig hn b x + (π / 2) * dist a b := by
      intro a b
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩) (fun j : Fin n => geoDist (b j) x)
      calc distToConfig hn a x ≤ geoDist (a i) x :=
            Finset.inf'_le (f := fun j : Fin n => geoDist (a j) x) (Finset.mem_univ i)
        _ ≤ geoDist (a i) (b i) + geoDist (b i) x := geoDist_triangle (a i) (b i) x
        _ = geoDist (a i) (b i) + distToConfig hn b x := by rw [← hi]; rfl
        _ ≤ (π / 2) * chordDist (a i) (b i) + distToConfig hn b x := by
            linarith [geoDist_le_pi_div_two_mul_chordDist (a i) (b i)]
        _ ≤ (π / 2) * dist a b + distToConfig hn b x := by
            have hd : chordDist (a i) (b i) ≤ dist a b := dist_le_pi_dist a b i
            nlinarith [pi_pos]
        _ = distToConfig hn b x + (π / 2) * dist a b := by ring
    have hpq := hstep p q
    rw [dist_comm] at hpq
    rw [abs_le]
    exact ⟨by linarith, by linarith [hstep q p]⟩
  refine ⟨ε / π, by positivity, fun q hq => ?_⟩
  have h1 : coveringRadius hn q ≤ coveringRadius hn p + (π / 2) * dist q p := by
    rw [coveringRadius_le_iff]
    intro x
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf'
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩) (fun j : Fin n => geoDist (q j) x)
    refine ⟨i, ?_⟩
    show geoDist (q i) x ≤ coveringRadius hn p + (π / 2) * dist q p
    have hi' : geoDist (q i) x = distToConfig hn q x := hi.symm
    rw [hi']
    have h := (abs_le.mp (hlip q x)).2
    linarith [distToConfig_le_coveringRadius hn p x]
  have h2 : coveringRadius hn p ≤ coveringRadius hn q + (π / 2) * dist q p := by
    rw [coveringRadius_le_iff]
    intro x
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf'
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩) (fun j : Fin n => geoDist (p j) x)
    refine ⟨i, ?_⟩
    show geoDist (p i) x ≤ coveringRadius hn q + (π / 2) * dist q p
    have hi' : geoDist (p i) x = distToConfig hn p x := hi.symm
    rw [hi']
    have h := (abs_le.mp (hlip q x)).1
    linarith [distToConfig_le_coveringRadius hn q x]
  rw [Real.dist_eq, abs_lt]
  have hmul : (π / 2) * dist q p < ε / 2 := by
    have hpi : 0 < π := pi_pos
    have : (π / 2) * (ε / π) = ε / 2 := by field_simp
    nlinarith
  exact ⟨by linarith, by linarith⟩

/-- Existence of an optimal spherical covering configuration on `S²` for every `n ≥ 1`. -/
theorem exists_optimal_covering {n : ℕ} (hn : 1 ≤ n) :
    ∃ p : Fin n → UnitSphere, ∀ q : Fin n → UnitSphere,
      coveringRadius hn p ≤ coveringRadius hn q := by
  have hcomp : IsCompact (Set.univ : Set (Fin n → UnitSphere)) := isCompact_univ
  have hne : (Set.univ : Set (Fin n → UnitSphere)).Nonempty := Set.univ_nonempty
  obtain ⟨p, -, hp⟩ := hcomp.exists_isMinOn hne (continuous_coveringRadius hn).continuousOn
  exact ⟨p, fun q => hp (Set.mem_univ q)⟩

end Geodesy.Spherical
