import LeanGeodesy.Spherical.Topology
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Spherical covering: inner products, convex hulls, Voronoi cells

Exact reformulations of the covering condition `IsCovering p r` on `S²`, the
algebraic base for certifying covering radii by finite data. Nothing here is a
new bound on any covering radius; every statement is an equivalence or a
one-line consequence of one.

For `0 ≤ r ≤ π` and a configuration `p : Fin n → UnitSphere`:

1. `mem_closedCap_iff`, `isCovering_iff_inner`: the geodesic condition
   `geoDist c x ≤ r` is the inner-product condition `cos r ≤ ⟪c, x⟫`.
2. `isCovering_iff_inner_support`: covering is the statement that the support
   function of the convex hull `hullOf p` is at least `cos r` in every unit
   direction: `∀ u, ∃ i, cos r ≤ ⟪p i, u⟫`, and `max_i ⟪p i, u⟫` is that support
   function (`hullOf_subset_halfSpace`).
3. `closedBall_subset_hullOf_iff`, `isCovering_iff_closedBall_subset_hullOf`:
   for `0 ≤ r ≤ π / 2`, the configuration covers at radius `r` exactly when the
   closed ball of radius `cos r` about the origin lies in the convex hull of
   the points. This uses Hahn–Banach separation of a point from a compact
   convex set, which is where `Classical.choice` enters.
4. `cos_le_of_supportPlane`: a unit direction `u` with `⟪p i, u⟫ ≤ c` for all
   `i` (a supporting plane of the hull) forces `cos r ≤ c`; this is the finite
   lower-bound test, and it needs no completeness of any face list.
5. `mem_voronoiCell_iff`, `isCovering_iff_voronoiCell_subset`: the spherical
   Voronoi cell of `p i` is the sphere cut by the half-spaces
   `⟪p j - p i, x⟫ ≤ 0`, and covering holds exactly when each cell lies in its
   own cap.
6. Degenerate configurations. Repeated points change nothing
   (`isCovering_comp_of_range_eq`, `hullOf` depends only on the range). If the
   origin is not an interior point of the hull, or all points lie in a closed
   hemisphere, no radius below `π / 2` covers
   (`not_isCovering_of_zero_not_mem_interior`,
   `pi_div_two_le_of_hemisphere`).
-/

namespace Geodesy.Spherical

open Real Geodesic

/-! ## 1. Caps as inner-product conditions -/

/-- For `0 ≤ r ≤ π`, a point lies in the closed cap `closedCap c r` exactly when
`cos r ≤ ⟪c, x⟫`. -/
theorem mem_closedCap_iff {r : ℝ} (h0 : 0 ≤ r) (hπ : r ≤ π) (c x : UnitSphere) :
    x ∈ closedCap c r ↔ cos r ≤ inner ℝ c.1 x.1 := by
  show geoDist c x ≤ r ↔ _
  constructor
  · intro h
    rw [← cos_geoDist]
    exact antitoneOn_cos ⟨geoDist_nonneg c x, geoDist_le_pi c x⟩ ⟨h0, hπ⟩ h
  · intro h
    rw [geoDist_eq_arccos_inner, ← arccos_cos h0 hπ]
    exact arccos_le_arccos_of_le h

/-- The covering condition as an inner-product condition. -/
theorem isCovering_iff_inner {n : ℕ} (p : Fin n → UnitSphere) {r : ℝ} (h0 : 0 ≤ r)
    (hπ : r ≤ π) :
    IsCovering p r ↔ ∀ x : UnitSphere, ∃ i : Fin n, cos r ≤ inner ℝ (p i).1 x.1 := by
  unfold IsCovering
  simp only [mem_closedCap_iff h0 hπ]

/-! ## 2. The convex hull and its support function -/

/-- The convex hull in `E3` of the points of a configuration. -/
def hullOf {n : ℕ} (p : Fin n → UnitSphere) : Set E3 :=
  convexHull ℝ (Set.range fun i => (p i).1)

/-- The hull depends only on the set of points, so repeated points change
nothing. -/
theorem hullOf_congr {n m : ℕ} {p : Fin n → UnitSphere} {q : Fin m → UnitSphere}
    (h : Set.range p = Set.range q) : hullOf p = hullOf q := by
  unfold hullOf
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ : p i ∈ Set.range q := h ▸ ⟨i, rfl⟩
    exact ⟨j, congrArg Subtype.val hj⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, hi⟩ : q j ∈ Set.range p := h ▸ ⟨j, rfl⟩
    exact ⟨i, congrArg Subtype.val hi⟩

private theorem isLinearMap_inner (w : E3) : IsLinearMap ℝ fun x : E3 => inner ℝ w x :=
  ⟨fun x y => inner_add_right w x y, fun c x => by simp [inner_smul_right]⟩

/-- The hull lies in the half-space `⟪w, x⟫ ≤ c` exactly when every point does:
the support function of the hull in direction `w` is `max_i ⟪w, p i⟫`. -/
theorem hullOf_subset_halfSpace {n : ℕ} (p : Fin n → UnitSphere) (w : E3) (c : ℝ) :
    hullOf p ⊆ {x | inner ℝ w x ≤ c} ↔ ∀ i, inner ℝ w (p i).1 ≤ c := by
  constructor
  · intro h i
    exact h (subset_convexHull ℝ _ ⟨i, rfl⟩)
  · intro h
    refine convexHull_min ?_ (convex_halfSpace_le (isLinearMap_inner w) c)
    rintro _ ⟨i, rfl⟩
    exact h i

/-! ## 3. Covering is containment of a ball in the hull -/

/-- A ball about the origin lies in the convex hull of the points exactly when,
in every unit direction, some point has inner product at least the radius. -/
theorem closedBall_subset_hullOf_iff {n : ℕ} (p : Fin n → UnitSphere) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Metric.closedBall (0 : E3) ρ ⊆ hullOf p ↔
      ∀ u : UnitSphere, ∃ i : Fin n, ρ ≤ inner ℝ (p i).1 u.1 := by
  constructor
  · intro h u
    by_contra hcon
    push Not at hcon
    have hmem : ρ • u.1 ∈ hullOf p := h (by
      rw [mem_closedBall_zero_iff, norm_smul, u.2, mul_one, Real.norm_eq_abs, abs_of_nonneg hρ])
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image
      (Finset.univ.image (fun i : Fin n => inner ℝ u.1 (p i).1) ∪ {ρ - 1}) id
      ⟨ρ - 1, by simp⟩
    have hmρ : m < ρ := by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hm
      rcases hm with ⟨i, rfl⟩ | rfl
      · rw [real_inner_comm]; exact hcon i
      · linarith
    have hall : ∀ i, inner ℝ u.1 (p i).1 ≤ m := fun i =>
      hmax _ (by simp)
    have hsub := (hullOf_subset_halfSpace p u.1 m).2 hall hmem
    have : inner ℝ u.1 (ρ • u.1) = ρ := by
      rw [inner_smul_right, real_inner_self_eq_norm_sq, u.2]; ring
    simp only [Set.mem_ofPred_eq, this] at hsub
    linarith
  · intro h y hy
    by_contra hyn
    have hconv : Convex ℝ (hullOf p) := convex_convexHull ℝ _
    have hclosed : IsClosed (hullOf p) :=
      (Set.Finite.isCompact_convexHull ℝ (Set.finite_range _)).isClosed
    obtain ⟨f, c, hfy, hb⟩ := geometric_hahn_banach_point_closed hconv hclosed hyn
    set w : E3 := (InnerProductSpace.toDual ℝ E3).symm f with hw
    have hwf : ∀ x, inner ℝ w x = f x := fun x => InnerProductSpace.toDual_symm_apply
    have hwf' : ∀ x, inner ℝ x w = f x := fun x => by rw [real_inner_comm]; exact hwf x
    obtain ⟨i0, -⟩ := h (Classical.arbitrary UnitSphere)
    have hc0 : c < f (p i0).1 := hb _ (subset_convexHull ℝ _ ⟨i0, rfl⟩)
    have hw0 : w ≠ 0 := by
      intro h0
      have hf0 : ∀ x, f x = 0 := fun x => by rw [← hwf, h0, inner_zero_left]
      rw [hf0] at hfy hc0
      linarith
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have hpos : 0 < ‖w‖⁻¹ := inv_pos.2 hn
    let u : UnitSphere := ⟨(‖w‖⁻¹) • (-w), by
      rw [norm_smul, norm_neg, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']⟩
    obtain ⟨i, hi⟩ := h u
    have hi' : c < f (p i).1 := hb _ (subset_convexHull ℝ _ ⟨i, rfl⟩)
    have e1 : inner ℝ (p i).1 u.1 = ‖w‖⁻¹ * (-(f (p i).1)) := by
      show inner ℝ (p i).1 ((‖w‖⁻¹) • (-w)) = _
      rw [inner_smul_right, inner_neg_right, hwf']
    have e2 : inner ℝ y u.1 = ‖w‖⁻¹ * (-(f y)) := by
      show inner ℝ y ((‖w‖⁻¹) • (-w)) = _
      rw [inner_smul_right, inner_neg_right, hwf']
    have s1 : ‖w‖⁻¹ * (-(f (p i).1)) < ‖w‖⁻¹ * (-c) :=
      mul_lt_mul_of_pos_left (by linarith) hpos
    have s2 : ‖w‖⁻¹ * (-c) < ‖w‖⁻¹ * (-(f y)) :=
      mul_lt_mul_of_pos_left (by linarith) hpos
    have s3 : inner ℝ y u.1 ≤ ρ :=
      (real_inner_le_norm y u.1).trans (by rw [u.2, mul_one]; exact mem_closedBall_zero_iff.1 hy)
    linarith

/-- For `0 ≤ r ≤ π`, covering at radius `r` means: in every unit direction `u`,
some point has `cos r ≤ ⟪p i, u⟫`; that is, the support function of `hullOf p`
is at least `cos r` everywhere. -/
theorem isCovering_iff_inner_support {n : ℕ} (p : Fin n → UnitSphere) {r : ℝ} (h0 : 0 ≤ r)
    (hπ : r ≤ π) :
    IsCovering p r ↔ ∀ u : UnitSphere, ∃ i : Fin n, cos r ≤ inner ℝ (p i).1 u.1 :=
  isCovering_iff_inner p h0 hπ

/-- Covering at radius `r ≤ π / 2` is exactly containment of the closed ball of
radius `cos r` in the convex hull of the points. -/
theorem isCovering_iff_closedBall_subset_hullOf {n : ℕ} (p : Fin n → UnitSphere) {r : ℝ}
    (h0 : 0 ≤ r) (hr : r ≤ π / 2) :
    IsCovering p r ↔ Metric.closedBall (0 : E3) (cos r) ⊆ hullOf p := by
  have hcos : 0 ≤ cos r := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hr⟩
  rw [closedBall_subset_hullOf_iff p hcos]
  exact isCovering_iff_inner p h0 (by linarith [pi_pos])

/-- The covering radius is at most `r ≤ π / 2` exactly when the ball of radius
`cos r` lies in the hull. -/
theorem coveringRadius_le_iff_closedBall_subset_hullOf {n : ℕ} (hn : 1 ≤ n)
    (p : Fin n → UnitSphere) {r : ℝ} (h0 : 0 ≤ r) (hr : r ≤ π / 2) :
    coveringRadius hn p ≤ r ↔ Metric.closedBall (0 : E3) (cos r) ⊆ hullOf p := by
  rw [coveringRadius_le_iff, isCovering_iff_closedBall_subset_hullOf p h0 hr]

/-! ## 4. Supporting planes bound the covering radius from below -/

/-- If all the points lie in the half-space `⟪p i, u⟫ ≤ c` for a unit vector `u`
(a supporting plane of the hull, at distance `c` from the origin), then any
covering radius `r ∈ [0, π]` of the configuration has `cos r ≤ c`. -/
theorem cos_le_of_supportPlane {n : ℕ} {p : Fin n → UnitSphere} {r : ℝ} (h0 : 0 ≤ r)
    (hπ : r ≤ π) (hcov : IsCovering p r) (u : UnitSphere) {c : ℝ}
    (hc : ∀ i, inner ℝ (p i).1 u.1 ≤ c) : cos r ≤ c := by
  obtain ⟨i, hi⟩ := (isCovering_iff_inner p h0 hπ).1 hcov u
  exact hi.trans (hc i)

/-! ## 5. Voronoi cells -/

/-- The spherical Voronoi cell of `p i`: the points of `S²` at least as close
(in geodesic distance) to `p i` as to every `p j`. Ties lie on the boundary and
are kept in every cell they touch, so the cells cover but overlap on their
boundaries; points repeated in `p` have equal cells. -/
def voronoiCell {n : ℕ} (p : Fin n → UnitSphere) (i : Fin n) : Set UnitSphere :=
  {x | ∀ j, geoDist (p i) x ≤ geoDist (p j) x}

/-- A point is nearer to `p i` than to `p j` exactly when `⟪p j - p i, x⟫ ≤ 0`. -/
theorem geoDist_le_geoDist_iff_inner (a b x : UnitSphere) :
    geoDist a x ≤ geoDist b x ↔ inner ℝ (b.1 - a.1) x.1 ≤ 0 := by
  rw [inner_sub_left, sub_nonpos]
  constructor
  · intro h
    rw [← cos_geoDist, ← cos_geoDist]
    exact antitoneOn_cos ⟨geoDist_nonneg a x, geoDist_le_pi a x⟩
      ⟨geoDist_nonneg b x, geoDist_le_pi b x⟩ h
  · intro h
    rw [geoDist_eq_arccos_inner, geoDist_eq_arccos_inner]
    exact arccos_le_arccos_of_le h

/-- The Voronoi cell of `p i` is the sphere cut by the half-spaces
`⟪p j - p i, x⟫ ≤ 0` through the origin. -/
theorem mem_voronoiCell_iff {n : ℕ} (p : Fin n → UnitSphere) (i : Fin n) (x : UnitSphere) :
    x ∈ voronoiCell p i ↔ ∀ j, inner ℝ ((p j).1 - (p i).1) x.1 ≤ 0 :=
  forall_congr' fun j => geoDist_le_geoDist_iff_inner (p i) (p j) x

/-- With at least one point, the Voronoi cells cover the sphere. -/
theorem exists_mem_voronoiCell {n : ℕ} (hn : 1 ≤ n) (p : Fin n → UnitSphere)
    (x : UnitSphere) : ∃ i, x ∈ voronoiCell p i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun j => geoDist (p j) x)
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩)
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- Covering reduces to the cells: it holds exactly when each Voronoi cell lies
in the cap of its own centre. -/
theorem isCovering_iff_voronoiCell_subset {n : ℕ} (hn : 1 ≤ n) (p : Fin n → UnitSphere)
    (r : ℝ) : IsCovering p r ↔ ∀ i, voronoiCell p i ⊆ closedCap (p i) r := by
  constructor
  · intro h i x hx
    obtain ⟨j, hj⟩ := h x
    exact le_trans (hx j) hj
  · intro h x
    obtain ⟨i, hi⟩ := exists_mem_voronoiCell hn p x
    exact ⟨i, h i hi⟩

/-! ## 6. Degenerate configurations -/

/-- Repeated points are harmless: two configurations with the same set of
points cover at the same radii. -/
theorem isCovering_comp_of_range_eq {n m : ℕ} {p : Fin n → UnitSphere}
    {q : Fin m → UnitSphere} (h : Set.range p = Set.range q) (r : ℝ) :
    IsCovering p r ↔ IsCovering q r := by
  have key : ∀ {a b : ℕ} (f : Fin a → UnitSphere) (g : Fin b → UnitSphere),
      Set.range f = Set.range g → IsCovering f r → IsCovering g r := by
    intro a b f g hfg hf x
    obtain ⟨i, hi⟩ := hf x
    obtain ⟨j, hj⟩ : f i ∈ Set.range g := hfg ▸ ⟨i, rfl⟩
    exact ⟨j, by rw [hj]; exact hi⟩
  exact ⟨key p q h, key q p h.symm⟩

/-- If the origin is not an interior point of the hull, no radius below `π / 2`
covers. -/
theorem not_isCovering_of_zero_not_mem_interior {n : ℕ} {p : Fin n → UnitSphere}
    (h : (0 : E3) ∉ interior (hullOf p)) {r : ℝ} (h0 : 0 ≤ r) (hr : r < π / 2) :
    ¬ IsCovering p r := by
  intro hcov
  have hcos : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hr⟩
  have hsub := (isCovering_iff_closedBall_subset_hullOf p h0 hr.le).1 hcov
  exact h (mem_interior_iff_mem_nhds.2
    (Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E3) hcos) hsub))

/-- If all the points lie in a closed hemisphere, the covering radius is at
least `π / 2`. -/
theorem pi_div_two_le_of_hemisphere {n : ℕ} {p : Fin n → UnitSphere} (u : UnitSphere)
    (hc : ∀ i, inner ℝ (p i).1 u.1 ≤ 0) {r : ℝ} (h0 : 0 ≤ r) (hπ : r ≤ π)
    (hcov : IsCovering p r) : π / 2 ≤ r := by
  have h := cos_le_of_supportPlane h0 hπ hcov u hc
  by_contra hlt
  push Not at hlt
  have : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hlt⟩
  linarith

end Geodesy.Spherical
