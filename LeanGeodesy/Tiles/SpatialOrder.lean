import LeanGeodesy.Tiles.Hilbert

/-!
# Spatial orders on the tile quadtree

A spatial index numbers the tiles of each zoom level, `Tile z ≃ Fin (4^z)`, so
that the number of a tile's parent is the tile's number divided by 4
(`SpatialOrder`). Both the Morton order (`mortonOrder`) and the Hilbert order
(`hilbertOrder`) are spatial orders in this sense.

Everything a spatial index is used for follows from that one property, for
any spatial order:

- the number of the ancestor `k` generations up is the number divided by
  `4^k` (`index_ancestor`, `ancestor_symm`);
- a tile descends from `s` exactly when its number has `s`'s number as base-4
  prefix, that is, lies in `[index s · 4^k, (index s + 1) · 4^k)`
  (`ancestor_eq_iff`, `ancestor_eq_iff_mem_interval`);
- so the subtree of every tile is one interval of numbers
  (`subtree_eq_symm_interval`): a range query on the subtree is an interval
  scan.

What distinguishes the orders is adjacency. The Hilbert order is an
adjacent order, consecutive tiles always sharing an edge
(`hilbertOrder_isAdjacentOrder`); the Morton order is not
(`mortonOrder_not_isAdjacentOrder`).
-/

namespace Geodesy.Tiles

/-- A numbering of the tiles of every zoom level compatible with the quadtree:
the parent's number is the tile's number divided by 4. -/
structure SpatialOrder where
  index : (z : ℕ) → Tile z ≃ Fin (4 ^ z)
  index_parent : ∀ (z : ℕ) (t : Tile (z + 1)), (index z (parent t)).1 = (index (z + 1) t).1 / 4

namespace SpatialOrder

variable (O : SpatialOrder)

/-- The number of the ancestor `k` generations up is the number divided by `4^k`. -/
theorem index_ancestor {z : ℕ} : (k : ℕ) → (t : Tile (z + k)) →
    (O.index z (ancestor k t)).1 = (O.index (z + k) t).1 / 4 ^ k
  | 0, t => by simp [ancestor]
  | k + 1, t => by
    show (O.index z (ancestor k (parent t))).1 = _
    rw [index_ancestor k (parent t), O.index_parent (z + k) t, Nat.div_div_eq_div_mul, ← pow_succ']
    rfl

/-- A tile descends from `s` exactly when its number has `s`'s number as base-4
prefix. -/
theorem ancestor_eq_iff {z k : ℕ} (t : Tile (z + k)) (s : Tile z) :
    ancestor k t = s ↔ (O.index (z + k) t).1 / 4 ^ k = (O.index z s).1 := by
  rw [← O.index_ancestor]
  constructor
  · rintro rfl; rfl
  · intro h; exact (O.index z).injective (Fin.ext h)

/-- ...that is, when its number lies in `[index s · 4^k, (index s + 1) · 4^k)`. -/
theorem ancestor_eq_iff_mem_interval {z k : ℕ} (t : Tile (z + k)) (s : Tile z) :
    ancestor k t = s ↔
      (O.index z s).1 * 4 ^ k ≤ (O.index (z + k) t).1 ∧
        (O.index (z + k) t).1 < ((O.index z s).1 + 1) * 4 ^ k := by
  rw [O.ancestor_eq_iff, div_eq_iff_mem_interval (four_pow_pos k)]

/-- The ancestor of the tile numbered `i` is the tile numbered `i / 4^k`. -/
theorem ancestor_symm {z k : ℕ} (i : Fin (4 ^ (z + k))) :
    ancestor k ((O.index (z + k)).symm i) =
      (O.index z).symm ⟨i.1 / 4 ^ k, by
        rw [Nat.div_lt_iff_lt_mul (four_pow_pos k), ← pow_add]; exact i.2⟩ := by
  apply (O.index z).injective
  rw [Equiv.apply_symm_apply]
  ext
  rw [O.index_ancestor, Equiv.apply_symm_apply]

/-- The subtree of a tile, `k` generations deep, is the set of tiles numbered by
one interval of length `4^k`. -/
theorem subtree_eq_symm_interval {z k : ℕ} (s : Tile z) :
    {t : Tile (z + k) | ancestor k t = s} =
      (O.index (z + k)).symm ''
        {i | (O.index z s).1 * 4 ^ k ≤ i.1 ∧ i.1 < ((O.index z s).1 + 1) * 4 ^ k} := by
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro h
    exact ⟨O.index (z + k) t, (O.ancestor_eq_iff_mem_interval t s).mp h, Equiv.symm_apply_apply _ t⟩
  · rintro ⟨i, hi, rfl⟩
    rw [O.ancestor_eq_iff_mem_interval, Equiv.apply_symm_apply]
    exact hi

/-- An adjacent order: consecutive tiles always share an edge. -/
def IsAdjacentOrder : Prop :=
  ∀ (z : ℕ) (i : Fin (4 ^ z)) (h : i.1 + 1 < 4 ^ z),
    Adjacent ((O.index z).symm i) ((O.index z).symm ⟨i.1 + 1, h⟩)

end SpatialOrder

/-- The Morton order as a spatial order. -/
def mortonOrder : SpatialOrder where
  index := mortonEquiv
  index_parent z t := by
    have h := mortonEquiv_succ_val t
    have := childDigit_lt t.1.1 t.2.1
    omega

/-- The Hilbert order as a spatial order: numbering by `encode`. -/
def hilbertOrder : SpatialOrder where
  index z := (hilbertEquiv z).symm
  index_parent z t := by
    have h := parent_hilbert_decode (encode (z + 1) t)
    rw [decode_encode] at h
    show (encode z (parent t)).1 = (encode (z + 1) t).1 / 4
    rw [h, encode_decode]

theorem hilbertOrder_index (z : ℕ) (t : Tile z) : hilbertOrder.index z t = encode z t := rfl

theorem mortonOrder_index (z : ℕ) (t : Tile z) : mortonOrder.index z t = mortonEquiv z t := rfl

/-- The Hilbert order is an adjacent order. -/
theorem hilbertOrder_isAdjacentOrder : hilbertOrder.IsAdjacentOrder :=
  fun _ i h => hilbert_adjacent i h

/-- The Morton order is not: at zoom 1 its tiles numbered 1 and 2 do not share an
edge. -/
theorem mortonOrder_not_isAdjacentOrder : ¬ mortonOrder.IsAdjacentOrder := by
  intro hadj
  obtain ⟨s, t, hs, ht, hn⟩ := morton_not_adjacent (z := 1) le_rfl
  have h := hadj 1 ⟨1, by norm_num⟩ (by norm_num)
  have e1 : (mortonOrder.index 1).symm ⟨1, by norm_num⟩ = s :=
    (Equiv.symm_apply_eq _).mpr (Fin.ext hs.symm)
  have e2 : (mortonOrder.index 1).symm ⟨1 + 1, by norm_num⟩ = t :=
    (Equiv.symm_apply_eq _).mpr (Fin.ext ht.symm)
  rw [e1, e2] at h
  exact hn h

/-! ## The Morton instances of the general theorems -/

/-- The Morton code of the ancestor `k` generations up is the code divided by `4^k`. -/
theorem morton_ancestor {z k : ℕ} (t : Tile (z + k)) :
    (mortonEquiv z (ancestor k t)).1 = (mortonEquiv (z + k) t).1 / 4 ^ k :=
  mortonOrder.index_ancestor k t

/-- A tile descends from `s` exactly when its Morton code lies in `s`'s interval. -/
theorem morton_ancestor_eq_iff_mem_interval {z k : ℕ} (t : Tile (z + k)) (s : Tile z) :
    ancestor k t = s ↔
      (mortonEquiv z s).1 * 4 ^ k ≤ (mortonEquiv (z + k) t).1 ∧
        (mortonEquiv (z + k) t).1 < ((mortonEquiv z s).1 + 1) * 4 ^ k :=
  mortonOrder.ancestor_eq_iff_mem_interval t s

/-- The subtree of a tile is the set of tiles with Morton codes in one interval. -/
theorem morton_subtree_eq_interval {z k : ℕ} (s : Tile z) :
    {t : Tile (z + k) | ancestor k t = s} =
      (mortonEquiv (z + k)).symm ''
        {i | (mortonEquiv z s).1 * 4 ^ k ≤ i.1 ∧ i.1 < ((mortonEquiv z s).1 + 1) * 4 ^ k} :=
  mortonOrder.subtree_eq_symm_interval s

end Geodesy.Tiles
