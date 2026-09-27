import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The tile quadtree

At zoom `z` the tiles are the pairs `(x, y)` with `x, y < 2^z` (`Tile`). A
tile at zoom `z + 1` has a parent at zoom `z`, `(x / 2, y / 2)`, and is one
of its four children, told apart by the digit `2 · (y mod 2) + (x mod 2)`,
the digit of a Bing Maps quadkey (`childDigit`). This splitting is a
bijection (`split`):

```
Tile (z + 1) ≃ Tile z × Fin 4
```

Repeating it from the root, a tile at zoom `z` is the same thing as a path
of `z` child digits from the root of the quadtree, coarsest first
(`QuadPath`, `tileEquivPath`): the path of a tile is the path of its parent
followed by its own digit (`tileEquivPath_succ`). The ancestor `k` generations
up (`ancestor`) has the column and row divided by `2^k` (`ancestor_val`).

This file is pure combinatorics on natural numbers; `Tiles.Grid` connects it
to Web Mercator and `Tiles.Morton` to Morton codes.
-/

namespace Geodesy.Tiles

/-- The tiles at zoom `z`: pairs of column and row, each below `2^z`. -/
abbrev Tile (z : ℕ) := Fin (2 ^ z) × Fin (2 ^ z)

/-- Paths of length `z` from the root of the quadtree: one of four child
digits per level, coarsest first. -/
abbrev QuadPath (z : ℕ) := Fin z → Fin 4

/-- The digit that tells a tile apart from its three siblings. -/
def childDigit (x y : ℕ) : ℕ := 2 * (y % 2) + x % 2

theorem childDigit_lt (x y : ℕ) : childDigit x y < 4 := by unfold childDigit; omega

theorem two_pow_succ' (z : ℕ) : 2 ^ (z + 1) = 2 * 2 ^ z := by rw [pow_succ, Nat.mul_comm]

/-- A tile at zoom `z + 1` is its parent at zoom `z` together with its child digit. -/
def split (z : ℕ) : Tile (z + 1) ≃ Tile z × Fin 4 where
  toFun t := ((⟨t.1.1 / 2, by have := t.1.2; have := two_pow_succ' z; omega⟩,
      ⟨t.2.1 / 2, by have := t.2.2; have := two_pow_succ' z; omega⟩),
    ⟨childDigit t.1.1 t.2.1, childDigit_lt _ _⟩)
  invFun p := (⟨2 * p.1.1.1 + p.2.1 % 2, by have := p.1.1.2; have := two_pow_succ' z; omega⟩,
    ⟨2 * p.1.2.1 + p.2.1 / 2, by have := p.1.2.2; have := p.2.2; have := two_pow_succ' z; omega⟩)
  left_inv t := by
    ext <;> simp [childDigit] <;> omega
  right_inv p := by
    have := p.2.2
    ext <;> simp [childDigit] <;> omega

/-- The parent of a tile. -/
def parent {z : ℕ} (t : Tile (z + 1)) : Tile z := (split z t).1

theorem parent_val {z : ℕ} (t : Tile (z + 1)) :
    (parent t).1.1 = t.1.1 / 2 ∧ (parent t).2.1 = t.2.1 / 2 := ⟨rfl, rfl⟩

/-- The children of a tile are exactly the tiles whose parent it is: columns
`2x` or `2x + 1` and rows `2y` or `2y + 1`. -/
theorem parent_eq_iff {z : ℕ} (t : Tile (z + 1)) (s : Tile z) :
    parent t = s ↔ (t.1.1 = 2 * s.1.1 ∨ t.1.1 = 2 * s.1.1 + 1) ∧
      (t.2.1 = 2 * s.2.1 ∨ t.2.1 = 2 * s.2.1 + 1) := by
  constructor
  · rintro rfl
    simp only [parent, split, Equiv.coe_fn_mk]
    omega
  · rintro ⟨hx, hy⟩
    ext <;> simp [parent, split] <;> omega

/-- Each tile has exactly four children. -/
theorem card_children {z : ℕ} (s : Tile z) :
    (Finset.univ.filter fun t : Tile (z + 1) => parent t = s).card = 4 := by
  have : (Finset.univ.filter fun t : Tile (z + 1) => parent t = s) =
      (Finset.univ : Finset (Fin 4)).map ⟨fun d => (split z).symm (s, d),
        fun d d' h => by simpa using congrArg (fun t => (split z t).2) h⟩ := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, parent]
    constructor
    · intro h
      exact ⟨(split z t).2, by rw [← h]; simp⟩
    · rintro ⟨d, rfl⟩
      simp
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-! ## Tiles are quadtree paths -/

/-- A tile at zoom `z` is a path of length `z` from the root of the quadtree. -/
def tileEquivPath : (z : ℕ) → Tile z ≃ QuadPath z
  | 0 =>
    { toFun := fun _ i => i.elim0
      invFun := fun _ => (⟨0, by simp⟩, ⟨0, by simp⟩)
      left_inv := fun t => by
        have h1 := t.1.2
        have h2 := t.2.2
        simp only [pow_zero] at h1 h2
        ext <;> simp only <;> omega
      right_inv := fun p => funext fun i => i.elim0 }
  | z + 1 =>
    (split z).trans ((Equiv.prodCongr (tileEquivPath z) (Equiv.refl (Fin 4))).trans
      ((Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ => Fin 4)))

/-- The path of a tile is the path of its parent followed by its child digit. -/
theorem tileEquivPath_succ {z : ℕ} (t : Tile (z + 1)) :
    tileEquivPath (z + 1) t = Fin.snoc (α := fun _ => Fin 4) (tileEquivPath z (parent t))
      (split z t).2 := by
  simp [tileEquivPath, parent, Fin.snocEquiv]

/-! ## Ancestors -/

/-- The ancestor `k` generations up: the parent taken `k` times. -/
def ancestor {z : ℕ} : (k : ℕ) → Tile (z + k) → Tile z
  | 0, t => t
  | k + 1, t => ancestor k (parent t)

/-- The ancestor `k` generations up has the column and row divided by `2^k`. -/
theorem ancestor_val {z : ℕ} : (k : ℕ) → (t : Tile (z + k)) →
    (ancestor k t).1.1 = t.1.1 / 2 ^ k ∧ (ancestor k t).2.1 = t.2.1 / 2 ^ k
  | 0, t => by simp [ancestor]
  | k + 1, t => by
    obtain ⟨h1, h2⟩ := ancestor_val k (parent t)
    simp only [ancestor]
    rw [h1, h2, (parent_val t).1, (parent_val t).2, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
      ← pow_succ']
    exact ⟨rfl, rfl⟩

end Geodesy.Tiles
