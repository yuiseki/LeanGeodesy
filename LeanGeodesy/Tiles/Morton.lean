import LeanGeodesy.Tiles.Quadtree
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Morton codes, and the three ways of naming a tile

A tile at zoom `z` can be named three ways: by its column and row
`(x, y)` (`Tile z`), by its path of `z` child digits from the root of the
quadtree (`QuadPath z`), or by a single number below `4^z`, its Morton code.
This file proves the three are in bijection (`tile_path_morton_bijective`):

```
Tile z  ≃  QuadPath z  ≃  Fin (4^z)            (tileEquivPath, pathEquivMorton, mortonEquiv)
```

and that the triangle commutes (`mortonEquiv_eq_trans`). The Morton code is
built with the quadtree split: the code of a tile is four times its parent's
code plus its child digit (`mortonEquiv_succ_val`). So

- it is the quadtree path read as a base-4 number, coarsest digit first
  (`mortonEquiv_val_eq_path`);
- it interleaves the bits of the column and the row, the Z-order curve
  (`morton_eq_interleave`);
- dividing by 4 gives the parent's code and the remainder is the child digit
  (`morton_div_four`, `morton_mod_four`).

This file is pure combinatorics on natural numbers, like `Tiles.Quadtree`;
`Tiles.TileOfPoint` connects the codes to Web Mercator.

The Z-order curve jumps: at zoom 1 the codes 1 and 2 are the tiles `(1, 0)`
and `(0, 1)`, which do not share an edge (`morton_jumps`). The Hilbert curve
avoids this and is not covered here.
-/

namespace Geodesy.Tiles

open Finset

/-- A tile at zoom `z` as a Morton code below `4^z`: four times its parent's
code plus its child digit. -/
def mortonEquiv : (z : ℕ) → Tile z ≃ Fin (4 ^ z)
  | 0 =>
    { toFun := fun _ => ⟨0, by simp⟩
      invFun := fun _ => (⟨0, by simp⟩, ⟨0, by simp⟩)
      left_inv := fun t => by
        have h1 := t.1.2
        have h2 := t.2.2
        simp only [pow_zero] at h1 h2
        ext <;> simp only <;> omega
      right_inv := fun m => by
        have := m.2
        simp only [pow_zero] at this
        ext; simp only; omega }
  | z + 1 =>
    (split z).trans ((Equiv.prodCongr (mortonEquiv z) (Equiv.refl (Fin 4))).trans
      (finProdFinEquiv.trans (finCongr (pow_succ 4 z).symm)))

/-- The Morton code of a quadtree path. -/
def pathEquivMorton (z : ℕ) : QuadPath z ≃ Fin (4 ^ z) := (tileEquivPath z).symm.trans (mortonEquiv z)

/-- The triangle commutes: going from a tile to its path and then to the Morton
code is going straight to the Morton code. -/
theorem mortonEquiv_eq_trans (z : ℕ) : mortonEquiv z = (tileEquivPath z).trans (pathEquivMorton z) := by
  ext t
  simp [pathEquivMorton]

/-- The three namings of the tiles at zoom `z` are in bijection. -/
theorem tile_path_morton_bijective (z : ℕ) :
    Function.Bijective (tileEquivPath z) ∧ Function.Bijective (pathEquivMorton z) ∧
      Function.Bijective (mortonEquiv z) :=
  ⟨(tileEquivPath z).bijective, (pathEquivMorton z).bijective, (mortonEquiv z).bijective⟩

/-- The code of a tile is four times its parent's code plus its child digit. -/
theorem mortonEquiv_succ_val {z : ℕ} (t : Tile (z + 1)) :
    (mortonEquiv (z + 1) t).1 = 4 * (mortonEquiv z (parent t)).1 + childDigit t.1.1 t.2.1 := by
  simp only [mortonEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
    id, finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val, parent, split, Equiv.coe_fn_mk]
  ring

/-- The Morton code is the quadtree path read as a base-4 number, coarsest digit first. -/
theorem mortonEquiv_val_eq_path : (z : ℕ) → (t : Tile z) →
    (mortonEquiv z t).1 = ∑ i : Fin z, (tileEquivPath z t i).1 * 4 ^ (z - 1 - i.1)
  | 0, t => by simp [mortonEquiv]
  | z + 1, t => by
    rw [mortonEquiv_succ_val, mortonEquiv_val_eq_path z (parent t), tileEquivPath_succ,
      Fin.sum_univ_castSucc, Finset.mul_sum]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hi := i.2
      rw [show z + 1 - 1 - i.1 = (z - 1 - i.1) + 1 by omega, pow_succ]
      ring
    · simp [split]

/-- The Morton code as a number: four times the parent's code plus the child digit. -/
def morton : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | z + 1, x, y => 4 * morton z (x / 2) (y / 2) + childDigit x y

theorem mortonEquiv_val : (z : ℕ) → (t : Tile z) → (mortonEquiv z t).1 = morton z t.1.1 t.2.1
  | 0, t => by simp [mortonEquiv, morton]
  | z + 1, t => by
    rw [mortonEquiv_succ_val, mortonEquiv_val z (parent t), morton]
    rfl

/-- Dividing a Morton code by 4 gives the parent's code... -/
theorem morton_div_four (z x y : ℕ) : morton (z + 1) x y / 4 = morton z (x / 2) (y / 2) := by
  have := childDigit_lt x y
  simp only [morton]
  omega

/-- ...and the remainder is the child digit. -/
theorem morton_mod_four (z x y : ℕ) : morton (z + 1) x y % 4 = childDigit x y := by
  have := childDigit_lt x y
  simp only [morton]
  omega

/-- The Morton code interleaves the bits of the column and the row: bit `i` of
`x` goes to position `2i` and bit `i` of `y` to position `2i + 1`. -/
theorem morton_eq_interleave : (z x y : ℕ) →
    morton z x y = ∑ i ∈ range z, (x / 2 ^ i % 2 * 4 ^ i + y / 2 ^ i % 2 * (2 * 4 ^ i))
  | 0, x, y => by simp [morton]
  | z + 1, x, y => by
    rw [morton, morton_eq_interleave z (x / 2) (y / 2), Finset.sum_range_succ']
    simp only [pow_zero, Nat.div_one, mul_one, pow_succ, Finset.mul_sum, childDigit]
    rw [add_comm (x % 2) _]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm 2 (2 ^ i)]
      ring
    · ring

/-- The Z-order curve jumps: at zoom 1, codes 1 and 2 are `(1, 0)` and `(0, 1)`,
which do not share an edge. -/
theorem morton_jumps : morton 1 1 0 = 1 ∧ morton 1 0 1 = 2 := by decide

end Geodesy.Tiles
