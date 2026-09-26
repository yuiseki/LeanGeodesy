import LeanGeodesy.Tiles.Quadtree
import LeanGeodesy.Tiles.Grid
import Mathlib.Algebra.BigOperators.Fin

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

The last section connects Web Mercator. On the half-open square every point
lies in a tile of `Tile z` (`tileOfPoint`), every tile of `Tile z` contains
a point (`tileOfPoint_surjective`), and the tile of a point at zoom `z + 1`
has as parent its tile at zoom `z` (`parent_tileOfPoint`), so its Morton
code divided by 4 is the code at zoom `z` (`morton_tileOfPoint_succ_div_four`).

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
    id, finCongr_apply, Fin.coe_cast, finProdFinEquiv_apply_val, parent, split, Equiv.coe_fn_mk]
  ring

/-- The Morton code is the quadtree path read as a base-4 number, coarsest digit first. -/
theorem mortonEquiv_val_eq_path : (z : ℕ) → (t : Tile z) →
    (mortonEquiv z t).1 = ∑ i : Fin z, (tileEquivPath z t i).1 * 4 ^ (z - 1 - i.1)
  | 0, t => by simp [mortonEquiv]
  | z + 1, t => by
    rw [mortonEquiv_succ_val, mortonEquiv_val_eq_path z (parent t), tileEquivPath_succ,
      Fin.sum_univ_castSucc, Finset.mul_sum]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last, Nat.sub_self,
      pow_zero, mul_one]
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

/-! ## Web Mercator tiles -/

open Projection

/-- The tile of a point of the half-open square at zoom `z`. -/
noncomputable def tileOfPoint (z : ℕ) {x y : ℝ} (hx : -halfExtent ≤ x ∧ x < halfExtent)
    (hy : -halfExtent < y ∧ y ≤ halfExtent) : Tile z :=
  (⟨tileX z x, tileX_lt z hx⟩, ⟨tileY z y, tileY_lt z hy⟩)

/-- The tile of a point at zoom `z + 1` has as parent its tile at zoom `z`. -/
theorem parent_tileOfPoint (z : ℕ) {x y : ℝ} (hx : -halfExtent ≤ x ∧ x < halfExtent)
    (hy : -halfExtent < y ∧ y ≤ halfExtent) :
    parent (tileOfPoint (z + 1) hx hy) = tileOfPoint z hx hy := by
  ext
  · exact tileX_succ_div_two z x
  · exact tileY_succ_div_two z y

/-- So its Morton code at zoom `z + 1`, divided by 4, is its code at zoom `z`. -/
theorem morton_tileOfPoint_succ_div_four (z : ℕ) {x y : ℝ} (hx : -halfExtent ≤ x ∧ x < halfExtent)
    (hy : -halfExtent < y ∧ y ≤ halfExtent) :
    (mortonEquiv (z + 1) (tileOfPoint (z + 1) hx hy)).1 / 4 = (mortonEquiv z (tileOfPoint z hx hy)).1 := by
  rw [mortonEquiv_succ_val, parent_tileOfPoint]
  have := childDigit_lt (tileOfPoint (z + 1) hx hy).1.1 (tileOfPoint (z + 1) hx hy).2.1
  omega

/-- Every tile at zoom `z` contains a point of the half-open square: its top-left
corner. -/
theorem tileOfPoint_surjective (z : ℕ) (t : Tile z) :
    ∃ x y, ∃ (hx : -halfExtent ≤ x ∧ x < halfExtent) (hy : -halfExtent < y ∧ y ≤ halfExtent),
      tileOfPoint z hx hy = t := by
  have hH := halfExtent_pos
  have h2 : (0 : ℝ) < 2 ^ z := by positivity
  have htx : (t.1.1 : ℝ) < 2 ^ z := by exact_mod_cast t.1.2
  have hty : (t.2.1 : ℝ) < 2 ^ z := by exact_mod_cast t.2.2
  set x := -halfExtent + 2 * halfExtent * t.1.1 / 2 ^ z
  set y := halfExtent - 2 * halfExtent * t.2.1 / 2 ^ z
  have hx : -halfExtent ≤ x ∧ x < halfExtent := by
    simp only [x]
    constructor
    · have : 0 ≤ 2 * halfExtent * t.1.1 / 2 ^ z := by positivity
      linarith
    · have : 2 * halfExtent * t.1.1 / 2 ^ z < 2 * halfExtent := by
        rw [div_lt_iff₀ h2]; nlinarith
      linarith
  have hy : -halfExtent < y ∧ y ≤ halfExtent := by
    simp only [y]
    constructor
    · have : 2 * halfExtent * t.2.1 / 2 ^ z < 2 * halfExtent := by
        rw [div_lt_iff₀ h2]; nlinarith
      linarith
    · have : 0 ≤ 2 * halfExtent * t.2.1 / 2 ^ z := by positivity
      linarith
  refine ⟨x, y, hx, hy, ?_⟩
  have hpx : pixelX z x / 256 = (t.1.1 : ℕ) := by
    simp only [x, pixelX, worldPixels]
    field_simp
    ring
  have hpy : pixelY z y / 256 = (t.2.1 : ℕ) := by
    simp only [y, pixelY, worldPixels]
    field_simp
    ring
  ext
  · simp only [tileOfPoint, tileX, tileIndex, hpx, Nat.floor_natCast]
  · simp only [tileOfPoint, tileY, tileIndex, hpy, Nat.floor_natCast]

end Geodesy.Tiles
