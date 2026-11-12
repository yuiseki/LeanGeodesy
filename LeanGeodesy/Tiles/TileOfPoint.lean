import LeanGeodesy.Tiles.Morton
import LeanGeodesy.Tiles.Grid

/-!
# The tile of a point of Web Mercator

This file connects the tile quadtree and Morton codes (`Tiles.Quadtree`,
`Tiles.Morton`, pure combinatorics on natural numbers) to the integer tile
grid of Web Mercator (`Tiles.Grid`, over the real numbers). On the half-open
square every point lies in a tile of `Tile z` (`tileOfPoint`), every tile of
`Tile z` contains a point (`tileOfPoint_surjective`), and the tile of a point
at zoom `z + 1` has as parent its tile at zoom `z` (`parent_tileOfPoint`), so
its Morton code divided by 4 is the code at zoom `z`
(`morton_tileOfPoint_succ_div_four`).
-/

namespace Geodesy.Tiles

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
