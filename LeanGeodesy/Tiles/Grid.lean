import LeanGeodesy.Projection.WebMercator
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# The integer tile grid of Web Mercator

Web maps cut the square world (`Projection.WebMercator`) into `2^z × 2^z`
tiles of `256 × 256` pixels at zoom `z`. A point's tile is its pixel
coordinate divided by 256, rounded down (`tileX`, `tileY`):

```
tileX = ⌊pixelX / 256⌋ = ⌊(x + π a) / (2 π a) · 2^z⌋
```

- The tile contains the point's pixel: `256 · tileX ≤ pixelX < 256 · (tileX + 1)`
  (`tileX_spec`).
- Tile indices lie in `0 .. 2^z - 1` on the half-open square
  `-π a ≤ x < π a`, `-π a < y ≤ π a` (`tileX_lt`, `tileY_lt`). The right edge
  (the antimeridian) and the bottom edge (the southern cut-off) are excluded:
  there the index would be `2^z`, one past the grid (`tileX_halfExtent`).
  Tiling schemes resolve this by assigning those edges to the neighbouring
  tile or by wrapping the antimeridian; this file keeps the half-open
  convention and does not wrap longitudes.
- Zooming in by one level doubles pixel coordinates (`pixelX_succ`), so the
  tile at zoom `z + 1` halves, rounded down, to the tile at zoom `z`
  (`tileX_succ_div_two`), and is one of its two children in each direction
  (`tileX_succ_eq`). This is what makes the tiles a quadtree (`Tiles.Quadtree`).
-/

namespace Geodesy.Projection

open Real

/-- The tile index of a pixel coordinate: `⌊p / 256⌋`. -/
noncomputable def tileIndex (p : ℝ) : ℕ := ⌊p / 256⌋₊

/-- The tile column of an easting at zoom `z`. -/
noncomputable def tileX (z : ℕ) (x : ℝ) : ℕ := tileIndex (pixelX z x)

/-- The tile row of a northing at zoom `z`, counted from the top. -/
noncomputable def tileY (z : ℕ) (y : ℝ) : ℕ := tileIndex (pixelY z y)

theorem pixelX_nonneg (z : ℕ) {x : ℝ} (hx : -halfExtent ≤ x) : 0 ≤ pixelX z x := by
  have hH := halfExtent_pos
  have := worldPixels_pos z
  unfold pixelX
  exact mul_nonneg (div_nonneg (by linarith) (by linarith)) this.le

theorem pixelY_nonneg (z : ℕ) {y : ℝ} (hy : y ≤ halfExtent) : 0 ≤ pixelY z y := by
  have hH := halfExtent_pos
  have := worldPixels_pos z
  unfold pixelY
  exact mul_nonneg (div_nonneg (by linarith) (by linarith)) this.le

/-- The tile contains the pixel. -/
theorem tileIndex_spec {p : ℝ} (hp : 0 ≤ p) :
    256 * (tileIndex p : ℝ) ≤ p ∧ p < 256 * ((tileIndex p : ℝ) + 1) := by
  have h1 := Nat.floor_le (div_nonneg hp (by norm_num : (0 : ℝ) ≤ 256))
  have h2 := Nat.lt_floor_add_one (p / 256)
  unfold tileIndex
  constructor <;> linarith

/-- The tile contains the point's pixel: `256 · tileX ≤ pixelX < 256 · (tileX + 1)`. -/
theorem tileX_spec (z : ℕ) {x : ℝ} (hx : -halfExtent ≤ x) :
    256 * (tileX z x : ℝ) ≤ pixelX z x ∧ pixelX z x < 256 * ((tileX z x : ℝ) + 1) :=
  tileIndex_spec (pixelX_nonneg z hx)

theorem tileY_spec (z : ℕ) {y : ℝ} (hy : y ≤ halfExtent) :
    256 * (tileY z y : ℝ) ≤ pixelY z y ∧ pixelY z y < 256 * ((tileY z y : ℝ) + 1) :=
  tileIndex_spec (pixelY_nonneg z hy)

theorem tileIndex_lt {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (h : p < 256 * n) : tileIndex p < n := by
  unfold tileIndex
  rw [Nat.floor_lt (div_nonneg hp (by norm_num))]
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 256)]
  linarith

/-- On the half-open square, tile columns lie in `0 .. 2^z - 1`. -/
theorem tileX_lt (z : ℕ) {x : ℝ} (hx : -halfExtent ≤ x ∧ x < halfExtent) : tileX z x < 2 ^ z := by
  have hH := halfExtent_pos
  refine tileIndex_lt (pixelX_nonneg z hx.1) ?_
  unfold pixelX worldPixels
  push_cast
  have hq : (x + halfExtent) / (2 * halfExtent) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h2 : (0 : ℝ) < 2 ^ z := by positivity
  nlinarith

/-- On the half-open square, tile rows lie in `0 .. 2^z - 1`. -/
theorem tileY_lt (z : ℕ) {y : ℝ} (hy : -halfExtent < y ∧ y ≤ halfExtent) : tileY z y < 2 ^ z := by
  have hH := halfExtent_pos
  refine tileIndex_lt (pixelY_nonneg z hy.2) ?_
  unfold pixelY worldPixels
  push_cast
  have hq : (halfExtent - y) / (2 * halfExtent) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h2 : (0 : ℝ) < 2 ^ z := by positivity
  nlinarith

/-- At the right edge, the antimeridian, the index would be `2^z`, one past the
grid: the reason the edge is excluded. -/
theorem tileX_halfExtent (z : ℕ) : tileX z halfExtent = 2 ^ z := by
  have hH := halfExtent_pos
  have : pixelX z halfExtent / 256 = (2 ^ z : ℕ) := by
    unfold pixelX worldPixels
    push_cast
    field_simp
    ring
  rw [tileX, tileIndex, this, Nat.floor_natCast]

/-- Doubling a pixel coordinate and halving the tile index gives the tile index back. -/
theorem tileIndex_two_mul_div_two (p : ℝ) : tileIndex (2 * p) / 2 = tileIndex p := by
  unfold tileIndex
  rw [← Nat.floor_div_natCast]
  congr 1
  push_cast
  ring

/-- The tile column at zoom `z + 1`, halved, is the tile column at zoom `z`. -/
theorem tileX_succ_div_two (z : ℕ) (x : ℝ) :
    tileX (z + 1) x / 2 = tileX z x := by
  rw [tileX, pixelX_succ, tileIndex_two_mul_div_two, tileX]

theorem tileY_succ_div_two (z : ℕ) (y : ℝ) :
    tileY (z + 1) y / 2 = tileY z y := by
  rw [tileY, pixelY_succ, tileIndex_two_mul_div_two, tileY]

/-- So the tile column at zoom `z + 1` is one of the two columns the column at
zoom `z` splits into. -/
theorem tileX_succ_eq (z : ℕ) (x : ℝ) :
    tileX (z + 1) x = 2 * tileX z x ∨ tileX (z + 1) x = 2 * tileX z x + 1 := by
  have := tileX_succ_div_two z x
  omega

theorem tileY_succ_eq (z : ℕ) (y : ℝ) :
    tileY (z + 1) y = 2 * tileY z y ∨ tileY (z + 1) y = 2 * tileY z y + 1 := by
  have := tileY_succ_div_two z y
  omega

end Geodesy.Projection
