import LeanGeodesy.Tiles.Quadtree

/-!
# Adjacent tiles

Two cells of a grid are adjacent when they share an edge: they agree in one
coordinate and differ by one in the other (`AdjN` on pairs of natural numbers,
`Adjacent` on tiles). Spatial orders are compared by whether consecutive tiles
are adjacent (`Tiles.Hilbert`, `Tiles.SpatialOrder`).
-/

namespace Geodesy.Tiles

/-- Two cells share an edge. -/
def AdjN (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨ (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

instance : DecidableRel AdjN := fun p q => by unfold AdjN; infer_instance

theorem AdjN.symm {p q : ℕ × ℕ} (h : AdjN p q) : AdjN q p := by unfold AdjN at *; omega

/-- No cell is adjacent to itself. -/
theorem AdjN.irrefl (p : ℕ × ℕ) : ¬ AdjN p p := by unfold AdjN; omega

/-- Two tiles share an edge. -/
def Adjacent {z : ℕ} (s t : Tile z) : Prop := AdjN (s.1.1, s.2.1) (t.1.1, t.2.1)

instance {z : ℕ} : DecidableRel (@Adjacent z) := fun s t => by unfold Adjacent; infer_instance

theorem Adjacent.symm {z : ℕ} {s t : Tile z} (h : Adjacent s t) : Adjacent t s := AdjN.symm h

theorem Adjacent.irrefl {z : ℕ} (s : Tile z) : ¬ Adjacent s s := AdjN.irrefl _

/-- Adjacent tiles are distinct. -/
theorem Adjacent.ne {z : ℕ} {s t : Tile z} (h : Adjacent s t) : s ≠ t := by
  rintro rfl; exact Adjacent.irrefl s h

end Geodesy.Tiles
