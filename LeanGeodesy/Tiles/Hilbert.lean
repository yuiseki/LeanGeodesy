import LeanGeodesy.Tiles.Morton
import LeanGeodesy.Tiles.Adjacency

/-!
# The Hilbert order on the tile grid

The Morton code orders the tiles of a zoom level along the Z-order curve,
which jumps (`morton_jumps`). The Hilbert order visits the same `2^z × 2^z`
tiles so that consecutive tiles always share an edge. This file defines it
on the finite grid; the continuous Hilbert curve is not covered.

`hilbertD z i` is the tile visited `i`-th at zoom `z`. At zoom `z + 1` the
index splits into its top base-4 digit `q = i / 4^z` and the rest
`r = i mod 4^z`; the curve at zoom `z` visits `r`, and is placed in quadrant
`q` after a symmetry of the `2^z` grid (`quadPlace`, with `n = 2^z`):

```
q = 0: (x, y) ↦ (y, x)                  transpose, quadrant (0, 0)
q = 1: (x, y) ↦ (x, y + n)              quadrant (0, 1)
q = 2: (x, y) ↦ (x + n, y + n)          quadrant (1, 1)
q = 3: (x, y) ↦ (2n - 1 - y, n - 1 - x) anti-transpose, quadrant (1, 0)
```

The curve at every zoom starts at `(0, 0)` and ends at `(2^z - 1, 0)`
(`hilbertD_zero`, `hilbertD_last`). This invariant is what makes the pieces
join: the end of each quadrant's curve is next to the start of the next one.
So

- consecutive tiles share an edge (`hilbertD_adj`, `hilbert_adjacent`);
- the order visits every tile exactly once: `decode : Fin (4^z) → Tile z` and
  the recursive, computable `encode` (`hilbertE`, which reads off the quadrant
  and undoes its symmetry) are inverse bijections (`encode_decode`,
  `decode_encode`, `hilbertEquiv`). Neither the maps nor the equivalence use
  `Classical.choice`; the axiom audit pins them to `propext` and `Quot.sound`;
- it is nested like the quadtree: the tile visited `i`-th at zoom `z + 1` has
  as parent the tile visited `i / 4`-th at zoom `z` (`parent_hilbert_decode`),
  so the tiles `4k .. 4k + 3` are the four children of tile `k`, in an order
  that depends on the orientation; more generally the ancestor `k` generations
  up of the tile visited `i`-th is the tile visited `i / 4^k`-th
  (`ancestor_decode`). So the tiles descending from one tile are exactly the
  tiles whose Hilbert indices fill one interval, the indices with that tile's
  index as base-4 prefix (`ancestor_eq_iff_encode_mem_interval`,
  `subtree_eq_decode_interval`);
- the Morton order, in contrast, is not adjacent at any zoom `z ≥ 1`: codes
  1 and 2 are always `(1, 0)` and `(0, 1)` (`morton_not_adjacent`).
-/

namespace Geodesy.Tiles

/-- Place a point of the `n × n` grid into quadrant `q` of the `2n × 2n` grid,
after the symmetry the Hilbert order uses there. -/
def quadPlace (n q : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if q = 0 then (p.2, p.1)
  else if q = 1 then (p.1, p.2 + n)
  else if q = 2 then (p.1 + n, p.2 + n)
  else (2 * n - 1 - p.2, n - 1 - p.1)

theorem quadPlace_zero (n : ℕ) (p : ℕ × ℕ) : quadPlace n 0 p = (p.2, p.1) := rfl
theorem quadPlace_one (n : ℕ) (p : ℕ × ℕ) : quadPlace n 1 p = (p.1, p.2 + n) := rfl
theorem quadPlace_two (n : ℕ) (p : ℕ × ℕ) : quadPlace n 2 p = (p.1 + n, p.2 + n) := rfl
theorem quadPlace_three (n : ℕ) (p : ℕ × ℕ) : quadPlace n 3 p = (2 * n - 1 - p.2, n - 1 - p.1) := rfl

/-- The tile visited `i`-th by the Hilbert order at zoom `z`. -/
def hilbertD : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (0, 0)
  | z + 1, i => quadPlace (2 ^ z) (i / 4 ^ z) (hilbertD z (i % 4 ^ z))

theorem hilbertD_succ (z i : ℕ) :
    hilbertD (z + 1) i = quadPlace (2 ^ z) (i / 4 ^ z) (hilbertD z (i % 4 ^ z)) := rfl

theorem four_pow_pos (z : ℕ) : 0 < 4 ^ z := Nat.pow_pos (by decide)

theorem four_pow_succ' (z : ℕ) : 4 ^ (z + 1) = 4 * 4 ^ z := by rw [pow_succ, Nat.mul_comm]

/-- The top digit of an index below `4^(z+1)` is below 4. -/
theorem div_four_pow_lt {z i : ℕ} (hi : i < 4 ^ (z + 1)) : i / 4 ^ z < 4 := by
  rw [Nat.div_lt_iff_lt_mul (four_pow_pos z)]
  rw [four_pow_succ'] at hi
  omega

/-- The Hilbert order stays in the grid. -/
theorem hilbertD_lt : (z i : ℕ) → i < 4 ^ z → (hilbertD z i).1 < 2 ^ z ∧ (hilbertD z i).2 < 2 ^ z
  | 0, _, _ => ⟨Nat.one_pos, Nat.one_pos⟩
  | z + 1, i, hi => by
    have hq := div_four_pow_lt hi
    have hp := hilbertD_lt z (i % 4 ^ z) (Nat.mod_lt _ (four_pow_pos z))
    have h2 := two_pow_succ' z
    rw [hilbertD_succ]
    generalize i / 4 ^ z = q at hq ⊢
    have : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · rw [quadPlace_zero]; exact ⟨by omega, by omega⟩
    · rw [quadPlace_one]; exact ⟨by omega, by simp only; omega⟩
    · rw [quadPlace_two]; exact ⟨by simp only; omega, by simp only; omega⟩
    · rw [quadPlace_three]; exact ⟨by simp only; omega, by simp only; omega⟩

/-- It starts at `(0, 0)`. -/
theorem hilbertD_zero : (z : ℕ) → hilbertD z 0 = (0, 0)
  | 0 => rfl
  | z + 1 => by
    rw [hilbertD_succ, Nat.zero_div, Nat.zero_mod, hilbertD_zero z]
    simp [quadPlace]

/-- It ends at `(2^z - 1, 0)`. -/
theorem hilbertD_last : (z : ℕ) → hilbertD z (4 ^ z - 1) = (2 ^ z - 1, 0)
  | 0 => rfl
  | z + 1 => by
    have hN := four_pow_pos z
    have h4 := four_pow_succ' z
    have h2 := two_pow_succ' z
    have hq : (4 ^ (z + 1) - 1) / 4 ^ z = 3 := by
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    have hr : (4 ^ (z + 1) - 1) % 4 ^ z = 4 ^ z - 1 := by
      have := Nat.div_add_mod (4 ^ (z + 1) - 1) (4 ^ z)
      rw [hq] at this
      omega
    rw [hilbertD_succ, hq, hr, hilbertD_last z]
    have : 1 ≤ 2 ^ z := Nat.one_le_two_pow
    rw [quadPlace_three]
    exact Prod.ext (show 2 * 2 ^ z - 1 - 0 = 2 ^ (z + 1) - 1 by omega)
      (show 2 ^ z - 1 - (2 ^ z - 1) = 0 by omega)

/-! ## Consecutive tiles share an edge -/

/-- The symmetries and translations of `quadPlace` keep neighbours neighbours. -/
theorem quadPlace_adj {n q : ℕ} {p p' : ℕ × ℕ} (hp : p.1 < n ∧ p.2 < n) (hp' : p'.1 < n ∧ p'.2 < n)
    (h : AdjN p p') : AdjN (quadPlace n q p) (quadPlace n q p') := by
  unfold quadPlace AdjN at *
  split_ifs <;> simp only <;> omega

/-- Quotient and remainder of `r + N q` by `N` when `r < N`. -/
theorem div_mod_add_mul {N q r : ℕ} (hN : 0 < N) (hr : r < N) :
    (r + N * q) / N = q ∧ (r + N * q) % N = r := by
  constructor
  · rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hr, zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- Consecutive tiles of the Hilbert order share an edge. -/
theorem hilbertD_adj : (z i : ℕ) → i + 1 < 4 ^ z → AdjN (hilbertD z i) (hilbertD z (i + 1))
  | 0, i, hi => by simp at hi
  | z + 1, i, hi => by
    have hN := four_pow_pos z
    have h4 := four_pow_succ' z
    have h2 := two_pow_succ' z
    have hn : 1 ≤ 2 ^ z := Nat.one_le_two_pow
    have hdm := Nat.div_add_mod i (4 ^ z)
    have hr := Nat.mod_lt i hN
    have hq := div_four_pow_lt (show i < 4 ^ (z + 1) by omega)
    rw [hilbertD_succ, hilbertD_succ]
    by_cases hc : i % 4 ^ z + 1 < 4 ^ z
    · -- Same quadrant.
      have e : i + 1 = (i % 4 ^ z + 1) + 4 ^ z * (i / 4 ^ z) := by linarith
      obtain ⟨e1, e2⟩ := div_mod_add_mul (q := i / 4 ^ z) hN hc
      rw [e, e1, e2]
      exact quadPlace_adj (hilbertD_lt z _ hr) (hilbertD_lt z _ hc) (hilbertD_adj z _ hc)
    · -- Crossing into the next quadrant: the end of one piece meets the start of the next.
      have hr' : i % 4 ^ z = 4 ^ z - 1 := by omega
      have e : i + 1 = 0 + 4 ^ z * (i / 4 ^ z + 1) := by rw [mul_add]; linarith
      obtain ⟨e1, e2⟩ := div_mod_add_mul (q := i / 4 ^ z + 1) hN hN
      have hq3 : i / 4 ^ z + 1 < 4 := by
        have : 4 ^ z * (i / 4 ^ z + 1) < 4 ^ z * 4 := by linarith [e]
        exact Nat.lt_of_mul_lt_mul_left this
      rw [e, e1, e2, hr', hilbertD_last, hilbertD_zero]
      interval_cases h : i / 4 ^ z <;> simp [quadPlace, AdjN] <;> omega

/-! ## Every tile exactly once -/

theorem quadPlace_inj {n q q' : ℕ} {p p' : ℕ × ℕ} (hp : p.1 < n ∧ p.2 < n) (hp' : p'.1 < n ∧ p'.2 < n)
    (hq : q < 4) (hq' : q' < 4) (h : quadPlace n q p = quadPlace n q' p') : q = q' ∧ p = p' := by
  unfold quadPlace at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> (constructor <;> [omega; (ext <;> omega)])

/-- Distinct indices give distinct tiles. -/
theorem hilbertD_inj : (z i j : ℕ) → i < 4 ^ z → j < 4 ^ z → hilbertD z i = hilbertD z j → i = j
  | 0, i, j, hi, hj, _ => (Nat.lt_one_iff.mp hi).trans (Nat.lt_one_iff.mp hj).symm
  | z + 1, i, j, hi, hj, h => by
    have hN := four_pow_pos z
    rw [hilbertD_succ, hilbertD_succ] at h
    obtain ⟨hqq, hpp⟩ := quadPlace_inj (hilbertD_lt z _ (Nat.mod_lt i hN))
      (hilbertD_lt z _ (Nat.mod_lt j hN)) (div_four_pow_lt hi) (div_four_pow_lt hj) h
    have hrr := hilbertD_inj z _ _ (Nat.mod_lt i hN) (Nat.mod_lt j hN) hpp
    have hi' := Nat.div_add_mod i (4 ^ z)
    have hj' := Nat.div_add_mod j (4 ^ z)
    rw [hqq, hrr] at hi'
    omega

/-- The Hilbert order as a map from indices to tiles. -/
def decode (z : ℕ) (i : Fin (4 ^ z)) : Tile z :=
  (⟨(hilbertD z i).1, (hilbertD_lt z i i.2).1⟩, ⟨(hilbertD z i).2, (hilbertD_lt z i i.2).2⟩)

theorem hilbertD_injective (z : ℕ) : Function.Injective (decode z) := fun i j h => by
  have h1 := congrArg (fun t : Tile z => t.1.1) h
  have h2 := congrArg (fun t : Tile z => t.2.1) h
  simp only [decode] at h1 h2
  exact Fin.ext (hilbertD_inj z i j i.2 j.2 (Prod.ext h1 h2))

theorem card_tile (z : ℕ) : Fintype.card (Tile z) = 4 ^ z := by
  rw [Fintype.card_prod, Fintype.card_fin, ← mul_pow]
  norm_num

/-! ## A computable encoder -/

/-- Undo `quadPlace`: the quadrant of a point of the `2n × 2n` grid and its
position in the `n × n` grid before the symmetry. -/
def quadUnplace (n : ℕ) (P : ℕ × ℕ) : ℕ × (ℕ × ℕ) :=
  if P.1 < n then
    if P.2 < n then (0, (P.2, P.1)) else (1, (P.1, P.2 - n))
  else
    if P.2 < n then (3, (n - 1 - P.2, 2 * n - 1 - P.1)) else (2, (P.1 - n, P.2 - n))

theorem quadUnplace_quadPlace {n q : ℕ} {p : ℕ × ℕ} (hp : p.1 < n ∧ p.2 < n) (hq : q < 4) :
    quadUnplace n (quadPlace n q p) = (q, p) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨ha, hb⟩ := hp
  have : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · rw [quadPlace_zero]; unfold quadUnplace; rw [if_pos hb, if_pos ha]
  · rw [quadPlace_one]; unfold quadUnplace; rw [if_pos ha, if_neg (by simp only; omega)]
    exact Prod.ext rfl (Prod.ext rfl (by simp only; omega))
  · rw [quadPlace_two]; unfold quadUnplace
    rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
    exact Prod.ext rfl (Prod.ext (by simp only; omega) (by simp only; omega))
  · rw [quadPlace_three]; unfold quadUnplace
    rw [if_neg (by simp only; omega), if_pos (by simp only; omega)]
    exact Prod.ext rfl (Prod.ext (by simp only; omega) (by simp only; omega))

theorem quadUnplace_spec {n : ℕ} {P : ℕ × ℕ} (hP : P.1 < 2 * n ∧ P.2 < 2 * n) :
    (quadUnplace n P).1 < 4 ∧ ((quadUnplace n P).2.1 < n ∧ (quadUnplace n P).2.2 < n) ∧
      quadPlace n (quadUnplace n P).1 (quadUnplace n P).2 = P := by
  obtain ⟨X, Y⟩ := P
  obtain ⟨h1, h2⟩ := hP
  unfold quadUnplace
  split_ifs with ha hb hb
  · exact ⟨by simp only; omega, ⟨hb, ha⟩, by rw [quadPlace_zero]⟩
  · refine ⟨by simp only; omega, ⟨ha, by simp only; omega⟩, ?_⟩
    rw [quadPlace_one]
    exact Prod.ext rfl (by simp only; omega)
  · refine ⟨by simp only; omega, ⟨by simp only; omega, by simp only; omega⟩, ?_⟩
    rw [quadPlace_three]
    exact Prod.ext (by simp only; omega) (by simp only; omega)
  · refine ⟨by simp only; omega, ⟨by simp only; omega, by simp only; omega⟩, ?_⟩
    rw [quadPlace_two]
    exact Prod.ext (by simp only; omega) (by simp only; omega)

/-- The Hilbert index of a cell, computed recursively from its quadrant: the
inverse of `hilbertD`, with no choice involved. -/
def hilbertE : ℕ → ℕ × ℕ → ℕ
  | 0, _ => 0
  | z + 1, P => (quadUnplace (2 ^ z) P).1 * 4 ^ z + hilbertE z (quadUnplace (2 ^ z) P).2

theorem hilbertE_lt : (z : ℕ) → (P : ℕ × ℕ) → P.1 < 2 ^ z ∧ P.2 < 2 ^ z → hilbertE z P < 4 ^ z
  | 0, _, _ => four_pow_pos 0
  | z + 1, P, hP => by
    have h2 := two_pow_succ' z
    have h4 := four_pow_succ' z
    obtain ⟨hq, hp, _⟩ := quadUnplace_spec (n := 2 ^ z) (P := P) (by rw [← h2]; exact hP)
    have ih := hilbertE_lt z _ hp
    simp only [hilbertE]
    rw [h4]
    have : (quadUnplace (2 ^ z) P).1 = 0 ∨ (quadUnplace (2 ^ z) P).1 = 1 ∨
        (quadUnplace (2 ^ z) P).1 = 2 ∨ (quadUnplace (2 ^ z) P).1 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h] <;> omega

/-- `hilbertE` undoes `hilbertD`. -/
theorem hilbertE_hilbertD : (z i : ℕ) → i < 4 ^ z → hilbertE z (hilbertD z i) = i
  | 0, i, hi => (Nat.lt_one_iff.mp hi).symm
  | z + 1, i, hi => by
    have hN := four_pow_pos z
    have hr := Nat.mod_lt i hN
    rw [hilbertD_succ, hilbertE,
      quadUnplace_quadPlace (hilbertD_lt z _ hr) (div_four_pow_lt hi), hilbertE_hilbertD z _ hr]
    exact Nat.div_add_mod' i (4 ^ z)

/-- `hilbertD` undoes `hilbertE`. -/
theorem hilbertD_hilbertE : (z : ℕ) → (P : ℕ × ℕ) → P.1 < 2 ^ z ∧ P.2 < 2 ^ z →
    hilbertD z (hilbertE z P) = P
  | 0, P, hP => by
    obtain ⟨X, Y⟩ := P
    obtain ⟨hX, hY⟩ := hP
    exact Prod.ext (show 0 = X by omega) (show 0 = Y by omega)
  | z + 1, P, hP => by
    have hN := four_pow_pos z
    have h2 := two_pow_succ' z
    obtain ⟨hq, hp, hplace⟩ := quadUnplace_spec (n := 2 ^ z) (P := P) (by rw [← h2]; exact hP)
    have he := hilbertE_lt z _ hp
    obtain ⟨e1, e2⟩ := div_mod_add_mul (q := (quadUnplace (2 ^ z) P).1) hN he
    rw [hilbertE, hilbertD_succ, Nat.add_comm, Nat.mul_comm,
      e1, e2, hilbertD_hilbertE z _ hp, hplace]

/-- The Hilbert index of a tile, computed by `hilbertE`. -/
def encode (z : ℕ) (t : Tile z) : Fin (4 ^ z) :=
  ⟨hilbertE z (t.1.1, t.2.1), hilbertE_lt z _ ⟨t.1.2, t.2.2⟩⟩

theorem encode_decode (z : ℕ) (i : Fin (4 ^ z)) : encode z (decode z i) = i :=
  Fin.ext (hilbertE_hilbertD z i i.2)

theorem decode_encode (z : ℕ) (t : Tile z) : decode z (encode z t) = t := by
  have h := hilbertD_hilbertE z (t.1.1, t.2.1) ⟨t.1.2, t.2.2⟩
  ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- The Hilbert order visits every tile exactly once: `decode` and `encode` are
inverse bijections, both computable. -/
def hilbertEquiv (z : ℕ) : Fin (4 ^ z) ≃ Tile z where
  toFun := decode z
  invFun := encode z
  left_inv := encode_decode z
  right_inv := decode_encode z

/-- `encode` computes: the last tile at zoom 2, `(3, 0)`, has index 15. -/
example : (encode 2 (⟨3, by norm_num⟩, ⟨0, by norm_num⟩)).1 = 15 := by decide

/-- Consecutive tiles of the Hilbert order share an edge. -/
theorem hilbert_adjacent {z : ℕ} (i : Fin (4 ^ z)) (h : i.1 + 1 < 4 ^ z) :
    Adjacent (decode z i) (decode z ⟨i.1 + 1, h⟩) :=
  hilbertD_adj z i h

/-! ## Nested like the quadtree -/

theorem quadPlace_halve {m q : ℕ} {p : ℕ × ℕ} (hp : p.1 < 2 * m ∧ p.2 < 2 * m) :
    ((quadPlace (2 * m) q p).1 / 2, (quadPlace (2 * m) q p).2 / 2) = quadPlace m q (p.1 / 2, p.2 / 2) := by
  unfold quadPlace
  split_ifs <;> ext <;> simp only <;> omega

/-- Halving the tile visited `i`-th at zoom `z + 1` gives the tile visited
`i / 4`-th at zoom `z`. -/
theorem hilbertD_halve : (z i : ℕ) → i < 4 ^ (z + 1) →
    ((hilbertD (z + 1) i).1 / 2, (hilbertD (z + 1) i).2 / 2) = hilbertD z (i / 4)
  | 0, i, hi => by
    norm_num at hi
    interval_cases i <;> rfl
  | z + 1, i, hi => by
    have hN := four_pow_pos (z + 1)
    have h4 := four_pow_succ' z
    have h2 := two_pow_succ' z
    have hr := Nat.mod_lt i hN
    have ih := hilbertD_halve z (i % 4 ^ (z + 1)) hr
    have hq : (i / 4) / 4 ^ z = i / 4 ^ (z + 1) := by rw [Nat.div_div_eq_div_mul, h4]
    have hm : (i / 4) % 4 ^ z = i % 4 ^ (z + 1) / 4 := by
      rw [h4, Nat.mod_mul_right_div_self]
    rw [hilbertD_succ (z + 1), hilbertD_succ z (i / 4), hq, hm, ← ih, h2]
    exact quadPlace_halve (by rw [← h2]; exact hilbertD_lt (z + 1) _ hr)

/-- The Hilbert order is nested like the quadtree: the parent of the tile
visited `i`-th at zoom `z + 1` is the tile visited `i / 4`-th at zoom `z`. -/
theorem parent_hilbert_decode {z : ℕ} (i : Fin (4 ^ (z + 1))) :
    parent (decode (z + 1) i) =
      decode z ⟨i.1 / 4, by have := i.2; have := four_pow_succ' z; omega⟩ := by
  have h := hilbertD_halve z i i.2
  ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- The ancestor `k` generations up of the tile visited `i`-th at zoom `z + k` is
the tile visited `i / 4^k`-th at zoom `z`. -/
theorem ancestor_decode {z : ℕ} : (k : ℕ) → (i : Fin (4 ^ (z + k))) →
    ancestor k (decode (z + k) i) =
      decode z ⟨i.1 / 4 ^ k, by
        rw [Nat.div_lt_iff_lt_mul (four_pow_pos k), ← pow_add]; exact i.2⟩
  | 0, i => by simp [ancestor]
  | k + 1, i => by
    show ancestor k (parent (decode (z + k + 1) i)) = _
    rw [parent_hilbert_decode, ancestor_decode k]
    congr 2
    rw [Nat.div_div_eq_div_mul, ← pow_succ']

/-! ## Subtrees are intervals of indices -/

/-- `e / N = p` exactly when `e` lies in `[p N, (p + 1) N)`. -/
theorem div_eq_iff_mem_interval {e p N : ℕ} (hN : 0 < N) : e / N = p ↔ p * N ≤ e ∧ e < (p + 1) * N := by
  rw [le_antisymm_iff, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hN, Nat.le_div_iff_mul_le hN, and_comm]

/-- A tile at zoom `z + k` descends from the tile `s` at zoom `z` exactly when its
Hilbert index has `s`'s index as its base-4 prefix. -/
theorem ancestor_eq_iff_encode {z k : ℕ} (t : Tile (z + k)) (s : Tile z) :
    ancestor k t = s ↔ (encode (z + k) t).1 / 4 ^ k = (encode z s).1 := by
  have h := ancestor_decode k (encode (z + k) t)
  rw [decode_encode] at h
  rw [h]
  constructor
  · intro hs
    have := congrArg (encode z) hs
    rw [encode_decode] at this
    exact congrArg Fin.val this
  · intro he
    rw [← decode_encode z s]
    exact congrArg (decode z) (Fin.ext he)

/-- So the descendants `k` generations down of a tile are exactly the tiles
whose Hilbert indices fill one interval of length `4^k`. -/
theorem ancestor_eq_iff_encode_mem_interval {z k : ℕ} (t : Tile (z + k)) (s : Tile z) :
    ancestor k t = s ↔
      (encode z s).1 * 4 ^ k ≤ (encode (z + k) t).1 ∧ (encode (z + k) t).1 < ((encode z s).1 + 1) * 4 ^ k := by
  rw [ancestor_eq_iff_encode, div_eq_iff_mem_interval (four_pow_pos k)]

/-- The same, in terms of `decode`: the tile visited `i`-th at zoom `z + k` descends
from the tile visited `p`-th at zoom `z` exactly when `i / 4^k = p`. -/
theorem ancestor_decode_eq_iff {z k : ℕ} (i : Fin (4 ^ (z + k))) (p : Fin (4 ^ z)) :
    ancestor k (decode (z + k) i) = decode z p ↔ i.1 / 4 ^ k = p.1 := by
  rw [ancestor_eq_iff_encode, encode_decode, encode_decode]

/-- The subtree of a tile, `k` generations deep, is the image under `decode` of
the interval of indices with that tile's index as prefix. -/
theorem subtree_eq_decode_interval {z k : ℕ} (s : Tile z) :
    {t : Tile (z + k) | ancestor k t = s} =
      decode (z + k) '' {i | (encode z s).1 * 4 ^ k ≤ i.1 ∧ i.1 < ((encode z s).1 + 1) * 4 ^ k} := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro h
    exact ⟨encode (z + k) t, (ancestor_eq_iff_encode_mem_interval t s).mp h, decode_encode _ t⟩
  · rintro ⟨i, hi, rfl⟩
    rw [ancestor_eq_iff_encode_mem_interval, encode_decode]
    exact hi

/-! ## The Morton order is not adjacent -/

theorem morton_zero_zero : (z : ℕ) → morton z 0 0 = 0
  | 0 => rfl
  | z + 1 => by simp [morton, morton_zero_zero z, childDigit]

/-- At every zoom `z ≥ 1`, the Morton codes 1 and 2 are the tiles `(1, 0)` and
`(0, 1)`, which do not share an edge: the Z-order is not an adjacent order. -/
theorem morton_not_adjacent {z : ℕ} (hz : 1 ≤ z) :
    ∃ s t : Tile z, (mortonEquiv z s).1 = 1 ∧ (mortonEquiv z t).1 = 2 ∧ ¬ Adjacent s t := by
  obtain ⟨w, rfl⟩ : ∃ w, z = w + 1 := ⟨z - 1, by omega⟩
  have h2 : 1 < 2 ^ (w + 1) := Nat.one_lt_two_pow (by omega)
  refine ⟨(⟨1, h2⟩, ⟨0, by omega⟩), (⟨0, by omega⟩, ⟨1, h2⟩), ?_, ?_, ?_⟩
  · rw [mortonEquiv_val]; simp [morton, morton_zero_zero, childDigit]
  · rw [mortonEquiv_val]; simp [morton, morton_zero_zero, childDigit]
  · simp [Adjacent, AdjN]

end Geodesy.Tiles
