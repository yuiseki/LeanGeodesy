import LeanGeodesy.Spherical.Packing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Local planar approximation on the unit sphere

On the unit sphere the great-circle distance `θ = geoDist x y` and the chord
`chordDist x y = 2 sin (θ / 2)` (`chordDist_eq_two_sin_half`) agree to third order:

```
0 ≤ geoDist x y - chordDist x y ≤ geoDist x y ^ 3 / 24
```

The upper bound comes from `x - x³/6 < sin x` for `x > 0` (Mathlib's `Real.sin_gt_sub_cube`)
applied at `x = θ / 2`; the lower bound from `sin x < x`.

What is proved: the two-sided bound `geoDist_sub_chordDist_le` and
`chordDist_le_geoDist'`, and the rearranged form `geoDist_le_chordDist_add`.

What is not proved: the matching lower bound of order `θ³` (the constant `1/24` is the
optimal leading coefficient, but its sharpness is not formalised), and any version on
the ellipsoid.
-/

namespace Geodesy.SphereEllipsoid

open Real Geodesy.Spherical

/-- The chord never exceeds the arc: `chordDist x y ≤ geoDist x y`. (The same fact is
`Geodesy.Spherical.chordDist_le_geoDist` in `Spherical/Topology.lean`; it is reproved here so
that this file depends only on `Spherical/Packing.lean`.) -/
theorem chordDist_le_geoDist' (x y : UnitSphere) : chordDist x y ≤ geoDist x y := by
  rw [chordDist_eq_two_sin_half]
  rcases (geoDist_nonneg x y).eq_or_lt with h | h
  · rw [← h]; simp
  · linarith [sin_lt (half_pos h)]

/-- **Local planar approximation.** The arc exceeds the chord by at most `θ³ / 24`. -/
theorem geoDist_sub_chordDist_le (x y : UnitSphere) :
    geoDist x y - chordDist x y ≤ geoDist x y ^ 3 / 24 := by
  rw [chordDist_eq_two_sin_half]
  rcases (geoDist_nonneg x y).eq_or_lt with h | h
  · rw [← h]; simp
  · have := sin_gt_sub_cube (half_pos h)
    nlinarith

/-- Both bounds together. -/
theorem geoDist_sub_chordDist_mem_Icc (x y : UnitSphere) :
    geoDist x y - chordDist x y ∈ Set.Icc 0 (geoDist x y ^ 3 / 24) :=
  ⟨sub_nonneg.mpr (chordDist_le_geoDist' x y), geoDist_sub_chordDist_le x y⟩

/-- Equivalent form: `geoDist x y ≤ chordDist x y + geoDist x y ^ 3 / 24`. -/
theorem geoDist_le_chordDist_add (x y : UnitSphere) :
    geoDist x y ≤ chordDist x y + geoDist x y ^ 3 / 24 := by
  linarith [geoDist_sub_chordDist_le x y]

end Geodesy.SphereEllipsoid
