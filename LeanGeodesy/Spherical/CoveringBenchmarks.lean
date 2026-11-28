import LeanGeodesy.Spherical.CoveringCert
import LeanGeodesy.Spherical.Packing

/-!
# Covering certificates for the regular octahedron and tetrahedron

Checked instances of `LeanGeodesy.Spherical.CoveringCert.checkCover`. The trees
come from `scripts/covering_cert/gen_cert.py`; Lean re-checks every leaf.

* Octahedron `±e₁, ±e₂, ±e₃`: the certificate has one leaf per cube face and
  accepts `R = 1/3`, which is exactly `cos² r` at the true covering radius
  `r = arccos (1/√3)`, so it bounds the covering radius from above with no
  slack. A deep hole is the cube corner `(1,1,1)`, which every box meets at a
  corner of its own, and there the margin is zero rather than negative. The
  matching lower bound is the hole direction `(1,1,1)/√3`
  (`arccos_le_coveringRadius_of_hole`). Together:
  `coveringRadius_octahedron6 : coveringRadius _ octahedron6 = arccos (1/√3)`.
* Tetrahedron: its holes are at the cube corners, which no box can have as an
  interior point, so the checker proves `R = 11/100` (a few thousandths below
  `cos² r = 1/9`), with 360 leaves. The hole direction `-(1,1,1)/√3` gives the
  lower bound `arccos (1/3)`. The two bounds bracket the covering radius of the
  tetrahedron between `arccos (1/3) ≈ 70.5288°` and `arccos √(11/100) ≈ 70.63°`.
  The exact value `arccos (1/3)` is proved separately, without any certificate,
  from the octahedron (`coveringRadius_tetrahedron4`).
-/

namespace Geodesy.Spherical

open Real Geodesic

/-! ## A hole bounds the covering radius from below -/

theorem coveringRadius_nonneg {n : ℕ} (hn : 1 ≤ n) (p : Fin n → UnitSphere) :
    0 ≤ coveringRadius hn p := by
  unfold coveringRadius
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, rfl⟩
  exact Finset.le_inf' _ _ fun i _ => geoDist_nonneg _ _

theorem coveringRadius_le_pi {n : ℕ} (hn : 1 ≤ n) (p : Fin n → UnitSphere) :
    coveringRadius hn p ≤ π := by
  rw [coveringRadius_le_iff]
  intro x
  exact ⟨⟨0, by omega⟩, geoDist_le_pi _ _⟩

/-- If a unit direction `u` has `⟪p i, u⟫ ≤ c` for every point (`u` is a hole of
depth `arccos c`), then the covering radius is at least `arccos c`. -/
theorem arccos_le_coveringRadius_of_hole {n : ℕ} (hn : 1 ≤ n) (p : Fin n → UnitSphere)
    (u : UnitSphere) {c : ℝ} (hc : ∀ i, inner ℝ (p i).1 u.1 ≤ c) :
    arccos c ≤ coveringRadius hn p := by
  have h0 := coveringRadius_nonneg hn p
  have hπ := coveringRadius_le_pi hn p
  have hcov : IsCovering p (coveringRadius hn p) := isCovering_coveringRadius hn p
  have hcos := cos_le_of_supportPlane h0 hπ hcov u hc
  calc arccos c ≤ arccos (cos (coveringRadius hn p)) := arccos_le_arccos_of_le hcos
    _ = coveringRadius hn p := arccos_cos h0 hπ

private theorem norm_vec3_eq {x y z c : ℝ} (h : x ^ 2 + y ^ 2 + z ^ 2 = c ^ 2) (hc : 0 ≤ c) :
    ‖vec3 x y z‖ = c := by
  have := norm_vec3_sq x y z
  rw [h] at this
  exact (sq_eq_sq₀ (norm_nonneg _) hc).1 this

/-! ## The octahedron -/

/-- The octahedron's vertices as rational directions. -/
def octaQ : Fin 6 → Q3 :=
  ![(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]

/-- The certificate for the octahedron: one leaf per face. -/
def octaTrees : Fin 3 → Bool → CoverTree :=
    fun a b => match a.val, b with
      | 0, true => .leaf 0
      | 0, false => .leaf 1
      | 1, true => .leaf 2
      | 1, false => .leaf 3
      | 2, true => .leaf 4
      | 2, false => .leaf 5
      | _, _ => .leaf 0

theorem octaCert_valid : checkCover octaQ (1 / 3) octaTrees = true := by decide +kernel

theorem octahedron6_realizes : Realizes octaQ octahedron6 := by
  intro i
  have h1 : ‖vec3 (1 : ℝ) 0 0‖ = 1 := norm_vec3_eq (by norm_num) (by norm_num)
  fin_cases i <;> simp [octahedron6, octaQ, qv, vec3_smul] <;>
    (rw [norm_vec3_eq (c := 1) (by norm_num) (by norm_num)]; simp)

/-- The covering radius of the regular octahedron is exactly `arccos (1/√3)`:
the checker gives the upper bound at `R = 1/3`, the hole `(1,1,1)/√3` the lower
bound. -/
theorem coveringRadius_octahedron6 :
    coveringRadius (by norm_num : 1 ≤ 6) octahedron6 = arccos (1 / √3) := by
  have hup : coveringRadius (by norm_num : 1 ≤ 6) octahedron6 ≤ arccos √((1 / 3 : ℚ) : ℝ) :=
    coveringRadius_le_of_checkCover (by norm_num) octaCert_valid octahedron6_realizes
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have hs : √((1 / 3 : ℚ) : ℝ) = 1 / √3 := by
    have : ((1 / 3 : ℚ) : ℝ) = (1 / √3) ^ 2 := by
      push_cast; rw [div_pow, h3]; norm_num
    rw [this, Real.sqrt_sq (by positivity)]
  rw [hs] at hup
  refine le_antisymm hup ?_
  have hu : ‖vec3 (1 / √3) (1 / √3) (1 / √3)‖ = 1 :=
    norm_vec3_eq (by rw [div_pow, h3]; norm_num) (by norm_num)
  refine arccos_le_coveringRadius_of_hole (by norm_num) octahedron6
    ⟨vec3 (1 / √3) (1 / √3) (1 / √3), hu⟩ (c := 1 / √3) fun i => ?_
  have hpos : (0 : ℝ) ≤ 1 / √3 := by positivity
  fin_cases i <;> simp [octahedron6, inner_vec3]

/-! ## The tetrahedron -/

/-- The tetrahedron's vertices as rational directions. -/
def tetraQ : Fin 4 → Q3 := ![(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]

/-- The certificate for the tetrahedron at `R = 11/100`, from `gen_cert.py`. -/
def tetraTrees : Fin 3 → Bool → CoverTree :=
    fun a b => match a.val, b with
      | 0, true => .cutU (0 : ℚ) (.cutV (0 : ℚ) (.leaf 1) (.cutU (-1/2 : ℚ) (.cutV (1/2 : ℚ) (.leaf 1) (.cutU (-3/4 : ℚ) (.cutV (3/4 : ℚ) (.leaf 1) (.cutU (-7/8 : ℚ) (.cutV (7/8 : ℚ) (.leaf 1) (.cutU (-15/16 : ℚ) (.cutV (15/16 : ℚ) (.leaf 1) (.cutU (-31/32 : ℚ) (.cutV (31/32 : ℚ) (.leaf 1) (.cutU (-63/64 : ℚ) (.cutV (63/64 : ℚ) (.leaf 1) (.cutU (-127/128 : ℚ) (.cutV (127/128 : ℚ) (.leaf 1) (.cutU (-255/256 : ℚ) (.leaf 1) (.leaf 0))) (.cutV (127/128 : ℚ) (.leaf 0) (.leaf 0)))) (.cutV (63/64 : ℚ) (.cutU (-125/128 : ℚ) (.leaf 1) (.leaf 0)) (.leaf 0)))) (.cutV (31/32 : ℚ) (.cutU (-61/64 : ℚ) (.leaf 1) (.leaf 0)) (.leaf 0)))) (.cutV (15/16 : ℚ) (.cutU (-29/32 : ℚ) (.leaf 1) (.leaf 0)) (.leaf 0)))) (.cutV (7/8 : ℚ) (.cutU (-13/16 : ℚ) (.leaf 1) (.leaf 0)) (.leaf 0)))) (.cutV (3/4 : ℚ) (.cutU (-5/8 : ℚ) (.leaf 1) (.leaf 0)) (.leaf 0)))) (.cutV (1/2 : ℚ) (.cutU (-1/4 : ℚ) (.leaf 1) (.leaf 0)) (.leaf 0)))) (.cutV (0 : ℚ) (.cutU (1/2 : ℚ) (.cutV (-1/2 : ℚ) (.leaf 1) (.cutU (1/4 : ℚ) (.leaf 1) (.leaf 0))) (.cutV (-1/2 : ℚ) (.cutU (3/4 : ℚ) (.cutV (-3/4 : ℚ) (.leaf 1) (.cutU (5/8 : ℚ) (.leaf 1) (.leaf 0))) (.cutV (-3/4 : ℚ) (.cutU (7/8 : ℚ) (.cutV (-7/8 : ℚ) (.leaf 1) (.cutU (13/16 : ℚ) (.leaf 1) (.leaf 0))) (.cutV (-7/8 : ℚ) (.cutU (15/16 : ℚ) (.cutV (-15/16 : ℚ) (.leaf 1) (.cutU (29/32 : ℚ) (.leaf 1) (.leaf 0))) (.cutV (-15/16 : ℚ) (.cutU (31/32 : ℚ) (.cutV (-31/32 : ℚ) (.leaf 1) (.cutU (61/64 : ℚ) (.leaf 1) (.leaf 0))) (.cutV (-31/32 : ℚ) (.cutU (63/64 : ℚ) (.cutV (-63/64 : ℚ) (.leaf 1) (.cutU (125/128 : ℚ) (.leaf 0) (.leaf 0))) (.cutV (-63/64 : ℚ) (.cutU (127/128 : ℚ) (.cutV (-127/128 : ℚ) (.leaf 1) (.leaf 0)) (.cutV (-127/128 : ℚ) (.cutU (255/256 : ℚ) (.leaf 1) (.leaf 0)) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))
      | 0, false => .cutU (0 : ℚ) (.cutV (0 : ℚ) (.cutU (-1/2 : ℚ) (.cutV (-1/2 : ℚ) (.cutU (-3/4 : ℚ) (.cutV (-3/4 : ℚ) (.cutU (-7/8 : ℚ) (.cutV (-7/8 : ℚ) (.cutU (-15/16 : ℚ) (.cutV (-15/16 : ℚ) (.cutU (-31/32 : ℚ) (.cutV (-31/32 : ℚ) (.cutU (-63/64 : ℚ) (.cutV (-63/64 : ℚ) (.cutU (-127/128 : ℚ) (.cutV (-127/128 : ℚ) (.cutU (-255/256 : ℚ) (.leaf 3) (.leaf 2)) (.leaf 3)) (.cutV (-127/128 : ℚ) (.leaf 2) (.leaf 2))) (.leaf 3)) (.cutV (-63/64 : ℚ) (.leaf 2) (.cutU (-125/128 : ℚ) (.leaf 3) (.leaf 2)))) (.leaf 3)) (.cutV (-31/32 : ℚ) (.leaf 2) (.cutU (-61/64 : ℚ) (.leaf 3) (.leaf 2)))) (.leaf 3)) (.cutV (-15/16 : ℚ) (.leaf 2) (.cutU (-29/32 : ℚ) (.leaf 3) (.leaf 2)))) (.leaf 3)) (.cutV (-7/8 : ℚ) (.leaf 2) (.cutU (-13/16 : ℚ) (.leaf 3) (.leaf 2)))) (.leaf 3)) (.cutV (-3/4 : ℚ) (.leaf 2) (.cutU (-5/8 : ℚ) (.leaf 3) (.leaf 2)))) (.leaf 3)) (.cutV (-1/2 : ℚ) (.leaf 2) (.cutU (-1/4 : ℚ) (.leaf 3) (.leaf 2)))) (.leaf 3)) (.cutV (0 : ℚ) (.leaf 2) (.cutU (1/2 : ℚ) (.cutV (1/2 : ℚ) (.cutU (1/4 : ℚ) (.leaf 3) (.leaf 2)) (.leaf 3)) (.cutV (1/2 : ℚ) (.leaf 2) (.cutU (3/4 : ℚ) (.cutV (3/4 : ℚ) (.cutU (5/8 : ℚ) (.leaf 3) (.leaf 2)) (.leaf 3)) (.cutV (3/4 : ℚ) (.leaf 2) (.cutU (7/8 : ℚ) (.cutV (7/8 : ℚ) (.cutU (13/16 : ℚ) (.leaf 3) (.leaf 2)) (.leaf 3)) (.cutV (7/8 : ℚ) (.leaf 2) (.cutU (15/16 : ℚ) (.cutV (15/16 : ℚ) (.cutU (29/32 : ℚ) (.leaf 3) (.leaf 2)) (.leaf 3)) (.cutV (15/16 : ℚ) (.leaf 2) (.cutU (31/32 : ℚ) (.cutV (31/32 : ℚ) (.cutU (61/64 : ℚ) (.leaf 3) (.leaf 2)) (.leaf 3)) (.cutV (31/32 : ℚ) (.leaf 2) (.cutU (63/64 : ℚ) (.cutV (63/64 : ℚ) (.cutU (125/128 : ℚ) (.leaf 2) (.leaf 2)) (.leaf 3)) (.cutV (63/64 : ℚ) (.leaf 2) (.cutU (127/128 : ℚ) (.cutV (127/128 : ℚ) (.leaf 2) (.leaf 3)) (.cutV (127/128 : ℚ) (.leaf 2) (.cutU (255/256 : ℚ) (.leaf 3) (.leaf 2)))))))))))))))))
      | 1, true => .cutU (0 : ℚ) (.cutV (0 : ℚ) (.leaf 2) (.cutU (-1/2 : ℚ) (.cutV (1/2 : ℚ) (.leaf 2) (.cutU (-3/4 : ℚ) (.cutV (3/4 : ℚ) (.leaf 2) (.cutU (-7/8 : ℚ) (.cutV (7/8 : ℚ) (.leaf 2) (.cutU (-15/16 : ℚ) (.cutV (15/16 : ℚ) (.leaf 2) (.cutU (-31/32 : ℚ) (.cutV (31/32 : ℚ) (.leaf 2) (.cutU (-63/64 : ℚ) (.cutV (63/64 : ℚ) (.leaf 2) (.cutU (-127/128 : ℚ) (.cutV (127/128 : ℚ) (.leaf 2) (.cutU (-255/256 : ℚ) (.leaf 2) (.leaf 0))) (.cutV (127/128 : ℚ) (.leaf 0) (.leaf 0)))) (.cutV (63/64 : ℚ) (.cutU (-125/128 : ℚ) (.leaf 2) (.leaf 0)) (.leaf 0)))) (.cutV (31/32 : ℚ) (.cutU (-61/64 : ℚ) (.leaf 2) (.leaf 0)) (.leaf 0)))) (.cutV (15/16 : ℚ) (.cutU (-29/32 : ℚ) (.leaf 2) (.leaf 0)) (.leaf 0)))) (.cutV (7/8 : ℚ) (.cutU (-13/16 : ℚ) (.leaf 2) (.leaf 0)) (.leaf 0)))) (.cutV (3/4 : ℚ) (.cutU (-5/8 : ℚ) (.leaf 2) (.leaf 0)) (.leaf 0)))) (.cutV (1/2 : ℚ) (.cutU (-1/4 : ℚ) (.leaf 2) (.leaf 0)) (.leaf 0)))) (.cutV (0 : ℚ) (.cutU (1/2 : ℚ) (.cutV (-1/2 : ℚ) (.leaf 2) (.cutU (1/4 : ℚ) (.leaf 2) (.leaf 0))) (.cutV (-1/2 : ℚ) (.cutU (3/4 : ℚ) (.cutV (-3/4 : ℚ) (.leaf 2) (.cutU (5/8 : ℚ) (.leaf 2) (.leaf 0))) (.cutV (-3/4 : ℚ) (.cutU (7/8 : ℚ) (.cutV (-7/8 : ℚ) (.leaf 2) (.cutU (13/16 : ℚ) (.leaf 2) (.leaf 0))) (.cutV (-7/8 : ℚ) (.cutU (15/16 : ℚ) (.cutV (-15/16 : ℚ) (.leaf 2) (.cutU (29/32 : ℚ) (.leaf 2) (.leaf 0))) (.cutV (-15/16 : ℚ) (.cutU (31/32 : ℚ) (.cutV (-31/32 : ℚ) (.leaf 2) (.cutU (61/64 : ℚ) (.leaf 2) (.leaf 0))) (.cutV (-31/32 : ℚ) (.cutU (63/64 : ℚ) (.cutV (-63/64 : ℚ) (.leaf 2) (.cutU (125/128 : ℚ) (.leaf 0) (.leaf 0))) (.cutV (-63/64 : ℚ) (.cutU (127/128 : ℚ) (.cutV (-127/128 : ℚ) (.leaf 2) (.leaf 0)) (.cutV (-127/128 : ℚ) (.cutU (255/256 : ℚ) (.leaf 2) (.leaf 0)) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))
      | 1, false => .cutU (0 : ℚ) (.cutV (0 : ℚ) (.cutU (-1/2 : ℚ) (.cutV (-1/2 : ℚ) (.cutU (-3/4 : ℚ) (.cutV (-3/4 : ℚ) (.cutU (-7/8 : ℚ) (.cutV (-7/8 : ℚ) (.cutU (-15/16 : ℚ) (.cutV (-15/16 : ℚ) (.cutU (-31/32 : ℚ) (.cutV (-31/32 : ℚ) (.cutU (-63/64 : ℚ) (.cutV (-63/64 : ℚ) (.cutU (-127/128 : ℚ) (.cutV (-127/128 : ℚ) (.cutU (-255/256 : ℚ) (.leaf 1) (.leaf 3)) (.leaf 1)) (.cutV (-127/128 : ℚ) (.leaf 3) (.leaf 1))) (.leaf 1)) (.cutV (-63/64 : ℚ) (.leaf 3) (.cutU (-125/128 : ℚ) (.leaf 1) (.leaf 1)))) (.leaf 1)) (.cutV (-31/32 : ℚ) (.leaf 3) (.cutU (-61/64 : ℚ) (.leaf 1) (.leaf 3)))) (.leaf 1)) (.cutV (-15/16 : ℚ) (.leaf 3) (.cutU (-29/32 : ℚ) (.leaf 1) (.leaf 3)))) (.leaf 1)) (.cutV (-7/8 : ℚ) (.leaf 3) (.cutU (-13/16 : ℚ) (.leaf 1) (.leaf 3)))) (.leaf 1)) (.cutV (-3/4 : ℚ) (.leaf 3) (.cutU (-5/8 : ℚ) (.leaf 1) (.leaf 3)))) (.leaf 1)) (.cutV (-1/2 : ℚ) (.leaf 3) (.cutU (-1/4 : ℚ) (.leaf 1) (.leaf 3)))) (.leaf 1)) (.cutV (0 : ℚ) (.leaf 3) (.cutU (1/2 : ℚ) (.cutV (1/2 : ℚ) (.cutU (1/4 : ℚ) (.leaf 1) (.leaf 3)) (.leaf 1)) (.cutV (1/2 : ℚ) (.leaf 3) (.cutU (3/4 : ℚ) (.cutV (3/4 : ℚ) (.cutU (5/8 : ℚ) (.leaf 1) (.leaf 3)) (.leaf 1)) (.cutV (3/4 : ℚ) (.leaf 3) (.cutU (7/8 : ℚ) (.cutV (7/8 : ℚ) (.cutU (13/16 : ℚ) (.leaf 1) (.leaf 3)) (.leaf 1)) (.cutV (7/8 : ℚ) (.leaf 3) (.cutU (15/16 : ℚ) (.cutV (15/16 : ℚ) (.cutU (29/32 : ℚ) (.leaf 1) (.leaf 3)) (.leaf 1)) (.cutV (15/16 : ℚ) (.leaf 3) (.cutU (31/32 : ℚ) (.cutV (31/32 : ℚ) (.cutU (61/64 : ℚ) (.leaf 1) (.leaf 3)) (.leaf 1)) (.cutV (31/32 : ℚ) (.leaf 3) (.cutU (63/64 : ℚ) (.cutV (63/64 : ℚ) (.cutU (125/128 : ℚ) (.leaf 1) (.leaf 3)) (.leaf 1)) (.cutV (63/64 : ℚ) (.leaf 3) (.cutU (127/128 : ℚ) (.cutV (127/128 : ℚ) (.leaf 1) (.leaf 1)) (.cutV (127/128 : ℚ) (.leaf 3) (.cutU (255/256 : ℚ) (.leaf 1) (.leaf 3)))))))))))))))))
      | 2, true => .cutU (0 : ℚ) (.cutV (0 : ℚ) (.leaf 3) (.cutU (-1/2 : ℚ) (.cutV (1/2 : ℚ) (.leaf 3) (.cutU (-3/4 : ℚ) (.cutV (3/4 : ℚ) (.leaf 3) (.cutU (-7/8 : ℚ) (.cutV (7/8 : ℚ) (.leaf 3) (.cutU (-15/16 : ℚ) (.cutV (15/16 : ℚ) (.leaf 3) (.cutU (-31/32 : ℚ) (.cutV (31/32 : ℚ) (.leaf 3) (.cutU (-63/64 : ℚ) (.cutV (63/64 : ℚ) (.leaf 3) (.cutU (-127/128 : ℚ) (.cutV (127/128 : ℚ) (.leaf 3) (.cutU (-255/256 : ℚ) (.leaf 3) (.leaf 0))) (.cutV (127/128 : ℚ) (.leaf 0) (.leaf 0)))) (.cutV (63/64 : ℚ) (.cutU (-125/128 : ℚ) (.leaf 3) (.leaf 0)) (.leaf 0)))) (.cutV (31/32 : ℚ) (.cutU (-61/64 : ℚ) (.leaf 3) (.leaf 0)) (.leaf 0)))) (.cutV (15/16 : ℚ) (.cutU (-29/32 : ℚ) (.leaf 3) (.leaf 0)) (.leaf 0)))) (.cutV (7/8 : ℚ) (.cutU (-13/16 : ℚ) (.leaf 3) (.leaf 0)) (.leaf 0)))) (.cutV (3/4 : ℚ) (.cutU (-5/8 : ℚ) (.leaf 3) (.leaf 0)) (.leaf 0)))) (.cutV (1/2 : ℚ) (.cutU (-1/4 : ℚ) (.leaf 3) (.leaf 0)) (.leaf 0)))) (.cutV (0 : ℚ) (.cutU (1/2 : ℚ) (.cutV (-1/2 : ℚ) (.leaf 3) (.cutU (1/4 : ℚ) (.leaf 3) (.leaf 0))) (.cutV (-1/2 : ℚ) (.cutU (3/4 : ℚ) (.cutV (-3/4 : ℚ) (.leaf 3) (.cutU (5/8 : ℚ) (.leaf 3) (.leaf 0))) (.cutV (-3/4 : ℚ) (.cutU (7/8 : ℚ) (.cutV (-7/8 : ℚ) (.leaf 3) (.cutU (13/16 : ℚ) (.leaf 3) (.leaf 0))) (.cutV (-7/8 : ℚ) (.cutU (15/16 : ℚ) (.cutV (-15/16 : ℚ) (.leaf 3) (.cutU (29/32 : ℚ) (.leaf 3) (.leaf 0))) (.cutV (-15/16 : ℚ) (.cutU (31/32 : ℚ) (.cutV (-31/32 : ℚ) (.leaf 3) (.cutU (61/64 : ℚ) (.leaf 3) (.leaf 0))) (.cutV (-31/32 : ℚ) (.cutU (63/64 : ℚ) (.cutV (-63/64 : ℚ) (.leaf 3) (.cutU (125/128 : ℚ) (.leaf 0) (.leaf 0))) (.cutV (-63/64 : ℚ) (.cutU (127/128 : ℚ) (.cutV (-127/128 : ℚ) (.leaf 3) (.leaf 0)) (.cutV (-127/128 : ℚ) (.cutU (255/256 : ℚ) (.leaf 3) (.leaf 0)) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))) (.leaf 0))
      | 2, false => .cutU (0 : ℚ) (.cutV (0 : ℚ) (.cutU (-1/2 : ℚ) (.cutV (-1/2 : ℚ) (.cutU (-3/4 : ℚ) (.cutV (-3/4 : ℚ) (.cutU (-7/8 : ℚ) (.cutV (-7/8 : ℚ) (.cutU (-15/16 : ℚ) (.cutV (-15/16 : ℚ) (.cutU (-31/32 : ℚ) (.cutV (-31/32 : ℚ) (.cutU (-63/64 : ℚ) (.cutV (-63/64 : ℚ) (.cutU (-127/128 : ℚ) (.cutV (-127/128 : ℚ) (.cutU (-255/256 : ℚ) (.leaf 2) (.leaf 1)) (.leaf 2)) (.cutV (-127/128 : ℚ) (.leaf 1) (.leaf 1))) (.leaf 2)) (.cutV (-63/64 : ℚ) (.leaf 1) (.cutU (-125/128 : ℚ) (.leaf 2) (.leaf 1)))) (.leaf 2)) (.cutV (-31/32 : ℚ) (.leaf 1) (.cutU (-61/64 : ℚ) (.leaf 2) (.leaf 1)))) (.leaf 2)) (.cutV (-15/16 : ℚ) (.leaf 1) (.cutU (-29/32 : ℚ) (.leaf 2) (.leaf 1)))) (.leaf 2)) (.cutV (-7/8 : ℚ) (.leaf 1) (.cutU (-13/16 : ℚ) (.leaf 2) (.leaf 1)))) (.leaf 2)) (.cutV (-3/4 : ℚ) (.leaf 1) (.cutU (-5/8 : ℚ) (.leaf 2) (.leaf 1)))) (.leaf 2)) (.cutV (-1/2 : ℚ) (.leaf 1) (.cutU (-1/4 : ℚ) (.leaf 2) (.leaf 1)))) (.leaf 2)) (.cutV (0 : ℚ) (.leaf 1) (.cutU (1/2 : ℚ) (.cutV (1/2 : ℚ) (.cutU (1/4 : ℚ) (.leaf 2) (.leaf 1)) (.leaf 2)) (.cutV (1/2 : ℚ) (.leaf 1) (.cutU (3/4 : ℚ) (.cutV (3/4 : ℚ) (.cutU (5/8 : ℚ) (.leaf 2) (.leaf 1)) (.leaf 2)) (.cutV (3/4 : ℚ) (.leaf 1) (.cutU (7/8 : ℚ) (.cutV (7/8 : ℚ) (.cutU (13/16 : ℚ) (.leaf 2) (.leaf 1)) (.leaf 2)) (.cutV (7/8 : ℚ) (.leaf 1) (.cutU (15/16 : ℚ) (.cutV (15/16 : ℚ) (.cutU (29/32 : ℚ) (.leaf 2) (.leaf 1)) (.leaf 2)) (.cutV (15/16 : ℚ) (.leaf 1) (.cutU (31/32 : ℚ) (.cutV (31/32 : ℚ) (.cutU (61/64 : ℚ) (.leaf 2) (.leaf 1)) (.leaf 2)) (.cutV (31/32 : ℚ) (.leaf 1) (.cutU (63/64 : ℚ) (.cutV (63/64 : ℚ) (.cutU (125/128 : ℚ) (.leaf 1) (.leaf 1)) (.leaf 2)) (.cutV (63/64 : ℚ) (.leaf 1) (.cutU (127/128 : ℚ) (.cutV (127/128 : ℚ) (.leaf 1) (.leaf 2)) (.cutV (127/128 : ℚ) (.leaf 1) (.cutU (255/256 : ℚ) (.leaf 2) (.leaf 1)))))))))))))))))
      | _, _ => .leaf 0

theorem tetraCert_valid : checkCover tetraQ (11 / 100) tetraTrees = true := by decide +kernel

theorem tetrahedron4_realizes : Realizes tetraQ tetrahedron4 := by
  intro i
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have key : ∀ x y z : ℝ, x ^ 2 = 1 → y ^ 2 = 1 → z ^ 2 = 1 → ‖vec3 x y z‖ = √3 :=
    fun x y z hx hy hz => norm_vec3_eq (by rw [hx, hy, hz, h3]; norm_num) (by positivity)
  fin_cases i <;> simp only [tetrahedron4, tetraQ, qv] <;> push_cast <;>
    (rw [key _ _ _ (by norm_num) (by norm_num) (by norm_num), vec3_smul]; simp)

/-- The covering radius of the regular tetrahedron lies between `arccos (1/3)`
(the hole `-(1,1,1)/√3`) and `arccos √(11/100)` (the certificate). -/
theorem coveringRadius_tetrahedron4_bounds :
    arccos (1 / 3) ≤ coveringRadius (by norm_num : 1 ≤ 4) tetrahedron4 ∧
      coveringRadius (by norm_num : 1 ≤ 4) tetrahedron4 ≤ arccos √((11 / 100 : ℚ) : ℝ) := by
  refine ⟨?_, coveringRadius_le_of_checkCover (by norm_num) tetraCert_valid
    tetrahedron4_realizes⟩
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have h3ne : √3 ≠ 0 := (sqrt_pos.mpr (by norm_num)).ne'
  have hu : ‖vec3 (-(1 / √3)) (-(1 / √3)) (-(1 / √3))‖ = 1 :=
    norm_vec3_eq (by rw [neg_sq, div_pow, h3]; norm_num) (by norm_num)
  refine arccos_le_coveringRadius_of_hole (by norm_num) tetrahedron4
    ⟨vec3 (-(1 / √3)) (-(1 / √3)) (-(1 / √3)), hu⟩ (c := 1 / 3) fun i => ?_
  fin_cases i <;> simp only [tetrahedron4, inner_vec3] <;> field_simp <;> nlinarith

/-! ## The tetrahedron exactly, through the octahedron

The six edge midpoints of the regular tetrahedron are the vertices of the
regular octahedron scaled by `1/√3`. So the hull of the tetrahedron contains
`1/√3` times the hull of the octahedron, which contains the ball of radius
`1/√3` (the octahedron covers at `arccos (1/√3)`); scaling, the hull of the
tetrahedron contains the ball of radius `1/3`, and the tetrahedron covers at
`arccos (1/3)`. No certificate is involved. -/

/-- Each vertex of the octahedron, scaled by `1/√3`, is the midpoint of an edge
of the tetrahedron. -/
theorem octahedron6_scaled_mem_hullOf_tetrahedron4 (k : Fin 6) :
    (1 / √3) • (octahedron6 k).1 ∈ hullOf tetrahedron4 := by
  have mid : ∀ i j : Fin 4,
      (1 / 2 : ℝ) • (tetrahedron4 i).1 + (1 / 2 : ℝ) • (tetrahedron4 j).1 ∈
        hullOf tetrahedron4 := fun i j =>
    convex_convexHull ℝ (Set.range fun i => (tetrahedron4 i).1)
      (subset_convexHull ℝ _ (Set.mem_range_self i)) (subset_convexHull ℝ _ (Set.mem_range_self j))
      (by norm_num) (by norm_num) (by norm_num)
  fin_cases k
  · convert mid 0 1 using 1
    simp only [octahedron6, tetrahedron4, vec3_smul, vec3_add]; apply vec3_congr <;> ring
  · convert mid 2 3 using 1
    simp only [octahedron6, tetrahedron4, vec3_smul, vec3_add]; apply vec3_congr <;> ring
  · convert mid 0 2 using 1
    simp only [octahedron6, tetrahedron4, vec3_smul, vec3_add]; apply vec3_congr <;> ring
  · convert mid 1 3 using 1
    simp only [octahedron6, tetrahedron4, vec3_smul, vec3_add]; apply vec3_congr <;> ring
  · convert mid 0 3 using 1
    simp only [octahedron6, tetrahedron4, vec3_smul, vec3_add]; apply vec3_congr <;> ring
  · convert mid 1 2 using 1
    simp only [octahedron6, tetrahedron4, vec3_smul, vec3_add]; apply vec3_congr <;> ring

/-- The ball of radius `1/√3` lies in the hull of the octahedron. -/
theorem closedBall_subset_hullOf_octahedron6 :
    Metric.closedBall (0 : E3) (1 / √3) ⊆ hullOf octahedron6 := by
  have h := isCovering_coveringRadius (by norm_num : 1 ≤ 6) octahedron6
  rw [coveringRadius_octahedron6] at h
  have hpos : (0 : ℝ) ≤ 1 / √3 := by positivity
  have hle : 1 / √3 ≤ 1 := by
    rw [div_le_one (sqrt_pos.2 (by norm_num))]
    exact one_le_sqrt.2 (by norm_num)
  have hsub := (isCovering_iff_closedBall_subset_hullOf octahedron6 (arccos_nonneg _)
    (arccos_le_pi_div_two.2 hpos)).1 h
  rwa [cos_arccos (by linarith) hle] at hsub

/-- The ball of radius `1/3` lies in the hull of the tetrahedron. -/
theorem closedBall_subset_hullOf_tetrahedron4 :
    Metric.closedBall (0 : E3) (1 / 3) ⊆ hullOf tetrahedron4 := by
  have hS : hullOf octahedron6 ⊆ (fun z => (1 / √3 : ℝ) • z) ⁻¹' hullOf tetrahedron4 :=
    convexHull_min (by rintro _ ⟨k, rfl⟩; exact octahedron6_scaled_mem_hullOf_tetrahedron4 k)
      ((convex_convexHull ℝ _).smul_preimage _)
  intro y hy
  have h3pos : 0 < √3 := sqrt_pos.2 (by norm_num)
  have h3 : √3 * √3 = 3 := mul_self_sqrt (by norm_num)
  have hy' : √3 • y ∈ Metric.closedBall (0 : E3) (1 / √3) := by
    rw [mem_closedBall_zero_iff] at hy ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos h3pos]
    calc √3 * ‖y‖ ≤ √3 * (1 / 3) := mul_le_mul_of_nonneg_left hy h3pos.le
      _ = 1 / √3 := by field_simp; linarith
  have hmem := hS (closedBall_subset_hullOf_octahedron6 hy')
  simp only [Set.mem_preimage, smul_smul] at hmem
  rwa [one_div, inv_mul_cancel₀ h3pos.ne', one_smul] at hmem

/-- The covering radius of the regular tetrahedron is exactly `arccos (1/3)`. -/
theorem coveringRadius_tetrahedron4 :
    coveringRadius (by norm_num : 1 ≤ 4) tetrahedron4 = arccos (1 / 3) := by
  refine le_antisymm ?_ coveringRadius_tetrahedron4_bounds.1
  rw [coveringRadius_le_iff_closedBall_subset_hullOf _ _ (arccos_nonneg _)
    (arccos_le_pi_div_two.2 (by norm_num)), cos_arccos (by norm_num) (by norm_num)]
  exact closedBall_subset_hullOf_tetrahedron4

/-! ## Rejected certificates -/

/-- No certificate at all can accept the octahedron above its true `cos² r`:
this is soundness plus the hole, not a property of one tree. -/
theorem octaCert_rejects_above {R : ℚ} (hR : 1 / 3 < R) (hR1 : R ≤ 1)
    (T : Fin 3 → Bool → CoverTree) : checkCover octaQ R T = false := by
  by_contra hne
  have h : checkCover octaQ R T = true := by simpa using hne
  have hup := coveringRadius_le_of_checkCover (by norm_num : 1 ≤ 6) h octahedron6_realizes
  rw [coveringRadius_octahedron6] at hup
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have hs : 1 / √3 < √(R : ℝ) := by
    have hR' : (1 / 3 : ℝ) < R := by
      have := (Rat.cast_lt (K := ℝ)).2 hR
      push_cast at this; exact this
    have : (1 / √3) ^ 2 < (√(R : ℝ)) ^ 2 := by
      rw [div_pow, h3, Real.sq_sqrt (by linarith)]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) this
  have hR1' : √(R : ℝ) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact_mod_cast hR1
  have hpos : (0 : ℝ) ≤ 1 / √3 := by positivity
  have := arccos_lt_arccos (by linarith : (-1 : ℝ) ≤ 1 / √3) hs hR1'
  linarith

/-- Likewise for the tetrahedron above `cos² r = 1/9`. -/
theorem tetraCert_rejects_above {R : ℚ} (hR : 1 / 9 < R) (hR1 : R ≤ 1)
    (T : Fin 3 → Bool → CoverTree) : checkCover tetraQ R T = false := by
  by_contra hne
  have h : checkCover tetraQ R T = true := by simpa using hne
  have hup := coveringRadius_le_of_checkCover (by norm_num : 1 ≤ 4) h tetrahedron4_realizes
  have hlow := coveringRadius_tetrahedron4_bounds.1
  have hs : (1 / 3 : ℝ) < √(R : ℝ) := by
    have hR' : (1 / 9 : ℝ) < R := by
      have := (Rat.cast_lt (K := ℝ)).2 hR
      push_cast at this; exact this
    have : (1 / 3 : ℝ) ^ 2 < (√(R : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt (by linarith)]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) this
  have hR1' : √(R : ℝ) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact_mod_cast hR1
  have := arccos_lt_arccos (by norm_num) hs hR1'
  linarith

/-- Concrete rejections: a value of `R` above the truth, a tree that names the
wrong point, a tree that names a point that is not there, and a configuration
with a vertex removed. -/
example : checkCover octaQ (1 / 3 + 1 / 1000) octaTrees = false := by decide +kernel
example : checkCover octaQ (1 / 3) (fun _ _ => .leaf 1) = false := by decide +kernel
example : checkCover octaQ (1 / 3) (fun _ _ => .leaf 9) = false := by decide +kernel
example : checkCover (fun i : Fin 5 => octaQ i.castSucc) (1 / 3) octaTrees = false := by
  decide +kernel
example : checkCover tetraQ (12 / 100) tetraTrees = false := by decide +kernel
example : checkCover tetraQ (11 / 100) (fun _ _ => .leaf 0) = false := by decide +kernel
example : checkCover tetraQ (-1 / 100) tetraTrees = false := by decide +kernel
example : checkCover tetraQ (11 / 100) (fun a b => if a = 0 ∧ b = true then
    .cutU 0 (.leaf 0) (.leaf 0) else tetraTrees a b) = false := by decide +kernel

end Geodesy.Spherical
