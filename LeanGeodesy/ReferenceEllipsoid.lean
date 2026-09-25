import LeanGeodesy.Surface

/-!
# Reference ellipsoids

A geodetic datum fixes an ellipsoid of revolution by two numbers: the
semi-major axis `a` (the equatorial radius) and the flattening `f`, how much
the ellipsoid is squashed at the poles. Everything else is derived:

| Quantity | Formula |
| --- | --- |
| semi-minor axis (polar radius) | `b = a (1 - f)` |
| first eccentricity squared | `e² = f (2 - f) = (a² - b²) / a²` |
| second eccentricity squared | `e'² = e² / (1 - e²) = (a² - b²) / b²` |

`f = 0` is a sphere; the Earth's flattening is about `1/298`.
-/

namespace Geodesy

/-- An ellipsoid of revolution given by its semi-major axis and flattening. -/
structure ReferenceEllipsoid where
  /-- Semi-major axis (equatorial radius), in metres. -/
  a : ℝ
  /-- Flattening `(a - b) / a`. -/
  f : ℝ
  a_pos : 0 < a
  f_nonneg : 0 ≤ f
  f_lt_one : f < 1

namespace ReferenceEllipsoid

variable (E : ReferenceEllipsoid)

/-- Semi-minor axis (polar radius). -/
noncomputable def b : ℝ := E.a * (1 - E.f)

/-- First eccentricity squared. -/
noncomputable def e2 : ℝ := E.f * (2 - E.f)

/-- Second eccentricity squared. -/
noncomputable def ep2 : ℝ := E.e2 / (1 - E.e2)

/-- The surface itself. -/
def toSet : Set E3 := ellipsoid E.a E.b

theorem b_pos : 0 < E.b := mul_pos E.a_pos (by linarith [E.f_lt_one])

theorem b_le_a : E.b ≤ E.a := by
  unfold b
  nlinarith [E.a_pos, E.f_nonneg]

/-- The flattening is recovered from the two axes. -/
theorem f_eq : E.f = (E.a - E.b) / E.a := by
  unfold b
  field_simp [E.a_pos.ne']
  ring

theorem e2_eq : E.e2 = (E.a ^ 2 - E.b ^ 2) / E.a ^ 2 := by
  unfold e2 b
  field_simp [E.a_pos.ne']
  ring

theorem one_sub_e2 : 1 - E.e2 = (1 - E.f) ^ 2 := by unfold e2; ring

theorem one_sub_e2_eq : 1 - E.e2 = E.b ^ 2 / E.a ^ 2 := by
  rw [one_sub_e2]
  unfold b
  field_simp [E.a_pos.ne']
  ring

theorem e2_nonneg : 0 ≤ E.e2 := mul_nonneg E.f_nonneg (by linarith [E.f_lt_one])

theorem e2_lt_one : E.e2 < 1 := by
  have : 0 < 1 - E.e2 := by rw [one_sub_e2]; nlinarith [E.f_lt_one]
  linarith

theorem one_sub_e2_pos : 0 < 1 - E.e2 := by linarith [E.e2_lt_one]

theorem ep2_eq : E.ep2 = (E.a ^ 2 - E.b ^ 2) / E.b ^ 2 := by
  unfold ep2
  rw [one_sub_e2_eq, e2_eq]
  have ha := E.a_pos.ne'
  have hb := E.b_pos.ne'
  field_simp

/-- `b² = a² (1 - e²)`: the relation used in every geodetic formula below. -/
theorem b_sq : E.b ^ 2 = E.a ^ 2 * (1 - E.e2) := by
  rw [one_sub_e2_eq]
  field_simp [E.a_pos.ne']

/-- Zero flattening, equal axes and zero eccentricity all say the same:
the reference ellipsoid is a sphere. -/
theorem isSphere_tfae : List.TFAE [E.f = 0, E.b = E.a, E.e2 = 0, E.toSet = sphere E.a] := by
  have ha := E.a_pos
  tfae_have 1 → 2 := by intro h; simp [b, h]
  tfae_have 2 → 1 := by
    intro h
    have := E.f_eq
    rw [h, sub_self, zero_div] at this
    exact this
  tfae_have 1 → 3 := by intro h; simp [e2, h]
  tfae_have 3 → 1 := by
    intro h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · linarith [E.f_lt_one]
  tfae_have 2 → 4 := by intro h; rw [toSet, h, ellipsoid_self ha]
  tfae_have 4 → 2 := by
    intro h
    -- The north pole of the ellipsoid lies on the sphere, at height `b`.
    have hmem : vec3 0 0 E.b ∈ E.toSet := northPole_mem E.b_pos.ne'
    rw [h, sphere, Metric.mem_sphere, dist_zero_right] at hmem
    have hs := norm_sq_eq (vec3 0 0 E.b)
    rw [hmem] at hs
    simp only [vec3_0, vec3_1, vec3_2] at hs
    nlinarith [E.b_pos]
  tfae_finish

/-- A sphere as a reference ellipsoid. -/
def ofSphere (R : ℝ) (hR : 0 < R) : ReferenceEllipsoid := ⟨R, 0, hR, le_rfl, zero_lt_one⟩

theorem ofSphere_toSet (R : ℝ) (hR : 0 < R) : (ofSphere R hR).toSet = sphere R :=
  ((ofSphere R hR).isSphere_tfae.out 0 3).mp rfl

end ReferenceEllipsoid

end Geodesy
