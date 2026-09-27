import LeanGeodesy.Projection.Cylindrical

/-!
# Rhumb lines on the sphere

A rhumb line, or loxodrome, is a path that keeps a constant bearing `α`,
measured clockwise from north. Sailors steer them because the compass
heading never changes. This file proves the property that makes Mercator's
projection a navigation chart:

```
constant bearing on the sphere  ↔  straight line on Mercator's map
```

(`constantBearing_iff_mercatorLine`).

A path heading north of east or west (`|α| < π/2`) crosses each parallel
once, so it can be written with the latitude as parameter,
`φ ↦ (φ, λ(φ))`. Its tangent on the sphere of radius `R` is the meridian
tangent plus `λ'(φ)` times the parallel tangent (`hasDerivAt_latitudeCurve`),
with northward component `R` and eastward component `R cos φ λ'(φ)`
(`northComponent_latitudeCurve`, `eastComponent_latitudeCurve`). So its
bearing is `α` exactly when `λ'(φ) = tan α / cos φ`
(`hasBearing_latitudeCurve_iff`). Integrating, the rhumb line through
`(φ₀, λ₀)` is

```
λ(φ) = λ₀ + tan α · (mercatorY φ - mercatorY φ₀)          (rhumbLon)
```

which Mercator draws on the straight line through the image of `(φ₀, λ₀)`
with direction `(sin α, cos α)` (`mercator_rhumb_on_line`).

Restrictions: the sphere, not the ellipsoid; latitudes strictly between the
poles; bearings strictly between west and east through north (southward
bearings are the same curves run backwards, and due east or west is a
parallel, which is not a graph over latitude); and the longitude is an
unwrapped real number, so a rhumb line crossing the antimeridian keeps
counting past 180°.
-/

namespace Geodesy.Projection

open Real

/-- The northward component of a tangent vector at `(φ, λ)`, in metres: its inner
product with the unit meridian tangent. -/
noncomputable def northComponent (R φ lam : ℝ) (v : E3) : ℝ := inner ℝ v (meridianTangent R φ lam) / R

/-- The eastward component of a tangent vector at `(φ, λ)`, in metres: its inner
product with the unit parallel tangent. -/
noncomputable def eastComponent (R φ lam : ℝ) (v : E3) : ℝ :=
  inner ℝ v (parallelTangent R φ lam) / (R * cos φ)

/-- A tangent vector at `(φ, λ)` points at bearing `α` (clockwise from north)
when its east and north components are a positive multiple of
`(sin α, cos α)`. -/
def HasBearing (R φ lam : ℝ) (v : E3) (α : ℝ) : Prop :=
  ∃ c > 0, eastComponent R φ lam v = c * sin α ∧ northComponent R φ lam v = c * cos α

variable {R : ℝ}

/-- A path parametrised by latitude, `φ ↦ (φ, λ(φ))`, has tangent
`meridianTangent + λ' • parallelTangent`. -/
theorem hasDerivAt_latitudeCurve {lon : ℝ → ℝ} {lon' φ : ℝ} (h : HasDerivAt lon lon' φ) :
    HasDerivAt (fun φ => spherePoint R φ (lon φ))
      (meridianTangent R φ (lon φ) + lon' • parallelTangent R φ (lon φ)) φ := by
  unfold spherePoint meridianTangent parallelTangent
  rw [vec3_smul, vec3_add]
  refine hasDerivAt_vec3 ?_ ?_ ?_
  · convert ((hasDerivAt_cos φ).const_mul R).mul (h.cos) using 1 <;> try rfl
    ring
  · convert ((hasDerivAt_cos φ).const_mul R).mul (h.sin) using 1 <;> try rfl
    ring
  · convert (hasDerivAt_sin φ).const_mul R using 1 <;> try rfl
    ring

section Components

variable (hR : 0 < R) {φ : ℝ} (hc : 0 < cos φ) (lam lon' : ℝ)
include hR hc

omit hc in
/-- Its northward component is `R`: it gains one radian of latitude per unit
of parameter. -/
theorem northComponent_latitudeCurve :
    northComponent R φ lam (meridianTangent R φ lam + lon' • parallelTangent R φ lam) = R := by
  rw [northComponent, inner_add_left, real_inner_smul_left,
    real_inner_comm (meridianTangent R φ lam) (parallelTangent R φ lam),
    inner_meridianTangent_parallelTangent, real_inner_self_eq_norm_sq, norm_meridianTangent_sq]
  field_simp
  ring

/-- Its eastward component is `R cos φ λ'`. -/
theorem eastComponent_latitudeCurve :
    eastComponent R φ lam (meridianTangent R φ lam + lon' • parallelTangent R φ lam) =
      R * cos φ * lon' := by
  rw [eastComponent, inner_add_left, real_inner_smul_left, inner_meridianTangent_parallelTangent,
    real_inner_self_eq_norm_sq, norm_parallelTangent_sq]
  have := mul_pos hR hc
  field_simp
  ring

/-- The tangent points at bearing `α` (with `|α| < π/2`) exactly when
`λ' = tan α / cos φ`. -/
theorem hasBearing_latitudeCurve_iff {α : ℝ} (hα : α ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    HasBearing R φ lam (meridianTangent R φ lam + lon' • parallelTangent R φ lam) α ↔
      lon' = tan α / cos φ := by
  have hca : 0 < cos α := cos_pos_of_mem_Ioo hα
  rw [HasBearing, northComponent_latitudeCurve hR, eastComponent_latitudeCurve hR hc]
  constructor
  · rintro ⟨c, hc0, he, hn⟩
    rw [tan_eq_sin_div_cos]
    field_simp
    have : c = R / cos α := by field_simp; linarith
    rw [this] at he
    field_simp at he
    have h3 : R * (lon' * (cos α * cos φ) - sin α) = 0 := by linear_combination R * he
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hR.ne'
    · linarith
  · intro h
    refine ⟨R / cos α, div_pos hR hca, ?_, by field_simp⟩
    rw [h, tan_eq_sin_div_cos]
    field_simp

end Components

/-! ## The rhumb line and Mercator's straight lines -/

/-- The longitude, unwrapped, of the rhumb line with bearing `α` through
`(φ₀, λ₀)`, at latitude `φ`. -/
noncomputable def rhumbLon (lam₀ φ₀ α φ : ℝ) : ℝ := lam₀ + tan α * (mercatorY φ - mercatorY φ₀)

theorem rhumbLon_start (lam₀ φ₀ α : ℝ) : rhumbLon lam₀ φ₀ α φ₀ = lam₀ := by simp [rhumbLon]

theorem hasDerivAt_rhumbLon (lam₀ φ₀ α : ℝ) {φ : ℝ} (hc : 0 < cos φ) :
    HasDerivAt (rhumbLon lam₀ φ₀ α) (tan α / cos φ) φ := by
  unfold rhumbLon
  convert ((hasDerivAt_mercatorY hc).sub_const (mercatorY φ₀)).const_mul (tan α) |>.const_add lam₀
    using 1 <;> try rfl
  ring

/-- The rhumb line keeps bearing `α` all along. -/
theorem rhumb_hasBearing (hR : 0 < R) (lam₀ φ₀ : ℝ) {α : ℝ} (hα : α ∈ Set.Ioo (-(π / 2)) (π / 2))
    {φ : ℝ} (hc : 0 < cos φ) :
    ∃ v, HasDerivAt (fun φ => spherePoint R φ (rhumbLon lam₀ φ₀ α φ)) v φ ∧
      HasBearing R φ (rhumbLon lam₀ φ₀ α φ) v α :=
  ⟨_, hasDerivAt_latitudeCurve (hasDerivAt_rhumbLon lam₀ φ₀ α hc),
    (hasBearing_latitudeCurve_iff hR hc _ _ hα).mpr rfl⟩

/-- Mercator draws the rhumb line on the straight line through the image of
`(φ₀, λ₀)` with direction `(sin α, cos α)`: `x - R λ₀ = tan α (y - R y₀)`. -/
theorem mercator_rhumb_on_line (lam₀ φ₀ α φ : ℝ) :
    (mercator R φ (rhumbLon lam₀ φ₀ α φ)) 0 - R * lam₀ =
      tan α * ((mercator R φ (rhumbLon lam₀ φ₀ α φ)) 1 - R * mercatorY φ₀) := by
  simp only [mercator, vec2_0, vec2_1, rhumbLon]
  ring

/-- Two functions with the same derivative on the open latitudes that agree at
one latitude agree everywhere between the poles. -/
theorem eqOn_Ioo_of_hasDerivAt_eq {f g d : ℝ → ℝ} {φ₀ : ℝ}
    (hφ₀ : φ₀ ∈ Set.Ioo (-(π / 2)) (π / 2))
    (hf : ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), HasDerivAt f (d φ) φ)
    (hg : ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), HasDerivAt g (d φ) φ) (h0 : f φ₀ = g φ₀) :
    ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), f φ = g φ := by
  have hd : ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), HasDerivAt (fun t => f t - g t) 0 φ := fun φ hφ => by
    convert (hf φ hφ).sub (hg φ hφ) using 1 <;> try rfl
    rw [sub_self]
  intro φ hφ
  have hconst := Convex.is_const_of_fderivWithin_eq_zero (convex_Ioo _ _)
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [fderivWithin_of_isOpen isOpen_Ioo hx, (hd x hx).hasFDerivAt.fderiv]
      ext
      simp) hφ hφ₀
  simp only [h0, sub_self] at hconst
  linarith

/-- Constant bearing on the sphere is a straight line on Mercator's map: a path
`φ ↦ (φ, λ(φ))` through `(φ₀, λ₀)` keeps bearing `α` at every latitude
between the poles exactly when its longitude is that of the rhumb line, that
is, exactly when its Mercator image lies on the line of
`mercator_rhumb_on_line`. -/
theorem constantBearing_iff_mercatorLine (hR : 0 < R) {lon : ℝ → ℝ} {lon' : ℝ → ℝ}
    (hlon : ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), HasDerivAt lon (lon' φ) φ)
    {φ₀ lam₀ α : ℝ} (hφ₀ : φ₀ ∈ Set.Ioo (-(π / 2)) (π / 2)) (h0 : lon φ₀ = lam₀)
    (hα : α ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    (∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2),
        HasBearing R φ (lon φ) (meridianTangent R φ (lon φ) + lon' φ • parallelTangent R φ (lon φ)) α) ↔
      ∀ φ ∈ Set.Ioo (-(π / 2)) (π / 2), lon φ = rhumbLon lam₀ φ₀ α φ := by
  constructor
  · intro hb
    refine eqOn_Ioo_of_hasDerivAt_eq (d := fun φ => tan α / cos φ) hφ₀ (fun φ hφ => ?_)
      (fun φ hφ => hasDerivAt_rhumbLon lam₀ φ₀ α (cos_pos_of_mem_Ioo hφ))
      (by rw [h0, rhumbLon_start])
    have h := (hasBearing_latitudeCurve_iff hR (cos_pos_of_mem_Ioo hφ) _ _ hα).mp (hb φ hφ)
    show HasDerivAt lon (tan α / cos φ) φ
    rw [← h]
    exact hlon φ hφ
  · intro heq φ hφ
    have hc := cos_pos_of_mem_Ioo hφ
    refine (hasBearing_latitudeCurve_iff hR hc _ _ hα).mpr ?_
    -- `lon` and the rhumb longitude agree near `φ`, so their derivatives agree.
    have hev : lon =ᶠ[nhds φ] rhumbLon lam₀ φ₀ α :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hφ) heq
    exact (hlon φ hφ).unique ((hasDerivAt_rhumbLon lam₀ φ₀ α hc).congr_of_eventuallyEq hev)

end Geodesy.Projection
