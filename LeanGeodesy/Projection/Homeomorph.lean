import LeanGeodesy.Projection.WebMercator
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Projections as homeomorphisms

A map projection is more than a formula: on the right domain it is a
homeomorphism, a continuous bijection with a continuous inverse. It then
neither tears the surface nor glues two places together, so a region and its
drawing on the map have the same topology. Whatever depends only on topology
(which areas touch, overlap or contain one another) can be read off the map.

## Mercator

In latitude and longitude, Mercator's projection is

```
(φ, λ) ↦ (R λ, R · mercatorY φ),   mercatorY φ = arsinh (tan φ).
```

`mercatorY` is a homeomorphism from the open latitudes `(-π/2, π/2)` onto the
whole line (`mercatorYHomeomorph`, inverse `gd`). With the longitude taken as a
real number, unwrapped, the projection is therefore a homeomorphism from
`(-π/2, π/2) × ℝ` onto the whole plane (`mercatorHomeomorph`). The poles are
excluded because they go to infinity.

## Web Mercator

Web Mercator is Mercator on the sphere of radius `a = 6378137 m`, with the
latitudes cut off at `maxLatitude` (about 85.05°) and the longitude an angle.
As an angle, 180° east and 180° west are one longitude, and the map draws it
on the right edge only. So the easting jumps from `π a` to `-π a` as the
longitude crosses the antimeridian (`not_continuousAt_webMercatorX_antimeridian`),
and the full conversion `webMercatorEquiv` is a bijection but not a
homeomorphism.

The domain on which Web Mercator is a homeomorphism cuts the globe along the
antimeridian: latitudes in `[-maxLatitude, maxLatitude]` and longitudes in
`(-π, π)` (`webMercatorChart`). Its image is the square without its left and
right edges (`webMercatorChartImage`), and `webMercatorHomeomorph` is the
homeomorphism between them. On a chart point it is the Web Mercator
projection of that latitude and longitude (`webMercatorHomeomorph_eq_webMercator`).
-/

namespace Geodesy.Projection

open Real

/-! ## Pieces -/

theorem continuous_gd : Continuous gd :=
  continuous_arctan.comp continuous_sinh

theorem continuousOn_mercatorY : ContinuousOn mercatorY (Set.Ioo (-(π / 2)) (π / 2)) :=
  continuous_arsinh.comp_continuousOn continuousOn_tan_Ioo

/-- `mercatorY` as a homeomorphism from the open latitudes onto the line. Its
inverse is the Gudermannian function `gd`. -/
noncomputable def mercatorYHomeomorph : Set.Ioo (-(π / 2)) (π / 2) ≃ₜ ℝ where
  toFun φ := mercatorY φ
  invFun y := ⟨gd y, gd_mem y⟩
  left_inv φ := Subtype.ext (gd_mercatorY φ.2)
  right_inv := mercatorY_gd
  continuous_toFun :=
    continuousOn_mercatorY.comp_continuous continuous_subtype_val Subtype.property
  continuous_invFun := continuous_gd.subtype_mk gd_mem

@[simp] theorem mercatorYHomeomorph_apply (φ : Set.Ioo (-(π / 2)) (π / 2)) :
    mercatorYHomeomorph φ = mercatorY φ := rfl

@[simp] theorem mercatorYHomeomorph_symm_apply (y : ℝ) :
    (mercatorYHomeomorph.symm y : ℝ) = gd y := rfl

theorem continuous_vec2 : Continuous fun p : ℝ × ℝ => vec2 p.1 p.2 := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd

/-- The plane is the coordinate pair `(x, y)`. -/
noncomputable def vec2Homeomorph : ℝ × ℝ ≃ₜ E2 where
  toFun p := vec2 p.1 p.2
  invFun q := (q 0, q 1)
  left_inv _ := rfl
  right_inv q := by
    ext i
    fin_cases i <;> rfl
  continuous_toFun := continuous_vec2
  continuous_invFun := (PiLp.continuous_apply 2 _ 0).prodMk (PiLp.continuous_apply 2 _ 1)

@[simp] theorem vec2Homeomorph_apply (p : ℝ × ℝ) : vec2Homeomorph p = vec2 p.1 p.2 := rfl

/-! ## Mercator -/

/-- Mercator's projection of the sphere of radius `R`, as a homeomorphism from
the open latitudes and the unwrapped longitudes onto the whole plane. -/
noncomputable def mercatorHomeomorph (R : ℝ) (hR : R ≠ 0) :
    Set.Ioo (-(π / 2)) (π / 2) × ℝ ≃ₜ E2 :=
  ((mercatorYHomeomorph.prodCongr (Homeomorph.refl ℝ)).trans (Homeomorph.prodComm _ _)).trans
    (((Homeomorph.mulLeft₀ R hR).prodCongr (Homeomorph.mulLeft₀ R hR)).trans vec2Homeomorph)

/-- It is Mercator's projection. -/
@[simp] theorem mercatorHomeomorph_apply (R : ℝ) (hR : R ≠ 0)
    (p : Set.Ioo (-(π / 2)) (π / 2) × ℝ) :
    mercatorHomeomorph R hR p = mercator R p.1 p.2 := rfl

/-- Its inverse reads the latitude `gd (y / R)` and the longitude `x / R`. -/
theorem mercatorHomeomorph_symm_apply (R : ℝ) (hR : R ≠ 0) (q : E2) :
    (((mercatorHomeomorph R hR).symm q).1 : ℝ) = gd (q 1 / R) ∧
      ((mercatorHomeomorph R hR).symm q).2 = q 0 / R := by
  constructor
  · show gd (R⁻¹ * q 1) = gd (q 1 / R)
    rw [inv_mul_eq_div]
  · show R⁻¹ * q 0 = q 0 / R
    rw [inv_mul_eq_div]

/-! ## Web Mercator -/

local notation "a" => webMercatorRadius

/-- The chart on which Web Mercator is a homeomorphism: latitudes within the
cut-off and longitudes strictly between the antimeridian, as real numbers. -/
def webMercatorChart : Set (ℝ × ℝ) :=
  Set.Icc (-maxLatitude) maxLatitude ×ˢ Set.Ioo (-π) π

/-- Its image: the square world without its left and right edges. -/
def webMercatorChartImage : Set E2 :=
  {p | (-halfExtent < p 0 ∧ p 0 < halfExtent) ∧ (-halfExtent ≤ p 1 ∧ p 1 ≤ halfExtent)}

theorem lat_mem_Ioo_of_mem_webMercatorChart {p : ℝ × ℝ} (hp : p ∈ webMercatorChart) :
    p.1 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
  ⟨by linarith [maxLatitude_mem.2, hp.1.1], by linarith [maxLatitude_mem.2, hp.1.2]⟩

theorem mercator_mem_webMercatorChartImage {p : ℝ × ℝ} (hp : p ∈ webMercatorChart) :
    mercator a p.1 p.2 ∈ webMercatorChartImage := by
  have ha := webMercatorRadius_pos
  refine ⟨⟨?_, ?_⟩, (y_mem_iff (lat_mem_Ioo_of_mem_webMercatorChart hp)).mpr hp.1⟩
  · show -(π * a) < a * p.2
    nlinarith [hp.2.1]
  · show a * p.2 < π * a
    nlinarith [hp.2.2]

theorem inverse_mem_webMercatorChart {q : E2} (hq : q ∈ webMercatorChartImage) :
    (gd (q 1 / a), q 0 / a) ∈ webMercatorChart := by
  have ha := webMercatorRadius_pos
  refine ⟨?_, ?_, ?_⟩
  · have h := (y_mem_iff (gd_mem (q 1 / a))).mp
    rw [webMercatorY, mercatorY_gd, mul_div_cancel₀ _ ha.ne'] at h
    exact h hq.2
  · rw [lt_div_iff₀ ha]
    have := hq.1.1
    rw [halfExtent] at this
    linarith
  · rw [div_lt_iff₀ ha]
    have := hq.1.2
    rw [halfExtent] at this
    linarith

/-- Web Mercator as a homeomorphism from the chart cut along the antimeridian
onto the square without its left and right edges. -/
noncomputable def webMercatorHomeomorph : webMercatorChart ≃ₜ webMercatorChartImage where
  toFun p := ⟨mercator a p.1.1 p.1.2, mercator_mem_webMercatorChartImage p.2⟩
  invFun q := ⟨(gd (q.1 1 / a), q.1 0 / a), inverse_mem_webMercatorChart q.2⟩
  left_inv p := by
    have ha := webMercatorRadius_pos
    apply Subtype.ext
    apply Prod.ext
    · show gd (a * mercatorY p.1.1 / a) = p.1.1
      rw [mul_div_cancel_left₀ _ ha.ne', gd_mercatorY (lat_mem_Ioo_of_mem_webMercatorChart p.2)]
    · show a * p.1.2 / a = p.1.2
      rw [mul_div_cancel_left₀ _ ha.ne']
  right_inv q := by
    have ha := webMercatorRadius_pos
    apply Subtype.ext
    ext i
    fin_cases i
    · show a * (q.1 0 / a) = q.1 0
      rw [mul_div_cancel₀ _ ha.ne']
    · show a * mercatorY (gd (q.1 1 / a)) = q.1 1
      rw [mercatorY_gd, mul_div_cancel₀ _ ha.ne']
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hy : Continuous fun p : webMercatorChart => mercatorY p.1.1 :=
      continuousOn_mercatorY.comp_continuous (continuous_fst.comp continuous_subtype_val)
        fun p => lat_mem_Ioo_of_mem_webMercatorChart p.2
    have hx : Continuous fun p : webMercatorChart => p.1.2 :=
      continuous_snd.comp continuous_subtype_val
    exact continuous_vec2.comp ((continuous_const.mul hx).prodMk (continuous_const.mul hy))
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    have h0 : Continuous fun q : webMercatorChartImage => q.1 0 :=
      (PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val
    have h1 : Continuous fun q : webMercatorChartImage => q.1 1 :=
      (PiLp.continuous_apply 2 _ 1).comp continuous_subtype_val
    exact (continuous_gd.comp (h1.div_const _)).prodMk (h0.div_const _)

@[simp] theorem webMercatorHomeomorph_apply (p : webMercatorChart) :
    (webMercatorHomeomorph p : E2) = mercator a p.1.1 p.1.2 := rfl

/-- On a chart point, the homeomorphism is the Web Mercator projection of the
coordinate with that latitude and, as an angle, that longitude. -/
theorem webMercatorHomeomorph_eq_webMercator (p : webMercatorChart) (c : GeodeticCoordinate)
    (hlat : c.lat.1 = p.1.1) (hlon : c.lon = (p.1.2 : Real.Angle)) :
    (webMercatorHomeomorph p : E2) = webMercator c := by
  have hlonReal : c.lon.toReal = p.1.2 := by
    rw [hlon, Real.Angle.toReal_coe_eq_self_iff]
    exact ⟨p.2.2.1, p.2.2.2.le⟩
  rw [webMercatorHomeomorph_apply, webMercator_eq_mercator, hlat, hlonReal]

/-! ## Why the antimeridian is cut -/

/-- Web Mercator's easting jumps at the antimeridian. Approached from the east
(longitudes just below 180°) it tends to `π a`; approached from the west
(just above -180°, the same angle from the other side) it tends to `-π a`.
So no domain containing the antimeridian, with the longitude as an angle,
makes Web Mercator continuous, and the chart has to be cut there. -/
theorem not_continuousAt_webMercatorX_antimeridian :
    ¬ ContinuousAt webMercatorX (π : Real.Angle) := by
  intro h
  have ha := webMercatorRadius_pos
  have hcoe : ((-π : ℝ) : Real.Angle) = (π : Real.Angle) := by
    rw [Real.Angle.coe_neg, Real.Angle.neg_coe_pi]
  have hc : ContinuousAt (fun t : ℝ => webMercatorX (t : Real.Angle)) (-π) := by
    refine ContinuousAt.comp (g := webMercatorX) ?_ Real.Angle.continuous_coe.continuousAt
    rw [hcoe]
    exact h
  have hlim : Filter.Tendsto (fun t : ℝ => webMercatorX (t : Real.Angle))
      (nhdsWithin (-π) (Set.Ioi (-π))) (nhds (a * π)) := by
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (-π)))
    rwa [hcoe, webMercatorX, Real.Angle.toReal_pi] at this
  have hlim' : Filter.Tendsto (fun t : ℝ => webMercatorX (t : Real.Angle))
      (nhdsWithin (-π) (Set.Ioi (-π))) (nhds (a * -π)) := by
    have hlin : Filter.Tendsto (fun t : ℝ => a * t) (nhdsWithin (-π) (Set.Ioi (-π)))
        (nhds (a * -π)) :=
      ((continuous_const.mul continuous_id).tendsto (-π)).mono_left nhdsWithin_le_nhds
    refine hlin.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show -π < π by linarith [pi_pos])] with t ht
    rw [webMercatorX, Real.Angle.toReal_coe_eq_self_iff.mpr ⟨ht.1, ht.2.le⟩]
  have := tendsto_nhds_unique hlim' hlim
  nlinarith [pi_pos]

end Geodesy.Projection
