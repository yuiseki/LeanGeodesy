import LeanGeodesy.CRS.WGS84
import LeanGeodesy.Projection.WebMercator

/-!
# The Web Mercator projected CRS

The projected CRS built from `Projection.WebMercator` over the WGS 84
geographic CRS.

- Its domain is the WGS 84 coordinates with latitude in
  `[-maxLatitude, maxLatitude]` (`webMercatorCRS_domain`), the cut-off that
  makes the world square.
- Its image is that square: eastings in `(-π a, π a]`, northings in
  `[-π a, π a]`.
- The forward map is `Projection.webMercator` (`webMercatorCRS_forward`) and
  the inverse is built from `Projection.webMercatorInverse`
  (`webMercatorCRS_inverse_lat`, `webMercatorCRS_inverse_lon`).

The domain is the one the existing proofs describe: a coordinate is in it
exactly when its latitude is strictly between the poles and its projection
lands in the square (`mem_webMercatorCRS_domain_iff`), which is
`Projection.y_mem_iff` restated for the CRS. The poles are outside it
(`northPole_not_mem_webMercatorCRS_domain`).
-/

namespace Geodesy

open Real Projection

/-- A plane vector is determined by its coordinates. -/
theorem vec2_eta (p : E2) : vec2 (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> rfl

/-- The latitudes of the square. -/
def webMercatorDomain : Set wgs84Geographic.Coordinate :=
  {c | -maxLatitude ≤ c.lat.1 ∧ c.lat.1 ≤ maxLatitude}

/-- The square: eastings in `(-π a, π a]`, northings in `[-π a, π a]`. -/
def webMercatorImage : Set E2 :=
  {p | (-halfExtent < p 0 ∧ p 0 ≤ halfExtent) ∧ (-halfExtent ≤ p 1 ∧ p 1 ≤ halfExtent)}

/-- The forward map: Web Mercator applied to the coordinate at height zero. -/
noncomputable def webMercatorForward (c : wgs84Geographic.Coordinate) : E2 :=
  webMercator c.toGeodetic

theorem webMercatorForward_eq (c : wgs84Geographic.Coordinate) :
    webMercatorForward c = vec2 (webMercatorX c.lon) (webMercatorY c.lat.1) := rfl

/-- The inverse map, from `Projection.webMercatorInverse`. -/
noncomputable def webMercatorBackward (p : E2) : wgs84Geographic.Coordinate :=
  ⟨⟨(webMercatorInverse (p 0) (p 1)).1, (gd_mem _).1.le, (gd_mem _).2.le⟩,
    ((webMercatorInverse (p 0) (p 1)).2 : Real.Angle)⟩

theorem lat_mem_Ioo_of_mem_webMercatorDomain {c : wgs84Geographic.Coordinate}
    (hc : c ∈ webMercatorDomain) : c.lat.1 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
  ⟨by linarith [maxLatitude_mem.2, hc.1], by linarith [maxLatitude_mem.2, hc.2]⟩

theorem webMercatorY_gd_div (y : ℝ) : webMercatorY (gd (y / webMercatorRadius)) = y := by
  rw [webMercatorY, mercatorY_gd, mul_div_cancel₀ _ webMercatorRadius_pos.ne']

theorem webMercatorForward_mapsTo :
    Set.MapsTo webMercatorForward webMercatorDomain webMercatorImage := by
  intro c hc
  rw [webMercatorForward_eq]
  simp only [webMercatorImage, Set.mem_setOf_eq, vec2_0, vec2_1]
  exact ⟨x_mem c.lon, (y_mem_iff (lat_mem_Ioo_of_mem_webMercatorDomain hc)).mpr hc⟩

theorem webMercatorBackward_mapsTo :
    Set.MapsTo webMercatorBackward webMercatorImage webMercatorDomain := by
  intro p hp
  have h := (y_mem_iff (gd_mem (p 1 / webMercatorRadius))).mp
  rw [webMercatorY_gd_div] at h
  exact h hp.2

theorem webMercatorBackward_forward (c : wgs84Geographic.Coordinate)
    (hc : c ∈ webMercatorDomain) : webMercatorBackward (webMercatorForward c) = c := by
  have hinv := webMercatorInverse_webMercator (lat_mem_Ioo_of_mem_webMercatorDomain hc) c.lon
  rw [webMercatorForward_eq]
  simp only [webMercatorBackward, vec2_0, vec2_1, hinv, Real.Angle.coe_toReal]
  rfl

theorem webMercatorForward_backward (p : E2) (hp : p ∈ webMercatorImage) :
    webMercatorForward (webMercatorBackward p) = p := by
  have ha := webMercatorRadius_pos
  have hx : -π < p 0 / webMercatorRadius ∧ p 0 / webMercatorRadius ≤ π := by
    have h₁ := hp.1.1
    have h₂ := hp.1.2
    rw [halfExtent] at h₁ h₂
    constructor
    · rw [lt_div_iff₀ ha]; linarith
    · rw [div_le_iff₀ ha]; linarith
  rw [webMercatorForward_eq]
  conv_rhs => rw [← vec2_eta p]
  simp only [webMercatorBackward, webMercatorInverse]
  rw [webMercatorX, Real.Angle.toReal_coe_eq_self_iff.mpr hx, mul_div_cancel₀ _ ha.ne',
    webMercatorY_gd_div]

/-- Web Mercator as a projected CRS over WGS 84. -/
noncomputable def webMercatorCRS : ProjectedCRS where
  base := wgs84Geographic
  domain := webMercatorDomain
  image := webMercatorImage
  forward := webMercatorForward
  inverse := webMercatorBackward
  forward_mapsTo := webMercatorForward_mapsTo
  inverse_mapsTo := webMercatorBackward_mapsTo
  inverse_forward := webMercatorBackward_forward
  forward_inverse := webMercatorForward_backward

@[simp] theorem webMercatorCRS_base : webMercatorCRS.base = wgs84Geographic := rfl

/-- The forward map of the CRS is `Projection.webMercator`: it sends a WGS 84
coordinate to its Web Mercator easting and northing. -/
theorem webMercatorCRS_forward (c : wgs84Geographic.Coordinate) :
    webMercatorCRS.forward c = webMercator c.toGeodetic := rfl

theorem webMercatorCRS_project (c : wgs84Geographic.Coordinate) :
    (webMercatorCRS.project c).pt = vec2 (webMercatorX c.lon) (webMercatorY c.lat.1) := rfl

/-- The inverse gives the latitude `gd (y / a)`... -/
theorem webMercatorCRS_inverse_lat (p : E2) :
    (webMercatorCRS.inverse p).lat.1 = gd (p 1 / webMercatorRadius) := rfl

/-- ...and the longitude `x / a`, taken modulo a full turn. -/
theorem webMercatorCRS_inverse_lon (p : E2) :
    (webMercatorCRS.inverse p).lon = ((p 0 / webMercatorRadius : ℝ) : Real.Angle) := rfl

/-- The domain is the latitudes within the cut-off. -/
theorem webMercatorCRS_domain :
    webMercatorCRS.domain = {c | -maxLatitude ≤ c.lat.1 ∧ c.lat.1 ≤ maxLatitude} := rfl

/-- A WGS 84 coordinate is in the domain exactly when its latitude is strictly
between the poles and its projection lands in the square: the domain agrees
with `Projection.y_mem_iff`. -/
theorem mem_webMercatorCRS_domain_iff (c : wgs84Geographic.Coordinate) :
    c ∈ webMercatorCRS.domain ↔
      c.lat.1 ∈ Set.Ioo (-(π / 2)) (π / 2) ∧ webMercatorCRS.forward c ∈ webMercatorCRS.image := by
  constructor
  · intro hc
    exact ⟨lat_mem_Ioo_of_mem_webMercatorDomain hc, webMercatorForward_mapsTo hc⟩
  · rintro ⟨hlat, himg⟩
    exact (y_mem_iff hlat).mp himg.2

/-- The north pole is outside the domain. -/
theorem northPole_not_mem_webMercatorCRS_domain (lon : GeodeticLongitude) :
    (⟨GeodeticLatitude.northPole, lon⟩ : wgs84Geographic.Coordinate) ∉ webMercatorCRS.domain := by
  intro h
  have := (lat_mem_Ioo_of_mem_webMercatorDomain h).2
  simp [GeodeticLatitude.northPole] at this

/-- Round trip from the geographic side. -/
theorem webMercatorCRS_unproject_project {c : wgs84Geographic.Coordinate}
    (hc : c ∈ webMercatorCRS.domain) :
    webMercatorCRS.unproject (webMercatorCRS.project c) = c :=
  webMercatorCRS.unproject_project hc

/-- Round trip from the projected side. -/
theorem webMercatorCRS_project_unproject {p : webMercatorCRS.Coordinate}
    (hp : p.pt ∈ webMercatorCRS.image) :
    webMercatorCRS.project (webMercatorCRS.unproject p) = p :=
  webMercatorCRS.project_unproject hp

end Geodesy
