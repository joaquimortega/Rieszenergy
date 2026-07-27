import BEMOCFormalization.LatitudeComparableRadiusBounds
import BEMOCFormalization.LatitudeComparableGradedGap

/-!
# Quadratic normalized-gap geometry on comparable rectangles

Writing `x` for the normalized latitude gap and `ρ_s,ρ_t` for the two
horizontal radii, the exact hyperbolic identity is

`(s-t)² = (ρ_s ρ_t)² x (x+2)`.

Consequently, on the local chart `x ≤ 1`, radius ceilings turn the
normalized gap into the quadratic scale
`x ≳ |s-t|² R⁻⁴`.  This is the lower bound needed when the negative powers
in the reduced-cusp derivative estimates are converted to the physical
scale in (5.5).
-/

open Set

namespace BEMOC

set_option maxHeartbeats 800000

private theorem interior_of_closed_and_radius_pos
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (hr : 0 < heightRadius s) :
    s ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · by_contra h
    have hse : s = -1 := by linarith [hs.1]
    subst s
    norm_num [heightRadius] at hr
  · by_contra h
    have hse : s = 1 := by linarith [hs.2]
    subst s
    norm_num [heightRadius] at hr

/-- Exact algebraic identity behind the quadratic normalized-gap scale. -/
theorem normalizedLatitudeGap_mul_add_two
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    (heightRadius s * heightRadius t) ^ 2 *
        (normalizedLatitudeGap s t *
          (normalizedLatitudeGap s t + 2)) =
      (s - t) ^ 2 := by
  have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hrs : heightRadius s ≠ 0 := (heightRadius_pos hs).ne'
  have hrt : heightRadius t ≠ 0 := (heightRadius_pos ht).ne'
  have hrsq := heightRadius_sq hs'
  have hrtq := heightRadius_sq ht'
  have hprod : heightRadius s * heightRadius t ≠ 0 :=
    mul_ne_zero hrs hrt
  have hnorm : normalizedLatitudeGap s t =
      (1 - s * t - heightRadius s * heightRadius t) /
        (heightRadius s * heightRadius t) := by
    unfold normalizedLatitudeGap
    field_simp [hprod]
  rw [hnorm]
  calc
    (heightRadius s * heightRadius t) ^ 2 *
          ((1 - s * t - heightRadius s * heightRadius t) /
            (heightRadius s * heightRadius t) *
          ((1 - s * t - heightRadius s * heightRadius t) /
            (heightRadius s * heightRadius t) + 2)) =
        (1 - s * t - heightRadius s * heightRadius t) *
          (1 - s * t + heightRadius s * heightRadius t) := by
            field_simp [hprod]
            ring
    _ = (1 - s * t) ^ 2 -
        (heightRadius s * heightRadius t) ^ 2 := by ring
    _ = (s - t) ^ 2 := by
      rw [mul_pow, hrsq, hrtq]
      ring

/-- If the normalized gap lies in the unit local chart, it has the required
quadratic lower bound in terms of the product of the two radii. -/
theorem normalizedLatitudeGap_quadratic_lower_of_le_one
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hgap0 : 0 ≤ normalizedLatitudeGap s t)
    (hgap1 : normalizedLatitudeGap s t ≤ 1) :
    (s - t) ^ 2 ≤
      3 * (heightRadius s * heightRadius t) ^ 2 *
        normalizedLatitudeGap s t := by
  have hid := normalizedLatitudeGap_mul_add_two hs ht
  have hx2 : normalizedLatitudeGap s t + 2 ≤ 3 := by linarith
  have hrprod : 0 ≤ (heightRadius s * heightRadius t) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hx2 hgap0) hrprod
  nlinarith

/-- Radius ceilings convert the preceding exact bound to
`x ≥ (3·40⁴)⁻¹ |s-t|² R⁻⁴`.  The product form avoids any ambiguity about
real powers and is the form consumed by the graded derivative proof. -/
theorem normalizedLatitudeGap_quadratic_lower_of_radius_ceiling
    {s t R : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hR : 0 < R)
    (hsupper : heightRadius s ≤ 40 * R)
    (htupper : heightRadius t ≤ 40 * R)
    (hgap0 : 0 ≤ normalizedLatitudeGap s t)
    (hgap1 : normalizedLatitudeGap s t ≤ 1) :
    ((3 * 40 ^ 4 : ℝ)⁻¹) * (s - t) ^ 2 *
        (R ^ 4)⁻¹ ≤ normalizedLatitudeGap s t := by
  have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
  have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
  have hprod :
      (heightRadius s * heightRadius t) ^ 2 ≤
        (40 * R) ^ 4 := by
    have hmul :
        heightRadius s * heightRadius t ≤ (40 * R) ^ 2 := by
      calc
        heightRadius s * heightRadius t ≤ (40 * R) * (40 * R) := by
          gcongr
        _ = (40 * R) ^ 2 := by ring
    have hleft : 0 ≤ heightRadius s * heightRadius t := by positivity
    have hright : 0 ≤ (40 * R) ^ 2 := by positivity
    nlinarith
  have hquad :=
    normalizedLatitudeGap_quadratic_lower_of_le_one
      hs ht hgap0 hgap1
  have hmain :
      (s - t) ^ 2 ≤
        (3 * 40 ^ 4) * R ^ 4 * normalizedLatitudeGap s t := by
    calc
      (s - t) ^ 2 ≤
          3 * (heightRadius s * heightRadius t) ^ 2 *
            normalizedLatitudeGap s t := hquad
      _ ≤ 3 * (40 * R) ^ 4 * normalizedLatitudeGap s t := by
        gcongr
      _ = (3 * 40 ^ 4) * R ^ 4 *
          normalizedLatitudeGap s t := by ring
  have hconst : (0 : ℝ) < 3 * 40 ^ 4 := by norm_num
  have hR4 : 0 < R ^ 4 := by positivity
  apply (mul_inv_le_iff₀ hR4).2
  apply (inv_mul_le_iff₀ hconst).2
  nlinarith

/-- On one closed hemisphere, radius ceilings imply the height diameter
bound used to place a comparable rectangle inside a local chart. -/
theorem sameHemisphere_abs_sub_le_of_radius_ceiling
    {s t R : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hsame : (0 ≤ s ∧ 0 ≤ t) ∨ (s ≤ 0 ∧ t ≤ 0))
    (hR : 0 ≤ R)
    (hsupper : heightRadius s ≤ 40 * R)
    (htupper : heightRadius t ≤ 40 * R) :
    |s - t| ≤ 3200 * R ^ 2 := by
  have hrsq := heightRadius_sq hs
  have hrtq := heightRadius_sq ht
  have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
  have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
  have hsSq : heightRadius s ^ 2 ≤ (40 * R) ^ 2 := by
    nlinarith
  have htSq : heightRadius t ^ 2 ≤ (40 * R) ^ 2 := by
    nlinarith
  rcases hsame with hnorth | hsouth
  · have hsGap : 1 - s ≤ heightRadius s ^ 2 := by
      rw [hrsq]
      nlinarith
    have htGap : 1 - t ≤ heightRadius t ^ 2 := by
      rw [hrtq]
      nlinarith
    rw [abs_le]
    constructor <;> nlinarith
  · have hsGap : 1 + s ≤ heightRadius s ^ 2 := by
      rw [hrsq]
      nlinarith
    have htGap : 1 + t ≤ heightRadius t ^ 2 := by
      rw [hrtq]
      nlinarith
    rw [abs_le]
    constructor <;> nlinarith

/-- Literal classified comparable rectangles have height diameter at most
`3200 R²` for the common radius scale `R=d_j/(10M)`. -/
theorem comparableSame_rectangle_abs_sub_le_radiusFloor_sq
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : ComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |s - t| ≤ 3200 *
      ((latitudeBandScale N j : ℝ) /
        (10 * (bandCount N : ℝ))) ^ 2 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hceil :=
    comparableSame_rectangle_common_radius_ceiling hM hjk hs ht
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hdreal : (0 : ℝ) < latitudeBandScale N j := by
    exact_mod_cast latitudeBandScale_pos N j
  apply sameHemisphere_abs_sub_le_of_radius_ceiling
    hsSphere htSphere _ (by positivity) hceil.1 hceil.2
  rcases hjk.2.2.1 with hNN | hSS
  · exact Or.inl
      ⟨northern_band_rectangle_nonnegative hM hNN.1 hs,
        northern_band_rectangle_nonnegative hM hNN.2 ht⟩
  · have hsn := northern_band_rectangle_nonnegative hM
      (reflect_southern_is_northern hSS.1)
      (neg_mem_reflected_band_rectangle hN j hs)
    have htn := northern_band_rectangle_nonnegative hM
      (reflect_southern_is_northern hSS.2)
      (neg_mem_reflected_band_rectangle hN k ht)
    exact Or.inr ⟨by linarith, by linarith⟩

/-- The exact quadratic normalized-gap lower bound on a literal comparable
rectangle, conditional only on being in the unit local chart. -/
theorem comparableSame_rectangle_normalizedGap_quadratic_lower
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : ComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hst : s ≠ t)
    (hgap : normalizedLatitudeGap s t ≤ 1) :
    ((3 * 40 ^ 4 : ℝ)⁻¹) * (s - t) ^ 2 *
        (((latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ))) ^ 4)⁻¹ ≤
      normalizedLatitudeGap s t := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hfloor := (comparableSame_rectangle_geometry hM hjk hs ht).1
  have hceil :=
    comparableSame_rectangle_common_radius_ceiling hM hjk hs ht
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hdreal : (0 : ℝ) < latitudeBandScale N j := by
    exact_mod_cast latitudeBandScale_pos N j
  let R : ℝ := (latitudeBandScale N j : ℝ) /
    (10 * (bandCount N : ℝ))
  have hR : 0 < R := by dsimp [R]; positivity
  have hspos : 0 < heightRadius s := hR.trans_le hfloor.1
  have htpos : 0 < heightRadius t := hR.trans_le hfloor.2
  have hsInterior :=
    interior_of_closed_and_radius_pos hsSphere hspos
  have htInterior :=
    interior_of_closed_and_radius_pos htSphere htpos
  have hgap0 : 0 ≤ normalizedLatitudeGap s t :=
    (normalizedLatitudeGap_pos hsInterior htInterior hst).le
  simpa [R] using
    normalizedLatitudeGap_quadratic_lower_of_radius_ceiling
      hsInterior htInterior hR hceil.1 hceil.2 hgap0 hgap

/-- All six graded normalized-gap derivative bounds are now discharged on
literal comparable rectangles once the unit-chart inequality is known. -/
theorem comparableSame_rectangle_gradedGapBound
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : ComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hgap : normalizedLatitudeGap s t ≤ 1) :
    LatitudeComparableGradedGapBound s t
      ((latitudeBandScale N j : ℝ) /
        (10 * (bandCount N : ℝ))) 3200 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hfloor := (comparableSame_rectangle_geometry hM hjk hs ht).1
  have hceil :=
    comparableSame_rectangle_common_radius_ceiling hM hjk hs ht
  have hdiam :=
    comparableSame_rectangle_abs_sub_le_radiusFloor_sq hM hjk hs ht
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hdreal : (0 : ℝ) < latitudeBandScale N j := by
    exact_mod_cast latitudeBandScale_pos N j
  exact latitudeComparableGradedGapBound
    hsSphere htSphere (by positivity) (by norm_num)
    hfloor.1 hfloor.2 hceil.1 hceil.2 hdiam hgap

/-- Every literal comparable rectangle lies in a fixed normalized-gap
chart.  Unlike the sharper unit-chart statement, this follows immediately
from the already proved radius floor and height diameter and is sufficient
for a cutoff-based local cusp decomposition. -/
theorem comparableSame_rectangle_normalizedLatitudeGap_le
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : ComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    normalizedLatitudeGap s t ≤ 3200 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hfloor := (comparableSame_rectangle_geometry hM hjk hs ht).1
  have hdiam :=
    comparableSame_rectangle_abs_sub_le_radiusFloor_sq hM hjk hs ht
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hdreal : (0 : ℝ) < latitudeBandScale N j := by
    exact_mod_cast latitudeBandScale_pos N j
  let R : ℝ := (latitudeBandScale N j : ℝ) /
    (10 * (bandCount N : ℝ))
  have hR : 0 < R := by dsimp [R]; positivity
  have hspos : 0 < heightRadius s := hR.trans_le hfloor.1
  have htpos : 0 < heightRadius t := hR.trans_le hfloor.2
  have hsInterior :=
    interior_of_closed_and_radius_pos hsSphere hspos
  have htInterior :=
    interior_of_closed_and_radius_pos htSphere htpos
  have hgap0 : 0 ≤ normalizedLatitudeGap s t := by
    rw [normalizedLatitudeGap_eq hsInterior htInterior]
    exact div_nonneg (latitudeRadialGapSq_nonneg s t)
      (by unfold latitudeAngularScale; positivity)
  have hid := normalizedLatitudeGap_mul_add_two
    hsInterior htInterior
  have hprodFloor :
      R ^ 2 ≤ heightRadius s * heightRadius t := by
    nlinarith [mul_le_mul hfloor.1 hfloor.2 hR.le
      (show 0 ≤ heightRadius s by unfold heightRadius; positivity)]
  have hprodSq :
      R ^ 4 ≤ (heightRadius s * heightRadius t) ^ 2 := by
    nlinarith [sq_nonneg
      (heightRadius s * heightRadius t - R ^ 2)]
  have hdiamSq : (s - t) ^ 2 ≤ 3200 ^ 2 * R ^ 4 := by
    have habs0 : 0 ≤ |s - t| := abs_nonneg _
    have hdiam' : |s - t| ≤ 3200 * R ^ 2 := by simpa [R] using hdiam
    nlinarith [sq_abs (s - t)]
  have hprodPos : 0 < (heightRadius s * heightRadius t) ^ 2 := by
    positivity
  have hmul :
      (heightRadius s * heightRadius t) ^ 2 *
          (normalizedLatitudeGap s t *
            (normalizedLatitudeGap s t + 2)) ≤
        (heightRadius s * heightRadius t) ^ 2 * 3200 ^ 2 := by
    rw [hid]
    calc
      (s - t) ^ 2 ≤ 3200 ^ 2 * R ^ 4 := hdiamSq
      _ ≤ 3200 ^ 2 *
          (heightRadius s * heightRadius t) ^ 2 := by gcongr
      _ = (heightRadius s * heightRadius t) ^ 2 * 3200 ^ 2 := by ring
  have hquad :
      normalizedLatitudeGap s t *
          (normalizedLatitudeGap s t + 2) ≤ 3200 ^ 2 := by
    exact (mul_le_mul_left hprodPos).mp (by simpa only [mul_assoc] using hmul)
  nlinarith

end BEMOC
