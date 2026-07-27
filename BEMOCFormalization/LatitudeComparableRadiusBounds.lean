import BEMOCFormalization.LatitudeComparableGeometry
import BEMOCFormalization.LatitudeUnequalGeometry

/-!
# Radius ceilings on comparable latitude rectangles

`LatitudeComparableGeometry` supplies the common radius floor needed away
from the poles.  The exact boundary formulas also give the matching ceiling.
Together they place both radii between `R` and `40 R`, where
`R = d_j/(10M)`.  This is the coefficient geometry needed for the graded
power-jet estimates in (5.5).
-/

open Set

namespace BEMOC

theorem sameHemisphere_regular_rectangle_radiusSq_upper
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)}
    (hsame : SameLatitudeHemisphere N j k)
    (hjreg : IsRegularLatitudeBand N j)
    (hkreg : IsRegularLatitudeBand N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    1 - s ^ 2 ≤
        12 * (latitudeBandScale N j : ℝ) ^ 2 / N ∧
      1 - t ^ 2 ≤
        12 * (latitudeBandScale N k : ℝ) ^ 2 / N := by
  rcases hsame with hNN | hSS
  · exact
      ⟨(northern_regular_rectangle_radiusSq_scale_bounds
          hN j hNN.1 hjreg hs).2,
        (northern_regular_rectangle_radiusSq_scale_bounds
          hN k hNN.2 hkreg ht).2⟩
  · have hsr := neg_mem_reflected_band_rectangle hN j hs
    have htr := neg_mem_reflected_band_rectangle hN k ht
    have hjr := reflect_southern_is_northern hSS.1
    have hkr := reflect_southern_is_northern hSS.2
    have hjregR :
        IsRegularLatitudeBand N (concreteReflectBandIndex N j) := by
      simpa using hjreg
    have hkregR :
        IsRegularLatitudeBand N (concreteReflectBandIndex N k) := by
      simpa using hkreg
    have hsupper :=
      (northern_regular_rectangle_radiusSq_scale_bounds
        hN (concreteReflectBandIndex N j) hjr hjregR hsr).2
    have htupper :=
      (northern_regular_rectangle_radiusSq_scale_bounds
        hN (concreteReflectBandIndex N k) hkr hkregR htr).2
    simpa using And.intro hsupper htupper

private theorem heightRadius_le_two_scale_div_bandCount
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {d : ℕ} (hd : 0 < d) {s : ℝ}
    (hsSphere : s ∈ Icc (-1 : ℝ) 1)
    (hsq : 1 - s ^ 2 ≤ 12 * (d : ℝ) ^ 2 / N) :
    heightRadius s ≤ 2 * (d : ℝ) / bandCount N := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hfour :
      4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  have hfrac :
      12 * (d : ℝ) ^ 2 / N ≤
        3 * (d : ℝ) ^ 2 / (bandCount N : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ hNreal (sq_pos_of_pos hMreal)).2
    have hmul := mul_le_mul_of_nonneg_left hfour
      (show 0 ≤ 3 * (d : ℝ) ^ 2 by positivity)
    nlinarith
  have hrsq := heightRadius_sq hsSphere
  have hr0 : 0 ≤ heightRadius s := by
    unfold heightRadius
    positivity
  have htarget0 :
      0 ≤ 2 * (d : ℝ) / bandCount N := by positivity
  have htargetSq :
      (2 * (d : ℝ) / bandCount N) ^ 2 =
        4 * (d : ℝ) ^ 2 / (bandCount N : ℝ) ^ 2 := by
    field_simp [hMreal.ne']
    ring
  rw [← hrsq] at hsq
  have hsquare :
      heightRadius s ^ 2 ≤
        (2 * (d : ℝ) / bandCount N) ^ 2 := by
    rw [htargetSq]
    exact hsq.trans (hfrac.trans (by
      apply div_le_div_of_nonneg_right
      · nlinarith [sq_nonneg (d : ℝ)]
      · positivity))
  nlinarith

/-- Both radii on a classified comparable rectangle have the matching
ceiling `40R` for the common floor `R=d_j/(10M)`. -/
theorem comparableSame_rectangle_common_radius_ceiling
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : ComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    heightRadius s ≤
        40 * ((latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ))) ∧
      heightRadius t ≤
        40 * ((latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ))) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hreg := comparableSame_pair_regular hjk
  have hsq := sameHemisphere_regular_rectangle_radiusSq_upper
    hN hjk.2.2.1 hreg.1 hreg.2 hs ht
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hsj := heightRadius_le_two_scale_div_bandCount
    hM (latitudeBandScale_pos N j) hsSphere hsq.1
  have htk := heightRadius_le_two_scale_div_bandCount
    hM (latitudeBandScale_pos N k) htSphere hsq.2
  have hcomp := hjk.2.2.2
  have hkj : latitudeBandScale N k ≤ 2 * latitudeBandScale N j := hcomp.2
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  constructor
  · calc
      heightRadius s ≤
          2 * (latitudeBandScale N j : ℝ) / bandCount N := hsj
      _ ≤ 4 * (latitudeBandScale N j : ℝ) / bandCount N := by
        have hd0 : (0 : ℝ) ≤ latitudeBandScale N j := by positivity
        exact div_le_div_of_nonneg_right (by nlinarith) hMreal.le
      _ = 40 * ((latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ))) := by ring
  · calc
      heightRadius t ≤
          2 * (latitudeBandScale N k : ℝ) / bandCount N := htk
      _ ≤ 4 * (latitudeBandScale N j : ℝ) / bandCount N := by
        have hkjR :
            (latitudeBandScale N k : ℝ) ≤
              2 * (latitudeBandScale N j : ℝ) := by
          exact_mod_cast hkj
        apply div_le_div_of_nonneg_right _ hMreal.le
        nlinarith
      _ = 40 * ((latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ))) := by
        field_simp [hMreal.ne']
        ring

end BEMOC
