import BEMOCFormalization.LatitudeCentralOppositeBlocks
import BEMOCFormalization.LatitudeOppositeGeometry
import BEMOCFormalization.CrossRingEstimate

/-!
# Geometry of the central latitude band

The central band is symmetric about the equator.  Its two boundary heights
are exactly `± centralPopulation / N`, so the elementary population bound
gives a uniform equatorial chart once `M` is moderately large.
-/

open Set

namespace BEMOC

/-- Exact upper boundary of the central band. -/
theorem central_bandBoundaryHeight_eq
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N) :
    bandBoundaryHeight N (concreteCentralBandIndex N) =
      (centralPopulation N : ℝ) / N := by
  let c := concreteCentralBandIndex N
  have hlen :
      (symmetricBandPopulations N).length - bandCount N = (c : ℕ) := by
    dsimp [c]
    simp [concreteCentralBandIndex, bandTailCount]
    omega
  have hk :
      bandCount N ≤ (symmetricBandPopulations N).length := by
    simp
    omega
  have hreflect :=
    concrete_bandBoundaryHeight_reflect (N := N) hN hk
  rw [hlen] at hreflect
  have hwidth := bandBoundaryHeight_sub_succ N c
  have hpop :
      finiteBandPopulation N c = centralPopulation N :=
    concrete_finiteBandPopulation_central hM
  rw [hpop] at hwidth
  have hcSucc :
      ((c : ℕ) + 1) = bandCount N := by
    dsimp [c]
    simp [concreteCentralBandIndex]
    omega
  rw [hcSucc] at hwidth
  change bandBoundaryHeight N (c : ℕ) =
    (centralPopulation N : ℝ) / N
  calc
    bandBoundaryHeight N (c : ℕ) =
        (bandBoundaryHeight N (c : ℕ) -
          bandBoundaryHeight N (bandCount N)) / 2 := by
      rw [hreflect]
      ring
    _ = (centralPopulation N : ℝ) / N := by
      rw [hwidth]
      ring

/-- Exact lower boundary of the central band. -/
theorem central_bandBoundaryHeight_succ_eq
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N) :
    bandBoundaryHeight N (concreteCentralBandIndex N + 1) =
      -(centralPopulation N : ℝ) / N := by
  have hk :
      bandCount N ≤ (symmetricBandPopulations N).length := by
    simp
    omega
  have hreflect :=
    concrete_bandBoundaryHeight_reflect (N := N) hN hk
  have hlen :
      (symmetricBandPopulations N).length - bandCount N =
        (concreteCentralBandIndex N : ℕ) := by
    simp [concreteCentralBandIndex, bandTailCount]
    omega
  rw [hlen, central_bandBoundaryHeight_eq hN hM] at hreflect
  have hcSucc :
      ((concreteCentralBandIndex N : ℕ) + 1) = bandCount N := by
    simp [concreteCentralBandIndex]
    omega
  change bandBoundaryHeight N
      ((concreteCentralBandIndex N : ℕ) + 1) =
    -(centralPopulation N : ℝ) / N
  rw [hcSucc]
  calc
    bandBoundaryHeight N (bandCount N) =
        -(-bandBoundaryHeight N (bandCount N)) := by ring
    _ = -((centralPopulation N : ℝ) / N) :=
      congrArg Neg.neg hreflect.symm
    _ = -(centralPopulation N : ℝ) / N := by ring

/-- Every point of the central rectangle has height controlled by the
central population. -/
theorem abs_central_band_rectangle_le_population_div
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    {s : ℝ}
    (hs : s ∈ Icc
      (bandBoundaryHeight N (concreteCentralBandIndex N + 1))
      (bandBoundaryHeight N (concreteCentralBandIndex N))) :
    |s| ≤ (centralPopulation N : ℝ) / N := by
  rw [central_bandBoundaryHeight_succ_eq hN hM,
    central_bandBoundaryHeight_eq hN hM] at hs
  rw [abs_le]
  simpa only [neg_div] using hs

/-- For `M ≥ 15`, the whole central band lies in `[-1/4,1/4]`. -/
theorem abs_central_band_rectangle_le_quarter
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {s : ℝ}
    (hs : s ∈ Icc
      (bandBoundaryHeight N (concreteCentralBandIndex N + 1))
      (bandBoundaryHeight N (concreteCentralBandIndex N))) :
    |s| ≤ (1 : ℝ) / 4 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hbasic :=
    abs_central_band_rectangle_le_population_div hN
      (by omega : 1 ≤ bandCount N) hs
  have hpopNat :=
    centralPopulation_le_fifteen_mul_bandCount
      (by omega : 1 ≤ bandCount N)
  have hpop :
      (centralPopulation N : ℝ) ≤ 15 * (bandCount N : ℝ) := by
    exact_mod_cast hpopNat
  have hMN :
      4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  have hMpos : (0 : ℝ) < bandCount N := by positivity
  have hM15 : (15 : ℝ) ≤ bandCount N := by exact_mod_cast hM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hratio :
      (centralPopulation N : ℝ) / N ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hNpos).2
    have h15 :
        15 * (bandCount N : ℝ) ≤ (bandCount N : ℝ) ^ 2 := by
      nlinarith
    nlinarith
  exact hbasic.trans hratio

/-- A central rectangle and a noncentral half-depth rectangle are separated
by at least one quarter in physical height. -/
theorem central_band_rectangle_height_gap_of_half_depth
    {N : ℕ} (hM : 15 ≤ bandCount N)
    (k : Fin (bandTailCount N + 1))
    (hkcentral : ¬ IsCentralLatitudeBand N k)
    (hkdepth : 2 * latitudeBandScale N k ≤ bandCount N)
    {s t : ℝ}
    (hs : s ∈ Icc
      (bandBoundaryHeight N (concreteCentralBandIndex N + 1))
      (bandBoundaryHeight N (concreteCentralBandIndex N)))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 : ℝ) / 4 ≤ |s - t| := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hsquarter := abs_central_band_rectangle_le_quarter hM hs
  rcases latitudeBand_region_trichotomy N k with hkN | hkC | hkS
  · have htHalf :=
      half_le_northern_band_rectangle_of_two_scale_le
        hN (by omega) k hkN hkdepth ht
    have hsUpper : s ≤ (1 : ℝ) / 4 := (abs_le.mp hsquarter).2
    rw [abs_of_nonpos (by linarith : s - t ≤ 0)]
    linarith
  · exact (hkcentral hkC).elim
  · have htHalf :=
      southern_band_rectangle_le_neg_half_of_two_scale_le
        hN (by omega) k hkS hkdepth ht
    have hsLower : -(1 : ℝ) / 4 ≤ s := by
      have := (abs_le.mp hsquarter).1
      linarith
    rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]
    linarith

/-- Uniform normal-convergence ratio for a central band paired with a
half-depth noncentral band. -/
theorem central_band_rectangle_unequalAngularRatio_le
    {N : ℕ} (hM : 15 ≤ bandCount N)
    (k : Fin (bandTailCount N + 1))
    (hkcentral : ¬ IsCentralLatitudeBand N k)
    (hkdepth : 2 * latitudeBandScale N k ≤ bandCount N)
    {s t : ℝ}
    (hs : s ∈ Icc
      (bandBoundaryHeight N (concreteCentralBandIndex N + 1))
      (bandBoundaryHeight N (concreteCentralBandIndex N)))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    unequalAngularRatio s t ≤ (63 : ℝ) / 64 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 := by
    have hlo := bandBoundaryHeight_mem hN
      (concreteCentralBandIndex N + 1)
    have hhi := bandBoundaryHeight_mem hN
      (concreteCentralBandIndex N)
    exact ⟨hlo.1.trans hs.1, hs.2.trans hhi.2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 := by
    have hlo := bandBoundaryHeight_mem hN (k + 1)
    have hhi := bandBoundaryHeight_mem hN k
    exact ⟨hlo.1.trans ht.1, ht.2.trans hhi.2⟩
  exact
    unequalAngularRatio_le_sixty_three_sixty_four_of_height_gap
      hsSphere htSphere
        (central_band_rectangle_height_gap_of_half_depth
          hM k hkcentral hkdepth hs ht)

end BEMOC
