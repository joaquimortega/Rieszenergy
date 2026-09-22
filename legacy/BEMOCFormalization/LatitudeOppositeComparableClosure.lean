import BEMOCFormalization.LatitudeComparableFourTermClosure
import BEMOCFormalization.LatitudeComparablePointwiseAssembly
import BEMOCFormalization.LatitudeExceptionalSeriesClosure
import BEMOCFormalization.LatitudeTransitionNeighboring

/-!
# Comparable smooth-opposite latitude blocks

This module begins with a predicate-free sharp four-term interface.  It is
useful for geometric classes other than `ComparableSameLatitudePair`: the
caller supplies the four literal Leibniz blocks at the separated physical
scale, and the checked algebra below converts them to the genuine mixed
derivative.

The second part records the fixed-gap branch of the smooth-opposite
comparable problem.  This is the branch in which at least one band has
half-depth.  Its analytic estimate is furnished by the endpoint-safe even
series, with no additional hypothesis.
-/

open Set

namespace BEMOC

/-- Predicate-free separated-scale control of the four top-level Leibniz
blocks in `variableReducedLatitudeKernelDsstt`. -/
def LatitudeSharpFourTermSeparatedBound
    (α s t R C : ℝ) : Prop :=
  SeparatedScaledAbs R |s - t| (-2 - α) (α - 3) C
      (latitudeJetMulD2
        (latitudePowerDss α s t) (latitudePowerDsst α s t)
          (latitudePowerDsstt α s t)
        (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
          (latitudeCusp0Dtt α s t)) ∧
  SeparatedScaledAbs R |s - t| (-2 - α) (α - 3) C
      (latitudeJetMul3D2
        (latitudePowerDs α s t) (latitudePowerDst α s t)
          (latitudePowerDstt α s t)
        (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
        (normalizedLatitudeGapDs s t) (normalizedLatitudeGapDst s t)
          (normalizedLatitudeGapDstt s t)) ∧
  SeparatedScaledAbs R |s - t| (-2 - α) (α - 3) C
      (latitudeJetMul3D2
        (latitudePower α s t) (latitudePowerDt α s t)
          (latitudePowerDtt α s t)
        (latitudeCusp2 α s t) (latitudeCusp2Dt α s t)
          (latitudeCusp2Dtt α s t)
        (normalizedLatitudeGapDs s t ^ 2)
          (2 * normalizedLatitudeGapDs s t *
            normalizedLatitudeGapDst s t)
          (2 * normalizedLatitudeGapDst s t ^ 2 +
            2 * normalizedLatitudeGapDs s t *
              normalizedLatitudeGapDstt s t)) ∧
  SeparatedScaledAbs R |s - t| (-2 - α) (α - 3) C
      (latitudeJetMul3D2
        (latitudePower α s t) (latitudePowerDt α s t)
          (latitudePowerDtt α s t)
        (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
        (normalizedLatitudeGapDss s t) (normalizedLatitudeGapDsst s t)
          (normalizedLatitudeGapDsstt s t))

/-- The predicate-free four-term separated interface is exactly the sharp
mixed-term interface used by the physical derivative estimate. -/
theorem LatitudeSharpFourTermSeparatedBound.toMixedTermBound
    {α s t R C : ℝ}
    (h : LatitudeSharpFourTermSeparatedBound α s t R C) :
    LatitudeComparableMixedTermBound α s t R C := by
  unfold LatitudeComparableMixedTermBound
  simpa [LatitudeSharpFourTermSeparatedBound, SeparatedScaledAbs,
    latitudePowerDerivativeScale, mul_assoc] using h

/-- Generic sharp four-term closure.  No band classification or rectangle
geometry occurs in this statement. -/
theorem abs_variableReducedLatitudeKernelDsstt_le_of_sharpFourTermSeparated
    {α s t R C : ℝ} (hC : 0 ≤ C)
    (hscale : 0 ≤ latitudePowerDerivativeScale α R |s - t|)
    (h : LatitudeSharpFourTermSeparatedBound α s t R C) :
    |variableReducedLatitudeKernelDsstt α s t| ≤
      5 * C * latitudePowerDerivativeScale α R |s - t| :=
  abs_variableReducedLatitudeKernelDsstt_le_of_comparableTerms
    hC hscale h.toMixedTermBound

/-- The fixed-gap even-series geometry for a smooth opposite rectangle
having a half-depth band. -/
theorem smoothOpposite_halfDepth_evenPowerSeriesRectangleGeometry
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (ho : SmoothOppositeLatitudePair N j k)
    (hdepth :
      2 * latitudeBandScale N j ≤ bandCount N ∨
        2 * latitudeBandScale N k ≤ bandCount N) :
    LatitudeEvenPowerSeriesRectangleGeometry N j k ((1 : ℝ) / 4) where
  base_pos := by norm_num
  base_le s hs t ht := by
    have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
        hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
    have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
        ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
    exact quarter_le_angularKernelA_of_half_height_gap hsSphere htSphere
      (opposite_band_rectangle_height_gap_of_half_depth
        hN hM j k ho.2.2 hdepth hs ht)
  ratio_le s hs t ht :=
    opposite_band_rectangle_unequalAngularRatio_le
      hN hM j k ho.2.2 hdepth hs ht
  interior_offDiagonal s hs t ht := by
    have hreg := smoothOpposite_pair_regular ho
    have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
        hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
    have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
        ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
    have hsRadius : 0 < heightRadius s := by
      rcases latitudeBand_region_trichotomy N j with hjN | hjC | hjS
      · have hb :=
          northern_regular_rectangle_radiusSq_scale_bounds
            hN j hjN hreg.1 hs
        have hd : (0 : ℝ) < latitudeBandScale N j := by
          exact_mod_cast latitudeBandScale_pos N j
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        have hlower :
            0 < 2 * (latitudeBandScale N j : ℝ) ^ 2 / N := by
          positivity
        have hr0 : 0 ≤ heightRadius s := by
          unfold heightRadius
          positivity
        have hrsq := heightRadius_sq hsSphere
        nlinarith [hb.1]
      · exact (ho.2.1 (Or.inl hjC)).elim
      · have hsr := neg_mem_reflected_band_rectangle_unequal hN j hs
        have hjr := reflect_southern_is_northern hjS
        have hregR :
            IsRegularLatitudeBand N (concreteReflectBandIndex N j) := by
          simpa using hreg.1
        have hb :=
          northern_regular_rectangle_radiusSq_scale_bounds
            hN (concreteReflectBandIndex N j) hjr hregR hsr
        have hd :
            (0 : ℝ) <
              latitudeBandScale N (concreteReflectBandIndex N j) := by
          exact_mod_cast latitudeBandScale_pos N
            (concreteReflectBandIndex N j)
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        simp only [neg_sq] at hb
        have hlower :
            0 < 2 *
                (latitudeBandScale N (concreteReflectBandIndex N j) : ℝ) ^ 2 /
              N := by
          positivity
        have hrsq := heightRadius_sq hsSphere
        have hr0 : 0 ≤ heightRadius s := by
          unfold heightRadius
          positivity
        nlinarith [hb.1]
    have htRadius : 0 < heightRadius t := by
      rcases latitudeBand_region_trichotomy N k with hkN | hkC | hkS
      · have hb :=
          northern_regular_rectangle_radiusSq_scale_bounds
            hN k hkN hreg.2 ht
        have hd : (0 : ℝ) < latitudeBandScale N k := by
          exact_mod_cast latitudeBandScale_pos N k
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        have hlower :
            0 < 2 * (latitudeBandScale N k : ℝ) ^ 2 / N := by
          positivity
        have hr0 : 0 ≤ heightRadius t := by
          unfold heightRadius
          positivity
        have hrtq := heightRadius_sq htSphere
        nlinarith [hb.1]
      · exact (ho.2.1 (Or.inr hkC)).elim
      · have htr := neg_mem_reflected_band_rectangle_unequal hN k ht
        have hkr := reflect_southern_is_northern hkS
        have hregR :
            IsRegularLatitudeBand N (concreteReflectBandIndex N k) := by
          simpa using hreg.2
        have hb :=
          northern_regular_rectangle_radiusSq_scale_bounds
            hN (concreteReflectBandIndex N k) hkr hregR htr
        have hd :
            (0 : ℝ) <
              latitudeBandScale N (concreteReflectBandIndex N k) := by
          exact_mod_cast latitudeBandScale_pos N
            (concreteReflectBandIndex N k)
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        simp only [neg_sq] at hb
        have hlower :
            0 < 2 *
                (latitudeBandScale N (concreteReflectBandIndex N k) : ℝ) ^ 2 /
              N := by
          positivity
        have hrtq := heightRadius_sq htSphere
        have hr0 : 0 ≤ heightRadius t := by
          unfold heightRadius
          positivity
        nlinarith [hb.1]
    have hsI :=
      mem_Ioo_of_mem_Icc_heightRadius_pos hsSphere hsRadius
    have htI :=
      mem_Ioo_of_mem_Icc_heightRadius_pos htSphere htRadius
    have hgap :=
      opposite_band_rectangle_height_gap_of_half_depth
        hN hM j k ho.2.2 hdepth hs ht
    exact ⟨hsI, htI, fun hst ↦ by subst t; norm_num at hgap⟩

/-- Unconditional endpoint-safe DSSTT estimate on the fixed-gap branch of
smooth opposite rectangles. -/
theorem smoothOpposite_halfDepth_Dsstt_bound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (ho : SmoothOppositeLatitudePair N j k)
    (hdepth :
      2 * latitudeBandScale N j ≤ bandCount N ∨
        2 * latitudeBandScale N k ≤ bandCount N)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |variableReducedLatitudeKernelDsstt α s t| ≤
      exceptionalLatitudeDssttConstant α := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  exact abs_variableReducedLatitudeKernelDsstt_le_series_scale
    hα0 hα2 hN hM
    (smoothOpposite_halfDepth_evenPowerSeriesRectangleGeometry
      hN (by omega) ho hdepth) hs ht

private theorem one_add_opposite_band_dist_le_two_bandCount
    {N : ℕ} (hM : 1 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1)) :
    1 + Nat.dist (j : ℕ) (k : ℕ) ≤ 2 * bandCount N := by
  have hj : (j : ℕ) ≤ bandTailCount N := by omega
  have hk : (k : ℕ) ≤ bandTailCount N := by omega
  have hd : Nat.dist (j : ℕ) (k : ℕ) ≤ bandTailCount N := by
    by_cases hjk : (j : ℕ) ≤ (k : ℕ)
    · rw [Nat.dist_eq_sub_of_le hjk]
      omega
    · rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (by omega : (k : ℕ) ≤ (j : ℕ))]
      omega
  simp [bandTailCount] at hd ⊢
  omega

/-- The endpoint-safe fixed-gap branch already has the complete comparable
block weight.  This theorem applies whenever one of the two comparable
opposite bands has half-depth. -/
theorem smoothOpposite_comparable_halfDepth_bound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    ∀ j k, SmoothOppositeLatitudePair N j k →
      ComparableLatitudeScales N j k →
      (2 * latitudeBandScale N j ≤ bandCount N ∨
        2 * latitudeBandScale N k ≤ bandCount N) →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α
          (65536 * exceptionalLatitudeDssttConstant α) N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let C : ℝ := exceptionalLatitudeDssttConstant α
  have hC : 0 ≤ C := by
    dsimp [C]
    exact exceptionalLatitudeDssttConstant_nonneg α
  intro j k ho hcomp hdepth
  have hgeo :=
    smoothOpposite_halfDepth_evenPowerSeriesRectangleGeometry
      hN (by omega) ho hdepth
  have hraw := abs_latitudeKernel_bandPairError_le_of_Dsstt
    hN hα0 hC j k
    (fun s hs t ht ↦ hgeo.interior_offDiagonal s hs t ht)
    (fun s hs t ht ↦
      smoothOpposite_halfDepth_Dsstt_bound_series
        hα0 hα2 hM ho hdepth hs ht)
  have hpops :
      finiteBandPopulation N j ≤ 4 * latitudeBandScale N j ∧
        finiteBandPopulation N k ≤ 4 * latitudeBandScale N k := by
    rcases ho.2.2 with hNS | hSN
    · exact
        ⟨finiteBandPopulation_le_four_scale_of_northern hNS.1,
          finiteBandPopulation_le_four_scale_of_southern hNS.2⟩
    · exact
        ⟨finiteBandPopulation_le_four_scale_of_southern hSN.1,
          finiteBandPopulation_le_four_scale_of_northern hSN.2⟩
  let dj : ℝ := latitudeBandScale N j
  let dk : ℝ := latitudeBandScale N k
  let M : ℝ := bandCount N
  let D : ℝ := 1 + Nat.dist (j : ℕ) (k : ℕ)
  have hdj : 0 < dj := by
    dsimp [dj]
    exact_mod_cast latitudeBandScale_pos N j
  have hdk : 0 < dk := by
    dsimp [dk]
    exact_mod_cast latitudeBandScale_pos N k
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by dsimp [M]; exact_mod_cast (by omega :
    1 ≤ bandCount N)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤ 4 * dj := by
    dsimp [dj]
    exact_mod_cast hpops.1
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤ 4 * dk := by
    dsimp [dk]
    exact_mod_cast hpops.2
  have hdkdj : dk ≤ 2 * dj := by
    dsimp [dj, dk]
    exact_mod_cast hcomp.2
  have hdjM : dj ≤ M := by
    dsimp [dj, M]
    exact_mod_cast latitudeBandScale_le_bandCount (by omega) j
  have hMN : 4 * M ^ 2 ≤ (N : ℝ) := by
    dsimp [M]
    exact_mod_cast four_mul_bandCount_sq_le N
  have hden : (4 * M ^ 2) ^ 4 ≤ (N : ℝ) ^ 4 := by gcongr
  have hdj5 : dj ^ 5 ≤ M ^ 5 := by gcongr
  have hdj6 : dj ^ 6 ≤ dj * M ^ 5 := by
    calc
      dj ^ 6 = dj * dj ^ 5 := by ring
      _ ≤ dj * M ^ 5 := mul_le_mul_of_nonneg_left hdj5 hdj.le
  have hcoarse :
      |bandPairError N j k (latitudeKernel α)| ≤
        8192 * C * dj / M ^ 3 := by
    calc
      |bandPairError N j k (latitudeKernel α)| ≤
          64 * C * (finiteBandPopulation N j : ℝ) ^ 3 *
            (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := hraw
      _ ≤ (64 * C * (4 * dj) ^ 3 * (4 * dk) ^ 3) /
            (N : ℝ) ^ 4 := by
        gcongr
      _ ≤ (64 * C * (4 * dj) ^ 3 * (4 * dk) ^ 3) /
            (4 * M ^ 2) ^ 4 := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 1024 * C * dj ^ 3 * dk ^ 3 / M ^ 8 := by
        field_simp
        ring
      _ ≤ 1024 * C * dj ^ 3 * (2 * dj) ^ 3 / M ^ 8 := by
        gcongr
      _ = 8192 * C * dj ^ 6 / M ^ 8 := by ring
      _ ≤ 8192 * C * (dj * M ^ 5) / M ^ 8 := by
        gcongr
      _ = 8192 * C * dj / M ^ 3 := by
        field_simp [hMpos.ne']
        ring
  have hDupper : D ≤ 2 * M := by
    dsimp [D, M]
    exact_mod_cast
      one_add_opposite_band_dist_le_two_bandCount (by omega) j k
  have he : α - 3 ≤ 0 := by linarith
  have hbasePow :
      (2 * M) ^ (α - 3) ≤ D ^ (α - 3) :=
    Real.rpow_le_rpow_of_nonpos hDpos hDupper he
  have htwo :
      (1 : ℝ) / 8 ≤ 2 ^ (α - 3) := by
    have ht := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by linarith : (-3 : ℝ) ≤ α - 3)
    norm_num at ht ⊢
    exact ht
  have hweight :
      (1 / 8) * M ^ (α - 3) ≤ D ^ (α - 3) := by
    calc
      (1 / 8) * M ^ (α - 3) ≤
          2 ^ (α - 3) * M ^ (α - 3) := by gcongr
      _ = (2 * M) ^ (α - 3) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hMpos.le]
      _ ≤ D ^ (α - 3) := hbasePow
  have hcombine :
      M ^ (-α) * M ^ (α - 3) = M ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hMpos]
    congr 1
    ring
  unfold comparableLatitudeBlockMajorant
  have hcoarse' :
      |bandPairError N j k (latitudeKernel α)| ≤
        8192 * C * dj * M ^ (-3 : ℝ) := by
    rw [show M ^ (3 : ℕ) = M ^ (3 : ℝ) by
        exact (Real.rpow_natCast M 3).symm,
      div_eq_mul_inv, ← Real.rpow_neg hMpos.le] at hcoarse
    simpa [mul_assoc] using hcoarse
  calc
    |bandPairError N j k (latitudeKernel α)| ≤
        8192 * C * dj * M ^ (-3 : ℝ) := hcoarse'
    _ = 65536 * C * dj *
          (M ^ (-α) * ((1 / 8) * M ^ (α - 3))) := by
      rw [show M ^ (-3 : ℝ) =
        M ^ (-α) * M ^ (α - 3) by exact hcombine.symm]
      ring
    _ ≤ 65536 * C * dj *
          (M ^ (-α) * D ^ (α - 3)) := by gcongr
    _ = 65536 * exceptionalLatitudeDssttConstant α *
        (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α) *
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
      dsimp [C, dj, M, D]
      ring

/-- Radius and diameter chart for the complementary, near-equatorial
smooth-opposite branch.  Here both depths exceed `M/2`, so the common
comparable radius floor is itself bounded below by `1/20`. -/
theorem smoothOpposite_comparable_nearEquator_rectangle_radiusChart
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (ho : SmoothOppositeLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hjdeep : bandCount N < 2 * latitudeBandScale N j)
    (_hkdeep : bandCount N < 2 * latitudeBandScale N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    let R := comparableLatitudeRadiusFloor N j
    s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧
      R ≤ heightRadius s ∧ R ≤ heightRadius t ∧
      heightRadius s ≤ 40 * R ∧ heightRadius t ≤ 40 * R ∧
      |s - t| ≤ 800 * R ^ 2 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let R : ℝ := comparableLatitudeRadiusFloor N j
  have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hdjr : (0 : ℝ) < latitudeBandScale N j := by
    exact_mod_cast latitudeBandScale_pos N j
  have hdkr : (0 : ℝ) < latitudeBandScale N k := by
    exact_mod_cast latitudeBandScale_pos N k
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    positivity
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hreg := smoothOpposite_pair_regular ho
  have hfloors :
      R ≤ heightRadius s ∧ R ≤ heightRadius t := by
    rcases ho.2.2 with hNS | hSN
    · have hsFloor :=
        northern_band_heightRadius_floor
          hM hNS.1 hreg.1 hs
      have htr := neg_mem_reflected_band_rectangle hN k ht
      have hkr := reflect_southern_is_northern hNS.2
      have hkregR :
          IsRegularLatitudeBand N (concreteReflectBandIndex N k) := by
        simpa using hreg.2
      have htFloorR :=
        northern_band_heightRadius_floor
          hM hkr hkregR htr
      have htFloor :
          (latitudeBandScale N k : ℝ) /
              (5 * (bandCount N : ℝ)) ≤ heightRadius t := by
        simpa using htFloorR
      have hjk :
          (latitudeBandScale N j : ℝ) ≤
            2 * (latitudeBandScale N k : ℝ) := by
        exact_mod_cast hcomp.1
      constructor
      · dsimp [R, comparableLatitudeRadiusFloor]
        calc
          (latitudeBandScale N j : ℝ) /
              (10 * (bandCount N : ℝ)) ≤
            (latitudeBandScale N j : ℝ) /
              (5 * (bandCount N : ℝ)) := by
                apply div_le_div_of_nonneg_left (by positivity)
                  (by positivity)
                nlinarith
          _ ≤ heightRadius s := hsFloor
      · dsimp [R, comparableLatitudeRadiusFloor]
        calc
          (latitudeBandScale N j : ℝ) /
              (10 * (bandCount N : ℝ)) =
            ((latitudeBandScale N j : ℝ) / 2) /
              (5 * (bandCount N : ℝ)) := by ring
          _ ≤ (latitudeBandScale N k : ℝ) /
              (5 * (bandCount N : ℝ)) := by
                apply div_le_div_of_nonneg_right (by linarith)
                  (by positivity)
          _ ≤ heightRadius t := htFloor
    · have hsr := neg_mem_reflected_band_rectangle hN j hs
      have hjr := reflect_southern_is_northern hSN.1
      have hjregR :
          IsRegularLatitudeBand N (concreteReflectBandIndex N j) := by
        simpa using hreg.1
      have hsFloorR :=
        northern_band_heightRadius_floor
          hM hjr hjregR hsr
      have hsFloor :
          (latitudeBandScale N j : ℝ) /
              (5 * (bandCount N : ℝ)) ≤ heightRadius s := by
        simpa using hsFloorR
      have htFloor :=
        northern_band_heightRadius_floor
          hM hSN.2 hreg.2 ht
      have hjk :
          (latitudeBandScale N j : ℝ) ≤
            2 * (latitudeBandScale N k : ℝ) := by
        exact_mod_cast hcomp.1
      constructor
      · dsimp [R, comparableLatitudeRadiusFloor]
        calc
          (latitudeBandScale N j : ℝ) /
              (10 * (bandCount N : ℝ)) ≤
            (latitudeBandScale N j : ℝ) /
              (5 * (bandCount N : ℝ)) := by
                apply div_le_div_of_nonneg_left (by positivity)
                  (by positivity)
                nlinarith
          _ ≤ heightRadius s := hsFloor
      · dsimp [R, comparableLatitudeRadiusFloor]
        calc
          (latitudeBandScale N j : ℝ) /
              (10 * (bandCount N : ℝ)) =
            ((latitudeBandScale N j : ℝ) / 2) /
              (5 * (bandCount N : ℝ)) := by ring
          _ ≤ (latitudeBandScale N k : ℝ) /
              (5 * (bandCount N : ℝ)) := by
                apply div_le_div_of_nonneg_right (by linarith)
                  (by positivity)
          _ ≤ heightRadius t := htFloor
  have hRlower : (1 : ℝ) / 20 < R := by
    have hjdeepR :
        (bandCount N : ℝ) <
          2 * (latitudeBandScale N j : ℝ) := by
      exact_mod_cast hjdeep
    dsimp [R, comparableLatitudeRadiusFloor]
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 20)
      (by positivity : 0 < 10 * (bandCount N : ℝ))).2
    nlinarith
  have hceilS : heightRadius s ≤ 40 * R := by
    calc
      heightRadius s ≤ 1 := heightRadius_le_one hsSphere
      _ ≤ 40 * R := by linarith
  have hceilT : heightRadius t ≤ 40 * R := by
    calc
      heightRadius t ≤ 1 := heightRadius_le_one htSphere
      _ ≤ 40 * R := by linarith
  have hsI :=
    mem_Ioo_of_mem_Icc_heightRadius_pos hsSphere
      (hR.trans_le hfloors.1)
  have htI :=
    mem_Ioo_of_mem_Icc_heightRadius_pos htSphere
      (hR.trans_le hfloors.2)
  have habs : |s - t| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [hsSphere.1, hsSphere.2,
      htSphere.1, htSphere.2]
  have hR2 : (1 : ℝ) / 400 < R ^ 2 := by
    nlinarith [sq_nonneg (R - 1 / 20)]
  have hdiam : |s - t| ≤ 800 * R ^ 2 :=
    habs.trans (by linarith)
  exact ⟨hsI, htI, hfloors.1, hfloors.2,
    hceilS, hceilT, hdiam⟩

private theorem northern_noncentral_band_rectangle_pos
    {N : ℕ} (hN : 0 < N)
    {j : Fin (bandTailCount N + 1)}
    (hj : IsNorthernLatitudeBand N j)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    0 < s := by
  have hj1 : (j : ℕ) + 1 ≤ bandCount N - 1 := by
    unfold IsNorthernLatitudeBand at hj
    omega
  have hformula := concrete_bandBoundaryHeight_north
    (N := N) (j := (j : ℕ) + 1) hj1
  rw [hformula] at hs
  have hfour :
      4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  have hM2 : 2 ≤ bandCount N := by
    unfold IsNorthernLatitudeBand at hj
    omega
  have hjM0 :
      (((j : ℕ) + 1 : ℕ) : ℝ) ≤
        ((bandCount N - 1 : ℕ) : ℝ) := by
    exact_mod_cast hj1
  have hjM :
      (((j : ℕ) + 1 : ℕ) : ℝ) ≤ (bandCount N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ bandCount N)] at hjM0
    norm_num at hjM0 ⊢
    exact hjM0
  have hpoly :
      2 * (((j : ℕ) + 1 : ℕ) : ℝ) *
          (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) <
        4 * (bandCount N : ℝ) ^ 2 := by
    have hMpos : (0 : ℝ) < bandCount N := by
      exact_mod_cast (show 0 < bandCount N by omega)
    nlinarith
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hfrac :
      2 * (((j : ℕ) + 1 : ℕ) : ℝ) *
          (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) / N < 1 := by
    apply (div_lt_iff₀ hNreal).2
    linarith
  exact (sub_pos.mpr hfrac).trans_le hs.1

private theorem southern_noncentral_band_rectangle_neg
    {N : ℕ} (hN : 0 < N)
    {j : Fin (bandTailCount N + 1)}
    (hj : IsSouthernLatitudeBand N j)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    s < 0 := by
  have href := neg_mem_reflected_band_rectangle_unequal hN j hs
  have hjr := reflect_southern_is_northern hj
  have hpos :=
    northern_noncentral_band_rectangle_pos hN hjr href
  linarith

/-- The smallest remaining analytic datum for the near-equatorial opposite
branch, already expressed at the row/index scale consumed by Peano
transfer. -/
def HasSmoothOppositeComparableNearEquatorDssttBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    SmoothOppositeLatitudePair N j k →
    ComparableLatitudeScales N j k →
    bandCount N < 2 * latitudeBandScale N j →
    bandCount N < 2 * latitudeBandScale N k →
    ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
        |variableReducedLatitudeKernelDsstt α s t| ≤
          C * (bandCount N : ℝ) ^ (8 - α) *
            (latitudeBandScale N j : ℝ) ^ (-5 : ℝ) *
            (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3)

/-- Peano transfer and population arithmetic close the entire
near-equatorial branch from the preceding exact pointwise datum. -/
theorem smoothOpposite_comparable_nearEquator_bound_of_Dsstt
    {α C : ℝ} {N : ℕ} (hM : 1 ≤ bandCount N)
    (hα0 : 0 < α) (hC : 0 ≤ C)
    (hD : HasSmoothOppositeComparableNearEquatorDssttBound α N C) :
    ∀ j k, SmoothOppositeLatitudePair N j k →
      ComparableLatitudeScales N j k →
      bandCount N < 2 * latitudeBandScale N j →
      bandCount N < 2 * latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α (8192 * C) N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hMN :
      4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  intro j k ho hcomp hjdeep hkdeep
  let D : ℝ := 1 + Nat.dist (j : ℕ) (k : ℕ)
  let B : ℝ :=
    C * (bandCount N : ℝ) ^ (8 - α) *
      (latitudeBandScale N j : ℝ) ^ (-5 : ℝ) *
      D ^ (α - 3)
  have hB : 0 ≤ B := by dsimp [B, D]; positivity
  have hraw :=
    abs_latitudeKernel_bandPairError_le_of_Dsstt
      hN hα0 hB j k
      (fun s hs t ht ↦ by
        have hc :=
          smoothOpposite_comparable_nearEquator_rectangle_radiusChart
            hM ho hcomp hjdeep hkdeep hs ht
        exact ⟨hc.1, hc.2.1, fun hst ↦ by
          subst t
          rcases ho.2.2 with hNS | hSN
          · have hs0 :=
              northern_noncentral_band_rectangle_pos hN hNS.1 hs
            have ht0 :=
              southern_noncentral_band_rectangle_neg hN hNS.2 ht
            linarith
          · have hs0 :=
              southern_noncentral_band_rectangle_neg hN hSN.1 hs
            have ht0 :=
              northern_noncentral_band_rectangle_pos hN hSN.2 ht
            linarith⟩)
      (fun s hs t ht ↦ by
        simpa [B, D] using
          hD j k ho hcomp hjdeep hkdeep s hs t ht)
  have hpops :
      finiteBandPopulation N j ≤ 4 * latitudeBandScale N j ∧
        finiteBandPopulation N k ≤ 4 * latitudeBandScale N k := by
    rcases ho.2.2 with hNS | hSN
    · exact
        ⟨finiteBandPopulation_le_four_scale_of_northern hNS.1,
          finiteBandPopulation_le_four_scale_of_southern hNS.2⟩
    · exact
        ⟨finiteBandPopulation_le_four_scale_of_southern hSN.1,
          finiteBandPopulation_le_four_scale_of_northern hSN.2⟩
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤
        4 * (latitudeBandScale N j : ℝ) := by
    exact_mod_cast hpops.1
  have hpk0 :
      (finiteBandPopulation N k : ℝ) ≤
        4 * (latitudeBandScale N k : ℝ) := by
    exact_mod_cast hpops.2
  have hcompR :
      (latitudeBandScale N k : ℝ) ≤
        2 * (latitudeBandScale N j : ℝ) := by
    exact_mod_cast hcomp.2
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤
        8 * (latitudeBandScale N j : ℝ) := by linarith
  have hscale := separatedComparable_scale_arithmetic
    (α := α) (C := C) (M := (bandCount N : ℝ)) (N := (N : ℝ))
    (d := (latitudeBandScale N j : ℝ))
    (p := (finiteBandPopulation N j : ℝ))
    (q := (finiteBandPopulation N k : ℝ)) (D := D)
    hC (by exact_mod_cast hM) (by exact_mod_cast hN)
    (by exact_mod_cast latitudeBandScale_pos N j)
    (by positivity) (by positivity) (by dsimp [D]; positivity)
    hpj hpk hMN
  exact hraw.trans (by
    simpa [B, D, comparableLatitudeBlockMajorant] using hscale)

/-- Full smooth-opposite comparable reduction at the project threshold.
The fixed-gap branch is unconditional; the sole remaining input is the
near-equatorial sharp mixed-derivative datum above. -/
theorem hasSmoothOppositeComparableLatitudeBlockBound_of_nearEquatorDsstt
    {α C : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N) (hC : 0 ≤ C)
    (hD : HasSmoothOppositeComparableNearEquatorDssttBound α N C) :
    HasSmoothOppositeComparableLatitudeBlockBound α N
      (65536 * exceptionalLatitudeDssttConstant α + 8192 * C) := by
  intro j k ho hcomp
  by_cases hdepth :
      2 * latitudeBandScale N j ≤ bandCount N ∨
        2 * latitudeBandScale N k ≤ bandCount N
  · exact (smoothOpposite_comparable_halfDepth_bound_series
      hα0 hα2 (by omega) j k ho hcomp hdepth).trans
        (comparableLatitudeBlockMajorant_mono (by
          have hE := exceptionalLatitudeDssttConstant_nonneg α
          nlinarith))
  · have hjdeep : bandCount N < 2 * latitudeBandScale N j := by
      push_neg at hdepth
      omega
    have hkdeep : bandCount N < 2 * latitudeBandScale N k := by
      push_neg at hdepth
      omega
    exact (smoothOpposite_comparable_nearEquator_bound_of_Dsstt
      (by omega) hα0 hC hD j k ho hcomp hjdeep hkdeep).trans
        (comparableLatitudeBlockMajorant_mono (by
          have hE := exceptionalLatitudeDssttConstant_nonneg α
          nlinarith))

end BEMOC
