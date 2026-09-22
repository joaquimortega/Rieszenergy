import BEMOCFormalization.ReducedCuspResonant
import BEMOCFormalization.LatitudeDiagonalBandBridge
import BEMOCFormalization.LatitudeComparableGapGeometry
import BEMOCFormalization.LatitudeUnequalBlocks

/-!
# Reduced-cusp insertion on neighboring regular latitude rectangles

This file performs the pointwise insertion which was missing between the
one-variable reduced-cusp analysis and the literal neighboring-band
estimates.  The statements concern the actual latitude kernel, not an
abstract local remainder.
-/

open MeasureTheory Set

namespace BEMOC

set_option maxHeartbeats 800000

/-- Once the common manuscript depth is at least `600`, the entire
neighboring rectangle lies in the unit normalized-gap chart.  The large
constant merely records the deliberately coarse radius floor already used
elsewhere in the comparable analysis. -/
theorem neighboringComparable_rectangle_normalizedLatitudeGap_le_one
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    normalizedLatitudeGap s t ≤ 1 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hdreal : (0 : ℝ) < latitudeBandScale N j := by
    exact_mod_cast latitudeBandScale_pos N j
  let R : ℝ := (latitudeBandScale N j : ℝ) /
    (10 * (bandCount N : ℝ))
  have hR : 0 < R := by dsimp [R]; positivity
  have hgeom := comparableSame_rectangle_geometry hM hjk.1 hs ht
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hspos : 0 < heightRadius s := hR.trans_le hgeom.1.1
  have htpos : 0 < heightRadius t := hR.trans_le hgeom.1.2
  have hsInterior : s ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · by_contra h
      have : s = -1 := by linarith [hsSphere.1]
      subst s
      norm_num [heightRadius] at hspos
    · by_contra h
      have : s = 1 := by linarith [hsSphere.2]
      subst s
      norm_num [heightRadius] at hspos
  have htInterior : t ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · by_contra h
      have : t = -1 := by linarith [htSphere.1]
      subst t
      norm_num [heightRadius] at htpos
    · by_contra h
      have : t = 1 := by linarith [htSphere.2]
      subst t
      norm_num [heightRadius] at htpos
  have hpop :=
    finiteBandPopulations_le_four_scales_of_same hjk.1.2.2.1
  have hcomp := hjk.1.2.2.2
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤
        8 * (latitudeBandScale N j : ℝ) := by
    have hpR :
        (finiteBandPopulation N k : ℝ) ≤
          4 * (latitudeBandScale N k : ℝ) := by
      exact_mod_cast hpop.2
    have hscaleR :
        (latitudeBandScale N k : ℝ) ≤
          2 * (latitudeBandScale N j : ℝ) := by
      exact_mod_cast hcomp.2
    linarith
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤
        4 * (latitudeBandScale N j : ℝ) := by
    exact_mod_cast hpop.1
  have hfourR :
      4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  have ha :
      neighboringBandLength N j k ≤
        6 * (latitudeBandScale N j : ℝ) /
          (bandCount N : ℝ) ^ 2 := by
    rw [neighboringBandLength_eq_populations hN]
    apply (div_le_div_iff₀ hNreal (sq_pos_of_pos hMreal)).2
    nlinarith
  have hdepthR : (600 : ℝ) ≤ latitudeBandScale N j := by
    exact_mod_cast hdepth
  have haR2 : neighboringBandLength N j k ≤ R ^ 2 := by
    calc
      neighboringBandLength N j k ≤
          6 * (latitudeBandScale N j : ℝ) /
            (bandCount N : ℝ) ^ 2 := ha
      _ ≤ R ^ 2 := by
        have hdineq :
            600 * (latitudeBandScale N j : ℝ) ≤
              (latitudeBandScale N j : ℝ) ^ 2 := by
          nlinarith
        calc
          6 * (latitudeBandScale N j : ℝ) /
                (bandCount N : ℝ) ^ 2 ≤
              (latitudeBandScale N j : ℝ) ^ 2 /
                (100 * (bandCount N : ℝ) ^ 2) := by
            rw [show
              (latitudeBandScale N j : ℝ) ^ 2 /
                  (100 * (bandCount N : ℝ) ^ 2) =
                ((latitudeBandScale N j : ℝ) ^ 2 / 100) /
                  (bandCount N : ℝ) ^ 2 by ring]
            apply div_le_div_of_nonneg_right
            · nlinarith
            · positivity
          _ = R ^ 2 := by
            dsimp [R]
            field_simp [hMreal.ne']
            ring
  have hw :=
    abs_sub_le_neighboringBandLength j k hjk.2 hs ht
  have hrprod :
      R ^ 2 ≤ heightRadius s * heightRadius t := by
    nlinarith [mul_le_mul hgeom.1.1 hgeom.1.2 hR.le
      (show 0 ≤ heightRadius s by unfold heightRadius; positivity)]
  have hwprod :
      |s - t| ≤ heightRadius s * heightRadius t :=
    hw.trans (haR2.trans hrprod)
  have hq0 : 0 ≤ normalizedLatitudeGap s t := by
    rw [normalizedLatitudeGap_eq hsInterior htInterior]
    exact div_nonneg (latitudeRadialGapSq_nonneg s t)
      (by unfold latitudeAngularScale; positivity)
  have hid := normalizedLatitudeGap_mul_add_two hsInterior htInterior
  have hr0 : 0 ≤ heightRadius s * heightRadius t := by positivity
  have hsq :
      (s - t) ^ 2 ≤
        (heightRadius s * heightRadius t) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hwprod 2
  have hrpos : 0 < (heightRadius s * heightRadius t) ^ 2 := by positivity
  apply le_of_not_gt
  intro hqgt
  have hprodgt :
      3 < normalizedLatitudeGap s t *
        (normalizedLatitudeGap s t + 2) := by nlinarith
  have := mul_lt_mul_of_pos_left hprodgt hrpos
  rw [hid] at this
  linarith

noncomputable def neighboringUpperAnalyticKernel (α s t : ℝ) : ℝ :=
  latitudeAngularScale s t ^ (α / 2) *
    (reducedCuspUpperConstantCoefficient α +
      reducedCuspUpperLinearCoefficient α *
        normalizedLatitudeGap s t)

noncomputable def neighboringUpperBranchKernel (α s t : ℝ) : ℝ :=
  latitudeAngularScale s t ^ (α / 2) *
    (normalizedLatitudeGap s t ^ reducedCuspUpperNu α *
      reducedCuspUpperBranchFactor α (normalizedLatitudeGap s t))

theorem latitudeKernel_eq_neighboringUpperAnalytic_add_branch
    {α s t : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hst : s ≠ t) (hq1 : normalizedLatitudeGap s t ≤ 1) :
    latitudeKernel α s t =
      neighboringUpperAnalyticKernel α s t +
        neighboringUpperBranchKernel α s t := by
  have hq := normalizedLatitudeGap_pos hs ht hst
  have hdec :=
    (reducedLatitudeCusp_eq_upperAffine_add_powerBranch
      hα1 hα2 hq hq1).1
  rw [latitudeKernel_eq_variableReducedLatitudeKernel hs ht]
  unfold variableReducedLatitudeKernel neighboringUpperAnalyticKernel
    neighboringUpperBranchKernel
  rw [hdec]
  ring

theorem abs_neighboringUpperBranchKernel_le
    {α s t : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hst : s ≠ t) (hq1 : normalizedLatitudeGap s t ≤ 1) :
    |neighboringUpperBranchKernel α s t| ≤
      latitudeAngularScale s t ^ (α / 2) *
        normalizedLatitudeGap s t ^ reducedCuspUpperNu α *
          (reducedCuspD2MajorantCoefficient α /
            ((reducedCuspUpperNu α - 1) *
              reducedCuspUpperNu α)) := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hq := normalizedLatitudeGap_pos hs ht hst
  have hb :=
    (reducedLatitudeCusp_eq_upperAffine_add_powerBranch
      hα1 hα2 hq hq1).2
  unfold neighboringUpperBranchKernel
  rw [abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hp.le _),
    abs_of_nonneg (Real.rpow_nonneg hq.le _)]
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hb
      (Real.rpow_nonneg hq.le (reducedCuspUpperNu α)))
    (Real.rpow_nonneg hp.le (α / 2))
  simpa only [mul_assoc] using hmul

noncomputable def neighboringLowerAnalyticKernel (α s t : ℝ) : ℝ :=
  latitudeAngularScale s t ^ (α / 2) *
    reducedCuspLowerConstantCoefficient α

noncomputable def neighboringLowerBranchKernel (α s t : ℝ) : ℝ :=
  latitudeAngularScale s t ^ (α / 2) *
    (normalizedLatitudeGap s t ^ reducedCuspUpperNu α *
      reducedCuspLowerBranchFactor α (normalizedLatitudeGap s t))

theorem latitudeKernel_eq_neighboringLowerAnalytic_add_branch
    {α s t : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hst : s ≠ t) (hq1 : normalizedLatitudeGap s t ≤ 1) :
    latitudeKernel α s t =
      neighboringLowerAnalyticKernel α s t +
        neighboringLowerBranchKernel α s t := by
  have hq := normalizedLatitudeGap_pos hs ht hst
  have hdec :=
    (reducedLatitudeCusp_eq_lowerConstant_add_powerBranch
      hα0 hα1 hq hq1).1
  rw [latitudeKernel_eq_variableReducedLatitudeKernel hs ht]
  unfold variableReducedLatitudeKernel neighboringLowerAnalyticKernel
    neighboringLowerBranchKernel
  rw [hdec]
  ring

theorem abs_neighboringLowerBranchKernel_le
    {α s t : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hst : s ≠ t) (hq1 : normalizedLatitudeGap s t ≤ 1) :
    |neighboringLowerBranchKernel α s t| ≤
      latitudeAngularScale s t ^ (α / 2) *
        normalizedLatitudeGap s t ^ reducedCuspUpperNu α *
          (reducedCuspLowerD1MajorantCoefficient α /
            reducedCuspUpperNu α) := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hq := normalizedLatitudeGap_pos hs ht hst
  have hb :=
    (reducedLatitudeCusp_eq_lowerConstant_add_powerBranch
      hα0 hα1 hq hq1).2
  unfold neighboringLowerBranchKernel
  rw [abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hp.le _),
    abs_of_nonneg (Real.rpow_nonneg hq.le _)]
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hb
      (Real.rpow_nonneg hq.le (reducedCuspUpperNu α)))
    (Real.rpow_nonneg hp.le (α / 2))
  simpa only [mul_assoc] using hmul

noncomputable def neighboringResonantModelKernel (s t : ℝ) : ℝ :=
  latitudeAngularScale s t ^ (1 / 2 : ℝ) *
    (reducedCuspResonantConstantCoefficient +
      reducedCuspResonantLinearCoefficient * normalizedLatitudeGap s t +
      reducedCuspResonantPrincipalCoefficient *
        normalizedLatitudeGap s t *
          Real.log (normalizedLatitudeGap s t))

noncomputable def neighboringResonantHigherBranchKernel (s t : ℝ) : ℝ :=
  latitudeAngularScale s t ^ (1 / 2 : ℝ) *
    (normalizedLatitudeGap s t ^ (3 / 2 : ℝ) *
      reducedCuspResonantBranchFactor (normalizedLatitudeGap s t))

theorem latitudeKernel_one_eq_neighboringResonantModel_add_branch
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t)
    (hq1 : normalizedLatitudeGap s t ≤ 1) :
    latitudeKernel 1 s t =
      neighboringResonantModelKernel s t +
        neighboringResonantHigherBranchKernel s t := by
  have hq := normalizedLatitudeGap_pos hs ht hst
  have hdec :=
    (reducedLatitudeCusp_one_eq_resonant_decomposition hq hq1).1
  rw [latitudeKernel_eq_variableReducedLatitudeKernel hs ht]
  unfold variableReducedLatitudeKernel neighboringResonantModelKernel
    neighboringResonantHigherBranchKernel
  norm_num
  rw [hdec]
  ring

theorem abs_neighboringResonantHigherBranchKernel_le
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t)
    (hq1 : normalizedLatitudeGap s t ≤ 1) :
    |neighboringResonantHigherBranchKernel s t| ≤
      latitudeAngularScale s t ^ (1 / 2 : ℝ) *
        normalizedLatitudeGap s t ^ (3 / 2 : ℝ) *
          ((4 / 3 : ℝ) * reducedCuspResonantRemainderCoefficient) := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hq := normalizedLatitudeGap_pos hs ht hst
  have hb :=
    (reducedLatitudeCusp_one_eq_resonant_decomposition hq hq1).2
  unfold neighboringResonantHigherBranchKernel
  rw [abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hp.le _),
    abs_of_nonneg (Real.rpow_nonneg hq.le _)]
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hb
      (Real.rpow_nonneg hq.le (3 / 2 : ℝ)))
    (Real.rpow_nonneg hp.le (1 / 2 : ℝ))
  simpa only [mul_assoc] using hmul

theorem abs_bandPairError_neighboringUpperBranchKernel_le_of_rectangle
    {α C : ℝ} (hC : 0 ≤ C)
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (hrect : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
        |neighboringUpperBranchKernel α s t| ≤ C) :
    |bandPairError N j k (neighboringUpperBranchKernel α)| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) * C := by
  exact abs_bandPairError_le_of_band_rectangle_bound
    hN j k _ C hC hrect

theorem abs_bandPairError_neighboringLowerBranchKernel_le_of_rectangle
    {α C : ℝ} (hC : 0 ≤ C)
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (hrect : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
        |neighboringLowerBranchKernel α s t| ≤ C) :
    |bandPairError N j k (neighboringLowerBranchKernel α)| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) * C := by
  exact abs_bandPairError_le_of_band_rectangle_bound
    hN j k _ C hC hrect

theorem abs_bandPairError_neighboringResonantHigherBranchKernel_le_of_rectangle
    {C : ℝ} (hC : 0 ≤ C)
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (hrect : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
        |neighboringResonantHigherBranchKernel s t| ≤ C) :
    |bandPairError N j k neighboringResonantHigherBranchKernel| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) * C := by
  exact abs_bandPairError_le_of_band_rectangle_bound
    hN j k _ C hC hrect

end BEMOC
