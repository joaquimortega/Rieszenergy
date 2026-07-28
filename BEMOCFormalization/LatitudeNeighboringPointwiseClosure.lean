import BEMOCFormalization.LatitudeNeighboringSmoothTaylor
import BEMOCFormalization.LatitudePointwiseAssembly
import BEMOCFormalization.LatitudeComparableDerivativeEnvelope
import BEMOCFormalization.LatitudeResonantExtraction

/-!
# Pointwise closure for neighboring regular comparable latitude blocks

This module inserts the neighboring local chart into the pointwise
comparable-block interface.  The first theorem below closes, without any
analytic premise, the finite-depth branch left over by the unit-chart
geometry.
-/

open Set

namespace BEMOC

set_option maxHeartbeats 800000

/-- The constant used to absorb all regular neighboring depths below `600`
and the distance weight (which is at worst `2^(α-3)`). -/
noncomputable def neighboringSmallDepthBlockConstant (α : ℝ) : ℝ :=
  614400 *
    (8 * ((1200 : ℝ) * (2 * 1200 + 1) / 2)) ^ (α / 2)

theorem neighboringSmallDepthBlockConstant_pos
    {α : ℝ} :
    0 < neighboringSmallDepthBlockConstant α := by
  unfold neighboringSmallDepthBlockConstant
  positivity

/-- The premise-free finite-depth estimate, converted to the exact
`comparableLatitudeBlockMajorant` interface. -/
theorem neighboringComparable_smallDepth_block_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : NeighboringComparableLatitudePair N j k)
    (hsmall : latitudeBandScale N j < 600) :
    |bandPairError N j k (latitudeKernel α)| ≤
      comparableLatitudeBlockMajorant α
        (neighboringSmallDepthBlockConstant α) N j k := by
  have hraw :=
    abs_bandPairError_neighboringComparable_smallDepth hα0.le
      hM j k hjk hsmall
  have hpops :=
    finiteBandPopulations_le_four_scales_of_same hjk.1.2.2.1
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤
        4 * (latitudeBandScale N j : ℝ) := by
    exact_mod_cast hpops.1
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤
        4 * (latitudeBandScale N k : ℝ) := by
    exact_mod_cast hpops.2
  have hcomp := hjk.1.2.2.2
  have hdk :
      (latitudeBandScale N k : ℝ) ≤
        2 * (latitudeBandScale N j : ℝ) := by
    exact_mod_cast hcomp.2
  have hd :
      (latitudeBandScale N j : ℝ) ≤ 600 := by
    exact_mod_cast (show latitudeBandScale N j ≤ 600 by omega)
  have hpop :
      4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) ≤
        76800 * (latitudeBandScale N j : ℝ) := by
    have hd0 : (0 : ℝ) ≤ latitudeBandScale N j := by positivity
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hpj) (sub_nonneg.mpr hpk)]
  have hMpos : (0 : ℝ) < bandCount N := by exact_mod_cast (by omega :
    0 < bandCount N)
  let A : ℝ := 8 * ((1200 : ℝ) * (2 * 1200 + 1) / 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hrpow :
      (8 * ((1200 : ℝ) * (2 * 1200 + 1) /
          (2 * (bandCount N : ℝ) ^ 2))) ^ (α / 2) =
        A ^ (α / 2) * (bandCount N : ℝ) ^ (-α) := by
    rw [show
      8 * ((1200 : ℝ) * (2 * 1200 + 1) /
          (2 * (bandCount N : ℝ) ^ 2)) =
        A / (bandCount N : ℝ) ^ 2 by
          dsimp [A]
          ring]
    rw [Real.div_rpow hA.le (sq_nonneg _),
      show (bandCount N : ℝ) ^ 2 =
        (bandCount N : ℝ) ^ (2 : ℝ) by
          exact (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hMpos.le, div_eq_mul_inv,
      ← Real.rpow_neg hMpos.le]
    congr 2
    ring
  have hD :
      (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ≤ 2 := by
    have hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1 := hjk.2
    exact_mod_cast (show
      1 + Nat.dist (j : ℕ) (k : ℕ) ≤ 2 by omega)
  have he : α - 3 ≤ 0 := by linarith
  have hweight :
      (1 : ℝ) / 8 ≤
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
    have hbase :
        (0 : ℝ) < 1 + Nat.dist (j : ℕ) (k : ℕ) := by positivity
    have hpow := Real.rpow_le_rpow_of_nonpos hbase hD he
    have htwo :
        (2 : ℝ) ^ (-3 : ℝ) ≤ 2 ^ (α - 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    norm_num at htwo ⊢
    exact htwo.trans hpow
  unfold comparableLatitudeBlockMajorant
  rw [hrpow] at hraw
  calc
    |bandPairError N j k (latitudeKernel α)| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (A ^ (α / 2) * (bandCount N : ℝ) ^ (-α)) := hraw
    _ ≤ 76800 * (latitudeBandScale N j : ℝ) *
          (A ^ (α / 2) * (bandCount N : ℝ) ^ (-α)) := by
      gcongr
    _ ≤ neighboringSmallDepthBlockConstant α *
          (latitudeBandScale N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) *
          (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
      unfold neighboringSmallDepthBlockConstant
      dsimp [A]
      have hnonneg :
          0 ≤ 76800 * (latitudeBandScale N j : ℝ) *
            ((8 * ((1200 : ℝ) * (2 * 1200 + 1) / 2)) ^
              (α / 2) * (bandCount N : ℝ) ^ (-α)) := by
        positivity
      nlinarith

/-- Uniform interior and unit-gap chart data on the large-depth neighboring
rectangle.  This version includes the diagonal (`q = 0`). -/
theorem neighboringComparable_largeDepth_rectangle_chart
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧
      0 ≤ normalizedLatitudeGap s t ∧
      normalizedLatitudeGap s t ≤ 1 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  let R := comparableLatitudeRadiusFloor N j
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hdr : (0 : ℝ) < latitudeBandScale N j := by
      exact_mod_cast latitudeBandScale_pos N j
    positivity
  have hfloor := (comparableSame_rectangle_geometry hM hjk.1 hs ht).1
  have hspos : 0 < heightRadius s := hR.trans_le (by simpa [R] using hfloor.1)
  have htpos : 0 < heightRadius t := hR.trans_le (by simpa [R] using hfloor.2)
  have hsI : s ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · by_contra h
      have : s = -1 := by linarith [hsSphere.1]
      subst s
      norm_num [heightRadius] at hspos
    · by_contra h
      have : s = 1 := by linarith [hsSphere.2]
      subst s
      norm_num [heightRadius] at hspos
  have htI : t ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · by_contra h
      have : t = -1 := by linarith [htSphere.1]
      subst t
      norm_num [heightRadius] at htpos
    · by_contra h
      have : t = 1 := by linarith [htSphere.2]
      subst t
      norm_num [heightRadius] at htpos
  have hq0 : 0 ≤ normalizedLatitudeGap s t := by
    rw [normalizedLatitudeGap_eq hsI htI]
    exact div_nonneg (latitudeRadialGapSq_nonneg s t)
      (by unfold latitudeAngularScale; positivity)
  exact ⟨hsI, htI, hq0,
    neighboringComparable_rectangle_normalizedLatitudeGap_le_one
      hM hjk hdepth hs ht⟩

/-- The normalized neighboring gap has the sharp quadratic upper scale
coming from `r² q(q+2) = (s-t)²` and the common radius floor. -/
theorem neighboringComparable_normalizedGap_le_physicalSq
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    normalizedLatitudeGap s t ≤
      (s - t) ^ 2 /
        (2 * comparableLatitudeRadiusFloor N j ^ 4) := by
  let R := comparableLatitudeRadiusFloor N j
  have hchart :=
    neighboringComparable_largeDepth_rectangle_chart hM hjk hdepth hs ht
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hdr : (0 : ℝ) < latitudeBandScale N j := by
      exact_mod_cast latitudeBandScale_pos N j
    positivity
  have hfloor := (comparableSame_rectangle_geometry hM hjk.1 hs ht).1
  have hrs : R ≤ heightRadius s := by simpa [R] using hfloor.1
  have hrt : R ≤ heightRadius t := by simpa [R] using hfloor.2
  let q := normalizedLatitudeGap s t
  have hq0 : 0 ≤ q := by simpa [q] using hchart.2.2.1
  have hrprod :
      R ^ 2 ≤ heightRadius s * heightRadius t := by
    nlinarith [mul_le_mul hrs hrt hR.le
      (show 0 ≤ heightRadius s by unfold heightRadius; positivity)]
  have hrpow :
      R ^ 4 ≤ (heightRadius s * heightRadius t) ^ 2 := by
    nlinarith [sq_nonneg
      (heightRadius s * heightRadius t - R ^ 2)]
  have hq2 : 2 * q ≤ q * (q + 2) := by nlinarith [sq_nonneg q]
  have hmul :
      2 * R ^ 4 * q ≤
        (heightRadius s * heightRadius t) ^ 2 * (q * (q + 2)) := by
    calc
      2 * R ^ 4 * q = R ^ 4 * (2 * q) := by ring
      _ ≤ (heightRadius s * heightRadius t) ^ 2 * (q * (q + 2)) := by
        exact mul_le_mul hrpow hq2 (by positivity) (by positivity)
  have hid := normalizedLatitudeGap_mul_add_two hchart.1 hchart.2.1
  dsimp [q] at hmul
  rw [hid] at hmul
  dsimp [R] at hmul
  apply (le_div_iff₀ (by
    have : 0 < comparableLatitudeRadiusFloor N j := by simpa [R] using hR
    positivity)).2
  nlinarith

/-- Positive-real homogeneity arithmetic for the physical neighboring cusp.
The deliberately coarse constant `3200^(α/2)` comes from the common radius
ceiling. -/
theorem neighboring_power_cusp_scale
    {α p q R w : ℝ} (hα : 0 < α) (hR : 0 < R)
    (hp0 : 0 ≤ p) (hp : p ≤ 3200 * R ^ 2)
    (hq0 : 0 ≤ q) (hq : q ≤ |w| ^ 2 * R ^ (-4 : ℝ)) :
    p ^ (α / 2) * q ^ ((1 + α) / 2) ≤
      (3200 : ℝ) ^ (α / 2) *
        (R ^ (-2 - α) * |w| ^ (1 + α)) := by
  have hαhalf : 0 ≤ α / 2 := by linarith
  have hν : 0 ≤ (1 + α) / 2 := by linarith
  have hpR : 0 ≤ 3200 * R ^ 2 := by positivity
  have hqR : 0 ≤ |w| ^ 2 * R ^ (-4 : ℝ) := by positivity
  have hpPow :
      p ^ (α / 2) ≤ (3200 * R ^ 2) ^ (α / 2) :=
    Real.rpow_le_rpow hp0 hp hαhalf
  have hqPow :
      q ^ ((1 + α) / 2) ≤
        (|w| ^ 2 * R ^ (-4 : ℝ)) ^ ((1 + α) / 2) :=
    Real.rpow_le_rpow hq0 hq hν
  calc
    p ^ (α / 2) * q ^ ((1 + α) / 2) ≤
        (3200 * R ^ 2) ^ (α / 2) *
          (|w| ^ 2 * R ^ (-4 : ℝ)) ^ ((1 + α) / 2) := by
      gcongr
    _ = (3200 : ℝ) ^ (α / 2) *
        (R ^ (-2 - α) * |w| ^ (1 + α)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3200) (sq_nonneg R),
        Real.mul_rpow (sq_nonneg |w|)
          (Real.rpow_nonneg hR.le (-4 : ℝ))]
      rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le,
        ← Real.rpow_mul hR.le]
      rw [← Real.rpow_natCast |w| 2,
        ← Real.rpow_mul (abs_nonneg w)]
      norm_num
      rw [show (2 : ℝ) * (α / 2) = α by ring,
        show (2 : ℝ) * ((1 + α) / 2) = 1 + α by ring,
        show -(4 * ((1 + α) / 2)) = -2 - 2 * α by ring]
      calc
        3200 ^ (α / 2) * R ^ α *
              (|w| ^ (1 + α) * R ^ (-2 - 2 * α)) =
            3200 ^ (α / 2) *
              ((R ^ α * R ^ (-2 - 2 * α)) * |w| ^ (1 + α)) := by
                ring
        _ = _ := by
          rw [← Real.rpow_add hR]
          congr 2
          ring

/-- The universal geometric factor in both nonresonant neighboring
power branches has the expected physical cusp scale. -/
theorem neighboringComparable_powerFactor_le
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    latitudeAngularScale s t ^ (α / 2) *
        normalizedLatitudeGap s t ^ reducedCuspUpperNu α ≤
      (3200 : ℝ) ^ (α / 2) *
        (comparableLatitudeRadiusFloor N j ^ (-2 - α) *
          |s - t| ^ (1 + α)) := by
  let R := comparableLatitudeRadiusFloor N j
  have hchart :=
    neighboringComparable_largeDepth_rectangle_chart hM hjk hdepth hs ht
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hdr : (0 : ℝ) < latitudeBandScale N j := by
      exact_mod_cast latitudeBandScale_pos N j
    positivity
  have hceil :=
    comparableSame_rectangle_common_radius_ceiling hM hjk.1 hs ht
  have hp0 : 0 ≤ latitudeAngularScale s t := by
    unfold latitudeAngularScale
    positivity
  have hp :
      latitudeAngularScale s t ≤ 3200 * R ^ 2 := by
    change 2 * heightRadius s * heightRadius t ≤ 3200 * R ^ 2
    have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
    have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
    have hm :
        heightRadius s * heightRadius t ≤ (40 * R) * (40 * R) := by
      exact mul_le_mul
        (by simpa [R] using hceil.1) (by simpa [R] using hceil.2)
        hrt0 (by positivity)
    calc
      2 * heightRadius s * heightRadius t =
          2 * (heightRadius s * heightRadius t) := by ring
      _ ≤ 2 * ((40 * R) * (40 * R)) := by gcongr
      _ = 3200 * R ^ 2 := by ring
  have hqPhysical :=
    neighboringComparable_normalizedGap_le_physicalSq
      hM hjk hdepth hs ht
  have hq :
      normalizedLatitudeGap s t ≤
        |s - t| ^ 2 * R ^ (-4 : ℝ) := by
    have hR4 : 0 < R ^ 4 := by positivity
    have hinv :
        (2 * R ^ 4)⁻¹ ≤ (R ^ 4)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) hR4]
      nlinarith
    have hw0 : 0 ≤ |s - t| ^ 2 := sq_nonneg _
    calc
      normalizedLatitudeGap s t ≤
          (s - t) ^ 2 / (2 * R ^ 4) := by
        simpa [R] using hqPhysical
      _ = |s - t| ^ 2 * (2 * R ^ 4)⁻¹ := by
        rw [div_eq_mul_inv, sq_abs]
      _ ≤ |s - t| ^ 2 * (R ^ 4)⁻¹ := by gcongr
      _ = |s - t| ^ 2 * R ^ (-4 : ℝ) := by
        rw [Real.rpow_neg hR.le]
        simpa only using congrArg
          (fun x : ℝ ↦ |s - t| ^ 2 * x⁻¹)
          (Real.rpow_natCast R 4).symm
  simpa [R, reducedCuspUpperNu, add_comm] using
    neighboring_power_cusp_scale hα0 hR hp0 hp hchart.2.2.1 hq

/-- The upper nonresonant branch is bounded by a constant multiple of the
physical `|s-t|^(1+α)` cusp on every large-depth neighboring rectangle. -/
theorem abs_neighboringUpperBranchKernel_le_physicalCusp
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hst : s ≠ t) :
    |neighboringUpperBranchKernel α s t| ≤
      ((3200 : ℝ) ^ (α / 2) *
        (reducedCuspD2MajorantCoefficient α /
          ((reducedCuspUpperNu α - 1) *
            reducedCuspUpperNu α))) *
      (comparableLatitudeRadiusFloor N j ^ (-2 - α) *
        |s - t| ^ (1 + α)) := by
  have hchart :=
    neighboringComparable_largeDepth_rectangle_chart hM hjk hdepth hs ht
  have hraw := abs_neighboringUpperBranchKernel_le hα1 hα2
    hchart.1 hchart.2.1 hst hchart.2.2.2
  have hfactor := neighboringComparable_powerFactor_le
    (by linarith : 0 < α) hα2 hM hjk hdepth hs ht
  have hcoef :
      0 ≤ reducedCuspD2MajorantCoefficient α /
        ((reducedCuspUpperNu α - 1) *
          reducedCuspUpperNu α) := by
    apply div_nonneg (reducedCuspD2MajorantCoefficient_nonneg α)
    unfold reducedCuspUpperNu
    exact mul_nonneg (by linarith) (by linarith)
  calc
    |neighboringUpperBranchKernel α s t| ≤
        (latitudeAngularScale s t ^ (α / 2) *
          normalizedLatitudeGap s t ^ reducedCuspUpperNu α) *
            (reducedCuspD2MajorantCoefficient α /
              ((reducedCuspUpperNu α - 1) *
                reducedCuspUpperNu α)) := by
      simpa only [mul_assoc] using hraw
    _ ≤ ((3200 : ℝ) ^ (α / 2) *
          (comparableLatitudeRadiusFloor N j ^ (-2 - α) *
            |s - t| ^ (1 + α))) *
            (reducedCuspD2MajorantCoefficient α /
              ((reducedCuspUpperNu α - 1) *
                reducedCuspUpperNu α)) := by
      gcongr
    _ = _ := by ring

theorem abs_neighboringUpperBranchKernel_le_physicalCusp_onRectangle
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringUpperBranchKernel α s t| ≤
      ((3200 : ℝ) ^ (α / 2) *
        (reducedCuspD2MajorantCoefficient α /
          ((reducedCuspUpperNu α - 1) *
            reducedCuspUpperNu α))) *
      (comparableLatitudeRadiusFloor N j ^ (-2 - α) *
        |s - t| ^ (1 + α)) := by
  by_cases hst : s = t
  · subst t
    have hsI :=
      (neighboringComparable_largeDepth_rectangle_chart
        hM hjk hdepth hs ht).1
    have hr : heightRadius s ≠ 0 := (heightRadius_pos hsI).ne'
    have hrsq := heightRadius_sq ⟨hsI.1.le, hsI.2.le⟩
    have hden : 1 - s * s ≠ 0 := by
      rw [← show heightRadius s * heightRadius s = 1 - s * s by
        nlinarith]
      exact mul_ne_zero hr hr
    have hq : normalizedLatitudeGap s s = 0 := by
      unfold normalizedLatitudeGap
      rw [show heightRadius s * heightRadius s = 1 - s * s by
        nlinarith]
      field_simp [hden]
    have hznu : (0 : ℝ) ^ ((1 + α) / 2) = 0 :=
      Real.zero_rpow (by linarith)
    rw [show neighboringUpperBranchKernel α s s = 0 by
      unfold neighboringUpperBranchKernel
      rw [hq]
      rw [show reducedCuspUpperNu α = (1 + α) / 2 by
        rfl, hznu]
      ring]
    simp only [abs_zero, sub_self]
    rw [Real.zero_rpow (by linarith : 1 + α ≠ 0)]
    ring_nf
    norm_num
  · exact abs_neighboringUpperBranchKernel_le_physicalCusp
      hα1 hα2 hM hjk hdepth hs ht hst

/-- The lower nonresonant branch obeys the identical physical cusp scale. -/
theorem abs_neighboringLowerBranchKernel_le_physicalCusp
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hst : s ≠ t) :
    |neighboringLowerBranchKernel α s t| ≤
      ((3200 : ℝ) ^ (α / 2) *
        (reducedCuspLowerD1MajorantCoefficient α /
          reducedCuspUpperNu α)) *
      (comparableLatitudeRadiusFloor N j ^ (-2 - α) *
        |s - t| ^ (1 + α)) := by
  have hchart :=
    neighboringComparable_largeDepth_rectangle_chart hM hjk hdepth hs ht
  have hraw := abs_neighboringLowerBranchKernel_le hα0 hα1
    hchart.1 hchart.2.1 hst hchart.2.2.2
  have hfactor := neighboringComparable_powerFactor_le
    hα0 (by linarith : α < 2) hM hjk hdepth hs ht
  have hcoef :
      0 ≤ reducedCuspLowerD1MajorantCoefficient α /
        reducedCuspUpperNu α := by
    exact div_nonneg
      (reducedCuspLowerD1MajorantCoefficient_nonneg hα1)
      (by unfold reducedCuspUpperNu; linarith)
  calc
    |neighboringLowerBranchKernel α s t| ≤
        (latitudeAngularScale s t ^ (α / 2) *
          normalizedLatitudeGap s t ^ reducedCuspUpperNu α) *
            (reducedCuspLowerD1MajorantCoefficient α /
              reducedCuspUpperNu α) := by
      simpa only [mul_assoc] using hraw
    _ ≤ ((3200 : ℝ) ^ (α / 2) *
          (comparableLatitudeRadiusFloor N j ^ (-2 - α) *
            |s - t| ^ (1 + α))) *
            (reducedCuspLowerD1MajorantCoefficient α /
              reducedCuspUpperNu α) := by
      gcongr
    _ = _ := by ring

theorem abs_neighboringLowerBranchKernel_le_physicalCusp_onRectangle
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringLowerBranchKernel α s t| ≤
      ((3200 : ℝ) ^ (α / 2) *
        (reducedCuspLowerD1MajorantCoefficient α /
          reducedCuspUpperNu α)) *
      (comparableLatitudeRadiusFloor N j ^ (-2 - α) *
        |s - t| ^ (1 + α)) := by
  by_cases hst : s = t
  · subst t
    have hsI :=
      (neighboringComparable_largeDepth_rectangle_chart
        hM hjk hdepth hs ht).1
    have hr : heightRadius s ≠ 0 := (heightRadius_pos hsI).ne'
    have hrsq := heightRadius_sq ⟨hsI.1.le, hsI.2.le⟩
    have hden : 1 - s * s ≠ 0 := by
      rw [← show heightRadius s * heightRadius s = 1 - s * s by
        nlinarith]
      exact mul_ne_zero hr hr
    have hq : normalizedLatitudeGap s s = 0 := by
      unfold normalizedLatitudeGap
      rw [show heightRadius s * heightRadius s = 1 - s * s by
        nlinarith]
      field_simp [hden]
    have hznu : (0 : ℝ) ^ ((1 + α) / 2) = 0 :=
      Real.zero_rpow (by linarith)
    rw [show neighboringLowerBranchKernel α s s = 0 by
      unfold neighboringLowerBranchKernel
      rw [hq]
      rw [show reducedCuspUpperNu α = (1 + α) / 2 by
        rfl, hznu]
      ring]
    simp only [abs_zero, sub_self]
    rw [Real.zero_rpow (by linarith : 1 + α ≠ 0)]
    ring_nf
    norm_num
  · exact abs_neighboringLowerBranchKernel_le_physicalCusp
      hα0 hα1 hM hjk hdepth hs ht hst

/-- Population geometry bounds the common neighboring rescaling length by
the sharp manuscript height scale. -/
theorem neighboringComparable_bandLength_le_scale
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k) :
    neighboringBandLength N j k ≤
      6 * (latitudeBandScale N j : ℝ) /
        (bandCount N : ℝ) ^ 2 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hpop :=
    finiteBandPopulations_le_four_scales_of_same hjk.1.2.2.1
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤
        4 * (latitudeBandScale N j : ℝ) := by exact_mod_cast hpop.1
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤
        8 * (latitudeBandScale N j : ℝ) := by
    have hpk' :
        (finiteBandPopulation N k : ℝ) ≤
          4 * (latitudeBandScale N k : ℝ) := by exact_mod_cast hpop.2
    have hcomp :
        (latitudeBandScale N k : ℝ) ≤
          2 * (latitudeBandScale N j : ℝ) := by
      exact_mod_cast hjk.1.2.2.2.2
    linarith
  have hfour :
      4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  rw [neighboringBandLength_eq_populations hN]
  apply (div_le_div_iff₀ hNreal (sq_pos_of_pos hMreal)).2
  nlinarith

private theorem neighboringCuspScale_identity
    {α d M : ℝ} (hd : 0 < d) (hM : 0 < M) :
    (d / (10 * M)) ^ (-2 - α) *
        (6 * d / M ^ 2) ^ (1 + α) =
      (10 : ℝ) ^ (2 + α) * (6 : ℝ) ^ (1 + α) *
        d ^ (-1 : ℝ) * M ^ (-α) := by
  rw [Real.div_rpow hd.le (by positivity : 0 ≤ 10 * M),
    Real.div_rpow (by positivity : 0 ≤ 6 * d) (sq_nonneg M)]
  rw [div_eq_mul_inv, div_eq_mul_inv,
    ← Real.rpow_neg (by positivity : 0 ≤ 10 * M),
    ← Real.rpow_neg (sq_nonneg M)]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) hM.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) hd.le]
  rw [← Real.rpow_natCast M 2, ← Real.rpow_mul hM.le]
  calc
    d ^ (-2 - α) *
          (10 ^ (-(-2 - α)) * M ^ (-(-2 - α))) *
        (6 ^ (1 + α) * d ^ (1 + α) *
          M ^ ((2 : ℝ) * (-(1 + α)))) =
      (10 ^ (2 + α) * 6 ^ (1 + α)) *
        (d ^ (-2 - α) * d ^ (1 + α)) *
        (M ^ (2 + α) * M ^ (-2 - 2 * α)) := by
          ring_nf
    _ = (10 : ℝ) ^ (2 + α) * 6 ^ (1 + α) *
        d ^ (-1 : ℝ) * M ^ (-α) := by
      rw [← Real.rpow_add hd, ← Real.rpow_add hM]
      congr 1 <;> ring

/-- A rectangle bound by a physical neighboring cusp is already at the
comparable block scale.  This is the literal fixed-rectangle transfer used
for both nonresonant branches. -/
theorem neighboringComparable_block_bound_of_physicalCusp
    {α B : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hB : 0 ≤ B)
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : NeighboringComparableLatitudePair N j k)
    (K : ℝ → ℝ → ℝ)
    (hrect :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          |K s t| ≤
            B * (comparableLatitudeRadiusFloor N j ^ (-2 - α) *
              |s - t| ^ (1 + α))) :
    |bandPairError N j k K| ≤
      comparableLatitudeBlockMajorant α
        (1024 * B * (10 : ℝ) ^ (2 + α) *
          (6 : ℝ) ^ (1 + α)) N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let d : ℝ := latitudeBandScale N j
  let M : ℝ := bandCount N
  let a : ℝ := neighboringBandLength N j k
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast latitudeBandScale_pos N j
  have hMr : 0 < M := by dsimp [M]; positivity
  have ha : 0 < a := by
    dsimp [a]
    exact neighboringBandLength_pos hN hM j k
  have halen : a ≤ 6 * d / M ^ 2 := by
    simpa [a, d, M] using
      neighboringComparable_bandLength_le_scale (by omega) hjk
  have hpow :
      a ^ (1 + α) ≤ (6 * d / M ^ 2) ^ (1 + α) :=
    Real.rpow_le_rpow ha.le halen (by linarith)
  have hR : 0 < comparableLatitudeRadiusFloor N j := by
    unfold comparableLatitudeRadiusFloor
    positivity
  have hC :
      0 ≤ B * (comparableLatitudeRadiusFloor N j ^ (-2 - α) *
        a ^ (1 + α)) := by positivity
  have hpair :
      |bandPairError N j k K| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (B * (comparableLatitudeRadiusFloor N j ^ (-2 - α) *
              a ^ (1 + α))) := by
    apply abs_bandPairError_le_of_band_rectangle_bound hN j k K _ hC
    intro s hs t ht
    have hw := abs_sub_le_neighboringBandLength j k hjk.2 hs ht
    have hwpow :
        |s - t| ^ (1 + α) ≤ a ^ (1 + α) :=
      Real.rpow_le_rpow (abs_nonneg _) (by simpa [a] using hw)
        (by linarith)
    exact (hrect s hs t ht).trans (by gcongr)
  have hpops :=
    finiteBandPopulations_le_four_scales_of_same hjk.1.2.2.1
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤ 4 * d := by
    dsimp [d]
    exact_mod_cast hpops.1
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤ 8 * d := by
    have hpk' :
        (finiteBandPopulation N k : ℝ) ≤
          4 * (latitudeBandScale N k : ℝ) := by exact_mod_cast hpops.2
    have hdk :
        (latitudeBandScale N k : ℝ) ≤ 2 * d := by
      dsimp [d]
      exact_mod_cast hjk.1.2.2.2.2
    linarith
  have hpop :
      4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) ≤ 128 * d ^ 2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hpj) (sub_nonneg.mpr hpk)]
  have hscale :
      comparableLatitudeRadiusFloor N j ^ (-2 - α) *
          a ^ (1 + α) ≤
        (10 : ℝ) ^ (2 + α) * 6 ^ (1 + α) *
          d ^ (-1 : ℝ) * M ^ (-α) := by
    calc
      comparableLatitudeRadiusFloor N j ^ (-2 - α) *
          a ^ (1 + α) ≤
        comparableLatitudeRadiusFloor N j ^ (-2 - α) *
          (6 * d / M ^ 2) ^ (1 + α) := by gcongr
      _ = _ := by
        simpa [comparableLatitudeRadiusFloor, d, M] using
          neighboringCuspScale_identity (α := α) hd hMr
  have hdInv : d ^ (-1 : ℝ) = d⁻¹ := by
    rw [Real.rpow_neg hd.le, Real.rpow_one]
  have hD :
      (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ≤ 2 := by
    have hn := hjk.2
    exact_mod_cast (show
      1 + Nat.dist (j : ℕ) (k : ℕ) ≤ 2 by omega)
  have hweight :
      (1 : ℝ) / 8 ≤
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
    have hbase :
        (0 : ℝ) < 1 + Nat.dist (j : ℕ) (k : ℕ) := by positivity
    have hpowD := Real.rpow_le_rpow_of_nonpos hbase hD
      (by linarith : α - 3 ≤ 0)
    have htwo :
        (2 : ℝ) ^ (-3 : ℝ) ≤ 2 ^ (α - 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    norm_num at htwo ⊢
    exact htwo.trans hpowD
  unfold comparableLatitudeBlockMajorant
  calc
    |bandPairError N j k K| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (B * (comparableLatitudeRadiusFloor N j ^ (-2 - α) *
              a ^ (1 + α))) := hpair
    _ ≤ 128 * d ^ 2 *
          (B * ((10 : ℝ) ^ (2 + α) * 6 ^ (1 + α) *
            d ^ (-1 : ℝ) * M ^ (-α))) := by
      gcongr
    _ = 128 * B * (10 : ℝ) ^ (2 + α) * 6 ^ (1 + α) *
          d * M ^ (-α) := by
      rw [hdInv]
      field_simp [hd.ne']
      ring
    _ ≤ 1024 * B * (10 : ℝ) ^ (2 + α) * 6 ^ (1 + α) *
          d * M ^ (-α) *
          (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
      have hnonneg :
          0 ≤ 128 * B * (10 : ℝ) ^ (2 + α) * 6 ^ (1 + α) *
            d * M ^ (-α) := by positivity
      nlinarith
    _ = _ := by rfl

noncomputable def neighboringUpperBranchBlockConstant (α : ℝ) : ℝ :=
  1024 *
    ((3200 : ℝ) ^ (α / 2) *
      (reducedCuspD2MajorantCoefficient α /
        ((reducedCuspUpperNu α - 1) * reducedCuspUpperNu α))) *
    (10 : ℝ) ^ (2 + α) * (6 : ℝ) ^ (1 + α)

noncomputable def neighboringLowerBranchBlockConstant (α : ℝ) : ℝ :=
  1024 *
    ((3200 : ℝ) ^ (α / 2) *
      (reducedCuspLowerD1MajorantCoefficient α /
        reducedCuspUpperNu α)) *
    (10 : ℝ) ^ (2 + α) * (6 : ℝ) ^ (1 + α)

theorem abs_bandPairError_neighboringUpperBranchKernel_le
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j) :
    |bandPairError N j k (neighboringUpperBranchKernel α)| ≤
      comparableLatitudeBlockMajorant α
        (neighboringUpperBranchBlockConstant α) N j k := by
  let B := (3200 : ℝ) ^ (α / 2) *
    (reducedCuspD2MajorantCoefficient α /
      ((reducedCuspUpperNu α - 1) * reducedCuspUpperNu α))
  have hB : 0 ≤ B := by
    dsimp [B]
    apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    apply div_nonneg (reducedCuspD2MajorantCoefficient_nonneg α)
    unfold reducedCuspUpperNu
    exact mul_nonneg (by linarith) (by linarith)
  simpa [B, neighboringUpperBranchBlockConstant] using
    neighboringComparable_block_bound_of_physicalCusp
      (by linarith : 0 < α) hα2 hB hM j k hjk
      (neighboringUpperBranchKernel α)
      (fun s hs t ht ↦
        abs_neighboringUpperBranchKernel_le_physicalCusp_onRectangle
          hα1 hα2 (by omega) hjk hdepth hs ht)

theorem abs_bandPairError_neighboringLowerBranchKernel_le
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j) :
    |bandPairError N j k (neighboringLowerBranchKernel α)| ≤
      comparableLatitudeBlockMajorant α
        (neighboringLowerBranchBlockConstant α) N j k := by
  let B := (3200 : ℝ) ^ (α / 2) *
    (reducedCuspLowerD1MajorantCoefficient α /
      reducedCuspUpperNu α)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (div_nonneg
        (reducedCuspLowerD1MajorantCoefficient_nonneg hα1)
        (by unfold reducedCuspUpperNu; linarith))
  simpa [B, neighboringLowerBranchBlockConstant] using
    neighboringComparable_block_bound_of_physicalCusp
      hα0 (by linarith : α < 2) hB hM j k hjk
      (neighboringLowerBranchKernel α)
      (fun s hs t ht ↦
        abs_neighboringLowerBranchKernel_le_physicalCusp_onRectangle
          hα0 hα1 (by omega) hjk hdepth hs ht)

/-- The sole large-depth block input still needed after the concrete
finite-depth and geometric reductions in this file. -/
def HasLargeDepthNeighboringComparableLatitudeBlockBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    NeighboringComparableLatitudePair N j k →
    600 ≤ latitudeBandScale N j →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α C N j k

/-- Once the unit-chart large-depth insertion is supplied, the finite-depth
fallback proved above yields every neighboring regular comparable block.
The sum of constants avoids any maximum bookkeeping. -/
theorem neighboringComparable_block_bound_of_largeDepth
    {α C : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N) (hC : 0 ≤ C)
    (hlarge :
      HasLargeDepthNeighboringComparableLatitudeBlockBound α N C) :
    ∀ j k : Fin (bandTailCount N + 1),
      NeighboringComparableLatitudePair N j k →
        |bandPairError N j k (latitudeKernel α)| ≤
          comparableLatitudeBlockMajorant α
            (neighboringSmallDepthBlockConstant α + C) N j k := by
  intro j k hjk
  by_cases hdepth : 600 ≤ latitudeBandScale N j
  · exact (hlarge j k hjk hdepth).trans
      (comparableLatitudeBlockMajorant_mono
        (by
          have hs : 0 ≤ neighboringSmallDepthBlockConstant α :=
            (neighboringSmallDepthBlockConstant_pos
              (α := α)).le
          linarith))
  · have hsmall : latitudeBandScale N j < 600 := by omega
    exact
      (neighboringComparable_smallDepth_block_bound
        hα0 hα2 hM j k hjk hsmall).trans
        (comparableLatitudeBlockMajorant_mono (by linarith))

/-- Sharp smooth-part input for the upper nonresonant decomposition, stated
directly at the band-error level.  Writing it as a difference avoids
repeating interval-integrability bookkeeping in downstream assembly. -/
def HasLargeDepthNeighboringUpperSmoothBlockBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    NeighboringComparableLatitudePair N j k →
    600 ≤ latitudeBandScale N j →
      |bandPairError N j k (latitudeKernel α) -
          bandPairError N j k (neighboringUpperBranchKernel α)| ≤
        comparableLatitudeBlockMajorant α C N j k

/-- Lower-range analogue of
`HasLargeDepthNeighboringUpperSmoothBlockBound`. -/
def HasLargeDepthNeighboringLowerSmoothBlockBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    NeighboringComparableLatitudePair N j k →
    600 ≤ latitudeBandScale N j →
      |bandPairError N j k (latitudeKernel α) -
          bandPairError N j k (neighboringLowerBranchKernel α)| ≤
        comparableLatitudeBlockMajorant α C N j k

theorem neighboringComparable_largeDepth_upper_block_bound
    {α C : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N) (hC : 0 ≤ C)
    (hsmooth : HasLargeDepthNeighboringUpperSmoothBlockBound α N C) :
    HasLargeDepthNeighboringComparableLatitudeBlockBound α N
      (C + neighboringUpperBranchBlockConstant α) := by
  intro j k hjk hdepth
  have hs := hsmooth j k hjk hdepth
  have hb := abs_bandPairError_neighboringUpperBranchKernel_le
    hα1 hα2 hM j k hjk hdepth
  have htri :
      |bandPairError N j k (latitudeKernel α)| ≤
        |bandPairError N j k (latitudeKernel α) -
          bandPairError N j k (neighboringUpperBranchKernel α)| +
        |bandPairError N j k (neighboringUpperBranchKernel α)| := by
    calc
      |bandPairError N j k (latitudeKernel α)| =
          |(bandPairError N j k (latitudeKernel α) -
              bandPairError N j k (neighboringUpperBranchKernel α)) +
            bandPairError N j k (neighboringUpperBranchKernel α)| := by
              congr 1
              ring
      _ ≤ _ := abs_add _ _
  calc
    |bandPairError N j k (latitudeKernel α)| ≤
        |bandPairError N j k (latitudeKernel α) -
          bandPairError N j k (neighboringUpperBranchKernel α)| +
        |bandPairError N j k (neighboringUpperBranchKernel α)| := htri
    _ ≤ comparableLatitudeBlockMajorant α C N j k +
        comparableLatitudeBlockMajorant α
          (neighboringUpperBranchBlockConstant α) N j k :=
      add_le_add hs hb
    _ = comparableLatitudeBlockMajorant α
        (C + neighboringUpperBranchBlockConstant α) N j k := by
      unfold comparableLatitudeBlockMajorant
      ring

theorem neighboringComparable_largeDepth_lower_block_bound
    {α C : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 3 ≤ bandCount N) (hC : 0 ≤ C)
    (hsmooth : HasLargeDepthNeighboringLowerSmoothBlockBound α N C) :
    HasLargeDepthNeighboringComparableLatitudeBlockBound α N
      (C + neighboringLowerBranchBlockConstant α) := by
  intro j k hjk hdepth
  have hs := hsmooth j k hjk hdepth
  have hb := abs_bandPairError_neighboringLowerBranchKernel_le
    hα0 hα1 hM j k hjk hdepth
  have htri :
      |bandPairError N j k (latitudeKernel α)| ≤
        |bandPairError N j k (latitudeKernel α) -
          bandPairError N j k (neighboringLowerBranchKernel α)| +
        |bandPairError N j k (neighboringLowerBranchKernel α)| := by
    calc
      |bandPairError N j k (latitudeKernel α)| =
          |(bandPairError N j k (latitudeKernel α) -
              bandPairError N j k (neighboringLowerBranchKernel α)) +
            bandPairError N j k (neighboringLowerBranchKernel α)| := by
              congr 1
              ring
      _ ≤ _ := abs_add _ _
  calc
    |bandPairError N j k (latitudeKernel α)| ≤
        |bandPairError N j k (latitudeKernel α) -
          bandPairError N j k (neighboringLowerBranchKernel α)| +
        |bandPairError N j k (neighboringLowerBranchKernel α)| := htri
    _ ≤ comparableLatitudeBlockMajorant α C N j k +
        comparableLatitudeBlockMajorant α
          (neighboringLowerBranchBlockConstant α) N j k :=
      add_le_add hs hb
    _ = comparableLatitudeBlockMajorant α
        (C + neighboringLowerBranchBlockConstant α) N j k := by
      unfold comparableLatitudeBlockMajorant
      ring

theorem neighboringComparable_upper_block_bound_of_smooth
    {α C : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N) (hC : 0 ≤ C)
    (hsmooth : HasLargeDepthNeighboringUpperSmoothBlockBound α N C) :
    ∀ j k : Fin (bandTailCount N + 1),
      NeighboringComparableLatitudePair N j k →
        |bandPairError N j k (latitudeKernel α)| ≤
          comparableLatitudeBlockMajorant α
            (neighboringSmallDepthBlockConstant α + C +
              neighboringUpperBranchBlockConstant α) N j k := by
  have hlarge := neighboringComparable_largeDepth_upper_block_bound
    hα1 hα2 hM hC hsmooth
  simpa [add_assoc] using
    neighboringComparable_block_bound_of_largeDepth
      (by linarith : 0 < α) hα2 (by omega) (by
        have hb : 0 ≤ neighboringUpperBranchBlockConstant α := by
          unfold neighboringUpperBranchBlockConstant
          have hc :
              0 ≤ reducedCuspD2MajorantCoefficient α /
                ((reducedCuspUpperNu α - 1) *
                  reducedCuspUpperNu α) := by
            apply div_nonneg (reducedCuspD2MajorantCoefficient_nonneg α)
            unfold reducedCuspUpperNu
            exact mul_nonneg (by linarith) (by linarith)
          positivity
        linarith) hlarge

theorem neighboringComparable_lower_block_bound_of_smooth
    {α C : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 3 ≤ bandCount N) (hC : 0 ≤ C)
    (hsmooth : HasLargeDepthNeighboringLowerSmoothBlockBound α N C) :
    ∀ j k : Fin (bandTailCount N + 1),
      NeighboringComparableLatitudePair N j k →
        |bandPairError N j k (latitudeKernel α)| ≤
          comparableLatitudeBlockMajorant α
            (neighboringSmallDepthBlockConstant α + C +
              neighboringLowerBranchBlockConstant α) N j k := by
  have hlarge := neighboringComparable_largeDepth_lower_block_bound
    hα0 hα1 hM hC hsmooth
  simpa [add_assoc] using
    neighboringComparable_block_bound_of_largeDepth
      hα0 (by linarith : α < 2) (by omega) (by
        have hb : 0 ≤ neighboringLowerBranchBlockConstant α := by
          unfold neighboringLowerBranchBlockConstant
          have hc :
              0 ≤ reducedCuspLowerD1MajorantCoefficient α /
                reducedCuspUpperNu α :=
            div_nonneg
              (reducedCuspLowerD1MajorantCoefficient_nonneg hα1)
              (by unfold reducedCuspUpperNu; linarith)
          positivity
        linarith) hlarge

/-- Dimensionless quadratic-gap coefficient used in the normalized
resonant chart. -/
noncomputable def neighboringNormalizedQuadraticCoefficient
    (R s t : ℝ) : ℝ :=
  R ^ 4 * latitudeQuadraticGapCoefficient s t

/-- Dimensionless angular coefficient multiplying the normalized resonant
cusp. -/
noncomputable def neighboringNormalizedAngularCoefficient
    (R s t : ℝ) : ℝ :=
  latitudeAngularScale s t ^ (1 / 2 : ℝ) / R

/-- Uniform coefficient bounds in any positive-radius unit-gap chart.
This formulation is independent of the band classification and can also be
reused by central neighboring rectangles. -/
theorem neighboring_normalized_resonant_coefficients_bounded
    {R s t : ℝ} (hR : 0 < R)
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t)
    (hsceil : heightRadius s ≤ 40 * R)
    (htceil : heightRadius t ≤ 40 * R)
    (hq0 : 0 ≤ normalizedLatitudeGap s t)
    (hq1 : normalizedLatitudeGap s t ≤ 1) :
    0 < neighboringNormalizedQuadraticCoefficient R s t ∧
      neighboringNormalizedQuadraticCoefficient R s t ≤ (1 : ℝ) / 2 ∧
      0 < neighboringNormalizedAngularCoefficient R s t ∧
      neighboringNormalizedAngularCoefficient R s t ≤ 3200 := by
  let r := heightRadius s * heightRadius t
  let q := normalizedLatitudeGap s t
  have hrs : 0 < heightRadius s := hR.trans_le hsfloor
  have hrt : 0 < heightRadius t := hR.trans_le htfloor
  have hr : 0 < r := by dsimp [r]; positivity
  have hrlo : R ^ 2 ≤ r := by
    dsimp [r]
    nlinarith [mul_le_mul hsfloor htfloor hR.le hrs.le]
  have hrhi : r ≤ 1600 * R ^ 2 := by
    dsimp [r]
    calc
      heightRadius s * heightRadius t ≤ (40 * R) * (40 * R) := by
        exact mul_le_mul hsceil htceil hrt.le (by positivity)
      _ = 1600 * R ^ 2 := by ring
  have hr2lo : R ^ 4 ≤ r ^ 2 := by
    nlinarith [sq_nonneg (r - R ^ 2)]
  let den := r ^ 2 * (q + 2)
  have hden : 0 < den := by dsimp [den]; positivity
  have hdenlo : 2 * R ^ 4 ≤ den := by
    dsimp [den]
    have hq2 : (2 : ℝ) ≤ q + 2 := by dsimp [q]; linarith
    calc
      2 * R ^ 4 = R ^ 4 * 2 := by ring
      _ ≤ r ^ 2 * 2 := by gcongr
      _ ≤ r ^ 2 * (q + 2) := by gcongr
  have hcpos := latitudeQuadraticGapCoefficient_pos hs ht
  have hceq :
      latitudeQuadraticGapCoefficient s t = den⁻¹ := by
    rfl
  have hcupper :
      latitudeQuadraticGapCoefficient s t ≤ (2 * R ^ 4)⁻¹ := by
    rw [hceq]
    exact (inv_le_inv₀ (a := den) (b := 2 * R ^ 4)
      hden (by positivity)).2 hdenlo
  have hnormCpos :
      0 < neighboringNormalizedQuadraticCoefficient R s t := by
    unfold neighboringNormalizedQuadraticCoefficient
    positivity
  have hnormCup :
      neighboringNormalizedQuadraticCoefficient R s t ≤ (1 : ℝ) / 2 := by
    unfold neighboringNormalizedQuadraticCoefficient
    have hm := mul_le_mul_of_nonneg_left hcupper (by positivity : 0 ≤ R ^ 4)
    have hR4 : 0 < R ^ 4 := by positivity
    calc
      R ^ 4 * latitudeQuadraticGapCoefficient s t ≤
          R ^ 4 * (2 * R ^ 4)⁻¹ := hm
      _ = (1 : ℝ) / 2 := by
        field_simp [hR4.ne']
        ring
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    positivity
  have hpupper :
      latitudeAngularScale s t ≤ 3200 * R ^ 2 := by
    change 2 * heightRadius s * heightRadius t ≤ 3200 * R ^ 2
    calc
      2 * heightRadius s * heightRadius t =
          2 * (heightRadius s * heightRadius t) := by ring
      _ ≤ 2 * (1600 * R ^ 2) := by
        simpa [r] using mul_le_mul_of_nonneg_left hrhi (by norm_num : (0 : ℝ) ≤ 2)
      _ = 3200 * R ^ 2 := by ring
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hpPow :
      latitudeAngularScale s t ^ (1 / 2 : ℝ) ≤
        (3200 * R ^ 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hp.le hpupper hhalf
  have hpScale :
      (3200 * R ^ 2) ^ (1 / 2 : ℝ) =
        (3200 : ℝ) ^ (1 / 2 : ℝ) * R := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3200) (sq_nonneg R),
      ← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le]
    norm_num
  have h3200 :
      (3200 : ℝ) ^ (1 / 2 : ℝ) ≤ 3200 := by
    have hone : (1 : ℝ) ≤ 3200 := by norm_num
    have := Real.rpow_le_rpow_of_exponent_le hone
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
    norm_num at this
    simpa using this
  have hnormPpos :
      0 < neighboringNormalizedAngularCoefficient R s t := by
    unfold neighboringNormalizedAngularCoefficient
    positivity
  have hnormPup :
      neighboringNormalizedAngularCoefficient R s t ≤ 3200 := by
    unfold neighboringNormalizedAngularCoefficient
    rw [div_le_iff₀ hR]
    calc
      latitudeAngularScale s t ^ (1 / 2 : ℝ) ≤
          (3200 * R ^ 2) ^ (1 / 2 : ℝ) := hpPow
      _ = (3200 : ℝ) ^ (1 / 2 : ℝ) * R := hpScale
      _ ≤ 3200 * R := by gcongr
  exact ⟨hnormCpos, hnormCup, hnormPpos, hnormPup⟩

/-- Concrete specialization of the normalized resonant coefficient bounds
to every large-depth regular neighboring rectangle. -/
theorem neighboringComparable_normalized_resonant_coefficients_bounded
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    0 < neighboringNormalizedQuadraticCoefficient
        (comparableLatitudeRadiusFloor N j) s t ∧
      neighboringNormalizedQuadraticCoefficient
        (comparableLatitudeRadiusFloor N j) s t ≤ (1 : ℝ) / 2 ∧
      0 < neighboringNormalizedAngularCoefficient
        (comparableLatitudeRadiusFloor N j) s t ∧
      neighboringNormalizedAngularCoefficient
        (comparableLatitudeRadiusFloor N j) s t ≤ 3200 := by
  have hchart :=
    neighboringComparable_largeDepth_rectangle_chart hM hjk hdepth hs ht
  have hfloor := (comparableSame_rectangle_geometry hM hjk.1 hs ht).1
  have hceil :=
    comparableSame_rectangle_common_radius_ceiling hM hjk.1 hs ht
  have hR : 0 < comparableLatitudeRadiusFloor N j := by
    unfold comparableLatitudeRadiusFloor
    positivity
  exact neighboring_normalized_resonant_coefficients_bounded hR
    hchart.1 hchart.2.1
    (by simpa [comparableLatitudeRadiusFloor] using hfloor.1)
    (by simpa [comparableLatitudeRadiusFloor] using hfloor.2)
    (by simpa [comparableLatitudeRadiusFloor] using hceil.1)
    (by simpa [comparableLatitudeRadiusFloor] using hceil.2)
    hchart.2.2.1 hchart.2.2.2

end BEMOC
