import BEMOCFormalization.LatitudeCentralComparableClosure
import BEMOCFormalization.LatitudeNeighboringRegularBlocks

/-!
# Endpoint closure for the resonant latitude decomposition

The positive-gap resonant decomposition has a bounded `x^(3/2)` remainder.
Together with the one-sided continuity of the reduced cusp, this identifies
its constant coefficient with the literal value at zero and closes the
kernel identity on the diagonal.
-/

open Filter Set
open scoped Topology

namespace BEMOC

set_option maxHeartbeats 800000

/-- The constant selected by the positive-gap resonant subtraction is the
literal endpoint value of the reduced cusp. -/
theorem reducedLatitudeCusp_one_zero_eq_resonantConstantCoefficient :
    reducedLatitudeCusp 1 0 =
      reducedCuspResonantConstantCoefficient := by
  let K : ℝ :=
    (4 / 3 : ℝ) * reducedCuspResonantRemainderCoefficient
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by norm_num)
      reducedCuspResonantRemainderCoefficient_nonneg
  have hx :
      Tendsto (fun x : ℝ ↦ x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hxlogFull :
      Tendsto (fun x : ℝ ↦ x * Real.log x) (𝓝 0) (𝓝 0) := by
    have hc :
        ContinuousAt (fun x : ℝ ↦ x * Real.log x) 0 :=
      Real.continuous_mul_log.continuousAt
    simpa using hc.tendsto
  have hxlog :
      Tendsto (fun x : ℝ ↦ x * Real.log x)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hxlogFull.mono_left inf_le_left
  have hxpowFull :
      Tendsto (fun x : ℝ ↦ x ^ (3 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
    have hc :
        ContinuousAt (fun x : ℝ ↦ x ^ (3 / 2 : ℝ)) 0 :=
      continuousAt_id.rpow_const (Or.inr (by norm_num))
    simpa [Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)] using
      hc.tendsto
  have hxpow :
      Tendsto (fun x : ℝ ↦ x ^ (3 / 2 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hxpowFull.mono_left inf_le_left
  have hone :
      ∀ᶠ x in 𝓝[>] (0 : ℝ), x ≤ 1 := by
    have honeFull : {x : ℝ | x ≤ 1} ∈ 𝓝 (0 : ℝ) := by
      apply mem_of_superset
        (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      intro x hx1
      change x < 1 at hx1
      change x ≤ 1
      exact hx1.le
    exact mem_inf_of_left honeFull
  have hbranchBound :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        |x ^ (3 / 2 : ℝ) * reducedCuspResonantBranchFactor x| ≤
          K * x ^ (3 / 2 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin, hone] with x hx0 hx1
    have hb :=
      (reducedLatitudeCusp_one_eq_resonant_decomposition hx0 hx1).2
    rw [abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hx0.le (3 / 2 : ℝ))]
    simpa [K, mul_comm] using
      mul_le_mul_of_nonneg_left hb
        (Real.rpow_nonneg hx0.le (3 / 2 : ℝ))
  have hbranchMajor :
      Tendsto (fun x : ℝ ↦ K * x ^ (3 / 2 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hxpow.const_mul K using 1 ; simp
  have hbranchAbs :
      Tendsto
        (fun x : ℝ ↦
          |x ^ (3 / 2 : ℝ) * reducedCuspResonantBranchFactor x|)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero'
      (Eventually.of_forall (fun _ ↦ abs_nonneg _))
      hbranchBound hbranchMajor
  have hbranch :
      Tendsto
        (fun x : ℝ ↦
          x ^ (3 / 2 : ℝ) * reducedCuspResonantBranchFactor x)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 hbranchAbs
  have hmodel :
      Tendsto
        (fun x : ℝ ↦
          reducedCuspResonantConstantCoefficient +
            reducedCuspResonantLinearCoefficient * x +
            reducedCuspResonantPrincipalCoefficient * x * Real.log x +
            x ^ (3 / 2 : ℝ) * reducedCuspResonantBranchFactor x)
        (𝓝[>] (0 : ℝ))
        (𝓝 reducedCuspResonantConstantCoefficient) := by
    have hlinear :=
      hx.const_mul reducedCuspResonantLinearCoefficient
    have hlog :=
      hxlog.const_mul reducedCuspResonantPrincipalCoefficient
    simpa [mul_assoc] using
      (((tendsto_const_nhds.add hlinear).add hlog).add hbranch)
  have hdecomp :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        reducedLatitudeCusp 1 x =
          reducedCuspResonantConstantCoefficient +
            reducedCuspResonantLinearCoefficient * x +
            reducedCuspResonantPrincipalCoefficient * x * Real.log x +
            x ^ (3 / 2 : ℝ) * reducedCuspResonantBranchFactor x := by
    filter_upwards [self_mem_nhdsWithin, hone] with x hx0 hx1
    exact
      (reducedLatitudeCusp_one_eq_resonant_decomposition hx0 hx1).1
  have hmodelEqCusp :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        (reducedCuspResonantConstantCoefficient +
            reducedCuspResonantLinearCoefficient * x +
            reducedCuspResonantPrincipalCoefficient * x * Real.log x +
            x ^ (3 / 2 : ℝ) * reducedCuspResonantBranchFactor x) =
          reducedLatitudeCusp 1 x := by
    filter_upwards [hdecomp] with x hx
    exact hx.symm
  have hcoefficient :
      Tendsto (reducedLatitudeCusp 1) (𝓝[>] (0 : ℝ))
        (𝓝 reducedCuspResonantConstantCoefficient) :=
    hmodel.congr' hmodelEqCusp
  exact tendsto_nhds_unique
    (tendsto_reducedLatitudeCusp_nhdsGT_zero
      (by norm_num) (by norm_num))
    hcoefficient

/-- Endpoint-complete resonant decomposition on the unit height chart. -/
theorem latitudeKernel_one_eq_neighboringResonantModel_add_branch_on_unitChart
    {s t : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hq1 : normalizedLatitudeGap s t ≤ 1) :
    latitudeKernel 1 s t =
      neighboringResonantModelKernel s t +
        neighboringResonantHigherBranchKernel s t := by
  by_cases hst : s = t
  · subst t
    rw [latitudeKernel_eq_variableReducedLatitudeKernel hs hs]
    have hq :
        normalizedLatitudeGap s s = 0 := by
      simpa using
        normalizedLatitudeGap_eq_quadraticCoefficient_mul_sq hs hs
    unfold variableReducedLatitudeKernel neighboringResonantModelKernel
      neighboringResonantHigherBranchKernel
    rw [hq,
      reducedLatitudeCusp_one_zero_eq_resonantConstantCoefficient,
      Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  · exact latitudeKernel_one_eq_neighboringResonantModel_add_branch
      hs ht hst hq1

end BEMOC
