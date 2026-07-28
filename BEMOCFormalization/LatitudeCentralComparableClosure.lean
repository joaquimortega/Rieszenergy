import BEMOCFormalization.LatitudeCentralSmoothBlockTransfer
import BEMOCFormalization.LatitudeOppositeComparableClosure

/-!
# Central comparable-scale latitude closure

This module supplies the fixed equatorial geometry and the Peano scale
conversion for comparable rectangles having one central band.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace BEMOC

set_option maxHeartbeats 800000

/-- The defining angular integral is Hölder continuous at the cusp
endpoint.  This elementary estimate is the missing endpoint input in the
local subtraction formulas: unlike their positive-gap FTC proofs, it also
controls the literal diagonal samples in a band quadrature. -/
theorem abs_reducedLatitudeCusp_sub_zero_le
    {α x : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hx : 0 ≤ x) :
    |reducedLatitudeCusp α x - reducedLatitudeCusp α 0| ≤
      x ^ (α / 2) := by
  let β : ℝ := α / 2
  let f : ℝ → ℝ :=
    fun θ ↦ (x + (1 - Real.cos θ)) ^ β
  let g : ℝ → ℝ :=
    fun θ ↦ (1 - Real.cos θ) ^ β
  have hβ0 : 0 < β := by dsimp [β]; linarith
  have hβ1 : β ≤ 1 := by dsimp [β]; linarith
  have hf : Continuous f := by
    dsimp [f]
    exact
      (continuous_const.add
        (continuous_const.sub Real.continuous_cos)).rpow_const
          (fun _ ↦ Or.inr hβ0.le)
  have hg : Continuous g := by
    dsimp [g]
    exact
      (continuous_const.sub Real.continuous_cos).rpow_const
        (fun _ ↦ Or.inr hβ0.le)
  have hpointLower (θ : ℝ) : g θ ≤ f θ := by
    dsimp [f, g]
    apply Real.rpow_le_rpow
      (sub_nonneg.mpr (Real.cos_le_one θ))
    · linarith
    · exact hβ0.le
  have hpointUpper (θ : ℝ) :
      f θ ≤ g θ + x ^ β := by
    dsimp [f, g]
    simpa [add_comm] using
      Real.rpow_add_le_add_rpow hx
        (sub_nonneg.mpr (Real.cos_le_one θ)) hβ0.le hβ1
  have hlen : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hlower :
      (∫ θ in (0 : ℝ)..2 * Real.pi, g θ) ≤
        ∫ θ in (0 : ℝ)..2 * Real.pi, f θ :=
    intervalIntegral.integral_mono_on hlen
      (hg.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
      (fun θ _ ↦ hpointLower θ)
  have hupper :
      (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) ≤
        ∫ θ in (0 : ℝ)..2 * Real.pi, (g θ + x ^ β) := by
    exact intervalIntegral.integral_mono_on hlen
      (hf.intervalIntegrable _ _)
      ((hg.add continuous_const).intervalIntegrable _ _)
      (fun θ _ ↦ hpointUpper θ)
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hdiff :
      0 ≤ reducedLatitudeCusp α x - reducedLatitudeCusp α 0 ∧
      reducedLatitudeCusp α x - reducedLatitudeCusp α 0 ≤ x ^ β := by
    rw [reducedLatitudeCusp_eq_moment,
      reducedLatitudeCusp_eq_moment]
    unfold reducedCuspMoment
    simp only [zero_add]
    change
      0 ≤ (1 / (2 * Real.pi)) *
          (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) -
            (1 / (2 * Real.pi)) *
              (∫ θ in (0 : ℝ)..2 * Real.pi, g θ) ∧
        (1 / (2 * Real.pi)) *
          (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) -
            (1 / (2 * Real.pi)) *
              (∫ θ in (0 : ℝ)..2 * Real.pi, g θ) ≤ x ^ β
    constructor
    · exact sub_nonneg.mpr
        (mul_le_mul_of_nonneg_left hlower (by positivity))
    · rw [intervalIntegral.integral_add
          (hg.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_const] at hupper
      simp only [smul_eq_mul] at hupper
      have hraw :
          (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) -
              (∫ θ in (0 : ℝ)..2 * Real.pi, g θ) ≤
            (2 * Real.pi) * x ^ β := by
        linarith
      calc
        (1 / (2 * Real.pi)) *
              (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) -
            (1 / (2 * Real.pi)) *
              (∫ θ in (0 : ℝ)..2 * Real.pi, g θ) =
            (1 / (2 * Real.pi)) *
              ((∫ θ in (0 : ℝ)..2 * Real.pi, f θ) -
                ∫ θ in (0 : ℝ)..2 * Real.pi, g θ) := by ring
        _ ≤ (1 / (2 * Real.pi)) *
              ((2 * Real.pi) * x ^ β) :=
          mul_le_mul_of_nonneg_left hraw (by positivity)
        _ = x ^ β := by field_simp
  rw [abs_of_nonneg hdiff.1]
  simpa [β] using hdiff.2

theorem tendsto_reducedLatitudeCusp_nhdsGT_zero
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Tendsto (reducedLatitudeCusp α) (𝓝[>] (0 : ℝ))
      (𝓝 (reducedLatitudeCusp α 0)) := by
  let β : ℝ := α / 2
  have hβ0 : 0 < β := by dsimp [β]; linarith
  have hrpowFull :
      Tendsto (fun x : ℝ ↦ x ^ β) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ ↦ x ^ β) 0 :=
      continuousAt_id.rpow_const (Or.inr hβ0.le)
    simpa [Real.zero_rpow hβ0.ne'] using hc.tendsto
  have hrpow :
      Tendsto (fun x : ℝ ↦ x ^ β) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hrpowFull.mono_left inf_le_left
  have hbound :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        |reducedLatitudeCusp α x - reducedLatitudeCusp α 0| ≤
          x ^ β := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact abs_reducedLatitudeCusp_sub_zero_le hα0 hα2 hx.le
  have habs :
      Tendsto
        (fun x : ℝ ↦
          |reducedLatitudeCusp α x - reducedLatitudeCusp α 0|)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero'
      (Eventually.of_forall (fun _ ↦ abs_nonneg _)) hbound hrpow
  have hsub :
      Tendsto
        (fun x : ℝ ↦
          reducedLatitudeCusp α x - reducedLatitudeCusp α 0)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  convert hsub.add_const (reducedLatitudeCusp α 0) using 1 <;> simp

theorem reducedLatitudeCusp_zero_eq_upperConstantCoefficient
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    reducedLatitudeCusp α 0 =
      reducedCuspUpperConstantCoefficient α := by
  let ν := reducedCuspUpperNu α
  let K :=
    reducedCuspD2MajorantCoefficient α /
      ((reducedCuspUpperNu α - 1) * reducedCuspUpperNu α)
  have hν : 0 < ν := by dsimp [ν, reducedCuspUpperNu]; linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    apply div_nonneg (reducedCuspD2MajorantCoefficient_nonneg α)
    unfold reducedCuspUpperNu
    exact mul_nonneg (by linarith) (by linarith)
  have hxlim :
      Tendsto (fun x : ℝ ↦ x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hpowFull :
      Tendsto (fun x : ℝ ↦ x ^ ν) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ ↦ x ^ ν) 0 :=
      continuousAt_id.rpow_const (Or.inr hν.le)
    simpa [Real.zero_rpow hν.ne'] using hc.tendsto
  have hpow :
      Tendsto (fun x : ℝ ↦ x ^ ν) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hpowFull.mono_left inf_le_left
  have hmajor :
      Tendsto
        (fun x : ℝ ↦
          |reducedCuspUpperLinearCoefficient α| * x + K * x ^ ν)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert
      (hxlim.const_mul
        |reducedCuspUpperLinearCoefficient α|).add
        (hpow.const_mul K) using 1 <;> simp
  have hone :
      ∀ᶠ x in 𝓝[>] (0 : ℝ), x ≤ 1 := by
    have honeFull : {x : ℝ | x ≤ 1} ∈ 𝓝 (0 : ℝ) := by
      apply mem_of_superset
        (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      show {x : ℝ | x < 1} ⊆ {x : ℝ | x ≤ 1}
      intro x hx
      change x < 1 at hx
      change x ≤ 1
      exact hx.le
    exact mem_inf_of_left honeFull
  have hbound :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        |reducedLatitudeCusp α x -
            reducedCuspUpperConstantCoefficient α| ≤
          |reducedCuspUpperLinearCoefficient α| * x + K * x ^ ν := by
    filter_upwards [self_mem_nhdsWithin, hone] with x hx hx1
    have hdec :=
      reducedLatitudeCusp_eq_upperAffine_add_powerBranch
        hα1 hα2 hx hx1
    calc
      |reducedLatitudeCusp α x -
          reducedCuspUpperConstantCoefficient α| =
          |reducedCuspUpperLinearCoefficient α * x +
            x ^ ν * reducedCuspUpperBranchFactor α x| := by
              rw [hdec.1]
              dsimp [ν]
              congr 1
              ring
      _ ≤ |reducedCuspUpperLinearCoefficient α * x| +
          |x ^ ν * reducedCuspUpperBranchFactor α x| :=
        abs_add _ _
      _ = |reducedCuspUpperLinearCoefficient α| * x +
          x ^ ν * |reducedCuspUpperBranchFactor α x| := by
        rw [abs_mul, abs_mul,
          show |x| = x from abs_of_pos hx,
          show |x ^ ν| = x ^ ν from
            abs_of_nonneg (Real.rpow_nonneg hx.le _)]
      _ ≤ |reducedCuspUpperLinearCoefficient α| * x +
          K * x ^ ν := by
        have hb : |reducedCuspUpperBranchFactor α x| ≤ K := by
          simpa [K] using hdec.2
        nlinarith [mul_le_mul_of_nonneg_left hb
          (Real.rpow_nonneg hx.le ν)]
  have habs :
      Tendsto
        (fun x : ℝ ↦
          |reducedLatitudeCusp α x -
            reducedCuspUpperConstantCoefficient α|)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero'
      (Eventually.of_forall (fun _ ↦ abs_nonneg _)) hbound hmajor
  have hsub :
      Tendsto
        (fun x : ℝ ↦
          reducedLatitudeCusp α x -
            reducedCuspUpperConstantCoefficient α)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  have hcoeff :
      Tendsto (reducedLatitudeCusp α) (𝓝[>] (0 : ℝ))
        (𝓝 (reducedCuspUpperConstantCoefficient α)) := by
    convert hsub.add_const
      (reducedCuspUpperConstantCoefficient α) using 1 <;> simp
  exact tendsto_nhds_unique
    (tendsto_reducedLatitudeCusp_nhdsGT_zero (by linarith) hα2)
    hcoeff

theorem reducedLatitudeCusp_zero_eq_lowerConstantCoefficient
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    reducedLatitudeCusp α 0 =
      reducedCuspLowerConstantCoefficient α := by
  let ν := reducedCuspUpperNu α
  let K :=
    reducedCuspLowerD1MajorantCoefficient α /
      reducedCuspUpperNu α
  have hν : 0 < ν := by dsimp [ν, reducedCuspUpperNu]; linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg
      (reducedCuspLowerD1MajorantCoefficient_nonneg hα1)
      (by unfold reducedCuspUpperNu; linarith)
  have hpowFull :
      Tendsto (fun x : ℝ ↦ x ^ ν) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ ↦ x ^ ν) 0 :=
      continuousAt_id.rpow_const (Or.inr hν.le)
    simpa [Real.zero_rpow hν.ne'] using hc.tendsto
  have hpow :
      Tendsto (fun x : ℝ ↦ x ^ ν) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hpowFull.mono_left inf_le_left
  have hmajor :
      Tendsto (fun x : ℝ ↦ K * x ^ ν)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hpow.const_mul K using 1 <;> simp
  have hone :
      ∀ᶠ x in 𝓝[>] (0 : ℝ), x ≤ 1 := by
    have honeFull : {x : ℝ | x ≤ 1} ∈ 𝓝 (0 : ℝ) := by
      apply mem_of_superset
        (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      show {x : ℝ | x < 1} ⊆ {x : ℝ | x ≤ 1}
      intro x hx
      change x < 1 at hx
      change x ≤ 1
      exact hx.le
    exact mem_inf_of_left honeFull
  have hbound :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        |reducedLatitudeCusp α x -
            reducedCuspLowerConstantCoefficient α| ≤
          K * x ^ ν := by
    filter_upwards [self_mem_nhdsWithin, hone] with x hx hx1
    have hdec :=
      reducedLatitudeCusp_eq_lowerConstant_add_powerBranch
        hα0 hα1 hx hx1
    calc
      |reducedLatitudeCusp α x -
          reducedCuspLowerConstantCoefficient α| =
          |x ^ ν * reducedCuspLowerBranchFactor α x| := by
            rw [hdec.1]
            dsimp [ν]
            congr 1
            ring
      _ = x ^ ν * |reducedCuspLowerBranchFactor α x| := by
        rw [abs_mul,
          show |x ^ ν| = x ^ ν from
            abs_of_nonneg (Real.rpow_nonneg hx.le _)]
      _ ≤ K * x ^ ν := by
        have hb : |reducedCuspLowerBranchFactor α x| ≤ K := by
          simpa [K] using hdec.2
        nlinarith [mul_le_mul_of_nonneg_left hb
          (Real.rpow_nonneg hx.le ν)]
  have habs :
      Tendsto
        (fun x : ℝ ↦
          |reducedLatitudeCusp α x -
            reducedCuspLowerConstantCoefficient α|)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero'
      (Eventually.of_forall (fun _ ↦ abs_nonneg _)) hbound hmajor
  have hsub :
      Tendsto
        (fun x : ℝ ↦
          reducedLatitudeCusp α x -
            reducedCuspLowerConstantCoefficient α)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 habs
  have hcoeff :
      Tendsto (reducedLatitudeCusp α) (𝓝[>] (0 : ℝ))
        (𝓝 (reducedCuspLowerConstantCoefficient α)) := by
    convert hsub.add_const
      (reducedCuspLowerConstantCoefficient α) using 1 <;> simp
  exact tendsto_nhds_unique
    (tendsto_reducedLatitudeCusp_nhdsGT_zero hα0
      (by linarith : α < 2))
    hcoeff

/-- Endpoint-complete upper local decomposition.  The earlier local theorem
requires a positive normalized gap; the coefficient identity above makes
the same formula valid on the literal diagonal. -/
theorem latitudeKernel_eq_neighboringUpperAnalytic_add_branch_on_unitChart
    {α s t : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hq1 : normalizedLatitudeGap s t ≤ 1) :
    latitudeKernel α s t =
      neighboringUpperAnalyticKernel α s t +
        neighboringUpperBranchKernel α s t := by
  by_cases hst : s = t
  · subst t
    rw [latitudeKernel_eq_variableReducedLatitudeKernel hs hs]
    have hq :
        normalizedLatitudeGap s s = 0 := by
      simpa using normalizedLatitudeGap_eq_quadraticCoefficient_mul_sq hs hs
    unfold variableReducedLatitudeKernel neighboringUpperAnalyticKernel
      neighboringUpperBranchKernel
    rw [hq, reducedLatitudeCusp_zero_eq_upperConstantCoefficient
      hα1 hα2]
    have hν : 0 < reducedCuspUpperNu α := by
      unfold reducedCuspUpperNu
      linarith
    rw [Real.zero_rpow hν.ne']
    ring
  · exact latitudeKernel_eq_neighboringUpperAnalytic_add_branch
      hα1 hα2 hs ht hst hq1

/-- Endpoint-complete lower local decomposition. -/
theorem latitudeKernel_eq_neighboringLowerAnalytic_add_branch_on_unitChart
    {α s t : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hq1 : normalizedLatitudeGap s t ≤ 1) :
    latitudeKernel α s t =
      neighboringLowerAnalyticKernel α s t +
        neighboringLowerBranchKernel α s t := by
  by_cases hst : s = t
  · subst t
    rw [latitudeKernel_eq_variableReducedLatitudeKernel hs hs]
    have hq :
        normalizedLatitudeGap s s = 0 := by
      simpa using normalizedLatitudeGap_eq_quadraticCoefficient_mul_sq hs hs
    unfold variableReducedLatitudeKernel neighboringLowerAnalyticKernel
      neighboringLowerBranchKernel
    rw [hq, reducedLatitudeCusp_zero_eq_lowerConstantCoefficient
      hα0 hα1]
    have hν : 0 < reducedCuspUpperNu α := by
      unfold reducedCuspUpperNu
      linarith
    rw [Real.zero_rpow hν.ne']
    ring
  · exact latitudeKernel_eq_neighboringLowerAnalytic_add_branch
      hα0 hα1 hs ht hst hq1

/-- Pair-error linearity from a decomposition known only on the literal
rectangle.  A Tietze extension of the first summand turns the second one
into the difference of two globally continuous kernels, discharging all
inner and outer interval-integrability conditions. -/
theorem bandPairError_eq_add_of_continuous_decomposition_on_literalRectangle
    {N : ℕ} (j k : Fin (bandTailCount N + 1))
    (K A B : ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : ℝ × ℝ ↦ K p.1 p.2))
    (hA : ContinuousOn (fun p : ℝ × ℝ ↦ A p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)))
    (hdecomp :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          K s t = A s t + B s t) :
    bandPairError N j k K =
      bandPairError N j k A + bandPairError N j k B := by
  let Is : Set ℝ := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It : Set ℝ := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  let fA : C(Is ×ˢ It, ℝ) :=
    ⟨fun p ↦ A p.1.1 p.1.2,
      continuousOn_iff_continuous_restrict.mp hA⟩
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq
    (isClosed_Icc.prod isClosed_Icc) fA
  have hGeq : ∀ p ∈ Is ×ˢ It, G p = A p.1 p.2 := by
    intro p hp
    exact DFunLike.congr_fun hG (⟨p, hp⟩ : Is ×ˢ It)
  let Bext : ℝ → ℝ → ℝ := fun s t ↦ K s t - G (s, t)
  have hGc : Continuous (fun p : ℝ × ℝ ↦ G p) := G.continuous
  have hBc : Continuous (fun p : ℝ × ℝ ↦ Bext p.1 p.2) := by
    exact hK.sub hGc
  have hsum :
      bandPairError N j k K =
        bandPairError N j k (fun s t ↦ G (s, t)) +
          bandPairError N j k Bext := by
    have hfun :
        K = fun s t ↦ G (s, t) + Bext s t := by
      funext s t
      dsimp [Bext]
      ring
    rw [hfun]
    unfold bandPairError
    rw [show
      (fun s ↦ bandError N k
        (fun t ↦ G (s, t) + Bext s t)) =
      (fun s ↦
        bandError N k (fun t ↦ G (s, t)) +
          bandError N k (Bext s)) by
        funext s
        rw [bandError_add]
        · exact (G.continuous.comp
            (continuous_const.prodMk continuous_id)
            |>.intervalIntegrable _ _)
        · exact (hBc.comp
            (continuous_const.prodMk continuous_id)
            |>.intervalIntegrable _ _)]
    rw [bandError_add]
    · exact (continuous_bandError_right k hGc).intervalIntegrable _ _
    · exact (continuous_bandError_right k hBc).intervalIntegrable _ _
  have hpairA :
      bandPairError N j k (fun s t ↦ G (s, t)) =
        bandPairError N j k A := by
    apply bandPairError_congr_on_literalRectangle j k
    intro s hs t ht
    exact hGeq (s, t) ⟨hs, ht⟩
  have hpairB :
      bandPairError N j k Bext =
        bandPairError N j k B := by
    apply bandPairError_congr_on_literalRectangle j k
    intro s hs t ht
    have hGA : G (s, t) = A s t := hGeq (s, t) ⟨hs, ht⟩
    dsimp [Bext]
    rw [hGA, hdecomp s hs t ht]
    ring
  rw [hpairA, hpairB] at hsum
  exact hsum

/-- A band in a central comparable pair has a uniform radius floor.  The
constant `1/10` is deliberately loose; for the noncentral member it follows
from the regular-band radius estimate and factor-two comparability, while
the central member lies in the fixed equatorial chart. -/
theorem centralComparable_rectangle_heightRadius_floor
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 : ℝ) / 10 ≤ heightRadius s ∧
      (1 : ℝ) / 10 ≤ heightRadius t := by
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
  have centralFloor {i : Fin (bandTailCount N + 1)} {x : ℝ}
      (hi : IsCentralLatitudeBand N i)
      (hx : x ∈ Icc (bandBoundaryHeight N (i + 1))
        (bandBoundaryHeight N i)) :
      (1 : ℝ) / 10 ≤ heightRadius x := by
    have hieq :
        i = concreteCentralBandIndex N :=
      (isCentralLatitudeBand_iff_eq_concreteCentralBandIndex i).mp hi
    subst i
    have habs := abs_central_band_rectangle_le_quarter hM hx
    have hxsq : x ^ 2 ≤ (1 : ℝ) / 16 := by
      rw [← sq_abs]
      have hm := pow_le_pow_left₀ (abs_nonneg x) habs 2
      norm_num at hm ⊢
      exact hm
    have hr := heightRadius_sq
      (show x ∈ Icc (-1 : ℝ) 1 from
        ⟨(bandBoundaryHeight_mem hN
          (concreteCentralBandIndex N + 1)).1.trans hx.1,
          hx.2.trans
            (bandBoundaryHeight_mem hN
              (concreteCentralBandIndex N)).2⟩)
    have hr0 : 0 ≤ heightRadius x := by
      unfold heightRadius
      positivity
    nlinarith
  have regularFloor {i : Fin (bandTailCount N + 1)} {x : ℝ}
      (hiNot : ¬ IsCentralLatitudeBand N i)
      (hiNotPolar : ¬ IsPolarLatitudeBand N i)
      (hscale : bandCount N ≤ 2 * latitudeBandScale N i)
      (hx : x ∈ Icc (bandBoundaryHeight N (i + 1))
        (bandBoundaryHeight N i)) :
      (1 : ℝ) / 10 ≤ heightRadius x := by
    have hireg : IsRegularLatitudeBand N i :=
      regular_of_not_polar hiNotPolar
    rcases latitudeBand_region_trichotomy N i with hiN | hiC | hiS
    · have hf := northern_band_heightRadius_floor
        (by omega : 1 ≤ bandCount N) hiN hireg hx
      have hMpos : (0 : ℝ) < bandCount N := by positivity
      have hsR :
          (bandCount N : ℝ) ≤
            2 * (latitudeBandScale N i : ℝ) := by exact_mod_cast hscale
      calc
        (1 : ℝ) / 10 ≤
            (latitudeBandScale N i : ℝ) /
              (5 * (bandCount N : ℝ)) := by
          apply (le_div_iff₀ (by positivity :
            0 < 5 * (bandCount N : ℝ))).2
          linarith
        _ ≤ heightRadius x := hf
    · exact (hiNot hiC).elim
    · let ir := concreteReflectBandIndex N i
      have hirN : IsNorthernLatitudeBand N ir :=
        reflect_southern_is_northern hiS
      have hirReg : IsRegularLatitudeBand N ir := by
        simpa [ir] using hireg
      have hxr := neg_mem_reflected_band_rectangle hN i hx
      have hf := northern_band_heightRadius_floor
        (by omega : 1 ≤ bandCount N) hirN hirReg hxr
      have hMpos : (0 : ℝ) < bandCount N := by positivity
      have hsR :
          (bandCount N : ℝ) ≤
            2 * (latitudeBandScale N ir : ℝ) := by
        exact_mod_cast (show bandCount N ≤
          2 * latitudeBandScale N ir by simpa [ir] using hscale)
      rw [heightRadius_neg] at hf
      calc
        (1 : ℝ) / 10 ≤
            (latitudeBandScale N ir : ℝ) /
              (5 * (bandCount N : ℝ)) := by
          apply (le_div_iff₀ (by positivity :
            0 < 5 * (bandCount N : ℝ))).2
          linarith
        _ ≤ heightRadius x := hf
  rcases hcentral.2 with hjC | hkC
  · unfold ComparableLatitudeScales at hcomp
    have hjScale := latitudeBandScale_eq_central
      (by omega : 1 ≤ bandCount N) hjC
    constructor
    · exact centralFloor hjC hs
    · by_cases hkC : IsCentralLatitudeBand N k
      · exact centralFloor hkC ht
      · exact regularFloor hkC
          (fun hp ↦ hcentral.1 (Or.inr hp))
          (by omega) ht
  · have hkScale := latitudeBandScale_eq_central
      (by omega : 1 ≤ bandCount N) hkC
    unfold ComparableLatitudeScales at hcomp
    constructor
    · by_cases hjC : IsCentralLatitudeBand N j
      · exact centralFloor hjC hs
      · exact regularFloor hjC
          (fun hp ↦ hcentral.1 (Or.inl hp))
          (by omega) hs
    · exact centralFloor hkC ht

/-- A central rectangle and a northern rectangle separated by at least one
intervening band have the sharp index-distance height gap. -/
theorem central_northern_rectangle_dist_separation
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {k : Fin (bandTailCount N + 1)}
    (hkN : IsNorthernLatitudeBand N k)
    (hsep :
      2 ≤ Nat.dist (concreteCentralBandIndex N : ℕ) (k : ℕ))
    {s t : ℝ}
    (hs : s ∈ Icc
      (bandBoundaryHeight N (concreteCentralBandIndex N + 1))
      (bandBoundaryHeight N (concreteCentralBandIndex N)))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 + Nat.dist (concreteCentralBandIndex N : ℕ) (k : ℕ) : ℝ) /
        (30 * (bandCount N : ℝ)) ≤ t - s := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let c : ℕ := bandCount N - 1
  let u : ℕ := (k : ℕ) + 1
  have hc : (concreteCentralBandIndex N : ℕ) = c := by
    simp [c, concreteCentralBandIndex]
  have hklt : (k : ℕ) < c := by
    dsimp [c]
    unfold IsNorthernLatitudeBand at hkN
    omega
  have huc : u ≤ c := by dsimp [u]; omega
  have hbc := concrete_bandBoundaryHeight_north
    (N := N) (j := c) (by dsimp [c]; omega)
  have hbu := concrete_bandBoundaryHeight_north
    (N := N) (j := u) (by simpa [c] using huc)
  have hcentralTop :
      bandBoundaryHeight N (concreteCentralBandIndex N) =
        1 - 2 * (c : ℝ) * (2 * (c : ℝ) + 1) / N := by
    rw [show (concreteCentralBandIndex N : ℕ) = c from hc]
    exact hbc
  have hnorthBottom :
      bandBoundaryHeight N (k + 1) =
        1 - 2 * (u : ℝ) * (2 * (u : ℝ) + 1) / N := by
    rw [show (k : ℕ) + 1 = u by rfl]
    exact hbu
  have hraw :
      (2 * (c : ℝ) * (2 * (c : ℝ) + 1) -
          2 * (u : ℝ) * (2 * (u : ℝ) + 1)) / N ≤ t - s := by
    calc
      _ = bandBoundaryHeight N (k + 1) -
          bandBoundaryHeight N (concreteCentralBandIndex N) := by
        rw [hcentralTop, hnorthBottom]
        ring
      _ ≤ t - s := by linarith [hs.2, ht.1]
  let D : ℕ := Nat.dist (concreteCentralBandIndex N : ℕ) (k : ℕ)
  have hD : D = c - (k : ℕ) := by
    dsimp [D]
    rw [hc, Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]
  have hcu : (c : ℝ) - u = (D - 1 : ℕ) := by
    have hcuNat : c - u = D - 1 := by
      rw [hD]
      dsimp [u]
      omega
    rw [← Nat.cast_sub huc]
    exact_mod_cast hcuNat
  have hfactor :
      2 * (c : ℝ) * (2 * (c : ℝ) + 1) -
          2 * (u : ℝ) * (2 * (u : ℝ) + 1) =
        2 * ((D - 1 : ℕ) : ℝ) *
          (2 * ((c : ℝ) + (u : ℝ)) + 1) := by
    rw [← hcu]
    ring
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNupper :
      (N : ℝ) ≤ 20 * (bandCount N : ℝ) ^ 2 := by
    exact_mod_cast bemoc_N_le_twenty_bandCount_sq hM
  have hcM : (c : ℝ) = (bandCount N : ℝ) - 1 := by
    dsimp [c]
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hbig :
      (bandCount N : ℝ) ≤
        2 * ((c : ℝ) + (u : ℝ)) + 1 := by
    have hu0 : (0 : ℝ) ≤ u := by positivity
    rw [hcM]
    linarith
  have hDineq : (D + 1 : ℕ) ≤ 3 * (D - 1) := by
    dsimp [D] at hsep ⊢
    omega
  have hDineqR :
      ((D + 1 : ℕ) : ℝ) ≤ 3 * ((D - 1 : ℕ) : ℝ) := by
    exact_mod_cast hDineq
  have hnum :
      ((D + 1 : ℕ) : ℝ) * (N : ℝ) ≤
        (30 * (bandCount N : ℝ)) *
          (2 * ((D - 1 : ℕ) : ℝ) *
            (2 * ((c : ℝ) + (u : ℝ)) + 1)) := by
    have hnon : 0 ≤ ((D + 1 : ℕ) : ℝ) := by positivity
    have hstep := mul_le_mul_of_nonneg_left hNupper hnon
    nlinarith [mul_le_mul_of_nonneg_left hbig
      (show 0 ≤ 2 * ((D - 1 : ℕ) : ℝ) by positivity)]
  calc
    (1 + Nat.dist (concreteCentralBandIndex N : ℕ) (k : ℕ) : ℝ) /
          (30 * (bandCount N : ℝ)) =
        ((D + 1 : ℕ) : ℝ) /
          (30 * (bandCount N : ℝ)) := by
      change (1 + (D : ℝ)) / (30 * (bandCount N : ℝ)) =
        ((D + 1 : ℕ) : ℝ) / (30 * (bandCount N : ℝ))
      push_cast
      ring
    _ ≤
        (2 * ((D - 1 : ℕ) : ℝ) *
          (2 * ((c : ℝ) + (u : ℝ)) + 1)) / N := by
      apply (div_le_div_iff₀ (by positivity :
        0 < 30 * (bandCount N : ℝ)) hNreal).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnum
    _ = (2 * (c : ℝ) * (2 * (c : ℝ) + 1) -
          2 * (u : ℝ) * (2 * (u : ℝ) + 1)) / N := by
      rw [hfactor]
    _ ≤ t - s := hraw

/-- Reflection of the preceding gap estimate to the southern hemisphere. -/
theorem central_southern_rectangle_dist_separation
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {k : Fin (bandTailCount N + 1)}
    (hkS : IsSouthernLatitudeBand N k)
    (hsep :
      2 ≤ Nat.dist (concreteCentralBandIndex N : ℕ) (k : ℕ))
    {s t : ℝ}
    (hs : s ∈ Icc
      (bandBoundaryHeight N (concreteCentralBandIndex N + 1))
      (bandBoundaryHeight N (concreteCentralBandIndex N)))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 + Nat.dist (concreteCentralBandIndex N : ℕ) (k : ℕ) : ℝ) /
        (30 * (bandCount N : ℝ)) ≤ s - t := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let kr := concreteReflectBandIndex N k
  have hkrN : IsNorthernLatitudeBand N kr :=
    reflect_southern_is_northern hkS
  have hcentralReflect :
      concreteReflectBandIndex N (concreteCentralBandIndex N) =
        concreteCentralBandIndex N := by
    apply Fin.ext
    simp [concreteReflectBandIndex, concreteCentralBandIndex,
      bandTailCount]
    omega
  have hsr0 :=
    neg_mem_reflected_band_rectangle hN (concreteCentralBandIndex N) hs
  have hsr :
      -s ∈ Icc
        (bandBoundaryHeight N (concreteCentralBandIndex N + 1))
        (bandBoundaryHeight N (concreteCentralBandIndex N)) := by
    simpa [hcentralReflect] using hsr0
  have htr := neg_mem_reflected_band_rectangle hN k ht
  have hdist :
      Nat.dist (concreteCentralBandIndex N : ℕ) (kr : ℕ) =
        Nat.dist (concreteCentralBandIndex N : ℕ) (k : ℕ) := by
    have hd := dist_reflected_band_indices N
      (concreteCentralBandIndex N) k
    simpa [kr, hcentralReflect] using hd
  have hg := central_northern_rectangle_dist_separation
    hM hkrN (by simpa [hdist] using hsep) hsr htr
  have hg' :
      (1 + Nat.dist (concreteCentralBandIndex N : ℕ) (k : ℕ) : ℝ) /
          (30 * (bandCount N : ℝ)) ≤ (-t) - (-s) := by
    simpa [hdist] using hg
  linarith

/-- Complete separated central-comparable rectangle geometry: a uniform
interior chart and physical separation at scale `(1+dist)/M`. -/
theorem centralComparable_separated_rectangle_geometry
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hsep : 2 ≤ Nat.dist (j : ℕ) (k : ℕ))
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧
      (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
        (30 * (bandCount N : ℝ)) ≤ |s - t| := by
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
  have hfloor :=
    centralComparable_rectangle_heightRadius_floor
      hM hcentral hcomp hs ht
  have hsI := mem_Ioo_of_mem_Icc_heightRadius_pos hsSphere
    ((by norm_num : (0 : ℝ) < (1 : ℝ) / 10).trans_le hfloor.1)
  have htI := mem_Ioo_of_mem_Icc_heightRadius_pos htSphere
    ((by norm_num : (0 : ℝ) < (1 : ℝ) / 10).trans_le hfloor.2)
  have gapCentralLeft
      (hjC : IsCentralLatitudeBand N j) :
      (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
          (30 * (bandCount N : ℝ)) ≤ |s - t| := by
    have hjeq :
        j = concreteCentralBandIndex N :=
      (isCentralLatitudeBand_iff_eq_concreteCentralBandIndex j).mp hjC
    subst j
    rcases latitudeBand_region_trichotomy N k with hkN | hkC | hkS
    · have hg := central_northern_rectangle_dist_separation
        (by omega : 1 ≤ bandCount N) hkN hsep hs ht
      have hgp : 0 <
          (1 + Nat.dist (concreteCentralBandIndex N : ℕ) (k : ℕ) : ℝ) /
            (30 * (bandCount N : ℝ)) := by positivity
      rw [abs_of_nonpos (by linarith [hg] : s - t ≤ 0)]
      linarith
    · have hkeq :
          k = concreteCentralBandIndex N :=
        (isCentralLatitudeBand_iff_eq_concreteCentralBandIndex k).mp hkC
      subst k
      simp at hsep
    · have hg := central_southern_rectangle_dist_separation
        (by omega : 1 ≤ bandCount N) hkS hsep hs ht
      have hgp : 0 <
          (1 + Nat.dist (concreteCentralBandIndex N : ℕ) (k : ℕ) : ℝ) /
            (30 * (bandCount N : ℝ)) := by positivity
      rw [abs_of_nonneg (by linarith [hg] : 0 ≤ s - t)]
      exact hg
  refine ⟨hsI, htI, ?_⟩
  rcases hcentral.2 with hjC | hkC
  · exact gapCentralLeft hjC
  · have hswapCentral :
        k = concreteCentralBandIndex N :=
      (isCentralLatitudeBand_iff_eq_concreteCentralBandIndex k).mp hkC
    subst k
    rcases latitudeBand_region_trichotomy N j with hjN | hjC | hjS
    · have hg := central_northern_rectangle_dist_separation
        (by omega : 1 ≤ bandCount N) hjN
        (by simpa [Nat.dist_comm] using hsep) ht hs
      have hgp : 0 <
          (1 + Nat.dist (concreteCentralBandIndex N : ℕ) (j : ℕ) : ℝ) /
            (30 * (bandCount N : ℝ)) := by positivity
      rw [abs_of_nonneg (by linarith [hg] : 0 ≤ s - t)]
      simpa [Nat.dist_comm] using hg
    · have hjeq :
          j = concreteCentralBandIndex N :=
        (isCentralLatitudeBand_iff_eq_concreteCentralBandIndex j).mp hjC
      subst j
      simp at hsep
    · have hg := central_southern_rectangle_dist_separation
        (by omega : 1 ≤ bandCount N) hjS
        (by simpa [Nat.dist_comm] using hsep) ht hs
      have hgp : 0 <
          (1 + Nat.dist (concreteCentralBandIndex N : ℕ) (j : ℕ) : ℝ) /
            (30 * (bandCount N : ℝ)) := by positivity
      rw [abs_of_nonpos (by linarith [hg] : s - t ≤ 0)]
      simpa [Nat.dist_comm] using hg

/-- Scale arithmetic for central comparable rectangles.  Both populations
are at most `15M`, while factor-two comparability with the central scale
gives `M ≤ 2d_j`. -/
theorem centralComparable_scale_arithmetic
    {α C M N d p q D : ℝ}
    (hC : 0 ≤ C) (hM : 0 < M) (hN : 0 < N)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hD : 0 < D)
    (hp' : p ≤ 15 * M) (hq' : q ≤ 15 * M)
    (hMd : M ≤ 2 * d) (hMN : 4 * M ^ 2 ≤ N) :
    64 * (C * M ^ (3 - α) * D ^ (α - 3)) *
          p ^ 3 * q ^ 3 / N ^ 4 ≤
      ((15 : ℝ) ^ 6 / 2 * C) * d * M ^ (-α) *
        D ^ (α - 3) := by
  have hcoef : 0 ≤ C * M ^ (3 - α) * D ^ (α - 3) := by
    positivity
  have hp3 : p ^ 3 ≤ (15 * M) ^ 3 := by gcongr
  have hq3 : q ^ 3 ≤ (15 * M) ^ 3 := by gcongr
  have hnum :
      64 * (C * M ^ (3 - α) * D ^ (α - 3)) *
          p ^ 3 * q ^ 3 ≤
        64 * (C * M ^ (3 - α) * D ^ (α - 3)) *
          (15 * M) ^ 3 * (15 * M) ^ 3 := by
    gcongr
  have hden : (4 * M ^ 2) ^ 4 ≤ N ^ 4 := by gcongr
  have hMcombine :
      M ^ (3 - α) * M ^ 6 * (M ^ 8)⁻¹ =
        M ^ (1 - α) := by
    rw [← Real.rpow_natCast M 6, ← Real.rpow_natCast M 8,
      ← Real.rpow_neg hM.le]
    rw [← Real.rpow_add hM, ← Real.rpow_add hM]
    congr 1
    ring
  have hMdRpow :
      M ^ (1 - α) ≤ 2 * d * M ^ (-α) := by
    have hrewrite :
        M ^ (1 - α) = M * M ^ (-α) := by
      rw [show (1 - α : ℝ) = 1 + (-α) by ring,
        Real.rpow_add hM, Real.rpow_one]
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_right hMd
      (Real.rpow_nonneg hM.le _)
  calc
    64 * (C * M ^ (3 - α) * D ^ (α - 3)) *
          p ^ 3 * q ^ 3 / N ^ 4 ≤
        (64 * (C * M ^ (3 - α) * D ^ (α - 3)) *
          (15 * M) ^ 3 * (15 * M) ^ 3) / N ^ 4 := by
      exact div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤
        (64 * (C * M ^ (3 - α) * D ^ (α - 3)) *
          (15 * M) ^ 3 * (15 * M) ^ 3) / (4 * M ^ 2) ^ 4 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = ((15 : ℝ) ^ 6 / 4 * C) *
          M ^ (1 - α) * D ^ (α - 3) := by
      rw [div_eq_mul_inv]
      rw [show (4 * M ^ 2) ^ 4 = 256 * M ^ 8 by ring]
      rw [mul_inv]
      calc
        64 * (C * M ^ (3 - α) * D ^ (α - 3)) *
              (15 * M) ^ 3 * (15 * M) ^ 3 *
              (256⁻¹ * (M ^ 8)⁻¹) =
            ((15 : ℝ) ^ 6 / 4 * C) *
              (M ^ (3 - α) * M ^ 6 * (M ^ 8)⁻¹) *
                D ^ (α - 3) := by ring
        _ = _ := by rw [hMcombine]
    _ ≤ ((15 : ℝ) ^ 6 / 4 * C) *
          (2 * d * M ^ (-α)) * D ^ (α - 3) := by
      gcongr
    _ = ((15 : ℝ) ^ 6 / 2 * C) * d * M ^ (-α) *
          D ^ (α - 3) := by ring

/-- Peano transfer and all population/exponent arithmetic for a separated
central comparable block.  The only remaining input is the sharp physical
mixed derivative estimate on its literal rectangle. -/
theorem centralComparable_separated_block_bound_of_Dsstt
    {α C : ℝ} (hα0 : 0 < α) (hC : 0 ≤ C)
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hsep : 2 ≤ Nat.dist (j : ℕ) (k : ℕ))
    (hrect : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
        s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧ s ≠ t)
    (hmixed : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
        |variableReducedLatitudeKernelDsstt α s t| ≤
          C * (bandCount N : ℝ) ^ (3 - α) *
            (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3)) :
    |bandPairError N j k (latitudeKernel α)| ≤
      comparableLatitudeBlockMajorant α
        ((15 : ℝ) ^ 6 / 2 * C) N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hMpos : (0 : ℝ) < bandCount N := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  let D : ℝ := 1 + Nat.dist (j : ℕ) (k : ℕ)
  let B : ℝ := C * (bandCount N : ℝ) ^ (3 - α) *
    D ^ (α - 3)
  have hB : 0 ≤ B := by dsimp [B, D]; positivity
  have hraw :=
    abs_latitudeKernel_bandPairError_le_of_Dsstt hN hα0 hB j k
      hrect (fun s hs t ht ↦ by
        simpa [B, D] using hmixed s hs t ht)
  have hpj :=
    finiteBandPopulation_le_fifteen_mul_bandCount
      (by omega : 1 ≤ bandCount N) j
  have hpk :=
    finiteBandPopulation_le_fifteen_mul_bandCount
      (by omega : 1 ≤ bandCount N) k
  have hrow : bandCount N ≤ 2 * latitudeBandScale N j := by
    unfold ComparableLatitudeScales at hcomp
    rcases hcentral.2 with hjC | hkC
    · rw [← latitudeBandScale_eq_central
        (by omega : 1 ≤ bandCount N) hjC]
      omega
    · rw [← latitudeBandScale_eq_central
        (by omega : 1 ≤ bandCount N) hkC]
      exact hcomp.2
  have harith := centralComparable_scale_arithmetic
    (α := α) (C := C) (M := (bandCount N : ℝ)) (N := (N : ℝ))
    (d := (latitudeBandScale N j : ℝ))
    (p := (finiteBandPopulation N j : ℝ))
    (q := (finiteBandPopulation N k : ℝ)) (D := D)
    hC hMpos hNpos
    (by positivity) (by positivity) (by dsimp [D]; positivity)
    (by exact_mod_cast hpj) (by exact_mod_cast hpk)
    (by exact_mod_cast hrow)
    (by exact_mod_cast four_mul_bandCount_sq_le N)
  unfold comparableLatitudeBlockMajorant
  exact hraw.trans (by simpa [B, D] using harith)

/-- The precise residual analytic datum for separated central comparable
rectangles.  It contains the off-diagonal chart needed by the literal Peano
transfer and the sharp physical-distance derivative scale after the
equatorial radius floor has been inserted. -/
def HasCentralComparableSeparatedDssttBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    CentralLatitudePair N j k →
    ComparableLatitudeScales N j k →
    2 ≤ Nat.dist (j : ℕ) (k : ℕ) →
      (∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧ s ≠ t) ∧
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          |variableReducedLatitudeKernelDsstt α s t| ≤
            C * (bandCount N : ℝ) ^ (3 - α) *
              (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3)

/-- The residual separated analytic datum implies the complete central
separated comparable block estimate. -/
theorem centralComparable_separated_block_bound_of_analytic
    {α C : ℝ} (hα0 : 0 < α) (hC : 0 ≤ C)
    {N : ℕ} (hM : 15 ≤ bandCount N)
    (hanalytic : HasCentralComparableSeparatedDssttBound α N C) :
    ∀ j k, CentralLatitudePair N j k →
      ComparableLatitudeScales N j k →
      2 ≤ Nat.dist (j : ℕ) (k : ℕ) →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α
          ((15 : ℝ) ^ 6 / 2 * C) N j k := by
  intro j k hc hcomp hsep
  have ha := hanalytic j k hc hcomp hsep
  exact centralComparable_separated_block_bound_of_Dsstt
    hα0 hC hM hc hcomp hsep ha.1 ha.2

/-- Final logical assembly for the central comparable class.  This theorem
isolates the two genuinely local inputs: the already-small neighboring
block and the separated sharp mixed derivative datum.  All central
geometry, Peano transfer, population bounds, and scale arithmetic occur
inside this module. -/
theorem centralComparable_block_bound_of_neighboring_and_analytic
    {α A C : ℝ} (hα0 : 0 < α) (hA : 0 ≤ A) (hC : 0 ≤ C)
    {N : ℕ} (hM : 15 ≤ bandCount N)
    (hneighbor :
      ∀ j k, CentralLatitudePair N j k →
        ComparableLatitudeScales N j k →
        Nat.dist (j : ℕ) (k : ℕ) ≤ 1 →
        |bandPairError N j k (latitudeKernel α)| ≤
          comparableLatitudeBlockMajorant α A N j k)
    (hanalytic : HasCentralComparableSeparatedDssttBound α N C) :
    ∀ j k, CentralLatitudePair N j k →
      ComparableLatitudeScales N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α
          (A + (15 : ℝ) ^ 6 / 2 * C) N j k := by
  intro j k hc hcomp
  by_cases hn : Nat.dist (j : ℕ) (k : ℕ) ≤ 1
  · exact (hneighbor j k hc hcomp hn).trans
      (comparableLatitudeBlockMajorant_mono
        (le_add_of_nonneg_right (mul_nonneg
          (by positivity : 0 ≤ (15 : ℝ) ^ 6 / 2) hC)))
  · have hs : 2 ≤ Nat.dist (j : ℕ) (k : ℕ) := by omega
    exact
      (centralComparable_separated_block_bound_of_analytic
        hα0 hC hM hanalytic j k hc hcomp hs).trans
        (comparableLatitudeBlockMajorant_mono
          (le_add_of_nonneg_left hA))

/-- The upper-range analytic component is exactly the central smooth normal
form, so its literal block estimate is unconditional. -/
theorem central_neighboring_upperAnalytic_block_bound
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k (neighboringUpperAnalyticKernel α)| ≤
      64 * centralAffineSmoothDssttConstant α
          (reducedCuspUpperConstantCoefficient α)
          (reducedCuspUpperLinearCoefficient α) *
        (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  have heq :
      bandPairError N j k (neighboringUpperAnalyticKernel α) =
        bandPairError N j k
          (neighboringAffineSmoothKernel α
            (reducedCuspUpperConstantCoefficient α)
            (reducedCuspUpperLinearCoefficient α)) := by
    apply bandPairError_congr_on_literalRectangle j k
    intro s hs t ht
    have hc := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hs ht
    exact neighboringUpperAnalyticKernel_eq_smooth hc.1 hc.2.1
  rw [heq]
  exact abs_bandPairError_neighboringAffineSmoothKernel_central
    (by linarith) hα2 hM hcentral hcomp hneigh

/-- The lower-range analytic component is the smooth normal form with zero
linear normalized-gap coefficient. -/
theorem central_neighboring_lowerAnalytic_block_bound
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k (neighboringLowerAnalyticKernel α)| ≤
      64 * centralAffineSmoothDssttConstant α
          (reducedCuspLowerConstantCoefficient α) 0 *
        (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  have heq :
      bandPairError N j k (neighboringLowerAnalyticKernel α) =
        bandPairError N j k
          (neighboringAffineSmoothKernel α
            (reducedCuspLowerConstantCoefficient α) 0) := by
    apply bandPairError_congr_on_literalRectangle j k
    intro s hs t ht
    rw [neighboringLowerAnalyticKernel_eq_power]
    unfold neighboringAffineSmoothKernel
    ring
  rw [heq]
  exact abs_bandPairError_neighboringAffineSmoothKernel_central
    hα0 (by linarith) hM hcentral hcomp hneigh

/-- The affine part of the resonant model is likewise fully closed.  Only
the extracted physical logarithmic cusp and the higher branch remain. -/
theorem central_neighboring_resonantAffine_block_bound
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k
        (neighboringAffineSmoothKernel 1
          reducedCuspResonantConstantCoefficient
          reducedCuspResonantLinearCoefficient)| ≤
      64 * centralAffineSmoothDssttConstant 1
          reducedCuspResonantConstantCoefficient
          reducedCuspResonantLinearCoefficient *
        (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  exact abs_bandPairError_neighboringAffineSmoothKernel_central
    (by norm_num) (by norm_num) hM hcentral hcomp hneigh

noncomputable def centralUpperBranchConstant (α : ℝ) : ℝ :=
  (2 : ℝ) ^ (α / 2) *
    (8 : ℝ) ^ reducedCuspUpperNu α *
      (reducedCuspD2MajorantCoefficient α /
        ((reducedCuspUpperNu α - 1) * reducedCuspUpperNu α))

theorem centralUpperBranchConstant_nonneg
    {α : ℝ} (hα1 : 1 < α) :
    0 ≤ centralUpperBranchConstant α := by
  unfold centralUpperBranchConstant
  have hν : 1 < reducedCuspUpperNu α := by
    unfold reducedCuspUpperNu
    linarith
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (div_nonneg (reducedCuspD2MajorantCoefficient_nonneg α)
      (mul_nonneg (by linarith) (zero_le_one.trans hν.le)))

private theorem rpow_sq_upperNu
    {α x : ℝ} (hx : 0 ≤ x) :
    (x ^ 2) ^ reducedCuspUpperNu α = x ^ (1 + α) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  unfold reducedCuspUpperNu
  congr 1
  ring

/-- The upper nonresonant branch has the literal physical cusp scale on
every central neighboring rectangle, including the diagonal. -/
theorem abs_neighboringUpperBranchKernel_le_central
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringUpperBranchKernel α s t| ≤
      centralUpperBranchConstant α * |s - t| ^ (1 + α) := by
  have hchart := centralComparable_neighboring_rectangle_chart
    hM hcentral hcomp hneigh hs ht
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨hchart.1.1.le, hchart.1.2.le⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨hchart.2.1.1.le, hchart.2.1.2.le⟩
  by_cases hst : s = t
  · subst t
    have hq :
        normalizedLatitudeGap s s = 0 := by
      simpa using normalizedLatitudeGap_eq_quadraticCoefficient_mul_sq
        hchart.1 hchart.1
    have hν : 0 < reducedCuspUpperNu α := by
      unfold reducedCuspUpperNu
      linarith
    have hαp : 0 < 1 + α := by linarith
    simp [neighboringUpperBranchKernel, hq, Real.zero_rpow hν.ne',
      Real.zero_rpow hαp.ne']
  · have hraw := abs_neighboringUpperBranchKernel_le
      hα1 hα2 hchart.1 hchart.2.1 hst hchart.2.2
    have hgap := centralComparable_neighboring_normalizedLatitudeGap_le_sq
      hM hcentral hcomp hneigh hs ht
    have hp0 : 0 ≤ latitudeAngularScale s t := by
      unfold latitudeAngularScale
      positivity
    have hrs := heightRadius_le_one hsSphere
    have hrt := heightRadius_le_one htSphere
    have hp2 : latitudeAngularScale s t ≤ 2 := by
      rw [latitudeAngularScale_eq_heightRadius]
      have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
      have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
      nlinarith [mul_le_mul hrs hrt hrt0 (by norm_num : (0 : ℝ) ≤ 1)]
    have hν0 : 0 ≤ reducedCuspUpperNu α := by
      unfold reducedCuspUpperNu
      linarith
    have hp :
        latitudeAngularScale s t ^ (α / 2) ≤
          (2 : ℝ) ^ (α / 2) :=
      Real.rpow_le_rpow hp0 hp2 (by linarith)
    have hq :
        normalizedLatitudeGap s t ^ reducedCuspUpperNu α ≤
          (8 * (s - t) ^ 2) ^ reducedCuspUpperNu α :=
      Real.rpow_le_rpow hgap.1 hgap.2 hν0
    have hK :
        0 ≤ reducedCuspD2MajorantCoefficient α /
          ((reducedCuspUpperNu α - 1) *
            reducedCuspUpperNu α) := by
      have hν : 1 < reducedCuspUpperNu α := by
        unfold reducedCuspUpperNu
        linarith
      exact div_nonneg (reducedCuspD2MajorantCoefficient_nonneg α)
        (mul_nonneg (by linarith) (zero_le_one.trans hν.le))
    have hqpow0 :
        0 ≤ normalizedLatitudeGap s t ^ reducedCuspUpperNu α :=
      Real.rpow_nonneg hgap.1 _
    calc
      |neighboringUpperBranchKernel α s t| ≤
          latitudeAngularScale s t ^ (α / 2) *
            normalizedLatitudeGap s t ^ reducedCuspUpperNu α *
              (reducedCuspD2MajorantCoefficient α /
                ((reducedCuspUpperNu α - 1) *
                  reducedCuspUpperNu α)) := hraw
      _ ≤ (2 : ℝ) ^ (α / 2) *
          (8 * (s - t) ^ 2) ^ reducedCuspUpperNu α *
            (reducedCuspD2MajorantCoefficient α /
              ((reducedCuspUpperNu α - 1) *
                reducedCuspUpperNu α)) := by gcongr
      _ = centralUpperBranchConstant α * |s - t| ^ (1 + α) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8)
          (sq_nonneg (s - t))]
        rw [show (s - t) ^ 2 = |s - t| ^ 2 by
          rw [sq_abs]]
        rw [rpow_sq_upperNu (abs_nonneg (s - t))]
        unfold centralUpperBranchConstant
        ring

/-- Literal block estimate for the upper branch. -/
theorem central_neighboring_upperBranch_block_bound
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k (neighboringUpperBranchKernel α)| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (centralUpperBranchConstant α *
            neighboringBandLength N j k ^ (1 + α)) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  apply abs_bandPairError_neighboringUpperBranchKernel_le_of_rectangle
    (mul_nonneg (centralUpperBranchConstant_nonneg hα1)
      (Real.rpow_nonneg
        (add_nonneg (bandWidth_nonneg (N := N) j)
          (bandWidth_nonneg (N := N) k)) _))
    hN j k
  intro s hs t ht
  have hp := abs_neighboringUpperBranchKernel_le_central
    hα1 hα2 hM hcentral hcomp hneigh hs ht
  have hw := abs_sub_le_neighboringBandLength j k hneigh hs ht
  exact hp.trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) hw (by linarith))
    (centralUpperBranchConstant_nonneg hα1)

noncomputable def centralLowerBranchConstant (α : ℝ) : ℝ :=
  (2 : ℝ) ^ (α / 2) *
    (8 : ℝ) ^ reducedCuspUpperNu α *
      (reducedCuspLowerD1MajorantCoefficient α /
        reducedCuspUpperNu α)

theorem centralLowerBranchConstant_nonneg
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 ≤ centralLowerBranchConstant α := by
  unfold centralLowerBranchConstant
  have hν : 0 < reducedCuspUpperNu α := by
    unfold reducedCuspUpperNu
    linarith
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (div_nonneg (reducedCuspLowerD1MajorantCoefficient_nonneg hα1)
      hν.le)

theorem abs_neighboringLowerBranchKernel_le_central
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringLowerBranchKernel α s t| ≤
      centralLowerBranchConstant α * |s - t| ^ (1 + α) := by
  have hchart := centralComparable_neighboring_rectangle_chart
    hM hcentral hcomp hneigh hs ht
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨hchart.1.1.le, hchart.1.2.le⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨hchart.2.1.1.le, hchart.2.1.2.le⟩
  by_cases hst : s = t
  · subst t
    have hq :
        normalizedLatitudeGap s s = 0 := by
      simpa using normalizedLatitudeGap_eq_quadraticCoefficient_mul_sq
        hchart.1 hchart.1
    have hν : 0 < reducedCuspUpperNu α := by
      unfold reducedCuspUpperNu
      linarith
    have hαp : 0 < 1 + α := by linarith
    simp [neighboringLowerBranchKernel, hq, Real.zero_rpow hν.ne',
      Real.zero_rpow hαp.ne']
  · have hraw := abs_neighboringLowerBranchKernel_le
      hα0 hα1 hchart.1 hchart.2.1 hst hchart.2.2
    have hgap := centralComparable_neighboring_normalizedLatitudeGap_le_sq
      hM hcentral hcomp hneigh hs ht
    have hp0 : 0 ≤ latitudeAngularScale s t := by
      unfold latitudeAngularScale
      positivity
    have hrs := heightRadius_le_one hsSphere
    have hrt := heightRadius_le_one htSphere
    have hp2 : latitudeAngularScale s t ≤ 2 := by
      rw [latitudeAngularScale_eq_heightRadius]
      have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
      have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
      nlinarith [mul_le_mul hrs hrt hrt0 (by norm_num : (0 : ℝ) ≤ 1)]
    have hν0 : 0 ≤ reducedCuspUpperNu α := by
      unfold reducedCuspUpperNu
      linarith
    have hp :
        latitudeAngularScale s t ^ (α / 2) ≤
          (2 : ℝ) ^ (α / 2) :=
      Real.rpow_le_rpow hp0 hp2 (by linarith)
    have hq :
        normalizedLatitudeGap s t ^ reducedCuspUpperNu α ≤
          (8 * (s - t) ^ 2) ^ reducedCuspUpperNu α :=
      Real.rpow_le_rpow hgap.1 hgap.2 hν0
    have hK :
        0 ≤ reducedCuspLowerD1MajorantCoefficient α /
          reducedCuspUpperNu α := by
      apply div_nonneg
        (reducedCuspLowerD1MajorantCoefficient_nonneg hα1)
      exact hν0
    have hqpow0 :
        0 ≤ normalizedLatitudeGap s t ^ reducedCuspUpperNu α :=
      Real.rpow_nonneg hgap.1 _
    calc
      |neighboringLowerBranchKernel α s t| ≤
          latitudeAngularScale s t ^ (α / 2) *
            normalizedLatitudeGap s t ^ reducedCuspUpperNu α *
              (reducedCuspLowerD1MajorantCoefficient α /
                reducedCuspUpperNu α) := hraw
      _ ≤ (2 : ℝ) ^ (α / 2) *
          (8 * (s - t) ^ 2) ^ reducedCuspUpperNu α *
            (reducedCuspLowerD1MajorantCoefficient α /
              reducedCuspUpperNu α) := by gcongr
      _ = centralLowerBranchConstant α * |s - t| ^ (1 + α) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8)
          (sq_nonneg (s - t))]
        rw [show (s - t) ^ 2 = |s - t| ^ 2 by rw [sq_abs]]
        rw [rpow_sq_upperNu (abs_nonneg (s - t))]
        unfold centralLowerBranchConstant
        ring

theorem central_neighboring_lowerBranch_block_bound
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k (neighboringLowerBranchKernel α)| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (centralLowerBranchConstant α *
            neighboringBandLength N j k ^ (1 + α)) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  apply abs_bandPairError_neighboringLowerBranchKernel_le_of_rectangle
    (mul_nonneg (centralLowerBranchConstant_nonneg hα0 hα1)
      (Real.rpow_nonneg
        (add_nonneg (bandWidth_nonneg (N := N) j)
          (bandWidth_nonneg (N := N) k)) _))
    hN j k
  intro s hs t ht
  have hp := abs_neighboringLowerBranchKernel_le_central
    hα0 hα1 hM hcentral hcomp hneigh hs ht
  have hw := abs_sub_le_neighboringBandLength j k hneigh hs ht
  exact hp.trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) hw (by linarith))
    (centralLowerBranchConstant_nonneg hα0 hα1)

theorem central_neighboring_upper_kernel_block_bound_raw
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k (latitudeKernel α)| ≤
      64 * centralAffineSmoothDssttConstant α
          (reducedCuspUpperConstantCoefficient α)
          (reducedCuspUpperLinearCoefficient α) *
        (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 +
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (centralUpperBranchConstant α *
            neighboringBandLength N j k ^ (1 + α)) := by
  let A := neighboringUpperAnalyticKernel α
  let B := neighboringUpperBranchKernel α
  have hA :
      ContinuousOn (fun p : ℝ × ℝ ↦ A p.1 p.2)
        (Icc (bandBoundaryHeight N (j + 1))
            (bandBoundaryHeight N j) ×ˢ
          Icc (bandBoundaryHeight N (k + 1))
            (bandBoundaryHeight N k)) := by
    intro p hp
    have hc := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hp.1 hp.2
    have hsmooth :=
      continuousAt_neighboringAffineSmoothKernel_joint
        (α := α) (H := reducedCuspUpperConstantCoefficient α)
        (L := reducedCuspUpperLinearCoefficient α) hc.1 hc.2.1
    apply hsmooth.continuousWithinAt.congr
    · intro q hq
      have hqc := centralComparable_neighboring_rectangle_chart
        hM hcentral hcomp hneigh hq.1 hq.2
      change neighboringUpperAnalyticKernel α q.1 q.2 =
        neighboringAffineSmoothKernel α
          (reducedCuspUpperConstantCoefficient α)
          (reducedCuspUpperLinearCoefficient α) q.1 q.2
      exact neighboringUpperAnalyticKernel_eq_smooth hqc.1 hqc.2.1
    · change neighboringUpperAnalyticKernel α p.1 p.2 =
        neighboringAffineSmoothKernel α
          (reducedCuspUpperConstantCoefficient α)
          (reducedCuspUpperLinearCoefficient α) p.1 p.2
      exact neighboringUpperAnalyticKernel_eq_smooth hc.1 hc.2.1
  have hdecomp :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          latitudeKernel α s t = A s t + B s t := by
    intro s hs t ht
    have hc := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hs ht
    exact latitudeKernel_eq_neighboringUpperAnalytic_add_branch_on_unitChart
      hα1 hα2 hc.1 hc.2.1 hc.2.2
  have heq :=
    bandPairError_eq_add_of_continuous_decomposition_on_literalRectangle
      j k (latitudeKernel α) A B (continuous_latitudeKernel (by linarith))
      hA hdecomp
  have ha := central_neighboring_upperAnalytic_block_bound
    hα1 hα2 hM hcentral hcomp hneigh
  have hb := central_neighboring_upperBranch_block_bound
    hα1 hα2 hM hcentral hcomp hneigh
  rw [heq]
  exact (abs_add _ _).trans (add_le_add ha hb)

theorem central_neighboring_lower_kernel_block_bound_raw
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k (latitudeKernel α)| ≤
      64 * centralAffineSmoothDssttConstant α
          (reducedCuspLowerConstantCoefficient α) 0 *
        (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 +
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (centralLowerBranchConstant α *
            neighboringBandLength N j k ^ (1 + α)) := by
  let A := neighboringLowerAnalyticKernel α
  let B := neighboringLowerBranchKernel α
  have hA :
      ContinuousOn (fun p : ℝ × ℝ ↦ A p.1 p.2)
        (Icc (bandBoundaryHeight N (j + 1))
            (bandBoundaryHeight N j) ×ˢ
          Icc (bandBoundaryHeight N (k + 1))
            (bandBoundaryHeight N k)) := by
    intro p hp
    have hc := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hp.1 hp.2
    have hsmooth :=
      continuousAt_neighboringAffineSmoothKernel_joint
        (α := α) (H := reducedCuspLowerConstantCoefficient α)
        (L := 0) hc.1 hc.2.1
    apply hsmooth.continuousWithinAt.congr
    · intro q hq
      rw [show A q.1 q.2 =
        neighboringLowerAnalyticKernel α q.1 q.2 by rfl]
      rw [neighboringLowerAnalyticKernel_eq_power]
      unfold neighboringAffineSmoothKernel
      ring
    · rw [show A p.1 p.2 =
        neighboringLowerAnalyticKernel α p.1 p.2 by rfl]
      rw [neighboringLowerAnalyticKernel_eq_power]
      unfold neighboringAffineSmoothKernel
      ring
  have hdecomp :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          latitudeKernel α s t = A s t + B s t := by
    intro s hs t ht
    have hc := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hs ht
    exact latitudeKernel_eq_neighboringLowerAnalytic_add_branch_on_unitChart
      hα0 hα1 hc.1 hc.2.1 hc.2.2
  have heq :=
    bandPairError_eq_add_of_continuous_decomposition_on_literalRectangle
      j k (latitudeKernel α) A B (continuous_latitudeKernel hα0)
      hA hdecomp
  have ha := central_neighboring_lowerAnalytic_block_bound
    hα0 hα1 hM hcentral hcomp hneigh
  have hb := central_neighboring_lowerBranch_block_bound
    hα0 hα1 hM hcentral hcomp hneigh
  rw [heq]
  exact (abs_add _ _).trans (add_le_add ha hb)

/-- Convert a central neighboring smooth raw Peano bound to the comparable
majorant.  The factor eight absorbs the worst neighboring distance weight. -/
theorem central_neighboring_smooth_raw_bound_to_majorant
    {α S : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hS : 0 ≤ S)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {E : ℝ}
    (hraw :
      E ≤ 64 * S * (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4) :
    E ≤ comparableLatitudeBlockMajorant α
      (4 * (15 : ℝ) ^ 6 * S) N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let M : ℝ := bandCount N
  let D : ℝ := 1 + Nat.dist (j : ℕ) (k : ℕ)
  have hMr : 0 < M := by dsimp [M]; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : 0 < D := by dsimp [D]; positivity
  have hD2 : D ≤ 2 := by
    dsimp [D]
    exact_mod_cast (show
      1 + Nat.dist (j : ℕ) (k : ℕ) ≤ 2 by omega)
  have hweight : (1 : ℝ) / 8 ≤ D ^ (α - 3) := by
    have hp := Real.rpow_le_rpow_of_nonpos hD hD2
      (by linarith : α - 3 ≤ 0)
    have htwo :
        (2 : ℝ) ^ (-3 : ℝ) ≤ 2 ^ (α - 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    norm_num at htwo ⊢
    exact htwo.trans hp
  have hMone : (1 : ℝ) ≤ M := by
    dsimp [M]
    exact_mod_cast (show 1 ≤ bandCount N by omega)
  have hMpow : M ≤ M ^ (3 - α) := by
    calc
      M = M ^ (1 : ℝ) := (Real.rpow_one M).symm
      _ ≤ M ^ (3 - α) :=
        Real.rpow_le_rpow_of_exponent_le hMone (by linarith)
  have hpowone : 1 ≤ M ^ (3 - α) := hMone.trans hMpow
  have hprod : 1 ≤ 8 * M ^ (3 - α) * D ^ (α - 3) := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hpowone) (sub_nonneg.mpr hweight)]
  have hcoef :
      S ≤ (8 * S) * M ^ (3 - α) * D ^ (α - 3) := by
    have := mul_le_mul_of_nonneg_left hprod hS
    nlinarith
  have hpj :=
    finiteBandPopulation_le_fifteen_mul_bandCount
      (by omega : 1 ≤ bandCount N) j
  have hpk :=
    finiteBandPopulation_le_fifteen_mul_bandCount
      (by omega : 1 ≤ bandCount N) k
  have hrow : bandCount N ≤ 2 * latitudeBandScale N j := by
    unfold ComparableLatitudeScales at hcomp
    rcases hcentral.2 with hjC | hkC
    · rw [← latitudeBandScale_eq_central
        (by omega : 1 ≤ bandCount N) hjC]
      omega
    · rw [← latitudeBandScale_eq_central
        (by omega : 1 ≤ bandCount N) hkC]
      exact hcomp.2
  have harith := centralComparable_scale_arithmetic
    (α := α) (C := 8 * S) (M := M) (N := (N : ℝ))
    (d := (latitudeBandScale N j : ℝ))
    (p := (finiteBandPopulation N j : ℝ))
    (q := (finiteBandPopulation N k : ℝ)) (D := D)
    (mul_nonneg (by norm_num) hS) hMr hNr
    (by positivity) (by positivity) hD
    (by simpa [M] using (show
      (finiteBandPopulation N j : ℝ) ≤
        15 * (bandCount N : ℝ) by exact_mod_cast hpj))
    (by simpa [M] using (show
      (finiteBandPopulation N k : ℝ) ≤
        15 * (bandCount N : ℝ) by exact_mod_cast hpk))
    (by simpa [M] using (show
      (bandCount N : ℝ) ≤
        2 * (latitudeBandScale N j : ℝ) by exact_mod_cast hrow))
    (by simpa [M] using (show
      (4 : ℝ) * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) by
        exact_mod_cast four_mul_bandCount_sq_le N))
  unfold comparableLatitudeBlockMajorant
  calc
    E ≤ 64 * S * (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := hraw
    _ ≤ 64 * ((8 * S) * M ^ (3 - α) * D ^ (α - 3)) *
        (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
      gcongr
    _ ≤ ((15 : ℝ) ^ 6 / 2 * (8 * S)) *
        (latitudeBandScale N j : ℝ) * M ^ (-α) *
          D ^ (α - 3) := harith
    _ = 4 * (15 : ℝ) ^ 6 * S *
        (latitudeBandScale N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) *
            (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
      dsimp [M, D]
      ring

/-- Convert a physical `|s-t|^(1+α)` neighboring cusp bound to the central
comparable majorant. -/
theorem central_neighboring_cusp_raw_bound_to_majorant
    {α B : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hB : 0 ≤ B)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {E : ℝ}
    (hraw :
      E ≤ 4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (B * neighboringBandLength N j k ^ (1 + α))) :
    E ≤ comparableLatitudeBlockMajorant α
      (14400 * (15 : ℝ) ^ (1 + α) * B) N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let M : ℝ := bandCount N
  let Nr : ℝ := N
  let d : ℝ := latitudeBandScale N j
  let D : ℝ := 1 + Nat.dist (j : ℕ) (k : ℕ)
  let p : ℝ := finiteBandPopulation N j
  let q : ℝ := finiteBandPopulation N k
  let a : ℝ := neighboringBandLength N j k
  have hMr : 0 < M := by dsimp [M]; positivity
  have hNr : 0 < Nr := by dsimp [Nr]; exact_mod_cast hN
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast latitudeBandScale_pos N j
  have hD : 0 < D := by dsimp [D]; positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hp' : p ≤ 15 * M := by
    dsimp [p, M]
    exact_mod_cast finiteBandPopulation_le_fifteen_mul_bandCount
      (by omega : 1 ≤ bandCount N) j
  have hq' : q ≤ 15 * M := by
    dsimp [q, M]
    exact_mod_cast finiteBandPopulation_le_fifteen_mul_bandCount
      (by omega : 1 ≤ bandCount N) k
  have hMN : 4 * M ^ 2 ≤ Nr := by
    dsimp [M, Nr]
    exact_mod_cast four_mul_bandCount_sq_le N
  have haeq : a = 2 * (p + q) / Nr := by
    dsimp [a, p, q, Nr]
    exact neighboringBandLength_eq_populations hN j k
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact add_nonneg (bandWidth_nonneg (N := N) j)
      (bandWidth_nonneg (N := N) k)
  have hpop : 2 * (p + q) ≤ 60 * M := by linarith
  have hright : 60 * M ≤ (15 / M) * Nr := by
    calc
      60 * M = (15 / M) * (4 * M ^ 2) := by
        field_simp [hMr.ne']
        ring
      _ ≤ (15 / M) * Nr := by
        gcongr
  have halen : a ≤ 15 / M := by
    rw [haeq]
    exact (div_le_iff₀ hNr).2 (hpop.trans hright)
  have hapow :
      a ^ (1 + α) ≤ (15 / M) ^ (1 + α) :=
    Real.rpow_le_rpow ha0 halen (by linarith)
  have hpowid :
      (15 / M) ^ (1 + α) =
        (15 : ℝ) ^ (1 + α) * M ^ (-(1 + α)) := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 15) hMr.le,
      Real.rpow_neg hMr.le]
    rw [div_eq_mul_inv]
  have hpopmul : 4 * p * q ≤ 900 * M ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp') (sub_nonneg.mpr hq')]
  have hcusp :
      4 * p * q * (B * a ^ (1 + α)) ≤
        900 * (15 : ℝ) ^ (1 + α) * B * M ^ (1 - α) := by
    calc
      4 * p * q * (B * a ^ (1 + α)) ≤
          900 * M ^ 2 * (B * (15 / M) ^ (1 + α)) := by
        gcongr
      _ = 900 * (15 : ℝ) ^ (1 + α) * B *
          M ^ (1 - α) := by
        rw [hpowid]
        calc
          900 * M ^ 2 *
                (B * (15 ^ (1 + α) * M ^ (-(1 + α)))) =
              900 * 15 ^ (1 + α) * B *
                (M ^ 2 * M ^ (-(1 + α))) := by ring
          _ = _ := by
            rw [← Real.rpow_natCast M 2, ← Real.rpow_add hMr]
            congr 1
            ring
  have hrow : bandCount N ≤ 2 * latitudeBandScale N j := by
    unfold ComparableLatitudeScales at hcomp
    rcases hcentral.2 with hjC | hkC
    · rw [← latitudeBandScale_eq_central
        (by omega : 1 ≤ bandCount N) hjC]
      omega
    · rw [← latitudeBandScale_eq_central
        (by omega : 1 ≤ bandCount N) hkC]
      exact hcomp.2
  have hMd : M ≤ 2 * d := by
    dsimp [M, d]
    exact_mod_cast hrow
  have hD2 : D ≤ 2 := by
    dsimp [D]
    exact_mod_cast (show
      1 + Nat.dist (j : ℕ) (k : ℕ) ≤ 2 by omega)
  have hweight : (1 : ℝ) / 8 ≤ D ^ (α - 3) := by
    have hpD := Real.rpow_le_rpow_of_nonpos hD hD2
      (by linarith : α - 3 ≤ 0)
    have htwo :
        (2 : ℝ) ^ (-3 : ℝ) ≤ 2 ^ (α - 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    norm_num at htwo ⊢
    exact htwo.trans hpD
  have hscale :
      M ^ (1 - α) ≤
        16 * d * M ^ (-α) * D ^ (α - 3) := by
    have hrewrite : M ^ (1 - α) = M * M ^ (-α) := by
      rw [show (1 - α : ℝ) = 1 + (-α) by ring,
        Real.rpow_add hMr, Real.rpow_one]
    rw [hrewrite]
    calc
      M * M ^ (-α) ≤ 2 * d * M ^ (-α) :=
        mul_le_mul_of_nonneg_right hMd (Real.rpow_nonneg hMr.le _)
      _ ≤ (2 * d * M ^ (-α)) * (8 * D ^ (α - 3)) := by
        apply le_mul_of_one_le_right (by positivity)
        nlinarith
      _ = 16 * d * M ^ (-α) * D ^ (α - 3) := by ring
  unfold comparableLatitudeBlockMajorant
  calc
    E ≤ 4 * p * q * (B * a ^ (1 + α)) := by
      simpa [p, q, a] using hraw
    _ ≤ 900 * (15 : ℝ) ^ (1 + α) * B *
        M ^ (1 - α) := hcusp
    _ ≤ 900 * (15 : ℝ) ^ (1 + α) * B *
        (16 * d * M ^ (-α) * D ^ (α - 3)) := by
      gcongr
    _ = 14400 * (15 : ℝ) ^ (1 + α) * B *
        (latitudeBandScale N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) *
            (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
      dsimp [M, d, D]
      ring

noncomputable def centralUpperNeighboringBlockConstant (α : ℝ) : ℝ :=
  4 * (15 : ℝ) ^ 6 *
      centralAffineSmoothDssttConstant α
        (reducedCuspUpperConstantCoefficient α)
        (reducedCuspUpperLinearCoefficient α) +
    14400 * (15 : ℝ) ^ (1 + α) * centralUpperBranchConstant α

noncomputable def centralLowerNeighboringBlockConstant (α : ℝ) : ℝ :=
  4 * (15 : ℝ) ^ 6 *
      centralAffineSmoothDssttConstant α
        (reducedCuspLowerConstantCoefficient α) 0 +
    14400 * (15 : ℝ) ^ (1 + α) * centralLowerBranchConstant α

theorem centralUpperNeighboringBlockConstant_nonneg
    {α : ℝ} (hα1 : 1 < α) :
    0 ≤ centralUpperNeighboringBlockConstant α := by
  unfold centralUpperNeighboringBlockConstant
  have hS : 0 ≤ centralAffineSmoothDssttConstant α
      (reducedCuspUpperConstantCoefficient α)
      (reducedCuspUpperLinearCoefficient α) := by
    unfold centralAffineSmoothDssttConstant centralPositivePowerJetConstant
      centralPositivePowerRpowBound centralPowerJetConstant
      centralNegativePowerRpowBound latitudePowerCoefficientEnvelope
      latitudeComparablePowerRpowConstant
    positivity
  exact add_nonneg (mul_nonneg (by positivity) hS)
    (mul_nonneg (by positivity) (centralUpperBranchConstant_nonneg hα1))

theorem centralLowerNeighboringBlockConstant_nonneg
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 ≤ centralLowerNeighboringBlockConstant α := by
  unfold centralLowerNeighboringBlockConstant
  have hS : 0 ≤ centralAffineSmoothDssttConstant α
      (reducedCuspLowerConstantCoefficient α) 0 := by
    unfold centralAffineSmoothDssttConstant centralPositivePowerJetConstant
      centralPositivePowerRpowBound centralPowerJetConstant
      centralNegativePowerRpowBound latitudePowerCoefficientEnvelope
      latitudeComparablePowerRpowConstant
    positivity
  exact add_nonneg (mul_nonneg (by positivity) hS)
    (mul_nonneg (by positivity)
      (centralLowerBranchConstant_nonneg hα0 hα1))

theorem centralComparable_neighboring_upper_block_bound
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k (latitudeKernel α)| ≤
      comparableLatitudeBlockMajorant α
        (centralUpperNeighboringBlockConstant α) N j k := by
  let S := centralAffineSmoothDssttConstant α
    (reducedCuspUpperConstantCoefficient α)
    (reducedCuspUpperLinearCoefficient α)
  let B := centralUpperBranchConstant α
  let Es := 64 * S * (finiteBandPopulation N j : ℝ) ^ 3 *
    (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4
  let Eb := 4 * (finiteBandPopulation N j : ℝ) *
    (finiteBandPopulation N k : ℝ) *
      (B * neighboringBandLength N j k ^ (1 + α))
  have hS : 0 ≤ S := by
    dsimp [S]
    unfold centralAffineSmoothDssttConstant centralPositivePowerJetConstant
      centralPositivePowerRpowBound centralPowerJetConstant
      centralNegativePowerRpowBound latitudePowerCoefficientEnvelope
      latitudeComparablePowerRpowConstant
    positivity
  have hB : 0 ≤ B := by
    exact centralUpperBranchConstant_nonneg hα1
  have hs :
      Es ≤ comparableLatitudeBlockMajorant α
        (4 * (15 : ℝ) ^ 6 * S) N j k :=
    central_neighboring_smooth_raw_bound_to_majorant
      (by linarith) hα2 hS hM hcentral hcomp hneigh le_rfl
  have hb :
      Eb ≤ comparableLatitudeBlockMajorant α
        (14400 * (15 : ℝ) ^ (1 + α) * B) N j k :=
    central_neighboring_cusp_raw_bound_to_majorant
      (by linarith) hα2 hB hM hcentral hcomp hneigh le_rfl
  have hraw := central_neighboring_upper_kernel_block_bound_raw
    hα1 hα2 hM hcentral hcomp hneigh
  calc
    |bandPairError N j k (latitudeKernel α)| ≤ Es + Eb := by
      simpa [Es, Eb, S, B] using hraw
    _ ≤ comparableLatitudeBlockMajorant α
          (4 * (15 : ℝ) ^ 6 * S) N j k +
        comparableLatitudeBlockMajorant α
          (14400 * (15 : ℝ) ^ (1 + α) * B) N j k :=
      add_le_add hs hb
    _ = comparableLatitudeBlockMajorant α
        (centralUpperNeighboringBlockConstant α) N j k := by
      unfold comparableLatitudeBlockMajorant
        centralUpperNeighboringBlockConstant
      dsimp [S, B]
      ring

theorem centralComparable_neighboring_lower_block_bound
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k (latitudeKernel α)| ≤
      comparableLatitudeBlockMajorant α
        (centralLowerNeighboringBlockConstant α) N j k := by
  let S := centralAffineSmoothDssttConstant α
    (reducedCuspLowerConstantCoefficient α) 0
  let B := centralLowerBranchConstant α
  let Es := 64 * S * (finiteBandPopulation N j : ℝ) ^ 3 *
    (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4
  let Eb := 4 * (finiteBandPopulation N j : ℝ) *
    (finiteBandPopulation N k : ℝ) *
      (B * neighboringBandLength N j k ^ (1 + α))
  have hS : 0 ≤ S := by
    dsimp [S]
    unfold centralAffineSmoothDssttConstant centralPositivePowerJetConstant
      centralPositivePowerRpowBound centralPowerJetConstant
      centralNegativePowerRpowBound latitudePowerCoefficientEnvelope
      latitudeComparablePowerRpowConstant
    positivity
  have hB : 0 ≤ B := centralLowerBranchConstant_nonneg hα0 hα1
  have hs :
      Es ≤ comparableLatitudeBlockMajorant α
        (4 * (15 : ℝ) ^ 6 * S) N j k :=
    central_neighboring_smooth_raw_bound_to_majorant
      hα0 (by linarith) hS hM hcentral hcomp hneigh le_rfl
  have hb :
      Eb ≤ comparableLatitudeBlockMajorant α
        (14400 * (15 : ℝ) ^ (1 + α) * B) N j k :=
    central_neighboring_cusp_raw_bound_to_majorant
      hα0 (by linarith) hB hM hcentral hcomp hneigh le_rfl
  have hraw := central_neighboring_lower_kernel_block_bound_raw
    hα0 hα1 hM hcentral hcomp hneigh
  calc
    |bandPairError N j k (latitudeKernel α)| ≤ Es + Eb := by
      simpa [Es, Eb, S, B] using hraw
    _ ≤ comparableLatitudeBlockMajorant α
          (4 * (15 : ℝ) ^ 6 * S) N j k +
        comparableLatitudeBlockMajorant α
          (14400 * (15 : ℝ) ^ (1 + α) * B) N j k :=
      add_le_add hs hb
    _ = comparableLatitudeBlockMajorant α
        (centralLowerNeighboringBlockConstant α) N j k := by
      unfold comparableLatitudeBlockMajorant
        centralLowerNeighboringBlockConstant
      dsimp [S, B]
      ring

/-- All central comparable blocks in the upper nonresonant range, reduced
only to the separated sharp mixed-derivative predicate. -/
theorem centralComparable_upper_block_bound_of_separated
    {α C : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hC : 0 ≤ C)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    (hanalytic : HasCentralComparableSeparatedDssttBound α N C) :
    ∀ j k, CentralLatitudePair N j k →
      ComparableLatitudeScales N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α
          (centralUpperNeighboringBlockConstant α +
            (15 : ℝ) ^ 6 / 2 * C) N j k := by
  apply centralComparable_block_bound_of_neighboring_and_analytic
    (by linarith : 0 < α)
    (centralUpperNeighboringBlockConstant_nonneg hα1) hC
    (by omega : 15 ≤ bandCount N)
  · intro j k hc hcomp hn
    exact centralComparable_neighboring_upper_block_bound
      hα1 hα2 hM hc hcomp hn
  · exact hanalytic

/-- All central comparable blocks in the lower nonresonant range, reduced
only to the separated sharp mixed-derivative predicate. -/
theorem centralComparable_lower_block_bound_of_separated
    {α C : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    (hanalytic : HasCentralComparableSeparatedDssttBound α N C) :
    ∀ j k, CentralLatitudePair N j k →
      ComparableLatitudeScales N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α
          (centralLowerNeighboringBlockConstant α +
            (15 : ℝ) ^ 6 / 2 * C) N j k := by
  apply centralComparable_block_bound_of_neighboring_and_analytic
    hα0 (centralLowerNeighboringBlockConstant_nonneg hα0 hα1) hC
    (by omega : 15 ≤ bandCount N)
  · intro j k hc hcomp hn
    exact centralComparable_neighboring_lower_block_bound
      hα0 hα1 hM hc hcomp hn
  · exact hanalytic

end BEMOC
