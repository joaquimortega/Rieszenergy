import BEMOCFormalization.MixedTaylorRemainder
import BEMOCFormalization.LatitudeVariableMixedDerivative
import BEMOCFormalization.LatitudeL2
import Mathlib.Topology.TietzeExtension

/-!
# Mixed Taylor specialization for the latitude kernel

This module derives the tensor Peano remainder directly from the explicit
off-diagonal derivative chain for `variableReducedLatitudeKernel`.
-/

open MeasureTheory Set

namespace BEMOC

/-- A degree-one Taylor bound from an explicit first/second derivative
chain.  Continuity of the second derivative is not required. -/
theorem abs_sub_linear_le_of_hasDerivAt_chain
    {f f₁ f₂ : ℝ → ℝ} {a b C x : ℝ}
    (_hab : a ≤ b) (hx : x ∈ Icc a b) (hC : 0 ≤ C)
    (hf : ∀ y ∈ Icc a b, HasDerivAt f (f₁ y) y)
    (hf₁ : ∀ y ∈ Icc a b, HasDerivAt f₁ (f₂ y) y)
    (hf₂ : ∀ y ∈ Icc a b, |f₂ y| ≤ C) :
    |f x - f a - (x - a) * f₁ a| ≤ C * (b - a) ^ 2 := by
  rcases eq_or_lt_of_le hx.1 with hxa | hax
  · subst x
    simp
    positivity
  have hxb : x ≤ b := hx.2
  have hI : Icc a x ⊆ Icc a b := by
    intro y hy
    exact ⟨hy.1, hy.2.trans hxb⟩
  have hdiff : DifferentiableOn ℝ f (Icc a x) := by
    intro y hy
    exact (hf y (hI hy)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ y ∈ Icc a x, derivWithin f (Icc a x) y = f₁ y := by
    intro y hy
    exact (hf y (hI hy)).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hax) y hy)
  have hcont₁ : ContinuousOn f₁ (Icc a x) := by
    intro y hy
    exact (hf₁ y (hI hy)).continuousAt.continuousWithinAt
  have hcontDeriv :
      ContinuousOn (derivWithin f (Icc a x)) (Icc a x) :=
    hcont₁.congr fun y hy ↦ hderiv y hy
  have hfC1 : ContDiffOn ℝ 1 f (Icc a x) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hax)]
    refine ⟨hdiff, ?_, ?_⟩
    · simp
    · rwa [contDiffOn_zero]
  have hiter₁ : ∀ y ∈ Icc a x,
      iteratedDerivWithin 1 f (Icc a x) y = f₁ y := by
    intro y hy
    rw [show (1 : ℕ) = 0 + 1 by norm_num,
      iteratedDerivWithin_succ, iteratedDerivWithin_zero]
    exact hderiv y hy
  have hdiff₁ : DifferentiableOn ℝ f₁ (Ioo a x) := by
    intro y hy
    exact (hf₁ y (hI ⟨hy.1.le, hy.2.le⟩)).differentiableAt
      |>.differentiableWithinAt
  have hiterDiff :
      DifferentiableOn ℝ
        (iteratedDerivWithin 1 f (Icc a x)) (Ioo a x) := by
    apply hdiff₁.congr
    intro y hy
    exact hiter₁ y ⟨hy.1.le, hy.2.le⟩
  obtain ⟨y, hy, hrem⟩ :=
    taylor_mean_remainder_lagrange (n := 1) hax hfC1 hiterDiff
  have hyI : y ∈ Icc a x := ⟨hy.1.le, hy.2.le⟩
  have hiter₂ :
      iteratedDerivWithin 2 f (Icc a x) y = f₂ y := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDerivWithin_succ]
    have heq : Set.EqOn
        (iteratedDerivWithin 1 f (Icc a x)) f₁ (Icc a x) :=
      fun z hz ↦ hiter₁ z hz
    rw [derivWithin_congr heq (heq hyI)]
    exact (hf₁ y (hI hyI)).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hax) y hyI)
  have hTaylor :
      taylorWithinEval f 1 (Icc a x) a x =
        f a + (x - a) * f₁ a := by
    rw [show taylorWithinEval f 1 (Icc a x) a x =
      f a + (x - a) * derivWithin f (Icc a x) a by
        simp [taylorWithinEval_succ]]
    rw [hderiv a ⟨le_rfl, hax.le⟩]
  have hyB : |f₂ y| ≤ C := hf₂ y (hI hyI)
  rw [hTaylor, hiter₂] at hrem
  have hwidth : 0 ≤ x - a := sub_nonneg.mpr hax.le
  have hwidthB : x - a ≤ b - a := by linarith
  rw [show f x - f a - (x - a) * f₁ a =
      f x - (f a + (x - a) * f₁ a) by ring,
    hrem, abs_div, abs_mul, abs_pow, abs_of_nonneg hwidth]
  norm_num
  calc
    |f₂ y| * (x - a) ^ 2 / 2 ≤ C * (x - a) ^ 2 := by
      nlinarith [sq_nonneg (x - a)]
    _ ≤ C * (b - a) ^ 2 := by
      gcongr

/-! ## The missing first mixed derivative chain -/

noncomputable def variableReducedLatitudeKernelDst
    (α s t : ℝ) : ℝ :=
  latitudeJetMulD1
      (latitudePowerDs α s t) (latitudePowerDst α s t)
      (latitudeCusp0 α s t) (latitudeCusp0Dt α s t) +
    latitudeJetMul3D1
      (latitudePower α s t) (latitudePowerDt α s t)
      (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
      (normalizedLatitudeGapDs s t) (normalizedLatitudeGapDst s t)

noncomputable def variableReducedLatitudeKernelDstt
    (α s t : ℝ) : ℝ :=
  latitudeJetMulD2
      (latitudePowerDs α s t) (latitudePowerDst α s t)
        (latitudePowerDstt α s t)
      (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
        (latitudeCusp0Dtt α s t) +
    latitudeJetMul3D2
      (latitudePower α s t) (latitudePowerDt α s t)
        (latitudePowerDtt α s t)
      (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
        (latitudeCusp1Dtt α s t)
      (normalizedLatitudeGapDs s t) (normalizedLatitudeGapDst s t)
        (normalizedLatitudeGapDstt s t)

theorem hasDerivAt_variableReducedLatitudeKernelDs_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ variableReducedLatitudeKernelDs α s y)
      (variableReducedLatitudeKernelDst α s t) t := by
  have hP := hasDerivAt_latitudePower_right (α := α) hs ht
  have hPs := hasDerivAt_latitudePowerDs_right (α := α) hs ht
  have hH0 := hasDerivAt_latitudeCusp0_right (α := α) hs ht hst
  have hH1 := hasDerivAt_latitudeCusp1_right (α := α) hs ht hst
  have hQs := hasDerivAt_normalizedLatitudeGapDs_right hs ht
  change HasDerivAt
    (fun y ↦
      latitudePowerDs α s y * latitudeCusp0 α s y +
        latitudePower α s y * latitudeCusp1 α s y *
          normalizedLatitudeGapDs s y)
    (variableReducedLatitudeKernelDst α s t) t
  unfold variableReducedLatitudeKernelDst latitudeJetMulD1
    latitudeJetMul3D1
  convert (hPs.mul hH0).add ((hP.mul hH1).mul hQs) using 1 ; ring

theorem hasDerivAt_variableReducedLatitudeKernelDst_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ variableReducedLatitudeKernelDst α s y)
      (variableReducedLatitudeKernelDstt α s t) t := by
  have hP := hasDerivAt_latitudePower_right (α := α) hs ht
  have hPt := hasDerivAt_latitudePowerDt_right (α := α) hs ht
  have hPs := hasDerivAt_latitudePowerDs_right (α := α) hs ht
  have hPst := hasDerivAt_latitudePowerDst_right (α := α) hs ht
  have hH0 := hasDerivAt_latitudeCusp0_right (α := α) hs ht hst
  have hH0t := hasDerivAt_latitudeCusp0Dt_right (α := α) hs ht hst
  have hH1 := hasDerivAt_latitudeCusp1_right (α := α) hs ht hst
  have hH1t := hasDerivAt_latitudeCusp1Dt_right (α := α) hs ht hst
  have hQs := hasDerivAt_normalizedLatitudeGapDs_right hs ht
  have hQst := hasDerivAt_normalizedLatitudeGapDst_right hs ht
  unfold variableReducedLatitudeKernelDst
    variableReducedLatitudeKernelDstt
  exact (hasDerivAt_latitudeJetMulD1 hPs hPst hH0 hH0t).add
    (hasDerivAt_latitudeJetMul3D1 hP hPt hH1 hH1t hQs hQst)

theorem latitudeAngularScale_comm (s t : ℝ) :
    latitudeAngularScale s t = latitudeAngularScale t s := by
  unfold latitudeAngularScale
  ring

theorem latitudePower_comm (α s t : ℝ) :
    latitudePower α s t = latitudePower α t s := by
  unfold latitudePower
  rw [latitudeAngularScale_comm]

theorem latitudePowerDt_eq_Ds_swap (α s t : ℝ) :
    latitudePowerDt α s t = latitudePowerDs α t s := by
  unfold latitudePowerDt latitudePowerDs latitudeAngularScaleDt
  rw [latitudeAngularScale_comm]

theorem latitudePowerDtt_eq_Dss_swap (α s t : ℝ) :
    latitudePowerDtt α s t = latitudePowerDss α t s := by
  unfold latitudePowerDtt latitudePowerDss latitudeAngularScaleDt
    latitudeAngularScaleDtt
  rw [latitudeAngularScale_comm]

theorem latitudePowerDst_comm (α s t : ℝ) :
    latitudePowerDst α s t = latitudePowerDst α t s := by
  unfold latitudePowerDst latitudeAngularScaleDt
  rw [latitudeAngularScale_comm]
  unfold latitudeAngularScaleDst latitudeAngularScaleDs heightRadiusD1
  ring

theorem latitudePowerDstt_eq_Dsst_swap (α s t : ℝ) :
    latitudePowerDstt α s t = latitudePowerDsst α t s := by
  unfold latitudePowerDstt latitudePowerDsst latitudeAngularScaleDt
    latitudeAngularScaleDtt latitudeAngularScaleDstt
  rw [latitudeAngularScale_comm]
  unfold latitudeAngularScaleDst latitudeAngularScaleDsst
    latitudeAngularScaleDs latitudeAngularScaleDss heightRadiusD1
    heightRadiusD2
  ring

theorem normalizedLatitudeGapDst_comm (s t : ℝ) :
    normalizedLatitudeGapDst s t = normalizedLatitudeGapDst t s := by
  unfold normalizedLatitudeGapDst
  ring

theorem variableReducedLatitudeKernelDstt_eq_Dsst_swap
    (α s t : ℝ) :
    variableReducedLatitudeKernelDstt α s t =
      variableReducedLatitudeKernelDsst α t s := by
  unfold variableReducedLatitudeKernelDstt
    variableReducedLatitudeKernelDsst latitudeJetMulD1
    latitudeJetMulD2 latitudeJetMul3D1 latitudeJetMul3D2
  unfold latitudeCusp0 latitudeCusp0Dt latitudeCusp0Dtt
    latitudeCusp1 latitudeCusp1Dt latitudeCusp1Dtt
    latitudeCusp2 latitudeCusp2Dt
  rw [latitudePower_comm α s t,
    latitudePowerDt_eq_Ds_swap α s t,
    latitudePowerDtt_eq_Dss_swap α s t,
    latitudePowerDst_comm α s t,
    latitudePowerDstt_eq_Dsst_swap α s t,
    ← latitudePowerDt_eq_Ds_swap α t s,
    normalizedLatitudeGap_comm s t,
    normalizedLatitudeGapDst_comm s t]
  unfold normalizedLatitudeGapDt normalizedLatitudeGapDtt
    normalizedLatitudeGapDstt
  ring

/-! ## The explicit latitude tensor remainder -/

theorem variableReducedLatitudeKernel_comm (α s t : ℝ) :
    variableReducedLatitudeKernel α s t =
      variableReducedLatitudeKernel α t s := by
  unfold variableReducedLatitudeKernel
  rw [latitudeAngularScale_comm, normalizedLatitudeGap_comm]

noncomputable def latitudeFirstTaylorError
    (α a s t : ℝ) : ℝ :=
  variableReducedLatitudeKernel α s t -
    variableReducedLatitudeKernel α a t -
      (s - a) * variableReducedLatitudeKernelDs α a t

noncomputable def latitudeFirstTaylorErrorDt
    (α a s t : ℝ) : ℝ :=
  variableReducedLatitudeKernelDs α t s -
    variableReducedLatitudeKernelDs α t a -
      (s - a) * variableReducedLatitudeKernelDst α a t

noncomputable def latitudeFirstTaylorErrorDtt
    (α a s t : ℝ) : ℝ :=
  variableReducedLatitudeKernelDss α t s -
    variableReducedLatitudeKernelDss α t a -
      (s - a) * variableReducedLatitudeKernelDstt α a t

noncomputable def latitudeExplicitMixedRemainder
    (α a c s t : ℝ) : ℝ :=
  latitudeFirstTaylorError α a s t -
    latitudeFirstTaylorError α a s c -
      (t - c) * latitudeFirstTaylorErrorDt α a s c

theorem hasDerivAt_variableReducedLatitudeKernel_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ variableReducedLatitudeKernel α s y)
      (variableReducedLatitudeKernelDs α t s) t := by
  have h := hasDerivAt_variableReducedLatitudeKernel_left
    (α := α) (s := t) (t := s) ht hs hst.symm
  convert h using 1
  funext y
  exact variableReducedLatitudeKernel_comm α s y

theorem hasDerivAt_latitudeFirstTaylorError_right
    {α a s t : ℝ}
    (ha : a ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hst : s ≠ t) (hat : a ≠ t) :
    HasDerivAt (fun y ↦ latitudeFirstTaylorError α a s y)
      (latitudeFirstTaylorErrorDt α a s t) t := by
  have hK := hasDerivAt_variableReducedLatitudeKernel_right
    (α := α) hs ht hst
  have hKa := hasDerivAt_variableReducedLatitudeKernel_right
    (α := α) ha ht hat
  have hDs := hasDerivAt_variableReducedLatitudeKernelDs_right
    (α := α) ha ht hat
  unfold latitudeFirstTaylorError latitudeFirstTaylorErrorDt
  convert (hK.sub hKa).sub ((hasDerivAt_const t (s - a)).mul hDs)
    using 1 ; ring

theorem hasDerivAt_latitudeFirstTaylorErrorDt_right
    {α a s t : ℝ}
    (ha : a ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hst : s ≠ t) (hat : a ≠ t) :
    HasDerivAt (fun y ↦ latitudeFirstTaylorErrorDt α a s y)
      (latitudeFirstTaylorErrorDtt α a s t) t := by
  have hDss := hasDerivAt_variableReducedLatitudeKernelDs_left
    (α := α) (s := t) (t := s) ht hs hst.symm
  have hDssa := hasDerivAt_variableReducedLatitudeKernelDs_left
    (α := α) (s := t) (t := a) ht ha hat.symm
  have hDst := hasDerivAt_variableReducedLatitudeKernelDst_right
    (α := α) ha ht hat
  unfold latitudeFirstTaylorErrorDt latitudeFirstTaylorErrorDtt
  convert (hDss.sub hDssa).sub
    ((hasDerivAt_const t (s - a)).mul hDst) using 1 ; ring

/-- Exact decomposition into the mixed remainder, a term affine in `t`,
and a term affine in `s`. -/
theorem latitudeExplicitMixedRemainder_decomposition
    (α a c s t : ℝ) :
    variableReducedLatitudeKernel α s t =
      latitudeExplicitMixedRemainder α a c s t +
        (latitudeFirstTaylorErrorDt α a s c * t +
          (latitudeFirstTaylorError α a s c -
            c * latitudeFirstTaylorErrorDt α a s c)) +
        (variableReducedLatitudeKernelDs α a t * s +
          (variableReducedLatitudeKernel α a t -
            a * variableReducedLatitudeKernelDs α a t)) := by
  unfold latitudeExplicitMixedRemainder latitudeFirstTaylorError
  ring

/-- On an interior off-diagonal rectangle, the explicit tensor remainder
is bounded by the pointwise mixed `(2,2)` derivative bound times the
product of squared side lengths. -/
theorem abs_latitudeExplicitMixedRemainder_le
    {α a b c d C s t : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hC : 0 ≤ C)
    (hrect : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      x ∈ Ioo (-1 : ℝ) 1 ∧ y ∈ Ioo (-1 : ℝ) 1 ∧ x ≠ y)
    (hmixed : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      |variableReducedLatitudeKernelDsstt α y x| ≤ C)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc c d) :
    |latitudeExplicitMixedRemainder α a c s t| ≤
      C * (b - a) ^ 2 * (d - c) ^ 2 := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hcI : c ∈ Icc c d := ⟨le_rfl, hcd⟩
  have hinner (y : ℝ) (hy : y ∈ Icc c d) :
      |latitudeFirstTaylorErrorDtt α a s y| ≤ C * (b - a) ^ 2 := by
    have hchain := abs_sub_linear_le_of_hasDerivAt_chain
      (f := fun x ↦ variableReducedLatitudeKernelDss α y x)
      (f₁ := fun x ↦ variableReducedLatitudeKernelDsst α y x)
      (f₂ := fun x ↦ variableReducedLatitudeKernelDsstt α y x)
      hab hs hC
      (fun x hx ↦ by
        have hr := hrect x hx y hy
        exact hasDerivAt_variableReducedLatitudeKernelDss_right
          (α := α) hr.2.1 hr.1 hr.2.2.symm)
      (fun x hx ↦ by
        have hr := hrect x hx y hy
        exact hasDerivAt_variableReducedLatitudeKernelDsst_right
          (α := α) hr.2.1 hr.1 hr.2.2.symm)
      (fun x hx ↦ hmixed x hx y hy)
    rw [latitudeFirstTaylorErrorDtt,
      variableReducedLatitudeKernelDstt_eq_Dsst_swap]
    exact hchain
  apply abs_sub_linear_le_of_hasDerivAt_chain
    (f := fun y ↦ latitudeFirstTaylorError α a s y)
    (f₁ := fun y ↦ latitudeFirstTaylorErrorDt α a s y)
    (f₂ := fun y ↦ latitudeFirstTaylorErrorDtt α a s y)
    hcd ht (mul_nonneg hC (sq_nonneg _))
  · intro y hy
    have hrs := hrect s hs y hy
    have hra := hrect a haI y hy
    exact hasDerivAt_latitudeFirstTaylorError_right
      hra.1 hrs.1 hrs.2.1 hrs.2.2 hra.2.2
  · intro y hy
    have hrs := hrect s hs y hy
    have hra := hrect a haI y hy
    exact hasDerivAt_latitudeFirstTaylorErrorDt_right
      hra.1 hrs.1 hrs.2.1 hrs.2.2 hra.2.2
  · intro y hy
    exact hinner y hy

/-! The right-first orientation consumes the latitude `Dsstt(s,t)` bound
without transposing its arguments. -/

noncomputable def latitudeRightTaylorError
    (α c s t : ℝ) : ℝ :=
  variableReducedLatitudeKernel α s t -
    variableReducedLatitudeKernel α s c -
      (t - c) * variableReducedLatitudeKernelDs α c s

noncomputable def latitudeRightTaylorErrorDs
    (α c s t : ℝ) : ℝ :=
  variableReducedLatitudeKernelDs α s t -
    variableReducedLatitudeKernelDs α s c -
      (t - c) * variableReducedLatitudeKernelDst α c s

noncomputable def latitudeRightTaylorErrorDss
    (α c s t : ℝ) : ℝ :=
  variableReducedLatitudeKernelDss α s t -
    variableReducedLatitudeKernelDss α s c -
      (t - c) * variableReducedLatitudeKernelDstt α c s

noncomputable def latitudeExplicitMixedRemainderRightFirst
    (α a c s t : ℝ) : ℝ :=
  latitudeRightTaylorError α c s t -
    latitudeRightTaylorError α c a t -
      (s - a) * latitudeRightTaylorErrorDs α c a t

theorem hasDerivAt_latitudeRightTaylorError_left
    {α c s t : ℝ}
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hst : s ≠ t) (hsc : s ≠ c) :
    HasDerivAt (fun x ↦ latitudeRightTaylorError α c x t)
      (latitudeRightTaylorErrorDs α c s t) s := by
  have hK := hasDerivAt_variableReducedLatitudeKernel_left
    (α := α) hs ht hst
  have hKc := hasDerivAt_variableReducedLatitudeKernel_left
    (α := α) hs hc hsc
  have hDs := hasDerivAt_variableReducedLatitudeKernelDs_right
    (α := α) hc hs hsc.symm
  unfold latitudeRightTaylorError latitudeRightTaylorErrorDs
  convert (hK.sub hKc).sub ((hasDerivAt_const s (t - c)).mul hDs)
    using 1 ; ring

theorem hasDerivAt_latitudeRightTaylorErrorDs_left
    {α c s t : ℝ}
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hst : s ≠ t) (hsc : s ≠ c) :
    HasDerivAt (fun x ↦ latitudeRightTaylorErrorDs α c x t)
      (latitudeRightTaylorErrorDss α c s t) s := by
  have hK := hasDerivAt_variableReducedLatitudeKernelDs_left
    (α := α) hs ht hst
  have hKc := hasDerivAt_variableReducedLatitudeKernelDs_left
    (α := α) hs hc hsc
  have hDst := hasDerivAt_variableReducedLatitudeKernelDst_right
    (α := α) hc hs hsc.symm
  unfold latitudeRightTaylorErrorDs latitudeRightTaylorErrorDss
  convert (hK.sub hKc).sub
    ((hasDerivAt_const s (t - c)).mul hDst) using 1 ; ring

theorem latitudeExplicitMixedRemainderRightFirst_decomposition
    (α a c s t : ℝ) :
    variableReducedLatitudeKernel α s t =
      latitudeExplicitMixedRemainderRightFirst α a c s t +
        (variableReducedLatitudeKernelDs α c s * t +
          (variableReducedLatitudeKernel α s c -
            c * variableReducedLatitudeKernelDs α c s)) +
        (latitudeRightTaylorErrorDs α c a t * s +
          (latitudeRightTaylorError α c a t -
            a * latitudeRightTaylorErrorDs α c a t)) := by
  unfold latitudeExplicitMixedRemainderRightFirst
    latitudeRightTaylorError
  ring

theorem abs_latitudeExplicitMixedRemainderRightFirst_le
    {α a b c d C s t : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hC : 0 ≤ C)
    (hrect : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      x ∈ Ioo (-1 : ℝ) 1 ∧ y ∈ Ioo (-1 : ℝ) 1 ∧ x ≠ y)
    (hmixed : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      |variableReducedLatitudeKernelDsstt α x y| ≤ C)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc c d) :
    |latitudeExplicitMixedRemainderRightFirst α a c s t| ≤
      C * (b - a) ^ 2 * (d - c) ^ 2 := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hcI : c ∈ Icc c d := ⟨le_rfl, hcd⟩
  have hinner (x : ℝ) (hx : x ∈ Icc a b) :
      |latitudeRightTaylorErrorDss α c x t| ≤ C * (d - c) ^ 2 := by
    have hchain := abs_sub_linear_le_of_hasDerivAt_chain
      (f := fun y ↦ variableReducedLatitudeKernelDss α x y)
      (f₁ := fun y ↦ variableReducedLatitudeKernelDsst α x y)
      (f₂ := fun y ↦ variableReducedLatitudeKernelDsstt α x y)
      hcd ht hC
      (fun y hy ↦ by
        have hr := hrect x hx y hy
        exact hasDerivAt_variableReducedLatitudeKernelDss_right
          (α := α) hr.1 hr.2.1 hr.2.2)
      (fun y hy ↦ by
        have hr := hrect x hx y hy
        exact hasDerivAt_variableReducedLatitudeKernelDsst_right
          (α := α) hr.1 hr.2.1 hr.2.2)
      (fun y hy ↦ hmixed x hx y hy)
    rw [latitudeRightTaylorErrorDss,
      variableReducedLatitudeKernelDstt_eq_Dsst_swap]
    exact hchain
  have hmain := abs_sub_linear_le_of_hasDerivAt_chain
    (f := fun x ↦ latitudeRightTaylorError α c x t)
    (f₁ := fun x ↦ latitudeRightTaylorErrorDs α c x t)
    (f₂ := fun x ↦ latitudeRightTaylorErrorDss α c x t)
    hab hs (mul_nonneg hC (sq_nonneg _))
    (fun x hx ↦ by
      have hrt := hrect x hx t ht
      have hrc := hrect x hx c hcI
      exact hasDerivAt_latitudeRightTaylorError_left
        hrc.2.1 hrt.1 hrt.2.1 hrt.2.2 hrc.2.2)
    (fun x hx ↦ by
      have hrt := hrect x hx t ht
      have hrc := hrect x hx c hcI
      exact hasDerivAt_latitudeRightTaylorErrorDs_left
        hrc.2.1 hrt.1 hrt.2.1 hrt.2.2 hrc.2.2)
    (fun x hx ↦ hinner x hx)
  unfold latitudeExplicitMixedRemainderRightFirst
  calc
    |latitudeRightTaylorError α c s t -
        latitudeRightTaylorError α c a t -
          (s - a) * latitudeRightTaylorErrorDs α c a t| ≤
      (C * (d - c) ^ 2) * (b - a) ^ 2 := hmain
    _ = C * (b - a) ^ 2 * (d - c) ^ 2 := by ring

set_option maxHeartbeats 800000 in
theorem continuousOn_latitudeExplicitMixedRemainderRightFirst
    {α a b c d : ℝ} (hα : 0 < α) (hab : a ≤ b) (hcd : c ≤ d)
    (hrect : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      x ∈ Ioo (-1 : ℝ) 1 ∧ y ∈ Ioo (-1 : ℝ) 1 ∧ x ≠ y) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦
        latitudeExplicitMixedRemainderRightFirst α a c p.1 p.2)
      (Icc a b ×ˢ Icc c d) := by
  let F : ℝ × ℝ → ℝ := fun p ↦
    (latitudeKernel α p.1 p.2 -
      latitudeKernel α p.1 c -
        (p.2 - c) * variableReducedLatitudeKernelDs α c p.1) -
    (latitudeKernel α a p.2 -
      latitudeKernel α a c -
        (p.2 - c) * variableReducedLatitudeKernelDs α c a) -
    (p.1 - a) *
      (variableReducedLatitudeKernelDs α a p.2 -
        variableReducedLatitudeKernelDs α a c -
          (p.2 - c) * variableReducedLatitudeKernelDst α c a)
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hcI : c ∈ Icc c d := ⟨le_rfl, hcd⟩
  have heq : ∀ q ∈ Icc a b ×ˢ Icc c d,
      latitudeExplicitMixedRemainderRightFirst α a c q.1 q.2 = F q := by
    intro q hq
    have hqst := hrect q.1 hq.1 q.2 hq.2
    have hqsc := hrect q.1 hq.1 c hcI
    have haqt := hrect a haI q.2 hq.2
    have hac := hrect a haI c hcI
    unfold latitudeExplicitMixedRemainderRightFirst
      latitudeRightTaylorError latitudeRightTaylorErrorDs
    dsimp [F]
    rw [← latitudeKernel_eq_variableReducedLatitudeKernel hqst.1 hqst.2.1,
      ← latitudeKernel_eq_variableReducedLatitudeKernel hqsc.1 hqsc.2.1,
      ← latitudeKernel_eq_variableReducedLatitudeKernel haqt.1 haqt.2.1,
      ← latitudeKernel_eq_variableReducedLatitudeKernel hac.1 hac.2.1]
  intro p hp
  have hr := hrect p.1 hp.1 p.2 hp.2
  have hrc := hrect p.1 hp.1 c hcI
  have hra := hrect a haI p.2 hp.2
  have hrac := hrect a haI c hcI
  have hDsc :
      ContinuousAt (fun x ↦ variableReducedLatitudeKernelDs α c x) p.1 :=
    (hasDerivAt_variableReducedLatitudeKernelDs_right
      (α := α) hrc.2.1 hrc.1 hrc.2.2.symm).continuousAt
  have hDsa :
      ContinuousAt (fun y ↦ variableReducedLatitudeKernelDs α a y) p.2 :=
    (hasDerivAt_variableReducedLatitudeKernelDs_right
      (α := α) hra.1 hra.2.1 hra.2.2).continuousAt
  have hF : ContinuousAt F p := by
    dsimp [F]
    have hK := continuous_latitudeKernel hα
    have hKst :
        ContinuousAt (fun q : ℝ × ℝ ↦ latitudeKernel α q.1 q.2) p :=
      hK.continuousAt
    have hKsc :
        ContinuousAt (fun q : ℝ × ℝ ↦ latitudeKernel α q.1 c) p :=
      (hK.comp (continuous_fst.prodMk continuous_const)).continuousAt
    have hKat :
        ContinuousAt (fun q : ℝ × ℝ ↦ latitudeKernel α a q.2) p :=
      (hK.comp (continuous_const.prodMk continuous_snd)).continuousAt
    have hDsc' :
        ContinuousAt
          (fun q : ℝ × ℝ ↦ variableReducedLatitudeKernelDs α c q.1) p :=
      hDsc.comp continuousAt_fst
    have hDsa' :
        ContinuousAt
          (fun q : ℝ × ℝ ↦ variableReducedLatitudeKernelDs α a q.2) p :=
      hDsa.comp continuousAt_snd
    have hE :
        ContinuousAt (fun q : ℝ × ℝ ↦
          latitudeKernel α q.1 q.2 - latitudeKernel α q.1 c -
            (q.2 - c) * variableReducedLatitudeKernelDs α c q.1) p :=
      (hKst.sub hKsc).sub
        ((continuousAt_snd.sub continuousAt_const).mul hDsc')
    have hEa :
        ContinuousAt (fun q : ℝ × ℝ ↦
          latitudeKernel α a q.2 - latitudeKernel α a c -
            (q.2 - c) * variableReducedLatitudeKernelDs α c a) p :=
      (hKat.sub continuousAt_const).sub
        ((continuousAt_snd.sub continuousAt_const).mul continuousAt_const)
    have hEsa :
        ContinuousAt (fun q : ℝ × ℝ ↦
          variableReducedLatitudeKernelDs α a q.2 -
            variableReducedLatitudeKernelDs α a c -
              (q.2 - c) * variableReducedLatitudeKernelDst α c a) p :=
      (hDsa'.sub continuousAt_const).sub
        ((continuousAt_snd.sub continuousAt_const).mul continuousAt_const)
    exact (hE.sub hEa).sub
      ((continuousAt_fst.sub continuousAt_const).mul hEsa)
  apply hF.continuousWithinAt.congr
  · intro q hq
    exact heq q hq
  · exact heq p hp

theorem bandError_congr_on_literalBand
    {N : ℕ} (j : Fin (bandTailCount N + 1)) {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j), f x = g x) :
    bandError N j f = bandError N j g := by
  rw [← bandError_restrictLatitudeBand j f,
    ← bandError_restrictLatitudeBand j g]
  congr 2
  funext x
  unfold restrictLatitudeBand
  split_ifs with hx
  · exact hfg x hx
  · rfl

theorem bandPairError_congr_on_literalRectangle
    {N : ℕ} (j k : Fin (bandTailCount N + 1))
    {K L : ℝ → ℝ → ℝ}
    (hKL : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k), K s t = L s t) :
    bandPairError N j k K = bandPairError N j k L := by
  unfold bandPairError
  apply bandError_congr_on_literalBand j
  intro s hs
  apply bandError_congr_on_literalBand k
  intro t ht
  exact hKL s hs t ht

/-- Fully concrete Peano transfer on a literal off-diagonal band
rectangle.  All regularity, commutation, and integrability facts are
discharged here; the only analytic inequality left to the caller is the
pointwise bound on the already computed `Dsstt` expression. -/
theorem abs_latitudeKernel_bandPairError_le_of_Dsstt
    {α C : ℝ} {N : ℕ} (hN : 0 < N) (hα : 0 < α) (hC : 0 ≤ C)
    (j k : Fin (bandTailCount N + 1))
    (hrect : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
      s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧ s ≠ t)
    (hmixed : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
      |variableReducedLatitudeKernelDsstt α s t| ≤ C) :
    |bandPairError N j k (latitudeKernel α)| ≤
      64 * C * (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  let Is : Set ℝ := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It : Set ℝ := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  let a : ℝ := bandBoundaryHeight N (j + 1)
  let c : ℝ := bandBoundaryHeight N (k + 1)
  let R : ℝ → ℝ → ℝ := fun s t ↦
    latitudeExplicitMixedRemainderRightFirst α a c s t
  have hcontR : ContinuousOn (fun p : ℝ × ℝ ↦ R p.1 p.2) (Is ×ˢ It) := by
    exact continuousOn_latitudeExplicitMixedRemainderRightFirst
      hα (bandBoundaryHeight_succ_le j) (bandBoundaryHeight_succ_le k)
      hrect
  let fR : C(Is ×ˢ It, ℝ) :=
    ⟨fun p ↦ R p.1.1 p.1.2,
      (continuousOn_iff_continuous_restrict.mp hcontR)⟩
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq
    (isClosed_Icc.prod isClosed_Icc) fR
  have hGeq : ∀ p ∈ Is ×ˢ It, G p = R p.1 p.2 := by
    intro p hp
    have hv := DFunLike.congr_fun hG (⟨p, hp⟩ : Is ×ˢ It)
    exact hv
  let uRight : ℝ → ℝ := fun s ↦
    variableReducedLatitudeKernelDs α c s
  let vRight : ℝ → ℝ := fun s ↦
    variableReducedLatitudeKernel α s c -
      c * variableReducedLatitudeKernelDs α c s
  let uLeft : ℝ → ℝ := fun t ↦
    latitudeRightTaylorErrorDs α c a t
  let vLeft : ℝ → ℝ := fun t ↦
    latitudeRightTaylorError α c a t -
      a * latitudeRightTaylorErrorDs α c a t
  let Kext : ℝ → ℝ → ℝ := fun s t ↦
    G (s, t) + (uRight s * t + vRight s) +
      (uLeft t * s + vLeft t)
  have hpair :
      bandPairError N j k (latitudeKernel α) =
        bandPairError N j k Kext := by
    apply bandPairError_congr_on_literalRectangle j k
    intro s hs t ht
    have hr := hrect s hs t ht
    rw [latitudeKernel_eq_variableReducedLatitudeKernel hr.1 hr.2.1]
    rw [latitudeExplicitMixedRemainderRightFirst_decomposition]
    have hGR : G (s, t) = R s t := hGeq (s, t) ⟨hs, ht⟩
    dsimp [Kext, uRight, vRight, uLeft, vLeft, R]
    rw [hGR]
  rw [hpair]
  apply abs_bandPairError_le_of_biaffine_mixed_remainder hN j k
    Kext (fun s t ↦ G (s, t)) uRight vRight uLeft vLeft C hC
  · intro s
    exact (G.continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (continuous_bandError_right k G.continuous).intervalIntegrable _ _
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (bandBoundaryHeight_succ_le k)]
    intro t ht
    have haI : a ∈ Is := ⟨le_rfl, bandBoundaryHeight_succ_le j⟩
    have hr := hrect a haI t ht
    have hrc := hrect a haI c
      (show c ∈ It from ⟨le_rfl, bandBoundaryHeight_succ_le k⟩)
    dsimp [uLeft]
    unfold latitudeRightTaylorErrorDs
    exact (((hasDerivAt_variableReducedLatitudeKernelDs_right
      (α := α) hr.1 hr.2.1 hr.2.2).continuousAt.sub
        continuousAt_const).sub
      ((hasDerivAt_id t).sub_const c |>.mul_const
        (variableReducedLatitudeKernelDst α c a) |>.continuousAt)).continuousWithinAt
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (bandBoundaryHeight_succ_le k)]
    intro t ht
    have haI : a ∈ Is := ⟨le_rfl, bandBoundaryHeight_succ_le j⟩
    have hr := hrect a haI t ht
    have hcI : c ∈ It := ⟨le_rfl, bandBoundaryHeight_succ_le k⟩
    have hrc := hrect a haI c hcI
    have hE : ContinuousAt (fun y ↦
        latitudeRightTaylorError α c a y) t := by
      unfold latitudeRightTaylorError
      exact (((hasDerivAt_variableReducedLatitudeKernel_right
        (α := α) hr.1 hr.2.1 hr.2.2).continuousAt.sub
          continuousAt_const).sub
        ((hasDerivAt_id t).sub_const c |>.mul_const
          (variableReducedLatitudeKernelDs α c a) |>.continuousAt))
    have hEs : ContinuousAt (fun y ↦
        latitudeRightTaylorErrorDs α c a y) t := by
      unfold latitudeRightTaylorErrorDs
      exact (((hasDerivAt_variableReducedLatitudeKernelDs_right
        (α := α) hr.1 hr.2.1 hr.2.2).continuousAt.sub
          continuousAt_const).sub
        ((hasDerivAt_id t).sub_const c |>.mul_const
          (variableReducedLatitudeKernelDst α c a) |>.continuousAt))
    dsimp [vLeft]
    exact (hE.sub (continuousAt_const.mul hEs)).continuousWithinAt
  · intro s t
    rfl
  · intro s hs t ht
    rw [hGeq (s, t) ⟨hs, ht⟩]
    dsimp [R, Is, It, a, c]
    simpa [bandWidth] using
      abs_latitudeExplicitMixedRemainderRightFirst_le
        (bandBoundaryHeight_succ_le j)
        (bandBoundaryHeight_succ_le k) hC hrect hmixed hs ht

end BEMOC
