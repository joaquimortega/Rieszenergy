import BEMOCFormalization.LatitudeCentralSmoothClosure

/-! Global continuous transfer of the central smooth tensor remainder. -/

open MeasureTheory Set

namespace BEMOC

set_option maxHeartbeats 800000

theorem continuousAt_latitudePower_joint
    {γ s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (fun p : ℝ × ℝ ↦ latitudePower γ p.1 p.2) (s, t) := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hpcont : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScale p.1 p.2) (s, t) := by
    unfold latitudeAngularScale
    fun_prop
  change ContinuousAt
    (fun p : ℝ × ℝ ↦ latitudeAngularScale p.1 p.2 ^ (γ / 2)) (s, t)
  exact ContinuousAt.comp'
    (f := fun p : ℝ × ℝ ↦ latitudeAngularScale p.1 p.2)
    (g := fun x : ℝ ↦ x ^ (γ / 2))
    (Real.continuousAt_rpow_const _ _ (Or.inl hp.ne')) hpcont

theorem continuousAt_latitudePowerDs_joint
    {γ s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (fun p : ℝ × ℝ ↦ latitudePowerDs γ p.1 p.2) (s, t) := by
  have hpow := continuousAt_latitudePower_joint
    (γ := γ - 2) hs ht
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hpcont : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScale p.1 p.2) (s, t) := by
    unfold latitudeAngularScale
    fun_prop
  have hrS : ContinuousAt (fun p : ℝ × ℝ ↦ heightRadius p.1) (s, t) := by
    unfold heightRadius
    fun_prop
  have hrT : ContinuousAt (fun p : ℝ × ℝ ↦ heightRadius p.2) (s, t) := by
    unfold heightRadius
    fun_prop
  have hdS : ContinuousAt
      (fun p : ℝ × ℝ ↦ heightRadiusD1 p.1) (s, t) := by
    unfold heightRadiusD1
    exact continuousAt_fst.neg.div hrS (heightRadius_pos hs).ne'
  have hpDs : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScaleDs p.1 p.2) (s, t) := by
    unfold latitudeAngularScaleDs
    exact (continuousAt_const.mul hdS).mul hrT
  have hpow' : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScale p.1 p.2 ^ (γ / 2 - 1))
      (s, t) :=
    ContinuousAt.comp'
      (f := fun p : ℝ × ℝ ↦ latitudeAngularScale p.1 p.2)
      (g := fun x : ℝ ↦ x ^ (γ / 2 - 1))
      (Real.continuousAt_rpow_const _ _ (Or.inl hp.ne')) hpcont
  change ContinuousAt
    (fun p : ℝ × ℝ ↦
      (γ / 2) * latitudeAngularScale p.1 p.2 ^ (γ / 2 - 1) *
        latitudeAngularScaleDs p.1 p.2) (s, t)
  exact (continuousAt_const.mul hpow').mul hpDs

theorem continuousAt_latitudePowerDt_joint
    {γ s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (fun p : ℝ × ℝ ↦ latitudePowerDt γ p.1 p.2) (s, t) := by
  have hswap : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudePowerDs γ p.2 p.1) (s, t) := by
    exact ContinuousAt.comp'
      (f := fun p : ℝ × ℝ ↦ (p.2, p.1))
      (g := fun p : ℝ × ℝ ↦ latitudePowerDs γ p.1 p.2)
      (continuousAt_latitudePowerDs_joint ht hs)
      (continuousAt_snd.prodMk continuousAt_fst)
  apply hswap.congr_of_eventuallyEq
  filter_upwards with p
  exact latitudePowerDt_eq_Ds_swap γ p.1 p.2

theorem continuousAt_latitudePowerDst_joint
    {γ s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (fun p : ℝ × ℝ ↦ latitudePowerDst γ p.1 p.2) (s, t) := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hpcont : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScale p.1 p.2) (s, t) := by
    unfold latitudeAngularScale
    fun_prop
  have hpow (e : ℝ) : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScale p.1 p.2 ^ e) (s, t) :=
    ContinuousAt.comp'
      (f := fun p : ℝ × ℝ ↦ latitudeAngularScale p.1 p.2)
      (g := fun x : ℝ ↦ x ^ e)
      (Real.continuousAt_rpow_const _ _ (Or.inl hp.ne')) hpcont
  have hrS : ContinuousAt (fun p : ℝ × ℝ ↦ heightRadius p.1) (s, t) := by
    unfold heightRadius
    fun_prop
  have hrT : ContinuousAt (fun p : ℝ × ℝ ↦ heightRadius p.2) (s, t) := by
    unfold heightRadius
    fun_prop
  have hdS : ContinuousAt
      (fun p : ℝ × ℝ ↦ heightRadiusD1 p.1) (s, t) := by
    unfold heightRadiusD1
    exact continuousAt_fst.neg.div hrS (heightRadius_pos hs).ne'
  have hdT : ContinuousAt
      (fun p : ℝ × ℝ ↦ heightRadiusD1 p.2) (s, t) := by
    unfold heightRadiusD1
    exact continuousAt_snd.neg.div hrT (heightRadius_pos ht).ne'
  have hpDs : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScaleDs p.1 p.2) (s, t) := by
    unfold latitudeAngularScaleDs
    exact (continuousAt_const.mul hdS).mul hrT
  have hpDt : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScaleDt p.1 p.2) (s, t) := by
    unfold latitudeAngularScaleDt latitudeAngularScaleDs
    exact (continuousAt_const.mul hdT).mul hrS
  have hpDst : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScaleDst p.1 p.2) (s, t) := by
    unfold latitudeAngularScaleDst
    exact (continuousAt_const.mul hdS).mul hdT
  change ContinuousAt
    (fun p : ℝ × ℝ ↦
      (γ / 2) * ((γ / 2 - 1) *
        latitudeAngularScale p.1 p.2 ^ (γ / 2 - 2) *
          latitudeAngularScaleDt p.1 p.2 *
            latitudeAngularScaleDs p.1 p.2 +
        latitudeAngularScale p.1 p.2 ^ (γ / 2 - 1) *
          latitudeAngularScaleDst p.1 p.2)) (s, t)
  exact continuousAt_const.mul
    ((((continuousAt_const.mul (hpow (γ / 2 - 2))).mul hpDt).mul hpDs).add
      ((hpow (γ / 2 - 1)).mul hpDst))

theorem continuousAt_neighboringAffineSmoothKernel_joint
    {α H L s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt
      (fun p : ℝ × ℝ ↦ neighboringAffineSmoothKernel α H L p.1 p.2)
      (s, t) := by
  change ContinuousAt
    (fun p : ℝ × ℝ ↦
      (H - L) * latitudePower α p.1 p.2 +
        2 * L * (1 - p.1 * p.2) * latitudePower (α - 2) p.1 p.2)
    (s, t)
  exact
    (continuousAt_const.mul (continuousAt_latitudePower_joint hs ht)).add
      (((continuousAt_const.mul
        (continuousAt_const.sub (continuousAt_fst.mul continuousAt_snd))).mul
          (continuousAt_latitudePower_joint hs ht)))

theorem continuousAt_neighboringAffineSmoothKernelDs_joint
    {α H L s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt
      (fun p : ℝ × ℝ ↦ neighboringAffineSmoothKernelDs α H L p.1 p.2)
      (s, t) := by
  change ContinuousAt
    (fun p : ℝ × ℝ ↦
      (H - L) * latitudePowerDs α p.1 p.2 +
        2 * L * (-p.2 * latitudePower (α - 2) p.1 p.2 +
          (1 - p.1 * p.2) * latitudePowerDs (α - 2) p.1 p.2))
    (s, t)
  exact
    (continuousAt_const.mul (continuousAt_latitudePowerDs_joint hs ht)).add
      (continuousAt_const.mul
        ((continuousAt_snd.neg.mul
          (continuousAt_latitudePower_joint hs ht)).add
          ((continuousAt_const.sub
            (continuousAt_fst.mul continuousAt_snd)).mul
              (continuousAt_latitudePowerDs_joint hs ht))))

theorem continuousAt_neighboringAffineSmoothKernelDst_joint
    {α H L s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt
      (fun p : ℝ × ℝ ↦ neighboringAffineSmoothKernelDst α H L p.1 p.2)
      (s, t) := by
  change ContinuousAt
    (fun p : ℝ × ℝ ↦
      (H - L) * latitudePowerDst α p.1 p.2 +
        2 * L * (-latitudePower (α - 2) p.1 p.2 -
          p.2 * latitudePowerDt (α - 2) p.1 p.2 -
          p.1 * latitudePowerDs (α - 2) p.1 p.2 +
          (1 - p.1 * p.2) * latitudePowerDst (α - 2) p.1 p.2))
    (s, t)
  exact
    (continuousAt_const.mul (continuousAt_latitudePowerDst_joint hs ht)).add
      (continuousAt_const.mul
        ((((continuousAt_latitudePower_joint hs ht).neg.sub
          (continuousAt_snd.mul
            (continuousAt_latitudePowerDt_joint hs ht))).sub
          (continuousAt_fst.mul
            (continuousAt_latitudePowerDs_joint hs ht))).add
          ((continuousAt_const.sub
            (continuousAt_fst.mul continuousAt_snd)).mul
              (continuousAt_latitudePowerDst_joint hs ht))))

theorem continuousOn_neighboringSmoothMixedRemainder_centralRectangle
    {α H L : ℝ}
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦
        neighboringSmoothMixedRemainder α H L
          (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N (k + 1)) p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
  let a := bandBoundaryHeight N (j + 1)
  let c := bandBoundaryHeight N (k + 1)
  have haI : a ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j) :=
    ⟨le_rfl, bandBoundaryHeight_succ_le j⟩
  have hcI : c ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k) :=
    ⟨le_rfl, bandBoundaryHeight_succ_le k⟩
  intro p hp
  have hpc := centralComparable_neighboring_rectangle_chart
    hM hcentral hcomp hneigh hp.1 hp.2
  have hac := centralComparable_neighboring_rectangle_chart
    hM hcentral hcomp hneigh haI hcI
  have hsc := centralComparable_neighboring_rectangle_chart
    hM hcentral hcomp hneigh hp.1 hcI
  have hat := centralComparable_neighboring_rectangle_chart
    hM hcentral hcomp hneigh haI hp.2
  have hKst : ContinuousAt
      (fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernel α H L q.1 q.2) p := by
    simpa using continuousAt_neighboringAffineSmoothKernel_joint
      (α := α) (H := H) (L := L) hpc.1 hpc.2.1
  have hKsc : ContinuousAt
      (fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernel α H L q.1 c) p :=
    ContinuousAt.comp'
      (f := fun q : ℝ × ℝ ↦ (q.1, c))
      (g := fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernel α H L q.1 q.2)
      (continuousAt_neighboringAffineSmoothKernel_joint hsc.1 hsc.2.1)
      (continuousAt_fst.prodMk continuousAt_const)
  have hKdscs : ContinuousAt
      (fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernelDs α H L c q.1) p :=
    ContinuousAt.comp'
      (f := fun q : ℝ × ℝ ↦ (c, q.1))
      (g := fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernelDs α H L q.1 q.2)
      (continuousAt_neighboringAffineSmoothKernelDs_joint hsc.2.1 hsc.1)
      (continuousAt_const.prodMk continuousAt_fst)
  have hKat : ContinuousAt
      (fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernel α H L a q.2) p :=
    ContinuousAt.comp'
      (f := fun q : ℝ × ℝ ↦ (a, q.2))
      (g := fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernel α H L q.1 q.2)
      (continuousAt_neighboringAffineSmoothKernel_joint hat.1 hat.2.1)
      (continuousAt_const.prodMk continuousAt_snd)
  have hKdsa : ContinuousAt
      (fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernelDs α H L a q.2) p :=
    ContinuousAt.comp'
      (f := fun q : ℝ × ℝ ↦ (a, q.2))
      (g := fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernelDs α H L q.1 q.2)
      (continuousAt_neighboringAffineSmoothKernelDs_joint hat.1 hat.2.1)
      (continuousAt_const.prodMk continuousAt_snd)
  have htminus : ContinuousAt (fun q : ℝ × ℝ ↦ q.2 - c) p :=
    continuousAt_snd.sub continuousAt_const
  have hsminus : ContinuousAt (fun q : ℝ × ℝ ↦ q.1 - a) p :=
    continuousAt_fst.sub continuousAt_const
  have hKDstca : ContinuousAt
      (fun _q : ℝ × ℝ ↦ neighboringAffineSmoothKernelDst α H L c a) p :=
    continuousAt_const
  have hE : ContinuousAt (fun q : ℝ × ℝ ↦
      neighboringAffineSmoothKernel α H L q.1 q.2 -
        neighboringAffineSmoothKernel α H L q.1 c -
          (q.2 - c) * neighboringAffineSmoothKernelDs α H L c q.1) p :=
    (hKst.sub hKsc).sub
      (htminus.mul hKdscs)
  have hEa : ContinuousAt (fun q : ℝ × ℝ ↦
      neighboringAffineSmoothKernel α H L a q.2 -
        neighboringAffineSmoothKernel α H L a c -
          (q.2 - c) * neighboringAffineSmoothKernelDs α H L c a) p :=
    (hKat.sub continuousAt_const).sub
      (htminus.mul continuousAt_const)
  have hEDs : ContinuousAt (fun q : ℝ × ℝ ↦
      neighboringAffineSmoothKernelDs α H L a q.2 -
        neighboringAffineSmoothKernelDs α H L a c -
          (q.2 - c) * neighboringAffineSmoothKernelDst α H L c a) p :=
    (hKdsa.sub continuousAt_const).sub
      (htminus.mul hKDstca)
  have hfinal : ContinuousAt (fun q : ℝ × ℝ ↦
      (neighboringAffineSmoothKernel α H L q.1 q.2 -
          neighboringAffineSmoothKernel α H L q.1 c -
            (q.2 - c) * neighboringAffineSmoothKernelDs α H L c q.1) -
        (neighboringAffineSmoothKernel α H L a q.2 -
          neighboringAffineSmoothKernel α H L a c -
            (q.2 - c) * neighboringAffineSmoothKernelDs α H L c a) -
        (q.1 - a) *
          (neighboringAffineSmoothKernelDs α H L a q.2 -
            neighboringAffineSmoothKernelDs α H L a c -
              (q.2 - c) * neighboringAffineSmoothKernelDst α H L c a)) p :=
    (hE.sub hEa).sub
      (hsminus.mul hEDs)
  simpa [a, c, neighboringSmoothMixedRemainder,
    neighboringSmoothRightTaylorError,
    neighboringSmoothRightTaylorErrorDs] using hfinal.continuousWithinAt

/-- Premise-free literal band-pair estimate for the smooth analytic part
of every central neighboring rectangle.  Joint continuity, the Tietze
extension, affine cancellation, and all integrability conditions are
discharged here. -/
theorem abs_bandPairError_neighboringAffineSmoothKernel_central
    {α H L : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k (neighboringAffineSmoothKernel α H L)| ≤
      64 * centralAffineSmoothDssttConstant α H L *
        (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let Is : Set ℝ := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It : Set ℝ := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  let a := bandBoundaryHeight N (j + 1)
  let c := bandBoundaryHeight N (k + 1)
  let R : ℝ → ℝ → ℝ := fun s t ↦
    neighboringSmoothMixedRemainder α H L a c s t
  have hcontR : ContinuousOn (fun p : ℝ × ℝ ↦ R p.1 p.2)
      (Is ×ˢ It) := by
    exact continuousOn_neighboringSmoothMixedRemainder_centralRectangle
      hM hcentral hcomp hneigh
  let fR : C(Is ×ˢ It, ℝ) :=
    ⟨fun p ↦ R p.1.1 p.1.2,
      (continuousOn_iff_continuous_restrict.mp hcontR)⟩
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq
    (isClosed_Icc.prod isClosed_Icc) fR
  have hGeq : ∀ p ∈ Is ×ˢ It, G p = R p.1 p.2 := by
    intro p hp
    exact DFunLike.congr_fun hG (⟨p, hp⟩ : Is ×ˢ It)
  let uRight : ℝ → ℝ := fun s ↦
    neighboringAffineSmoothKernelDs α H L c s
  let vRight : ℝ → ℝ := fun s ↦
    neighboringAffineSmoothKernel α H L s c -
      c * neighboringAffineSmoothKernelDs α H L c s
  let uLeft : ℝ → ℝ := fun t ↦
    neighboringSmoothRightTaylorErrorDs α H L c a t
  let vLeft : ℝ → ℝ := fun t ↦
    neighboringSmoothRightTaylorError α H L c a t -
      a * neighboringSmoothRightTaylorErrorDs α H L c a t
  let Kext : ℝ → ℝ → ℝ := fun s t ↦
    G (s, t) + (uRight s * t + vRight s) +
      (uLeft t * s + vLeft t)
  have hpair :
      bandPairError N j k (neighboringAffineSmoothKernel α H L) =
        bandPairError N j k Kext := by
    apply bandPairError_congr_on_literalRectangle j k
    intro s hs t ht
    rw [neighboringSmoothMixedRemainder_decomposition]
    have hGR : G (s, t) = R s t := hGeq (s, t) ⟨hs, ht⟩
    dsimp [Kext, uRight, vRight, uLeft, vLeft, R, a, c]
    rw [hGR]
  rw [hpair]
  apply abs_bandPairError_le_of_biaffine_mixed_remainder hN j k
    Kext (fun s t ↦ G (s, t)) uRight vRight uLeft vLeft
    (centralAffineSmoothDssttConstant α H L)
  · unfold centralAffineSmoothDssttConstant centralPositivePowerJetConstant
      centralPositivePowerRpowBound centralPowerJetConstant
      centralNegativePowerRpowBound latitudePowerCoefficientEnvelope
      latitudeComparablePowerRpowConstant
    positivity
  · intro s
    exact (G.continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (continuous_bandError_right k G.continuous).intervalIntegrable _ _
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (bandBoundaryHeight_succ_le k)]
    intro t ht
    have haI : a ∈ Is := ⟨le_rfl, bandBoundaryHeight_succ_le j⟩
    have hcI : c ∈ It := ⟨le_rfl, bandBoundaryHeight_succ_le k⟩
    have hat := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh haI ht
    have hca := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh haI hcI
    dsimp [uLeft]
    unfold neighboringSmoothRightTaylorErrorDs
    exact
      (((continuousAt_neighboringAffineSmoothKernelDs_joint
          hat.1 hat.2.1).comp'
          (continuousAt_const.prodMk continuousAt_id)).sub
        continuousAt_const).sub
        ((continuousAt_id.sub continuousAt_const).mul
          continuousAt_const) |>.continuousWithinAt
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (bandBoundaryHeight_succ_le k)]
    intro t ht
    have haI : a ∈ Is := ⟨le_rfl, bandBoundaryHeight_succ_le j⟩
    have hcI : c ∈ It := ⟨le_rfl, bandBoundaryHeight_succ_le k⟩
    have hat := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh haI ht
    dsimp [vLeft]
    unfold neighboringSmoothRightTaylorError
      neighboringSmoothRightTaylorErrorDs
    have hK : ContinuousAt
        (fun y ↦ neighboringAffineSmoothKernel α H L a y) t :=
      (continuousAt_neighboringAffineSmoothKernel_joint
        hat.1 hat.2.1).comp'
        (continuousAt_const.prodMk continuousAt_id)
    have hDs : ContinuousAt
        (fun y ↦ neighboringAffineSmoothKernelDs α H L a y) t :=
      (continuousAt_neighboringAffineSmoothKernelDs_joint
        hat.1 hat.2.1).comp'
        (continuousAt_const.prodMk continuousAt_id)
    have hE : ContinuousAt (fun y ↦
        neighboringAffineSmoothKernel α H L a y -
          neighboringAffineSmoothKernel α H L a c -
            (y - c) * neighboringAffineSmoothKernelDs α H L c a) t :=
      (hK.sub continuousAt_const).sub
        ((continuousAt_id.sub continuousAt_const).mul continuousAt_const)
    have hEDs : ContinuousAt (fun y ↦
        neighboringAffineSmoothKernelDs α H L a y -
          neighboringAffineSmoothKernelDs α H L a c -
            (y - c) * neighboringAffineSmoothKernelDst α H L c a) t :=
      (hDs.sub continuousAt_const).sub
        ((continuousAt_id.sub continuousAt_const).mul continuousAt_const)
    exact (hE.sub (continuousAt_const.mul hEDs)).continuousWithinAt
  · intro s t
    dsimp [Kext]
  · intro s hs t ht
    rw [hGeq (s, t) ⟨hs, ht⟩]
    exact abs_neighboringSmoothMixedRemainder_le_centralRectangle
      hα0 hα2 hM hcentral hcomp hneigh hs ht

end BEMOC
