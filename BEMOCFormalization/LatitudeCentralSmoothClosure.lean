import BEMOCFormalization.LatitudeCentralResonantCoefficient
import BEMOCFormalization.LatitudeComparableSharpJetClosure

/-! Quantitative smooth-kernel closure on central neighboring rectangles. -/

open Set

namespace BEMOC

set_option maxHeartbeats 800000

noncomputable def centralNegativePowerRpowBound (γ : ℝ) : ℝ :=
  ((1 : ℝ) / 2) ^ (γ / 2 - 4)

theorem latitudePowerRpowBound_central_of_nonpos
    {γ s t : ℝ} (hγ : γ ≤ 0)
    (_hs : s ∈ Icc (-1 : ℝ) 1) (_ht : t ∈ Icc (-1 : ℝ) 1)
    (hsfloor : (1 : ℝ) / 2 ≤ heightRadius s)
    (htfloor : (1 : ℝ) / 2 ≤ heightRadius t) :
    LatitudePowerRpowBound γ s t (centralNegativePowerRpowBound γ) := by
  have hp :
      (1 : ℝ) / 2 ≤ latitudeAngularScale s t := by
    convert two_mul_radiusFloor_sq_le_latitudeAngularScale
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2) hsfloor htfloor using 1 ;
      norm_num [inv_pow]
  have hp0 : 0 < latitudeAngularScale s t :=
    (by norm_num : (0 : ℝ) < (1 : ℝ) / 2).trans_le hp
  have hbase0 : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
  have hbase1 : (1 : ℝ) / 2 ≤ 1 := by norm_num
  have hbound (m : ℝ) (hm0 : 0 ≤ m) (hm4 : m ≤ 4) :
      |latitudeAngularScale s t ^ (γ / 2 - m)| ≤
        centralNegativePowerRpowBound γ := by
    rw [abs_of_nonneg (Real.rpow_nonneg hp0.le _)]
    calc
      latitudeAngularScale s t ^ (γ / 2 - m) ≤
          ((1 : ℝ) / 2) ^ (γ / 2 - m) :=
        Real.rpow_le_rpow_of_nonpos hbase0 hp (by linarith)
      _ ≤ ((1 : ℝ) / 2) ^ (γ / 2 - 4) :=
        Real.rpow_le_rpow_of_exponent_ge hbase0 hbase1 (by linarith)
      _ = centralNegativePowerRpowBound γ := rfl
  refine ⟨Real.rpow_nonneg (by norm_num) _, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hbound 0 (by norm_num) (by norm_num)
  · simpa using hbound 1 (by norm_num) (by norm_num)
  · simpa using hbound 2 (by norm_num) (by norm_num)
  · simpa using hbound 3 (by norm_num) (by norm_num)
  · simpa using hbound 4 (by norm_num) (by norm_num)

theorem latitudeAngularDerivativeJetBound_central
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hsfloor : (1 : ℝ) / 2 ≤ heightRadius s)
    (htfloor : (1 : ℝ) / 2 ≤ heightRadius t) :
    LatitudeAngularDerivativeJetBound s t 320 := by
  have hjet := latitudeComparableAngularJetBound hs ht
    (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) hsfloor htfloor
    (by
      have := heightRadius_le_one hs
      norm_num
      linarith)
    (by
      have := heightRadius_le_one ht
      norm_num
      linarith)
  rcases hjet with
    ⟨_, _, hds, hdt, hdss, hdtt, hdst, hdsst, hdstt, hdsstt⟩
  unfold LatitudeAngularDerivativeJetBound
  norm_num at hdss hdtt hdst hdsst hdstt hdsstt
  constructor
  · norm_num
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

noncomputable def centralPowerJetConstant (γ : ℝ) : ℝ :=
  15 * latitudePowerCoefficientEnvelope γ *
    centralNegativePowerRpowBound γ * (320 : ℝ) ^ 4

theorem latitudePowerJetBound_central_of_nonpos
    {γ s t : ℝ} (hγ : γ ≤ 0)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hsfloor : (1 : ℝ) / 2 ≤ heightRadius s)
    (htfloor : (1 : ℝ) / 2 ≤ heightRadius t) :
    LatitudePowerJetBound γ s t (centralPowerJetConstant γ) := by
  exact latitudePowerJetBound_of_coefficient_rpow_angular
    (latitudePowerCoefficientBound_envelope γ)
    (latitudePowerRpowBound_central_of_nonpos hγ hs ht hsfloor htfloor)
    (latitudeAngularDerivativeJetBound_central hs ht hsfloor htfloor)

noncomputable def centralPositivePowerRpowBound (α : ℝ) : ℝ :=
  latitudeComparablePowerRpowConstant α *
    ((1 : ℝ) / 2) ^ (α - 8)

theorem latitudePowerRpowBound_central_of_pos
    {α s t : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hsfloor : (1 : ℝ) / 2 ≤ heightRadius s)
    (htfloor : (1 : ℝ) / 2 ≤ heightRadius t) :
    LatitudePowerRpowBound α s t (centralPositivePowerRpowBound α) := by
  have hjet := latitudeComparableAngularJetBound hs ht
    (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) hsfloor htfloor
    (by
      have := heightRadius_le_one hs
      norm_num
      linarith)
    (by
      have := heightRadius_le_one ht
      norm_num
      linarith)
  have hg := latitudeComparablePowerRpowGradedBound hα0 hα2
    (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) hjet
  rcases hg with ⟨hA, h0, h1, h2, h3, h4⟩
  have hb0 : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
  have hb1 : (1 : ℝ) / 2 ≤ 1 := by norm_num
  have hmono (e : ℝ) (he : α - 8 ≤ e) :
      ((1 : ℝ) / 2) ^ e ≤ ((1 : ℝ) / 2) ^ (α - 8) :=
    Real.rpow_le_rpow_of_exponent_ge hb0 hb1 he
  have hstep {x e : ℝ} (hx :
      |x| ≤ latitudeComparablePowerRpowConstant α *
        ((1 : ℝ) / 2) ^ e) (he : α - 8 ≤ e) :
      |x| ≤ centralPositivePowerRpowBound α := by
    exact hx.trans (mul_le_mul_of_nonneg_left (hmono e he) hA)
  refine ⟨mul_nonneg hA (Real.rpow_nonneg (by norm_num) _),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact hstep h0 (by linarith)
  · exact hstep h1 (by linarith)
  · exact hstep h2 (by linarith)
  · exact hstep h3 (by linarith)
  · exact hstep h4 (by linarith)

noncomputable def centralPositivePowerJetConstant (α : ℝ) : ℝ :=
  15 * latitudePowerCoefficientEnvelope α *
    centralPositivePowerRpowBound α * (320 : ℝ) ^ 4

theorem latitudePowerJetBound_central_of_pos
    {α s t : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hsfloor : (1 : ℝ) / 2 ≤ heightRadius s)
    (htfloor : (1 : ℝ) / 2 ≤ heightRadius t) :
    LatitudePowerJetBound α s t (centralPositivePowerJetConstant α) := by
  exact latitudePowerJetBound_of_coefficient_rpow_angular
    (latitudePowerCoefficientBound_envelope α)
    (latitudePowerRpowBound_central_of_pos hα0 hα2 hs ht hsfloor htfloor)
    (latitudeAngularDerivativeJetBound_central hs ht hsfloor htfloor)

noncomputable def centralAffineSmoothDssttConstant
    (α H L : ℝ) : ℝ :=
  |H - L| * centralPositivePowerJetConstant α +
    20 * |L| * centralPowerJetConstant (α - 2)

theorem abs_neighboringAffineSmoothKernelDsstt_le_centralRectangle
    {α H L : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
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
    |neighboringAffineSmoothKernelDsstt α H L s t| ≤
      centralAffineSmoothDssttConstant α H L := by
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
  have habs :=
    abs_centralComparable_neighboring_rectangle_le hM hcentral hcomp
      hneigh hs ht
  have hrsq := heightRadius_sq hsSphere
  have hrtsq := heightRadius_sq htSphere
  have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
  have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
  have hsSq : s ^ 2 ≤ (1 : ℝ) / 1600 := by
    have hm := mul_self_le_mul_self (abs_nonneg s) habs.1
    norm_num at hm ⊢
    simpa [pow_two] using hm
  have htSq : t ^ 2 ≤ (1 : ℝ) / 1600 := by
    have hm := mul_self_le_mul_self (abs_nonneg t) habs.2
    norm_num at hm ⊢
    simpa [pow_two] using hm
  have hrs : (1 : ℝ) / 2 ≤ heightRadius s := by nlinarith
  have hrt : (1 : ℝ) / 2 ≤ heightRadius t := by nlinarith
  exact abs_neighboringAffineSmoothKernelDsstt_le hsSphere htSphere
    (latitudePowerJetBound_central_of_pos hα0 hα2
      hsSphere htSphere hrs hrt)
    (latitudePowerJetBound_central_of_nonpos
      (by linarith : α - 2 ≤ 0) hsSphere htSphere hrs hrt)

theorem abs_neighboringSmoothMixedRemainder_le_centralRectangle
    {α H L : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
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
    |neighboringSmoothMixedRemainder α H L
        (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N (k + 1)) s t| ≤
      centralAffineSmoothDssttConstant α H L *
        bandWidth N j ^ 2 * bandWidth N k ^ 2 := by
  have hab :
      bandBoundaryHeight N (j + 1) ≤ bandBoundaryHeight N j := by
    have := bandWidth_nonneg (N := N) j
    unfold bandWidth at this
    linarith
  have hcd :
      bandBoundaryHeight N (k + 1) ≤ bandBoundaryHeight N k := by
    have := bandWidth_nonneg (N := N) k
    unfold bandWidth at this
    linarith
  have hC : 0 ≤ centralAffineSmoothDssttConstant α H L := by
    unfold centralAffineSmoothDssttConstant centralPositivePowerJetConstant
      centralPositivePowerRpowBound centralPowerJetConstant
      centralNegativePowerRpowBound latitudePowerCoefficientEnvelope
      latitudeComparablePowerRpowConstant
    positivity
  have hrect :
      ∀ x ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ y ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          x ∈ Ioo (-1 : ℝ) 1 ∧ y ∈ Ioo (-1 : ℝ) 1 := by
    intro x hx y hy
    have hc := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hx hy
    exact ⟨hc.1, hc.2.1⟩
  have h := abs_neighboringSmoothMixedRemainder_le hab hcd hC hrect
    (fun x hx y hy ↦
      abs_neighboringAffineSmoothKernelDsstt_le_centralRectangle
        hα0 hα2 hM hcentral hcomp hneigh hx hy) hs ht
  simpa [bandWidth] using h

/- The joint-continuity/Tietze transfer is continued in the next closure
module; the quantitative pointwise and tensor estimates above are the
stable checkpoint exported here.

theorem continuousAt_neighboringAffineSmoothKernel
    {α H L s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt
      (fun p : ℝ × ℝ ↦ neighboringAffineSmoothKernel α H L p.1 p.2)
      (s, t) := by
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
  unfold neighboringAffineSmoothKernel latitudePower
  fun_prop

theorem continuousAt_neighboringAffineSmoothKernelDs
    {α H L s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt
      (fun p : ℝ × ℝ ↦ neighboringAffineSmoothKernelDs α H L p.1 p.2)
      (s, t) := by
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
  have hrscont : ContinuousAt heightRadius s := by
    unfold heightRadius
    fun_prop
  have hrtcont : ContinuousAt heightRadius t := by
    unfold heightRadius
    fun_prop
  have hrsPair := ContinuousAt.comp'
    (f := fun p : ℝ × ℝ ↦ p.1) (g := heightRadius)
    hrscont continuousAt_fst
  have hrtPair := ContinuousAt.comp'
    (f := fun p : ℝ × ℝ ↦ p.2) (g := heightRadius)
    hrtcont continuousAt_snd
  have hd1s : ContinuousAt
      (fun p : ℝ × ℝ ↦ -p.1 / heightRadius p.1) (s, t) :=
    continuousAt_fst.neg.div hrsPair (heightRadius_pos hs).ne'
  have hpds : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScaleDs p.1 p.2) (s, t) := by
    unfold latitudeAngularScaleDs heightRadiusD1
    exact (continuousAt_const.mul hd1s).mul hrtPair
  have hPds (γ : ℝ) : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudePowerDs γ p.1 p.2) (s, t) := by
    unfold latitudePowerDs
    exact ((continuousAt_const.mul (hpow (γ / 2 - 1))).mul hpds)
  unfold neighboringAffineSmoothKernelDs latitudePower latitudePowerDs
  exact
    (continuousAt_const.mul (hPds α)).add
      (continuousAt_const.mul
        ((continuousAt_snd.neg.mul (hpow ((α - 2) / 2))).add
          ((continuousAt_const.sub (continuousAt_fst.mul continuousAt_snd)).mul
            (hPds (α - 2)))))

theorem continuousAt_neighboringAffineSmoothKernelDst
    {α H L s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt
      (fun p : ℝ × ℝ ↦ neighboringAffineSmoothKernelDst α H L p.1 p.2)
      (s, t) := by
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
  have hrscont : ContinuousAt heightRadius s := by
    unfold heightRadius
    fun_prop
  have hrtcont : ContinuousAt heightRadius t := by
    unfold heightRadius
    fun_prop
  have hrsPair := ContinuousAt.comp'
    (f := fun p : ℝ × ℝ ↦ p.1) (g := heightRadius)
    hrscont continuousAt_fst
  have hrtPair := ContinuousAt.comp'
    (f := fun p : ℝ × ℝ ↦ p.2) (g := heightRadius)
    hrtcont continuousAt_snd
  have hd1s : ContinuousAt
      (fun p : ℝ × ℝ ↦ -p.1 / heightRadius p.1) (s, t) :=
    continuousAt_fst.neg.div hrsPair (heightRadius_pos hs).ne'
  have hd1t : ContinuousAt
      (fun p : ℝ × ℝ ↦ -p.2 / heightRadius p.2) (s, t) :=
    continuousAt_snd.neg.div hrtPair (heightRadius_pos ht).ne'
  have hpds : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScaleDs p.1 p.2) (s, t) := by
    unfold latitudeAngularScaleDs heightRadiusD1
    exact (continuousAt_const.mul hd1s).mul hrtPair
  have hpdt : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScaleDt p.1 p.2) (s, t) := by
    unfold latitudeAngularScaleDt latitudeAngularScaleDs heightRadiusD1
    exact (continuousAt_const.mul hd1t).mul hrsPair
  have hpdst : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudeAngularScaleDst p.1 p.2) (s, t) := by
    unfold latitudeAngularScaleDst
    exact (continuousAt_const.mul hd1s).mul hd1t
  have hPdt (γ : ℝ) : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudePowerDt γ p.1 p.2) (s, t) := by
    unfold latitudePowerDt
    exact ((continuousAt_const.mul (hpow (γ / 2 - 1))).mul hpdt)
  have hPds (γ : ℝ) : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudePowerDs γ p.1 p.2) (s, t) := by
    unfold latitudePowerDs
    exact ((continuousAt_const.mul (hpow (γ / 2 - 1))).mul hpds)
  have hPdst (γ : ℝ) : ContinuousAt
      (fun p : ℝ × ℝ ↦ latitudePowerDst γ p.1 p.2) (s, t) := by
    unfold latitudePowerDst
    exact continuousAt_const.mul
      (((continuousAt_const.mul (hpow (γ / 2 - 2))).mul hpdt |>.mul hpds).add
        ((hpow (γ / 2 - 1)).mul hpdst))
  unfold neighboringAffineSmoothKernelDst latitudePower latitudePowerDs
    latitudePowerDt latitudePowerDst latitudeAngularScaleDs
    latitudeAngularScaleDt latitudeAngularScaleDst heightRadiusD1
  exact
    (continuousAt_const.mul (hPdst α)).add
      (continuousAt_const.mul
        ((((hpow ((α - 2) / 2)).neg.sub
          (continuousAt_snd.mul (hPdt (α - 2)))).sub
          (continuousAt_fst.mul (hPds (α - 2)))).add
          ((continuousAt_const.sub (continuousAt_fst.mul continuousAt_snd)).mul
            (hPdst (α - 2)))))
-/

end BEMOC
