# Calculus of the truncated angular integral

`NearTailIntegralCalculus.lean` supplies the analytic bridge for near and
intermediate comparable latitude bands. It proves the actual truncated
kernel is `C⁴` on a nonpolar height domain with a uniformly positive chord,
and moves its mixed fourth derivative inside the angular integral. No
derivative bound is assumed in this module.

## Compact-interval parameter theorem

For an open set `W` in parameter-angle space,
`integralParameterDomain W a b` consists of the parameter pairs whose
entire angle slice `[a,b]` lies in `W`. Compactness of `[a,b]` makes this
parameter domain open and gives a small closed parameter ball whose product
with `[a,b]` remains in `W`. The joint derivative of the integrand is
bounded on that compact product. This supplies a constant integrable
envelope for mathlib's dominated derivative-under-integral theorem.

`hasFDerivAt_intervalIntegral_param_of_C1` proves the first derivative
formula for a generic Banach-valued integrand. Induction on `n`, using the
joint parameter derivative as the next integrand, proves
`contDiffOn_intervalIntegral_param_of_contDiffOn`: a jointly `Cⁿ`
integrand has a `Cⁿ` fixed-interval parameter integral. The induction
uses no statement about the specific Riesz profile.

The height derivatives are extracted by evaluating the Fréchet derivative
on `(1,0)` and `(0,1)`. Four applications, twice in each height, yield
`mixedFourth_intervalIntegral_eq`. The same continuous fourth-stage
integrand proves `intervalIntegrable_mixedFourth_slice`, needed for absolute
angular-integral estimates. The proof identifies the staged
derivatives both with the integral's `mixedFourth` and with the fixed-angle
integrand's `mixedFourth` using the open-domain identities from `Taylor`.

## Riesz profile specialization

`nearTailSmoothDomain` requires both heights to lie strictly between the
poles and the squared chord to be positive. It is open. On it the two
square-root radius factors are smooth because their arguments are nonzero,
and the positive chord can be raised to the real power `α/2`; hence
`latitudeProfile_joint_contDiffOn` holds for every real `α`.

For `0<r`, `r⁻¹≤π`, an open height set `W` inside the nonpolar square, and
positive chord at every `p∈W` and `θ∈[r⁻¹,π]`, the theorem
`nearTailKernel_contDiffOn_of_chord_pos` proves `C⁴` regularity of the
actual normalized tail average. The theorem
`mixedFourth_nearTailKernel_eq_integral` gives its exact mixed-derivative
formula. The constant normalization `1/π` is handled by
`mixedFourth_const_mul_of_C4`, so the final identity matches the definition
of `nearTailKernel` exactly.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.ComparableNearBlocks

/-! Smooth differentiation under a fixed compact angular integral. -/

open MeasureTheory Set Filter Metric
open scoped Interval Topology

namespace BEMOC.Definitive

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

/-- Parameters whose entire angular integration slice lies in an open domain. -/
def integralParameterDomain {E : Type*} (W : Set (E × ℝ)) (a b : ℝ) : Set E :=
  {x | ∀ θ ∈ Icc a b, (x, θ) ∈ W}

theorem isOpen_integralParameterDomain
    {E : Type*} [MetricSpace E] {W : Set (E × ℝ)}
    (hW : IsOpen W) (a b : ℝ) :
    IsOpen (integralParameterDomain W a b) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hprod : W ∈ 𝓝 x ×ˢ 𝓝ˢ (Icc a b) :=
    isCompact_Icc.mem_prod_nhdsSet_of_forall (by
      intro θ hθ
      rw [← nhds_prod_eq]
      exact hW.mem_nhds (hx θ hθ))
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp hprod
  apply Filter.mem_of_superset hu
  intro y hy θ hθ
  exact huv ⟨hy, (subset_of_mem_nhdsSet hv) hθ⟩

theorem exists_closedBall_integral_slice_subset
    {E : Type*} [MetricSpace E]
    {W : Set (E × ℝ)} (hW : IsOpen W)
    {x : E} {a b : ℝ}
    (hx : x ∈ integralParameterDomain W a b) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.closedBall x ε ×ˢ Icc a b ⊆ W := by
  have hprod : W ∈ 𝓝 x ×ˢ 𝓝ˢ (Icc a b) :=
    isCompact_Icc.mem_prod_nhdsSet_of_forall (by
      intro θ hθ
      rw [← nhds_prod_eq]
      exact hW.mem_nhds (hx θ hθ))
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp hprod
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨ε / 2, by positivity, ?_⟩
  have hclosed : Metric.closedBall x (ε / 2) ⊆ u :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεsub
  exact (Set.prod_mono hclosed (subset_of_mem_nhdsSet hv)).trans huv

/-- A jointly continuous integrand has a continuous fixed-interval parameter
integral on the open set where every angular slice stays in its domain. -/
theorem continuousOn_intervalIntegral_param_of_continuousOn
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {F : (ℝ × ℝ) × ℝ → H} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) (hF : ContinuousOn F W)
    {a b : ℝ} (hab : a ≤ b) :
    ContinuousOn
      (fun p : ℝ × ℝ => ∫ θ in a..b, F (p, θ))
      (integralParameterDomain W a b) := by
  intro p hp
  obtain ⟨ε, hε, hsub⟩ :=
    exists_closedBall_integral_slice_subset hW hp
  have hK : IsCompact (Metric.closedBall p ε ×ˢ Icc a b) :=
    (isCompact_closedBall p ε).prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.bddAbove_image ((hF.mono hsub).norm)
  have hbound : ∀ q ∈ Metric.closedBall p ε, ∀ θ ∈ Icc a b,
      ‖F (q, θ)‖ ≤ M := by
    intro q hq θ hθ
    exact hM (mem_image_of_mem _ ⟨hq, hθ⟩)
  have hmeas : ∀ᶠ q in 𝓝 p,
      AEStronglyMeasurable (fun θ => F (q, θ))
        (volume.restrict (Ι a b)) := by
    filter_upwards [Metric.ball_mem_nhds p hε] with q hq
    have hqc : q ∈ Metric.closedBall p ε := Metric.ball_subset_closedBall hq
    have hcont : ContinuousOn (fun θ => F (q, θ)) (Icc a b) := by
      apply hF.comp (by fun_prop)
      intro θ hθ
      exact hsub ⟨hqc, hθ⟩
    exact (hcont.mono (by
      simpa [uIoc_of_le hab] using Ioc_subset_Icc_self : Ι a b ⊆ Icc a b)).aestronglyMeasurable
      measurableSet_uIoc
  have hbound' : ∀ᶠ q in 𝓝 p, ∀ᵐ θ ∂(volume : Measure ℝ),
      θ ∈ Ι a b → ‖F (q, θ)‖ ≤ M := by
    filter_upwards [Metric.ball_mem_nhds p hε] with q hq
    filter_upwards [] with θ
    intro hθ
    exact hbound q (Metric.ball_subset_closedBall hq) θ
      ((by simpa [uIoc_of_le hab] using Ioc_subset_Icc_self : Ι a b ⊆ Icc a b) hθ)
  have hcont : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι a b →
      ContinuousAt (fun q => F (q, θ)) p := by
    filter_upwards [] with θ
    intro hθ
    have hθI : θ ∈ Icc a b :=
      (by simpa [uIoc_of_le hab] using Ioc_subset_Icc_self : Ι a b ⊆ Icc a b) hθ
    have hFp : ContinuousAt F (p, θ) :=
      hF.continuousAt (hW.mem_nhds (hp θ hθI))
    have hmap : ContinuousAt (fun q : ℝ × ℝ => (q, θ)) p :=
      continuousAt_id.prodMk continuousAt_const
    exact ContinuousAt.comp_of_eq (f := fun q : ℝ × ℝ => (q, θ))
      hFp hmap rfl
  have hci := intervalIntegral.continuousAt_of_dominated_interval
    hmeas hbound' (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => M) volume a b) hcont
  exact hci.continuousWithinAt

/-- The derivative of the integrand in the two height parameters. -/
noncomputable def integralParamFDeriv
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : (ℝ × ℝ) × ℝ → H) (z : (ℝ × ℝ) × ℝ) :
    (ℝ × ℝ) →L[ℝ] H :=
  (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ)

/-- Differentiation under a compact angular integral when the full integrand
is jointly `C¹` on an open neighborhood of the parameter slice. -/
theorem hasFDerivAt_intervalIntegral_param_of_C1
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {F : (ℝ × ℝ) × ℝ → H} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W)
    {a b : ℝ} (hab : a ≤ b)
    {p : ℝ × ℝ} (hp : p ∈ integralParameterDomain W a b) :
    HasFDerivAt
      (fun q : ℝ × ℝ => ∫ θ in a..b, F (q, θ))
      (∫ θ in a..b, integralParamFDeriv F (p, θ)) p := by
  obtain ⟨ε, hε, hsub⟩ :=
    exists_closedBall_integral_slice_subset hW hp
  have hK : IsCompact (Metric.closedBall p ε ×ˢ Icc a b) :=
    (isCompact_closedBall p ε).prod isCompact_Icc
  have hpart : ContinuousOn (integralParamFDeriv F) W := by
    unfold integralParamFDeriv
    have hfd : ContDiffOn ℝ 0 (fderiv ℝ F) W :=
      hF.fderiv_of_isOpen hW (by norm_num)
    exact (hfd.clm_comp contDiffOn_const).continuousOn
  obtain ⟨M, hM⟩ := hK.bddAbove_image ((hpart.mono hsub).norm)
  have hbound : ∀ q ∈ Metric.closedBall p ε, ∀ θ ∈ Icc a b,
      ‖integralParamFDeriv F (q, θ)‖ ≤ M := by
    intro q hq θ hθ
    exact hM (mem_image_of_mem _ ⟨hq, hθ⟩)
  have hcont : ∀ q ∈ Metric.closedBall p ε,
      ContinuousOn (fun θ => F (q, θ)) (Icc a b) := by
    intro q hq
    apply hF.continuousOn.comp (by fun_prop)
    intro θ hθ
    exact hsub ⟨hq, hθ⟩
  have hcont' : ∀ q ∈ Metric.closedBall p ε,
      ContinuousOn (fun θ => integralParamFDeriv F (q, θ)) (Icc a b) := by
    intro q hq
    apply hpart.comp (by fun_prop)
    intro θ hθ
    exact hsub ⟨hq, hθ⟩
  have hpball : p ∈ Metric.closedBall p ε := Metric.mem_closedBall_self hε.le
  have hmeas : ∀ᶠ q in 𝓝 p,
      AEStronglyMeasurable (fun θ => F (q, θ))
        (volume.restrict (Ι a b)) := by
    filter_upwards [Metric.ball_mem_nhds p hε] with q hq
    exact ((hcont q (Metric.ball_subset_closedBall hq)).mono (by
      simpa [uIoc_of_le hab] using Ioc_subset_Icc_self : Ι a b ⊆ Icc a b)).aestronglyMeasurable
      measurableSet_uIoc
  have hint : IntervalIntegrable (fun θ => F (p, θ)) volume a b :=
    (hcont p hpball).intervalIntegrable_of_Icc hab
  have hmeas' : AEStronglyMeasurable
      (fun θ => integralParamFDeriv F (p, θ))
      (volume.restrict (Ι a b)) :=
    ((hcont' p hpball).mono (by
      simpa [uIoc_of_le hab] using Ioc_subset_Icc_self : Ι a b ⊆ Icc a b)).aestronglyMeasurable
      measurableSet_uIoc
  have hbound' : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι a b →
      ∀ q ∈ Metric.ball p ε, ‖integralParamFDeriv F (q, θ)‖ ≤ M := by
    filter_upwards [] with θ
    intro hθ q hq
    exact hbound q (Metric.ball_subset_closedBall hq) θ
      ((by simpa [uIoc_of_le hab] using Ioc_subset_Icc_self : Ι a b ⊆ Icc a b) hθ)
  have hdiff : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι a b →
      ∀ q ∈ Metric.ball p ε,
        HasFDerivAt (fun y : ℝ × ℝ => F (y, θ))
          (integralParamFDeriv F (q, θ)) q := by
    filter_upwards [] with θ
    intro hθ q hq
    have hqθ : (q, θ) ∈ W := hsub ⟨Metric.ball_subset_closedBall hq,
      ((by simpa [uIoc_of_le hab] using Ioc_subset_Icc_self : Ι a b ⊆ Icc a b) hθ)⟩
    have hdiffF : DifferentiableAt ℝ F (q, θ) :=
      (hF.contDiffAt (hW.mem_nhds hqθ)).differentiableAt (by decide)
    exact hdiffF.hasFDerivAt.comp q (hasFDerivAt_prodMk_left q θ)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q θ => F (q, θ))
    (F' := fun q θ => integralParamFDeriv F (q, θ))
    (bound := fun _ => M) (μ := volume) (a := a) (b := b)
    (x₀ := p) hε hmeas hint hmeas' hbound'
    intervalIntegrable_const hdiff

/-- Finite-order smoothness of a fixed compact interval integral follows
from joint finite-order smoothness of its integrand. -/
theorem contDiffOn_intervalIntegral_param_of_contDiffOn
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (n : ℕ) {F : (ℝ × ℝ) × ℝ → H} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ n F W)
    {a b : ℝ} (hab : a ≤ b) :
    ContDiffOn ℝ n
      (fun p : ℝ × ℝ => ∫ θ in a..b, F (p, θ))
      (integralParameterDomain W a b) := by
  induction n generalizing H F with
  | zero =>
      exact contDiffOn_zero.mpr
        (continuousOn_intervalIntegral_param_of_continuousOn
          hW (contDiffOn_zero.mp hF) hab)
  | succ n ih =>
      let G : (ℝ × ℝ) × ℝ → (ℝ × ℝ) →L[ℝ] H :=
        integralParamFDeriv F
      have hG : ContDiffOn ℝ n G W := by
        have hfd : ContDiffOn ℝ n (fderiv ℝ F) W :=
          hF.fderiv_of_isOpen hW (by norm_num)
        exact hfd.clm_comp contDiffOn_const
      have hGI : ContDiffOn ℝ n
          (fun p : ℝ × ℝ => ∫ θ in a..b, G (p, θ))
          (integralParameterDomain W a b) :=
        ih (H := (ℝ × ℝ) →L[ℝ] H) (F := G) hG
      let I : ℝ × ℝ → H := fun p => ∫ θ in a..b, F (p, θ)
      have hdiff : DifferentiableOn ℝ I (integralParameterDomain W a b) := by
        intro p hp
        exact (hasFDerivAt_intervalIntegral_param_of_C1 hW
          (hF.of_le (by norm_num)) hab hp).differentiableAt.differentiableWithinAt
      have hfdEq : ∀ p ∈ integralParameterDomain W a b,
          fderiv ℝ I p = ∫ θ in a..b, G (p, θ) := by
        intro p hp
        exact (hasFDerivAt_intervalIntegral_param_of_C1 hW
          (hF.of_le (by norm_num)) hab hp).fderiv
      have hfdSmooth : ContDiffOn ℝ n (fderiv ℝ I)
          (integralParameterDomain W a b) :=
        hGI.congr (fun p hp => hfdEq p hp)
      exact (contDiffOn_succ_iff_fderiv_of_isOpen
        (isOpen_integralParameterDomain hW a b)).mpr
          ⟨hdiff, by simp, hfdSmooth⟩

/-- Joint first derivative of an angular integrand in its first height. -/
noncomputable def integralParamPartialFirst
    (F : (ℝ × ℝ) × ℝ → ℝ) (z : (ℝ × ℝ) × ℝ) : ℝ :=
  integralParamFDeriv F z (1, 0)

/-- Joint first derivative of an angular integrand in its second height. -/
noncomputable def integralParamPartialSecond
    (F : (ℝ × ℝ) × ℝ → ℝ) (z : (ℝ × ℝ) × ℝ) : ℝ :=
  integralParamFDeriv F z (0, 1)

theorem contDiffOn_integralParamPartialFirst
    {F : (ℝ × ℝ) × ℝ → ℝ} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) {n : ℕ} (hF : ContDiffOn ℝ (n + 1) F W) :
    ContDiffOn ℝ n (integralParamPartialFirst F) W := by
  unfold integralParamPartialFirst integralParamFDeriv
  have hfd : ContDiffOn ℝ n (fderiv ℝ F) W :=
    hF.fderiv_of_isOpen hW (by norm_num)
  exact (hfd.clm_comp contDiffOn_const).clm_apply contDiffOn_const

theorem contDiffOn_integralParamPartialSecond
    {F : (ℝ × ℝ) × ℝ → ℝ} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) {n : ℕ} (hF : ContDiffOn ℝ (n + 1) F W) :
    ContDiffOn ℝ n (integralParamPartialSecond F) W := by
  unfold integralParamPartialSecond integralParamFDeriv
  have hfd : ContDiffOn ℝ n (fderiv ℝ F) W :=
    hF.fderiv_of_isOpen hW (by norm_num)
  exact (hfd.clm_comp contDiffOn_const).clm_apply contDiffOn_const

theorem partialFirst_intervalIntegral_eq
    {F : (ℝ × ℝ) × ℝ → ℝ} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W)
    {a b : ℝ} (hab : a ≤ b)
    {p : ℝ × ℝ} (hp : p ∈ integralParameterDomain W a b) :
    partialFirst (fun q : ℝ × ℝ => ∫ θ in a..b, F (q, θ)) p =
      ∫ θ in a..b, integralParamPartialFirst F (p, θ) := by
  have hder := (hasFDerivAt_intervalIntegral_param_of_C1 hW hF hab hp).fderiv
  have hint : IntervalIntegrable
      (fun θ => integralParamFDeriv F (p, θ)) volume a b := by
    have hcont : ContinuousOn
        (fun θ => integralParamFDeriv F (p, θ)) (Icc a b) := by
      have hpart : ContinuousOn (integralParamFDeriv F) W := by
        unfold integralParamFDeriv
        have hfd : ContDiffOn ℝ 0 (fderiv ℝ F) W :=
          hF.fderiv_of_isOpen hW (by norm_num)
        exact (hfd.clm_comp contDiffOn_const).continuousOn
      apply hpart.comp (by fun_prop)
      intro θ hθ
      exact hp θ hθ
    exact hcont.intervalIntegrable_of_Icc hab
  rw [partialFirst, hder,
    ContinuousLinearMap.intervalIntegral_apply hint ((1, 0) : ℝ × ℝ)]
  rfl

theorem partialSecond_intervalIntegral_eq
    {F : (ℝ × ℝ) × ℝ → ℝ} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W)
    {a b : ℝ} (hab : a ≤ b)
    {p : ℝ × ℝ} (hp : p ∈ integralParameterDomain W a b) :
    partialSecond (fun q : ℝ × ℝ => ∫ θ in a..b, F (q, θ)) p =
      ∫ θ in a..b, integralParamPartialSecond F (p, θ) := by
  have hder := (hasFDerivAt_intervalIntegral_param_of_C1 hW hF hab hp).fderiv
  have hint : IntervalIntegrable
      (fun θ => integralParamFDeriv F (p, θ)) volume a b := by
    have hcont : ContinuousOn
        (fun θ => integralParamFDeriv F (p, θ)) (Icc a b) := by
      have hpart : ContinuousOn (integralParamFDeriv F) W := by
        unfold integralParamFDeriv
        have hfd : ContDiffOn ℝ 0 (fderiv ℝ F) W :=
          hF.fderiv_of_isOpen hW (by norm_num)
        exact (hfd.clm_comp contDiffOn_const).continuousOn
      apply hpart.comp (by fun_prop)
      intro θ hθ
      exact hp θ hθ
    exact hcont.intervalIntegrable_of_Icc hab
  rw [partialSecond, hder,
    ContinuousLinearMap.intervalIntegral_apply hint ((0, 1) : ℝ × ℝ)]
  rfl

/-- Four height derivatives pass through a fixed compact angular integral.
The joint derivatives are taken second-height twice, then first-height twice. -/
theorem partialFirstTwice_partialSecondTwice_intervalIntegral_eq
    {F : (ℝ × ℝ) × ℝ → ℝ} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 4 F W)
    {a b : ℝ} (hab : a ≤ b)
    {p : ℝ × ℝ} (hp : p ∈ integralParameterDomain W a b) :
    partialFirstTwice (partialSecondTwice
      (fun q : ℝ × ℝ => ∫ θ in a..b, F (q, θ))) p =
      ∫ θ in a..b,
        integralParamPartialFirst
          (integralParamPartialFirst
            (integralParamPartialSecond
              (integralParamPartialSecond F))) (p, θ) := by
  let P := integralParameterDomain W a b
  have hP : IsOpen P := isOpen_integralParameterDomain hW a b
  let F₁ := integralParamPartialSecond F
  let F₂ := integralParamPartialSecond F₁
  let F₃ := integralParamPartialFirst F₂
  let F₄ := integralParamPartialFirst F₃
  let I₀ : ℝ × ℝ → ℝ := fun q => ∫ θ in a..b, F (q, θ)
  let I₁ : ℝ × ℝ → ℝ := fun q => ∫ θ in a..b, F₁ (q, θ)
  let I₂ : ℝ × ℝ → ℝ := fun q => ∫ θ in a..b, F₂ (q, θ)
  let I₃ : ℝ × ℝ → ℝ := fun q => ∫ θ in a..b, F₃ (q, θ)
  let I₄ : ℝ × ℝ → ℝ := fun q => ∫ θ in a..b, F₄ (q, θ)
  have hF₁ : ContDiffOn ℝ 3 F₁ W :=
    contDiffOn_integralParamPartialSecond hW (by simpa using hF)
  have hF₂ : ContDiffOn ℝ 2 F₂ W :=
    contDiffOn_integralParamPartialSecond hW (by simpa using hF₁)
  have hF₃ : ContDiffOn ℝ 1 F₃ W :=
    contDiffOn_integralParamPartialFirst hW (by simpa using hF₂)
  have hEq₁ : EqOn (partialSecond I₀) I₁ P := by
    intro q hq
    exact partialSecond_intervalIntegral_eq hW
      (hF.of_le (by norm_num)) hab hq
  have hEq₂ : EqOn (partialSecondTwice I₀) I₂ P := by
    intro q hq
    calc
      partialSecondTwice I₀ q = partialSecond I₁ q := by
        exact partialSecond_congr_on_open hP hEq₁ q hq
      _ = I₂ q := partialSecond_intervalIntegral_eq hW
        (hF₁.of_le (by norm_num)) hab hq
  have hEq₃ : EqOn (partialFirst (partialSecondTwice I₀)) I₃ P := by
    intro q hq
    calc
      partialFirst (partialSecondTwice I₀) q = partialFirst I₂ q :=
        partialFirst_congr_on_open hP hEq₂ q hq
      _ = I₃ q := partialFirst_intervalIntegral_eq hW
        (hF₂.of_le (by norm_num)) hab hq
  have hEq₄ : EqOn (partialFirstTwice (partialSecondTwice I₀)) I₄ P := by
    intro q hq
    calc
      partialFirstTwice (partialSecondTwice I₀) q = partialFirst I₃ q := by
        exact partialFirst_congr_on_open hP hEq₃ q hq
      _ = I₄ q := partialFirst_intervalIntegral_eq hW hF₃ hab hq
  exact hEq₄ hp

theorem integralParamPartialFirst_eq_slice
    {F : (ℝ × ℝ) × ℝ → ℝ} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W)
    {p : ℝ × ℝ} {θ : ℝ} (hp : (p, θ) ∈ W) :
    integralParamPartialFirst F (p, θ) =
      partialFirst (fun q : ℝ × ℝ => F (q, θ)) p := by
  have hdiffF : DifferentiableAt ℝ F (p, θ) :=
    (hF.contDiffAt (hW.mem_nhds hp)).differentiableAt (by decide)
  have hslice : HasFDerivAt (fun q : ℝ × ℝ => F (q, θ))
      (integralParamFDeriv F (p, θ)) p :=
    hdiffF.hasFDerivAt.comp p (hasFDerivAt_prodMk_left p θ)
  unfold integralParamPartialFirst partialFirst
  rw [hslice.fderiv]

theorem integralParamPartialSecond_eq_slice
    {F : (ℝ × ℝ) × ℝ → ℝ} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W)
    {p : ℝ × ℝ} {θ : ℝ} (hp : (p, θ) ∈ W) :
    integralParamPartialSecond F (p, θ) =
      partialSecond (fun q : ℝ × ℝ => F (q, θ)) p := by
  have hdiffF : DifferentiableAt ℝ F (p, θ) :=
    (hF.contDiffAt (hW.mem_nhds hp)).differentiableAt (by decide)
  have hslice : HasFDerivAt (fun q : ℝ × ℝ => F (q, θ))
      (integralParamFDeriv F (p, θ)) p :=
    hdiffF.hasFDerivAt.comp p (hasFDerivAt_prodMk_left p θ)
  unfold integralParamPartialSecond partialSecond
  rw [hslice.fderiv]

/-- The four joint parameter derivatives coincide with the manuscript's
mixed derivative of each fixed-angle profile. -/
theorem integralParamFourth_eq_mixedFourth_slice
    {F : (ℝ × ℝ) × ℝ → ℝ} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 4 F W)
    {p : ℝ × ℝ} {θ : ℝ} (hp : (p, θ) ∈ W) :
    integralParamPartialFirst
      (integralParamPartialFirst
        (integralParamPartialSecond
          (integralParamPartialSecond F))) (p, θ) =
      mixedFourth (fun q : ℝ × ℝ => F (q, θ)) p.1 p.2 := by
  let S : Set (ℝ × ℝ) := {q | (q, θ) ∈ W}
  have hS : IsOpen S := hW.preimage (by fun_prop)
  let F₀ : ℝ × ℝ → ℝ := fun q => F (q, θ)
  let F₁ := integralParamPartialSecond F
  let F₂ := integralParamPartialSecond F₁
  let F₃ := integralParamPartialFirst F₂
  let F₄ := integralParamPartialFirst F₃
  let G₁ : ℝ × ℝ → ℝ := fun q => F₁ (q, θ)
  let G₂ : ℝ × ℝ → ℝ := fun q => F₂ (q, θ)
  let G₃ : ℝ × ℝ → ℝ := fun q => F₃ (q, θ)
  let G₄ : ℝ × ℝ → ℝ := fun q => F₄ (q, θ)
  have hF₁ : ContDiffOn ℝ 3 F₁ W :=
    contDiffOn_integralParamPartialSecond hW (by simpa using hF)
  have hF₂ : ContDiffOn ℝ 2 F₂ W :=
    contDiffOn_integralParamPartialSecond hW (by simpa using hF₁)
  have hF₃ : ContDiffOn ℝ 1 F₃ W :=
    contDiffOn_integralParamPartialFirst hW (by simpa using hF₂)
  have hG₀ : ContDiffOn ℝ 4 F₀ S := by
    apply hF.comp (contDiffOn_id.prodMk contDiffOn_const)
    intro q hq
    exact hq
  have hEq₁ : EqOn G₁ (partialSecond F₀) S := by
    intro q hq
    exact integralParamPartialSecond_eq_slice hW
      (hF.of_le (by norm_num)) hq
  have hEq₂ : EqOn G₂ (partialSecondTwice F₀) S := by
    intro q hq
    calc
      G₂ q = partialSecond G₁ q :=
        integralParamPartialSecond_eq_slice hW
          (hF₁.of_le (by norm_num)) hq
      _ = partialSecondTwice F₀ q := by
        exact partialSecond_congr_on_open hS hEq₁ q hq
  have hEq₃ : EqOn G₃ (partialFirst (partialSecondTwice F₀)) S := by
    intro q hq
    calc
      G₃ q = partialFirst G₂ q :=
        integralParamPartialFirst_eq_slice hW
          (hF₂.of_le (by norm_num)) hq
      _ = partialFirst (partialSecondTwice F₀) q :=
        partialFirst_congr_on_open hS hEq₂ q hq
  have hEq₄ : EqOn G₄ (partialFirstTwice (partialSecondTwice F₀)) S := by
    intro q hq
    calc
      G₄ q = partialFirst G₃ q :=
        integralParamPartialFirst_eq_slice hW hF₃ hq
      _ = partialFirstTwice (partialSecondTwice F₀) q :=
        partialFirst_congr_on_open hS hEq₃ q hq
  rw [mixedFourth_eq_partialFirstTwice_partialSecondTwice hS hG₀ p.1 p.2 hp]
  exact hEq₄ hp

/-- Exact fourth mixed-derivative interchange for a jointly smooth angular
integrand on an open neighborhood of the full compact angular slice. -/
theorem mixedFourth_intervalIntegral_eq
    {F : (ℝ × ℝ) × ℝ → ℝ} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 4 F W)
    {a b : ℝ} (hab : a ≤ b)
    {p : ℝ × ℝ} (hp : p ∈ integralParameterDomain W a b) :
    mixedFourth
      (fun q : ℝ × ℝ => ∫ θ in a..b, F (q, θ)) p.1 p.2 =
      ∫ θ in a..b,
        mixedFourth (fun q : ℝ × ℝ => F (q, θ)) p.1 p.2 := by
  have hP : IsOpen (integralParameterDomain W a b) :=
    isOpen_integralParameterDomain hW a b
  have hI : ContDiffOn ℝ 4
      (fun q : ℝ × ℝ => ∫ θ in a..b, F (q, θ))
      (integralParameterDomain W a b) :=
    contDiffOn_intervalIntegral_param_of_contDiffOn 4 hW hF hab
  rw [mixedFourth_eq_partialFirstTwice_partialSecondTwice hP hI p.1 p.2 hp,
    partialFirstTwice_partialSecondTwice_intervalIntegral_eq hW hF hab hp]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hθI : θ ∈ Icc a b := by simpa [uIcc_of_le hab] using hθ
  exact integralParamFourth_eq_mixedFourth_slice hW hF (hp θ hθI)

/-- The fixed-angle mixed fourth derivative is interval integrable whenever
the joint profile is `C⁴` around the compact angular slice. -/
theorem intervalIntegrable_mixedFourth_slice
    {F : (ℝ × ℝ) × ℝ → ℝ} {W : Set ((ℝ × ℝ) × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 4 F W)
    {a b : ℝ} (hab : a ≤ b)
    {p : ℝ × ℝ} (hp : p ∈ integralParameterDomain W a b) :
    IntervalIntegrable
      (fun θ => mixedFourth (fun q : ℝ × ℝ => F (q, θ)) p.1 p.2)
      volume a b := by
  let F₁ := integralParamPartialSecond F
  let F₂ := integralParamPartialSecond F₁
  let F₃ := integralParamPartialFirst F₂
  let F₄ := integralParamPartialFirst F₃
  have hF₁ : ContDiffOn ℝ 3 F₁ W :=
    contDiffOn_integralParamPartialSecond hW (by simpa using hF)
  have hF₂ : ContDiffOn ℝ 2 F₂ W :=
    contDiffOn_integralParamPartialSecond hW (by simpa using hF₁)
  have hF₃ : ContDiffOn ℝ 1 F₃ W :=
    contDiffOn_integralParamPartialFirst hW (by simpa using hF₂)
  have hF₄ : ContDiffOn ℝ 0 F₄ W :=
    contDiffOn_integralParamPartialFirst hW (by simpa using hF₃)
  have hcont₄ : ContinuousOn (fun θ => F₄ (p, θ)) (Icc a b) := by
    apply (contDiffOn_zero.mp hF₄).comp (by fun_prop)
    intro θ hθ
    exact hp θ hθ
  have hcont : ContinuousOn
      (fun θ => mixedFourth (fun q : ℝ × ℝ => F (q, θ)) p.1 p.2)
      (Icc a b) := by
    apply hcont₄.congr
    intro θ hθ
    exact (integralParamFourth_eq_mixedFourth_slice hW hF (hp θ hθ)).symm
  exact hcont.intervalIntegrable_of_Icc hab

/-- The joint nonpolar, positive-chord domain for the height-angle profile. -/
def nearTailSmoothDomain : Set ((ℝ × ℝ) × ℝ) :=
  {z | z.1.1 ∈ Ioo (-1 : ℝ) 1 ∧
    z.1.2 ∈ Ioo (-1 : ℝ) 1 ∧
    0 < 2 - 2 * z.1.1 * z.1.2 -
      2 * Real.sqrt (1 - z.1.1 ^ 2) *
        Real.sqrt (1 - z.1.2 ^ 2) * Real.cos z.2}

theorem isOpen_nearTailSmoothDomain : IsOpen nearTailSmoothDomain := by
  have hs : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1.1) := by fun_prop
  have ht : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1.2) := by fun_prop
  have hc : Continuous (fun z : (ℝ × ℝ) × ℝ =>
      2 - 2 * z.1.1 * z.1.2 -
        2 * Real.sqrt (1 - z.1.1 ^ 2) *
          Real.sqrt (1 - z.1.2 ^ 2) * Real.cos z.2) := by fun_prop
  have hopen := (((isOpen_Ioo : IsOpen (Ioo (-1 : ℝ) 1)).preimage hs).inter
    ((isOpen_Ioo : IsOpen (Ioo (-1 : ℝ) 1)).preimage ht)).inter
      (isOpen_lt (continuous_const :
        Continuous (fun _ : (ℝ × ℝ) × ℝ => (0 : ℝ))) hc)
  simpa only [nearTailSmoothDomain, Set.preimage, Set.inter_def,
    Set.mem_setOf_eq, and_assoc] using hopen

theorem latitudeProfile_joint_contDiffOn (α : ℝ) :
    ContDiffOn ℝ 4
      (fun z : (ℝ × ℝ) × ℝ => latitudeProfile α z.1.1 z.1.2 z.2)
      nearTailSmoothDomain := by
  apply (isOpen_nearTailSmoothDomain.contDiffOn_iff).2
  intro z hz
  have hs : z.1.1 ∈ Ioo (-1 : ℝ) 1 := hz.1
  have ht : z.1.2 ∈ Ioo (-1 : ℝ) 1 := hz.2.1
  have hchord : 0 < 2 - 2 * z.1.1 * z.1.2 -
      2 * Real.sqrt (1 - z.1.1 ^ 2) *
        Real.sqrt (1 - z.1.2 ^ 2) * Real.cos z.2 := hz.2.2
  have hsc : ContDiffAt ℝ 4 (fun w : (ℝ × ℝ) × ℝ => w.1.1) z := by fun_prop
  have htc : ContDiffAt ℝ 4 (fun w : (ℝ × ℝ) × ℝ => w.1.2) z := by fun_prop
  have hθc : ContDiffAt ℝ 4 (fun w : (ℝ × ℝ) × ℝ => w.2) z := by fun_prop
  have hsr : ContDiffAt ℝ 4
      (fun w : (ℝ × ℝ) × ℝ => Real.sqrt (1 - w.1.1 ^ 2)) z :=
    (contDiffAt_const.sub (hsc.pow 2)).sqrt (by nlinarith [hs.1, hs.2])
  have htr : ContDiffAt ℝ 4
      (fun w : (ℝ × ℝ) × ℝ => Real.sqrt (1 - w.1.2 ^ 2)) z :=
    (contDiffAt_const.sub (htc.pow 2)).sqrt (by nlinarith [ht.1, ht.2])
  have hcos : ContDiffAt ℝ 4
      (fun w : (ℝ × ℝ) × ℝ => Real.cos w.2) z :=
    Real.contDiff_cos.contDiffAt.comp z hθc
  have hterm : ContDiffAt ℝ 4
      (fun w : (ℝ × ℝ) × ℝ =>
        2 * Real.sqrt (1 - w.1.1 ^ 2) *
          Real.sqrt (1 - w.1.2 ^ 2) * Real.cos w.2) z :=
    (((contDiffAt_const.mul hsr).mul htr).mul hcos)
  have hbase : ContDiffAt ℝ 4
      (fun w : (ℝ × ℝ) × ℝ =>
        2 - 2 * w.1.1 * w.1.2 -
          2 * Real.sqrt (1 - w.1.1 ^ 2) *
            Real.sqrt (1 - w.1.2 ^ 2) * Real.cos w.2) z :=
    (contDiffAt_const.sub ((contDiffAt_const.mul hsc).mul htc)).sub hterm
  change ContDiffAt ℝ 4
    (fun w : (ℝ × ℝ) × ℝ =>
      (2 - 2 * w.1.1 * w.1.2 -
        2 * Real.sqrt (1 - w.1.1 ^ 2) *
          Real.sqrt (1 - w.1.2 ^ 2) * Real.cos w.2) ^ (α / 2)) z
  exact hbase.rpow_const_of_ne hchord.ne'

/-- The truncated angular average is `C⁴` on every open nonpolar height
domain whose full angular slices have positive chord. -/
theorem nearTailKernel_contDiffOn_of_chord_pos
    {α r : ℝ} (_hr : 0 < r) (hrπ : r⁻¹ ≤ Real.pi)
    {W : Set (ℝ × ℝ)} (_hW : IsOpen W)
    (hphysical : W ⊆ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1)
    (hchord : ∀ p ∈ W, ∀ θ ∈ Icc r⁻¹ Real.pi,
      0 < 2 - 2 * p.1 * p.2 -
        2 * Real.sqrt (1 - p.1 ^ 2) *
          Real.sqrt (1 - p.2 ^ 2) * Real.cos θ) :
    ContDiffOn ℝ 4 (nearTailKernel α r) W := by
  have hsub : W ⊆ integralParameterDomain nearTailSmoothDomain r⁻¹ Real.pi := by
    intro p hp θ hθ
    exact ⟨(hphysical hp).1, (hphysical hp).2, hchord p hp θ hθ⟩
  have hI : ContDiffOn ℝ 4
      (fun p : ℝ × ℝ => ∫ θ in r⁻¹..Real.pi,
        latitudeProfile α p.1 p.2 θ)
      (integralParameterDomain nearTailSmoothDomain r⁻¹ Real.pi) :=
    contDiffOn_intervalIntegral_param_of_contDiffOn 4
      isOpen_nearTailSmoothDomain (latitudeProfile_joint_contDiffOn α) hrπ
  change ContDiffOn ℝ 4
    (fun p : ℝ × ℝ => (1 / Real.pi) *
      ∫ θ in r⁻¹..Real.pi, latitudeProfile α p.1 p.2 θ) W
  exact (contDiffOn_const.mul hI).mono hsub

theorem partialFirst_const_mul_of_C1
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 1 G W)
    (c : ℝ) {p : ℝ × ℝ} (hp : p ∈ W) :
    partialFirst (fun q => c * G q) p = c * partialFirst G p := by
  have hdiff : DifferentiableAt ℝ G p :=
    (hG.contDiffAt (hW.mem_nhds hp)).differentiableAt (by decide)
  unfold partialFirst
  rw [fderiv_const_mul hdiff c]
  rfl

theorem partialSecond_const_mul_of_C1
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 1 G W)
    (c : ℝ) {p : ℝ × ℝ} (hp : p ∈ W) :
    partialSecond (fun q => c * G q) p = c * partialSecond G p := by
  have hdiff : DifferentiableAt ℝ G p :=
    (hG.contDiffAt (hW.mem_nhds hp)).differentiableAt (by decide)
  unfold partialSecond
  rw [fderiv_const_mul hdiff c]
  rfl

theorem mixedFourth_const_mul_of_C4
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (c : ℝ) {p : ℝ × ℝ} (hp : p ∈ W) :
    mixedFourth (fun q => c * G q) p.1 p.2 =
      c * mixedFourth G p.1 p.2 := by
  let H : ℝ × ℝ → ℝ := fun q => c * G q
  have hH : ContDiffOn ℝ 4 H W := contDiffOn_const.mul hG
  have hG₁ : ContDiffOn ℝ 3 (partialSecond G) W :=
    contDiffOn_partialSecond hW hG
  have hG₂ : ContDiffOn ℝ 2 (partialSecondTwice G) W :=
    contDiffOn_partialSecondTwice hW hG
  have hG₃ : ContDiffOn ℝ 1
      (partialFirst (partialSecondTwice G)) W :=
    contDiffOn_partialFirst_of_succ hW hG₂ (by decide)
  have hEq₁ : EqOn (partialSecond H)
      (fun q => c * partialSecond G q) W := by
    intro q hq
    exact partialSecond_const_mul_of_C1 hW
      (hG.of_le (by norm_num)) c hq
  have hEq₂ : EqOn (partialSecondTwice H)
      (fun q => c * partialSecondTwice G q) W := by
    intro q hq
    calc
      partialSecondTwice H q =
          partialSecond (fun x => c * partialSecond G x) q :=
        partialSecond_congr_on_open hW hEq₁ q hq
      _ = c * partialSecondTwice G q :=
        partialSecond_const_mul_of_C1 hW
          (hG₁.of_le (by norm_num)) c hq
  have hEq₃ : EqOn (partialFirst (partialSecondTwice H))
      (fun q => c * partialFirst (partialSecondTwice G) q) W := by
    intro q hq
    calc
      partialFirst (partialSecondTwice H) q =
          partialFirst (fun x => c * partialSecondTwice G x) q :=
        partialFirst_congr_on_open hW hEq₂ q hq
      _ = c * partialFirst (partialSecondTwice G) q :=
        partialFirst_const_mul_of_C1 hW
          (hG₂.of_le (by norm_num)) c hq
  have hEq₄ : EqOn (partialFirstTwice (partialSecondTwice H))
      (fun q => c * partialFirstTwice (partialSecondTwice G) q) W := by
    intro q hq
    calc
      partialFirstTwice (partialSecondTwice H) q =
          partialFirst (fun x => c * partialFirst (partialSecondTwice G) x) q :=
        partialFirst_congr_on_open hW hEq₃ q hq
      _ = c * partialFirstTwice (partialSecondTwice G) q :=
        partialFirst_const_mul_of_C1 hW hG₃ c hq
  rw [mixedFourth_eq_partialFirstTwice_partialSecondTwice hW hH p.1 p.2 hp,
    mixedFourth_eq_partialFirstTwice_partialSecondTwice hW hG p.1 p.2 hp]
  exact hEq₄ hp

/-- The near-tail mixed fourth derivative is the angular integral of the
pointwise mixed fourth derivative, on every uniformly positive-chord open
height domain. -/
theorem mixedFourth_nearTailKernel_eq_integral
    {α r : ℝ} (_hr : 0 < r) (hrπ : r⁻¹ ≤ Real.pi)
    {W : Set (ℝ × ℝ)} (_hW : IsOpen W)
    (hphysical : W ⊆ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1)
    (hchord : ∀ p ∈ W, ∀ θ ∈ Icc r⁻¹ Real.pi,
      0 < 2 - 2 * p.1 * p.2 -
        2 * Real.sqrt (1 - p.1 ^ 2) *
          Real.sqrt (1 - p.2 ^ 2) * Real.cos θ)
    {p : ℝ × ℝ} (hp : p ∈ W) :
    mixedFourth (nearTailKernel α r) p.1 p.2 =
      (1 / Real.pi) * ∫ θ in r⁻¹..Real.pi,
        mixedFourth
          (fun q : ℝ × ℝ => latitudeProfile α q.1 q.2 θ)
          p.1 p.2 := by
  let P := integralParameterDomain nearTailSmoothDomain r⁻¹ Real.pi
  have hP : IsOpen P :=
    isOpen_integralParameterDomain isOpen_nearTailSmoothDomain _ _
  have hsub : W ⊆ P := by
    intro q hq θ hθ
    exact ⟨(hphysical hq).1, (hphysical hq).2, hchord q hq θ hθ⟩
  have hpP : p ∈ P := hsub hp
  let F : ((ℝ × ℝ) × ℝ) → ℝ :=
    fun z => latitudeProfile α z.1.1 z.1.2 z.2
  have hF : ContDiffOn ℝ 4 F nearTailSmoothDomain :=
    latitudeProfile_joint_contDiffOn α
  have hI : ContDiffOn ℝ 4
      (fun q : ℝ × ℝ => ∫ θ in r⁻¹..Real.pi, F (q, θ)) P :=
    contDiffOn_intervalIntegral_param_of_contDiffOn 4
      isOpen_nearTailSmoothDomain hF hrπ
  change mixedFourth
    (fun q : ℝ × ℝ => (1 / Real.pi) *
      ∫ θ in r⁻¹..Real.pi, F (q, θ)) p.1 p.2 = _
  rw [mixedFourth_const_mul_of_C4 hP hI (1 / Real.pi) hpP]
  rw [mixedFourth_intervalIntegral_eq
    isOpen_nearTailSmoothDomain hF hrπ hpP]

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
