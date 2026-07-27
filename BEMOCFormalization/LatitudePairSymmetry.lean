import BEMOCFormalization.LatitudeL2
import BEMOCFormalization.LatitudeConcreteBlocks
import BEMOCFormalization.LatitudeSeparatedBlocks

/-!
# Symmetry of latitude block errors

The one-dimensional band rule is a signed linear functional.  Two such
functionals therefore commute on a continuous kernel; the only analytic
ingredient is Fubini on the compact band rectangle.  For symmetric kernels
this identifies a block with the block having its two indices reversed.
-/

open MeasureTheory Set

namespace BEMOC

/-- Fubini for two ordered interval integrals of a jointly continuous
function. -/
theorem intervalIntegral_intervalIntegral_swap_of_continuous
    {K : ℝ → ℝ → ℝ} (hK : Continuous (fun p : ℝ × ℝ ↦ K p.1 p.2))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ s in a..b, ∫ t in c..d, K s t) =
      ∫ t in c..d, ∫ s in a..b, K s t := by
  have hrect : IntegrableOn (fun p : ℝ × ℝ ↦ K p.1 p.2)
      (Icc a b ×ˢ Icc c d) :=
    hK.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hioc : IntegrableOn (fun p : ℝ × ℝ ↦ K p.1 p.2)
      (Ioc a b ×ˢ Ioc c d) :=
    hrect.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hint : Integrable (Function.uncurry K)
      ((volume.restrict (Ioc a b)).prod
        (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact hioc
  simp_rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hcd]
  exact MeasureTheory.integral_integral_swap hint

/-- The atomic parts of two band rules commute, with the kernel transposed. -/
theorem bandAtomicValue_bandAtomicValue_swap
    (N : ℕ) (j k : Fin (bandTailCount N + 1))
    (K : ℝ → ℝ → ℝ) :
    bandAtomicValue N j
        (fun s ↦ bandAtomicValue N k (fun t ↦ K s t)) =
      bandAtomicValue N k
        (fun t ↦ bandAtomicValue N j (fun s ↦ K s t)) := by
  unfold bandAtomicValue
  ring

/-- An atomic band rule commutes past a continuous band rule, with the
kernel transposed. -/
theorem bandAtomicValue_bandContinuousValue_swap
    (N : ℕ) (j k : Fin (bandTailCount N + 1))
    (K : ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : ℝ × ℝ ↦ K p.1 p.2)) :
    bandAtomicValue N j
        (fun s ↦ bandContinuousValue N k (fun t ↦ K s t)) =
      bandContinuousValue N k
        (fun t ↦ bandAtomicValue N j (fun s ↦ K s t)) := by
  unfold bandAtomicValue bandContinuousValue
  have h₁ : IntervalIntegrable
      (fun t ↦ (midpointRingPopulation N j : ℝ) *
        K (bandMidpointHeight N j) t) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k) :=
    (continuous_const.mul
      (hK.comp (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
  have h₂ : IntervalIntegrable
      (fun t ↦ (boundarySixth N j : ℝ) *
        K (bandBoundaryHeight N j) t) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k) :=
    (continuous_const.mul
      (hK.comp (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
  have h₃ : IntervalIntegrable
      (fun t ↦ (boundarySixth N j : ℝ) *
        K (bandBoundaryHeight N (j + 1)) t) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k) :=
    (continuous_const.mul
      (hK.comp (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
  simp only
  rw [intervalIntegral.integral_add (h₁.add h₂) h₃,
    intervalIntegral.integral_add h₁ h₂,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

/-- The continuous parts of two band rules commute, with the kernel
transposed. -/
theorem bandContinuousValue_bandContinuousValue_swap
    (N : ℕ) (j k : Fin (bandTailCount N + 1))
    (K : ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : ℝ × ℝ ↦ K p.1 p.2)) :
    bandContinuousValue N j
        (fun s ↦ bandContinuousValue N k (fun t ↦ K s t)) =
      bandContinuousValue N k
        (fun t ↦ bandContinuousValue N j (fun s ↦ K s t)) := by
  unfold bandContinuousValue
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral_intervalIntegral_swap_of_continuous hK
    (bandBoundaryHeight_succ_le j) (bandBoundaryHeight_succ_le k)]

/-- The continuous part of a band rule is additive on interval-integrable
functions. -/
theorem bandContinuousValue_sub
    (N : ℕ) (j : Fin (bandTailCount N + 1)) (f g : ℝ → ℝ)
    (hf : IntervalIntegrable f volume
      (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j))
    (hg : IntervalIntegrable g volume
      (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j)) :
    bandContinuousValue N j (fun t ↦ f t - g t) =
      bandContinuousValue N j f - bandContinuousValue N j g := by
  unfold bandContinuousValue
  rw [intervalIntegral.integral_sub hf hg]
  ring

/-- Expansion of a paired band error into its four atomic/continuous
components. -/
theorem bandPairError_eq_four_terms
    (N : ℕ) (j k : Fin (bandTailCount N + 1))
    (K : ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : ℝ × ℝ ↦ K p.1 p.2)) :
    bandPairError N j k K =
      bandAtomicValue N j
          (fun s ↦ bandAtomicValue N k (fun t ↦ K s t)) -
        bandAtomicValue N j
          (fun s ↦ bandContinuousValue N k (fun t ↦ K s t)) -
        bandContinuousValue N j
          (fun s ↦ bandAtomicValue N k (fun t ↦ K s t)) +
        bandContinuousValue N j
          (fun s ↦ bandContinuousValue N k (fun t ↦ K s t)) := by
  unfold bandPairError
  rw [show bandError N j
      (fun s ↦ bandError N k (fun t ↦ K s t)) =
      bandAtomicValue N j
          (fun s ↦ bandError N k (fun t ↦ K s t)) -
        bandContinuousValue N j
          (fun s ↦ bandError N k (fun t ↦ K s t)) by rfl]
  rw [show bandAtomicValue N j
      (fun s ↦ bandError N k (fun t ↦ K s t)) =
      bandAtomicValue N j
          (fun s ↦ bandAtomicValue N k (fun t ↦ K s t)) -
        bandAtomicValue N j
          (fun s ↦ bandContinuousValue N k (fun t ↦ K s t)) by
    unfold bandError bandAtomicValue
    ring]
  rw [show bandContinuousValue N j
      (fun s ↦ bandError N k (fun t ↦ K s t)) =
      bandContinuousValue N j
        (fun s ↦ bandAtomicValue N k (fun t ↦ K s t) -
          bandContinuousValue N k (fun t ↦ K s t)) by rfl]
  have hsub : bandContinuousValue N j
      (fun s ↦ bandAtomicValue N k (fun t ↦ K s t) -
        bandContinuousValue N k (fun t ↦ K s t)) =
      bandContinuousValue N j
          (fun s ↦ bandAtomicValue N k (fun t ↦ K s t)) -
        bandContinuousValue N j
          (fun s ↦ bandContinuousValue N k (fun t ↦ K s t)) :=
    bandContinuousValue_sub N j _ _
      ((continuous_bandAtomicValue_right k hK).intervalIntegrable _ _)
      ((continuous_bandContinuousValue_right k hK).intervalIntegrable _ _)
  rw [hsub]
  ring

/-- Paired band errors of a continuous symmetric kernel are symmetric in the
two band indices. -/
theorem bandPairError_swap_of_continuous_of_symmetric
    (N : ℕ) (j k : Fin (bandTailCount N + 1))
    (K : ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : ℝ × ℝ ↦ K p.1 p.2))
    (hsym : ∀ s t, K s t = K t s) :
    bandPairError N j k K = bandPairError N k j K := by
  let KT : ℝ → ℝ → ℝ := fun t s ↦ K s t
  have hKT : Continuous (fun p : ℝ × ℝ ↦ KT p.1 p.2) :=
    hK.comp (continuous_snd.prodMk continuous_fst)
  have hKT_eq : KT = K := by
    funext t s
    exact hsym s t
  rw [bandPairError_eq_four_terms N j k K hK]
  conv_rhs => rw [← hKT_eq]
  rw [bandPairError_eq_four_terms N k j KT hKT]
  rw [bandAtomicValue_bandAtomicValue_swap N j k K,
    bandAtomicValue_bandContinuousValue_swap N j k K hK,
    ← bandAtomicValue_bandContinuousValue_swap N k j KT hKT,
    bandContinuousValue_bandContinuousValue_swap N j k K hK]
  simp only [KT]
  ring

/-- In particular, every positive-exponent latitude-kernel block is
symmetric. -/
theorem latitudeKernel_bandPairError_swap
    {α : ℝ} (hα : 0 < α) (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) :
    bandPairError N j k (latitudeKernel α) =
      bandPairError N k j (latitudeKernel α) :=
  bandPairError_swap_of_continuous_of_symmetric N j k
    (latitudeKernel α) (continuous_latitudeKernel hα) (latitudeKernel_swap α)

end BEMOC
