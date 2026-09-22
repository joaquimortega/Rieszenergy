import BEMOCFormalization.LatitudePushforward

/-!
# Two-variable latitude quadrature bookkeeping

This module contains the algebraic half of the latitude L2 step.  In
particular, it makes the passage from a double sum of local band errors to a
single outer band error completely explicit.  The remaining geometric input
is the identification of the continuous height-pair quadrature with the
spherical constant potential.
-/

open scoped BigOperators
open MeasureTheory Set

namespace BEMOC

/-- The angular average is jointly continuous for positive Riesz exponent. -/
theorem continuous_latitudeKernel {α : ℝ} (hα : 0 < α) :
    Continuous (fun p : ℝ × ℝ ↦ latitudeKernel α p.1 p.2) := by
  unfold latitudeKernel
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous (fun p : (ℝ × ℝ) × ℝ ↦ angularPairKernel α p.1.1 p.1.2 p.2)
  exact continuous_angularPairKernel hα |>.comp
    (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))

/-- Applying one atomic band rule in the second variable preserves
continuity in the first variable. -/
theorem continuous_bandAtomicValue_right {N : ℕ}
    (j : Fin (bandTailCount N + 1)) {K : ℝ → ℝ → ℝ}
    (hK : Continuous (fun p : ℝ × ℝ ↦ K p.1 p.2)) :
    Continuous (fun s ↦ bandAtomicValue N j (fun t ↦ K s t)) := by
  unfold bandAtomicValue
  fun_prop

/-- Applying one continuous band rule in the second variable preserves
continuity in the first variable. -/
theorem continuous_bandContinuousValue_right {N : ℕ}
    (j : Fin (bandTailCount N + 1)) {K : ℝ → ℝ → ℝ}
    (hK : Continuous (fun p : ℝ × ℝ ↦ K p.1 p.2)) :
    Continuous (fun s ↦ bandContinuousValue N j (fun t ↦ K s t)) := by
  unfold bandContinuousValue
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous (fun p : ℝ × ℝ ↦ K p.1 p.2)
  exact hK

/-- The one-band error in the second variable is continuous in the first. -/
theorem continuous_bandError_right {N : ℕ}
    (j : Fin (bandTailCount N + 1)) {K : ℝ → ℝ → ℝ}
    (hK : Continuous (fun p : ℝ × ℝ ↦ K p.1 p.2)) :
    Continuous (fun s ↦ bandError N j (fun t ↦ K s t)) := by
  unfold bandError
  exact (continuous_bandAtomicValue_right j hK).sub
    (continuous_bandContinuousValue_right j hK)

/-- A local band error commutes with a finite sum of continuous functions. -/
theorem bandError_finset_sum {N : ℕ}
    (j : Fin (bandTailCount N + 1)) {ι : Type*} (S : Finset ι)
    (f : ι → ℝ → ℝ) (hf : ∀ i ∈ S, Continuous (f i)) :
    bandError N j (fun x ↦ ∑ i ∈ S, f i x) =
      ∑ i ∈ S, bandError N j (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [bandError, bandAtomicValue, bandContinuousValue]
  | insert a S ha ih =>
      have hsum : (fun x ↦ ∑ i ∈ insert a S, f i x) =
          (fun x ↦ f a x) + (fun x ↦ ∑ i ∈ S, f i x) := by
        funext x
        rw [Finset.sum_insert ha]
        rfl
      rw [hsum, Finset.sum_insert ha]
      change bandError N j (fun x ↦ f a x + ∑ i ∈ S, f i x) = _
      rw [bandError_add]
      · rw [ih]
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      · exact (hf a (Finset.mem_insert_self a S)).intervalIntegrable _ _
      · exact (continuous_finset_sum _ fun i hi ↦
          hf i (Finset.mem_insert_of_mem hi)).intervalIntegrable _ _

/-- The double sum of local pair errors is exactly an outer band error
applied to the summed inner errors.  This is the finite-sum/Fubini part of
the L2 bookkeeping; no estimate is used. -/
theorem sum_bandPairError_eq_total_bandError {N : ℕ}
    {K : ℝ → ℝ → ℝ}
    (hK : Continuous (fun p : ℝ × ℝ ↦ K p.1 p.2)) :
    (∑ j : Fin (bandTailCount N + 1),
      ∑ k : Fin (bandTailCount N + 1), bandPairError N j k K) =
    ∑ j : Fin (bandTailCount N + 1),
      bandError N j (fun s ↦
        ∑ k : Fin (bandTailCount N + 1), bandError N k (fun t ↦ K s t)) := by
  apply Finset.sum_congr rfl
  intro j hj
  symm
  apply bandError_finset_sum
  intro k hk
  exact continuous_bandError_right k hK

/-- The uncombined double atomic band rule.  The following theorem identifies
it with the literal BEMOC midpoint/shared-boundary ring quadrature. -/
noncomputable def bandAtomicPairValue (N : ℕ) (K : ℝ → ℝ → ℝ) : ℝ :=
  ∑ j : Fin (bandTailCount N + 1),
    bandAtomicValue N j (fun s ↦
      ∑ k : Fin (bandTailCount N + 1), bandAtomicValue N k (fun t ↦ K s t))

theorem bandAtomicPairValue_eq_bemoc_sum {N : ℕ} (hN : 0 < N)
    (K : ℝ → ℝ → ℝ) :
    bandAtomicPairValue N K =
      ∑ p : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
        ∑ q : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
          (bemocRingFamily N p).population * (bemocRingFamily N q).population *
            K (bemocRingFamily N p).height (bemocRingFamily N q).height := by
  unfold bandAtomicPairValue
  rw [sum_bandAtomicValue_eq_bemocRingFamily hN]
  simp_rw [sum_bandAtomicValue_eq_bemocRingFamily hN]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- The precise geometric/Fubini proposition connecting the local band
algebra to the latitude-deficit identity.  `LatitudeAxialBridge` proves it
for the concrete BEMOC geometry. -/
def HasExactLatitudePairQuadrature (α : ℝ) (N : ℕ) : Prop :=
  (∑ j : Fin (bandTailCount N + 1),
    ∑ k : Fin (bandTailCount N + 1),
      bandPairError N j k (latitudeKernel α)) =
    bandAtomicPairValue N (latitudeKernel α) - continuousEnergy α * (N : ℝ) ^ 2

/-- Given the geometric constant-potential/Fubini bridge, the desired L2
equation follows by exact scalar bookkeeping. -/
theorem bemocLatitudeDeficit_eq_neg_sum_bandPairError_of_exactLatitudePairQuadrature
    {N : ℕ} {α : ℝ} (hN : 0 < N) (hα : 0 < α)
    (hquad : HasExactLatitudePairQuadrature α N) :
    bemocLatitudeDeficit α N =
      -∑ j : Fin (bandTailCount N + 1),
        ∑ k : Fin (bandTailCount N + 1),
          bandPairError N j k (latitudeKernel α) := by
  rw [bemocLatitudeDeficit_eq_continuous_minus_latitudeKernelSum hα]
  rw [← bandAtomicPairValue_eq_bemoc_sum hN (latitudeKernel α)]
  unfold HasExactLatitudePairQuadrature at hquad
  linarith

end BEMOC
