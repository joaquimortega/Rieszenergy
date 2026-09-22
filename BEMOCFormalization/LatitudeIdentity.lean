import BEMOCFormalization.BandErrors
import BEMOCFormalization.LatitudePotential

open scoped BigOperators
open MeasureTheory
namespace BEMOC.Definitive

/-- Consecutive closed latitude bands telescope as oriented interval integrals. -/
theorem sum_band_interval_integrals (N m : ℕ) (f : ℝ → ℝ)
    (hf : Continuous f) :
    (∑ j ∈ Finset.Icc 1 m,
      ∫ t in boundary N j..boundary N (j - 1), f t) =
      ∫ t in boundary N m..boundary N 0, f t := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
      have hsub : m + 1 - 1 = m := by omega
      rw [hsub, add_comm]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

/-- Reindex a sum over one-based occupied bands as the finite ring type. -/
theorem sum_ringIndex_eq_sum_Icc {N : ℕ} (hN : 4 ≤ N) (f : ℕ → ℝ) :
    (∑ j : RingIndex N, f (j.val + 1)) =
      ∑ j ∈ Finset.Icc 1 (2 * bandParameter N - 1), f j := by
  let M := bandParameter N
  have hM : 1 ≤ M := bandParameter_pos hN
  calc
    (∑ j : RingIndex N, f (j.val + 1)) =
        ∑ j ∈ Finset.range (2 * M - 1), f (j + 1) := by
          simpa [RingIndex, M] using
            (Fin.sum_univ_eq_sum_range (fun j : ℕ => f (j + 1)) (2 * M - 1))
    _ = ∑ j ∈ Finset.Ico 1 (2 * M), f j := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_comm]
    _ = ∑ j ∈ Finset.Icc 1 (2 * M - 1), f j := by
      rw [Nat.Icc_pred_right 1 (by omega : 0 < 2 * M)]

/-- All occupied band integrals form the full height interval. -/
theorem sum_ring_band_integrals {N : ℕ} (hN : 4 ≤ N)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∑ j : RingIndex N,
      ∫ t in boundary N (j.val + 1)..boundary N (j.val + 1 - 1), f t) =
      ∫ t in (-1 : ℝ)..1, f t := by
  rw [show (∑ j : RingIndex N,
      ∫ t in boundary N (j.val + 1)..boundary N (j.val + 1 - 1), f t) =
      ∑ j ∈ Finset.Icc 1 (2 * bandParameter N - 1),
        ∫ t in boundary N j..boundary N (j - 1), f t from
    sum_ringIndex_eq_sum_Icc hN
      (fun j => ∫ t in boundary N j..boundary N (j - 1), f t)]
  rw [sum_band_interval_integrals N (2 * bandParameter N - 1) f hf]
  rw [boundary_last hN, boundary_zero]

/-- The sum of signed band rules is the difference of full-height and atomic rules. -/
theorem sum_bandError_eq {N : ℕ} (hN : 4 ≤ N)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∑ j : RingIndex N, bandError N (j.val + 1) f) =
      (N : ℝ) / 2 * (∫ t in (-1 : ℝ)..1, f t) -
        ∑ j : RingIndex N,
          (population N (j.val + 1) : ℝ) * f (height N (j.val + 1)) := by
  simp only [bandError, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_ring_band_integrals hN f hf]

/-- The inner sum of band errors is continuous in the outer height. -/
theorem continuous_sum_bandError_kernel {α : ℝ} (hα : 0 < α) (N : ℕ) :
    Continuous (fun s => ∑ k : RingIndex N,
      bandError N (k.val + 1) (fun t => latitudeKernel α s t)) := by
  apply continuous_finset_sum
  intro k _
  unfold bandError
  have hK := continuous_latitudeKernel_bandErrors hα
  exact (continuous_const.mul (continuous_intervalIntegral_right hK _ _)).sub
    (continuous_const.mul (hK.comp (continuous_id.prodMk continuous_const)))

/-- The potential of the continuous latitude distribution, with total mass `N`. -/
theorem integral_latitudeKernel_eq_mass_potential {α s : ℝ} (hα : 0 < α)
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (N : ℕ) :
    (N : ℝ) / 2 * (∫ t in (-1 : ℝ)..1, latitudeKernel α s t) =
      (N : ℝ) * continuousEnergy α := by
  have hp := half_intervalIntegral_latitudeKernel hs hα
  nlinarith [hp]

/-- Sum of the inner band rules evaluated at any physical height. -/
theorem sum_inner_bandError_kernel {α s : ℝ} (hα : 0 < α)
    {N : ℕ} (hN : 4 ≤ N) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    (∑ k : RingIndex N,
      bandError N (k.val + 1) (fun t => latitudeKernel α s t)) =
      (N : ℝ) * continuousEnergy α -
        ∑ k : RingIndex N,
          (population N (k.val + 1) : ℝ) *
            latitudeKernel α s (height N (k.val + 1)) := by
  rw [sum_bandError_eq hN]
  · rw [integral_latitudeKernel_eq_mass_potential hα hs N]
  · exact (continuous_latitudeKernel_bandErrors hα).comp
      (continuous_const.prodMk continuous_id)

/-- The atomic potential has the same full-height integral as the continuous one. -/
theorem integral_atomic_potential {α : ℝ} (hα : 0 < α)
    {N : ℕ} (hN : 4 ≤ N) :
    (∫ s in (-1 : ℝ)..1,
      ∑ k : RingIndex N, (population N (k.val + 1) : ℝ) *
        latitudeKernel α s (height N (k.val + 1))) =
      2 * (N : ℝ) * continuousEnergy α := by
  have hK := continuous_latitudeKernel_bandErrors hα
  rw [intervalIntegral.integral_finset_sum]
  · have hterm (k : RingIndex N) :
        (∫ s in (-1 : ℝ)..1,
          (population N (k.val + 1) : ℝ) *
            latitudeKernel α s (height N (k.val + 1))) =
          (population N (k.val + 1) : ℝ) * (2 * continuousEnergy α) := by
        rw [intervalIntegral.integral_const_mul]
        have hh : height N (k.val + 1) ∈ Set.Icc (-1 : ℝ) 1 := by
          have hi := height_in_open_unit hN (j := k.val + 1)
            (by omega) (by have := k.isLt; omega)
          exact Set.Ioo_subset_Icc_self hi
        have hp := half_intervalIntegral_latitudeKernel (s := height N (k.val + 1))
          (α := α) hh hα
        have hswap :
            (∫ s in (-1 : ℝ)..1,
              latitudeKernel α s (height N (k.val + 1))) =
            ∫ s in (-1 : ℝ)..1,
              latitudeKernel α (height N (k.val + 1)) s := by
          apply intervalIntegral.integral_congr
          intro s _
          exact latitudeKernel_swap α s _
        rw [hswap]
        congr 1
        linarith
    simp_rw [hterm, ← Finset.sum_mul]
    have hpop : (∑ k : RingIndex N, (population N (k.val + 1) : ℝ)) = N := by
      exact_mod_cast population_sum_eq N hN
    rw [hpop]
    ring
  · intro k _
    exact (continuous_const.mul
      (hK.comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _

/-- The continuous height rule annihilates the summed inner discrepancy. -/
theorem integral_sum_inner_bandError_eq_zero {α : ℝ} (hα : 0 < α)
    {N : ℕ} (hN : 4 ≤ N) :
    (∫ s in (-1 : ℝ)..1,
      ∑ k : RingIndex N,
        bandError N (k.val + 1) (fun t => latitudeKernel α s t)) = 0 := by
  have hcong :
      (∫ s in (-1 : ℝ)..1,
        ∑ k : RingIndex N,
          bandError N (k.val + 1) (fun t => latitudeKernel α s t)) =
      ∫ s in (-1 : ℝ)..1,
        (N : ℝ) * continuousEnergy α -
          ∑ k : RingIndex N,
            (population N (k.val + 1) : ℝ) *
              latitudeKernel α s (height N (k.val + 1)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact sum_inner_bandError_kernel hα hN
      (by simpa only [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs)
  rw [hcong, intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const, integral_atomic_potential hα hN]
    simp only [smul_eq_mul]
    ring
  · exact intervalIntegrable_const
  · apply Continuous.intervalIntegrable
    apply continuous_finset_sum
    intro k _
    exact continuous_const.mul
      ((continuous_latitudeKernel_bandErrors hα).comp
        (continuous_id.prodMk continuous_const))

/-- Finite additivity of a band rule for continuous summands. -/
theorem bandError_finset_sum {ι : Type*} (S : Finset ι) (N j : ℕ)
    (f : ι → ℝ → ℝ) (hf : ∀ i ∈ S, Continuous (f i)) :
    bandError N j (fun s => ∑ i ∈ S, f i s) =
      ∑ i ∈ S, bandError N j (f i) := by
  unfold bandError
  rw [intervalIntegral.integral_finset_sum]
  · rw [Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
  · intro i hi
    exact (hf i hi).intervalIntegrable _ _

/-- Summed blocks are the outer signed rule applied to the summed inner rule. -/
theorem sum_kernelBlocks_eq_outer_rule {α : ℝ} (hα : 0 < α)
    (N : ℕ) :
    (∑ j : RingIndex N, ∑ k : RingIndex N,
      kernelBlock α N (j.val + 1) (k.val + 1)) =
      ∑ j : RingIndex N,
        bandError N (j.val + 1) (fun s =>
          ∑ k : RingIndex N,
            bandError N (k.val + 1) (fun t => latitudeKernel α s t)) := by
  apply Finset.sum_congr rfl
  intro j _
  change (∑ k : RingIndex N,
      bandError N (j.val + 1)
        (fun s => bandError N (k.val + 1)
          (fun t => latitudeKernel α s t))) = _
  symm
  apply bandError_finset_sum
  intro k _
  have hK := continuous_latitudeKernel_bandErrors hα
  unfold bandError
  exact (continuous_const.mul (continuous_intervalIntegral_right hK _ _)).sub
    (continuous_const.mul (hK.comp (continuous_id.prodMk continuous_const)))

/-- The latitude energy identity follows from the concrete height potential. -/
theorem latitudeIdentity_of_pos {α : ℝ} (hα : 0 < α) : LatitudeIdentity α := by
  intro N hN
  have hpop : (∑ j : RingIndex N, (population N (j.val + 1) : ℝ)) = N := by
    exact_mod_cast population_sum_eq N hN
  have hsum := sum_kernelBlocks_eq_outer_rule hα N
  rw [hsum, sum_bandError_eq hN _ (continuous_sum_bandError_kernel hα N),
    integral_sum_inner_bandError_eq_zero hα hN]
  simp only [mul_zero, zero_sub]
  have hinner (j : RingIndex N) := sum_inner_bandError_kernel hα hN
    (show height N (j.val + 1) ∈ Set.Icc (-1 : ℝ) 1 from
      Set.Ioo_subset_Icc_self
        (height_in_open_unit hN (by omega)
          (by have := j.isLt; omega)))
  simp_rw [hinner]
  unfold latitudeError ringEnergy
  simp_rw [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  rw [hpop]
  ring

end BEMOC.Definitive
