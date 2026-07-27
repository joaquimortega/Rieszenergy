import BEMOCFormalization.LatitudeUnequalSummand
import BEMOCFormalization.RealBinomialSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual even binomial expansion of the latitude angular average

This module evaluates the generalized binomial series under the angular
integral, removes its odd terms by symmetry, and identifies the remaining
height-dependent factor with `latitudeEvenPowerSummand`.
-/

open MeasureTheory Set

namespace BEMOC

noncomputable section

/-- The normalized cosine moment on the full circle. -/
def normalizedCosineMoment (n : ℕ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos θ ^ n

/-- A term of the generalized binomial series before angular integration. -/
def angularBinomialTerm (β q : ℝ) (n : ℕ) (θ : ℝ) : ℝ :=
  Ring.choose β n * (-q * Real.cos θ) ^ n

theorem continuous_angularBinomialTerm (β q : ℝ) (n : ℕ) :
    Continuous (angularBinomialTerm β q n) := by
  unfold angularBinomialTerm
  fun_prop

theorem summable_angularBinomialTerm (β q θ : ℝ) (hq : |q| < 1) :
    Summable (fun n ↦ angularBinomialTerm β q n θ) := by
  apply summable_real_choose_mul_pow β (-q * Real.cos θ)
  calc
    |-q * Real.cos θ| = |q| * |Real.cos θ| := by rw [abs_mul, abs_neg]
    _ ≤ |q| * 1 := mul_le_mul_of_nonneg_left (abs_cos_le_one θ) (abs_nonneg q)
    _ < 1 := by simpa using hq

/-- Normal convergence on the angular interval, in the exact form needed
by the interval-integral sum theorem. -/
private theorem summable_restricted_angularBinomialTerm_norm
    (β q : ℝ) (hq : |q| < 1) :
    Summable (fun n : ℕ ↦
      ‖(⟨angularBinomialTerm β q n,
          continuous_angularBinomialTerm β q n⟩ : C(ℝ, ℝ)).restrict
        (⟨uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ : Compacts ℝ)‖) := by
  have habs :
      Summable (fun n : ℕ ↦ |Ring.choose β n * |q| ^ n|) := by
    simpa [Real.norm_eq_abs] using
      (summable_real_choose_mul_pow β |q| (by simpa [abs_abs] using hq)).norm
  apply habs.of_nonneg_of_le
  · intro n
    exact norm_nonneg _
  · intro n
    apply (ContinuousMap.norm_le _ (abs_nonneg _)).2
    intro θ
    simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk,
      angularBinomialTerm, Real.norm_eq_abs, abs_mul, abs_pow]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      calc
        |-q * Real.cos θ| = |q| * |Real.cos θ| := by rw [abs_mul, abs_neg]
        _ ≤ |q| := by
          simpa using mul_le_mul_of_nonneg_left
            (abs_cos_le_one (θ : ℝ)) (abs_nonneg q)) n

/-- The generalized binomial sum may be integrated term by term on the
full angular circle. -/
theorem tsum_intervalIntegral_angularBinomialTerm
    (β q : ℝ) (hq : |q| < 1) :
    ∑' n : ℕ, ∫ θ in (0 : ℝ)..2 * Real.pi,
        angularBinomialTerm β q n θ =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        ∑' n : ℕ, angularBinomialTerm β q n θ := by
  let f : ℕ → C(ℝ, ℝ) := fun n ↦
    ⟨angularBinomialTerm β q n, continuous_angularBinomialTerm β q n⟩
  simpa [f] using
    intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (summable_restricted_angularBinomialTerm_norm β q hq)

/-- Pointwise evaluation of the angular generalized-binomial series. -/
theorem tsum_angularBinomialTerm_eq_rpow
    (β q θ : ℝ) (hq : |q| < 1) :
    ∑' n : ℕ, angularBinomialTerm β q n θ =
      (1 - q * Real.cos θ) ^ β := by
  unfold angularBinomialTerm
  rw [tsum_real_choose_mul_pow_eq_rpow]
  · ring_nf
  · calc
      |-q * Real.cos θ| ≤ |q| := by
        rw [abs_mul, abs_neg]
        simpa using mul_le_mul_of_nonneg_left
          (abs_cos_le_one θ) (abs_nonneg q)
      _ < 1 := hq

/-- The normalized angular real-power average is the series of normalized
cosine moments. -/
theorem normalized_angular_rpow_eq_tsum
    (β q : ℝ) (hq : |q| < 1) :
    (1 / (2 * Real.pi)) *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          (1 - q * Real.cos θ) ^ β =
      ∑' n : ℕ,
        Ring.choose β n * (-q) ^ n * normalizedCosineMoment n := by
  rw [← tsum_intervalIntegral_angularBinomialTerm β q hq]
  rw [← tsum_angularBinomialTerm_eq_rpow β q · hq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold angularBinomialTerm normalizedCosineMoment
  rw [intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_const_mul]
  congr 2
  funext θ
  rw [mul_pow]
  ring

end

end BEMOC
