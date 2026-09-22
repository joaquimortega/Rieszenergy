import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import BEMOCFormalization.SeparatedKernel
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open scoped ENNReal NNReal Topology
namespace BEMOC.Definitive

/-- A real scalar power series, defined by its coefficients. -/
noncomputable def scalarPowerSeries (a : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' m : ℕ, a m * z ^ m

private noncomputable def scalarFormalSeries (a : ℕ → ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ a

private theorem scalarFormalSeries_radius_ge_one (a : ℕ → ℝ)
    (ha : ∀ m, |a m| ≤ 1) :
    (1 : ℝ≥0∞) ≤ (scalarFormalSeries a).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro q hq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hq1 : (q : ℝ) < 1 := by
    exact_mod_cast (ENNReal.coe_lt_coe.mp hq)
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have hgeom : Summable (fun m : ℕ => (q : ℝ) ^ m) :=
    summable_geometric_of_lt_one hq0 hq1
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (norm_nonneg _) (pow_nonneg hq0 _))
    (fun m => ?_) hgeom
  rw [scalarFormalSeries, FormalMultilinearSeries.ofScalars_norm]
  exact mul_le_of_le_one_left (pow_nonneg hq0 _) (by simpa only [Real.norm_eq_abs] using ha m)

private theorem scalarPowerSeries_eq_formal_sum (a : ℕ → ℝ) :
    scalarPowerSeries a = (scalarFormalSeries a).sum := by
  funext z
  change (∑' m : ℕ, a m * z ^ m) = FormalMultilinearSeries.ofScalarsSum a z
  simp only [FormalMultilinearSeries.ofScalars_sum_eq, smul_eq_mul]

/-- Coefficients of the successive scalar derivative series. -/
noncomputable def scalarDerivCoeff (a : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, m => a m
  | k + 1, m => (m + 1 : ℝ) * scalarDerivCoeff a k (m + 1)

/-- Shifted falling-factorial formula for the differentiated coefficients. -/
theorem scalarDerivCoeff_eq_descFactorial (a : ℕ → ℝ) (k m : ℕ) :
    scalarDerivCoeff a k m =
      (((m + k).descFactorial k : ℕ) : ℝ) * a (m + k) := by
  induction k generalizing m with
  | zero => simp [scalarDerivCoeff]
  | succ k ih =>
      rw [scalarDerivCoeff, ih]
      rw [show m + (k + 1) = m + 1 + k by omega, Nat.descFactorial_succ]
      simp only [Nat.add_sub_cancel_right, Nat.cast_mul]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

private theorem scalarDerivCoeff_bound (a : ℕ → ℝ) (ha : ∀ m, |a m| ≤ 1) :
    ∀ k m, |scalarDerivCoeff a k m| ≤ ((m + k + 1 : ℕ) : ℝ) ^ k := by
  intro k
  induction k with
  | zero =>
      intro m
      simpa only [scalarDerivCoeff, pow_zero, Nat.add_zero] using ha m
  | succ k ih =>
      intro m
      have hm0 : (0 : ℝ) ≤ m + 1 := by positivity
      have hbase := ih (m + 1)
      simp only [scalarDerivCoeff, abs_mul, abs_of_nonneg hm0] at hbase ⊢
      have hcast : ((m + 1 + k + 1 : ℕ) : ℝ) = (m + k + 2 : ℝ) := by push_cast; ring
      rw [hcast] at hbase
      have hmle : (m + 1 : ℝ) ≤ (m + k + 2 : ℝ) := by
        have hk0 : (0 : ℝ) ≤ k := by positivity
        linarith
      have htarget : ((m + (k + 1) + 1 : ℕ) : ℝ) = (m + k + 2 : ℝ) := by
        push_cast
        ring
      rw [htarget]
      calc
        (m + 1 : ℝ) * |scalarDerivCoeff a k (m + 1)| ≤
          (m + 1) * (m + k + 2 : ℝ) ^ k := mul_le_mul_of_nonneg_left hbase hm0
        _ ≤ (m + k + 2 : ℝ) ^ (k + 1) := by
          rw [pow_succ]
          have hpow0 : 0 ≤ (m + k + 2 : ℝ) ^ k := pow_nonneg (by positivity) _
          nlinarith [mul_le_mul_of_nonneg_left hmle hpow0]

private theorem scalarFormalSeries_radius_ge_one_of_poly (a : ℕ → ℝ)
    (k : ℕ) (ha : ∀ m, |a m| ≤ ((m + k + 1 : ℕ) : ℝ) ^ k) :
    (1 : ℝ≥0∞) ≤ (scalarFormalSeries a).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro q hq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hq1 : (q : ℝ) < 1 := by exact_mod_cast (ENNReal.coe_lt_coe.mp hq)
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have hpoly := summable_separated_polynomial k hq0 hq1
  have hmajor : Summable (fun m : ℕ =>
      ((k + 1 : ℕ) : ℝ) ^ k * (((m : ℝ) + 1) ^ k * (q : ℝ) ^ m)) :=
    hpoly.mul_left _
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (norm_nonneg _) (pow_nonneg hq0 _))
    (fun m => ?_) hmajor
  rw [scalarFormalSeries, FormalMultilinearSeries.ofScalars_norm]
  have hmle : ((m + k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * ((m : ℝ) + 1) := by
    push_cast
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by positivity)
      (show (0 : ℝ) ≤ m by positivity)]
  have hcoeff : |a m| ≤ ((k + 1 : ℕ) : ℝ) ^ k * ((m : ℝ) + 1) ^ k := by
    calc
      |a m| ≤ ((m + k + 1 : ℕ) : ℝ) ^ k := ha m
      _ ≤ (((k + 1 : ℕ) : ℝ) * ((m : ℝ) + 1)) ^ k := by gcongr
      _ = _ := mul_pow _ _ _
  simpa only [Real.norm_eq_abs, mul_assoc] using
    (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hq0 m))

private theorem scalarPowerSeries_deriv_eq (a : ℕ → ℝ)
    (hr : (1 : ℝ≥0∞) ≤ (scalarFormalSeries a).radius)
    (z : ℝ) (hz : |z| < 1) :
    deriv (scalarPowerSeries a) z =
      ∑' m : ℕ, (m + 1 : ℝ) * a (m + 1) * z ^ m := by
  let p := scalarFormalSeries a
  have hr0 : (0 : ℝ≥0∞) < p.radius := lt_of_lt_of_le (by norm_num) hr
  have hp := FormalMultilinearSeries.hasFPowerSeriesOnBall p hr0
  have hzball : z ∈ EMetric.ball (0 : ℝ) p.radius := by
    simp only [EMetric.mem_ball, edist_dist, dist_zero_right]
    exact lt_of_lt_of_le (ENNReal.ofReal_lt_one.mpr (by simpa only [Real.norm_eq_abs] using hz)) hr
  have hs := (hp.fderiv).hasSum hzball
  have hs' := hs.map (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
    (ContinuousLinearMap.continuous _)
  rw [scalarPowerSeries_eq_formal_sum]
  convert hs'.tsum_eq.symm using 1
  · simpa only [zero_add, ContinuousLinearMap.apply_apply] using
      (fderiv_deriv (f := p.sum) (x := z)).symm
  · apply tsum_congr
    intro m
    simp [p, scalarFormalSeries, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      FormalMultilinearSeries.derivSeries_coeff_one, smul_eq_mul, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Bounded coefficients give a real-analytic series on the open unit interval. -/
theorem scalarPowerSeries_analyticOnNhd (a : ℕ → ℝ)
    (ha : ∀ m, |a m| ≤ 1) :
    AnalyticOnNhd ℝ (scalarPowerSeries a) (Set.Ioo (-1 : ℝ) 1) := by
  let p := scalarFormalSeries a
  have hr : (1 : ℝ≥0∞) ≤ p.radius := scalarFormalSeries_radius_ge_one a ha
  have hr0 : (0 : ℝ≥0∞) < p.radius := lt_of_lt_of_le (by norm_num) hr
  have hp := (FormalMultilinearSeries.hasFPowerSeriesOnBall p hr0).analyticOnNhd
  rw [scalarPowerSeries_eq_formal_sum]
  intro z hz
  apply hp
  have hzabs : |z| < 1 := abs_lt.mpr hz
  simp only [EMetric.mem_ball, edist_dist, dist_zero_right]
  apply lt_of_lt_of_le (b := (1 : ℝ≥0∞)) _ hr
  exact ENNReal.ofReal_lt_one.mpr (by simpa only [Real.norm_eq_abs] using hzabs)

/-- In particular, bounded coefficients give four continuous derivatives. -/
theorem scalarPowerSeries_contDiffOn_four (a : ℕ → ℝ)
    (ha : ∀ m, |a m| ≤ 1) :
    ContDiffOn ℝ 4 (scalarPowerSeries a) (Set.Ioo (-1 : ℝ) 1) := by
  exact (scalarPowerSeries_analyticOnNhd a ha).analyticOn.contDiffOn_of_completeSpace

/-- Every iterated real derivative is the termwise differentiated scalar series. -/
theorem scalarPowerSeries_iteratedDeriv_eq (a : ℕ → ℝ)
    (ha : ∀ m, |a m| ≤ 1) (k : ℕ) (z : ℝ)
    (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
    iteratedDeriv k (scalarPowerSeries a) z =
      scalarPowerSeries (scalarDerivCoeff a k) z := by
  induction k generalizing z with
  | zero => simp [scalarDerivCoeff, iteratedDeriv_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv k (scalarPowerSeries a) =ᶠ[𝓝 z]
          scalarPowerSeries (scalarDerivCoeff a k) :=
        (isOpen_Ioo.eventually_mem hz).mono (fun y hy => ih y hy)
      rw [heq.deriv_eq]
      have hr : (1 : ℝ≥0∞) ≤
          (scalarFormalSeries (scalarDerivCoeff a k)).radius :=
        scalarFormalSeries_radius_ge_one_of_poly _ k (scalarDerivCoeff_bound a ha k)
      have hder := scalarPowerSeries_deriv_eq (scalarDerivCoeff a k) hr z
        (abs_lt.mpr hz)
      rw [hder]
      rfl

/-- Termwise formula with the usual falling factorial, valid at every finite order. -/
theorem scalarPowerSeries_iteratedDeriv_tsum (a : ℕ → ℝ)
    (ha : ∀ m, |a m| ≤ 1) (k : ℕ) (z : ℝ)
    (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
    iteratedDeriv k (scalarPowerSeries a) z =
      ∑' m : ℕ, (((m + k).descFactorial k : ℕ) : ℝ) * a (m + k) * z ^ m := by
  rw [scalarPowerSeries_iteratedDeriv_eq a ha k z hz]
  simp only [scalarPowerSeries, scalarDerivCoeff_eq_descFactorial]

/-- A convenient fourth-derivative specialization for the separated kernel. -/
theorem scalarPowerSeries_fourthDeriv_eq (a : ℕ → ℝ)
    (ha : ∀ m, |a m| ≤ 1) (z : ℝ)
    (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
    iteratedDeriv 4 (scalarPowerSeries a) z =
      ∑' m : ℕ, (((m + 4).descFactorial 4 : ℕ) : ℝ) * a (m + 4) * z ^ m := by
  rw [scalarPowerSeries_iteratedDeriv_eq a ha 4 z hz]
  simp only [scalarPowerSeries, scalarDerivCoeff_eq_descFactorial]

end BEMOC.Definitive
