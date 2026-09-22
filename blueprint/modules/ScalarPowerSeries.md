# Scalar power-series smoothness

`BEMOCFormalization/ScalarPowerSeries.lean` isolates a generic analytic fact used by the separated-kernel proof. The real function `scalarPowerSeries a z` is the actual infinite sum `∑' m, a m * z^m`; it is not an abstract differentiable surrogate. Its hypothesis is the transparent coefficient bound `∀ m, |a m| ≤ 1`. In the present application, `a` is `separatedEvenCoefficient α`, and `abs_separatedEvenCoefficient_le_one` in `SeparatedSeriesSum.lean` supplies that hypothesis when `0 < α < 2`.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
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
```

<!-- END_LEAN_STATEMENTS -->

The proof constructs `scalarFormalSeries a : FormalMultilinearSeries ℝ ℝ ℝ` with Mathlib's `FormalMultilinearSeries.ofScalars`. Mathlib's `ofScalars_norm` identifies the norm of its degree-`m` term with `|a m|`. For every nonnegative radius `q < 1`, the norm-weighted terms are bounded by the summable geometric series `q^m`; `FormalMultilinearSeries.le_radius_of_summable_norm` therefore gives `q ≤ radius`. The ENNReal characterization `le_of_forall_nnreal_lt` then yields `1 ≤ radius`. This argument does not require ratios of adjacent coefficients, nonzero coefficients, or a closed form for the sum.

`scalarPowerSeries_eq_formal_sum` identifies the original `tsum` with the sum function attached to the formal multilinear series. It uses Mathlib's `FormalMultilinearSeries.ofScalars_sum_eq`, which evaluates the formal series term as the ordinary scalar term `a m * z^m`. Because the convergence radius is at least one, `FormalMultilinearSeries.hasFPowerSeriesOnBall` gives a power-series expansion on the radius ball. `HasFPowerSeriesOnBall.analyticOnNhd` propagates analyticity from the center to every point of the ball. The real interval `(-1,1)` lies in that ball because `|z|<1` for its points. This proves `scalarPowerSeries_analyticOnNhd` on the entire open interval, not merely near zero.

Finally, Mathlib's `AnalyticOn.contDiffOn_of_completeSpace` gives `scalarPowerSeries_contDiffOn_four`, the (C^4) regularity needed to differentiate the polar extension of the separated kernel. The analytic theorem itself is stronger and supports any later finite derivative order. The lemma does not claim uniform (C^4) estimates at the boundary `z=±1`: the separated-kernel argument must keep `|Q|<1`, or separately prove endpoint bounds where its ratio approaches the boundary.

The module's direct Mathlib dependencies are `Analysis.Analytic.OfScalars`, `Analysis.Analytic.ChangeOrigin`, and `Analysis.Calculus.ContDiff.Defs`. It has no dependency on the energy or geometry modules, and no axioms or placeholders. `lake build BEMOCFormalization.ScalarPowerSeries` checks its proof. The consuming module should combine `separatedEvenSeries_eq_ratioSeries`, the bound on `separatedEvenCoefficient`, smoothness of (U^{\alpha/2}) where (U>0), and smoothness of the ratio (Q) where its denominator is positive. The current API establishes regularity of the scalar series and leaves those chain-rule and coordinate-domain obligations to that consumer.

The module also proves an exact termwise derivative formula at every finite order, strengthening the (C^4) result. `scalarDerivCoeff a k m` is defined recursively: the order-zero coefficient is `a m`, and the next derivative coefficient at index `m` is `(m+1) * scalarDerivCoeff a k (m+1)`. The theorem `scalarDerivCoeff_eq_descFactorial` identifies it with `((m+k).descFactorial k : ℝ) * a (m+k)`. This shifted form correctly handles the low-degree terms that vanish after differentiation and avoids subtraction on natural-number exponents.

The analytic proof alone does not identify derivatives term by term, so the file gives a separate argument. `scalarPowerSeries_deriv_eq` applies `HasFPowerSeriesOnBall.fderiv` to the formal scalar series, evaluates the resulting continuous linear maps at `1`, and uses `FormalMultilinearSeries.derivSeries_coeff_one`. This yields the first derivative as `∑' m, (m+1)*a(m+1)*z^m`. To iterate, `scalarDerivCoeff_bound` proves by induction that the absolute value of an order-`k` coefficient is at most `(m+k+1)^k` when the original coefficients are bounded by one. Mathlib's polynomially weighted geometric summability, provided by `summable_separated_polynomial` in `SeparatedKernel.lean`, shows the differentiated formal series still has convergence radius at least one. The scalar first-derivative identity may therefore be applied at every stage.

For the induction on `iteratedDeriv`, two functions known equal on `(-1,1)` are eventually equal near any point of that open interval, so their ordinary derivatives agree there. The result is `scalarPowerSeries_iteratedDeriv_tsum`:

\[
 \frac{d^k}{dz^k}\sum_{j\ge0}a_j z^j
 =\sum_{m\ge0}(m+k)_{\underline{k}}a_{m+k}z^m,
 \qquad |z|<1.
\]

`scalarPowerSeries_fourthDeriv_eq` specializes to `k=4`. The implementation has no bound on `k`; this follows from the same polynomial-geometric summability argument for each fixed natural order. The new direct repository dependency on `SeparatedKernel.lean` is solely for its proved generic polynomial-geometric summability theorem. Consumers should use the fourth-order specialization or the general theorem to match differentiated series in `mixedFourth`.
