import BEMOCFormalization.EulerPower
import Mathlib

/-!
# Identifying the finite-part power-sum constant with Riemann zeta

This module isolates the analytic identification still needed for the
general-`α` Euler--Maclaurin theorem as an equality of two explicit,
absolutely convergent series.
-/

open scoped BigOperators Topology Real
open Filter Set

namespace PowerZetaIdentification

noncomputable def positiveZetaSeries (α : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + α)

noncomputable def zetaFunctionalCoefficient (α : ℝ) : ℝ :=
  2 * (2 * Real.pi) ^ (-(1 + α)) * Real.Gamma (1 + α) *
    Real.cos (Real.pi * (1 + α) / 2) * positiveZetaSeries α

theorem summable_positiveZetaSeries {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + α)) := by
  have hraw : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + α))) :=
    Real.summable_nat_rpow.mpr (by linarith : -(1 + α) < -1)
  have hshift := (summable_nat_add_iff 1).2 hraw
  refine hshift.congr (fun n => ?_)
  rw [Real.rpow_neg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]
  simp only [one_div]

theorem riemannZeta_one_add_real_eq_ofReal_tsum {α : ℝ} (hα : 0 < α) :
    riemannZeta ((1 + α : ℝ) : ℂ) = (positiveZetaSeries α : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow]
  · rw [positiveZetaSeries, Complex.ofReal_tsum]
    congr 1
    funext n
    rw [Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_cpow (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]
    norm_num
  · norm_num
    linarith

theorem riemannZeta_neg_real_functional_equation {α : ℝ} (hα : 0 < α) :
    riemannZeta (-(α : ℂ)) =
      2 * (2 * (Real.pi : ℂ)) ^ (-((1 + α : ℝ) : ℂ)) *
        Complex.Gamma ((1 + α : ℝ) : ℂ) *
        Complex.cos ((Real.pi : ℂ) * ((1 + α : ℝ) : ℂ) / 2) *
        riemannZeta ((1 + α : ℝ) : ℂ) := by
  have hs (n : ℕ) : ((1 + α : ℝ) : ℂ) ≠ -(n : ℂ) := by
    intro hn
    have hr := congrArg Complex.re hn
    norm_num at hr
    linarith
  have hs1 : ((1 + α : ℝ) : ℂ) ≠ 1 := by
    intro hn
    have hr := congrArg Complex.re hn
    norm_num at hr
    linarith
  have harg : (1 : ℂ) - ((1 + α : ℝ) : ℂ) = -(α : ℂ) := by
    push_cast
    ring
  rw [← harg]
  exact riemannZeta_one_sub (s := ((1 + α : ℝ) : ℂ)) hs hs1

/-- Checked functional-equation evaluation of the zeta side of the target. -/
theorem riemannZeta_neg_eq_ofReal_coefficient {α : ℝ} (hα : 0 < α) :
    riemannZeta (-(α : ℂ)) = (zetaFunctionalCoefficient α : ℂ) := by
  rw [riemannZeta_neg_real_functional_equation hα,
    riemannZeta_one_add_real_eq_ofReal_tsum hα]
  have hbase : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    rfl
  have hexp : -((1 + α : ℝ) : ℂ) = ((-(1 + α) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hcosarg :
      (Real.pi : ℂ) * ((1 + α : ℝ) : ℂ) / 2 =
        ((Real.pi * (1 + α) / 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hbase, hexp, hcosarg]
  rw [← Complex.ofReal_cpow (by positivity : 0 ≤ 2 * Real.pi),
    Complex.Gamma_ofReal, ← Complex.ofReal_cos]
  unfold zetaFunctionalCoefficient
  norm_cast

theorem riemannZeta_neg_re_eq_coefficient {α : ℝ} (hα : 0 < α) :
    (riemannZeta ((-α : ℝ) : ℂ)).re = zetaFunctionalCoefficient α := by
  rw [show (((-α : ℝ) : ℂ)) = -(α : ℂ) by push_cast; rfl]
  rw [riemannZeta_neg_eq_ofReal_coefficient hα]
  rfl

/-! ## An exact convergent real-series form of the power-sum side -/

theorem renormalizedPowerSum_one {α : ℝ} :
    EulerPower.renormalizedPowerSum α 1 =
      -1 / (α + 1) + 1 / 2 - α / 12 := by
  unfold EulerPower.renormalizedPowerSum EulerPower.powerSum
  simp [Real.one_rpow]
  ring

theorem powerSumConstant_eq_increment_series {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    EulerPower.powerSumConstant α =
      -1 / (α + 1) + 1 / 2 - α / 12 +
        ∑' n : ℕ, EulerPower.powerSumIncrement α (n + 1) := by
  have hs := EulerPower.summable_powerSumIncrement α hα0 hα2
  rw [EulerPower.powerSumConstant, hs.tsum_eq_zero_add,
    EulerPower.powerSumIncrement, renormalizedPowerSum_one]
  ring

theorem shifted_powerSumIncrement_eq_localIncrement {α : ℝ} (hα : 0 < α) (n : ℕ) :
    EulerPower.powerSumIncrement α (n + 1) =
      ((n + 1 : ℕ) : ℝ) ^ α *
        EulerPower.localIncrement α (1 / ((n + 1 : ℕ) : ℝ)) := by
  apply EulerPower.powerSumIncrement_eq_rpow_mul_localIncrement
  · linarith
  · omega

theorem summable_localIncrement_series {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ α *
      EulerPower.localIncrement α (1 / ((n + 1 : ℕ) : ℝ))) := by
  have hs := (EulerPower.summable_powerSumIncrement α hα0 hα2).comp_injective
    (show Function.Injective (fun n : ℕ => n + 1) by
      intro m n h
      exact Nat.add_right_cancel h)
  exact hs.congr (fun n => shifted_powerSumIncrement_eq_localIncrement hα0 n)

/-- The finite-part constant is reduced to an absolutely convergent series of
third-order local Euler--Maclaurin remainders. -/
theorem powerSumConstant_eq_localIncrement_series {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    EulerPower.powerSumConstant α =
      -1 / (α + 1) + 1 / 2 - α / 12 +
        ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ α *
          EulerPower.localIncrement α (1 / ((n + 1 : ℕ) : ℝ)) := by
  rw [powerSumConstant_eq_increment_series hα0 hα2]
  congr 1
  apply tsum_congr
  exact shifted_powerSumIncrement_eq_localIncrement hα0

/-- Exact reduction of the requested identification to one explicit,
absolutely convergent Euler--Maclaurin/Bernoulli series identity. -/
theorem powerSumConstant_eq_riemannZeta_re_iff {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    EulerPower.powerSumConstant α = (riemannZeta ((-α : ℝ) : ℂ)).re ↔
      -1 / (α + 1) + 1 / 2 - α / 12 +
          ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ α *
            EulerPower.localIncrement α (1 / ((n + 1 : ℕ) : ℝ)) =
        zetaFunctionalCoefficient α := by
  rw [powerSumConstant_eq_localIncrement_series hα0 hα2,
    riemannZeta_neg_re_eq_coefficient hα0]

/-! ## Fully closed special case `α = 1` -/

theorem riemannZeta_neg_one_re :
    (riemannZeta ((-(1 : ℝ) : ℝ) : ℂ)).re = -1 / 12 := by
  rw [show (((-(1 : ℝ) : ℝ) : ℂ)) = -(1 : ℕ) by norm_num,
    riemannZeta_neg_nat_eq_bernoulli' 1, bernoulli'_two]
  norm_num

theorem powerSumConstant_eq_riemannZeta_re_one :
    EulerPower.powerSumConstant 1 =
      (riemannZeta ((-(1 : ℝ) : ℝ) : ℂ)).re := by
  rw [EulerPower.powerSumConstant_one, riemannZeta_neg_one_re]

end PowerZetaIdentification
