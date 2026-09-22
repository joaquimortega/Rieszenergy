import BEMOCFormalization.PowerZeta

open scoped BigOperators Topology
open Filter

namespace ComplexFinitePart

/-- The order-two Euler--Maclaurin finite approximation to `ζ(s)`.

At `s = -α` this is the corrected power sum used in `EulerPower`; as a
function of `s`, it is the natural family to continue from `Re(s) > 1`.
-/
noncomputable def zetaFiniteApprox (s : ℂ) (N : ℕ) : ℂ :=
  (∑ k ∈ Finset.Ico 1 N, (k : ℂ) ^ (-s)) -
      (N : ℂ) ^ (1 - s) / (1 - s) +
    (1 / 2 : ℂ) * (N : ℂ) ^ (-s) +
    s / 12 * (N : ℂ) ^ (-s - 1)

theorem zetaFiniteApprox_neg_real (α : ℝ) (N : ℕ) :
    zetaFiniteApprox (-((α : ℝ) : ℂ)) N =
      (EulerPower.renormalizedPowerSum α N : ℂ) := by
  unfold zetaFiniteApprox EulerPower.renormalizedPowerSum EulerPower.powerSum
  have hN : 0 ≤ (N : ℝ) := by positivity
  have hk (k : ℕ) : 0 ≤ (k : ℝ) := by positivity
  simp_rw [show -(-((α : ℝ) : ℂ)) = (α : ℂ) by ring]
  rw [show (1 : ℂ) - -((α : ℝ) : ℂ) = ((α + 1 : ℝ) : ℂ) by push_cast; ring]
  push_cast
  simp_rw [Complex.ofReal_cpow (hk _)]
  norm_num
  ring

theorem tendsto_zetaFiniteApprox_neg_real {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    Tendsto (zetaFiniteApprox (-((α : ℝ) : ℂ))) atTop
      (𝓝 (EulerPower.powerSumConstant α : ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (EulerPower.tendsto_renormalizedPowerSum hα0 hα2)
  exact h.congr' (Filter.Eventually.of_forall fun N =>
    (zetaFiniteApprox_neg_real α N).symm)

end ComplexFinitePart
