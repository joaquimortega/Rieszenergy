import Mathlib

namespace BEMOC.Definitive

theorem near_tail_radius_denominator (r M : ℝ) :
    r / (240 * M) = (r / M) / 240 := by ring

/-- Separate the radial and angular powers in the near-tail fourth derivative. -/
theorem near_tail_pointwise_power_identity
    {α R θ : ℝ} (hR : 0 < R) (hθ : 0 < θ) :
    (R * θ) ^ (α - 4) / (R / 240) ^ 4 =
      240 ^ 4 * R ^ (α - 8) * θ ^ (α - 4) := by
  rw [Real.mul_rpow hR.le hθ.le, div_pow]
  have hpow : R ^ (α - 8) = R ^ (α - 4) / R ^ 4 := by
    rw [show α - 8 = (α - 4) - 4 by ring,
      Real.rpow_sub hR]
    norm_cast
  rw [hpow]
  have hR4 : R ^ 4 ≠ 0 := pow_ne_zero _ hR.ne'
  norm_num
  field_simp
  ring

/-- Angular integration contributes `r^(3-α)`, leaving the exact
`M^8/(r^5 M^α)` height derivative scale. -/
theorem near_tail_integrated_power_identity
    {α r M : ℝ} (hr : 0 < r) (hM : 0 < M) :
    r ^ (3 - α) * (r / M) ^ (α - 8) =
      M ^ 8 / (r ^ 5 * M ^ α) := by
  rw [Real.div_rpow hr.le hM.le]
  have hrpow : r ^ (3 - α) * r ^ (α - 8) = (r ^ 5)⁻¹ := by
    rw [← Real.rpow_add hr,
      show (3 - α) + (α - 8) = -(5 : ℝ) by ring,
      Real.rpow_neg hr.le]
    norm_cast
  have hMpow : M ^ (α - 8) = M ^ α / M ^ 8 := by
    rw [show α - 8 = α - 8 by ring, Real.rpow_sub hM]
    norm_cast
  rw [← mul_div_assoc, hrpow, hMpow]
  have hr5 : r ^ 5 ≠ 0 := pow_ne_zero _ hr.ne'
  have hM8 : M ^ 8 ≠ 0 := pow_ne_zero _ hM.ne'
  have hMα : M ^ α ≠ 0 := (Real.rpow_pos_of_pos hM _).ne'
  field_simp

/-- Combined identity in the variables used by near polar bands. -/
theorem near_tail_full_power_identity
    {α r M θ : ℝ} (hr : 0 < r) (hM : 0 < M) (hθ : 0 < θ) :
    r ^ (3 - α) *
      (((r / M) * θ) ^ (α - 4) / ((r / M) / 240) ^ 4) =
      240 ^ 4 * (M ^ 8 / (r ^ 5 * M ^ α)) * θ ^ (α - 4) := by
  rw [near_tail_pointwise_power_identity (div_pos hr hM) hθ]
  calc
    r ^ (3 - α) * (240 ^ 4 * (r / M) ^ (α - 8) * θ ^ (α - 4)) =
        240 ^ 4 * (r ^ (3 - α) * (r / M) ^ (α - 8)) * θ ^ (α - 4) := by ring
    _ = _ := by rw [near_tail_integrated_power_identity hr hM]

end BEMOC.Definitive
