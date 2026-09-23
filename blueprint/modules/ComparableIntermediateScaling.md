# Comparable intermediate scaling

The angular fourth-derivative integral contributes five inverse radius powers. These cancel five of the six population powers in the cubic Taylor prefactor. This module proves the exact scalar identity and restores the fixed geometric constants, yielding the manuscript's comparable weight for all gaps at least two.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.ComparablePowerScaling

namespace BEMOC.Definitive

/-- Exact cancellation of the radial and angular scales in the intermediate
comparable regime. -/
theorem comparable_intermediate_power_identity
    (α M r r' ℓ : ℝ) (hM : 0 < M) (hr : 0 < r) (hℓ : 0 < ℓ) :
    r ^ 3 * r' ^ 3 / M ^ 8 * (r / M) ^ (-5 : ℝ) *
        (ℓ / M) ^ (α - 3) =
      (r' ^ 3 / r ^ 2) / M ^ α * ℓ ^ (α - 3) := by
  have hR : 0 < r / M := div_pos hr hM
  rw [Real.div_rpow hr.le hM.le, Real.div_rpow hℓ.le hM.le]
  rw [Real.rpow_neg hr.le, Real.rpow_neg hM.le]
  rw [show (r : ℝ) ^ (5 : ℝ) = r ^ 5 by norm_cast]
  rw [show (M : ℝ) ^ (5 : ℝ) = M ^ 5 by norm_cast]
  have hMpow : M ^ (α - 3) = M ^ α / M ^ 3 := by
    rw [Real.rpow_sub hM]
    norm_cast
  rw [hMpow]
  have hm5 : M ^ 5 ≠ 0 := pow_ne_zero _ hM.ne'
  have hm3 : M ^ 3 ≠ 0 := pow_ne_zero _ hM.ne'
  have hm8 : M ^ 8 ≠ 0 := pow_ne_zero _ hM.ne'
  have hr5 : r ^ 5 ≠ 0 := pow_ne_zero _ hr.ne'
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero _ hr.ne'
  have hmα : M ^ α ≠ 0 := (Real.rpow_pos_of_pos hM _).ne'
  field_simp
  ring

/-- The comparable partner's population leaves one power of the first
population after five radial powers cancel. -/
theorem comparable_intermediate_population_power
    {r r' : ℝ} (hr : 0 < r) (hr' : 0 ≤ r')
    (hr'le : r' ≤ 8 * r) :
    r' ^ 3 / r ^ 2 ≤ 512 * r := by
  have hpow : r' ^ 3 ≤ 512 * r ^ 3 := by
    have h := pow_le_pow_left₀ hr' hr'le 3
    nlinarith
  apply (div_le_iff₀ (sq_pos_of_pos hr)).2
  nlinarith

/-- Scalar conversion for intermediate blocks, before fixed geometric
constants from the angular model are inserted. -/
theorem comparable_intermediate_power_scaling
    {α M r r' ℓ : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hM : 16 ≤ M) (hr : 0 < r) (hr' : 0 ≤ r')
    (hr'le : r' ≤ 8 * r) (hℓ : 2 ≤ ℓ) :
    r ^ 3 * r' ^ 3 / M ^ 8 * (r / M) ^ (-5 : ℝ) *
        (ℓ / M) ^ (α - 3) ≤
      4096 * (r / M ^ α) * (1 + ℓ) ^ (α - 3) := by
  have hM0 : 0 < M := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  rw [comparable_intermediate_power_identity α M r r' ℓ hM0 hr hℓ0]
  have hpop := comparable_intermediate_population_power hr hr' hr'le
  have hidx := comparable_far_index_power hα0 hα2 hℓ
  have hℓpow : 0 ≤ ℓ ^ (α - 3) := Real.rpow_nonneg hℓ0.le _
  have hMpow : 0 < M ^ α := Real.rpow_pos_of_pos hM0 _
  calc
    r' ^ 3 / r ^ 2 / M ^ α * ℓ ^ (α - 3) ≤
        512 * r / M ^ α * ℓ ^ (α - 3) := by
      gcongr
    _ ≤ 4096 * (r / M ^ α) * (1 + ℓ) ^ (α - 3) := by
      have h := mul_le_mul_of_nonneg_left hidx
        (show 0 ≤ 512 * (r / M ^ α) by positivity)
      convert h using 1 <;> ring

/-- Restore the fixed geometric constants in the scaled angular integral. -/
theorem comparable_intermediate_fixed_factors
    {α R d A : ℝ} (hR : 0 < R) (hd : 0 < d) :
    A * (R / 240) ^ (-4 : ℝ) *
        ((d / 60) ^ (α - 3) / (R / 180)) =
      (180 * 240 ^ 4 * 60 ^ (3 - α)) *
        (A * R ^ (-5 : ℝ) * d ^ (α - 3)) := by
  have h240 : (0 : ℝ) < 240 := by norm_num
  have h60 : (0 : ℝ) < 60 := by norm_num
  rw [Real.div_rpow hR.le h240.le, Real.div_rpow hd.le h60.le]
  rw [Real.rpow_neg hR.le, Real.rpow_neg h240.le]
  rw [show (60 : ℝ) ^ (α - 3) = ((60 : ℝ) ^ (3 - α))⁻¹ by
    rw [show α - 3 = -(3 - α) by ring, Real.rpow_neg h60.le]]
  rw [Real.rpow_neg hR.le]
  have hR4 : R ^ 4 ≠ 0 := pow_ne_zero _ hR.ne'
  have hR5 : R ^ 5 ≠ 0 := pow_ne_zero _ hR.ne'
  have h60pow : (60 : ℝ) ^ (3 - α) ≠ 0 := (Real.rpow_pos_of_pos h60 _).ne'
  field_simp
  have hp : R ^ (5 : ℝ) = R ^ (4 : ℝ) * R := by
    rw [show (5 : ℝ) = 4 + 1 by norm_num, Real.rpow_add hR]
    simp
  rw [hp]
  ring

/-- The full numerical conversion needed after the intermediate angular
integral and fourth-order Taylor estimate. -/
theorem comparable_intermediate_full_scaling
    {α M r r' ℓ : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hM : 16 ≤ M) (hr : 0 < r) (hr' : 0 ≤ r')
    (hr'le : r' ≤ 8 * r) (hℓ : 2 ≤ ℓ) :
    r ^ 3 * r' ^ 3 / M ^ 8 * ((r / M) / 240) ^ (-4 : ℝ) *
        (((ℓ / M) / 60) ^ (α - 3) / ((r / M) / 180)) ≤
      (4096 * 180 * 240 ^ 4 * 60 ^ (3 - α)) *
        (r / M ^ α) * (1 + ℓ) ^ (α - 3) := by
  have hM0 : 0 < M := by linarith
  have hR : 0 < r / M := div_pos hr hM0
  have hd : 0 < ℓ / M := div_pos (by linarith) hM0
  rw [comparable_intermediate_fixed_factors hR hd]
  have hsc := comparable_intermediate_power_scaling hα0 hα2 hM hr hr' hr'le hℓ
  have hcoeff : 0 ≤ (180 : ℝ) * 240 ^ 4 * 60 ^ (3 - α) := by positivity
  have h := mul_le_mul_of_nonneg_left hsc hcoeff
  convert h using 1 <;> ring

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
