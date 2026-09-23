# ComparablePowerScaling: far-block scalar conversion

`ComparablePowerScaling.lean` converts the Taylor lower scale `((ℓ/M)²/3600)^(α/2−4)` into the manuscript's comparable-block weight. The exact normalization separates the factors `3600^(4−α/2)`, `M^(−α)`, and `ℓ^(α−8)`. The assumptions `r'≤8r` and `2r<ℓ` absorb five radius powers; `ℓ≥2` converts `ℓ^(α−3)` to `(1+ℓ)^(α−3)` with factor eight. The resulting theorem uses the explicit constant `128*3600^(4−α/2)`.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import Mathlib

/-! Scalar real-power conversion for separated comparable bands. -/

namespace BEMOC.Definitive

/-- Normalize the Taylor lower scale into population and index powers. -/
theorem comparable_far_power_identity
    (α M r r' ℓ : ℝ) (hM : 0 < M) (hℓ : 0 < ℓ) :
    r ^ 3 * r' ^ 3 / M ^ 8 *
        (((ℓ / M) ^ 2 / 3600) ^ (α / 2 - 4)) =
      3600 ^ (4 - α / 2) * (r ^ 3 * r' ^ 3) /
        M ^ α * ℓ ^ (α - 8) := by
  have hx : 0 < ℓ / M := div_pos hℓ hM
  have h3600 : (0 : ℝ) < 3600 := by norm_num
  rw [Real.div_rpow (sq_nonneg _) h3600.le]
  rw [← Real.rpow_two (ℓ / M), ← Real.rpow_mul hx.le]
  rw [show (2 : ℝ) * (α / 2 - 4) = α - 8 by ring]
  rw [Real.div_rpow hℓ.le hM.le]
  have hMpow : M ^ (α - 8) = M ^ α / M ^ 8 := by
    calc
      M ^ (α - 8) = M ^ α / M ^ (8 : ℝ) := Real.rpow_sub hM _ _
      _ = M ^ α / M ^ 8 :=
        congrArg (fun z : ℝ => M ^ α / z) (Real.rpow_natCast M 8)
  have h3600pow : (3600 : ℝ) ^ (α / 2 - 4) =
      ((3600 : ℝ) ^ (4 - α / 2))⁻¹ := by
    rw [show α / 2 - 4 = -(4 - α / 2) by ring,
      Real.rpow_neg h3600.le]
  rw [hMpow, h3600pow]
  have hM8 : M ^ 8 ≠ 0 := pow_ne_zero _ hM.ne'
  have hMα : M ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hM _)
  have hC : (3600 : ℝ) ^ (4 - α / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos h3600 _)
  field_simp
  ring

/-- The far-band geometry absorbs five powers of the smaller radius. -/
theorem comparable_far_population_power
    {r r' ℓ : ℝ} (hr : 0 < r) (hr' : 0 ≤ r')
    (hr'le : r' ≤ 8 * r) (hℓ : 2 * r < ℓ) :
    r ^ 3 * r' ^ 3 ≤ 16 * r * ℓ ^ 5 := by
  have hr3 : 0 ≤ r ^ 3 := pow_nonneg hr.le _
  have hr'3 : r' ^ 3 ≤ 512 * r ^ 3 := by
    have h := pow_le_pow_left₀ hr' hr'le 3
    nlinarith
  have hr5 : 32 * r ^ 5 ≤ ℓ ^ 5 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * r) hℓ.le 5
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_left hr'3 hr3
  have hsecond := mul_le_mul_of_nonneg_left hr5 hr.le
  nlinarith [sq_nonneg (r ^ 3)]

/-- Replace the positive index gap by the manuscript's `1+gap` weight. -/
theorem comparable_far_index_power
    {α ℓ : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hℓ : 2 ≤ ℓ) :
    ℓ ^ (α - 3) ≤ 8 * (1 + ℓ) ^ (α - 3) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hstep : (2 * ℓ) ^ (α - 3) ≤ (1 + ℓ) ^ (α - 3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have h2 : (1 / 8 : ℝ) ≤ 2 ^ (α - 3) := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by linarith : (-3 : ℝ) ≤ α - 3)
    norm_num at h ⊢
    exact h
  have hmul : (1 / 8 : ℝ) * ℓ ^ (α - 3) ≤
      2 ^ (α - 3) * ℓ ^ (α - 3) :=
    mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hℓ0.le _)
  rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hℓ0.le] at hmul
  nlinarith [hstep]

/-- Exact scalar conversion from the far Taylor estimate to the comparable
block rate. -/
theorem comparable_far_power_scaling
    {α M r r' ℓ : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hM : 16 ≤ M) (hr : 0 < r) (hr' : 0 ≤ r')
    (hr'le : r' ≤ 8 * r) (hfar : 2 * r < ℓ) (hℓ : 2 ≤ ℓ) :
    r ^ 3 * r' ^ 3 / M ^ 8 *
        (((ℓ / M) ^ 2 / 3600) ^ (α / 2 - 4)) ≤
      (128 * 3600 ^ (4 - α / 2)) *
        (r / M ^ α) * (1 + ℓ) ^ (α - 3) := by
  have hM0 : 0 < M := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  rw [comparable_far_power_identity α M r r' ℓ hM0 hℓ0]
  have hpop := comparable_far_population_power hr hr' hr'le hfar
  have hidx := comparable_far_index_power hα0 hα2 hℓ
  have hℓpow : 0 ≤ ℓ ^ (α - 8) := Real.rpow_nonneg hℓ0.le _
  have hMpow : 0 < M ^ α := Real.rpow_pos_of_pos hM0 _
  have hC : 0 ≤ (3600 : ℝ) ^ (4 - α / 2) := by positivity
  have hpowid : ℓ ^ 5 * ℓ ^ (α - 8) = ℓ ^ (α - 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hℓ0]
    congr 1
    ring
  have hscaled : (r ^ 3 * r' ^ 3) * ℓ ^ (α - 8) ≤
      128 * r * (1 + ℓ) ^ (α - 3) := by
    calc
      _ ≤ (16 * r * ℓ ^ 5) * ℓ ^ (α - 8) :=
        mul_le_mul_of_nonneg_right hpop hℓpow
      _ = 16 * r * ℓ ^ (α - 3) := by rw [mul_assoc, hpowid]
      _ ≤ 128 * r * (1 + ℓ) ^ (α - 3) := by
        nlinarith [mul_le_mul_of_nonneg_left hidx (show 0 ≤ 16 * r by positivity)]
  calc
    3600 ^ (4 - α / 2) * (r ^ 3 * r' ^ 3) / M ^ α * ℓ ^ (α - 8) =
        (3600 ^ (4 - α / 2) / M ^ α) *
          ((r ^ 3 * r' ^ 3) * ℓ ^ (α - 8)) := by ring
    _ ≤ (3600 ^ (4 - α / 2) / M ^ α) *
          (128 * r * (1 + ℓ) ^ (α - 3)) :=
        mul_le_mul_of_nonneg_left hscaled (div_nonneg hC hMpow.le)
    _ = (128 * 3600 ^ (4 - α / 2)) *
          (r / M ^ α) * (1 + ℓ) ^ (α - 3) := by ring

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
