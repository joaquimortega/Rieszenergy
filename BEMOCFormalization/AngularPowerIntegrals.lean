import Mathlib

/-!
Elementary angular inverse-power integrals used in the regular-block estimates.
-/

namespace BEMOC.Definitive

open MeasureTheory

private lemma angular_kernel_intervalIntegrable {α δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => (δ ^ 2 + θ ^ 2) ^ ((α - 4) / 2))
      volume a b := by
  apply Continuous.intervalIntegrable
  apply Continuous.rpow_const
  · fun_prop
  · intro θ
    have : 0 < δ ^ 2 + θ ^ 2 := by positivity
    exact Or.inl this.ne'

private lemma angular_kernel_pointwise_low {α δ θ : ℝ}
    (hα : α < 2) (hδ : 0 < δ) (_hθ : 0 ≤ θ) :
    (δ ^ 2 + θ ^ 2) ^ ((α - 4) / 2) ≤ δ ^ (α - 4) := by
  have hbase : δ ^ 2 ≤ δ ^ 2 + θ ^ 2 := by nlinarith [sq_nonneg θ]
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < δ ^ 2) hbase
    (by linarith : (α - 4) / 2 ≤ 0)
  convert hpow using 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
  ring

private lemma angular_kernel_pointwise_high {α δ θ : ℝ}
    (hα : α < 2) (_hδ : 0 < δ) (hθ : 0 < θ) :
    (δ ^ 2 + θ ^ 2) ^ ((α - 4) / 2) ≤ θ ^ (α - 4) := by
  have hbase : θ ^ 2 ≤ δ ^ 2 + θ ^ 2 := by nlinarith [sq_nonneg δ]
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < θ ^ 2) hbase
    (by linarith : (α - 4) / 2 ≤ 0)
  convert hpow using 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hθ.le]
  ring

private lemma angular_power_integral_bound_to {α δ b : ℝ}
    (hα : α < 2) (hδ : 0 < δ) (hb : 0 ≤ b) :
    (∫ θ in (0 : ℝ)..b, (δ ^ 2 + θ ^ 2) ^ ((α - 4) / 2)) ≤
      (1 + 1 / (3 - α)) * δ ^ (α - 3) := by
  let f : ℝ → ℝ := fun θ => (δ ^ 2 + θ ^ 2) ^ ((α - 4) / 2)
  have hf : ∀ a c : ℝ, IntervalIntegrable f volume a c :=
    fun a c => angular_kernel_intervalIntegrable hδ a c
  have hden : 0 < 3 - α := by linarith
  by_cases hbd : b ≤ δ
  · have hmono : (∫ θ in (0 : ℝ)..b, f θ) ≤ ∫ _θ in (0 : ℝ)..b, δ ^ (α - 4) :=
      intervalIntegral.integral_mono_on hb (hf 0 b) intervalIntegrable_const (by
        intro θ hθ
        exact angular_kernel_pointwise_low hα hδ hθ.1)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
    have hp : 0 ≤ δ ^ (α - 4) := le_of_lt (Real.rpow_pos_of_pos hδ _)
    have hmul : b * δ ^ (α - 4) ≤ δ * δ ^ (α - 4) :=
      mul_le_mul_of_nonneg_right hbd hp
    have heq : δ * δ ^ (α - 4) = δ ^ (α - 3) := by
      calc
        δ * δ ^ (α - 4) = δ ^ (1 : ℝ) * δ ^ (α - 4) := by rw [Real.rpow_one]
        _ = δ ^ ((1 : ℝ) + (α - 4)) := (Real.rpow_add hδ _ _).symm
        _ = δ ^ (α - 3) := by congr 1; ring
    have hconst : 0 ≤ (1 / (3 - α)) * δ ^ (α - 3) := by positivity
    nlinarith
  · have hdb : δ ≤ b := le_of_lt (lt_of_not_ge hbd)
    have hlow : (∫ θ in (0 : ℝ)..δ, f θ) ≤ δ ^ (α - 3) := by
      have hmono : (∫ θ in (0 : ℝ)..δ, f θ) ≤
          ∫ _θ in (0 : ℝ)..δ, δ ^ (α - 4) :=
        intervalIntegral.integral_mono_on hδ.le (hf 0 δ) intervalIntegrable_const (by
          intro θ hθ
          exact angular_kernel_pointwise_low hα hδ hθ.1)
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
      have heq : δ * δ ^ (α - 4) = δ ^ (α - 3) := by
        calc
          δ * δ ^ (α - 4) = δ ^ (1 : ℝ) * δ ^ (α - 4) := by rw [Real.rpow_one]
          _ = δ ^ ((1 : ℝ) + (α - 4)) := (Real.rpow_add hδ _ _).symm
          _ = δ ^ (α - 3) := by congr 1; ring
      simpa [heq] using hmono
    have hhigh : (∫ θ in δ..b, f θ) ≤ δ ^ (α - 3) / (3 - α) := by
      have hmono : (∫ θ in δ..b, f θ) ≤ ∫ θ in δ..b, θ ^ (α - 4) :=
        intervalIntegral.integral_mono_on hdb (hf δ b)
          (intervalIntegral.intervalIntegrable_rpow (Or.inr (by
            simp only [Set.uIcc_of_le hdb, Set.mem_Icc]
            intro h
            linarith [h.1]))) (by
            intro θ hθ
            exact angular_kernel_pointwise_high hα hδ (lt_of_lt_of_le hδ hθ.1))
      have hint : (∫ θ in δ..b, θ ^ (α - 4)) =
          (δ ^ (α - 3) - b ^ (α - 3)) / (3 - α) := by
        rw [integral_rpow (Or.inr ⟨by linarith, by
          simp only [Set.uIcc_of_le hdb, Set.mem_Icc]
          intro h
          linarith [h.1]⟩)]
        have : α - 4 + 1 = α - 3 := by ring
        rw [this]
        field_simp [show α - 3 ≠ 0 by linarith, show 3 - α ≠ 0 by linarith]
        ring
      rw [hint] at hmono
      have hbpow : 0 ≤ b ^ (α - 3) := le_of_lt (Real.rpow_pos_of_pos (lt_of_lt_of_le hδ hdb) _)
      apply hmono.trans
      apply div_le_div_of_nonneg_right _ hden.le
      linarith
    have hsum := intervalIntegral.integral_add_adjacent_intervals (hf 0 δ) (hf δ b)
    rw [← hsum]
    convert add_le_add hlow hhigh using 1 <;> ring

/-- Uniform inverse-power bound on an angular interval. -/
theorem angular_inverse_power_integral_bound {α δ R : ℝ}
    (_hα0 : 0 < α) (hα2 : α < 2) (hδ : 0 < δ) (hR : 0 < R) :
    (∫ θ in (0 : ℝ)..Real.pi, (δ ^ 2 + (R * θ) ^ 2) ^ ((α - 4) / 2)) ≤
      (1 + 1 / (3 - α)) * δ ^ (α - 3) / R := by
  have hscaled := angular_power_integral_bound_to hα2 hδ
    (show 0 ≤ R * Real.pi by positivity)
  have hsubst : R * (∫ θ in (0 : ℝ)..Real.pi,
      (δ ^ 2 + (R * θ) ^ 2) ^ ((α - 4) / 2)) =
      ∫ t in (0 : ℝ)..R * Real.pi, (δ ^ 2 + t ^ 2) ^ ((α - 4) / 2) := by
    simpa only [mul_zero] using
      (intervalIntegral.mul_integral_comp_mul_left
        (f := fun t : ℝ => (δ ^ 2 + t ^ 2) ^ ((α - 4) / 2))
        (c := R) (a := 0) (b := Real.pi))
  rw [← hsubst] at hscaled
  exact (le_div_iff₀ hR).2 (by simpa only [mul_comm] using hscaled)

/-- The same estimate with the square of the scale expanded. -/
theorem angular_inverse_power_integral_bound' {α δ R : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hδ : 0 < δ) (hR : 0 < R) :
    (∫ θ in (0 : ℝ)..Real.pi, (δ ^ 2 + R ^ 2 * θ ^ 2) ^ ((α - 4) / 2)) ≤
      (1 + 1 / (3 - α)) * δ ^ (α - 3) / R := by
  simpa only [mul_pow] using angular_inverse_power_integral_bound hα0 hα2 hδ hR

/-- The unscaled angular estimate. -/
theorem angular_inverse_power_integral_bound_unscaled {α δ : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hδ : 0 < δ) :
    (∫ θ in (0 : ℝ)..Real.pi, (δ ^ 2 + θ ^ 2) ^ ((α - 4) / 2)) ≤
      (1 + 1 / (3 - α)) * δ ^ (α - 3) := by
  simpa using angular_inverse_power_integral_bound hα0 hα2 hδ zero_lt_one

/-- The singular angular tail starts at reciprocal scale. -/
theorem truncated_angular_power_integral_bound {α r : ℝ}
    (_hα0 : 0 < α) (hα2 : α < 2) (hr : 1 ≤ r) :
    (∫ θ in r⁻¹..Real.pi, θ ^ (α - 4)) ≤
      (1 / (3 - α)) * r ^ (3 - α) := by
  have hrpos : 0 < r := by linarith
  have hri : 0 < r⁻¹ := inv_pos.mpr hrpos
  have hle : r⁻¹ ≤ Real.pi := by
    have hri1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
    have hpi : (1 : ℝ) ≤ Real.pi := by
      have := Real.pi_gt_three
      linarith
    exact hri1.trans hpi
  have hden : 0 < 3 - α := by linarith
  have hint : (∫ θ in r⁻¹..Real.pi, θ ^ (α - 4)) =
      ((r⁻¹) ^ (α - 3) - Real.pi ^ (α - 3)) / (3 - α) := by
    rw [integral_rpow (Or.inr ⟨by linarith, by
      simp only [Set.uIcc_of_le hle, Set.mem_Icc]
      intro h
      linarith [h.1]⟩)]
    have : α - 4 + 1 = α - 3 := by ring
    rw [this]
    field_simp [show α - 3 ≠ 0 by linarith, show 3 - α ≠ 0 by linarith]
    ring
  rw [hint]
  have hpow : (r⁻¹) ^ (α - 3) = r ^ (3 - α) := by
    rw [Real.inv_rpow hrpos.le]
    rw [← Real.rpow_neg hrpos.le]
    congr 1
    ring
  rw [hpow]
  have hpipow : 0 ≤ Real.pi ^ (α - 3) := by positivity
  apply (div_le_div_of_nonneg_right (sub_le_self _ hpipow) hden.le).trans
  simp [div_eq_mul_inv, mul_comm]

/-- Positivity of the reciprocal-scale angular tail. -/
theorem truncated_angular_power_integral_nonneg {α r : ℝ}
    (_hα0 : 0 < α) (_hα2 : α < 2) (hr : 1 ≤ r) :
    0 ≤ ∫ θ in r⁻¹..Real.pi, θ ^ (α - 4) := by
  have hri : 0 < r⁻¹ := inv_pos.mpr (by linarith)
  have hle : r⁻¹ ≤ Real.pi := by
    have := inv_le_one_of_one_le₀ hr
    have hpi := Real.pi_gt_three
    linarith
  exact intervalIntegral.integral_nonneg hle (by
    intro θ hθ
    exact Real.rpow_nonneg (le_trans hri.le hθ.1) _)

end BEMOC.Definitive
