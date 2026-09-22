import BEMOCFormalization.SquareWithinRing

/-!
# Negligibility of the central midpoint ring

On the square subsequence `N = 4m²`, the central midpoint ring has exactly
`4m` points.  Its radius is at most one, so after division by the sharp
within-ring scale `m^(2-α)` its weighted contribution is `O(1/m)`.
-/

open scoped Topology
open Filter

namespace BEMOC

/-- The literal population-radius weight of the central midpoint ring on the
square subsequence. -/
noncomputable def squareCentralMidpointWeightedTerm (α : ℝ) (m : ℕ) : ℝ :=
  (bemocRingFamily (4 * m ^ 2) (Sum.inl (squareCentralBandIndex m))).radius ^ α *
    ((midpointRingPopulation (4 * m ^ 2) (squareCentralBandIndex m) : ℝ) ^
      (1 - α))

theorem squareCentralMidpointWeightedTerm_nonneg (α : ℝ) (m : ℕ) :
    0 ≤ squareCentralMidpointWeightedTerm α m := by
  exact mul_nonneg
    (Real.rpow_nonneg
      (bemocRingFamily (4 * m ^ 2)
        (Sum.inl (squareCentralBandIndex m))).radius_nonneg α)
    (Real.rpow_nonneg (Nat.cast_nonneg _) (1 - α))

theorem squareCentralMidpointWeightedTerm_div_scale_eventually_le
    {α : ℝ} (hα0 : 0 < α) :
    ∀ᶠ m : ℕ in atTop,
      squareCentralMidpointWeightedTerm α m / (m : ℝ) ^ (2 - α) ≤
        (4 : ℝ) ^ (1 - α) / (m : ℝ) := by
  filter_upwards [eventually_atTop.2 ⟨2, fun m hm ↦ hm⟩] with m hm
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hr0 : 0 ≤
      (bemocRingFamily (4 * m ^ 2)
        (Sum.inl (squareCentralBandIndex m))).radius :=
    OccupiedRing.radius_nonneg _
  have hr1 :
      (bemocRingFamily (4 * m ^ 2)
        (Sum.inl (squareCentralBandIndex m))).radius ≤ 1 :=
    OccupiedRing.radius_le_one _
  have hrpow :
      (bemocRingFamily (4 * m ^ 2)
        (Sum.inl (squareCentralBandIndex m))).radius ^ α ≤ 1 := by
    simpa using Real.rpow_le_one hr0 hr1 hα0.le
  rw [squareCentralMidpointWeightedTerm,
    square_midpointRingPopulation_central hm]
  have hpop : ((4 * m : ℕ) : ℝ) = (4 : ℝ) * (m : ℝ) := by norm_num
  rw [hpop, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hmR.le]
  have hden : 0 < (m : ℝ) ^ (2 - α) := Real.rpow_pos_of_pos hmR _
  calc
    (_ ^ α * ((4 : ℝ) ^ (1 - α) * (m : ℝ) ^ (1 - α))) /
          (m : ℝ) ^ (2 - α)
        ≤ (1 * ((4 : ℝ) ^ (1 - α) * (m : ℝ) ^ (1 - α))) /
          (m : ℝ) ^ (2 - α) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul_of_nonneg_right hrpow
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg hmR.le _))
    _ = (4 : ℝ) ^ (1 - α) / (m : ℝ) := by
      rw [show (2 - α : ℝ) = (1 - α) + 1 by ring,
        Real.rpow_add hmR]
      field_simp [hmR.ne', (Real.rpow_pos_of_pos hmR (1 - α)).ne']
      ring

/-- The central midpoint ring is negligible at the sharp square
within-ring scale. -/
theorem tendsto_squareCentralMidpointWeightedTerm_div_scale
    {α : ℝ} (hα0 : 0 < α) (_hα2 : α < 2) :
    Tendsto
      (fun m : ℕ ↦ squareCentralMidpointWeightedTerm α m /
        (m : ℝ) ^ (2 - α))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun m ↦
      div_nonneg (squareCentralMidpointWeightedTerm_nonneg α m)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact squareCentralMidpointWeightedTerm_div_scale_eventually_le hα0
  · exact tendsto_const_div_atTop_nhds_zero_nat ((4 : ℝ) ^ (1 - α))

end BEMOC
