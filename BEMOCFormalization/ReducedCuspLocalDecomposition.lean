import BEMOCFormalization.ReducedCuspDerivatives
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Local subtraction for the reduced latitude cusp

This file begins a direct-integral proof of the local expansion (5.4).
For `1 < α < 2`, the second derivative of the reduced cusp is integrable
at the origin.  We therefore define the constant and linear analytic
coefficients by actual convergent interval integrals and prove that the
remaining quotient by `x^((1+α)/2)` is uniformly bounded on `(0,1]`.

No asymptotic coefficient or regularity premise is assumed.
-/

open MeasureTheory Set
open scoped Interval

namespace BEMOC

set_option maxHeartbeats 1200000

noncomputable def reducedCuspD2ZeroExtension (α x : ℝ) : ℝ :=
  if 0 < x then reducedLatitudeCuspD2Value α x else 0

noncomputable def reducedCuspUpperNu (α : ℝ) : ℝ :=
  (1 + α) / 2

noncomputable def reducedCuspD2MajorantCoefficient (α : ℝ) : ℝ :=
  |(α / 2) * (α / 2 - 1)| *
    (Real.pi / (2 * Real.sqrt 2))

theorem reducedCuspD2MajorantCoefficient_nonneg (α : ℝ) :
    0 ≤ reducedCuspD2MajorantCoefficient α := by
  unfold reducedCuspD2MajorantCoefficient
  positivity

private theorem continuousOn_reducedLatitudeCuspD2Value_pos
    (α : ℝ) :
    ContinuousOn (reducedLatitudeCuspD2Value α) (Ioi 0) := by
  intro x hx
  exact (hasDerivAt_reducedLatitudeCuspD2Value
    (α := α) hx).continuousAt.continuousWithinAt

private theorem aestronglyMeasurable_reducedCuspD2ZeroExtension
    (α : ℝ) :
    AEStronglyMeasurable (reducedCuspD2ZeroExtension α) volume := by
  have hpos :
      AEStronglyMeasurable (reducedLatitudeCuspD2Value α)
        (volume.restrict (Ioi 0)) :=
    (continuousOn_reducedLatitudeCuspD2Value_pos α).aestronglyMeasurable
      measurableSet_Ioi
  have hzero :
      AEStronglyMeasurable (fun _ : ℝ ↦ (0 : ℝ))
        (volume.restrict (Ioi (0 : ℝ))ᶜ) :=
    aestronglyMeasurable_const
  have hp := hpos.piecewise measurableSet_Ioi hzero
  simpa [reducedCuspD2ZeroExtension, Set.piecewise] using hp

/-- In the upper nonresonant range the zero extension of the second
derivative is genuinely integrable at the cusp point. -/
theorem intervalIntegrable_reducedCuspD2ZeroExtension
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    IntervalIntegrable (reducedCuspD2ZeroExtension α) volume 0 1 := by
  let ν := reducedCuspUpperNu α
  let A := reducedCuspD2MajorantCoefficient α
  have hν : 1 < ν := by
    dsimp [ν, reducedCuspUpperNu]
    linarith
  have hexp : -1 < ν - 2 := by linarith
  have hmajor :
      IntervalIntegrable (fun x : ℝ ↦ A * x ^ (ν - 2))
        volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hexp).const_mul A
  apply hmajor.mono_fun
  · exact
      (aestronglyMeasurable_reducedCuspD2ZeroExtension α).mono_measure
        (Measure.restrict_le_self)
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    have hraw :=
      abs_reducedLatitudeCuspD2Value_le_rpow hx0 hα2.le
    have hrewrite :
        α / 2 - 3 / 2 = ν - 2 := by
      dsimp [ν, reducedCuspUpperNu]
      ring
    simp only [Real.norm_eq_abs]
    rw [reducedCuspD2ZeroExtension, if_pos hx0]
    rw [hrewrite] at hraw
    rw [abs_of_nonneg (mul_nonneg
      (reducedCuspD2MajorantCoefficient_nonneg α)
      (Real.rpow_nonneg hx0.le _))]
    simpa [A, reducedCuspD2MajorantCoefficient] using hraw

noncomputable def reducedCuspUpperLinearCoefficient (α : ℝ) : ℝ :=
  reducedLatitudeCuspD1Value α 1 -
    ∫ y in (0 : ℝ)..1, reducedCuspD2ZeroExtension α y

/-- The derivative after subtraction of its limiting linear coefficient. -/
noncomputable def reducedCuspUpperD1Remainder (α x : ℝ) : ℝ :=
  if 0 < x then
    reducedLatitudeCuspD1Value α x -
      reducedCuspUpperLinearCoefficient α
  else 0

private theorem intervalIntegrable_reducedLatitudeCuspD2Value_pos
    {α a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (reducedLatitudeCuspD2Value α) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  exact (continuousOn_reducedLatitudeCuspD2Value_pos α).mono
    (fun x hx ↦ ha.trans_le hx.1)

/-- Exact fundamental-theorem identity for the subtracted first
derivative. -/
theorem reducedCuspUpperD1Remainder_eq_integral
    {α x : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    reducedCuspUpperD1Remainder α x =
      ∫ y in (0 : ℝ)..x, reducedCuspD2ZeroExtension α y := by
  have hD2int :=
    intervalIntegrable_reducedCuspD2ZeroExtension hα1 hα2
  have hD2x1 :
      IntervalIntegrable (reducedCuspD2ZeroExtension α) volume x 1 :=
    hD2int.mono_set
      (uIcc_subset_uIcc (a₁ := x) (b₁ := 1)
        (a₂ := 0) (b₂ := 1)
        (by simp [hx.le, hx1]) (by simp))
  have heqOn :
      (∫ y in x..1, reducedCuspD2ZeroExtension α y) =
        ∫ y in x..1, reducedLatitudeCuspD2Value α y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx1] at hy
    have hy0 : 0 < y := hx.trans_le hy.1
    simp [reducedCuspD2ZeroExtension, hy0]
  have hFTC :
      (∫ y in x..1, reducedLatitudeCuspD2Value α y) =
        reducedLatitudeCuspD1Value α 1 -
          reducedLatitudeCuspD1Value α x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro y hy
      rw [uIcc_of_le hx1] at hy
      exact hasDerivAt_reducedLatitudeCuspD1Value
        (α := α) (hx.trans_le hy.1)
    · exact intervalIntegrable_reducedLatitudeCuspD2Value_pos hx hx1
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hD2int.mono_set
      (uIcc_subset_uIcc (a₁ := 0) (b₁ := x)
        (a₂ := 0) (b₂ := 1)
        (by simp) (by simp [hx.le, hx1])))
    hD2x1
  unfold reducedCuspUpperD1Remainder
    reducedCuspUpperLinearCoefficient
  simp only [if_pos hx]
  rw [heqOn, hFTC] at hadd
  linarith

/-- Sharp integrable power bound for the subtracted first derivative. -/
theorem abs_reducedCuspUpperD1Remainder_le
    {α x : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    |reducedCuspUpperD1Remainder α x| ≤
      (reducedCuspD2MajorantCoefficient α /
        (reducedCuspUpperNu α - 1)) *
        x ^ (reducedCuspUpperNu α - 1) := by
  let ν := reducedCuspUpperNu α
  let A := reducedCuspD2MajorantCoefficient α
  have hν : 1 < ν := by dsimp [ν, reducedCuspUpperNu]; linarith
  have hexp : -1 < ν - 2 := by linarith
  have hD2int :=
    (intervalIntegrable_reducedCuspD2ZeroExtension hα1 hα2).mono_set
      (uIcc_subset_uIcc (a₁ := 0) (b₁ := x)
        (a₂ := 0) (b₂ := 1)
        (by simp) (by simp [hx.le, hx1]))
  have hmajor :
      IntervalIntegrable (fun y : ℝ ↦ A * y ^ (ν - 2))
        volume 0 x :=
    ((intervalIntegral.intervalIntegrable_rpow' hexp).const_mul A)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (f := reducedCuspD2ZeroExtension α)
    (g := fun y : ℝ ↦ A * y ^ (ν - 2)) ?_ hmajor
  · rw [reducedCuspUpperD1Remainder_eq_integral hα1 hα2 hx hx1]
    have hnorm' :
        |∫ y in (0 : ℝ)..x, reducedCuspD2ZeroExtension α y| ≤
          |∫ y in (0 : ℝ)..x, A * y ^ (ν - 2)| := by
      simpa [Real.norm_eq_abs] using hnorm
    calc
      |∫ y in (0 : ℝ)..x, reducedCuspD2ZeroExtension α y| ≤
          |∫ y in (0 : ℝ)..x, A * y ^ (ν - 2)| := hnorm'
      _ = A / (ν - 1) * x ^ (ν - 1) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hexp)]
        have hνne : ν - 1 ≠ 0 := by linarith
        rw [show ν - 2 + 1 = ν - 1 by ring,
          Real.zero_rpow hνne, sub_zero]
        rw [abs_of_nonneg (mul_nonneg
          (reducedCuspD2MajorantCoefficient_nonneg α)
          (div_nonneg (Real.rpow_nonneg hx.le _) (by linarith)))]
        ring
      _ = _ := by rfl
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
    rw [uIoc_of_le hx.le] at hy
    have hy0 : 0 < y := hy.1
    have hraw :=
      abs_reducedLatitudeCuspD2Value_le_rpow hy0 hα2.le
    have hrewrite : α / 2 - 3 / 2 = ν - 2 := by
      dsimp [ν, reducedCuspUpperNu]
      ring
    simp only [Real.norm_eq_abs]
    rw [reducedCuspD2ZeroExtension, if_pos hy0]
    rw [hrewrite] at hraw
    simpa [A, reducedCuspD2MajorantCoefficient] using hraw

private theorem continuousOn_reducedLatitudeCuspD1Value_pos
    (α : ℝ) :
    ContinuousOn (reducedLatitudeCuspD1Value α) (Ioi 0) := by
  intro x hx
  exact (hasDerivAt_reducedLatitudeCuspD1Value
    (α := α) hx).continuousAt.continuousWithinAt

private theorem aestronglyMeasurable_reducedCuspUpperD1Remainder
    (α : ℝ) :
    AEStronglyMeasurable (reducedCuspUpperD1Remainder α) volume := by
  have hcont :
      ContinuousOn
        (fun x ↦ reducedLatitudeCuspD1Value α x -
          reducedCuspUpperLinearCoefficient α) (Ioi 0) :=
    (continuousOn_reducedLatitudeCuspD1Value_pos α).sub continuousOn_const
  have hpos :
      AEStronglyMeasurable
        (fun x ↦ reducedLatitudeCuspD1Value α x -
          reducedCuspUpperLinearCoefficient α)
        (volume.restrict (Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have hzero :
      AEStronglyMeasurable (fun _ : ℝ ↦ (0 : ℝ))
        (volume.restrict (Ioi (0 : ℝ))ᶜ) :=
    aestronglyMeasurable_const
  have hp := hpos.piecewise measurableSet_Ioi hzero
  simpa [reducedCuspUpperD1Remainder, Set.piecewise] using hp

theorem intervalIntegrable_reducedCuspUpperD1Remainder
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    IntervalIntegrable (reducedCuspUpperD1Remainder α) volume 0 1 := by
  let ν := reducedCuspUpperNu α
  let A := reducedCuspD2MajorantCoefficient α
  let C := A / (ν - 1)
  have hν : 1 < ν := by dsimp [ν, reducedCuspUpperNu]; linarith
  have hexp : -1 < ν - 1 := by linarith
  have hmajor :
      IntervalIntegrable (fun x : ℝ ↦ C * x ^ (ν - 1))
        volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hexp).const_mul C
  apply hmajor.mono_fun
  · exact
      (aestronglyMeasurable_reducedCuspUpperD1Remainder α).mono_measure
        Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    have hbound :=
      abs_reducedCuspUpperD1Remainder_le hα1 hα2 hx0 hx.2
    have hC0 : 0 ≤ C := by
      dsimp [C, A]
      exact div_nonneg
        (reducedCuspD2MajorantCoefficient_nonneg α) (by linarith)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hx0.le _))]
    simpa [C, A, ν] using hbound

noncomputable def reducedCuspUpperConstantCoefficient (α : ℝ) : ℝ :=
  reducedLatitudeCusp α 1 -
    reducedCuspUpperLinearCoefficient α -
    ∫ y in (0 : ℝ)..1, reducedCuspUpperD1Remainder α y

/-- Exact twice-integrated subtraction formula in the upper nonresonant
range. -/
theorem reducedLatitudeCusp_sub_upperAffine_eq_integral
    {α x : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    reducedLatitudeCusp α x -
        (reducedCuspUpperConstantCoefficient α +
          reducedCuspUpperLinearCoefficient α * x) =
      ∫ y in (0 : ℝ)..x, reducedCuspUpperD1Remainder α y := by
  have hrem :=
    intervalIntegrable_reducedCuspUpperD1Remainder hα1 hα2
  have hrem0x :
      IntervalIntegrable (reducedCuspUpperD1Remainder α) volume 0 x :=
    hrem.mono_set
      (uIcc_subset_uIcc (a₁ := 0) (b₁ := x)
        (a₂ := 0) (b₂ := 1) (by simp) (by simp [hx.le, hx1]))
  have hremx1 :
      IntervalIntegrable (reducedCuspUpperD1Remainder α) volume x 1 :=
    hrem.mono_set
      (uIcc_subset_uIcc (a₁ := x) (b₁ := 1)
        (a₂ := 0) (b₂ := 1) (by simp [hx.le, hx1]) (by simp))
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals hrem0x hremx1
  have hD1int :
      IntervalIntegrable (reducedLatitudeCuspD1Value α) volume x 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hx1
    exact (continuousOn_reducedLatitudeCuspD1Value_pos α).mono
      (fun y hy ↦ hx.trans_le hy.1)
  have hFTC :
      (∫ y in x..1, reducedLatitudeCuspD1Value α y) =
        reducedLatitudeCusp α 1 - reducedLatitudeCusp α x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro y hy
      rw [uIcc_of_le hx1] at hy
      exact hasDerivAt_reducedLatitudeCusp
        (α := α) (hx.trans_le hy.1)
    · exact hD1int
  have hsplit :
      (∫ y in x..1, reducedLatitudeCuspD1Value α y) =
        (∫ y in x..1, reducedCuspUpperD1Remainder α y) +
          reducedCuspUpperLinearCoefficient α * (1 - x) := by
    calc
      _ = ∫ y in x..1,
          (reducedCuspUpperD1Remainder α y +
            reducedCuspUpperLinearCoefficient α) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hx1] at hy
        have hy0 : 0 < y := hx.trans_le hy.1
        simp [reducedCuspUpperD1Remainder, hy0]
      _ = (∫ y in x..1, reducedCuspUpperD1Remainder α y) +
          ∫ _y in x..1, reducedCuspUpperLinearCoefficient α := by
        rw [intervalIntegral.integral_add hremx1
          (continuous_const.intervalIntegrable _ _)]
      _ = _ := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  unfold reducedCuspUpperConstantCoefficient
  rw [hFTC] at hsplit
  linarith

noncomputable def reducedCuspUpperBranchFactor (α x : ℝ) : ℝ :=
  (reducedLatitudeCusp α x -
      (reducedCuspUpperConstantCoefficient α +
        reducedCuspUpperLinearCoefficient α * x)) /
    x ^ reducedCuspUpperNu α

/-- Genuine local power-branch decomposition for `1 < α < 2`, with an
explicit uniform bound on the branch factor. -/
theorem reducedLatitudeCusp_eq_upperAffine_add_powerBranch
    {α x : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    reducedLatitudeCusp α x =
        reducedCuspUpperConstantCoefficient α +
          reducedCuspUpperLinearCoefficient α * x +
          x ^ reducedCuspUpperNu α *
            reducedCuspUpperBranchFactor α x ∧
      |reducedCuspUpperBranchFactor α x| ≤
        reducedCuspD2MajorantCoefficient α /
          ((reducedCuspUpperNu α - 1) *
            reducedCuspUpperNu α) := by
  let ν := reducedCuspUpperNu α
  let A := reducedCuspD2MajorantCoefficient α
  let C := A / (ν - 1)
  have hν : 1 < ν := by dsimp [ν, reducedCuspUpperNu]; linarith
  have hxpow : 0 < x ^ ν := Real.rpow_pos_of_pos hx _
  constructor
  · unfold reducedCuspUpperBranchFactor
    field_simp [hxpow.ne']
  · have hrem :=
      (intervalIntegrable_reducedCuspUpperD1Remainder hα1 hα2).mono_set
        (uIcc_subset_uIcc (a₁ := 0) (b₁ := x)
          (a₂ := 0) (b₂ := 1) (by simp) (by simp [hx.le, hx1]))
    have hexp : -1 < ν - 1 := by linarith
    have hmajor :
        IntervalIntegrable (fun y : ℝ ↦ C * y ^ (ν - 1))
          volume 0 x :=
      (intervalIntegral.intervalIntegrable_rpow' hexp).const_mul C
    have hC0 : 0 ≤ C := by
      dsimp [C, A]
      exact div_nonneg
        (reducedCuspD2MajorantCoefficient_nonneg α) (by linarith)
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le
      (f := reducedCuspUpperD1Remainder α)
      (g := fun y : ℝ ↦ C * y ^ (ν - 1)) (by
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
        rw [uIoc_of_le hx.le] at hy
        have hy0 : 0 < y := hy.1
        have hb :=
          abs_reducedCuspUpperD1Remainder_le hα1 hα2 hy0
            (hy.2.trans hx1)
        simp only [Real.norm_eq_abs]
        simpa [C, A, ν] using hb) hmajor
    have hint :
        |∫ y in (0 : ℝ)..x, reducedCuspUpperD1Remainder α y| ≤
          C / ν * x ^ ν := by
      have hnorm' :
          |∫ y in (0 : ℝ)..x, reducedCuspUpperD1Remainder α y| ≤
            |∫ y in (0 : ℝ)..x, C * y ^ (ν - 1)| := by
        simpa [Real.norm_eq_abs] using hnorm
      calc
        _ ≤ |∫ y in (0 : ℝ)..x, C * y ^ (ν - 1)| := hnorm'
        _ = C / ν * x ^ ν := by
          rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inl hexp)]
          have hν0 : ν ≠ 0 := by linarith
          rw [show ν - 1 + 1 = ν by ring,
            Real.zero_rpow hν0, sub_zero]
          rw [abs_of_nonneg (mul_nonneg hC0
            (div_nonneg (Real.rpow_nonneg hx.le _)
              (by linarith : 0 ≤ ν)))]
          ring
    have hdecomp :=
      reducedLatitudeCusp_sub_upperAffine_eq_integral
        hα1 hα2 hx hx1
    unfold reducedCuspUpperBranchFactor
    rw [hdecomp, abs_div, abs_of_pos hxpow]
    apply (div_le_iff₀ hxpow).2
    calc
      |∫ y in (0 : ℝ)..x, reducedCuspUpperD1Remainder α y| ≤
          C / ν * x ^ ν := hint
      _ = (A / ((ν - 1) * ν)) * x ^ ν := by
        dsimp [C]
        field_simp
      _ = _ := by
        dsimp [A, ν]

/-
## Lower nonresonant range

Here the first derivative itself has the integrable cusp scale
`x^(ν-1)`, where `ν = (1+α)/2 ∈ (1/2,1)`.  We obtain that scale by
integrating the already established sharp second-derivative estimate
backwards from `1`.
-/

noncomputable def reducedCuspLowerD1MajorantCoefficient (α : ℝ) : ℝ :=
  |reducedLatitudeCuspD1Value α 1| +
    reducedCuspD2MajorantCoefficient α /
      (1 - reducedCuspUpperNu α)

theorem reducedCuspLowerD1MajorantCoefficient_nonneg
    {α : ℝ} (hα1 : α < 1) :
    0 ≤ reducedCuspLowerD1MajorantCoefficient α := by
  unfold reducedCuspLowerD1MajorantCoefficient
  exact add_nonneg (abs_nonneg _)
    (div_nonneg (reducedCuspD2MajorantCoefficient_nonneg α)
      (by
        unfold reducedCuspUpperNu
        linarith))

/-- Sharp first-derivative cusp bound in the lower nonresonant range. -/
theorem abs_reducedLatitudeCuspD1Value_le_lower_rpow
    {α x : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    |reducedLatitudeCuspD1Value α x| ≤
      reducedCuspLowerD1MajorantCoefficient α *
        x ^ (reducedCuspUpperNu α - 1) := by
  let ν := reducedCuspUpperNu α
  let A := reducedCuspD2MajorantCoefficient α
  let K := |reducedLatitudeCuspD1Value α 1| + A / (1 - ν)
  have hν0 : 0 < ν := by
    dsimp [ν, reducedCuspUpperNu]
    linarith
  have hν1 : ν < 1 := by
    dsimp [ν, reducedCuspUpperNu]
    linarith
  have hpneg : ν - 1 < 0 := by linarith
  have hxpow1 : 1 ≤ x ^ (ν - 1) := by
    have h :=
      Real.rpow_le_rpow_of_nonpos hx hx1 (le_of_lt hpneg)
    simpa using h
  have hD2int :=
    intervalIntegrable_reducedLatitudeCuspD2Value_pos
      (α := α) hx hx1
  have hFTC :
      (∫ y in x..1, reducedLatitudeCuspD2Value α y) =
        reducedLatitudeCuspD1Value α 1 -
          reducedLatitudeCuspD1Value α x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro y hy
      rw [uIcc_of_le hx1] at hy
      exact hasDerivAt_reducedLatitudeCuspD1Value
        (α := α) (hx.trans_le hy.1)
    · exact hD2int
  have hmajor :
      IntervalIntegrable (fun y : ℝ ↦ A * y ^ (ν - 2))
        volume x 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hx1
    exact continuousOn_const.mul
      (continuousOn_id.rpow_const
        (fun y hy ↦ Or.inl (hx.trans_le hy.1).ne'))
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (f := reducedLatitudeCuspD2Value α)
    (g := fun y : ℝ ↦ A * y ^ (ν - 2)) (by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
      rw [uIoc_of_le hx1] at hy
      have hy0 : 0 < y := hx.trans hy.1
      have hraw :=
        abs_reducedLatitudeCuspD2Value_le_rpow hy0 (by linarith : α ≤ 2)
      have hrewrite : α / 2 - 3 / 2 = ν - 2 := by
        dsimp [ν, reducedCuspUpperNu]
        ring
      simp only [Real.norm_eq_abs]
      rw [hrewrite] at hraw
      simpa [A, reducedCuspD2MajorantCoefficient] using hraw) hmajor
  have hexpne : ν - 2 ≠ -1 := by linarith
  have hzero : (0 : ℝ) ∉ uIcc x 1 := by
    rw [uIcc_of_le hx1]
    intro h
    linarith [h.1]
  have hint :
      |∫ y in x..1, reducedLatitudeCuspD2Value α y| ≤
        A / (1 - ν) * (x ^ (ν - 1) - 1) := by
    have hnorm' :
        |∫ y in x..1, reducedLatitudeCuspD2Value α y| ≤
          |∫ y in x..1, A * y ^ (ν - 2)| := by
      simpa [Real.norm_eq_abs] using hnorm
    calc
      _ ≤ |∫ y in x..1, A * y ^ (ν - 2)| := hnorm'
      _ = A / (1 - ν) * (x ^ (ν - 1) - 1) := by
        rw [intervalIntegral.integral_const_mul,
          integral_rpow (Or.inr ⟨hexpne, hzero⟩)]
        rw [show ν - 2 + 1 = ν - 1 by ring,
          Real.one_rpow]
        have hA0 : 0 ≤ A :=
          reducedCuspD2MajorantCoefficient_nonneg α
        have hdiff0 : 0 ≤ x ^ (ν - 1) - 1 := sub_nonneg.mpr hxpow1
        have heq :
            A * ((1 - x ^ (ν - 1)) / (ν - 1)) =
              A / (1 - ν) * (x ^ (ν - 1) - 1) := by
          have hne₁ : ν - 1 ≠ 0 := by linarith
          have hne₂ : 1 - ν ≠ 0 := by linarith
          field_simp [hne₁, hne₂]
          ring
        rw [heq, abs_of_nonneg
          (mul_nonneg (div_nonneg hA0 (by linarith)) hdiff0)]
  have hD1 :
      |reducedLatitudeCuspD1Value α x| ≤
        |reducedLatitudeCuspD1Value α 1| +
          A / (1 - ν) * (x ^ (ν - 1) - 1) := by
    calc
      _ = |reducedLatitudeCuspD1Value α 1 -
          ∫ y in x..1, reducedLatitudeCuspD2Value α y| := by
        congr 1
        rw [hFTC]
        ring
      _ ≤ |reducedLatitudeCuspD1Value α 1| +
          |∫ y in x..1, reducedLatitudeCuspD2Value α y| :=
        abs_sub _ _
      _ ≤ _ := add_le_add_left hint _
  have hcoeff0 : 0 ≤ A / (1 - ν) := by
    exact div_nonneg (reducedCuspD2MajorantCoefficient_nonneg α)
      (by linarith)
  calc
    _ ≤ |reducedLatitudeCuspD1Value α 1| +
        A / (1 - ν) * (x ^ (ν - 1) - 1) := hD1
    _ ≤ K * x ^ (ν - 1) := by
      dsimp [K]
      nlinarith [abs_nonneg (reducedLatitudeCuspD1Value α 1),
        hcoeff0]
    _ = _ := by
      rfl

noncomputable def reducedCuspD1ZeroExtension (α x : ℝ) : ℝ :=
  if 0 < x then reducedLatitudeCuspD1Value α x else 0

private theorem aestronglyMeasurable_reducedCuspD1ZeroExtension
    (α : ℝ) :
    AEStronglyMeasurable (reducedCuspD1ZeroExtension α) volume := by
  have hpos :
      AEStronglyMeasurable (reducedLatitudeCuspD1Value α)
        (volume.restrict (Ioi 0)) :=
    (continuousOn_reducedLatitudeCuspD1Value_pos α).aestronglyMeasurable
      measurableSet_Ioi
  have hzero :
      AEStronglyMeasurable (fun _ : ℝ ↦ (0 : ℝ))
        (volume.restrict (Ioi (0 : ℝ))ᶜ) :=
    aestronglyMeasurable_const
  have hp := hpos.piecewise measurableSet_Ioi hzero
  simpa [reducedCuspD1ZeroExtension, Set.piecewise] using hp

theorem intervalIntegrable_reducedCuspD1ZeroExtension_lower
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IntervalIntegrable (reducedCuspD1ZeroExtension α) volume 0 1 := by
  let ν := reducedCuspUpperNu α
  let K := reducedCuspLowerD1MajorantCoefficient α
  have hν0 : 0 < ν := by
    dsimp [ν, reducedCuspUpperNu]
    linarith
  have hmajor :
      IntervalIntegrable (fun x : ℝ ↦ K * x ^ (ν - 1))
        volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul K
  apply hmajor.mono_fun
  · exact
      (aestronglyMeasurable_reducedCuspD1ZeroExtension α).mono_measure
        Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    have hb :=
      abs_reducedLatitudeCuspD1Value_le_lower_rpow
        hα0 hα1 hx0 hx.2
    simp only [Real.norm_eq_abs]
    rw [reducedCuspD1ZeroExtension, if_pos hx0]
    have hK0 :=
      reducedCuspLowerD1MajorantCoefficient_nonneg hα1
    rw [abs_of_nonneg (mul_nonneg hK0 (Real.rpow_nonneg hx0.le _))]
    simpa [K, ν] using hb

noncomputable def reducedCuspLowerConstantCoefficient (α : ℝ) : ℝ :=
  reducedLatitudeCusp α 1 -
    ∫ y in (0 : ℝ)..1, reducedCuspD1ZeroExtension α y

theorem reducedLatitudeCusp_sub_lowerConstant_eq_integral
    {α x : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    reducedLatitudeCusp α x -
        reducedCuspLowerConstantCoefficient α =
      ∫ y in (0 : ℝ)..x, reducedCuspD1ZeroExtension α y := by
  have hint :=
    intervalIntegrable_reducedCuspD1ZeroExtension_lower hα0 hα1
  have h0x :=
    hint.mono_set
      (uIcc_subset_uIcc (a₁ := 0) (b₁ := x)
        (a₂ := 0) (b₂ := 1) (by simp) (by simp [hx.le, hx1]))
  have hx1int :=
    hint.mono_set
      (uIcc_subset_uIcc (a₁ := x) (b₁ := 1)
        (a₂ := 0) (b₂ := 1)
        (by simp [hx.le, hx1]) (by simp))
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals h0x hx1int
  have heqOn :
      (∫ y in x..1, reducedCuspD1ZeroExtension α y) =
        ∫ y in x..1, reducedLatitudeCuspD1Value α y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx1] at hy
    have hy0 : 0 < y := hx.trans_le hy.1
    simp [reducedCuspD1ZeroExtension, hy0]
  have hFTC :
      (∫ y in x..1, reducedLatitudeCuspD1Value α y) =
        reducedLatitudeCusp α 1 - reducedLatitudeCusp α x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro y hy
      rw [uIcc_of_le hx1] at hy
      exact hasDerivAt_reducedLatitudeCusp
        (α := α) (hx.trans_le hy.1)
    · apply ContinuousOn.intervalIntegrable_of_Icc hx1
      exact (continuousOn_reducedLatitudeCuspD1Value_pos α).mono
        (fun y hy ↦ hx.trans_le hy.1)
  unfold reducedCuspLowerConstantCoefficient
  rw [heqOn, hFTC] at hadd
  linarith

noncomputable def reducedCuspLowerBranchFactor (α x : ℝ) : ℝ :=
  (reducedLatitudeCusp α x -
      reducedCuspLowerConstantCoefficient α) /
    x ^ reducedCuspUpperNu α

/-- Genuine local power-branch decomposition for `0 < α < 1`. -/
theorem reducedLatitudeCusp_eq_lowerConstant_add_powerBranch
    {α x : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    reducedLatitudeCusp α x =
        reducedCuspLowerConstantCoefficient α +
          x ^ reducedCuspUpperNu α *
            reducedCuspLowerBranchFactor α x ∧
      |reducedCuspLowerBranchFactor α x| ≤
        reducedCuspLowerD1MajorantCoefficient α /
          reducedCuspUpperNu α := by
  let ν := reducedCuspUpperNu α
  let K := reducedCuspLowerD1MajorantCoefficient α
  have hν0 : 0 < ν := by
    dsimp [ν, reducedCuspUpperNu]
    linarith
  have hxpow : 0 < x ^ ν := Real.rpow_pos_of_pos hx _
  constructor
  · unfold reducedCuspLowerBranchFactor
    field_simp [hxpow.ne']
  · have hmajor :
        IntervalIntegrable (fun y : ℝ ↦ K * y ^ (ν - 1))
          volume 0 x :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul K
    have hK0 : 0 ≤ K := by
      exact reducedCuspLowerD1MajorantCoefficient_nonneg hα1
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le
      (f := reducedCuspD1ZeroExtension α)
      (g := fun y : ℝ ↦ K * y ^ (ν - 1)) (by
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
        rw [uIoc_of_le hx.le] at hy
        have hy0 : 0 < y := hy.1
        have hb :=
          abs_reducedLatitudeCuspD1Value_le_lower_rpow
            hα0 hα1 hy0 (hy.2.trans hx1)
        simp only [Real.norm_eq_abs]
        rw [reducedCuspD1ZeroExtension, if_pos hy0]
        simpa [K, ν] using hb) hmajor
    have hint :
        |∫ y in (0 : ℝ)..x, reducedCuspD1ZeroExtension α y| ≤
          K / ν * x ^ ν := by
      have hnorm' :
          |∫ y in (0 : ℝ)..x, reducedCuspD1ZeroExtension α y| ≤
            |∫ y in (0 : ℝ)..x, K * y ^ (ν - 1)| := by
        simpa [Real.norm_eq_abs] using hnorm
      calc
        _ ≤ |∫ y in (0 : ℝ)..x, K * y ^ (ν - 1)| := hnorm'
        _ = K / ν * x ^ ν := by
          rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inl (by linarith))]
          rw [show ν - 1 + 1 = ν by ring,
            Real.zero_rpow hν0.ne', sub_zero]
          rw [abs_of_nonneg (mul_nonneg hK0
            (div_nonneg (Real.rpow_nonneg hx.le _) hν0.le))]
          ring
    have hdecomp :=
      reducedLatitudeCusp_sub_lowerConstant_eq_integral
        hα0 hα1 hx hx1
    unfold reducedCuspLowerBranchFactor
    rw [hdecomp, abs_div, abs_of_pos hxpow]
    apply (div_le_iff₀ hxpow).2
    calc
      _ ≤ K / ν * x ^ ν := hint
      _ = (K / ν) * x ^ ν := rfl
      _ = _ := by
        dsimp [K, ν]

end BEMOC
