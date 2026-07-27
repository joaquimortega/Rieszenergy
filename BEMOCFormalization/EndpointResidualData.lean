import BEMOCFormalization.EndpointRegularity
import BEMOCFormalization.EndpointExtension

open scoped Topology ENat Interval
open Set Filter Function MeasureTheory

namespace BEMOC.CircleGeneral.EndpointRegularity

theorem deriv_sincPiPow_zero (α : ℝ) : deriv (sincPiPow α) 0 = 0 :=
  (hasDerivAt_sincPiPow_zero α).deriv

theorem deriv_sincPiPow_linear_bound (α : ℝ) :
    ∃ C : ℝ, ∀ x ∈ Icc (0 : ℝ) (1 / 2 : ℝ),
      |deriv (sincPiPow α) x| ≤ C * x := by
  have hcont : ContDiffOn ℝ 1 (deriv (sincPiPow α))
      (Icc (0 : ℝ) (1 / 2 : ℝ)) := by
    exact (contDiffOn_deriv_sincPiPow α).of_le (by norm_num) |>.mono (by
      intro x hx
      constructor <;> linarith [hx.1, hx.2])
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (n := 0) hcont
  refine ⟨C, ?_⟩
  intro x hx
  have := hC x hx
  rw [taylor_within_zero_eval] at this
  simp only [deriv_sincPiPow_zero, sub_zero, pow_one] at this
  simpa using this

theorem deriv2_sincPiPow_bound (α : ℝ) :
    ∃ C : ℝ, ∀ x ∈ Icc (0 : ℝ) (1 / 2 : ℝ),
      |deriv (deriv (sincPiPow α)) x| ≤ C := by
  have hc : ContinuousOn (deriv (deriv (sincPiPow α)))
      (Icc (0 : ℝ) (1 / 2 : ℝ)) := by
    exact (contDiffOn_deriv2_sincPiPow α).continuousOn.mono (by
      intro x hx
      constructor <;> linarith [hx.1, hx.2])
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc.norm
  refine ⟨C, ?_⟩
  intro x hx
  exact hC (mem_image_of_mem _ hx)

theorem deriv3_sincPiPow_bound (α : ℝ) :
    ∃ C : ℝ, ∀ x ∈ Icc (0 : ℝ) (1 / 2 : ℝ),
      |deriv (deriv (deriv (sincPiPow α))) x| ≤ C := by
  have hc : ContinuousOn (deriv (deriv (deriv (sincPiPow α))))
      (Icc (0 : ℝ) (1 / 2 : ℝ)) := by
    exact (contDiffOn_deriv3_sincPiPow α).continuousOn.mono (by
      intro x hx
      constructor <;> linarith [hx.1, hx.2])
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc.norm
  refine ⟨C, ?_⟩
  intro x hx
  exact hC (mem_image_of_mem _ hx)

noncomputable def leftSingularCorrection (α x : ℝ) : ℝ :=
  x ^ α * (sincPiPow α x - 1)

noncomputable def leftSingularCorrectionD1 (α x : ℝ) : ℝ :=
  α * x ^ (α - 1) * (sincPiPow α x - 1) +
    x ^ α * deriv (sincPiPow α) x

noncomputable def leftSingularCorrectionD2 (α x : ℝ) : ℝ :=
  α * (α - 1) * x ^ (α - 2) * (sincPiPow α x - 1) +
    2 * α * x ^ (α - 1) * deriv (sincPiPow α) x +
    x ^ α * deriv (deriv (sincPiPow α)) x

noncomputable def leftSingularCorrectionD3 (α x : ℝ) : ℝ :=
  α * (α - 1) * (α - 2) * x ^ (α - 3) * (sincPiPow α x - 1) +
    3 * α * (α - 1) * x ^ (α - 2) * deriv (sincPiPow α) x +
    3 * α * x ^ (α - 1) * deriv (deriv (sincPiPow α)) x +
    x ^ α * deriv (deriv (deriv (sincPiPow α))) x

private theorem hasDerivAt_q {α x : ℝ} (hx : |x| < 1) :
    HasDerivAt (sincPiPow α) (deriv (sincPiPow α) x) x :=
  (contDiffAt_sincPiPow hx).differentiableAt (by simp) |>.hasDerivAt

private theorem hasDerivAt_q1 {α x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (deriv (sincPiPow α))
      (deriv (deriv (sincPiPow α)) x) x :=
  ((contDiffOn_deriv_sincPiPow α).contDiffAt
    (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num) |>.hasDerivAt

private theorem hasDerivAt_q2 {α x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (deriv (deriv (sincPiPow α)))
      (deriv (deriv (deriv (sincPiPow α))) x) x :=
  ((contDiffOn_deriv2_sincPiPow α).contDiffAt
    (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num) |>.hasDerivAt

theorem hasDerivAt_leftSingularCorrection {α x : ℝ}
    (hx0 : x ≠ 0) (hx1 : |x| < 1) :
    HasDerivAt (leftSingularCorrection α)
      (leftSingularCorrectionD1 α x) x := by
  unfold leftSingularCorrection leftSingularCorrectionD1
  convert (Real.hasDerivAt_rpow_const (p := α) (Or.inl hx0)).mul
    ((hasDerivAt_q hx1).sub_const 1) using 1 <;> ring

theorem hasDerivAt_leftSingularCorrectionD1 {α x : ℝ}
    (hx0 : x ≠ 0) (hx1 : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (leftSingularCorrectionD1 α)
      (leftSingularCorrectionD2 α x) x := by
  unfold leftSingularCorrectionD1 leftSingularCorrectionD2
  have hp1 := Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hx0)
  have hp0 := Real.hasDerivAt_rpow_const (p := α) (Or.inl hx0)
  have hq := hasDerivAt_q (α := α)
    (show |x| < 1 by simpa [abs_lt] using hx1)
  have hq1 := hasDerivAt_q1 (α := α) hx1
  convert (((hp1.const_mul α).mul (hq.sub_const 1)).add
    (hp0.mul hq1)) using 1 <;> ring

theorem hasDerivAt_leftSingularCorrectionD2 {α x : ℝ}
    (hx0 : x ≠ 0) (hx1 : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (leftSingularCorrectionD2 α)
      (leftSingularCorrectionD3 α x) x := by
  unfold leftSingularCorrectionD2 leftSingularCorrectionD3
  have hp2 := Real.hasDerivAt_rpow_const (p := α - 2) (Or.inl hx0)
  have hp1 := Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hx0)
  have hp0 := Real.hasDerivAt_rpow_const (p := α) (Or.inl hx0)
  have hq := hasDerivAt_q (α := α)
    (show |x| < 1 by simpa [abs_lt] using hx1)
  have hq1 := hasDerivAt_q1 (α := α) hx1
  have hq2 := hasDerivAt_q2 (α := α) hx1
  convert ((((hp2.const_mul (α * (α - 1))).mul (hq.sub_const 1)).add
    ((hp1.const_mul (2 * α)).mul hq1)).add (hp0.mul hq2)) using 1 <;> ring

theorem leftSingularCorrectionD3_bound {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioc (0 : ℝ) (1 / 2 : ℝ),
      |leftSingularCorrectionD3 α x| ≤ C * x ^ (α - 1) := by
  obtain ⟨C0, hC0⟩ := sincPiPow_sub_one_quadratic_bound α
  obtain ⟨C1, hC1⟩ := deriv_sincPiPow_linear_bound α
  obtain ⟨C2, hC2⟩ := deriv2_sincPiPow_bound α
  obtain ⟨C3, hC3⟩ := deriv3_sincPiPow_bound α
  have hC0n : 0 ≤ C0 := by
    have h := hC0 (1 / 2) (by constructor <;> norm_num)
    have hz : 0 ≤ |sincPiPow α (1 / 2) - 1| := abs_nonneg _
    nlinarith
  have hC1n : 0 ≤ C1 := by
    have h := hC1 (1 / 2) (by constructor <;> norm_num)
    have hz : 0 ≤ |deriv (sincPiPow α) (1 / 2)| := abs_nonneg _
    nlinarith
  have hC2n : 0 ≤ C2 := by
    have h := hC2 0 (by constructor <;> norm_num)
    exact (abs_nonneg _).trans h
  have hC3n : 0 ≤ C3 := by
    have h := hC3 0 (by constructor <;> norm_num)
    exact (abs_nonneg _).trans h
  refine ⟨|α * (α - 1) * (α - 2)| * C0 +
      |3 * α * (α - 1)| * C1 + |3 * α| * C2 + C3, by positivity, ?_⟩
  intro x hx
  have hxI : x ∈ Icc (0 : ℝ) (1 / 2 : ℝ) := ⟨hx.1.le, hx.2⟩
  have hx1 : x ≤ 1 := hx.2.trans (by norm_num)
  have hr0 (r : ℝ) : 0 ≤ x ^ r := Real.rpow_nonneg hx.1.le r
  have hp2 : x ^ (α - 3) * x ^ 2 = x ^ (α - 1) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hx.1]
    congr 1
    ring
  have hp1 : x ^ (α - 2) * x = x ^ (α - 1) := by
    calc
      x ^ (α - 2) * x = x ^ (α - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((α - 2) + 1) := (Real.rpow_add hx.1 _ _).symm
      _ = _ := by congr 1 <;> ring
  have hp0 : x ^ α = x ^ (α - 1) * x := by
    calc
      x ^ α = x ^ ((α - 1) + 1) := by congr 1 <;> ring
      _ = x ^ (α - 1) * x ^ (1 : ℝ) := Real.rpow_add hx.1 _ _
      _ = _ := by rw [Real.rpow_one]
  have ht0 :
      |α * (α - 1) * (α - 2) * x ^ (α - 3) *
          (sincPiPow α x - 1)| ≤
        |α * (α - 1) * (α - 2)| * C0 * x ^ (α - 1) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (hr0 (α - 3))]
    calc
      |α * (α - 1) * (α - 2)| * x ^ (α - 3) *
          |sincPiPow α x - 1| ≤
          |α * (α - 1) * (α - 2)| * x ^ (α - 3) * (C0 * x ^ 2) := by
            exact mul_le_mul_of_nonneg_left (hC0 x hxI)
              (mul_nonneg (abs_nonneg _) (hr0 _))
      _ = _ := by rw [← hp2]; ring
  have ht1 :
      |3 * α * (α - 1) * x ^ (α - 2) * deriv (sincPiPow α) x| ≤
        |3 * α * (α - 1)| * C1 * x ^ (α - 1) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (hr0 (α - 2))]
    calc
      |3 * α * (α - 1)| * x ^ (α - 2) * |deriv (sincPiPow α) x| ≤
          |3 * α * (α - 1)| * x ^ (α - 2) * (C1 * x) := by
            exact mul_le_mul_of_nonneg_left (hC1 x hxI)
              (mul_nonneg (abs_nonneg _) (hr0 _))
      _ = _ := by rw [← hp1]; ring
  have ht2 :
      |3 * α * x ^ (α - 1) * deriv (deriv (sincPiPow α)) x| ≤
        |3 * α| * C2 * x ^ (α - 1) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (hr0 (α - 1))]
    calc
      |3 * α| * x ^ (α - 1) * |deriv (deriv (sincPiPow α)) x| ≤
          |3 * α| * x ^ (α - 1) * C2 :=
        mul_le_mul_of_nonneg_left (hC2 x hxI)
          (mul_nonneg (abs_nonneg _) (hr0 _))
      _ = _ := by ring
  have ht3 :
      |x ^ α * deriv (deriv (deriv (sincPiPow α))) x| ≤
        C3 * x ^ (α - 1) := by
    rw [abs_mul, abs_of_nonneg (hr0 α), hp0]
    calc
      x ^ (α - 1) * x * |deriv (deriv (deriv (sincPiPow α))) x| ≤
          x ^ (α - 1) * x * C3 := by
            exact mul_le_mul_of_nonneg_left (hC3 x hxI)
              (mul_nonneg (hr0 _) hx.1.le)
      _ ≤ x ^ (α - 1) * 1 * C3 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hx1 (hr0 _)) hC3n
      _ = _ := by ring
  unfold leftSingularCorrectionD3
  calc
    |_ + _ + _ + _| ≤
        |α * (α - 1) * (α - 2) * x ^ (α - 3) * (sincPiPow α x - 1)| +
          |3 * α * (α - 1) * x ^ (α - 2) * deriv (sincPiPow α) x| +
          |3 * α * x ^ (α - 1) * deriv (deriv (sincPiPow α)) x| +
          |x ^ α * deriv (deriv (deriv (sincPiPow α))) x| := by
            linarith [abs_add
              (α * (α - 1) * (α - 2) * x ^ (α - 3) * (sincPiPow α x - 1) +
                3 * α * (α - 1) * x ^ (α - 2) * deriv (sincPiPow α) x +
                3 * α * x ^ (α - 1) * deriv (deriv (sincPiPow α)) x)
              (x ^ α * deriv (deriv (deriv (sincPiPow α))) x),
              abs_add
                (α * (α - 1) * (α - 2) * x ^ (α - 3) * (sincPiPow α x - 1) +
                  3 * α * (α - 1) * x ^ (α - 2) * deriv (sincPiPow α) x)
                (3 * α * x ^ (α - 1) * deriv (deriv (sincPiPow α)) x),
              abs_add
                (α * (α - 1) * (α - 2) * x ^ (α - 3) * (sincPiPow α x - 1))
                (3 * α * (α - 1) * x ^ (α - 2) * deriv (sincPiPow α) x)]
    _ ≤ (|α * (α - 1) * (α - 2)| * C0 +
          |3 * α * (α - 1)| * C1 + |3 * α| * C2 + C3) * x ^ (α - 1) := by
      calc
        _ ≤ |α * (α - 1) * (α - 2)| * C0 * x ^ (α - 1) +
            |3 * α * (α - 1)| * C1 * x ^ (α - 1) +
            |3 * α| * C2 * x ^ (α - 1) + C3 * x ^ (α - 1) := by linarith
        _ = _ := by ring

theorem leftSingularCorrectionD3_intervalIntegrable {α : ℝ} (hα : 0 < α) :
    IntervalIntegrable (leftSingularCorrectionD3 α) volume
      (0 : ℝ) (1 / 2 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := leftSingularCorrectionD3_bound hα
  have hmaj : IntervalIntegrable (fun x : ℝ => C * x ^ (α - 1)) volume
      (0 : ℝ) (1 / 2 : ℝ) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1)).const_mul C
  have hmeas : AEStronglyMeasurable (leftSingularCorrectionD3 α)
      (volume.restrict (Ι (0 : ℝ) (1 / 2 : ℝ))) := by
    apply EulerSmooth.aestronglyMeasurable_restrict_of_hasDerivAt_Ioo (by norm_num)
    intro x hx
    apply hasDerivAt_leftSingularCorrectionD2 hx.1.ne'
    constructor <;> linarith [hx.1, hx.2]
  apply hmaj.mono_fun hmeas
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  rw [uIoc_of_le (show (0 : ℝ) ≤ 1 / 2 by norm_num)] at hx
  have hb := hC x hx
  rw [Real.norm_eq_abs]
  calc
    |leftSingularCorrectionD3 α x| ≤ C * x ^ (α - 1) := hb
    _ = |C * x ^ (α - 1)| := by
      rw [abs_of_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hx.1.le _))]
    _ = ‖C * x ^ (α - 1)‖ := by rw [Real.norm_eq_abs]

theorem leftSingularCorrectionD1_bound (α : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioc (0 : ℝ) (1 / 2 : ℝ),
      |leftSingularCorrectionD1 α x| ≤ C * x ^ (α + 1) := by
  obtain ⟨C0, hC0⟩ := sincPiPow_sub_one_quadratic_bound α
  obtain ⟨C1, hC1⟩ := deriv_sincPiPow_linear_bound α
  have hC0n : 0 ≤ C0 := by
    have h := hC0 (1 / 2) (by constructor <;> norm_num)
    nlinarith [abs_nonneg (sincPiPow α (1 / 2) - 1)]
  have hC1n : 0 ≤ C1 := by
    have h := hC1 (1 / 2) (by constructor <;> norm_num)
    nlinarith [abs_nonneg (deriv (sincPiPow α) (1 / 2))]
  refine ⟨|α| * C0 + C1, by positivity, ?_⟩
  intro x hx
  have hxI : x ∈ Icc (0 : ℝ) (1 / 2 : ℝ) := ⟨hx.1.le, hx.2⟩
  have hp2 : x ^ (α - 1) * x ^ 2 = x ^ (α + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx.1]
    congr 1 <;> ring
  have hp1 : x ^ α * x = x ^ (α + 1) := by
    calc
      x ^ α * x = x ^ α * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ (α + 1) := (Real.rpow_add hx.1 _ _).symm
  have ht0 : |α * x ^ (α - 1) * (sincPiPow α x - 1)| ≤
      |α| * C0 * x ^ (α + 1) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    calc
      |α| * x ^ (α - 1) * |sincPiPow α x - 1| ≤
          |α| * x ^ (α - 1) * (C0 * x ^ 2) :=
        mul_le_mul_of_nonneg_left (hC0 x hxI)
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hx.1.le _))
      _ = _ := by rw [← hp2]; ring
  have ht1 : |x ^ α * deriv (sincPiPow α) x| ≤ C1 * x ^ (α + 1) := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    calc
      x ^ α * |deriv (sincPiPow α) x| ≤ x ^ α * (C1 * x) :=
        mul_le_mul_of_nonneg_left (hC1 x hxI) (Real.rpow_nonneg hx.1.le _)
      _ = _ := by rw [← hp1]; ring
  unfold leftSingularCorrectionD1
  calc
    |_ + _| ≤ |α * x ^ (α - 1) * (sincPiPow α x - 1)| +
        |x ^ α * deriv (sincPiPow α) x| := abs_add _ _
    _ ≤ |α| * C0 * x ^ (α + 1) + C1 * x ^ (α + 1) := add_le_add ht0 ht1
    _ = (|α| * C0 + C1) * x ^ (α + 1) := by ring

theorem leftSingularCorrectionD2_bound (α : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioc (0 : ℝ) (1 / 2 : ℝ),
      |leftSingularCorrectionD2 α x| ≤ C * x ^ α := by
  obtain ⟨C0, hC0⟩ := sincPiPow_sub_one_quadratic_bound α
  obtain ⟨C1, hC1⟩ := deriv_sincPiPow_linear_bound α
  obtain ⟨C2, hC2⟩ := deriv2_sincPiPow_bound α
  have hC0n : 0 ≤ C0 := by
    have h := hC0 (1 / 2) (by constructor <;> norm_num)
    nlinarith [abs_nonneg (sincPiPow α (1 / 2) - 1)]
  have hC1n : 0 ≤ C1 := by
    have h := hC1 (1 / 2) (by constructor <;> norm_num)
    nlinarith [abs_nonneg (deriv (sincPiPow α) (1 / 2))]
  have hC2n : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0 (by constructor <;> norm_num))
  refine ⟨|α * (α - 1)| * C0 + |2 * α| * C1 + C2, by positivity, ?_⟩
  intro x hx
  have hxI : x ∈ Icc (0 : ℝ) (1 / 2 : ℝ) := ⟨hx.1.le, hx.2⟩
  have hp2 : x ^ (α - 2) * x ^ 2 = x ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx.1]
    congr 1 <;> ring
  have hp1 : x ^ (α - 1) * x = x ^ α := by
    calc
      x ^ (α - 1) * x = x ^ (α - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((α - 1) + 1) := (Real.rpow_add hx.1 _ _).symm
      _ = _ := by congr 1 <;> ring
  have ht0 :
      |α * (α - 1) * x ^ (α - 2) * (sincPiPow α x - 1)| ≤
        |α * (α - 1)| * C0 * x ^ α := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    calc
      |α * (α - 1)| * x ^ (α - 2) * |sincPiPow α x - 1| ≤
          |α * (α - 1)| * x ^ (α - 2) * (C0 * x ^ 2) :=
        mul_le_mul_of_nonneg_left (hC0 x hxI)
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hx.1.le _))
      _ = _ := by rw [← hp2]; ring
  have ht1 : |2 * α * x ^ (α - 1) * deriv (sincPiPow α) x| ≤
      |2 * α| * C1 * x ^ α := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    calc
      |2 * α| * x ^ (α - 1) * |deriv (sincPiPow α) x| ≤
          |2 * α| * x ^ (α - 1) * (C1 * x) :=
        mul_le_mul_of_nonneg_left (hC1 x hxI)
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hx.1.le _))
      _ = _ := by rw [← hp1]; ring
  have ht2 : |x ^ α * deriv (deriv (sincPiPow α)) x| ≤ C2 * x ^ α := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    calc
      x ^ α * |deriv (deriv (sincPiPow α)) x| ≤ x ^ α * C2 :=
        mul_le_mul_of_nonneg_left (hC2 x hxI) (Real.rpow_nonneg hx.1.le _)
      _ = _ := by ring
  unfold leftSingularCorrectionD2
  calc
    |_ + _ + _| ≤
        |α * (α - 1) * x ^ (α - 2) * (sincPiPow α x - 1)| +
        |2 * α * x ^ (α - 1) * deriv (sincPiPow α) x| +
        |x ^ α * deriv (deriv (sincPiPow α)) x| := by
          linarith [abs_add
            (α * (α - 1) * x ^ (α - 2) * (sincPiPow α x - 1))
            (2 * α * x ^ (α - 1) * deriv (sincPiPow α) x),
            abs_add
              (α * (α - 1) * x ^ (α - 2) * (sincPiPow α x - 1) +
                2 * α * x ^ (α - 1) * deriv (sincPiPow α) x)
              (x ^ α * deriv (deriv (sincPiPow α)) x)]
    _ ≤ |α * (α - 1)| * C0 * x ^ α +
        |2 * α| * C1 * x ^ α + C2 * x ^ α := by linarith
    _ = (|α * (α - 1)| * C0 + |2 * α| * C1 + C2) * x ^ α := by ring

private theorem tendsto_const_mul_rpow_nhdsGT_zero
    {C p : ℝ} (hp : 0 < p) :
    Tendsto (fun x : ℝ => C * x ^ p) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp.le)).tendsto.const_mul C
  simpa [Real.zero_rpow hp.ne'] using h.mono_left inf_le_left

theorem tendsto_leftSingularCorrectionD1_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (leftSingularCorrectionD1 α) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := leftSingularCorrectionD1_bound α
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _)
  · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    exact hC x hx
  · exact tendsto_const_mul_rpow_nhdsGT_zero (by linarith : 0 < α + 1)

theorem tendsto_leftSingularCorrectionD2_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (leftSingularCorrectionD2 α) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := leftSingularCorrectionD2_bound α
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _)
  · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    exact hC x hx
  · exact tendsto_const_mul_rpow_nhdsGT_zero hα

theorem circleProfile_eq_left_factor {α x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    circleProfile α x = (2 * Real.pi) ^ α * x ^ α * sincPiPow α x := by
  have hsin : Real.sin (Real.pi * x) = Real.pi * x * sincPi x := by
    rw [sincPi_eq hx0.ne']
    field_simp [Real.pi_ne_zero, hx0.ne']
  have hsinc : 0 ≤ sincPi x := (sincPi_pos_of_abs_lt_one
    (show |x| < 1 by rw [abs_of_pos hx0]; exact hx1)).le
  unfold circleProfile sincPiPow
  rw [hsin]
  rw [show 2 * (Real.pi * x * sincPi x) = (2 * Real.pi) * (x * sincPi x) by ring]
  rw [Real.mul_rpow (by positivity) (mul_nonneg hx0.le hsinc),
    Real.mul_rpow hx0.le hsinc]
  ring

noncomputable def smoothEndpointTail (α x : ℝ) : ℝ :=
  (1 - x) ^ α - 1 + α * x * (1 - x)

noncomputable def smoothEndpointTailD1 (α x : ℝ) : ℝ :=
  -α * (1 - x) ^ (α - 1) + α * (1 - 2 * x)

noncomputable def smoothEndpointTailD2 (α x : ℝ) : ℝ :=
  α * (α - 1) * (1 - x) ^ (α - 2) - 2 * α

noncomputable def smoothEndpointTailD3 (α x : ℝ) : ℝ :=
  -α * (α - 1) * (α - 2) * (1 - x) ^ (α - 3)

noncomputable def leftResidual (α x : ℝ) : ℝ :=
  (2 * Real.pi) ^ α *
    (leftSingularCorrection α x - smoothEndpointTail α x)

noncomputable def leftResidualD1 (α x : ℝ) : ℝ :=
  (2 * Real.pi) ^ α *
    (leftSingularCorrectionD1 α x - smoothEndpointTailD1 α x)

noncomputable def leftResidualD2 (α x : ℝ) : ℝ :=
  (2 * Real.pi) ^ α *
    (leftSingularCorrectionD2 α x - smoothEndpointTailD2 α x)

noncomputable def leftResidualD3 (α x : ℝ) : ℝ :=
  (2 * Real.pi) ^ α *
    (leftSingularCorrectionD3 α x - smoothEndpointTailD3 α x)

private theorem hasDerivAt_smoothEndpointTail {α x : ℝ}
    (hx : 1 - x ≠ 0) :
    HasDerivAt (smoothEndpointTail α) (smoothEndpointTailD1 α x) x := by
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x 1).sub (hasDerivAt_id x) using 1 <;> ring
  have hpoly : HasDerivAt (fun y : ℝ => α * y * (1 - y))
      (α * (1 - 2 * x)) x := by
    convert ((hasDerivAt_id x).mul hsub).const_mul α using 1 <;>
      simp only [id_eq] <;> ring
  unfold smoothEndpointTail smoothEndpointTailD1
  convert (((hsub.rpow_const (Or.inl hx)).sub_const 1).add hpoly) using 1 <;> ring

private theorem hasDerivAt_smoothEndpointTailD1 {α x : ℝ}
    (hx : 1 - x ≠ 0) :
    HasDerivAt (smoothEndpointTailD1 α) (smoothEndpointTailD2 α x) x := by
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x 1).sub (hasDerivAt_id x) using 1 <;> ring
  unfold smoothEndpointTailD1 smoothEndpointTailD2
  convert ((hsub.rpow_const (p := α - 1) (Or.inl hx)).const_mul (-α)).add
    ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).const_mul 2) |>.const_mul α)
    using 1 <;> ring

private theorem hasDerivAt_smoothEndpointTailD2 {α x : ℝ}
    (hx : 1 - x ≠ 0) :
    HasDerivAt (smoothEndpointTailD2 α) (smoothEndpointTailD3 α x) x := by
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x 1).sub (hasDerivAt_id x) using 1 <;> ring
  unfold smoothEndpointTailD2 smoothEndpointTailD3
  convert ((hsub.rpow_const (p := α - 2) (Or.inl hx)).const_mul
    (α * (α - 1))).sub_const (2 * α) using 1 <;> ring

theorem hasDerivAt_leftResidual {α x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (leftResidual α) (leftResidualD1 α x) x := by
  unfold leftResidual leftResidualD1
  exact ((hasDerivAt_leftSingularCorrection hx.1.ne'
    (show |x| < 1 by rw [abs_of_pos hx.1]; exact hx.2)).sub
      (hasDerivAt_smoothEndpointTail (sub_ne_zero.mpr hx.2.ne'))).const_mul _

theorem hasDerivAt_leftResidualD1 {α x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (leftResidualD1 α) (leftResidualD2 α x) x := by
  unfold leftResidualD1 leftResidualD2
  exact ((hasDerivAt_leftSingularCorrectionD1 hx.1.ne'
    (show x ∈ Ioo (-1 : ℝ) 1 by exact ⟨by linarith [hx.1], hx.2⟩)).sub
      (hasDerivAt_smoothEndpointTailD1 (sub_ne_zero.mpr hx.2.ne'))).const_mul _

theorem hasDerivAt_leftResidualD2 {α x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (leftResidualD2 α) (leftResidualD3 α x) x := by
  unfold leftResidualD2 leftResidualD3
  exact ((hasDerivAt_leftSingularCorrectionD2 hx.1.ne'
    (show x ∈ Ioo (-1 : ℝ) 1 by exact ⟨by linarith [hx.1], hx.2⟩)).sub
      (hasDerivAt_smoothEndpointTailD2 (sub_ne_zero.mpr hx.2.ne'))).const_mul _

theorem leftResidual_eq_circleEndpointResidual {α x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    leftResidual α x = circleEndpointResidual α x := by
  unfold circleEndpointResidual
  rw [circleProfile_eq_left_factor hx.1 hx.2]
  unfold leftResidual leftSingularCorrection smoothEndpointTail
    endpointModel
  ring

theorem leftResidualD1_zero {α : ℝ} (hα : 0 < α) :
    leftResidualD1 α 0 = 0 := by
  unfold leftResidualD1 leftSingularCorrectionD1 smoothEndpointTailD1
  simp [Real.zero_rpow hα.ne', sincPiPow_zero, deriv_sincPiPow_zero]

theorem leftResidualD2_zero {α : ℝ} (hα : 0 < α) :
    leftResidualD2 α 0 = (2 * Real.pi) ^ α * α * (3 - α) := by
  unfold leftResidualD2 leftSingularCorrectionD2 smoothEndpointTailD2
  simp [Real.zero_rpow hα.ne', sincPiPow_zero, deriv_sincPiPow_zero]
  ring

theorem continuousAt_leftSingularCorrection_zero {α : ℝ} (hα : 0 < α) :
    ContinuousAt (leftSingularCorrection α) 0 := by
  unfold leftSingularCorrection
  exact (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).mul
    ((contDiffAt_sincPiPow (by norm_num : |(0 : ℝ)| < 1)).continuousAt.sub
      continuousAt_const)

theorem continuousAt_leftResidual_zero {α : ℝ} (hα : 0 < α) :
    ContinuousAt (leftResidual α) 0 := by
  unfold leftResidual
  exact ((continuousAt_leftSingularCorrection_zero hα).sub
    (hasDerivAt_smoothEndpointTail (α := α) (x := 0) (by norm_num)).continuousAt).const_mul _

theorem tendsto_leftResidualD1_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (leftResidualD1 α) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  unfold leftResidualD1
  have ht := (tendsto_leftSingularCorrectionD1_zero hα).sub
    ((hasDerivAt_smoothEndpointTailD1 (α := α) (x := 0) (by norm_num)).continuousAt.tendsto.mono_left
      inf_le_left)
  simpa [smoothEndpointTailD1] using ht.const_mul ((2 * Real.pi) ^ α)

theorem tendsto_leftResidualD2_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (leftResidualD2 α) (𝓝[>] (0 : ℝ))
      (𝓝 ((2 * Real.pi) ^ α * α * (3 - α))) := by
  unfold leftResidualD2
  have ht := (tendsto_leftSingularCorrectionD2_zero hα).sub
    ((hasDerivAt_smoothEndpointTailD2 (α := α) (x := 0) (by norm_num)).continuousAt.tendsto.mono_left
      inf_le_left)
  convert ht.const_mul ((2 * Real.pi) ^ α) using 1 <;>
    simp [smoothEndpointTailD2] <;> ring

theorem hasDerivWithinAt_leftResidual_zero {α : ℝ} (hα : 0 < α) :
    HasDerivWithinAt (leftResidual α) 0 (Ici (0 : ℝ)) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ioo (0 : ℝ) 1)
  · intro x hx
    exact (hasDerivAt_leftResidual hx).differentiableAt.differentiableWithinAt
  · exact (continuousAt_leftResidual_zero hα).continuousWithinAt
  · exact Ioo_mem_nhdsGT zero_lt_one
  · have heq : (fun x : ℝ => deriv (leftResidual α) x) =ᶠ[𝓝[>] (0 : ℝ)]
        leftResidualD1 α := by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
      exact (hasDerivAt_leftResidual hx).deriv
    exact (tendsto_leftResidualD1_zero hα).congr' heq.symm

theorem hasDerivWithinAt_leftResidualD1_zero {α : ℝ} (hα : 0 < α) :
    HasDerivWithinAt (leftResidualD1 α)
      ((2 * Real.pi) ^ α * α * (3 - α)) (Ici (0 : ℝ)) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ioo (0 : ℝ) 1)
  · intro x hx
    exact (hasDerivAt_leftResidualD1 hx).differentiableAt.differentiableWithinAt
  · show Tendsto (leftResidualD1 α) (𝓝[Ioo (0 : ℝ) 1] 0)
      (𝓝 (leftResidualD1 α 0))
    rw [leftResidualD1_zero hα]
    exact (tendsto_leftResidualD1_zero hα).mono_left (by
      exact inf_le_inf_left _ (principal_mono.mpr Ioo_subset_Ioi_self))
  · exact Ioo_mem_nhdsGT zero_lt_one
  · have heq : (fun x : ℝ => deriv (leftResidualD1 α) x) =ᶠ[𝓝[>] (0 : ℝ)]
        leftResidualD2 α := by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
      exact (hasDerivAt_leftResidualD1 hx).deriv
    exact (tendsto_leftResidualD2_zero hα).congr' heq.symm

theorem circleEndpointResidual_symm (α x : ℝ) :
    circleEndpointResidual α (1 - x) = circleEndpointResidual α x := by
  have hsin : Real.sin (Real.pi * (1 - x)) = Real.sin (Real.pi * x) := by
    rw [show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring,
      Real.sin_pi_sub]
  unfold circleEndpointResidual circleProfile endpointModel
  rw [hsin]
  congr 1
  ring

theorem leftResidual_symm {α x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    leftResidual α (1 - x) = leftResidual α x := by
  have hx' : 1 - x ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  rw [leftResidual_eq_circleEndpointResidual hx',
    leftResidual_eq_circleEndpointResidual hx,
    circleEndpointResidual_symm]

theorem leftResidualD1_symm {α x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    leftResidualD1 α (1 - x) = -leftResidualD1 α x := by
  have hx' : 1 - x ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x 1).sub (hasDerivAt_id x) using 1 <;> ring
  have hc := (hasDerivAt_leftResidual (α := α) hx').comp x hsub
  have heq : leftResidual α =ᶠ[𝓝 x]
      (leftResidual α ∘ fun y : ℝ => 1 - y) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (leftResidual_symm hy).symm
  have hc' := hc.congr_of_eventuallyEq heq
  have hu := hc'.unique (hasDerivAt_leftResidual hx)
  linarith

theorem leftResidualD2_symm {α x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    leftResidualD2 α (1 - x) = leftResidualD2 α x := by
  have hx' : 1 - x ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x 1).sub (hasDerivAt_id x) using 1 <;> ring
  have hc := (hasDerivAt_leftResidualD1 (α := α) hx').comp x hsub
  have heq : (fun y : ℝ => -leftResidualD1 α y) =ᶠ[𝓝 x]
      (leftResidualD1 α ∘ fun y : ℝ => 1 - y) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (leftResidualD1_symm hy).symm
  have hc' := hc.congr_of_eventuallyEq heq
  have hr := (hasDerivAt_leftResidualD1 (α := α) hx).neg
  have hu := hc'.unique hr
  linarith

theorem leftResidualD3_symm {α x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    leftResidualD3 α (1 - x) = -leftResidualD3 α x := by
  have hx' : 1 - x ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x 1).sub (hasDerivAt_id x) using 1 <;> ring
  have hc := (hasDerivAt_leftResidualD2 (α := α) hx').comp x hsub
  have heq : leftResidualD2 α =ᶠ[𝓝 x]
      (leftResidualD2 α ∘ fun y : ℝ => 1 - y) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (leftResidualD2_symm hy).symm
  have hc' := hc.congr_of_eventuallyEq heq
  have hu := hc'.unique (hasDerivAt_leftResidualD2 hx)
  linarith

private theorem tendsto_one_sub_nhdsLT_one :
    Tendsto (fun x : ℝ => 1 - x) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · convert (tendsto_const_nhds.sub tendsto_id :
      Tendsto (fun x : ℝ => 1 - x) (𝓝 (1 : ℝ)) (𝓝 (1 - 1))) |>.mono_left inf_le_left <;>
      norm_num
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < 1 - x
    exact sub_pos.mpr hx

theorem leftResidualD3_intervalIntegrable_left {α : ℝ} (hα : 0 < α) :
    IntervalIntegrable (leftResidualD3 α) volume (0 : ℝ) (1 / 2 : ℝ) := by
  have htail : IntervalIntegrable (smoothEndpointTailD3 α) volume
      (0 : ℝ) (1 / 2 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    unfold smoothEndpointTailD3
    have hb : ContinuousOn (fun x : ℝ => (1 - x) ^ (α - 3))
        (Icc (0 : ℝ) (1 / 2 : ℝ)) :=
      (continuousOn_const.sub continuousOn_id).rpow continuousOn_const (by
      intro x hx
      exact Or.inl (by linarith [hx.2] : 1 - x ≠ 0))
    exact continuousOn_const.mul hb
  unfold leftResidualD3
  exact ((leftSingularCorrectionD3_intervalIntegrable hα).sub htail).const_mul _

theorem leftResidualD3_intervalIntegrable {α : ℝ} (hα : 0 < α) :
    IntervalIntegrable (leftResidualD3 α) volume (0 : ℝ) 1 := by
  have hleft := leftResidualD3_intervalIntegrable_left hα
  have href : IntervalIntegrable
      (fun x : ℝ => -leftResidualD3 α (1 - x)) volume (1 / 2 : ℝ) 1 := by
    convert ((hleft.comp_sub_left 1).symm).neg using 1 <;> norm_num
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
    simpa only [mem_singleton_iff] using
      (measure_zero_iff_ae_nmem.mp (Real.volume_singleton (a := (1 : ℝ))))
  have hright : IntervalIntegrable (leftResidualD3 α) volume (1 / 2 : ℝ) 1 := by
    apply href.congr
    filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae hne]
      with x hx hx1
    rw [uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hx
    have hxi : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], lt_of_le_of_ne hx.2 hx1⟩
    linarith [leftResidualD3_symm (α := α) hxi]
  exact hleft.trans hright

theorem tendsto_leftResidualD1_one {α : ℝ} (hα : 0 < α) :
    Tendsto (leftResidualD1 α) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hcomp := (tendsto_leftResidualD1_zero hα).comp tendsto_one_sub_nhdsLT_one
  have hneg := hcomp.neg
  have heq : (fun x : ℝ => -(leftResidualD1 α ∘ fun y : ℝ => 1 - y) x) =ᶠ[𝓝[<] 1]
      leftResidualD1 α := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
    simp only [Function.comp_apply]
    linarith [leftResidualD1_symm (α := α) hx]
  simpa only [neg_zero] using hneg.congr' heq

theorem tendsto_leftResidualD2_one {α : ℝ} (hα : 0 < α) :
    Tendsto (leftResidualD2 α) (𝓝[<] (1 : ℝ))
      (𝓝 ((2 * Real.pi) ^ α * α * (3 - α))) := by
  have hcomp := (tendsto_leftResidualD2_zero hα).comp tendsto_one_sub_nhdsLT_one
  have heq : (leftResidualD2 α ∘ fun y : ℝ => 1 - y) =ᶠ[𝓝[<] 1]
      leftResidualD2 α := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
    exact leftResidualD2_symm hx
  exact hcomp.congr' heq

@[simp] theorem sincPi_one : sincPi 1 = 0 := by
  rw [sincPi_eq one_ne_zero]
  simp [Real.pi_ne_zero]

theorem leftResidual_zero {α : ℝ} (hα : 0 < α) : leftResidual α 0 = 0 := by
  unfold leftResidual leftSingularCorrection smoothEndpointTail
  simp [Real.zero_rpow hα.ne']

theorem leftResidual_one {α : ℝ} (hα : 0 < α) : leftResidual α 1 = 0 := by
  unfold leftResidual leftSingularCorrection smoothEndpointTail sincPiPow
  simp [Real.zero_rpow hα.ne']

theorem tendsto_leftResidual_one {α : ℝ} (hα : 0 < α) :
    Tendsto (leftResidual α) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hcomp := ((continuousAt_leftResidual_zero hα).tendsto.mono_left
    inf_le_left).comp tendsto_one_sub_nhdsLT_one
  have heq : (leftResidual α ∘ fun y : ℝ => 1 - y) =ᶠ[𝓝[<] 1]
      leftResidual α := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
    exact leftResidual_symm hx
  simpa [leftResidual_zero hα] using hcomp.congr' heq

theorem hasDerivWithinAt_leftResidual_one {α : ℝ} (hα : 0 < α) :
    HasDerivWithinAt (leftResidual α) 0 (Iic (1 : ℝ)) 1 := by
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (s := Ioo (0 : ℝ) 1)
  · intro x hx
    exact (hasDerivAt_leftResidual hx).differentiableAt.differentiableWithinAt
  · show Tendsto (leftResidual α) (𝓝[Ioo (0 : ℝ) 1] 1)
      (𝓝 (leftResidual α 1))
    rw [leftResidual_one hα]
    exact (tendsto_leftResidual_one hα).mono_left (by
      exact inf_le_inf_left _ (principal_mono.mpr Ioo_subset_Iio_self))
  · exact Ioo_mem_nhdsLT zero_lt_one
  · have heq : (fun x : ℝ => deriv (leftResidual α) x) =ᶠ[𝓝[<] (1 : ℝ)]
        leftResidualD1 α := by
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
      exact (hasDerivAt_leftResidual hx).deriv
    exact (tendsto_leftResidualD1_one hα).congr' heq.symm

noncomputable def residualDeriv1 (α x : ℝ) : ℝ :=
  if x = 0 ∨ x = 1 then 0 else leftResidualD1 α x

noncomputable def residualDeriv2 (α x : ℝ) : ℝ :=
  if x = 0 ∨ x = 1 then (2 * Real.pi) ^ α * α * (3 - α)
  else leftResidualD2 α x

theorem residualDeriv1_eq {α x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    residualDeriv1 α x = leftResidualD1 α x := by
  simp [residualDeriv1, hx.1.ne', hx.2.ne]

theorem residualDeriv2_eq {α x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    residualDeriv2 α x = leftResidualD2 α x := by
  simp [residualDeriv2, hx.1.ne', hx.2.ne]

@[simp] theorem residualDeriv1_zero (α : ℝ) : residualDeriv1 α 0 = 0 := by
  simp [residualDeriv1]

@[simp] theorem residualDeriv1_one (α : ℝ) : residualDeriv1 α 1 = 0 := by
  simp [residualDeriv1]

@[simp] theorem residualDeriv2_zero (α : ℝ) :
    residualDeriv2 α 0 = (2 * Real.pi) ^ α * α * (3 - α) := by
  simp [residualDeriv2]

@[simp] theorem residualDeriv2_one (α : ℝ) :
    residualDeriv2 α 1 = (2 * Real.pi) ^ α * α * (3 - α) := by
  simp [residualDeriv2]

theorem hasDerivAt_leftResidual_residualDeriv1 {α x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (leftResidual α) (residualDeriv1 α x) x := by
  rw [residualDeriv1_eq hx]
  exact hasDerivAt_leftResidual hx

theorem hasDerivAt_residualDeriv1 {α x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (residualDeriv1 α) (residualDeriv2 α x) x := by
  rw [residualDeriv2_eq hx]
  have heq : residualDeriv1 α =ᶠ[𝓝 x] leftResidualD1 α := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact residualDeriv1_eq hy
  exact (hasDerivAt_leftResidualD1 hx).congr_of_eventuallyEq heq

theorem hasDerivWithinAt_leftResidual_residualDeriv1_zero {α : ℝ}
    (hα : 0 < α) :
    HasDerivWithinAt (leftResidual α) (residualDeriv1 α 0) (Ici (0 : ℝ)) 0 := by
  simp only [residualDeriv1_zero]
  exact hasDerivWithinAt_leftResidual_zero hα

theorem hasDerivWithinAt_leftResidual_residualDeriv1_one {α : ℝ}
    (hα : 0 < α) :
    HasDerivWithinAt (leftResidual α) (residualDeriv1 α 1) (Iic (1 : ℝ)) 1 := by
  simp only [residualDeriv1_one]
  exact hasDerivWithinAt_leftResidual_one hα

theorem tendsto_residualDeriv1_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (residualDeriv1 α) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply (tendsto_leftResidualD1_zero hα).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  exact (residualDeriv1_eq hx).symm

theorem tendsto_residualDeriv1_one {α : ℝ} (hα : 0 < α) :
    Tendsto (residualDeriv1 α) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  apply (tendsto_leftResidualD1_one hα).congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
  exact (residualDeriv1_eq hx).symm

theorem tendsto_residualDeriv2_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (residualDeriv2 α) (𝓝[>] (0 : ℝ))
      (𝓝 ((2 * Real.pi) ^ α * α * (3 - α))) := by
  apply (tendsto_leftResidualD2_zero hα).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  exact (residualDeriv2_eq hx).symm

theorem tendsto_residualDeriv2_one {α : ℝ} (hα : 0 < α) :
    Tendsto (residualDeriv2 α) (𝓝[<] (1 : ℝ))
      (𝓝 ((2 * Real.pi) ^ α * α * (3 - α))) := by
  apply (tendsto_leftResidualD2_one hα).congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
  exact (residualDeriv2_eq hx).symm

theorem hasDerivWithinAt_residualDeriv1_zero {α : ℝ} (hα : 0 < α) :
    HasDerivWithinAt (residualDeriv1 α) (residualDeriv2 α 0)
      (Ici (0 : ℝ)) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ioo (0 : ℝ) 1)
  · intro x hx
    exact (hasDerivAt_residualDeriv1 hx).differentiableAt.differentiableWithinAt
  · show Tendsto (residualDeriv1 α) (𝓝[Ioo (0 : ℝ) 1] 0)
      (𝓝 (residualDeriv1 α 0))
    simp only [residualDeriv1_zero]
    exact (tendsto_residualDeriv1_zero hα).mono_left (by
      exact inf_le_inf_left _ (principal_mono.mpr Ioo_subset_Ioi_self))
  · exact Ioo_mem_nhdsGT zero_lt_one
  · have heq : (fun x : ℝ => deriv (residualDeriv1 α) x) =ᶠ[𝓝[>] (0 : ℝ)]
        residualDeriv2 α := by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
      exact (hasDerivAt_residualDeriv1 hx).deriv
    rw [residualDeriv2_zero]
    exact (tendsto_residualDeriv2_zero hα).congr' heq.symm

theorem hasDerivWithinAt_residualDeriv1_one {α : ℝ} (hα : 0 < α) :
    HasDerivWithinAt (residualDeriv1 α) (residualDeriv2 α 1)
      (Iic (1 : ℝ)) 1 := by
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (s := Ioo (0 : ℝ) 1)
  · intro x hx
    exact (hasDerivAt_residualDeriv1 hx).differentiableAt.differentiableWithinAt
  · show Tendsto (residualDeriv1 α) (𝓝[Ioo (0 : ℝ) 1] 1)
      (𝓝 (residualDeriv1 α 1))
    simp only [residualDeriv1_one]
    exact (tendsto_residualDeriv1_one hα).mono_left (by
      exact inf_le_inf_left _ (principal_mono.mpr Ioo_subset_Iio_self))
  · exact Ioo_mem_nhdsLT zero_lt_one
  · have heq : (fun x : ℝ => deriv (residualDeriv1 α) x) =ᶠ[𝓝[<] (1 : ℝ)]
        residualDeriv2 α := by
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
      exact (hasDerivAt_residualDeriv1 hx).deriv
    rw [residualDeriv2_one]
    exact (tendsto_residualDeriv2_one hα).congr' heq.symm

theorem continuousOn_residualDeriv2 {α : ℝ} (hα : 0 < α) :
    ContinuousOn (residualDeriv2 α) (Icc (0 : ℝ) 1) := by
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hx0
  · have hright : ContinuousWithinAt (residualDeriv2 α) (Ioi (0 : ℝ)) 0 := by
      show Tendsto (residualDeriv2 α) (𝓝[>] (0 : ℝ))
        (𝓝 (residualDeriv2 α 0))
      rw [residualDeriv2_zero]
      exact tendsto_residualDeriv2_zero hα
    exact (continuousWithinAt_singleton.union hright).mono (by
      intro y hy
      by_cases hy0 : y = 0
      · exact Or.inl (by simpa [hy0])
      · exact Or.inr (lt_of_le_of_ne hy.1 (Ne.symm hy0)))
  · rcases hx.2.eq_or_lt with rfl | hx1
    · have hleft : ContinuousWithinAt (residualDeriv2 α) (Iio (1 : ℝ)) 1 := by
        show Tendsto (residualDeriv2 α) (𝓝[<] (1 : ℝ))
          (𝓝 (residualDeriv2 α 1))
        rw [residualDeriv2_one]
        exact tendsto_residualDeriv2_one hα
      exact (hleft.union continuousWithinAt_singleton).mono (by
        intro y hy
        by_cases hy1 : y = 1
        · exact Or.inr (by simpa [hy1])
        · exact Or.inl (lt_of_le_of_ne hy.2 hy1))
    · exact (hasDerivAt_leftResidualD2 (α := α) ⟨hx0, hx1⟩).continuousAt.continuousWithinAt.congr_of_eventuallyEq
        (by
          have hi : ∀ᶠ y in 𝓝[Icc (0 : ℝ) 1] x, y ∈ Ioo (0 : ℝ) 1 :=
            (show ∀ᶠ y in 𝓝 x, y ∈ Ioo (0 : ℝ) 1 from
              Ioo_mem_nhds hx0 hx1).filter_mono inf_le_left
          filter_upwards [self_mem_nhdsWithin, hi] with y _ hy
          exact residualDeriv2_eq hy)
        (residualDeriv2_eq ⟨hx0, hx1⟩)

theorem leftResidual_eq_circleEndpointResidual_on {α : ℝ} (hα : 0 < α) :
    ∀ x ∈ Icc (0 : ℝ) 1, leftResidual α x = circleEndpointResidual α x := by
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hx0
  · rw [leftResidual_zero hα, circleEndpointResidual_zero hα]
  · rcases hx.2.eq_or_lt with rfl | hx1
    · rw [leftResidual_one hα, circleEndpointResidual_one hα]
    · exact leftResidual_eq_circleEndpointResidual ⟨hx0, hx1⟩

theorem hasDerivAt_residualDeriv2 {α x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (residualDeriv2 α) (leftResidualD3 α x) x := by
  have heq : residualDeriv2 α =ᶠ[𝓝 x] leftResidualD2 α := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact residualDeriv2_eq hy
  exact (hasDerivAt_leftResidualD2 hx).congr_of_eventuallyEq heq

/-- The explicit endpoint regularity package for the general circle profile.
The third derivative is controlled by `O(x^(α-1))` at each endpoint. -/
noncomputable def endpointResidualData {α : ℝ} (hα : 0 < α) :
    EndpointResidualData α :=
  EndpointExtension.endpointResidualDataOfLocalTwoJet
    α (leftResidual α) (residualDeriv1 α) (residualDeriv2 α)
      (leftResidualD3 α)
    (leftResidual_eq_circleEndpointResidual_on hα)
    (fun x hx => hasDerivAt_leftResidual_residualDeriv1 hx)
    (hasDerivWithinAt_leftResidual_residualDeriv1_zero hα)
    (hasDerivWithinAt_leftResidual_residualDeriv1_one hα)
    (fun x hx => hasDerivAt_residualDeriv1 hx)
    (hasDerivWithinAt_residualDeriv1_zero hα)
    (hasDerivWithinAt_residualDeriv1_one hα)
    (continuousOn_residualDeriv2 hα)
    (fun x hx => hasDerivAt_residualDeriv2 hx)
    (leftResidualD3_intervalIntegrable hα)
    (by simp)

end BEMOC.CircleGeneral.EndpointRegularity
