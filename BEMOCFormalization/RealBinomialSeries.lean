import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.RingTheory.Binomial

namespace BEMOC

open Filter
open scoped Topology

noncomputable section

/-- The elementary coefficient recurrence for generalized real binomial coefficients. -/
theorem real_choose_succ (β : ℝ) (n : ℕ) :
    (n + 1 : ℝ) * Ring.choose β (n + 1) = (β - n) * Ring.choose β n := by
  have h := Ring.choose_smul_choose (R := ℝ) β (Nat.le_succ n)
  simp only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.succ_sub, Nat.sub_self,
    Ring.choose_one_right] at h
  simpa [mul_comm] using h

theorem real_choose_succ_div (β : ℝ) (n : ℕ) :
    Ring.choose β (n + 1) = ((β - n) / (n + 1)) * Ring.choose β n := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hdiv :
      Ring.choose β (n + 1) = ((β - n) * Ring.choose β n) / (n + 1) := by
    apply (eq_div_iff hn).2
    simpa [mul_comm] using real_choose_succ β n
  rw [hdiv]
  ring

theorem tendsto_abs_real_choose_ratio (β : ℝ) :
    Tendsto (fun n : ℕ ↦ |(β - n) / (n + 1 : ℝ)|) atTop (𝓝 1) := by
  have h' := RCLike.tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) β 1 (-1) (d := 1) one_ne_zero
  have h : Tendsto (fun k : ℕ ↦ (β + -1 * k) / (1 + 1 * k)) atTop (𝓝 (-1 : ℝ)) := by
    simpa only [div_one] using h'
  have ha := (continuous_abs.tendsto (-1)).comp h
  simpa [sub_eq_add_neg, add_comm, mul_comm, mul_left_comm] using ha

/-- The generalized binomial series is absolutely summable throughout its open unit disk. -/
theorem summable_real_choose_mul_pow (β x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ ↦ Ring.choose β n * x ^ n) := by
  obtain ⟨r, hxr, hr⟩ := exists_between hx
  apply summable_of_ratio_norm_eventually_le hr
  have hlim :
      Tendsto (fun n : ℕ ↦ |(β - n) / (n + 1 : ℝ)| * |x|) atTop (𝓝 |x|) := by
    simpa using (tendsto_abs_real_choose_ratio β).mul_const |x|
  filter_upwards [hlim.eventually_le_const hxr] with n hn
  rw [real_choose_succ_div, pow_succ]
  simp only [norm_mul, Real.norm_eq_abs, abs_mul]
  convert mul_le_mul_of_nonneg_right hn
    (mul_nonneg (abs_nonneg (Ring.choose β n)) (abs_nonneg (x ^ n))) using 1 <;> ring

/-- Any fixed polynomial loss is still summable in the generalized
binomial series.  This is the normal-convergence input for any fixed
finite number of termwise differentiations. -/
theorem summable_nat_add_one_pow_mul_real_choose_mul_pow
    (degree : ℕ) (β x : ℝ) (hx : |x| < 1) :
    Summable (fun n : ℕ ↦
      ((n : ℝ) + 1) ^ degree * Ring.choose β n * x ^ n) := by
  obtain ⟨r, hxr, hr⟩ := exists_between hx
  apply summable_of_ratio_norm_eventually_le hr
  have hweight' := RCLike.tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) 2 1 1 (d := 1) one_ne_zero
  have hweight :
      Tendsto (fun n : ℕ ↦ (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ degree)
        atTop (𝓝 1) := by
    have hbase :
        Tendsto (fun n : ℕ ↦ ((n : ℝ) + 2) / ((n : ℝ) + 1))
          atTop (𝓝 1) := by
      simpa [add_comm, mul_comm] using hweight'
    simpa using hbase.pow degree
  have hlim :
      Tendsto (fun n : ℕ ↦
        (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ degree *
          |(β - n) / (n + 1 : ℝ)| * |x|) atTop (𝓝 |x|) := by
    simpa using (hweight.mul (tendsto_abs_real_choose_ratio β)).mul_const |x|
  filter_upwards [hlim.eventually_le_const hxr] with n hn
  rw [real_choose_succ_div, pow_succ]
  simp only [Nat.cast_add, Nat.cast_one, norm_mul, Real.norm_eq_abs, abs_mul,
    abs_pow, abs_of_pos (by positivity : 0 < (n : ℝ) + 1),
    abs_of_pos (by positivity : 0 < (n : ℝ) + 2)]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  convert mul_le_mul_of_nonneg_right hn
    (((n : ℝ) + 1) ^ degree *
      |Ring.choose β n| * |x ^ n| |>.nonneg) using 1
  · field_simp [hn1]
    ring
  · ring

theorem real_succ_mul_choose (β : ℝ) (n : ℕ) :
    (n + 1 : ℝ) * Ring.choose β (n + 1) =
      β * Ring.choose (β - 1) n := by
  have h := Ring.choose_smul_choose (R := ℝ) β (show 1 ≤ n + 1 by omega)
  simp only [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right,
    Nat.succ_sub, Nat.sub_self] at h
  simpa using h

def realBinomialTerm (β : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Ring.choose β n * x ^ n

def realBinomialTermD (β : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * Ring.choose β n * x ^ (n - 1)

theorem hasDerivAt_realBinomialTerm (β : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (realBinomialTerm β n) (realBinomialTermD β n x) x := by
  convert (hasDerivAt_pow n x).const_mul (Ring.choose β n) using 1 <;>
    simp [realBinomialTerm, realBinomialTermD] <;> ring

private def realBinomialDerivativeMajorant (β ρ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else |β * Ring.choose (β - 1) (n - 1) * ρ ^ (n - 1)|

private theorem summable_realBinomialDerivativeMajorant (β ρ : ℝ) (hρ : |ρ| < 1) :
    Summable (realBinomialDerivativeMajorant β ρ) := by
  rw [← summable_nat_add_iff 1]
  simpa [realBinomialDerivativeMajorant, abs_mul, mul_assoc] using
    ((summable_real_choose_mul_pow (β - 1) ρ hρ).mul_left β).norm

private theorem norm_realBinomialTermD_le (β ρ : ℝ) {n : ℕ} {y : ℝ}
    (hρ : 0 ≤ ρ) (hy : |y| ≤ ρ) :
    ‖realBinomialTermD β n y‖ ≤ realBinomialDerivativeMajorant β ρ n := by
  cases n with
  | zero => simp [realBinomialTermD, realBinomialDerivativeMajorant]
  | succ n =>
      unfold realBinomialTermD realBinomialDerivativeMajorant
      simp only [Nat.add_sub_cancel, if_false (by omega : n + 1 ≠ 0), Nat.cast_add,
        Nat.cast_one]
      change
        ‖((n + 1 : ℝ) * Ring.choose β (n + 1)) * y ^ n‖ ≤
          |β * Ring.choose (β - 1) n * ρ ^ n|
      rw [real_succ_mul_choose]
      simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hρ]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg y) hy n)
        (mul_nonneg (abs_nonneg β) (abs_nonneg (Ring.choose (β - 1) n)))

/-- Termwise differentiability of the generalized real binomial series on `(-1,1)`. -/
theorem hasDerivAt_tsum_realBinomialTerm (β x : ℝ) (hx : |x| < 1) :
    HasDerivAt (fun y ↦ ∑' n, realBinomialTerm β n y)
      (∑' n, realBinomialTermD β n x) x := by
  obtain ⟨ρ, hxρ, hρ1⟩ := exists_between hx
  have hρpos : 0 < ρ := (abs_nonneg x).trans_lt hxρ
  apply hasDerivAt_tsum_of_isPreconnected
    (u := realBinomialDerivativeMajorant β ρ) (t := Set.Ioo (-ρ) ρ)
    (g := realBinomialTerm β) (g' := realBinomialTermD β) (y₀ := 0)
  · exact summable_realBinomialDerivativeMajorant β ρ
      (by rw [abs_of_pos hρpos]; exact hρ1)
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro n y _
    exact hasDerivAt_realBinomialTerm β n y
  · intro n y hy
    exact norm_realBinomialTermD_le β ρ hρpos.le
      (le_of_lt (abs_lt.2 hy))
  · exact ⟨neg_lt_zero.mpr hρpos, hρpos⟩
  · simpa [realBinomialTerm] using
      summable_real_choose_mul_pow β 0 (by norm_num)
  · exact abs_lt.mp hxρ

theorem summable_realBinomialTermD (β x : ℝ) (hx : |x| < 1) :
    Summable (fun n ↦ realBinomialTermD β n x) := by
  rw [← summable_nat_add_iff 1]
  simpa [realBinomialTermD, realBinomialTerm, real_succ_mul_choose, mul_assoc] using
    (summable_real_choose_mul_pow (β - 1) x hx).mul_left β

theorem tsum_realBinomialTermD_eq (β x : ℝ) (hx : |x| < 1) :
    ∑' n, realBinomialTermD β n x =
      β * ∑' n, realBinomialTerm (β - 1) n x := by
  have hd := summable_realBinomialTermD β x hx
  rw [hd.tsum_eq_zero_add]
  simp only [realBinomialTermD, Nat.cast_zero, zero_mul, Nat.zero_sub, pow_zero, zero_add]
  simp only [realBinomialTerm]
  rw [← (summable_real_choose_mul_pow (β - 1) x hx).tsum_mul_left β]
  congr 1
  funext n
  simp only [realBinomialTerm, realBinomialTermD, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel]
  rw [real_succ_mul_choose]
  ring

theorem hasDerivAt_tsum_realBinomialTerm_eq (β x : ℝ) (hx : |x| < 1) :
    HasDerivAt (fun y ↦ ∑' n, realBinomialTerm β n y)
      (β * ∑' n, realBinomialTerm (β - 1) n x) x := by
  simpa only [tsum_realBinomialTermD_eq β x hx] using
    hasDerivAt_tsum_realBinomialTerm β x hx

theorem real_choose_succ_pascal (β : ℝ) (n : ℕ) :
    Ring.choose β (n + 1) =
      Ring.choose (β - 1) n + Ring.choose (β - 1) (n + 1) := by
  have h := Ring.choose_succ_succ (R := ℝ) (β - 1) n
  simpa using h

/-- Pascal's recursion evaluated inside the open disk. -/
theorem tsum_realBinomialTerm_pascal (β x : ℝ) (hx : |x| < 1) :
    ∑' n, realBinomialTerm β n x =
      (1 + x) * ∑' n, realBinomialTerm (β - 1) n x := by
  let L := ∑' n, realBinomialTerm (β - 1) n x
  have hL : Summable (fun n ↦ realBinomialTerm (β - 1) n x) := by
    simpa [realBinomialTerm] using summable_real_choose_mul_pow (β - 1) x hx
  have hA :
      HasSum (fun n ↦ x * realBinomialTerm (β - 1) n x) (x * L) :=
    hL.hasSum.mul_left x
  have hB :
      HasSum (fun n ↦ realBinomialTerm (β - 1) (n + 1) x) (L - 1) := by
    have h := (hasSum_nat_add_iff' 1).2 hL.hasSum
    simpa only [Finset.sum_range_one, realBinomialTerm, Ring.choose_zero_right, pow_zero,
      mul_one] using h
  have htail := hA.add hB
  have hterm (n : ℕ) :
      realBinomialTerm β (n + 1) x =
        x * realBinomialTerm (β - 1) n x +
          realBinomialTerm (β - 1) (n + 1) x := by
    unfold realBinomialTerm
    rw [real_choose_succ_pascal β n, pow_succ]
    ring
  have htail' :
      HasSum (fun n ↦ realBinomialTerm β (n + 1) x) (x * L + (L - 1)) :=
    htail.congr (fun n ↦ (hterm n).symm)
  have hfull :
      HasSum (fun n ↦ realBinomialTerm β n x)
        (x * L + (L - 1) + realBinomialTerm β 0 x) :=
    (hasSum_nat_add_iff 1).1 htail'
  rw [hfull.tsum_eq]
  simp only [realBinomialTerm, Ring.choose_zero_right, pow_zero, mul_one]
  ring

def realBinomialSum (β x : ℝ) : ℝ :=
  ∑' n, realBinomialTerm β n x

theorem hasDerivAt_realBinomialSum_ode (β x : ℝ) (hx : |x| < 1) :
    HasDerivAt (realBinomialSum β)
      ((β / (1 + x)) * realBinomialSum β x) x := by
  have hbase : 1 + x ≠ 0 := by
    have := (abs_lt.mp hx).1
    linarith
  have hderiv := hasDerivAt_tsum_realBinomialTerm_eq β x hx
  rw [tsum_realBinomialTerm_pascal β x hx] at hderiv
  convert hderiv using 1
  · rfl
  · simp only [realBinomialSum]
    field_simp

theorem realBinomialSum_zero (β : ℝ) : realBinomialSum β 0 = 1 := by
  unfold realBinomialSum
  rw [tsum_eq_single 0]
  · simp [realBinomialTerm, Ring.choose_zero_right]
  · intro n hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    simp [realBinomialTerm, zero_pow hnpos.ne']

private theorem hasDerivAt_realBinomialSum_mul_negRpow (β x : ℝ) (hx : |x| < 1) :
    HasDerivAt
      (fun y ↦ realBinomialSum β y * (1 + y) ^ (-β))
      0 x := by
  have hbase : 0 < 1 + x := by
    have := (abs_lt.mp hx).1
    linarith
  have hF := hasDerivAt_realBinomialSum_ode β x hx
  have hp :
      HasDerivAt (fun y : ℝ ↦ (1 + y) ^ (-β))
        ((-β) * (1 + x) ^ (-β - 1)) x := by
    simpa using
      ((hasDerivAt_const x 1).add (hasDerivAt_id x)).rpow_const
        (Or.inl hbase.ne')
  convert hF.mul hp using 1
  rw [Real.rpow_sub_one hbase.ne' (-β)]
  field_simp
  ring

/-- The generalized real binomial theorem on the full open unit disk. -/
theorem tsum_real_choose_mul_pow_eq_rpow (β x : ℝ) (hx : |x| < 1) :
    ∑' n : ℕ, Ring.choose β n * x ^ n = (1 + x) ^ β := by
  let H : ℝ → ℝ := fun y ↦ realBinomialSum β y * (1 + y) ^ (-β)
  have hdiff : DifferentiableOn ℝ H (Set.Ioo (-1) 1) := by
    intro y hy
    exact (hasDerivAt_realBinomialSum_mul_negRpow β y
      (abs_lt.2 hy)).differentiableAt.differentiableWithinAt
  have hzero : Set.Ioo (-1 : ℝ) 1 |>.EqOn (deriv H) 0 := by
    intro y hy
    exact (hasDerivAt_realBinomialSum_mul_negRpow β y (abs_lt.2 hy)).deriv
  have hconst :
      H x = H 0 :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero
      (abs_lt.2 hx) (by norm_num)
  have hHx : H x = 1 := by
    rw [hconst]
    simp [H, realBinomialSum_zero]
  have hbase : 0 < 1 + x := by
    have := (abs_lt.mp hx).1
    linarith
  change realBinomialSum β x = (1 + x) ^ β
  dsimp [H] at hHx
  rw [Real.rpow_neg hbase.le] at hHx
  have hp : (1 + x) ^ β ≠ 0 := (Real.rpow_pos_of_pos hbase β).ne'
  field_simp [hp] at hHx
  exact hHx

end

end BEMOC
