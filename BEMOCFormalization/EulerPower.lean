import Mathlib

/-!
# Power-sum Euler--Maclaurin increment bound

This module is independent of the canonical development.  It proves the local
real-power estimate needed for the finite power-sum part of Lemma 3.1 in
`BEMOCRieszEnergies.tex`.
-/

open scoped BigOperators Topology
open Filter Set Asymptotics

namespace EulerPower

noncomputable def powerSum (α : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 N, (k : ℝ) ^ α

theorem powerSum_succ (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    powerSum α (N + 1) = powerSum α N + (N : ℝ) ^ α := by
  simpa only [powerSum] using
    Finset.sum_Ico_succ_top hN (fun k : ℕ => (k : ℝ) ^ α)

noncomputable def renormalizedPowerSum (α : ℝ) (N : ℕ) : ℝ :=
  powerSum α N
    - (N : ℝ) ^ (α + 1) / (α + 1)
    + (1 / 2 : ℝ) * (N : ℝ) ^ α
    - (α / 12) * (N : ℝ) ^ (α - 1)

noncomputable def powerSumIncrement (α : ℝ) (n : ℕ) : ℝ :=
  renormalizedPowerSum α (n + 1) - renormalizedPowerSum α n

theorem powerSumIncrement_eq (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    powerSumIncrement α N =
      (N : ℝ) ^ α
      - ((N + 1 : ℕ) : ℝ) ^ (α + 1) / (α + 1)
      + (N : ℝ) ^ (α + 1) / (α + 1)
      + (1 / 2 : ℝ) *
          (((N + 1 : ℕ) : ℝ) ^ α - (N : ℝ) ^ α)
      - (α / 12) *
          (((N + 1 : ℕ) : ℝ) ^ (α - 1) - (N : ℝ) ^ (α - 1)) := by
  rw [powerSumIncrement, renormalizedPowerSum, renormalizedPowerSum,
    powerSum_succ α hN]
  ring

/-! ## Taylor expansion of `(1+x)^p` -/

noncomputable def fallingCoeff (p : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (p - k)

@[simp] theorem fallingCoeff_zero (p : ℝ) : fallingCoeff p 0 = 1 := by
  simp [fallingCoeff]

theorem fallingCoeff_succ (p : ℝ) (n : ℕ) :
    fallingCoeff p (n + 1) = fallingCoeff p n * (p - n) := by
  simp [fallingCoeff, Finset.prod_range_succ]

theorem iteratedDeriv_one_add_rpow (p : ℝ) :
    ∀ (n : ℕ) (x : ℝ), -1 < x →
      iteratedDeriv n (fun y : ℝ => (1 + y) ^ p) x =
        fallingCoeff p n * (1 + x) ^ (p - n)
  := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simp
  | succ n ih =>
      intro x hx
      rw [show n + 1 = Nat.succ n by omega, iteratedDeriv_succ]
      have heq :
          iteratedDeriv n (fun y : ℝ => (1 + y) ^ p) =ᶠ[𝓝 x]
            fun y : ℝ => fallingCoeff p n * (1 + y) ^ (p - n) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        exact ih y hy
      rw [Filter.EventuallyEq.deriv_eq heq]
      have hbase : 1 + x ≠ 0 := by linarith
      have hadd : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
        simpa using (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
      have hd : HasDerivAt
          (fun y : ℝ => fallingCoeff p n * (1 + y) ^ (p - n))
          (fallingCoeff p n * ((p - n) * (1 + x) ^ (p - n - 1))) x := by
        simpa only [Function.comp_apply, mul_one] using
          ((Real.hasDerivAt_rpow_const (p := p - n) (Or.inl hbase)).comp x hadd).const_mul
            (fallingCoeff p n)
      rw [hd.deriv, fallingCoeff_succ]
      push_cast
      ring

theorem iteratedDerivWithin_Ioi_neg_one_at_zero (p : ℝ) (n : ℕ) :
    iteratedDerivWithin n (fun y : ℝ => (1 + y) ^ p) (Ioi (-1)) 0 =
      iteratedDeriv n (fun y : ℝ => (1 + y) ^ p) 0 := by
  have hset : Ioi (-1 : ℝ) =ᶠ[𝓝 0] Set.univ := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0)] with y hy
    apply propext
    change (-1 < y) ↔ True
    exact iff_true_intro hy
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedDeriv_eq_iteratedFDeriv]
  rw [iteratedFDerivWithin_congr_set (f := fun y : ℝ => (1 + y) ^ p)
    (s := Ioi (-1)) (t := Set.univ) (x := 0) hset n,
    iteratedFDerivWithin_univ]

theorem contDiffOn_one_add_rpow (p : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun y : ℝ => (1 + y) ^ p) (Ioi (-1)) := by
  intro x hx
  have hbase : 1 + x ≠ 0 := by
    rw [Set.mem_Ioi] at hx
    linarith
  have hadd : ContDiffAt ℝ n (fun y : ℝ => 1 + y) x :=
    contDiffAt_const.add contDiffAt_id
  exact ((Real.contDiffAt_rpow_const_of_ne (n := n) hbase).comp x hadd).contDiffWithinAt

noncomputable def rpowTaylor (p : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    ((k.factorial : ℕ) : ℝ)⁻¹ * x ^ k * fallingCoeff p k

theorem taylorWithinEval_one_add_rpow_eq (p : ℝ) (n : ℕ) (x : ℝ) :
    taylorWithinEval (fun y : ℝ => (1 + y) ^ p) n (Ioi (-1)) 0 x =
      rpowTaylor p n x := by
  rw [taylor_within_apply, rpowTaylor]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_Ioi_neg_one_at_zero,
    iteratedDeriv_one_add_rpow p k 0 (by norm_num)]
  simp only [Nat.cast_ofNat, zero_add, add_zero, mul_one, sub_zero, smul_eq_mul]
  rw [show (1 : ℝ) ^ (p - (k : ℝ)) = 1 by exact Real.one_rpow _]
  ring

theorem one_add_rpow_sub_taylor_isLittleO (p : ℝ) (n : ℕ) :
    (fun x : ℝ => (1 + x) ^ p - rpowTaylor p n x) =o[𝓝 0]
      (fun x : ℝ => x ^ n) := by
  have h := taylor_isLittleO (s := Ioi (-1)) (convex_Ioi (-1 : ℝ))
    (show (0 : ℝ) ∈ Ioi (-1) by norm_num) (contDiffOn_one_add_rpow p n)
  rw [nhdsWithin_eq_nhds.2 (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0))] at h
  simpa only [sub_zero, taylorWithinEval_one_add_rpow_eq] using h

theorem rpowTaylor_two (p x : ℝ) :
    rpowTaylor p 2 x =
      1 + p * x + p * (p - 1) / 2 * x ^ 2 := by
  norm_num [rpowTaylor, fallingCoeff, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

theorem rpowTaylor_three (p x : ℝ) :
    rpowTaylor p 3 x =
      1 + p * x + p * (p - 1) / 2 * x ^ 2 +
        p * (p - 1) * (p - 2) / 6 * x ^ 3 := by
  norm_num [rpowTaylor, fallingCoeff, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

theorem rpowTaylor_four (p x : ℝ) :
    rpowTaylor p 4 x =
      1 + p * x + p * (p - 1) / 2 * x ^ 2 +
        p * (p - 1) * (p - 2) / 6 * x ^ 3 +
        p * (p - 1) * (p - 2) * (p - 3) / 24 * x ^ 4 := by
  norm_num [rpowTaylor, fallingCoeff, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-! ## Cancellation in the normalized local increment -/

noncomputable def localIncrement (α x : ℝ) : ℝ :=
  1 - ((1 + x) ^ (α + 1) - 1) / ((α + 1) * x) +
    (1 / 2 : ℝ) * ((1 + x) ^ α - 1) -
    (α / 12) * x * ((1 + x) ^ (α - 1) - 1)

noncomputable def localPolynomialPart (α x : ℝ) : ℝ :=
  1 - (rpowTaylor (α + 1) 4 x - 1) / ((α + 1) * x) +
    (1 / 2 : ℝ) * (rpowTaylor α 3 x - 1) -
    (α / 12) * x * (rpowTaylor (α - 1) 2 x - 1)

noncomputable def localRemainderFour (α x : ℝ) : ℝ :=
  (1 + x) ^ (α + 1) - rpowTaylor (α + 1) 4 x

noncomputable def localRemainderThree (α x : ℝ) : ℝ :=
  (1 + x) ^ α - rpowTaylor α 3 x

noncomputable def localRemainderTwo (α x : ℝ) : ℝ :=
  (1 + x) ^ (α - 1) - rpowTaylor (α - 1) 2 x

theorem localIncrement_decomposition {α x : ℝ} (hα : α + 1 ≠ 0) (hx : x ≠ 0) :
    localIncrement α x =
      localPolynomialPart α x -
        (α + 1)⁻¹ * (localRemainderFour α x * x⁻¹) +
        (1 / 2 : ℝ) * localRemainderThree α x -
        (α / 12) * (x * localRemainderTwo α x) := by
  simp only [localIncrement, localPolynomialPart, localRemainderFour,
    localRemainderThree, localRemainderTwo]
  field_simp [hα, hx]
  ring

theorem localPolynomialPart_eq_zero {α x : ℝ} (hα : α + 1 ≠ 0) (hx : x ≠ 0) :
    localPolynomialPart α x = 0 := by
  rw [localPolynomialPart, rpowTaylor_four, rpowTaylor_three, rpowTaylor_two]
  field_simp [hα, hx]
  ring

theorem localIncrement_isLittleO (α : ℝ) (hα : α + 1 ≠ 0) :
    localIncrement α =o[𝓝[≠] 0] (fun x : ℝ => x ^ 3) := by
  have h4 : localRemainderFour α =o[𝓝[≠] 0] (fun x : ℝ => x ^ 4) := by
    simpa only [localRemainderFour] using
      (one_add_rpow_sub_taylor_isLittleO (α + 1) 4).mono nhdsWithin_le_nhds
  have h3 : localRemainderThree α =o[𝓝[≠] 0] (fun x : ℝ => x ^ 3) := by
    simpa only [localRemainderThree] using
      (one_add_rpow_sub_taylor_isLittleO α 3).mono nhdsWithin_le_nhds
  have h2 : localRemainderTwo α =o[𝓝[≠] 0] (fun x : ℝ => x ^ 2) := by
    simpa only [localRemainderTwo] using
      (one_add_rpow_sub_taylor_isLittleO (α - 1) 2).mono nhdsWithin_le_nhds
  have hpow43 :
      (fun x : ℝ => x ^ 4 * x⁻¹) =ᶠ[𝓝[≠] 0] (fun x : ℝ => x ^ 3) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    field_simp [hx0]
    ring
  have hpow12 :
      (fun x : ℝ => x * x ^ 2) =ᶠ[𝓝[≠] 0] (fun x : ℝ => x ^ 3) := by
    exact Filter.Eventually.of_forall (fun x => by ring)
  have h4div :
      (fun x : ℝ => localRemainderFour α x * x⁻¹) =o[𝓝[≠] 0]
        (fun x : ℝ => x ^ 3) := by
    exact (h4.mul_isBigO (isBigO_refl (fun x : ℝ => x⁻¹) _)).congr'
      Filter.EventuallyEq.rfl hpow43
  have hxR2 :
      (fun x : ℝ => x * localRemainderTwo α x) =o[𝓝[≠] 0]
        (fun x : ℝ => x ^ 3) := by
    exact ((isBigO_refl (fun x : ℝ => x) _).mul_isLittleO h2).congr'
      Filter.EventuallyEq.rfl hpow12
  have hsum :
      (fun x : ℝ =>
        -(α + 1)⁻¹ * (localRemainderFour α x * x⁻¹) +
          (1 / 2 : ℝ) * localRemainderThree α x -
          (α / 12) * (x * localRemainderTwo α x)) =o[𝓝[≠] 0]
        (fun x : ℝ => x ^ 3) := by
    exact (h4div.const_mul_left (-(α + 1)⁻¹)).add
      (h3.const_mul_left (1 / 2)) |>.sub (hxR2.const_mul_left (α / 12))
  have heq :
      localIncrement α =ᶠ[𝓝[≠] 0]
        (fun x : ℝ =>
          -(α + 1)⁻¹ * (localRemainderFour α x * x⁻¹) +
            (1 / 2 : ℝ) * localRemainderThree α x -
            (α / 12) * (x * localRemainderTwo α x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    rw [localIncrement_decomposition hα hx0, localPolynomialPart_eq_zero hα hx0]
    ring
  exact hsum.congr' heq.symm Filter.EventuallyEq.rfl

/-! ## Transfer from the local variable `x = 1/n` to `n → ∞` -/

theorem nat_succ_rpow_factor {n : ℕ} (hn : 1 ≤ n) (p : ℝ) :
    (((n + 1 : ℕ) : ℝ) ^ p) =
      (n : ℝ) ^ p * (1 + 1 / (n : ℝ)) ^ p := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hfac : ((n + 1 : ℕ) : ℝ) =
      (n : ℝ) * (1 + 1 / (n : ℝ)) := by
    push_cast
    field_simp [hnpos.ne']
  rw [hfac, Real.mul_rpow hnpos.le (by positivity)]

theorem powerSumIncrement_eq_rpow_mul_localIncrement
    {α : ℝ} (hα : α + 1 ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    powerSumIncrement α n =
      (n : ℝ) ^ α * localIncrement α (1 / (n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  rw [powerSumIncrement_eq α hn,
    nat_succ_rpow_factor hn (α + 1),
    nat_succ_rpow_factor hn α,
    nat_succ_rpow_factor hn (α - 1),
    localIncrement,
    Real.rpow_add_one hnpos.ne' α,
    Real.rpow_sub_one hnpos.ne' α]
  field_simp [hα, hnpos.ne']
  ring

theorem tendsto_one_div_nat_punctured :
    Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝[≠] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt hn)
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, div_eq_zero_iff,
    one_ne_zero, false_or, not_false_eq_true] using hn0

theorem rpow_mul_one_div_cube_eventually (α : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ α * (1 / (n : ℝ)) ^ 3) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (α - 3)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  rw [Real.rpow_sub hnpos α 3]
  field_simp [hnpos.ne']
  exact Or.inl (Real.rpow_natCast (n : ℝ) 3)

/-- The missing local estimate for the power-sum Euler--Maclaurin constant. -/
theorem powerSumIncrement_isBigO (α : ℝ) (hα0 : 0 < α) :
    powerSumIncrement α =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (α - 3)) := by
  have hαne : α + 1 ≠ 0 := by linarith
  have hlocal :
      (fun n : ℕ => localIncrement α (1 / (n : ℝ))) =o[atTop]
        (fun n : ℕ => (1 / (n : ℝ)) ^ 3) :=
    (localIncrement_isLittleO α hαne).comp_tendsto tendsto_one_div_nat_punctured
  have hprod :
      (fun n : ℕ => (n : ℝ) ^ α * localIncrement α (1 / (n : ℝ))) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ α * (1 / (n : ℝ)) ^ 3) :=
    (isBigO_refl (fun n : ℕ => (n : ℝ) ^ α) atTop).mul hlocal.isBigO
  have hleft :
      powerSumIncrement α =ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) ^ α * localIncrement α (1 / (n : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact powerSumIncrement_eq_rpow_mul_localIncrement hαne hn
  exact hprod.congr' hleft.symm (rpow_mul_one_div_cube_eventually α)

theorem summable_powerSumIncrement (α : ℝ) (hα0 : 0 < α) (hα2 : α < 2) :
    Summable (powerSumIncrement α) := by
  apply summable_of_isBigO_nat ((Real.summable_nat_rpow).2 ?_)
    (powerSumIncrement_isBigO α hα0)
  linarith

theorem powerSumIncrement_isBigO_of_mem_Ioo {α : ℝ} (hα : α ∈ Ioo 0 2) :
    powerSumIncrement α =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (α - 3)) :=
  powerSumIncrement_isBigO α hα.1

theorem summable_powerSumIncrement_of_mem_Ioo {α : ℝ} (hα : α ∈ Ioo 0 2) :
    Summable (powerSumIncrement α) :=
  summable_powerSumIncrement α hα.1 hα.2

/-! ## The convergent Euler--Maclaurin constant -/

/-- The constant selected by the corrected finite power sums.  Identifying
this real number with the analytically continued value `ζ(-α)` is the
remaining zeta-identification step; convergence itself is unconditional in
the paper's range. -/
noncomputable def powerSumConstant (α : ℝ) : ℝ :=
  renormalizedPowerSum α 0 + ∑' n : ℕ, powerSumIncrement α n

/-- Exact telescoping of the corrected increments. -/
theorem sum_powerSumIncrement (α : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, powerSumIncrement α n =
      renormalizedPowerSum α N - renormalizedPowerSum α 0 := by
  simpa only [powerSumIncrement] using
    Finset.sum_range_sub (renormalizedPowerSum α) N

/-- The corrected power sums converge for every `0 < α < 2`. -/
theorem tendsto_renormalizedPowerSum {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Tendsto (renormalizedPowerSum α) atTop (𝓝 (powerSumConstant α)) := by
  have hsum := (summable_powerSumIncrement α hα0 hα2).hasSum.tendsto_sum_nat
  have heq :
      (fun N => ∑ n ∈ Finset.range N, powerSumIncrement α n) =
        fun N => renormalizedPowerSum α N - renormalizedPowerSum α 0 := by
    funext N
    exact sum_powerSumIncrement α N
  rw [heq] at hsum
  have hadd := hsum.add_const (renormalizedPowerSum α 0)
  convert hadd using 1
  · funext N
    ring
  · unfold powerSumConstant
    ring

/-- Membership-form wrapper for the paper's parameter range. -/
theorem tendsto_renormalizedPowerSum_of_mem_Ioo {α : ℝ} (hα : α ∈ Ioo 0 2) :
    Tendsto (renormalizedPowerSum α) atTop (𝓝 (powerSumConstant α)) :=
  tendsto_renormalizedPowerSum hα.1 hα.2

/-! ## Independent check at `α = 1` -/

theorem powerSum_one (N : ℕ) :
    powerSum 1 N = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
  induction N with
  | zero => simp [powerSum]
  | succ N ih =>
      rcases N with _ | N
      · simp [powerSum]
      · rw [powerSum_succ 1 (by omega : 1 ≤ N + 1), ih, Real.rpow_one]
        push_cast
        ring

theorem renormalizedPowerSum_one (N : ℕ) :
    renormalizedPowerSum 1 N = -1 / 12 := by
  rw [renormalizedPowerSum, powerSum_one, Real.rpow_one]
  norm_num
  push_cast
  by_cases hN : N = 0
  · simp [hN]
  ring

theorem powerSumConstant_one : powerSumConstant 1 = -1 / 12 := by
  unfold powerSumConstant powerSumIncrement
  simp_rw [renormalizedPowerSum_one, sub_self]
  simp

end EulerPower
