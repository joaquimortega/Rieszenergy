import Mathlib
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.Taylor

/-!
# Complex Euler--Maclaurin continuation for the power-sum constant

This module supplies Taylor estimates for complex powers on positive real
intervals.  They are used in the analytic continuation of the corrected
power-sum finite part.
-/

open scoped BigOperators Topology Real Interval
open Filter Set Asymptotics MeasureTheory

namespace ComplexPowerTaylor

noncomputable def powerFun (p : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ p

theorem hasDerivAt_powerFun {p : ℂ} {x : ℝ} (hx : 0 < x) :
    HasDerivAt (powerFun p) (p * (x : ℂ) ^ (p - 1)) x := by
  have hbase : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x :=
    Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  have hslit : (x : ℂ) ∈ Complex.slitPlane := by
    simpa [Complex.mem_slitPlane_iff] using hx
  simpa only [powerFun, mul_one] using
    ((Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt.comp_ofReal)

noncomputable def fallingCoeff (p : ℂ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, (p - k)

@[simp] theorem fallingCoeff_zero (p : ℂ) : fallingCoeff p 0 = 1 := by
  simp [fallingCoeff]

theorem fallingCoeff_succ (p : ℂ) (n : ℕ) :
    fallingCoeff p (n + 1) = fallingCoeff p n * (p - n) := by
  simp [fallingCoeff, Finset.prod_range_succ]

theorem iteratedDeriv_powerFun (p : ℂ) :
    ∀ (n : ℕ) (x : ℝ), 0 < x →
      iteratedDeriv n (powerFun p) x =
        fallingCoeff p n * (x : ℂ) ^ (p - n) := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simp [powerFun]
  | succ n ih =>
      intro x hx
      rw [show n + 1 = Nat.succ n by omega, iteratedDeriv_succ]
      have heq :
          iteratedDeriv n (powerFun p) =ᶠ[𝓝 x]
            fun y : ℝ => fallingCoeff p n * (y : ℂ) ^ (p - n) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        exact ih y hy
      rw [Filter.EventuallyEq.deriv_eq heq]
      have hd : HasDerivAt
          (fun y : ℝ => fallingCoeff p n * (y : ℂ) ^ (p - n))
          (fallingCoeff p n *
            ((p - n) * (x : ℂ) ^ ((p - n) - 1))) x := by
        simpa only [mul_one] using
          (hasDerivAt_powerFun (p := p - n) hx).const_mul
            (fallingCoeff p n)
      rw [hd.deriv, fallingCoeff_succ]
      push_cast
      ring_nf

theorem contDiffOn_powerFun (p : ℂ) (n : ℕ) :
    ContDiffOn ℝ n (powerFun p) (Ioi 0) := by
  intro x hx
  have heq : powerFun p =ᶠ[𝓝 x]
      fun y : ℝ => Complex.exp ((Real.log y : ℂ) * p) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [powerFun, Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne')]
    rw [Complex.ofReal_log hy.le]
  have h : ContDiffAt ℝ n
      (fun y : ℝ => Complex.exp ((Real.log y : ℂ) * p)) x := by
    have hlog : ContDiffAt ℝ n Real.log x :=
      (Real.contDiffAt_log.mpr hx.ne')
    have hcast : ContDiffAt ℝ n (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog
    exact (hcast.mul contDiffAt_const).cexp
  exact (h.congr_of_eventuallyEq heq).contDiffWithinAt

theorem iteratedDerivWithin_powerFun_Icc (p : ℂ) (k : ℕ)
    {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx : x ∈ Icc (m : ℝ) (m + 1 : ℝ)) :
    iteratedDerivWithin k (powerFun p) (Icc (m : ℝ) (m + 1 : ℝ)) x =
      fallingCoeff p k * (x : ℂ) ^ (p - k) := by
  have hlt : (m : ℝ) < m + 1 := by norm_num
  have hpos : 0 < x := lt_of_lt_of_le (by exact_mod_cast (show 0 < m by omega)) hx.1
  have hcd : ContDiffAt ℝ k (powerFun p) x :=
    (contDiffOn_powerFun p k x hpos).contDiffAt (Ioi_mem_nhds hpos)
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc hlt) hcd hx]
  change iteratedDeriv k (powerFun p) x = _
  exact iteratedDeriv_powerFun p k x hpos

theorem taylorWithinEval_powerFun_two (p : ℂ) {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    taylorWithinEval (powerFun p) 2 (Icc (m : ℝ) (m + 1 : ℝ)) (m : ℝ) x =
      (m : ℂ) ^ p + (x - m) * (p * (m : ℂ) ^ (p - 1)) +
        (x - m) ^ 2 / 2 * (p * (p - 1) * (m : ℂ) ^ (p - 2)) := by
  have hm_mem : (m : ℝ) ∈ Icc (m : ℝ) (m + 1 : ℝ) :=
    left_mem_Icc.mpr (by norm_num)
  have h1 := iteratedDerivWithin_powerFun_Icc p 1 hm hm_mem
  have h2 := iteratedDerivWithin_powerFun_Icc p 2 hm hm_mem
  have hf2 : fallingCoeff p 2 = p * (p - 1) := by
    norm_num [fallingCoeff, Finset.prod_range_succ]
  have h1' : derivWithin (powerFun p) (Icc (m : ℝ) (m + 1 : ℝ)) m =
      fallingCoeff p 1 * (m : ℂ) ^ (p - 1) := by
    simpa using h1
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ]
  rw [h1', h2]
  rw [hf2]
  norm_num [fallingCoeff, powerFun]
  push_cast
  ring
  simp

theorem powerFun_taylor_two_bound {p : ℂ} (hp : p.re < 2)
    {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx : x ∈ Icc (m : ℝ) (m + 1 : ℝ)) :
    ‖powerFun p x -
        ((m : ℂ) ^ p + (x - m) * (p * (m : ℂ) ^ (p - 1)) +
          (x - m) ^ 2 / 2 * (p * (p - 1) * (m : ℂ) ^ (p - 2)))‖ ≤
      ‖fallingCoeff p 3‖ * (m : ℝ) ^ (p.re - 3) * (x - m) ^ 3 / 2 := by
  have hlt : (m : ℝ) < m + 1 := by norm_num
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsub : Icc (m : ℝ) (m + 1 : ℝ) ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact lt_of_lt_of_le hmpos hy.1
  have hcd : ContDiffOn ℝ 3 (powerFun p) (Icc (m : ℝ) (m + 1 : ℝ)) :=
    (contDiffOn_powerFun p 3).mono hsub
  have hC : ∀ y ∈ Icc (m : ℝ) (m + 1 : ℝ),
      ‖iteratedDerivWithin 3 (powerFun p) (Icc (m : ℝ) (m + 1 : ℝ)) y‖ ≤
        ‖fallingCoeff p 3‖ * (m : ℝ) ^ (p.re - 3) := by
    intro y hy
    rw [iteratedDerivWithin_powerFun_Icc p 3 hm hy, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hmpos hy.1)]
    have hexp : (p - (3 : ℕ)).re = p.re - 3 := by norm_num
    rw [hexp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_nonpos hmpos hy.1 (by linarith)
  have h := taylor_mean_remainder_bound (E := ℂ) (n := 2)
    (le_of_lt hlt) hcd hx hC
  rw [taylorWithinEval_powerFun_two p hm x] at h
  norm_num at h ⊢
  exact h

theorem taylorWithinEval_powerFun_one (p : ℂ) {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    taylorWithinEval (powerFun p) 1 (Icc (m : ℝ) (m + 1 : ℝ)) (m : ℝ) x =
      (m : ℂ) ^ p + (x - m) * (p * (m : ℂ) ^ (p - 1)) := by
  have hm_mem : (m : ℝ) ∈ Icc (m : ℝ) (m + 1 : ℝ) :=
    left_mem_Icc.mpr (by norm_num)
  have h1 := iteratedDerivWithin_powerFun_Icc p 1 hm hm_mem
  have h1' : derivWithin (powerFun p) (Icc (m : ℝ) (m + 1 : ℝ)) m =
      fallingCoeff p 1 * (m : ℂ) ^ (p - 1) := by
    simpa using h1
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ]
  rw [h1']
  norm_num [fallingCoeff, powerFun]

theorem powerFun_taylor_one_bound {p : ℂ} (hp : p.re < 1)
    {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx : x ∈ Icc (m : ℝ) (m + 1 : ℝ)) :
    ‖powerFun p x -
        ((m : ℂ) ^ p + (x - m) * (p * (m : ℂ) ^ (p - 1)))‖ ≤
      ‖fallingCoeff p 2‖ * (m : ℝ) ^ (p.re - 2) * (x - m) ^ 2 := by
  have hlt : (m : ℝ) < m + 1 := by norm_num
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsub : Icc (m : ℝ) (m + 1 : ℝ) ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact lt_of_lt_of_le hmpos hy.1
  have hcd : ContDiffOn ℝ 2 (powerFun p) (Icc (m : ℝ) (m + 1 : ℝ)) :=
    (contDiffOn_powerFun p 2).mono hsub
  have hC : ∀ y ∈ Icc (m : ℝ) (m + 1 : ℝ),
      ‖iteratedDerivWithin 2 (powerFun p) (Icc (m : ℝ) (m + 1 : ℝ)) y‖ ≤
        ‖fallingCoeff p 2‖ * (m : ℝ) ^ (p.re - 2) := by
    intro y hy
    rw [iteratedDerivWithin_powerFun_Icc p 2 hm hy, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hmpos hy.1)]
    have hexp : (p - (2 : ℕ)).re = p.re - 2 := by norm_num
    rw [hexp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_nonpos hmpos hy.1 (by linarith)
  have h := taylor_mean_remainder_bound (E := ℂ) (n := 1)
    (le_of_lt hlt) hcd hx hC
  rw [taylorWithinEval_powerFun_one p hm x] at h
  norm_num at h ⊢
  exact h

noncomputable def taylorPolyTwo (p : ℂ) (m : ℕ) (x : ℝ) : ℂ :=
  (m : ℂ) ^ p + (x - m) * (p * (m : ℂ) ^ (p - 1)) +
    (x - m) ^ 2 / 2 * (p * (p - 1) * (m : ℂ) ^ (p - 2))

theorem intervalIntegral_taylorPolyTwo (p : ℂ) (m : ℕ) :
    (∫ x : ℝ in (m : ℝ)..m + 1, taylorPolyTwo p m x) =
      (m : ℂ) ^ p + (1 / 2 : ℂ) * (p * (m : ℂ) ^ (p - 1)) +
        (1 / 6 : ℂ) * (p * (p - 1) * (m : ℂ) ^ (p - 2)) := by
  let A : ℂ := (m : ℂ) ^ p
  let B : ℂ := p * (m : ℂ) ^ (p - 1)
  let C : ℂ := p * (p - 1) * (m : ℂ) ^ (p - 2)
  have hlinCast : (∫ x : ℝ in (m : ℝ)..m + 1, ((x - m : ℝ) : ℂ)) =
      (1 / 2 : ℂ) := by
    have hr : (∫ x : ℝ in (m : ℝ)..m + 1, x - m) = (1 / 2 : ℝ) := by
      calc
        (∫ x : ℝ in (m : ℝ)..m + 1, x - m) =
            ∫ x : ℝ in (0 : ℝ)..1, x := by
              simpa only [sub_self, add_sub_cancel_left] using
                (intervalIntegral.integral_comp_sub_right
                (f := fun x : ℝ => x) (a := (m : ℝ)) (b := m + 1) (m : ℝ))
        _ = 1 / 2 := by norm_num [integral_id]
    rw [intervalIntegral.integral_ofReal]
    rw [hr]
    norm_num
  have hsqCast : (∫ x : ℝ in (m : ℝ)..m + 1, (((x - m) ^ 2 : ℝ) : ℂ)) =
      (1 / 3 : ℂ) := by
    have hr : (∫ x : ℝ in (m : ℝ)..m + 1, (x - m) ^ 2) = (1 / 3 : ℝ) := by
      calc
        (∫ x : ℝ in (m : ℝ)..m + 1, (x - m) ^ 2) =
            ∫ x : ℝ in (0 : ℝ)..1, x ^ 2 := by
              simpa only [sub_self, add_sub_cancel_left] using
                (intervalIntegral.integral_comp_sub_right
                (f := fun x : ℝ => x ^ 2) (a := (m : ℝ)) (b := m + 1) (m : ℝ))
        _ = 1 / 3 := by norm_num [integral_pow]
    rw [intervalIntegral.integral_ofReal]
    rw [hr]
    norm_num
  have hlin : (∫ x : ℝ in (m : ℝ)..m + 1, (x : ℂ) - (m : ℂ)) =
      (1 / 2 : ℂ) := by
    simpa only [Complex.ofReal_sub] using hlinCast
  have hsq : (∫ x : ℝ in (m : ℝ)..m + 1, ((x : ℂ) - (m : ℂ)) ^ 2) =
      (1 / 3 : ℂ) := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_pow] using hsqCast
  have hA : IntervalIntegrable (fun _ : ℝ => A) volume (m : ℝ) (m + 1) :=
    intervalIntegrable_const
  have hB : IntervalIntegrable (fun x : ℝ => ((x : ℂ) - (m : ℂ)) * B)
      volume (m : ℝ) (m + 1) := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold taylorPolyTwo
  change (∫ x : ℝ in (m : ℝ)..m + 1,
      A + ((x : ℂ) - (m : ℂ)) * B + ((x : ℂ) - (m : ℂ)) ^ 2 / 2 * C) = _
  rw [intervalIntegral.integral_add (hA.add hB)
      (by apply Continuous.intervalIntegrable; fun_prop : IntervalIntegrable
        (fun x : ℝ => ((x : ℂ) - (m : ℂ)) ^ 2 / 2 * C)
        volume (m : ℝ) (m + 1)),
    intervalIntegral.integral_add hA hB]
  simp only [intervalIntegral.integral_const, add_sub_cancel_left, one_smul,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_div]
  rw [hlin, hsq]
  dsimp [A, B, C]
  push_cast
  ring

noncomputable def taylorRemainderTwo (p : ℂ) (m : ℕ) (x : ℝ) : ℂ :=
  powerFun p x - taylorPolyTwo p m x

noncomputable def derivativeRemainderOne (p : ℂ) (m : ℕ) : ℂ :=
  p * ((m + 1 : ℕ) : ℂ) ^ (p - 1) -
    (p * (m : ℂ) ^ (p - 1) +
      p * (p - 1) * (m : ℂ) ^ (p - 2))

noncomputable def integralEulerIncrement (p : ℂ) (m : ℕ) : ℂ :=
  (1 / 2 : ℂ) *
      (powerFun p m + powerFun p (m + 1)) -
    (∫ x : ℝ in (m : ℝ)..m + 1, powerFun p x) -
    (1 / 12 : ℂ) *
      (p * ((m + 1 : ℕ) : ℂ) ^ (p - 1) -
        p * (m : ℂ) ^ (p - 1))

theorem integralEulerIncrement_eq_remainders (p : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    integralEulerIncrement p m =
      (1 / 2 : ℂ) * taylorRemainderTwo p m (m + 1) -
        (∫ x : ℝ in (m : ℝ)..m + 1, taylorRemainderTwo p m x) -
        (1 / 12 : ℂ) * derivativeRemainderOne p m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsub : uIcc (m : ℝ) (m + 1 : ℝ) ⊆ Ioi (0 : ℝ) := by
    rw [uIcc_of_le (by norm_num : (m : ℝ) ≤ m + 1)]
    intro x hx
    exact lt_of_lt_of_le hmpos hx.1
  have hf : IntervalIntegrable (powerFun p) volume (m : ℝ) (m + 1) :=
    ((contDiffOn_powerFun p 0).continuousOn.mono hsub).intervalIntegrable
  have hP : IntervalIntegrable (taylorPolyTwo p m) volume (m : ℝ) (m + 1) := by
    apply Continuous.intervalIntegrable
    unfold taylorPolyTwo
    fun_prop
  rw [integralEulerIncrement]
  simp only [taylorRemainderTwo]
  rw [intervalIntegral.integral_sub hf hP, intervalIntegral_taylorPolyTwo]
  unfold derivativeRemainderOne taylorPolyTwo powerFun
  push_cast
  ring

noncomputable def cellBound (p : ℂ) (m : ℕ) : ℝ :=
  ‖fallingCoeff p 3‖ * (m : ℝ) ^ (p.re - 3)

theorem cellBound_nonneg (p : ℂ) (m : ℕ) : 0 ≤ cellBound p m := by
  exact mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (by positivity : 0 ≤ (m : ℝ)) _)

theorem taylorRemainderTwo_bound_half {p : ℂ} (hp : p.re < 2)
    {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx : x ∈ Icc (m : ℝ) (m + 1 : ℝ)) :
    ‖taylorRemainderTwo p m x‖ ≤ cellBound p m / 2 := by
  have h := powerFun_taylor_two_bound hp hm hx
  change ‖taylorRemainderTwo p m x‖ ≤ _
  rw [cellBound]
  change ‖powerFun p x - taylorPolyTwo p m x‖ ≤ _
  apply h.trans
  have hxm0 : 0 ≤ x - m := sub_nonneg.mpr hx.1
  have hxm1 : x - m ≤ 1 := by linarith [hx.2]
  have hcube : (x - m) ^ 3 ≤ 1 := by nlinarith [sq_nonneg (x - m)]
  have hC := cellBound_nonneg p m
  rw [cellBound] at hC
  apply div_le_div_of_nonneg_right _ (by norm_num)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hcube hC

theorem derivativeRemainderOne_bound {p : ℂ} (hp : p.re < 2)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖derivativeRemainderOne p m‖ ≤ cellBound p m := by
  have hx : (m + 1 : ℝ) ∈ Icc (m : ℝ) (m + 1 : ℝ) := right_mem_Icc.mpr (by norm_num)
  have hq : (p - 1).re < 1 := by norm_num; linarith
  have h := powerFun_taylor_one_bound (p := p - 1) hq hm hx
  have hexp : (p - 1).re - 2 = p.re - 3 := by norm_num; ring
  rw [hexp] at h
  norm_num at h
  have hfall : fallingCoeff p 3 = p * fallingCoeff (p - 1) 2 := by
    norm_num [fallingCoeff, Finset.prod_range_succ]
    ring
  rw [derivativeRemainderOne, cellBound, hfall, norm_mul]
  have heq :
      p * ((m + 1 : ℕ) : ℂ) ^ (p - 1) -
          (p * (m : ℂ) ^ (p - 1) + p * (p - 1) * (m : ℂ) ^ (p - 2)) =
        p * (powerFun (p - 1) (m + 1) -
          ((m : ℂ) ^ (p - 1) +
            (((m + 1 : ℝ) - m : ℝ) : ℂ) *
              ((p - 1) * (m : ℂ) ^ ((p - 1) - 1)))) := by
    unfold powerFun
    push_cast
    ring
  rw [heq, norm_mul]
  have hres :
      ‖powerFun (p - 1) (m + 1) -
          ((m : ℂ) ^ (p - 1) +
            (((m + 1 : ℝ) - m : ℝ) : ℂ) *
              ((p - 1) * (m : ℂ) ^ ((p - 1) - 1)))‖ ≤
        ‖fallingCoeff (p - 1) 2‖ * (m : ℝ) ^ (p.re - 3) := by
    simpa using h
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hres (norm_nonneg p)

theorem norm_integral_taylorRemainderTwo_le {p : ℂ} (hp : p.re < 2)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖∫ x : ℝ in (m : ℝ)..m + 1, taylorRemainderTwo p m x‖ ≤
      cellBound p m / 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (m : ℝ)) (b := m + 1) (C := cellBound p m / 2)
    (f := taylorRemainderTwo p m) (fun x hx => by
      apply taylorRemainderTwo_bound_half hp hm
      rw [← uIcc_of_le (by norm_num : (m : ℝ) ≤ m + 1)]
      exact uIoc_subset_uIcc hx)
  norm_num at h ⊢
  exact h

theorem integralEulerIncrement_bound {p : ℂ} (hp : p.re < 2)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖integralEulerIncrement p m‖ ≤ cellBound p m := by
  rw [integralEulerIncrement_eq_remainders p hm]
  have h0 : ‖taylorRemainderTwo p m (m + 1)‖ ≤ cellBound p m / 2 :=
    taylorRemainderTwo_bound_half hp hm (right_mem_Icc.mpr (by norm_num))
  have hI := norm_integral_taylorRemainderTwo_le hp hm
  have h1 := derivativeRemainderOne_bound hp hm
  have hC := cellBound_nonneg p m
  calc
    ‖(1 / 2 : ℂ) * taylorRemainderTwo p m (m + 1) -
          (∫ x : ℝ in (m : ℝ)..m + 1, taylorRemainderTwo p m x) -
          (1 / 12 : ℂ) * derivativeRemainderOne p m‖
        ≤ ‖(1 / 2 : ℂ) * taylorRemainderTwo p m (m + 1)‖ +
            ‖∫ x : ℝ in (m : ℝ)..m + 1, taylorRemainderTwo p m x‖ +
            ‖(1 / 12 : ℂ) * derivativeRemainderOne p m‖ := by
              exact (norm_sub_le _ _).trans
                (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ (1 / 2 : ℝ) * (cellBound p m / 2) +
          cellBound p m / 2 + (1 / 12 : ℝ) * cellBound p m := by
            simp only [norm_mul]
            norm_num
            exact add_le_add (add_le_add
              (mul_le_mul_of_nonneg_left h0 (by norm_num)) hI)
              (mul_le_mul_of_nonneg_left h1 (by norm_num))
    _ ≤ cellBound p m := by linarith

noncomputable def complexPowerSumIncrement (p : ℂ) (n : ℕ) : ℂ :=
  let m : ℕ := n + 1
  (m : ℂ) ^ p
    - (((m + 1 : ℕ) : ℂ) ^ (p + 1)) / (p + 1)
    + ((m : ℂ) ^ (p + 1)) / (p + 1)
    + (1 / 2 : ℂ) *
        ((((m + 1 : ℕ) : ℂ) ^ p) - ((m : ℂ) ^ p))
    - (p / 12) *
        ((((m + 1 : ℕ) : ℂ) ^ (p - 1)) - ((m : ℂ) ^ (p - 1)))

theorem complexPowerSumIncrement_eq_integral (p : ℂ) (n : ℕ)
    (hpole : p ≠ -1) :
    complexPowerSumIncrement p n = integralEulerIncrement p (n + 1) := by
  let m : ℕ := n + 1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hzero : (0 : ℝ) ∉ [[(m : ℝ), m + 1]] := by
    rw [uIcc_of_le (by norm_num : (m : ℝ) ≤ m + 1)]
    intro h
    linarith [h.1]
  have hint := integral_cpow (r := p) (a := (m : ℝ)) (b := m + 1)
    (Or.inr ⟨hpole, hzero⟩)
  dsimp [m] at hint
  unfold complexPowerSumIncrement integralEulerIncrement powerFun
  dsimp only [m]
  rw [hint]
  push_cast
  ring

theorem complexPowerSumIncrement_bound {p : ℂ} (hp : p.re < 2)
    (hpole : p ≠ -1) (n : ℕ) :
    ‖complexPowerSumIncrement p n‖ ≤ cellBound p (n + 1) := by
  rw [complexPowerSumIncrement_eq_integral p n hpole]
  exact integralEulerIncrement_bound hp (by omega)

/-! ## Locally uniform summation on a pole-free continuation domain -/

def continuationDomain : Set ℂ :=
  {p : ℂ | p.re < 2 ∧ -1 < p.re + p.im}

theorem isOpen_continuationDomain : IsOpen continuationDomain := by
  exact (isOpen_lt Complex.continuous_re continuous_const).inter
    (isOpen_lt continuous_const
      (Complex.continuous_re.add Complex.continuous_im))

theorem convex_continuationDomain : Convex ℝ continuationDomain := by
  rw [continuationDomain]
  have hlin : IsLinearMap ℝ (fun z : ℂ => z.re + z.im) := IsLinearMap.mk
    (fun x y => by simp only [Complex.add_re, Complex.add_im]; ring)
    (fun c x => by
      simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
      ring)
  exact (convex_halfSpace_re_lt 2).inter (convex_halfSpace_gt hlin (-1))

theorem isPreconnected_continuationDomain : IsPreconnected continuationDomain :=
  convex_continuationDomain.isPreconnected

theorem ne_neg_one_of_mem_continuationDomain {p : ℂ}
    (hp : p ∈ continuationDomain) : p ≠ -1 := by
  intro h
  subst p
  norm_num [continuationDomain] at hp

theorem norm_fallingCoeff_three_le {p : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hp : ‖p‖ ≤ R) :
    ‖fallingCoeff p 3‖ ≤ (R + 2) ^ 3 := by
  have hfall : fallingCoeff p 3 = p * (p - 1) * (p - 2) := by
    norm_num [fallingCoeff, Finset.prod_range_succ]
  have h1 : ‖p - 1‖ ≤ R + 1 := by
    calc
      ‖p - 1‖ ≤ ‖p‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ R + 1 := by norm_num; linarith
  have h2 : ‖p - 2‖ ≤ R + 2 := by
    calc
      ‖p - 2‖ ≤ ‖p‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ R + 2 := by norm_num; linarith
  rw [hfall, norm_mul, norm_mul]
  have hR1 : 0 ≤ R + 1 := by linarith
  have hR2 : 0 ≤ R + 2 := by linarith
  calc
    ‖p‖ * ‖p - 1‖ * ‖p - 2‖ ≤ R * (R + 1) * (R + 2) := by
      gcongr
    _ ≤ (R + 2) ^ 3 := by nlinarith [sq_nonneg R, sq_nonneg (R + 1)]

theorem norm_le_center_add_radius {p p₀ : ℂ} {r : ℝ}
    (hp : p ∈ Metric.ball p₀ r) : ‖p‖ ≤ ‖p₀‖ + r := by
  have hd : ‖p - p₀‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hp
  calc
    ‖p‖ = ‖(p - p₀) + p₀‖ := by ring_nf
    _ ≤ ‖p - p₀‖ + ‖p₀‖ := norm_add_le _ _
    _ ≤ ‖p₀‖ + r := by linarith

theorem re_le_center_add_radius {p p₀ : ℂ} {r : ℝ}
    (hp : p ∈ Metric.ball p₀ r) : p.re ≤ p₀.re + r := by
  have hd : ‖p - p₀‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hp
  have hre := Complex.abs_re_le_norm (p - p₀)
  rw [Complex.sub_re] at hre
  linarith [le_abs_self (p.re - p₀.re)]

theorem cellBound_le_on_ball {p p₀ : ℂ} {r β : ℝ}
    (hr : 0 ≤ r) (hβ : β = p₀.re + r)
    (hpball : p ∈ Metric.ball p₀ r) {m : ℕ} (hm : 1 ≤ m) :
    cellBound p m ≤
      (‖p₀‖ + r + 2) ^ 3 * (m : ℝ) ^ (β - 3) := by
  have hpnorm : ‖p‖ ≤ ‖p₀‖ + r := norm_le_center_add_radius hpball
  have hcoeff := norm_fallingCoeff_three_le
    (R := ‖p₀‖ + r) (by positivity) hpnorm
  have hre : p.re ≤ β := by
    rw [hβ]
    exact re_le_center_add_radius hpball
  have hpow : (m : ℝ) ^ (p.re - 3) ≤ (m : ℝ) ^ (β - 3) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)
  rw [cellBound]
  exact mul_le_mul hcoeff hpow (Real.rpow_nonneg (by positivity) _)
    (by positivity)

theorem differentiableOn_complexPowerSumIncrement (n : ℕ) :
    DifferentiableOn ℂ (fun p => complexPowerSumIncrement p n)
      continuationDomain := by
  intro p hp
  have hden : p + 1 ≠ 0 := by
    intro h
    exact ne_neg_one_of_mem_continuationDomain hp
      (add_eq_zero_iff_eq_neg.mp h)
  have hm : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : n + 1 ≠ 0)
  have hm1 : ((((n + 1) + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : (n + 1) + 1 ≠ 0)
  have hd_m (t : ℂ) : DifferentiableAt ℂ
      (fun z : ℂ => ((n + 1 : ℕ) : ℂ) ^ z) t :=
    differentiableAt_id.const_cpow (Or.inl hm)
  have hd_m1 (t : ℂ) : DifferentiableAt ℂ
      (fun z : ℂ => (((n + 1) + 1 : ℕ) : ℂ) ^ z) t :=
    differentiableAt_id.const_cpow (Or.inl hm1)
  unfold complexPowerSumIncrement
  dsimp only
  have hdadd : DifferentiableAt ℂ (fun z : ℂ => z + 1) p :=
    differentiableAt_id.add_const 1
  have hdsub : DifferentiableAt ℂ (fun z : ℂ => z - 1) p :=
    differentiableAt_id.sub_const 1
  have hdmadd : DifferentiableAt ℂ
      (fun z : ℂ => ((n + 1 : ℕ) : ℂ) ^ (z + 1)) p :=
    hdadd.const_cpow (Or.inl hm)
  have hdm1add : DifferentiableAt ℂ
      (fun z : ℂ => (((n + 1) + 1 : ℕ) : ℂ) ^ (z + 1)) p :=
    hdadd.const_cpow (Or.inl hm1)
  have hdmsub : DifferentiableAt ℂ
      (fun z : ℂ => ((n + 1 : ℕ) : ℂ) ^ (z - 1)) p :=
    hdsub.const_cpow (Or.inl hm)
  have hdm1sub : DifferentiableAt ℂ
      (fun z : ℂ => (((n + 1) + 1 : ℕ) : ℂ) ^ (z - 1)) p :=
    hdsub.const_cpow (Or.inl hm1)
  exact (((hd_m p).sub (hdm1add.div hdadd hden)).add
    (hdmadd.div hdadd hden)).add
      ((differentiableAt_const (1 / 2 : ℂ)).mul
        ((hd_m1 p).sub (hd_m p))) |>.sub
      ((differentiableAt_id.div_const 12).mul
        (hdm1sub.sub hdmsub)) |>.differentiableWithinAt

noncomputable def complexPowerSumConstant (p : ℂ) : ℂ :=
  -1 / (p + 1) + 1 / 2 - p / 12 +
    ∑' n : ℕ, complexPowerSumIncrement p n

theorem differentiableOn_increment_tsum :
    DifferentiableOn ℂ
      (fun p : ℂ => ∑' n : ℕ, complexPowerSumIncrement p n)
      continuationDomain := by
  intro p₀ hp₀
  let r : ℝ := (2 - p₀.re) / 2
  let β : ℝ := p₀.re + r
  let C : ℝ := (‖p₀‖ + r + 2) ^ 3
  have hr : 0 < r := by
    dsimp [r]
    linarith [hp₀.1]
  have hβ2 : β < 2 := by
    dsimp [β, r]
    linarith [hp₀.1]
  have hexp : β - 3 < -1 := by linarith
  have hraw : Summable (fun n : ℕ => (n : ℝ) ^ (β - 3)) :=
    Real.summable_nat_rpow.mpr hexp
  have hshift : Summable
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (β - 3)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hraw
  have hsum : Summable
      (fun n : ℕ => C * ((n + 1 : ℕ) : ℝ) ^ (β - 3)) :=
    hshift.mul_left C
  let U : Set ℂ := continuationDomain ∩ Metric.ball p₀ r
  have hUopen : IsOpen U :=
    isOpen_continuationDomain.inter Metric.isOpen_ball
  have hp₀U : p₀ ∈ U := ⟨hp₀, Metric.mem_ball_self hr⟩
  have hbound : ∀ n (p : ℂ), p ∈ U →
      ‖complexPowerSumIncrement p n‖ ≤
        C * ((n + 1 : ℕ) : ℝ) ^ (β - 3) := by
    intro n p hpU
    calc
      ‖complexPowerSumIncrement p n‖ ≤ cellBound p (n + 1) :=
        complexPowerSumIncrement_bound hpU.1.1
          (ne_neg_one_of_mem_continuationDomain hpU.1) n
      _ ≤ C * ((n + 1 : ℕ) : ℝ) ^ (β - 3) := by
        exact cellBound_le_on_ball hr.le rfl hpU.2 (by omega)
  have hdU : DifferentiableOn ℂ
      (fun p : ℂ => ∑' n : ℕ, complexPowerSumIncrement p n) U :=
    Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun n => (differentiableOn_complexPowerSumIncrement n).mono inter_subset_left)
      hUopen hbound
  exact (hdU p₀ hp₀U).differentiableAt
    (hUopen.mem_nhds hp₀U) |>.differentiableWithinAt

theorem differentiableOn_complexPowerSumConstant :
    DifferentiableOn ℂ complexPowerSumConstant continuationDomain := by
  intro p hp
  have hden : p + 1 ≠ 0 := by
    intro h
    exact ne_neg_one_of_mem_continuationDomain hp
      (add_eq_zero_iff_eq_neg.mp h)
  unfold complexPowerSumConstant
  exact (((differentiableWithinAt_const (c := (-1 : ℂ))).div
      (differentiableWithinAt_id.add_const 1) hden).add
      (differentiableWithinAt_const (c := (1 / 2 : ℂ))) |>.sub
      (differentiableWithinAt_id.div_const 12)).add
      (differentiableOn_increment_tsum p hp)

end ComplexPowerTaylor
