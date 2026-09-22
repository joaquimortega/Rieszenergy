import BEMOCFormalization.PowerZeta
import BEMOCFormalization.EulerSmooth
import BEMOCFormalization.ComplexFinitePart
import BEMOCFormalization.ComplexPowerTaylor
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Topology

/-!
# Zeta identification by analytic continuation of corrected power sums

This module identifies the corrected finite-part power-sum constant with
Riemann zeta by a complex Euler--Maclaurin continuation.

The intended complex finite-part series is holomorphic on `re s < 2`, away
from its expected pole at `s = -1`.  On `re s < -1`, all finite-part
corrections vanish and the limit is the ordinary Dirichlet series for
`riemannZeta (-s)`.  The identity theorem then propagates the equality to
the paper's range `0 < s < 2`.
-/

open scoped BigOperators Topology Real Interval
open Filter Set Asymptotics

namespace PowerZetaContinuation

open EulerSmooth

/-- A convex continuation domain which contains every real `s ∈ (-1,2)`,
contains an open subset of `re s < -1`, and avoids the pole `s = -1`.

Using this tilted half-plane avoids proving connectedness of a punctured
half-plane. -/
def continuationDomain : Set ℂ :=
  {s : ℂ | s.re < 2 ∧ -1 < s.re + s.im}

theorem isOpen_continuationDomain : IsOpen continuationDomain := by
  apply IsOpen.inter
  · exact isOpen_lt Complex.continuous_re continuous_const
  · exact isOpen_lt continuous_const
      (Complex.continuous_re.add Complex.continuous_im)

theorem convex_continuationDomain : Convex ℝ continuationDomain := by
  rw [continuationDomain]
  have hlin : IsLinearMap ℝ (fun z : ℂ ↦ z.re + z.im) := IsLinearMap.mk
    (fun x y ↦ by simp only [Complex.add_re, Complex.add_im]; ring)
    (fun c x ↦ by
      simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
      ring)
  exact (convex_halfSpace_re_lt 2).inter (convex_halfSpace_gt hlin (-1))

theorem isPreconnected_continuationDomain :
    IsPreconnected continuationDomain :=
  convex_continuationDomain.isPreconnected

theorem real_mem_continuationDomain {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    (α : ℂ) ∈ continuationDomain := by
  constructor <;> norm_num <;> linarith

private noncomputable def seed : ℂ := (-2 : ℂ) + 2 * Complex.I

private theorem seed_mem : seed ∈ continuationDomain := by
  change ((-2 : ℂ) + 2 * Complex.I).re < 2 ∧
    -1 < ((-2 : ℂ) + 2 * Complex.I).re + ((-2 : ℂ) + 2 * Complex.I).im
  norm_num

private theorem seed_re : seed.re < -1 := by
  change ((-2 : ℂ) + 2 * Complex.I).re < -1
  norm_num

/-- A local-ball M-test criterion tailored to the complex Euler--Maclaurin
increment.  Both `re s` and `‖s‖` may be bounded on the chosen ball; no
uniformity in the unbounded imaginary direction is asserted. -/
theorem differentiableOn_tsum_of_increment_bound
    (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, DifferentiableOn ℂ (F n) continuationDomain)
    (hbound : ∀ s₀ ∈ continuationDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball s₀ r ⊆ continuationDomain ∧
      ∃ β : ℝ, β < 2 ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ n (s : ℂ), s ∈ Metric.ball s₀ r →
          ‖F n s‖ ≤ C * ((n + 1 : ℕ) : ℝ) ^ (β - 3)) :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∑' n : ℕ, F n s)
      continuationDomain := by
  intro s hs
  obtain ⟨r, hr, hball, β, hβ2, C, hC, hFC⟩ := hbound s hs
  have hp : β - 3 < -1 := by linarith
  have hsum0 : Summable (fun n : ℕ ↦ (n : ℝ) ^ (β - 3)) :=
    Real.summable_nat_rpow.mpr hp
  have hsumShift : Summable
      (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ (β - 3))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hsum0
  have hsum : Summable
      (fun n : ℕ ↦ C * (((n + 1 : ℕ) : ℝ) ^ (β - 3))) :=
    hsumShift.mul_left C
  have hopen : IsOpen (Metric.ball s r) := Metric.isOpen_ball
  have hsball : s ∈ Metric.ball s r := Metric.mem_ball_self hr
  have hdiff : DifferentiableOn ℂ (fun z : ℂ ↦ ∑' n : ℕ, F n z)
      (Metric.ball s r) :=
    Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun n ↦ (hF n).mono hball) hopen hFC
  exact (hdiff s hsball).differentiableAt
    (hopen.mem_nhds hsball) |>.differentiableWithinAt

/-- Complex version of the corrected increment, shifted so every base is a
strictly positive natural number. -/
noncomputable def complexPowerSumIncrement (s : ℂ) (n : ℕ) : ℂ :=
  let m : ℕ := n + 1
  (m : ℂ) ^ s
    - (((m + 1 : ℕ) : ℂ) ^ (s + 1)) / (s + 1)
    + ((m : ℂ) ^ (s + 1)) / (s + 1)
    + (1 / 2 : ℂ) *
        ((((m + 1 : ℕ) : ℂ) ^ s) - ((m : ℂ) ^ s))
    - (s / 12) *
        ((((m + 1 : ℕ) : ℂ) ^ (s - 1)) - ((m : ℂ) ^ (s - 1)))

/-- Every explicit complex increment is holomorphic on the tilted domain.
Thus the M-test bound above is the only missing input for holomorphy of its
sum. -/
theorem differentiableOn_complexPowerSumIncrement (n : ℕ) :
    DifferentiableOn ℂ (fun s ↦ complexPowerSumIncrement s n)
      continuationDomain := by
  intro s hs
  have hden : s + 1 ≠ 0 := by
    intro h
    change s.re < 2 ∧ -1 < s.re + s.im at hs
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    norm_num at hr hi
    linarith
  have hm : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : n + 1 ≠ 0)
  have hm1 : ((((n + 1) + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : (n + 1) + 1 ≠ 0)
  have hd_m (t : ℂ) : DifferentiableAt ℂ (fun z : ℂ ↦ ((n + 1 : ℕ) : ℂ) ^ z) t :=
    differentiableAt_id.const_cpow (Or.inl hm)
  have hd_m1 (t : ℂ) : DifferentiableAt ℂ
      (fun z : ℂ ↦ (((n + 1) + 1 : ℕ) : ℂ) ^ z) t :=
    differentiableAt_id.const_cpow (Or.inl hm1)
  unfold complexPowerSumIncrement
  dsimp only
  have hdadd : DifferentiableAt ℂ (fun z : ℂ ↦ z + 1) s :=
    differentiableAt_id.add_const 1
  have hdsub : DifferentiableAt ℂ (fun z : ℂ ↦ z - 1) s :=
    differentiableAt_id.sub_const 1
  have hdmadd : DifferentiableAt ℂ
      (fun z : ℂ ↦ ((n + 1 : ℕ) : ℂ) ^ (z + 1)) s :=
    hdadd.const_cpow (Or.inl hm)
  have hdm1add : DifferentiableAt ℂ
      (fun z : ℂ ↦ (((n + 1) + 1 : ℕ) : ℂ) ^ (z + 1)) s :=
    hdadd.const_cpow (Or.inl hm1)
  have hdmsub : DifferentiableAt ℂ
      (fun z : ℂ ↦ ((n + 1 : ℕ) : ℂ) ^ (z - 1)) s :=
    hdsub.const_cpow (Or.inl hm)
  have hdm1sub : DifferentiableAt ℂ
      (fun z : ℂ ↦ (((n + 1) + 1 : ℕ) : ℂ) ^ (z - 1)) s :=
    hdsub.const_cpow (Or.inl hm1)
  exact (((hd_m s).sub (hdm1add.div hdadd hden)).add
    (hdmadd.div hdadd hden)).add
      ((differentiableAt_const (1 / 2 : ℂ)).mul
        ((hd_m1 s).sub (hd_m s))) |>.sub
      ((differentiableAt_id.div_const 12).mul
        (hdm1sub.sub hdmsub)) |>.differentiableWithinAt

/-- The complex finite-part series suggested by the real definition. -/
noncomputable def complexPowerSumConstant (s : ℂ) : ℂ :=
  -1 / (s + 1) + 1 / 2 - s / 12 +
    ∑' n : ℕ, complexPowerSumIncrement s n

/-- Once the uniform third-order increment estimate is supplied, the
complex finite-part constant is holomorphic on the continuation domain. -/
theorem differentiableOn_complexPowerSumConstant_of_bound
    (hbound : ∀ s₀ ∈ continuationDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball s₀ r ⊆ continuationDomain ∧
      ∃ β : ℝ, β < 2 ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ n (s : ℂ), s ∈ Metric.ball s₀ r →
          ‖complexPowerSumIncrement s n‖ ≤
            C * ((n + 1 : ℕ) : ℝ) ^ (β - 3)) :
    DifferentiableOn ℂ complexPowerSumConstant continuationDomain := by
  have hsum : DifferentiableOn ℂ
      (fun s : ℂ ↦ ∑' n : ℕ, complexPowerSumIncrement s n)
      continuationDomain :=
    differentiableOn_tsum_of_increment_bound
      (fun n s ↦ complexPowerSumIncrement s n)
      differentiableOn_complexPowerSumIncrement hbound
  intro s hs
  have hden : s + 1 ≠ 0 := by
    intro h
    change s.re < 2 ∧ -1 < s.re + s.im at hs
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    norm_num at hr hi
    linarith
  unfold complexPowerSumConstant
  exact (((differentiableWithinAt_const (c := (-1 : ℂ))).div
      (differentiableWithinAt_id.add_const 1) hden).add
      (differentiableWithinAt_const (c := (1 / 2 : ℂ))) |>.sub
      (differentiableWithinAt_id.div_const 12)).add (hsum s hs)

/-- The analytic-continuation step itself.  Once a holomorphic complex
finite-part function `F` has been constructed and identified with the
Dirichlet series on `re s < -1`, this theorem gives the desired value at
every real `0 < α < 2`. -/
theorem eq_riemannZeta_neg_of_analyticContinuation
    (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F continuationDomain)
    (hDirichlet : ∀ s ∈ continuationDomain, s.re < -1 →
      F s = riemannZeta (-s))
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    F (α : ℂ) = riemannZeta (-(α : ℂ)) := by
  have hZ : DifferentiableOn ℂ (fun s : ℂ ↦ riemannZeta (-s))
      continuationDomain := by
    intro s hs
    have hne : -s ≠ 1 := by
      intro h
      change s.re < 2 ∧ -1 < s.re + s.im at hs
      have hr := congrArg Complex.re h
      have hi := congrArg Complex.im h
      norm_num at hr hi
      linarith
    simpa only [Function.comp_apply] using
      ((differentiableAt_riemannZeta hne).comp s
        differentiableAt_id.neg).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F continuationDomain :=
    hF.analyticOnNhd isOpen_continuationDomain
  have hZa : AnalyticOnNhd ℂ (fun s : ℂ ↦ riemannZeta (-s))
      continuationDomain := hZ.analyticOnNhd isOpen_continuationDomain
  have hopenSeed : IsOpen
      (continuationDomain ∩ {s : ℂ | s.re < -1}) :=
    isOpen_continuationDomain.inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hseedOpen : seed ∈ continuationDomain ∩ {s : ℂ | s.re < -1} :=
    ⟨seed_mem, seed_re⟩
  have hevent : ∀ᶠ s in 𝓝 seed,
      F s = riemannZeta (-s) := by
    filter_upwards [hopenSeed.mem_nhds hseedOpen] with s hs
    exact hDirichlet s hs.1 hs.2
  have hfreq : ∃ᶠ s in 𝓝[≠] seed,
      F s = riemannZeta (-s) :=
    (hevent.filter_mono nhdsWithin_le_nhds).frequently
  have heq := hFa.eqOn_of_preconnected_of_frequently_eq hZa
    isPreconnected_continuationDomain seed_mem hfreq
  exact heq (real_mem_continuationDomain hα0 hα2)

/-! ## Complex one-cell Euler--Maclaurin identity -/

noncomputable def trapezoidKernelC (a b x : ℝ) : ℂ :=
  (trapezoidKernel a b x : ℂ)

noncomputable def trapezoidKernelC' (a b x : ℝ) : ℂ :=
  (trapezoidKernel' a b x : ℂ)

noncomputable def peanoKernelC (a b x : ℝ) : ℂ :=
  (peanoKernel a b x : ℂ)

noncomputable def peanoKernelC' (a b x : ℝ) : ℂ :=
  (peanoKernel' a b x : ℂ)

theorem hasDerivAt_trapezoidKernelC (a b x : ℝ) :
    HasDerivAt (trapezoidKernelC a b) (trapezoidKernelC' a b x) x := by
  exact (hasDerivAt_trapezoidKernel a b x).ofReal_comp

theorem hasDerivAt_trapezoidKernelC' (a b x : ℝ) :
    HasDerivAt (trapezoidKernelC' a b) (-1) x := by
  convert (hasDerivAt_trapezoidKernel' a b x).ofReal_comp using 1
  norm_num

theorem hasDerivAt_peanoKernelC (a b x : ℝ) :
    HasDerivAt (peanoKernelC a b) (peanoKernelC' a b x) x := by
  exact (hasDerivAt_peanoKernel a b x).ofReal_comp

@[simp] theorem trapezoidKernelC_left (a b : ℝ) :
    trapezoidKernelC a b a = 0 := by simp [trapezoidKernelC]

@[simp] theorem trapezoidKernelC_right (a b : ℝ) :
    trapezoidKernelC a b b = 0 := by simp [trapezoidKernelC]

@[simp] theorem trapezoidKernelC'_left (a b : ℝ) :
    trapezoidKernelC' a b a = ((b - a) / 2 : ℝ) := by
  simp [trapezoidKernelC']

@[simp] theorem trapezoidKernelC'_right (a b : ℝ) :
    trapezoidKernelC' a b b = -((b - a) / 2 : ℝ) := by
  simp [trapezoidKernelC']
  ring_nf

@[simp] theorem peanoKernelC_left (a b : ℝ) : peanoKernelC a b a = 0 := by
  simp [peanoKernelC]

@[simp] theorem peanoKernelC_right (a b : ℝ) : peanoKernelC a b b = 0 := by
  simp [peanoKernelC]

/-- Complex-valued corrected trapezoid formula on one real interval. -/
theorem local_trapezoid_corrected_complex
    {g g' g'' g''' : ℝ → ℂ} {a b : ℝ}
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ uIcc a b, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x ∈ uIcc a b, HasDerivAt g'' (g''' x) x)
    (hint' : IntervalIntegrable g' MeasureTheory.volume a b)
    (hint'' : IntervalIntegrable g'' MeasureTheory.volume a b)
    (hint''' : IntervalIntegrable g''' MeasureTheory.volume a b) :
    (((b - a : ℝ) : ℂ) / 2 * (g a + g b) - (∫ x in a..b, g x))
        - (((b - a : ℝ) : ℂ) ^ 2 / 12) * (g' b - g' a) =
      ∫ x in a..b, peanoKernelC a b x * g''' x := by
  have hKint : IntervalIntegrable (trapezoidKernelC' a b)
      MeasureTheory.volume a b :=
    (continuous_iff_continuousAt.2 fun x ↦
      (hasDerivAt_trapezoidKernelC' a b x).continuousAt).intervalIntegrable a b
  have hnegOneInt : IntervalIntegrable (fun _ : ℝ ↦ (-1 : ℂ))
      MeasureTheory.volume a b := continuous_const.intervalIntegrable a b
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ hasDerivAt_trapezoidKernelC a b x) hg' hKint hint''
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ hasDerivAt_trapezoidKernelC' a b x) hg hnegOneInt hint'
  simp only [trapezoidKernelC_left, trapezoidKernelC_right, zero_mul, sub_zero] at hfirst
  simp only [trapezoidKernelC'_left, trapezoidKernelC'_right] at hsecond
  rw [intervalIntegral.integral_const_mul] at hsecond
  have hbase :
      ((b - a : ℝ) : ℂ) / 2 * (g a + g b) - (∫ x in a..b, g x) =
        ∫ x in a..b, trapezoidKernelC a b x * g'' x := by
    push_cast at hfirst hsecond ⊢
    rw [hfirst, hsecond]
    ring
  have hftc : (∫ x in a..b, g'' x) = g' b - g' a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hg' hint''
  have hPint : IntervalIntegrable (peanoKernelC' a b)
      MeasureTheory.volume a b := by
    have hc : Continuous (peanoKernelC' a b) := by
      unfold peanoKernelC' peanoKernel'
      fun_prop
    exact hc.intervalIntegrable a b
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ hasDerivAt_peanoKernelC a b x) hg'' hPint hint'''
  simp only [peanoKernelC_left, peanoKernelC_right, zero_mul, sub_zero] at hparts
  calc
    ((b - a : ℝ) : ℂ) / 2 * (g a + g b) - (∫ x in a..b, g x) -
          (((b - a : ℝ) : ℂ) ^ 2 / 12) * (g' b - g' a) =
        (∫ x in a..b, trapezoidKernelC a b x * g'' x) -
          (((b - a : ℝ) : ℂ) ^ 2 / 12) * (g' b - g' a) := by rw [hbase]
    _ = (∫ x in a..b, trapezoidKernelC a b x * g'' x) -
          (((b - a : ℝ) : ℂ) ^ 2 / 12) * (∫ x in a..b, g'' x) := by rw [hftc]
    _ = (∫ x in a..b, trapezoidKernelC a b x * g'' x) -
          ∫ x in a..b, (((b - a : ℝ) : ℂ) ^ 2 / 12) * g'' x := by
            rw [intervalIntegral.integral_const_mul]
    _ = ∫ x in a..b, trapezoidKernelC a b x * g'' x -
          (((b - a : ℝ) : ℂ) ^ 2 / 12) * g'' x := by
            rw [intervalIntegral.integral_sub]
            · exact hint''.continuousOn_mul
                ((continuous_iff_continuousAt.2 fun x ↦
                  (hasDerivAt_trapezoidKernelC a b x).continuousAt).continuousOn)
            · exact hint''.const_mul _
    _ = ∫ x in a..b, -(peanoKernelC' a b x * g'' x) := by
          apply intervalIntegral.integral_congr
          intro x _
          have hc : (((b - a : ℝ) : ℂ) ^ 2 / 12) =
              ((((b - a) ^ 2 / 12 : ℝ)) : ℂ) := by
            push_cast
            rfl
          rw [hc]
          change (trapezoidKernel a b x : ℂ) * g'' x -
              ((((b - a) ^ 2 / 12 : ℝ)) : ℂ) * g'' x =
            -((peanoKernel' a b x : ℂ) * g'' x)
          rw [← sub_mul, ← Complex.ofReal_sub]
          have hr : trapezoidKernel a b x - (b - a) ^ 2 / 12 =
              -peanoKernel' a b x := by
            unfold trapezoidKernel peanoKernel'
            ring
          rw [hr]
          push_cast
          ring
    _ = -(∫ x in a..b, peanoKernelC' a b x * g'' x) := by
          rw [intervalIntegral.integral_neg]
    _ = ∫ x in a..b, peanoKernelC a b x * g''' x := by
          simpa using hparts.symm

/-! ## The Peano representation of `zetaFiniteApprox` increments -/

noncomputable def zetaPower0 (s : ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ (-s)
noncomputable def zetaPower1 (s : ℂ) (x : ℝ) : ℂ :=
  (-s) * (x : ℂ) ^ (-s - 1)
noncomputable def zetaPower2 (s : ℂ) (x : ℝ) : ℂ :=
  (-s) * (-s - 1) * (x : ℂ) ^ (-s - 2)
noncomputable def zetaPower3 (s : ℂ) (x : ℝ) : ℂ :=
  (-s) * (-s - 1) * (-s - 2) * (x : ℂ) ^ (-s - 3)

theorem hasDerivAt_zetaPower0 (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zetaPower0 s) (zetaPower1 s x) x := by
  simpa only [zetaPower0, zetaPower1] using
    (ComplexPowerTaylor.hasDerivAt_powerFun (p := -s) hx)

theorem hasDerivAt_zetaPower1 (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zetaPower1 s) (zetaPower2 s x) x := by
  convert (ComplexPowerTaylor.hasDerivAt_powerFun
    (p := -s - 1) hx).const_mul (-s) using 1 ;
    simp only [zetaPower1, zetaPower2, ComplexPowerTaylor.powerFun] ;
    ring_nf

theorem hasDerivAt_zetaPower2 (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zetaPower2 s) (zetaPower3 s x) x := by
  convert (ComplexPowerTaylor.hasDerivAt_powerFun
    (p := -s - 2) hx).const_mul ((-s) * (-s - 1)) using 1 ;
    simp only [zetaPower2, zetaPower3, ComplexPowerTaylor.powerFun] ;
    ring_nf

theorem continuous_zetaPower3_on_Ici (s : ℂ) :
    ContinuousOn (zetaPower3 s) (Ici (1 : ℝ)) := by
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  exact ((ComplexPowerTaylor.hasDerivAt_powerFun
    (p := -s - 3) hx0).const_mul
      ((-s) * (-s - 1) * (-s - 2))).continuousAt.continuousWithinAt

noncomputable def zetaFiniteIncrement (s : ℂ) (n : ℕ) : ℂ :=
  ComplexFinitePart.zetaFiniteApprox s (n + 2) -
    ComplexFinitePart.zetaFiniteApprox s (n + 1)

/-- A finite-approximation increment is exactly one complex Peano
remainder. -/
theorem zetaFiniteIncrement_eq_peano {s : ℂ} (hs1 : s ≠ 1) (n : ℕ) :
    zetaFiniteIncrement s n =
      ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ),
        peanoKernelC ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ) x *
          zetaPower3 s x := by
  let a : ℝ := ((n + 1 : ℕ) : ℝ)
  let b : ℝ := ((n + 2 : ℕ) : ℝ)
  have hab : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast (by omega : n + 1 ≤ n + 2)
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact_mod_cast (by omega : 1 ≤ n + 1)
  have hpos : ∀ x ∈ uIcc a b, 0 < x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact zero_lt_one.trans_le (ha1.trans hx.1)
  have hc1 : ContinuousOn (zetaPower1 s) (uIcc a b) := fun x hx ↦
    (hasDerivAt_zetaPower1 s (hpos x hx)).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn (zetaPower2 s) (uIcc a b) := fun x hx ↦
    (hasDerivAt_zetaPower2 s (hpos x hx)).continuousAt.continuousWithinAt
  have hc3 : ContinuousOn (zetaPower3 s) (uIcc a b) :=
    (continuous_zetaPower3_on_Ici s).mono (by
      rw [uIcc_of_le hab]
      exact fun x hx ↦ ha1.trans hx.1)
  have hloc := local_trapezoid_corrected_complex
    (g := zetaPower0 s) (g' := zetaPower1 s)
    (g'' := zetaPower2 s) (g''' := zetaPower3 s)
    (a := a) (b := b)
    (fun x hx ↦ hasDerivAt_zetaPower0 s (hpos x hx))
    (fun x hx ↦ hasDerivAt_zetaPower1 s (hpos x hx))
    (fun x hx ↦ hasDerivAt_zetaPower2 s (hpos x hx))
    hc1.intervalIntegrable hc2.intervalIntegrable hc3.intervalIntegrable
  have hsneg : -s ≠ -1 := by
    intro h
    apply hs1
    linear_combination -h
  have hzero : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    intro h
    linarith [ha1, h.1]
  have hint : (∫ x in a..b, zetaPower0 s x) =
      ((b : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
    unfold zetaPower0
    rw [integral_cpow (Or.inr ⟨hsneg, hzero⟩)]
    congr 2 <;> ring_nf
  rw [hint] at hloc
  dsimp [a, b] at hloc ⊢
  rw [zetaFiniteIncrement, ComplexFinitePart.zetaFiniteApprox,
    ComplexFinitePart.zetaFiniteApprox]
  have hsum := Finset.sum_Ico_succ_top (show 1 ≤ n + 1 by omega)
    (fun k : ℕ ↦ (k : ℂ) ^ (-s))
  rw [hsum]
  dsimp [zetaPower0, zetaPower1] at hloc
  convert hloc using 1 ; push_cast ; ring

/-- Uniform increment bound on a parameter set with lower real-part bound
and bounded norm.  This is the quantitative input for the local-ball
M-test on `re s > -2`. -/
theorem norm_zetaFiniteIncrement_le
    {β R : ℝ} (hβ : -2 < β) {s : ℂ} (hs1 : s ≠ 1)
    (hre : β ≤ s.re) (hR : ‖s‖ ≤ R) (n : ℕ) :
    ‖zetaFiniteIncrement s n‖ ≤
      (R * (R + 1) * (R + 2) / 2) *
        ((n + 1 : ℕ) : ℝ) ^ (-β - 3) := by
  rw [zetaFiniteIncrement_eq_peano hs1]
  have hR0 : 0 ≤ R := (norm_nonneg s).trans hR
  have hfac1 : ‖-s - 1‖ ≤ R + 1 := by
    calc
      ‖-s - 1‖ ≤ ‖-s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ + 1 := by simp
      _ ≤ R + 1 := by linarith
  have hfac2 : ‖-s - 2‖ ≤ R + 2 := by
    calc
      ‖-s - 2‖ ≤ ‖-s‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ + 2 := by norm_num
      _ ≤ R + 2 := by linarith
  have hfac : ‖(-s) * (-s - 1) * (-s - 2)‖ ≤
      R * (R + 1) * (R + 2) := by
    rw [norm_mul, norm_mul, norm_neg]
    exact mul_le_mul
      (mul_le_mul hR hfac1 (norm_nonneg _) hR0)
      hfac2 (norm_nonneg _) (mul_nonneg hR0 (by linarith))
  have hmpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hpnonpos : -β - 3 ≤ 0 := by linarith
  have hpoint : ∀ x ∈ Ι (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)),
      ‖peanoKernelC ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ) x *
          zetaPower3 s x‖ ≤
        R * (R + 1) * (R + 2) / 2 *
          ((n + 1 : ℕ) : ℝ) ^ (-β - 3) := by
    intro x hx
    have hab : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n + 1 ≤ n + 2)
    rw [uIoc_of_le hab] at hx
    have hxIcc : x ∈ Icc (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)) :=
      ⟨hx.1.le, hx.2⟩
    have hxpos : 0 < x := hmpos.trans_le hxIcc.1
    have hk : ‖peanoKernelC ((n + 1 : ℕ) : ℝ)
        ((n + 2 : ℕ) : ℝ) x‖ ≤ 1 / 2 := by
      rw [peanoKernelC, Complex.norm_real, Real.norm_eq_abs]
      convert abs_peanoKernel_le hxIcc using 1 ; push_cast ; norm_num
    have hexp : (-s - 3).re ≤ -β - 3 := by
      norm_num
      linarith
    have hpow1 : x ^ (-s - 3).re ≤ x ^ (-β - 3) :=
      Real.rpow_le_rpow_of_exponent_le
        ((show (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast (by omega : 1 ≤ n + 1)).trans
          hxIcc.1) hexp
    have hpow2 : x ^ (-β - 3) ≤
        ((n + 1 : ℕ) : ℝ) ^ (-β - 3) :=
      Real.rpow_le_rpow_of_exponent_nonpos hmpos hxIcc.1 hpnonpos
    have hz3 : ‖zetaPower3 s x‖ ≤
        (R * (R + 1) * (R + 2)) *
          ((n + 1 : ℕ) : ℝ) ^ (-β - 3) := by
      rw [zetaPower3, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      exact mul_le_mul hfac (hpow1.trans hpow2)
        (Real.rpow_nonneg hxpos.le _)
        (mul_nonneg (mul_nonneg hR0 (by linarith)) (by linarith))
    rw [norm_mul]
    calc
      ‖peanoKernelC ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ) x‖ *
          ‖zetaPower3 s x‖ ≤
        (1 / 2) *
          (R * (R + 1) * (R + 2) * ((n + 1 : ℕ) : ℝ) ^ (-β - 3)) := by
            exact mul_le_mul hk hz3 (norm_nonneg _)
              (by positivity)
      _ = R * (R + 1) * (R + 2) / 2 *
          ((n + 1 : ℕ) : ℝ) ^ (-β - 3) := by ring
  calc
    ‖∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ),
        peanoKernelC ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ) x *
          zetaPower3 s x‖ ≤
      (R * (R + 1) * (R + 2) / 2 *
        ((n + 1 : ℕ) : ℝ) ^ (-β - 3)) *
          |((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (R * (R + 1) * (R + 2) / 2) *
        ((n + 1 : ℕ) : ℝ) ^ (-β - 3) := by
      push_cast
      norm_num

/-! ## Holomorphic finite-part family on a zeta continuation domain -/

def zetaContinuationDomain : Set ℂ :=
  {s : ℂ | -2 < s.re ∧ s.re + s.im < 1}

theorem isOpen_zetaContinuationDomain : IsOpen zetaContinuationDomain := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (Complex.continuous_re.add Complex.continuous_im) continuous_const)

theorem convex_zetaContinuationDomain : Convex ℝ zetaContinuationDomain := by
  rw [zetaContinuationDomain]
  have hlin : IsLinearMap ℝ (fun z : ℂ ↦ z.re + z.im) := IsLinearMap.mk
    (fun x y ↦ by simp only [Complex.add_re, Complex.add_im]; ring)
    (fun c x ↦ by
      simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
      ring)
  exact (convex_halfSpace_re_gt (-2)).inter (convex_halfSpace_lt hlin 1)

theorem isPreconnected_zetaContinuationDomain :
    IsPreconnected zetaContinuationDomain :=
  convex_zetaContinuationDomain.isPreconnected

theorem neg_real_mem_zetaContinuationDomain {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    (-((α : ℝ) : ℂ)) ∈ zetaContinuationDomain := by
  rw [zetaContinuationDomain]
  norm_num
  constructor <;> linarith

theorem differentiableOn_zetaFiniteApprox (N : ℕ) (hN : 0 < N) :
    DifferentiableOn ℂ (fun s ↦ ComplexFinitePart.zetaFiniteApprox s N)
      zetaContinuationDomain := by
  intro s hs
  have hden : 1 - s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    change -2 < s.re ∧ s.re + s.im < 1 at hs
    norm_num at hr hi
    linarith
  unfold ComplexFinitePart.zetaFiniteApprox
  apply DifferentiableAt.differentiableWithinAt
  fun_prop (disch := aesop (config := { warnOnNonterminal := false }))

theorem differentiableOn_zetaFiniteIncrement (n : ℕ) :
    DifferentiableOn ℂ (fun s ↦ zetaFiniteIncrement s n)
      zetaContinuationDomain := by
  unfold zetaFiniteIncrement
  exact (differentiableOn_zetaFiniteApprox (n + 2) (by omega)).sub
    (differentiableOn_zetaFiniteApprox (n + 1) (by omega))

noncomputable def zetaFinitePartHolomorphic (s : ℂ) : ℂ :=
  ComplexFinitePart.zetaFiniteApprox s 1 +
    ∑' n : ℕ, zetaFiniteIncrement s n

theorem differentiableOn_zetaFinitePartHolomorphic :
    DifferentiableOn ℂ zetaFinitePartHolomorphic zetaContinuationDomain := by
  have hsum : DifferentiableOn ℂ
      (fun s : ℂ ↦ ∑' n : ℕ, zetaFiniteIncrement s n)
      zetaContinuationDomain := by
    intro s₀ hs₀
    obtain ⟨ε, hε, hεsub⟩ :=
      Metric.isOpen_iff.mp isOpen_zetaContinuationDomain s₀ hs₀
    let δ : ℝ := (s₀.re + 2) / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith [hs₀.1]
    let r : ℝ := min ε δ
    have hr : 0 < r := lt_min hε hδ
    have hrε : r ≤ ε := min_le_left _ _
    have hrδ : r ≤ δ := min_le_right _ _
    have hball : Metric.ball s₀ r ⊆ zetaContinuationDomain :=
      (Metric.ball_subset_ball hrε).trans hεsub
    let β : ℝ := s₀.re - r
    have hβ : -2 < β := by
      dsimp [β, δ] at *
      linarith [hs₀.1]
    let R : ℝ := ‖s₀‖ + r
    have hR0 : 0 ≤ R := by dsimp [R]; positivity
    let C : ℝ := R * (R + 1) * (R + 2) / 2
    have hC0 : 0 ≤ C := by
      dsimp [C]
      positivity
    have hp : -β - 3 < -1 := by linarith
    have hsum0 : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-β - 3)) :=
      Real.summable_nat_rpow.mpr hp
    have hsumShift : Summable
        (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ (-β - 3))) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).2 hsum0
    have hdom : Summable
        (fun n : ℕ ↦ C * (((n + 1 : ℕ) : ℝ) ^ (-β - 3))) :=
      hsumShift.mul_left C
    have hparam : ∀ z ∈ Metric.ball s₀ r, β ≤ z.re ∧ ‖z‖ ≤ R := by
      intro z hz
      have hdist : ‖z - s₀‖ < r := by simpa [dist_eq_norm] using hz
      have hreNorm : |(z - s₀).re| ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
      constructor
      · dsimp [β]
        have hre : z.re = (z - s₀).re + s₀.re := by
          simp only [Complex.sub_re]
          ring
        linarith [neg_abs_le ((z - s₀).re)]
      · dsimp [R]
        calc
          ‖z‖ = ‖(z - s₀) + s₀‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - s₀‖ + ‖s₀‖ := norm_add_le _ _
          _ ≤ ‖s₀‖ + r := by linarith
    have hbound : ∀ n (z : ℂ), z ∈ Metric.ball s₀ r →
        ‖zetaFiniteIncrement z n‖ ≤
          C * ((n + 1 : ℕ) : ℝ) ^ (-β - 3) := by
      intro n z hz
      have hpz := hparam z hz
      have hz1 : z ≠ 1 := by
        intro h
        rw [h] at hz
        have := hball hz
        norm_num [zetaContinuationDomain] at this
      simpa only [C] using norm_zetaFiniteIncrement_le hβ hz1 hpz.1 hpz.2 n
    have hopen : IsOpen (Metric.ball s₀ r) := Metric.isOpen_ball
    have hdiff := Complex.differentiableOn_tsum_of_summable_norm hdom
      (fun n ↦ (differentiableOn_zetaFiniteIncrement n).mono hball)
      hopen hbound
    exact (hdiff s₀ (Metric.mem_ball_self hr)).differentiableAt
      (hopen.mem_nhds (Metric.mem_ball_self hr)) |>.differentiableWithinAt
  unfold zetaFinitePartHolomorphic
  exact (differentiableOn_zetaFiniteApprox 1 (by omega)).add hsum

/-! ## Telescoping the holomorphic increment series -/

theorem summable_zetaFiniteIncrement {s : ℂ}
    (hs : s ∈ zetaContinuationDomain) :
    Summable (fun n : ℕ ↦ zetaFiniteIncrement s n) := by
  let β : ℝ := (s.re - 2) / 2
  have hβ : -2 < β := by
    dsimp [β]
    linarith [hs.1]
  have hβs : β ≤ s.re := by
    dsimp [β]
    linarith [hs.1]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num [zetaContinuationDomain] at hs
  let C : ℝ := ‖s‖ * (‖s‖ + 1) * (‖s‖ + 2) / 2
  have hp : -β - 3 < -1 := by linarith
  have hsum0 : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-β - 3)) :=
    Real.summable_nat_rpow.mpr hp
  have hsumShift : Summable
      (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ (-β - 3))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 hsum0
  have hdom : Summable
      (fun n : ℕ ↦ C * (((n + 1 : ℕ) : ℝ) ^ (-β - 3))) :=
    hsumShift.mul_left C
  exact Summable.of_norm_bounded
    (fun n : ℕ ↦ C * (((n + 1 : ℕ) : ℝ) ^ (-β - 3))) hdom (fun n ↦ by
    simpa only [C] using
      norm_zetaFiniteIncrement_le hβ hs1 hβs le_rfl n)

theorem sum_zetaFiniteIncrement (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, zetaFiniteIncrement s n) =
      ComplexFinitePart.zetaFiniteApprox s (N + 1) -
        ComplexFinitePart.zetaFiniteApprox s 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      unfold zetaFiniteIncrement
      ring

theorem tendsto_zetaFiniteApprox_to_finitePart_shifted {s : ℂ}
    (hs : s ∈ zetaContinuationDomain) :
    Tendsto (fun N : ℕ ↦ ComplexFinitePart.zetaFiniteApprox s (N + 1))
      atTop (𝓝 (zetaFinitePartHolomorphic s)) := by
  have hsum := (summable_zetaFiniteIncrement hs).hasSum.tendsto_sum_nat
  have hconst : Tendsto
      (fun _ : ℕ ↦ ComplexFinitePart.zetaFiniteApprox s 1) atTop
      (𝓝 (ComplexFinitePart.zetaFiniteApprox s 1)) := tendsto_const_nhds
  have hadd := hconst.add hsum
  unfold zetaFinitePartHolomorphic
  convert hadd using 1
  ext N
  rw [sum_zetaFiniteIncrement]
  ring

theorem tendsto_zetaFiniteApprox_to_finitePart {s : ℂ}
    (hs : s ∈ zetaContinuationDomain) :
    Tendsto (ComplexFinitePart.zetaFiniteApprox s) atTop
      (𝓝 (zetaFinitePartHolomorphic s)) := by
  exact (tendsto_add_atTop_iff_nat 1).mp
    (tendsto_zetaFiniteApprox_to_finitePart_shifted hs)

/-! ## Identification on the Dirichlet half-plane -/

theorem tendsto_natCast_cpow_zero {p : ℂ} (hp : p.re < 0) :
    Tendsto (fun N : ℕ ↦ (N : ℂ) ^ p) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hr : Tendsto (fun x : ℝ ↦ x ^ p.re) atTop (𝓝 0) := by
    simpa only [neg_neg] using
      (tendsto_rpow_neg_atTop (show 0 < -p.re by linarith))
  have hrnat := hr.comp tendsto_natCast_atTop_atTop
  exact hrnat.congr' ((eventually_gt_atTop 0).mp
    (Eventually.of_forall fun N hN ↦ by
      simpa only [Function.comp_apply] using
        (Complex.norm_natCast_cpow_of_pos hN p).symm))

theorem tendsto_zetaDirichletPartialSum {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ ↦
      ∑ k ∈ Finset.Ico 1 N, (k : ℂ) ^ (-s)) atTop
      (𝓝 (riemannZeta s)) := by
  let q : ℕ → ℂ := fun n ↦ 1 / ((n + 1 : ℕ) : ℂ) ^ s
  have hq : Summable q := by
    dsimp [q]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2
        (Complex.summable_one_div_nat_cpow.mpr hs)
  have hqsum : HasSum q (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    convert hq.hasSum using 1
    simp only [q, Nat.cast_add, Nat.cast_one]
  have hpowsum : HasSum
      (fun n : ℕ ↦ (((n + 1 : ℕ) : ℂ) ^ (-s)))
      (riemannZeta s) := by
    apply hqsum.congr
    intro n
    simp only [q, Complex.cpow_neg, one_div]
  have hshift : Tendsto (fun N : ℕ ↦
      ∑ k ∈ Finset.Ico 1 (N + 1), (k : ℂ) ^ (-s)) atTop
      (𝓝 (riemannZeta s)) := by
    simpa only [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel,
      Nat.add_comm] using hpowsum.tendsto_sum_nat
  exact (tendsto_add_atTop_iff_nat 1).mp (by
    simpa only [Nat.add_comm] using hshift)

theorem tendsto_zetaFiniteApprox_to_riemannZeta {s : ℂ}
    (hs : 1 < s.re) :
    Tendsto (ComplexFinitePart.zetaFiniteApprox s) atTop
      (𝓝 (riemannZeta s)) := by
  have hmain := tendsto_zetaDirichletPartialSum hs
  have hpow1 : Tendsto (fun N : ℕ ↦ (N : ℂ) ^ (1 - s)) atTop (𝓝 0) :=
    tendsto_natCast_cpow_zero (by norm_num; linarith)
  have hpow2 : Tendsto (fun N : ℕ ↦ (N : ℂ) ^ (-s)) atTop (𝓝 0) :=
    tendsto_natCast_cpow_zero (by norm_num; linarith)
  have hpow3 : Tendsto (fun N : ℕ ↦ (N : ℂ) ^ (-s - 1)) atTop (𝓝 0) :=
    tendsto_natCast_cpow_zero (by norm_num; linarith)
  have hhalf : Tendsto (fun _ : ℕ ↦ (1 / 2 : ℂ)) atTop
      (𝓝 (1 / 2 : ℂ)) := tendsto_const_nhds
  have hs12 : Tendsto (fun _ : ℕ ↦ s / 12) atTop
      (𝓝 (s / 12)) := tendsto_const_nhds
  have hlim := ((hmain.sub (hpow1.div_const (1 - s))).add
    (hhalf.mul hpow2)).add (hs12.mul hpow3)
  simpa only [ComplexFinitePart.zetaFiniteApprox, sub_zero, add_zero,
    mul_zero, zero_div] using hlim

/-! ## Analytic continuation and the project leaf -/

theorem differentiableOn_riemannZeta_zetaContinuationDomain :
    DifferentiableOn ℂ riemannZeta zetaContinuationDomain := by
  intro s hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num [zetaContinuationDomain] at hs
  exact (differentiableAt_riemannZeta hs1).differentiableWithinAt

theorem zetaFinitePartHolomorphic_eq_riemannZeta_of_one_lt_re
    {s : ℂ} (hs : s ∈ zetaContinuationDomain) (hre : 1 < s.re) :
    zetaFinitePartHolomorphic s = riemannZeta s := by
  exact tendsto_nhds_unique
    (tendsto_zetaFiniteApprox_to_finitePart hs)
    (tendsto_zetaFiniteApprox_to_riemannZeta hre)

private noncomputable def zetaSeed : ℂ := (3 / 2 : ℂ) - 2 * Complex.I

private theorem zetaSeed_mem : zetaSeed ∈ zetaContinuationDomain := by
  change -2 < ((3 / 2 : ℂ) - 2 * Complex.I).re ∧
    ((3 / 2 : ℂ) - 2 * Complex.I).re +
      ((3 / 2 : ℂ) - 2 * Complex.I).im < 1
  norm_num

private theorem one_lt_zetaSeed_re : 1 < zetaSeed.re := by
  change 1 < ((3 / 2 : ℂ) - 2 * Complex.I).re
  norm_num

theorem zetaFinitePartHolomorphic_eq_riemannZeta
    {s : ℂ} (hs : s ∈ zetaContinuationDomain) :
    zetaFinitePartHolomorphic s = riemannZeta s := by
  have hFa : AnalyticOnNhd ℂ zetaFinitePartHolomorphic
      zetaContinuationDomain :=
    differentiableOn_zetaFinitePartHolomorphic.analyticOnNhd
      isOpen_zetaContinuationDomain
  have hZa : AnalyticOnNhd ℂ riemannZeta zetaContinuationDomain :=
    differentiableOn_riemannZeta_zetaContinuationDomain.analyticOnNhd
      isOpen_zetaContinuationDomain
  have hopenSeed : IsOpen
      (zetaContinuationDomain ∩ {z : ℂ | 1 < z.re}) :=
    isOpen_zetaContinuationDomain.inter
      (isOpen_lt continuous_const Complex.continuous_re)
  have hseedOpen : zetaSeed ∈
      zetaContinuationDomain ∩ {z : ℂ | 1 < z.re} :=
    ⟨zetaSeed_mem, one_lt_zetaSeed_re⟩
  have hevent : ∀ᶠ z in 𝓝 zetaSeed,
      zetaFinitePartHolomorphic z = riemannZeta z := by
    filter_upwards [hopenSeed.mem_nhds hseedOpen] with z hz
    exact zetaFinitePartHolomorphic_eq_riemannZeta_of_one_lt_re hz.1 hz.2
  have hfreq : ∃ᶠ z in 𝓝[≠] zetaSeed,
      zetaFinitePartHolomorphic z = riemannZeta z :=
    (hevent.filter_mono nhdsWithin_le_nhds).frequently
  have heq := hFa.eqOn_of_preconnected_of_frequently_eq hZa
    isPreconnected_zetaContinuationDomain zetaSeed_mem hfreq
  exact heq hs

/-- The complex Euler--Maclaurin family converges to `ζ(-α)` throughout
the full range required by the paper. -/
theorem tendsto_zetaFiniteApprox_neg_real_to_riemannZeta
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Tendsto (ComplexFinitePart.zetaFiniteApprox (-((α : ℝ) : ℂ)))
      atTop (𝓝 (riemannZeta (-((α : ℝ) : ℂ)))) := by
  have hs := neg_real_mem_zetaContinuationDomain hα0 hα2
  have hlim := tendsto_zetaFiniteApprox_to_finitePart hs
  rw [zetaFinitePartHolomorphic_eq_riemannZeta hs] at hlim
  exact hlim

/-- The finite-part power-sum constant is `ζ(-α)` throughout the range
required by the paper. -/
theorem powerSumConstant_eq_riemannZeta_re {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    EulerPower.powerSumConstant α =
      (riemannZeta (-((α : ℝ) : ℂ))).re := by
  have heq := tendsto_nhds_unique
    (ComplexFinitePart.tendsto_zetaFiniteApprox_neg_real hα0 hα2)
    (tendsto_zetaFiniteApprox_neg_real_to_riemannZeta hα0 hα2)
  exact congrArg Complex.re heq

end PowerZetaContinuation
