import Mathlib

/-!
# Smooth trapezoidal remainders

This module develops the ordinary (smooth) part of the endpoint
Euler--Maclaurin argument used in `BEMOCRieszEnergies.tex`.  No result from
`BEMOCFormalization.lean` is imported.

The principal result below is a corrected composite-trapezoid formula with
an exact Peano-kernel remainder.  For a `C³` function on `[0,1]`, it gives an
`O(w⁻²)` remainder at the (unscaled) sum level after the usual endpoint and
first-derivative corrections.  If the endpoint values vanish and the
endpoint derivatives agree, this is exactly the estimate needed for the
smooth remainder after the two endpoint singularities have been removed.
-/

open scoped BigOperators Interval
open Asymptotics Filter MeasureTheory Set

namespace EulerSmooth

/-- The interior mesh sum `∑_{k=1}^{w-1} g(k/w)`. -/
noncomputable def interiorMeshSum (g : ℝ → ℝ) (w : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (w - 1), g (((k + 1 : ℕ) : ℝ) / (w : ℝ))

/-- The composite trapezoidal sum at mesh size `1/w`, but without the
outer factor `1/w`. -/
noncomputable def trapezoidMeshSum (g : ℝ → ℝ) (w : ℕ) : ℝ :=
  ∑ k ∈ Finset.range w,
    (g ((k : ℝ) / (w : ℝ)) + g (((k + 1 : ℕ) : ℝ) / (w : ℝ))) / 2

/-- The cell-average definition of `trapezoidMeshSum` agrees with the usual
interior sum plus half of each endpoint. -/
theorem trapezoidMeshSum_eq_interior (g : ℝ → ℝ) (w : ℕ) (hw : 0 < w) :
    trapezoidMeshSum g w = interiorMeshSum g w + (g 0 + g 1) / 2 := by
  have hwdec : w - 1 + 1 = w := Nat.sub_add_cancel hw
  have hw0 : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  have hleft :
      (∑ k ∈ Finset.range w, g ((k : ℝ) / (w : ℝ))) =
        g 0 + interiorMeshSum g w := by
    have hs := Finset.sum_range_succ'
      (fun k : ℕ ↦ g ((k : ℝ) / (w : ℝ))) (w - 1)
    rw [hwdec] at hs
    simpa only [Nat.cast_zero, zero_div, interiorMeshSum, add_comm] using hs
  have hright :
      (∑ k ∈ Finset.range w, g (((k + 1 : ℕ) : ℝ) / (w : ℝ))) =
        interiorMeshSum g w + g 1 := by
    have hs := Finset.sum_range_succ
      (fun k : ℕ ↦ g (((k + 1 : ℕ) : ℝ) / (w : ℝ))) (w - 1)
    rw [hwdec] at hs
    simpa only [interiorMeshSum, hwdec, Nat.cast_add, Nat.cast_one,
      div_self hw0] using hs
  unfold trapezoidMeshSum
  rw [← Finset.sum_div, Finset.sum_add_distrib, hleft, hright]
  ring

/-- Quadratic kernel for the one-cell trapezoidal error. -/
noncomputable def trapezoidKernel (a b x : ℝ) : ℝ :=
  (x - a) * (b - x) / 2

/-- Derivative of `trapezoidKernel`. -/
noncomputable def trapezoidKernel' (a b x : ℝ) : ℝ :=
  (a + b) / 2 - x

theorem hasDerivAt_trapezoidKernel (a b x : ℝ) :
    HasDerivAt (trapezoidKernel a b) (trapezoidKernel' a b x) x := by
  unfold trapezoidKernel trapezoidKernel'
  convert (((hasDerivAt_id x).sub_const a).mul
    ((hasDerivAt_const x b).sub (hasDerivAt_id x))).div_const 2 using 1 ;
    (try simp only [id_eq]) ; ring

theorem hasDerivAt_trapezoidKernel' (a b x : ℝ) :
    HasDerivAt (trapezoidKernel' a b) (-1) x := by
  unfold trapezoidKernel'
  convert (hasDerivAt_const x ((a + b) / 2)).sub (hasDerivAt_id x) using 1 ;
    ring

@[simp] theorem trapezoidKernel_left (a b : ℝ) : trapezoidKernel a b a = 0 := by
  simp [trapezoidKernel]

@[simp] theorem trapezoidKernel_right (a b : ℝ) : trapezoidKernel a b b = 0 := by
  simp [trapezoidKernel]

@[simp] theorem trapezoidKernel'_left (a b : ℝ) :
    trapezoidKernel' a b a = (b - a) / 2 := by
  unfold trapezoidKernel'
  ring

@[simp] theorem trapezoidKernel'_right (a b : ℝ) :
    trapezoidKernel' a b b = -(b - a) / 2 := by
  unfold trapezoidKernel'
  ring

/-- The cubic Peano kernel on a single interval `[a,b]`.  It vanishes at
both endpoints, and its derivative is the centered quadratic kernel which
appears after removing the first Euler--Maclaurin correction. -/
noncomputable def peanoKernel (a b x : ℝ) : ℝ :=
  let t := x - a
  let h := b - a
  t ^ 3 / 6 - h * t ^ 2 / 4 + h ^ 2 * t / 12

/-- Derivative of the cubic Peano kernel. -/
noncomputable def peanoKernel' (a b x : ℝ) : ℝ :=
  (x - a) ^ 2 / 2 - (b - a) * (x - a) / 2 + (b - a) ^ 2 / 12

@[simp] theorem peanoKernel_left (a b : ℝ) : peanoKernel a b a = 0 := by
  simp [peanoKernel]

@[simp] theorem peanoKernel_right (a b : ℝ) : peanoKernel a b b = 0 := by
  unfold peanoKernel
  ring

theorem hasDerivAt_peanoKernel (a b x : ℝ) :
    HasDerivAt (peanoKernel a b) (peanoKernel' a b x) x := by
  unfold peanoKernel peanoKernel'
  convert (((hasDerivAt_id x).sub_const a).pow 3).div_const 6 |>.sub
    (((hasDerivAt_const x (b - a)).mul (((hasDerivAt_id x).sub_const a).pow 2)).div_const 4)
    |>.add
      (((hasDerivAt_const x ((b - a) ^ 2)).mul
        ((hasDerivAt_id x).sub_const a)).div_const 12) using 1 ;
    (try simp only [id_eq]) ; ring

/-- A deliberately simple uniform bound for the cubic Peano kernel.  The
constant `1/2` is not optimized; its scale `(b-a)³` is what is needed. -/
theorem abs_peanoKernel_le {a b x : ℝ} (hx : x ∈ Icc a b) :
    |peanoKernel a b x| ≤ (b - a) ^ 3 / 2 := by
  have ht0 : 0 ≤ x - a := sub_nonneg.mpr hx.1
  have hth : x - a ≤ b - a := sub_le_sub_right hx.2 a
  have hh0 : 0 ≤ b - a := sub_nonneg.mpr (hx.1.trans hx.2)
  have ht2 : (x - a) ^ 2 ≤ (b - a) ^ 2 := by nlinarith
  have ht3 : (x - a) ^ 3 ≤ (b - a) ^ 3 := by
    calc
      (x - a) ^ 3 = (x - a) ^ 2 * (x - a) := by ring
      _ ≤ (b - a) ^ 2 * (x - a) := mul_le_mul_of_nonneg_right ht2 ht0
      _ ≤ (b - a) ^ 2 * (b - a) :=
        mul_le_mul_of_nonneg_left hth (sq_nonneg (b - a))
      _ = (b - a) ^ 3 := by ring
  unfold peanoKernel
  calc
    |(x - a) ^ 3 / 6 - (b - a) * (x - a) ^ 2 / 4 +
        (b - a) ^ 2 * (x - a) / 12| ≤
        |(x - a) ^ 3 / 6| + |(b - a) * (x - a) ^ 2 / 4| +
          |(b - a) ^ 2 * (x - a) / 12| := by
            exact (abs_add _ _).trans (add_le_add_right (abs_sub _ _) _)
    _ = (x - a) ^ 3 / 6 + (b - a) * (x - a) ^ 2 / 4 +
          (b - a) ^ 2 * (x - a) / 12 := by
            rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
              abs_of_nonneg (by positivity)]
    _ ≤ (b - a) ^ 3 / 2 := by
          nlinarith [mul_le_mul_of_nonneg_left ht2 hh0,
            mul_le_mul_of_nonneg_left hth (sq_nonneg (b - a))]

/-- A one-cell bound for the Peano remainder. -/
theorem abs_integral_peano_mul_le {g''' : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hM : ∀ x ∈ Icc a b, |g''' x| ≤ M) :
    |∫ x in a..b, peanoKernel a b x * g''' x| ≤ M * (b - a) ^ 4 / 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg (g''' a)).trans (hM a ⟨le_rfl, hab⟩)
  have hbound : ∀ x ∈ Ι a b,
      ‖peanoKernel a b x * g''' x‖ ≤ (b - a) ^ 3 / 2 * M := by
    intro x hx
    have hx' : x ∈ Icc a b := by
      rw [uIoc_of_le hab] at hx
      exact ⟨hx.1.le, hx.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_peanoKernel_le hx') (hM x hx')
      (abs_nonneg _)
      (div_nonneg (pow_nonneg (sub_nonneg.mpr hab) _) (by norm_num))
  calc
    |∫ x in a..b, peanoKernel a b x * g''' x| =
        ‖∫ x in a..b, peanoKernel a b x * g''' x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ((b - a) ^ 3 / 2 * M) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = M * (b - a) ^ 4 / 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      ring

/-- The Peano remainder bounded by the `L¹` norm of the third derivative on
one cell.  Unlike `abs_integral_peano_mul_le`, this permits an unbounded
third derivative. -/
theorem abs_integral_peano_mul_le_integral_abs
    {g''' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hint''' : IntervalIntegrable g''' volume a b) :
    |∫ x in a..b, peanoKernel a b x * g''' x| ≤
      (b - a) ^ 3 / 2 * ∫ x in a..b, |g''' x| := by
  have hPcont : ContinuousOn (peanoKernel a b) (uIcc a b) :=
    (continuous_iff_continuousAt.2 fun x ↦
      (hasDerivAt_peanoKernel a b x).continuousAt).continuousOn
  have hprod : IntervalIntegrable (fun x ↦ peanoKernel a b x * g''' x) volume a b :=
    hint'''.continuousOn_mul hPcont
  have hupper : IntervalIntegrable
      (fun x ↦ ((b - a) ^ 3 / 2) * |g''' x|) volume a b :=
    hint'''.abs.const_mul _
  calc
    |∫ x in a..b, peanoKernel a b x * g''' x| ≤
        ∫ x in a..b, |peanoKernel a b x * g''' x| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ x in a..b, ((b - a) ^ 3 / 2) * |g''' x| := by
      apply intervalIntegral.integral_mono_on hab hprod.abs hupper
      intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_peanoKernel_le hx) (abs_nonneg _)
    _ = (b - a) ^ 3 / 2 * ∫ x in a..b, |g''' x| := by
      rw [intervalIntegral.integral_const_mul]

/-- A derivative specified on the interior of an interval is strongly
measurable almost everywhere on that interval; the omitted endpoint is a
null set. -/
theorem aestronglyMeasurable_restrict_of_hasDerivAt_Ioo
    {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    AEStronglyMeasurable f' (volume.restrict (Ι a b)) := by
  have hderiv : AEStronglyMeasurable (deriv f) (volume.restrict (Ι a b)) :=
    (aestronglyMeasurable_deriv f volume).mono_measure Measure.restrict_le_self
  apply hderiv.congr
  rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc, uIoc_of_le hab]
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ b := by
    simpa only [mem_singleton_iff] using
      (measure_zero_iff_ae_nmem.mp (Real.volume_singleton (a := b)))
  filter_upwards [hne] with x hxb hx
  exact (hf' x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩).deriv

/-- For an a.e. measurable real function, interval integrability is
equivalent to interval integrability of its absolute value. -/
theorem intervalIntegrable_of_abs
    {f : ℝ → ℝ} {a b : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ι a b)))
    (habs : IntervalIntegrable (fun x ↦ |f x|) volume a b) :
    IntervalIntegrable f volume a b := by
  apply (IntervalIntegrable.intervalIntegrable_norm_iff hmeas).mp
  simpa only [Real.norm_eq_abs] using habs

/-- Exact one-cell trapezoidal identity. -/
theorem local_trapezoid_eq_integral_kernel
    {g g' g'' : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ uIcc a b, HasDerivAt g' (g'' x) x)
    (hint' : IntervalIntegrable g' volume a b)
    (hint'' : IntervalIntegrable g'' volume a b) :
    (b - a) / 2 * (g a + g b) - ∫ x in a..b, g x =
      ∫ x in a..b, ((x - a) * (b - x) / 2) * g'' x := by
  have hKint : IntervalIntegrable (trapezoidKernel' a b) volume a b :=
    (continuous_iff_continuousAt.2 fun x ↦
      (hasDerivAt_trapezoidKernel' a b x).continuousAt).intervalIntegrable a b
  have hnegOneInt : IntervalIntegrable (fun _ : ℝ ↦ (-1 : ℝ)) volume a b :=
    (continuous_const : Continuous (fun _ : ℝ ↦ (-1 : ℝ))).intervalIntegrable a b
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ hasDerivAt_trapezoidKernel a b x) hg' hKint hint''
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ hasDerivAt_trapezoidKernel' a b x) hg hnegOneInt hint'
  simp only [trapezoidKernel_left, trapezoidKernel_right, zero_mul, sub_zero] at hfirst
  simp only [trapezoidKernel'_left, trapezoidKernel'_right] at hsecond
  rw [intervalIntegral.integral_const_mul] at hsecond
  change _ = ∫ x in a..b, trapezoidKernel a b x * g'' x
  rw [hfirst, hsecond]
  ring

/-- Exact one-cell Euler--Maclaurin formula through the first derivative
correction, with a cubic Peano-kernel remainder. -/
theorem local_trapezoid_corrected
    {g g' g'' g''' : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ uIcc a b, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x ∈ uIcc a b, HasDerivAt g'' (g''' x) x)
    (hint' : IntervalIntegrable g' volume a b)
    (hint'' : IntervalIntegrable g'' volume a b)
    (hint''' : IntervalIntegrable g''' volume a b) :
    ((b - a) / 2 * (g a + g b) - (∫ x in a..b, g x))
        - (b - a) ^ 2 / 12 * (g' b - g' a) =
      ∫ x in a..b, peanoKernel a b x * g''' x := by
  have hbase := local_trapezoid_eq_integral_kernel hg hg' hint' hint''
  have hftc : (∫ x in a..b, g'' x) = g' b - g' a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hg' hint''
  have hP'int : IntervalIntegrable (peanoKernel' a b) volume a b :=
    (by
      have hc : Continuous (peanoKernel' a b) := by
        unfold peanoKernel'
        fun_prop
      exact hc.intervalIntegrable a b)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ hasDerivAt_peanoKernel a b x) hg'' hP'int hint'''
  simp only [peanoKernel_left, peanoKernel_right, zero_mul, sub_zero] at hparts
  calc
    (b - a) / 2 * (g a + g b) - (∫ x in a..b, g x) -
          (b - a) ^ 2 / 12 * (g' b - g' a) =
        (∫ x in a..b, ((x - a) * (b - x) / 2) * g'' x) -
          (b - a) ^ 2 / 12 * (g' b - g' a) := by rw [hbase]
    _ = (∫ x in a..b, trapezoidKernel a b x * g'' x) -
          (b - a) ^ 2 / 12 * (g' b - g' a) := by rfl
    _ = (∫ x in a..b, trapezoidKernel a b x * g'' x) -
          (b - a) ^ 2 / 12 * (∫ x in a..b, g'' x) := by rw [hftc]
    _ =
        (∫ x in a..b, trapezoidKernel a b x * g'' x) -
          ∫ x in a..b, ((b - a) ^ 2 / 12) * g'' x := by
            rw [intervalIntegral.integral_const_mul]
    _ = ∫ x in a..b,
          trapezoidKernel a b x * g'' x - ((b - a) ^ 2 / 12) * g'' x := by
            rw [intervalIntegral.integral_sub]
            · exact (by
                have hc : Continuous (trapezoidKernel a b) :=
                  continuous_iff_continuousAt.2 fun x ↦
                    (hasDerivAt_trapezoidKernel a b x).continuousAt
                exact hint''.continuousOn_mul hc.continuousOn)
            · exact hint''.const_mul _
    _ = ∫ x in a..b, -(peanoKernel' a b x * g'' x) := by
          apply intervalIntegral.integral_congr
          intro x _
          unfold trapezoidKernel peanoKernel'
          ring
    _ = -(∫ x in a..b, peanoKernel' a b x * g'' x) := by
          rw [intervalIntegral.integral_neg]
    _ = ∫ x in a..b, peanoKernel a b x * g''' x := by
          linarith

/-- Exact one-cell formula allowing the third derivative to fail to exist at
the cell endpoints.  This is the form used for integrable endpoint
singularities. -/
theorem local_trapezoid_corrected_of_integrable
    {g g' g'' g''' : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''cont : ContinuousOn g'' (uIcc a b))
    (hg'' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt g'' (g''' x) x)
    (hint' : IntervalIntegrable g' volume a b)
    (hint'' : IntervalIntegrable g'' volume a b)
    (hint''' : IntervalIntegrable g''' volume a b) :
    ((b - a) / 2 * (g a + g b) - (∫ x in a..b, g x))
        - (b - a) ^ 2 / 12 * (g' b - g' a) =
      ∫ x in a..b, peanoKernel a b x * g''' x := by
  have hbase := local_trapezoid_eq_integral_kernel hg hg' hint' hint''
  have hftc : (∫ x in a..b, g'' x) = g' b - g' a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hg' hint''
  have hPcont : ContinuousOn (peanoKernel a b) (uIcc a b) :=
    (continuous_iff_continuousAt.2 fun x ↦
      (hasDerivAt_peanoKernel a b x).continuousAt).continuousOn
  have hP'int : IntervalIntegrable (peanoKernel' a b) volume a b := by
    have hc : Continuous (peanoKernel' a b) := by
      unfold peanoKernel'
      fun_prop
    exact hc.intervalIntegrable a b
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hPcont hg''cont
    (fun x _ ↦ hasDerivAt_peanoKernel a b x) hg'' hP'int hint'''
  simp only [peanoKernel_left, peanoKernel_right, zero_mul, sub_zero] at hparts
  calc
    (b - a) / 2 * (g a + g b) - (∫ x in a..b, g x) -
          (b - a) ^ 2 / 12 * (g' b - g' a) =
        (∫ x in a..b, ((x - a) * (b - x) / 2) * g'' x) -
          (b - a) ^ 2 / 12 * (g' b - g' a) := by rw [hbase]
    _ = (∫ x in a..b, trapezoidKernel a b x * g'' x) -
          (b - a) ^ 2 / 12 * (g' b - g' a) := by rfl
    _ = (∫ x in a..b, trapezoidKernel a b x * g'' x) -
          (b - a) ^ 2 / 12 * (∫ x in a..b, g'' x) := by rw [hftc]
    _ =
        (∫ x in a..b, trapezoidKernel a b x * g'' x) -
          ∫ x in a..b, ((b - a) ^ 2 / 12) * g'' x := by
            rw [intervalIntegral.integral_const_mul]
    _ = ∫ x in a..b,
          trapezoidKernel a b x * g'' x - ((b - a) ^ 2 / 12) * g'' x := by
            rw [intervalIntegral.integral_sub]
            · exact (by
                have hc : Continuous (trapezoidKernel a b) :=
                  continuous_iff_continuousAt.2 fun x ↦
                    (hasDerivAt_trapezoidKernel a b x).continuousAt
                exact hint''.continuousOn_mul hc.continuousOn)
            · exact hint''.const_mul _
    _ = ∫ x in a..b, -(peanoKernel' a b x * g'' x) := by
          apply intervalIntegral.integral_congr
          intro x _
          unfold trapezoidKernel peanoKernel'
          ring
    _ = -(∫ x in a..b, peanoKernel' a b x * g'' x) := by
          rw [intervalIntegral.integral_neg]
    _ = ∫ x in a..b, peanoKernel a b x * g''' x := by
          linarith

/-! ## Composite formula on the uniform mesh of `[0,1]` -/

/-- Exact corrected composite-trapezoid formula.  The normalization is chosen
so that `trapezoidMeshSum` is the unscaled sum used in applications. -/
theorem composite_trapezoid_corrected
    {g g' g'' g''' : ℝ → ℝ} (w : ℕ) (hw : 0 < w)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x, HasDerivAt g'' (g''' x) x)
    (hcont''' : Continuous g''') :
    (1 / (w : ℝ)) * trapezoidMeshSum g w - (∫ x in (0 : ℝ)..1, g x)
        - (1 / (w : ℝ)) ^ 2 / 12 * (g' 1 - g' 0) =
      ∑ k ∈ Finset.range w,
        ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
          peanoKernel ((k : ℝ) / (w : ℝ))
            (((k + 1 : ℕ) : ℝ) / (w : ℝ)) x * g''' x := by
  have hcont : Continuous g := continuous_iff_continuousAt.2 fun x ↦ (hg x).continuousAt
  have hcont' : Continuous g' := continuous_iff_continuousAt.2 fun x ↦ (hg' x).continuousAt
  have hcont'' : Continuous g'' := continuous_iff_continuousAt.2 fun x ↦ (hg'' x).continuousAt
  have hw0 : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  have hstep (k : ℕ) :
      (((k + 1 : ℕ) : ℝ) / (w : ℝ)) - (k : ℝ) / (w : ℝ) = 1 / (w : ℝ) := by
    field_simp
  have hsum :
      (∑ k ∈ Finset.range w,
        (((((k + 1 : ℕ) : ℝ) / (w : ℝ)) - (k : ℝ) / (w : ℝ)) / 2 *
              (g ((k : ℝ) / (w : ℝ)) +
                g (((k + 1 : ℕ) : ℝ) / (w : ℝ))) -
            (∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)), g x) -
          ((((k + 1 : ℕ) : ℝ) / (w : ℝ)) - (k : ℝ) / (w : ℝ)) ^ 2 / 12 *
            (g' (((k + 1 : ℕ) : ℝ) / (w : ℝ)) - g' ((k : ℝ) / (w : ℝ))))) =
        ∑ k ∈ Finset.range w,
          ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
            peanoKernel ((k : ℝ) / (w : ℝ))
              (((k + 1 : ℕ) : ℝ) / (w : ℝ)) x * g''' x := by
    apply Finset.sum_congr rfl
    intro k _
    apply local_trapezoid_corrected
    · exact fun x _ ↦ hg x
    · exact fun x _ ↦ hg' x
    · exact fun x _ ↦ hg'' x
    · exact hcont'.intervalIntegrable _ _
    · exact hcont''.intervalIntegrable _ _
    · exact hcont'''.intervalIntegrable _ _
  have hsumInt :
      (∑ k ∈ Finset.range w,
        ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)), g x) =
        ∫ x in (0 : ℝ)..1, g x := by
    convert intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ ↦ (k : ℝ) / (w : ℝ))
      (f := g) (μ := volume)
      (fun _ _ ↦ hcont.intervalIntegrable _ _) using 1 ; simp [hw0]
  have htel :
      (∑ k ∈ Finset.range w,
        (g' (((k + 1 : ℕ) : ℝ) / (w : ℝ)) - g' ((k : ℝ) / (w : ℝ)))) =
        g' 1 - g' 0 := by
    convert Finset.sum_range_sub (fun k : ℕ ↦ g' ((k : ℝ) / (w : ℝ))) w using 1 ;
      simp [hw0]
  rw [← hsum]
  simp_rw [hstep]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsumInt]
  unfold trapezoidMeshSum
  rw [← Finset.sum_div]
  rw [← Finset.mul_sum, ← Finset.mul_sum, htel]
  ring

/-- Exact corrected composite-trapezoid formula under an `L¹` hypothesis on
the third derivative.  The derivative of `g''` is required only on `(0,1)`,
so integrable endpoint singularities are allowed. -/
theorem composite_trapezoid_corrected_of_integrable
    {g g' g'' g''' : ℝ → ℝ} (w : ℕ) (hw : 0 < w)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg''cont : ContinuousOn g'' (Icc (0 : ℝ) 1))
    (hg'' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g'' (g''' x) x)
    (hint''' : IntervalIntegrable g''' volume (0 : ℝ) 1) :
    (1 / (w : ℝ)) * trapezoidMeshSum g w - (∫ x in (0 : ℝ)..1, g x)
        - (1 / (w : ℝ)) ^ 2 / 12 * (g' 1 - g' 0) =
      ∑ k ∈ Finset.range w,
        ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
          peanoKernel ((k : ℝ) / (w : ℝ))
            (((k + 1 : ℕ) : ℝ) / (w : ℝ)) x * g''' x := by
  have hcont : Continuous g := continuous_iff_continuousAt.2 fun x ↦ (hg x).continuousAt
  have hcont' : Continuous g' := continuous_iff_continuousAt.2 fun x ↦ (hg' x).continuousAt
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hw0 : (w : ℝ) ≠ 0 := hwR.ne'
  have hstep (k : ℕ) :
      (((k + 1 : ℕ) : ℝ) / (w : ℝ)) - (k : ℝ) / (w : ℝ) = 1 / (w : ℝ) := by
    field_simp
  have hsum :
      (∑ k ∈ Finset.range w,
        (((((k + 1 : ℕ) : ℝ) / (w : ℝ)) - (k : ℝ) / (w : ℝ)) / 2 *
              (g ((k : ℝ) / (w : ℝ)) +
                g (((k + 1 : ℕ) : ℝ) / (w : ℝ))) -
            (∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)), g x) -
          ((((k + 1 : ℕ) : ℝ) / (w : ℝ)) - (k : ℝ) / (w : ℝ)) ^ 2 / 12 *
            (g' (((k + 1 : ℕ) : ℝ) / (w : ℝ)) - g' ((k : ℝ) / (w : ℝ))))) =
        ∑ k ∈ Finset.range w,
          ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
            peanoKernel ((k : ℝ) / (w : ℝ))
              (((k + 1 : ℕ) : ℝ) / (w : ℝ)) x * g''' x := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < w := Finset.mem_range.mp hk
    have hkw : k + 1 ≤ w := Nat.succ_le_iff.mpr hklt
    have ha0 : (0 : ℝ) ≤ (k : ℝ) / (w : ℝ) := by positivity
    have hb1 : (((k + 1 : ℕ) : ℝ) / (w : ℝ)) ≤ 1 := by
      rw [div_le_one hwR]
      exact_mod_cast hkw
    have hab : (k : ℝ) / (w : ℝ) ≤ (((k + 1 : ℕ) : ℝ) / (w : ℝ)) := by
      gcongr
      exact Nat.le_succ k
    have hcell :
        uIcc ((k : ℝ) / (w : ℝ)) (((k + 1 : ℕ) : ℝ) / (w : ℝ)) ⊆
          Icc (0 : ℝ) 1 := by
      rw [uIcc_of_le hab]
      exact Icc_subset_Icc ha0 hb1
    have hcellU :
        uIcc ((k : ℝ) / (w : ℝ)) (((k + 1 : ℕ) : ℝ) / (w : ℝ)) ⊆
          uIcc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using hcell
    apply local_trapezoid_corrected_of_integrable
    · exact fun x _ ↦ hg x
    · exact fun x _ ↦ hg' x
    · exact hg''cont.mono hcell
    · intro x hx
      rw [min_eq_left hab, max_eq_right hab] at hx
      exact hg'' x ⟨ha0.trans_lt hx.1, hx.2.trans_le hb1⟩
    · exact hcont'.intervalIntegrable _ _
    · exact (hg''cont.mono hcell).intervalIntegrable
    · exact hint'''.mono hcellU le_rfl
  have hsumInt :
      (∑ k ∈ Finset.range w,
        ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)), g x) =
        ∫ x in (0 : ℝ)..1, g x := by
    convert intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ ↦ (k : ℝ) / (w : ℝ))
      (f := g) (μ := volume)
      (fun _ _ ↦ hcont.intervalIntegrable _ _) using 1 ; simp [hw0]
  have htel :
      (∑ k ∈ Finset.range w,
        (g' (((k + 1 : ℕ) : ℝ) / (w : ℝ)) - g' ((k : ℝ) / (w : ℝ)))) =
        g' 1 - g' 0 := by
    convert Finset.sum_range_sub (fun k : ℕ ↦ g' ((k : ℝ) / (w : ℝ))) w using 1 ;
      simp [hw0]
  rw [← hsum]
  simp_rw [hstep]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsumInt]
  unfold trapezoidMeshSum
  rw [← Finset.sum_div]
  rw [← Finset.mul_sum, ← Finset.mul_sum, htel]
  ring

/-- `L¹` remainder bound for the normalized composite trapezoid rule.  Its
constant is the integral of `|g'''|`; no pointwise bound is assumed. -/
theorem abs_composite_trapezoid_corrected_le_integral_abs
    {g g' g'' g''' : ℝ → ℝ} (w : ℕ) (hw : 0 < w)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg''cont : ContinuousOn g'' (Icc (0 : ℝ) 1))
    (hg'' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g'' (g''' x) x)
    (hint''' : IntervalIntegrable g''' volume (0 : ℝ) 1) :
    |(1 / (w : ℝ)) * trapezoidMeshSum g w - (∫ x in (0 : ℝ)..1, g x)
        - (1 / (w : ℝ)) ^ 2 / 12 * (g' 1 - g' 0)| ≤
      (1 / (w : ℝ)) ^ 3 / 2 * ∫ x in (0 : ℝ)..1, |g''' x| := by
  rw [composite_trapezoid_corrected_of_integrable
    w hw hg hg' hg''cont hg'' hint''']
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hsubset (k : ℕ) (hk : k < w) :
      uIcc ((k : ℝ) / (w : ℝ)) (((k + 1 : ℕ) : ℝ) / (w : ℝ)) ⊆
        uIcc (0 : ℝ) 1 := by
    have hkw : k + 1 ≤ w := Nat.succ_le_iff.mpr hk
    have ha0 : (0 : ℝ) ≤ (k : ℝ) / (w : ℝ) := by positivity
    have hb1 : (((k + 1 : ℕ) : ℝ) / (w : ℝ)) ≤ 1 := by
      rw [div_le_one hwR]
      exact_mod_cast hkw
    have hab : (k : ℝ) / (w : ℝ) ≤ (((k + 1 : ℕ) : ℝ) / (w : ℝ)) := by
      gcongr
      exact Nat.le_succ k
    rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc ha0 hb1
  have hcellInt (k : ℕ) (hk : k < w) :
      IntervalIntegrable g''' volume
        ((k : ℝ) / (w : ℝ)) (((k + 1 : ℕ) : ℝ) / (w : ℝ)) :=
    hint'''.mono (hsubset k hk) le_rfl
  have hcell (k : ℕ) (hk : k ∈ Finset.range w) :
      |∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
          peanoKernel ((k : ℝ) / (w : ℝ))
            (((k + 1 : ℕ) : ℝ) / (w : ℝ)) x * g''' x| ≤
        (1 / (w : ℝ)) ^ 3 / 2 *
          ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
            |g''' x| := by
    have hklt : k < w := Finset.mem_range.mp hk
    have hab : (k : ℝ) / (w : ℝ) ≤ (((k + 1 : ℕ) : ℝ) / (w : ℝ)) := by
      gcongr
      exact Nat.le_succ k
    calc
      |∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
          peanoKernel ((k : ℝ) / (w : ℝ))
            (((k + 1 : ℕ) : ℝ) / (w : ℝ)) x * g''' x| ≤
          ((((k + 1 : ℕ) : ℝ) / (w : ℝ)) - (k : ℝ) / (w : ℝ)) ^ 3 / 2 *
            ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
              |g''' x| :=
        abs_integral_peano_mul_le_integral_abs hab (hcellInt k hklt)
      _ = (1 / (w : ℝ)) ^ 3 / 2 *
            ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
              |g''' x| := by
        congr 2
        field_simp
  have hsumAbs :
      (∑ k ∈ Finset.range w,
        ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
          |g''' x|) = ∫ x in (0 : ℝ)..1, |g''' x| := by
    convert intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ ↦ (k : ℝ) / (w : ℝ))
      (f := fun x ↦ |g''' x|) (μ := volume)
      (fun k hk ↦ (hcellInt k hk).abs) using 1 ; simp [hwR.ne']
  calc
    |∑ k ∈ Finset.range w,
        ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
          peanoKernel ((k : ℝ) / (w : ℝ))
            (((k + 1 : ℕ) : ℝ) / (w : ℝ)) x * g''' x| ≤
        ∑ k ∈ Finset.range w,
          |∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
            peanoKernel ((k : ℝ) / (w : ℝ))
              (((k + 1 : ℕ) : ℝ) / (w : ℝ)) x * g''' x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range w,
        (1 / (w : ℝ)) ^ 3 / 2 *
          ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
            |g''' x| := Finset.sum_le_sum fun k hk ↦ hcell k hk
    _ = (1 / (w : ℝ)) ^ 3 / 2 *
          ∑ k ∈ Finset.range w,
            ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
              |g''' x| := by rw [Finset.mul_sum]
    _ = (1 / (w : ℝ)) ^ 3 / 2 * ∫ x in (0 : ℝ)..1, |g''' x| := by
      rw [hsumAbs]

/-- Sum-scale `L¹` bound.  In particular the corrected mesh error is bounded
by `C * w⁻²`, where `C = (∫₀¹ |g'''|) / 2`. -/
theorem abs_trapezoidMeshSum_sub_integral_corrected_le_integral_abs
    {g g' g'' g''' : ℝ → ℝ} (w : ℕ) (hw : 0 < w)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg''cont : ContinuousOn g'' (Icc (0 : ℝ) 1))
    (hg'' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g'' (g''' x) x)
    (hint''' : IntervalIntegrable g''' volume (0 : ℝ) 1) :
    |trapezoidMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)
        - (1 / (w : ℝ)) / 12 * (g' 1 - g' 0)| ≤
      (∫ x in (0 : ℝ)..1, |g''' x|) * (1 / (w : ℝ)) ^ 2 / 2 := by
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have h := abs_composite_trapezoid_corrected_le_integral_abs
    w hw hg hg' hg''cont hg'' hint'''
  have hid :
      trapezoidMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)
          - (1 / (w : ℝ)) / 12 * (g' 1 - g' 0) =
        (w : ℝ) *
          ((1 / (w : ℝ)) * trapezoidMeshSum g w - (∫ x in (0 : ℝ)..1, g x)
            - (1 / (w : ℝ)) ^ 2 / 12 * (g' 1 - g' 0)) := by
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos hwR]
  calc
    (w : ℝ) *
        |(1 / (w : ℝ)) * trapezoidMeshSum g w - (∫ x in (0 : ℝ)..1, g x)
          - (1 / (w : ℝ)) ^ 2 / 12 * (g' 1 - g' 0)| ≤
        (w : ℝ) * ((1 / (w : ℝ)) ^ 3 / 2 *
          ∫ x in (0 : ℝ)..1, |g''' x|) :=
      mul_le_mul_of_nonneg_left h hwR.le
    _ = (∫ x in (0 : ℝ)..1, |g''' x|) * (1 / (w : ℝ)) ^ 2 / 2 := by
      field_simp
      ring

/-- Endpoint-vanishing form of the sum-scale `L¹` estimate. -/
theorem abs_interiorMeshSum_sub_integral_le_integral_abs
    {g g' g'' g''' : ℝ → ℝ} (w : ℕ) (hw : 0 < w)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg''cont : ContinuousOn g'' (Icc (0 : ℝ) 1))
    (hg'' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g'' (g''' x) x)
    (hint''' : IntervalIntegrable g''' volume (0 : ℝ) 1)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0) (hg'end : g' 1 = g' 0) :
    |interiorMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)| ≤
      (∫ x in (0 : ℝ)..1, |g''' x|) * (1 / (w : ℝ)) ^ 2 / 2 := by
  have h := abs_trapezoidMeshSum_sub_integral_corrected_le_integral_abs
    w hw hg hg' hg''cont hg'' hint'''
  rw [trapezoidMeshSum_eq_interior g w hw, hg0, hg1, hg'end] at h
  simpa using h

/-- Literal absolute-integrability wrapper for the corrected sum-scale
estimate.  Measurability of `g'''` is recovered from the fact that it is the
derivative of `g''` on `(0,1)`. -/
theorem abs_trapezoidMeshSum_sub_integral_corrected_le_of_abs_integrable
    {g g' g'' g''' : ℝ → ℝ} (w : ℕ) (hw : 0 < w)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg''cont : ContinuousOn g'' (Icc (0 : ℝ) 1))
    (hg'' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g'' (g''' x) x)
    (habs : IntervalIntegrable (fun x ↦ |g''' x|) volume (0 : ℝ) 1) :
    |trapezoidMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)
        - (1 / (w : ℝ)) / 12 * (g' 1 - g' 0)| ≤
      (∫ x in (0 : ℝ)..1, |g''' x|) * (1 / (w : ℝ)) ^ 2 / 2 := by
  have hmeas : AEStronglyMeasurable g''' (volume.restrict (Ι (0 : ℝ) 1)) :=
    aestronglyMeasurable_restrict_of_hasDerivAt_Ioo zero_le_one hg''
  have hint''' : IntervalIntegrable g''' volume (0 : ℝ) 1 :=
    intervalIntegrable_of_abs hmeas habs
  exact abs_trapezoidMeshSum_sub_integral_corrected_le_integral_abs
    w hw hg hg' hg''cont hg'' hint'''

/-- Literal absolute-integrability wrapper for the endpoint-vanishing
interior mesh sum. -/
theorem abs_interiorMeshSum_sub_integral_le_of_abs_integrable
    {g g' g'' g''' : ℝ → ℝ} (w : ℕ) (hw : 0 < w)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg''cont : ContinuousOn g'' (Icc (0 : ℝ) 1))
    (hg'' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g'' (g''' x) x)
    (habs : IntervalIntegrable (fun x ↦ |g''' x|) volume (0 : ℝ) 1)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0) (hg'end : g' 1 = g' 0) :
    |interiorMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)| ≤
      (∫ x in (0 : ℝ)..1, |g''' x|) * (1 / (w : ℝ)) ^ 2 / 2 := by
  have hmeas : AEStronglyMeasurable g''' (volume.restrict (Ι (0 : ℝ) 1)) :=
    aestronglyMeasurable_restrict_of_hasDerivAt_Ioo zero_le_one hg''
  have hint''' : IntervalIntegrable g''' volume (0 : ℝ) 1 :=
    intervalIntegrable_of_abs hmeas habs
  exact abs_interiorMeshSum_sub_integral_le_integral_abs
    w hw hg hg' hg''cont hg'' hint''' hg0 hg1 hg'end

/-- Uniform `O(w⁻³)` remainder for the normalized composite trapezoid rule.
Equivalently, this is `O(w⁻²)` for the unscaled mesh sum. -/
theorem abs_composite_trapezoid_corrected_le
    {g g' g'' g''' : ℝ → ℝ} {M : ℝ} (w : ℕ) (hw : 0 < w)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x, HasDerivAt g'' (g''' x) x)
    (hcont''' : Continuous g''')
    (hM : ∀ x ∈ Icc (0 : ℝ) 1, |g''' x| ≤ M) :
    |(1 / (w : ℝ)) * trapezoidMeshSum g w - (∫ x in (0 : ℝ)..1, g x)
        - (1 / (w : ℝ)) ^ 2 / 12 * (g' 1 - g' 0)| ≤
      M * (1 / (w : ℝ)) ^ 3 / 2 := by
  rw [composite_trapezoid_corrected w hw hg hg' hg'' hcont''']
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hcell (k : ℕ) (hk : k ∈ Finset.range w) :
      |∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
          peanoKernel ((k : ℝ) / (w : ℝ))
            (((k + 1 : ℕ) : ℝ) / (w : ℝ)) x * g''' x| ≤
        M * (1 / (w : ℝ)) ^ 4 / 2 := by
    have hklt : k < w := Finset.mem_range.mp hk
    have hkw : k + 1 ≤ w := Nat.succ_le_iff.mpr hklt
    have ha0 : (0 : ℝ) ≤ (k : ℝ) / (w : ℝ) := by positivity
    have hb1 : (((k + 1 : ℕ) : ℝ) / (w : ℝ)) ≤ 1 := by
      rw [div_le_one hwR]
      exact_mod_cast hkw
    have hab : (k : ℝ) / (w : ℝ) ≤ (((k + 1 : ℕ) : ℝ) / (w : ℝ)) := by
      gcongr
      exact Nat.le_succ k
    calc
      |∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
          peanoKernel ((k : ℝ) / (w : ℝ))
            (((k + 1 : ℕ) : ℝ) / (w : ℝ)) x * g''' x| ≤
          M * ((((k + 1 : ℕ) : ℝ) / (w : ℝ)) - (k : ℝ) / (w : ℝ)) ^ 4 / 2 := by
            apply abs_integral_peano_mul_le hab
            intro x hx
            exact hM x ⟨ha0.trans hx.1, hx.2.trans hb1⟩
      _ = M * (1 / (w : ℝ)) ^ 4 / 2 := by
            congr 2
            field_simp
  calc
    |∑ k ∈ Finset.range w,
        ∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
          peanoKernel ((k : ℝ) / (w : ℝ))
            (((k + 1 : ℕ) : ℝ) / (w : ℝ)) x * g''' x| ≤
        ∑ k ∈ Finset.range w,
          |∫ x in ((k : ℝ) / (w : ℝ))..(((k + 1 : ℕ) : ℝ) / (w : ℝ)),
            peanoKernel ((k : ℝ) / (w : ℝ))
              (((k + 1 : ℕ) : ℝ) / (w : ℝ)) x * g''' x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range w, M * (1 / (w : ℝ)) ^ 4 / 2 := by
      exact Finset.sum_le_sum fun k hk ↦ hcell k hk
    _ = M * (1 / (w : ℝ)) ^ 3 / 2 := by
      rw [Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul]
      field_simp
      ring

/-- Sum-scale version of `abs_composite_trapezoid_corrected_le`. -/
theorem abs_trapezoidMeshSum_sub_integral_corrected_le
    {g g' g'' g''' : ℝ → ℝ} {M : ℝ} (w : ℕ) (hw : 0 < w)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x, HasDerivAt g'' (g''' x) x)
    (hcont''' : Continuous g''')
    (hM : ∀ x ∈ Icc (0 : ℝ) 1, |g''' x| ≤ M) :
    |trapezoidMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)
        - (1 / (w : ℝ)) / 12 * (g' 1 - g' 0)| ≤
      M * (1 / (w : ℝ)) ^ 2 / 2 := by
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have h := abs_composite_trapezoid_corrected_le w hw hg hg' hg'' hcont''' hM
  have hid :
      trapezoidMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)
          - (1 / (w : ℝ)) / 12 * (g' 1 - g' 0) =
        (w : ℝ) *
          ((1 / (w : ℝ)) * trapezoidMeshSum g w - (∫ x in (0 : ℝ)..1, g x)
            - (1 / (w : ℝ)) ^ 2 / 12 * (g' 1 - g' 0)) := by
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos hwR]
  calc
    (w : ℝ) *
        |(1 / (w : ℝ)) * trapezoidMeshSum g w - (∫ x in (0 : ℝ)..1, g x)
          - (1 / (w : ℝ)) ^ 2 / 12 * (g' 1 - g' 0)| ≤
        (w : ℝ) * (M * (1 / (w : ℝ)) ^ 3 / 2) :=
      mul_le_mul_of_nonneg_left h hwR.le
    _ = M * (1 / (w : ℝ)) ^ 2 / 2 := by
      field_simp
      ring

/-- If the endpoint values vanish and the endpoint derivatives agree, the
interior mesh sum has an `O(w⁻²)` error at sum scale. -/
theorem abs_interiorMeshSum_sub_integral_le
    {g g' g'' g''' : ℝ → ℝ} {M : ℝ} (w : ℕ) (hw : 0 < w)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x, HasDerivAt g'' (g''' x) x)
    (hcont''' : Continuous g''')
    (hM : ∀ x ∈ Icc (0 : ℝ) 1, |g''' x| ≤ M)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0) (hg'end : g' 1 = g' 0) :
    |interiorMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)| ≤
      M * (1 / (w : ℝ)) ^ 2 / 2 := by
  have h := abs_trapezoidMeshSum_sub_integral_corrected_le
    w hw hg hg' hg'' hcont''' hM
  rw [trapezoidMeshSum_eq_interior g w hw, hg0, hg1, hg'end] at h
  simpa using h

/-- The elementary comparison `w⁻² = o(w⁻α)` for `α < 2`, stated with
real powers on the right. -/
theorem inv_sq_isLittleO_rpow_neg {α : ℝ} (hα : α < 2) :
    (fun w : ℕ ↦ (1 / (w : ℝ)) ^ 2) =o[atTop]
      (fun w : ℕ ↦ (w : ℝ) ^ (-α)) := by
  have hreal :
      (fun x : ℝ ↦ x ^ (-(2 : ℝ))) =o[atTop]
        (fun x : ℝ ↦ x ^ (-α)) := by
    refine (isLittleO_iff_tendsto' ?_).2 ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx hzero
      exact False.elim ((Real.rpow_pos_of_pos hx _).ne' hzero)
    · refine (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_sub hx]
      congr 1
      ring
  have hnat := hreal.comp_tendsto tendsto_natCast_atTop_atTop
  apply hnat.congr'
  · filter_upwards [eventually_ge_atTop 1] with w hw
    have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hw)
    change (w : ℝ) ^ (-(2 : ℝ)) = (1 / (w : ℝ)) ^ 2
    rw [Real.rpow_neg hwR.le, Real.rpow_two]
    field_simp
  · exact EventuallyEq.rfl

/-- `L¹` version of the smooth Euler--Maclaurin remainder.  It applies when
`g'''` has integrable endpoint singularities and proves the same
`o(w⁻α)` conclusion for every `0 < α < 2`. -/
theorem interiorMeshSum_sub_integral_isLittleO_of_integrable
    {g g' g'' g''' : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg''cont : ContinuousOn g'' (Icc (0 : ℝ) 1))
    (hg'' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g'' (g''' x) x)
    (hint''' : IntervalIntegrable g''' volume (0 : ℝ) 1)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0) (hg'end : g' 1 = g' 0) :
    (fun w : ℕ ↦
      interiorMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)) =o[atTop]
        (fun w : ℕ ↦ (w : ℝ) ^ (-α)) := by
  have _hα0 := hα0
  let C : ℝ := (∫ x in (0 : ℝ)..1, |g''' x|) / 2
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg
      (intervalIntegral.integral_nonneg zero_le_one fun _ _ ↦ abs_nonneg _)
      (by norm_num)
  have hbig :
      (fun w : ℕ ↦
        interiorMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)) =O[atTop]
          (fun w : ℕ ↦ (1 / (w : ℝ)) ^ 2) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop 1] with w hw
    have hwpos : 0 < w := Nat.zero_lt_of_lt hw
    have hb := abs_interiorMeshSum_sub_integral_le_integral_abs
      w hwpos hg hg' hg''cont hg'' hint''' hg0 hg1 hg'end
    simp only [Real.norm_eq_abs]
    calc
      |interiorMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)| ≤
          (∫ x in (0 : ℝ)..1, |g''' x|) * (1 / (w : ℝ)) ^ 2 / 2 := hb
      _ = C * |(1 / (w : ℝ)) ^ 2| := by
        rw [abs_of_nonneg (sq_nonneg _)]
        dsimp [C]
        ring
  exact hbig.trans_isLittleO (inv_sq_isLittleO_rpow_neg hα2)

/-- Final absolute-integrability form needed by endpoint-subtracted circle
profiles with `g'''(x) = O(x^(α-1))` near an endpoint. -/
theorem interiorMeshSum_sub_integral_isLittleO_of_abs_integrable
    {g g' g'' g''' : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg''cont : ContinuousOn g'' (Icc (0 : ℝ) 1))
    (hg'' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g'' (g''' x) x)
    (habs : IntervalIntegrable (fun x ↦ |g''' x|) volume (0 : ℝ) 1)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0) (hg'end : g' 1 = g' 0) :
    (fun w : ℕ ↦
      interiorMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)) =o[atTop]
        (fun w : ℕ ↦ (w : ℝ) ^ (-α)) := by
  have hmeas : AEStronglyMeasurable g''' (volume.restrict (Ι (0 : ℝ) 1)) :=
    aestronglyMeasurable_restrict_of_hasDerivAt_Ioo zero_le_one hg''
  have hint''' : IntervalIntegrable g''' volume (0 : ℝ) 1 :=
    intervalIntegrable_of_abs hmeas habs
  exact interiorMeshSum_sub_integral_isLittleO_of_integrable
    hα0 hα2 hg hg' hg''cont hg'' hint''' hg0 hg1 hg'end

/-- Main smooth-remainder result for the endpoint Euler--Maclaurin argument.
After endpoint values vanish and endpoint derivatives match, the unscaled
interior mesh error is `o(w⁻α)` for every fixed `0 < α < 2`. -/
theorem interiorMeshSum_sub_integral_isLittleO
    {g g' g'' g''' : ℝ → ℝ} {M α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x, HasDerivAt g'' (g''' x) x)
    (hcont''' : Continuous g''')
    (hM : ∀ x ∈ Icc (0 : ℝ) 1, |g''' x| ≤ M)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0) (hg'end : g' 1 = g' 0) :
    (fun w : ℕ ↦
      interiorMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)) =o[atTop]
        (fun w : ℕ ↦ (w : ℝ) ^ (-α)) := by
  have _hα0 := hα0
  have hM0 : 0 ≤ M := (abs_nonneg (g''' 0)).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hbig :
      (fun w : ℕ ↦
        interiorMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)) =O[atTop]
          (fun w : ℕ ↦ (1 / (w : ℝ)) ^ 2) := by
    apply IsBigO.of_bound (M / 2)
    filter_upwards [eventually_ge_atTop 1] with w hw
    have hwpos : 0 < w := Nat.zero_lt_of_lt hw
    have hb := abs_interiorMeshSum_sub_integral_le
      w hwpos hg hg' hg'' hcont''' hM hg0 hg1 hg'end
    simp only [Real.norm_eq_abs]
    calc
      |interiorMeshSum g w - (w : ℝ) * (∫ x in (0 : ℝ)..1, g x)| ≤
          M * (1 / (w : ℝ)) ^ 2 / 2 := hb
      _ = M / 2 * |(1 / (w : ℝ)) ^ 2| := by
        rw [abs_of_nonneg (sq_nonneg _)]
        ring
  exact hbig.trans_isLittleO (inv_sq_isLittleO_rpow_neg hα2)

/-!
The theorem above completes the *smooth remainder* portion of the endpoint
Euler--Maclaurin argument.  To obtain the full coefficient in equation (3.1)
of the manuscript one must still combine it with a separate formalization of
the singular model power sum

`∑ k < w, k ^ α = w ^ (α+1)/(α+1) - w^α/2 + ζ(-α) + O(w^(α-1))`.

Mathlib 4.19 contains integration by parts, Taylor remainders, and complex
Riemann zeta values at negative natural numbers, but no general real-exponent
Euler--Maclaurin or finite power-sum theorem providing this zeta constant.
-/

end EulerSmooth
