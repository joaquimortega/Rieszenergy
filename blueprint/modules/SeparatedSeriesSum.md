# SeparatedSeriesSum: coefficient-weighted series and its fourth-order bound

This module imports `SeparatedSeriesBounds`. `separatedEvenSeries` is the angular even-mode sum, and `separatedEvenCoefficient` is its binomial coefficient times normalized cosine moment. Under `0<α<2`, the coefficient has absolute value at most one. Where `angularKernelA>0`, `separatedEvenPowerSummand_eq_ratio` factors each mode as `A^(α/2) separatedRatio^m`; summing gives `separatedEvenSeries_eq_ratioSeries`. `latitudeKernel_eq_separatedEvenSeries` records the equality with the physical angular kernel under the local `|B/A|<1` condition.

`separatedSeriesFourthConstant` is the explicit finite constant `32768 + 8388608 + 4194304` times the shifted coefficient series, and `separatedSeriesFourthConstant_pos` proves positivity for nonnegative `q`. `abs_tsum_separatedEvenPowerDSSTTSeriesTerm_le` splits the full fourth-derivative series into modes `0`, `1`, and the `m≥2` tail. The low-mode bounds and the tail majorant from `SeparatedSeriesBounds`, followed by the triangle inequality for a summable `tsum`, give the scale `A^(α/2-4)` uniformly when `separatedRatio≤q<1`. At this stage the series is an explicit derivative series; `SeparatedSeriesDifferentiation` and `SeparatedMixedFourth` identify it with the derivative of an actual function.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.SeparatedSeriesBounds

/-! The separated series and a uniform bound for its formal mixed derivative. -/

namespace BEMOC.Definitive

open Set

/-- The same even series represents the angular kernel on the physical
height square and gives an extension across polar boundaries. -/
noncomputable def separatedEvenSeries (α s t : ℝ) : ℝ :=
  ∑' m : ℕ,
    (Ring.choose (α / 2) (2 * m) * normalizedCosineMoment (2 * m)) *
      separatedEvenPowerSummand α m s t

noncomputable def separatedEvenCoefficient (α : ℝ) (m : ℕ) : ℝ :=
  Ring.choose (α / 2) (2 * m) * normalizedCosineMoment (2 * m)

theorem abs_separatedEvenCoefficient_le_one
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (m : ℕ) :
    |separatedEvenCoefficient α m| ≤ 1 := by
  have hc : |Ring.choose (α / 2) (2 * m)| ≤ 1 :=
    abs_choose_le_one (by linarith) (by linarith) _
  have hm := abs_normalizedCosineMoment_le_one (2 * m)
  unfold separatedEvenCoefficient
  rw [abs_mul]
  nlinarith [abs_nonneg (Ring.choose (α / 2) (2 * m)),
    abs_nonneg (normalizedCosineMoment (2 * m))]

theorem separatedEvenPowerSummand_eq_ratio
    {α s t : ℝ} (hU : 0 < angularKernelA s t) (m : ℕ) :
    separatedEvenPowerSummand α m s t =
      angularKernelA s t ^ (α / 2) * separatedRatio s t ^ m := by
  let U := angularKernelA s t
  have hUne : U ≠ 0 := hU.ne'
  have hr := Real.rpow_sub_natCast hUne (α / 2) (2 * m)
  have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by norm_num
  rw [hcast] at hr
  unfold separatedEvenPowerSummand separatedRatio
  change U ^ (α / 2 - 2 * (m : ℝ)) * (4 : ℝ) ^ m *
      (1 - s ^ 2) ^ m * (1 - t ^ 2) ^ m =
    U ^ (α / 2) * (4 * (1 - s ^ 2) * (1 - t ^ 2) / U ^ 2) ^ m
  rw [hr, div_pow, mul_pow, mul_pow, pow_mul]
  field_simp [pow_ne_zero _ hUne]
  ring

theorem separatedEvenSeries_eq_ratioSeries
    {α s t : ℝ} (hU : 0 < angularKernelA s t) :
    separatedEvenSeries α s t =
      angularKernelA s t ^ (α / 2) *
        ∑' m : ℕ, separatedEvenCoefficient α m * separatedRatio s t ^ m := by
  unfold separatedEvenSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [separatedEvenPowerSummand_eq_ratio hU]
  unfold separatedEvenCoefficient
  ring

theorem latitudeKernel_eq_separatedEvenSeries
    {α s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hU : 0 < angularKernelA s t)
    (hq : |angularKernelB s t / angularKernelA s t| < 1) :
    latitudeKernel α s t = separatedEvenSeries α s t := by
  exact latitudeKernel_eq_separatedEvenPowerSeries hs ht hU hq

/-- The exact constant for the coefficient-weighted formal fourth derivative
series.  Its geometric sum is finite whenever `0 ≤ q < 1`. -/
noncomputable def separatedSeriesFourthConstant (α q : ℝ) : ℝ :=
  32768 + 8388608 +
    4194304 * ∑' r : ℕ,
      evenAngularDerivativeCoefficient α (r + 2) * q ^ r

theorem separatedSeriesFourthConstant_pos
    (α : ℝ) {q : ℝ} (hq0 : 0 ≤ q) :
    0 < separatedSeriesFourthConstant α q := by
  have hterm : ∀ r : ℕ,
      0 ≤ evenAngularDerivativeCoefficient α (r + 2) * q ^ r := by
    intro r
    exact mul_nonneg (evenAngularDerivativeCoefficient_nonneg α _) (pow_nonneg hq0 _)
  have hsum : 0 ≤ ∑' r : ℕ,
      evenAngularDerivativeCoefficient α (r + 2) * q ^ r :=
    tsum_nonneg hterm
  unfold separatedSeriesFourthConstant
  positivity

/-- The full formal fourth-derivative series has the manuscript scale.
The estimate includes the two low modes and is uniform for a fixed ratio
bound `q < 1`. -/
theorem abs_tsum_separatedEvenPowerDSSTTSeriesTerm_le
    {α s t q : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hU : 0 < angularKernelA s t)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hq : separatedRatio s t ≤ q) :
    |∑' m : ℕ, separatedEvenPowerDSSTTSeriesTerm α m s t| ≤
      separatedSeriesFourthConstant α q *
        angularKernelA s t ^ (α / 2 - 4) := by
  let f : ℕ → ℝ := fun m ↦ separatedEvenPowerDSSTTSeriesTerm α m s t
  let Uγ := angularKernelA s t ^ (α / 2 - 4)
  have hsum : Summable f :=
    summable_separatedEvenPowerDSSTTSeriesTerm hα0 hα2 hs ht hU hq0 hq1 hq
  have h0 : |f 0| ≤ 32768 * Uγ := by
    exact abs_separatedEvenPowerDSSTTSeriesTerm_zero_le hα0 hα2 hs ht hU
  have h1 : |f 1| ≤ 8388608 * Uγ := by
    have hchoose : |Ring.choose (α / 2) 2| ≤ 1 :=
      abs_choose_le_one (by linarith) (by linarith) 2
    have h := abs_separatedEvenPowerDSSTTSeriesTerm_one_le hα0 hα2 hs ht hU
    calc
      |f 1| ≤ (8388608 * |Ring.choose (α / 2) 2|) * Uγ := h
      _ ≤ 8388608 * Uγ := by
        have hc : 8388608 * |Ring.choose (α / 2) 2| ≤ (8388608 : ℝ) := by
          nlinarith
        exact mul_le_mul_of_nonneg_right hc (by positivity)
  let v : ℕ → ℝ := fun r ↦
    4194304 * Uγ *
      (evenAngularDerivativeCoefficient α (r + 2) * q ^ r)
  have hvsum : Summable v :=
    (summable_shifted_evenAngularDerivativeCoefficient_mul_pow α hq0 hq1).mul_left _
  have htail : ∀ r : ℕ, |f (r + 2)| ≤ v r := by
    intro r
    have hterm := abs_separatedEvenPowerSummandDSSTT_le
      hα0 hα2 hs ht hU hq (m := r + 2) (by omega)
    rw [show r + 2 - 2 = r by omega] at hterm
    unfold f v separatedEvenPowerDSSTTSeriesTerm
    rw [abs_mul, abs_mul]
    calc
      |Ring.choose (α / 2) (2 * (r + 2))| *
          |normalizedCosineMoment (2 * (r + 2))| *
          |separatedEvenPowerSummandDSSTT α (r + 2) s t| ≤
        |Ring.choose (α / 2) (2 * (r + 2))| *
          |normalizedCosineMoment (2 * (r + 2))| *
          (4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) * Uγ * q ^ r) := by
            gcongr
      _ = 4194304 * Uγ *
          (evenAngularDerivativeCoefficient α (r + 2) * q ^ r) := by
        unfold evenAngularDerivativeCoefficient
        ring
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have htailSum : |∑' r : ℕ, f (r + 2)| ≤ ∑' r : ℕ, v r := by
    have hnorm : Summable (fun r : ℕ ↦ ‖f (r + 2)‖) :=
      (hsum.comp_injective (fun _ _ h ↦ by omega)).norm
    calc
      |∑' r : ℕ, f (r + 2)| ≤ ∑' r : ℕ, |f (r + 2)| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' r : ℕ, v r :=
        hnorm.tsum_le_tsum htail hvsum
  rw [← hsplit]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at *
  calc
    |f 0 + f 1 + ∑' r : ℕ, f (r + 2)| ≤
        |f 0| + |f 1| + |∑' r : ℕ, f (r + 2)| := by
          exact (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ 32768 * Uγ + 8388608 * Uγ + ∑' r : ℕ, v r := by
      gcongr
    _ = separatedSeriesFourthConstant α q * Uγ := by
      unfold separatedSeriesFourthConstant v
      rw [tsum_mul_left]
      ring

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
