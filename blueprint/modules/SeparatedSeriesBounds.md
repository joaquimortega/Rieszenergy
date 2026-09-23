# SeparatedSeriesBounds: uniform majorants for the even-mode derivatives

This module imports `SeparatedSummandDerivatives` and `SeparatedKernel`. `SeparatedSeriesRectangle a b c d L q` packages the exact hypotheses used for normal convergence on a closed physical rectangle: `L>0`, `0≤q<1`, both height intervals inside `[-1,1]`, `L≤angularKernelA`, and `separatedRatio≤q` throughout. The corresponding open interior is where later modules differentiate the sum.

For modes `m≥2`, `unequalDerivativeMonomial_eq_normalized` factors a fourth-order term into `16 A^(β-4) Q^(m-2)` times nonnegative powers of `u/A` and `v/A`. The latter ratios are at most one because `A=(1-s²)+(1-t²)+(s-t)²`. This form retains natural radius exponents and works when a squared radius is zero. The auxiliary bounds control radius derivatives, base derivatives, and four falling factors by a constant times `(m+1)^4`; the central result `abs_separatedEvenPowerSummandDSSTT_le` gives the numerical majorant `4194304 (m+1)^4 A^(α/2-4) q^(m-2)` for the explicit fourth derivative.

`evenAngularDerivativeCoefficient` incorporates the absolute binomial coefficient, cosine moment, and `(m+1)^4`. Its geometric-weighted series is summable for `0≤q<1`, using a square-root substitution into the earlier binomial-series summability theorem. This proves summability of the shifted fourth-derivative tail. Modes `0` and `1` are handled separately by `abs_separatedEvenPowerDSSTTSeriesTerm_zero_le` and `...one_le`; adjoining them proves summability of the full weighted series.

The same endpoint-safe method bounds the undifferentiated term and the three lower derivative stages `DS`, `DSS`, and `DSST`. `separatedLatitudeTailMajorant` replaces the varying base by the rectangle's lower bound `L`, providing one summable majorant for all four derivative stages in `norm_separatedEvenPower_tailStages_le_majorant`. These estimates justify subsequent termwise differentiation. This module bounds explicit summands and proves normal convergence; it does not alone identify the mixed derivative of the summed kernel.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.SeparatedSummandDerivatives
import BEMOCFormalization.SeparatedKernel

/-! Endpoint-safe algebra and coefficient estimates adapted from the prior
formalization's generic unequal-latitude series lemmas. -/

open Set

namespace BEMOC.Definitive

set_option maxHeartbeats 800000

/-- Data for a closed physical rectangle on which the even series converges
normally.  Its open interior is the domain for termwise differentiation. -/
structure SeparatedSeriesRectangle
    (a b c d L q : ℝ) : Prop where
  base_pos : 0 < L
  ratio_nonneg : 0 ≤ q
  ratio_lt_one : q < 1
  left_mem : ∀ s ∈ Icc a b, s ∈ Icc (-1 : ℝ) 1
  right_mem : ∀ t ∈ Icc c d, t ∈ Icc (-1 : ℝ) 1
  base_le : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d,
    L ≤ angularKernelA s t
  ratio_le : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d,
    separatedRatio s t ≤ q

private theorem angularKernelA_eq_radiusSq_add (s t : ℝ) :
    angularKernelA s t = (1 - s ^ 2) + (1 - t ^ 2) + (s - t) ^ 2 := by
  unfold angularKernelA
  ring

noncomputable def unequalDerivativeMonomial
    (β A u v : ℝ) (m a b c : ℕ) : ℝ :=
  A ^ β *
    (((4 : ℕ) ^ m : ℕ) * u ^ (m - b) * v ^ (m - c) /
      A ^ (2 * m + a))

/-- Exact normalization of a differentiated series monomial.  The formula
separates the geometric factor `Q^(m-2)` from two harmless ratios bounded
by one on a separated rectangle. -/
theorem unequalDerivativeMonomial_eq_normalized
    {β A u v : ℝ} {m a b c : ℕ}
    (hA : 0 < A) (hb : b ≤ 2) (hc : c ≤ 2)
    (habc : a + b + c = 4) (hm : 2 ≤ m) :
    unequalDerivativeMonomial β A u v m a b c =
      16 * A ^ (β - 4) *
        (4 * u * v / A ^ 2) ^ (m - 2) *
        (u / A) ^ (2 - b) * (v / A) ^ (2 - c) := by
  have hA0 : A ≠ 0 := hA.ne'
  have hmb : m - b = (m - 2) + (2 - b) := by omega
  have hmc : m - c = (m - 2) + (2 - c) := by omega
  have hexp : 2 * m + a =
      2 * (m - 2) + (2 - b) + (2 - c) + 4 := by omega
  have hrpow : A ^ β = A ^ (β - 4) * (A * A * A * A) := by
    have hpow4 : A ^ (4 : ℝ) = A * A * A * A := by
      exact (Real.rpow_natCast A 4).trans (by ring)
    calc
      A ^ β = A ^ (β - 4) * A ^ (4 : ℝ) := by
        rw [← Real.rpow_add hA]
        congr 1
        ring
      _ = A ^ (β - 4) * (A * A * A * A) := by rw [hpow4]
  have hfour : (((4 : ℕ) ^ m : ℕ) : ℝ) =
      16 * (((4 : ℕ) ^ (m - 2) : ℕ) : ℝ) := by
    rw [show m = (m - 2) + 2 by omega, pow_add]
    push_cast
    ring
  unfold unequalDerivativeMonomial
  rw [hrpow, hmb, hmc, pow_add, pow_add, hexp]
  rw [hfour]
  field_simp
  ring

/-- Core endpoint-safe monomial estimate behind (5.6).  It is valid when
either squared radius vanishes, because no negative power of `u` or `v`
appears before the final (harmless) ratios. -/
theorem unequalDerivativeMonomial_le
    {β A u v : ℝ} {m a b c : ℕ}
    (hA : 0 < A) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (huA : u ≤ A) (hvA : v ≤ A)
    (hb : b ≤ 2) (hc : c ≤ 2) (habc : a + b + c = 4)
    (hm : 2 ≤ m) :
    unequalDerivativeMonomial β A u v m a b c ≤
      16 * A ^ (β - 4) *
        (4 * u * v / A ^ 2) ^ (m - 2) := by
  rw [unequalDerivativeMonomial_eq_normalized hA hb hc habc hm]
  have huRatio : 0 ≤ u / A ∧ u / A ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one hA).2 huA
  have hvRatio : 0 ≤ v / A ∧ v / A ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one hA).2 hvA
  have hub : (u / A) ^ (2 - b) ≤ 1 := by
    exact pow_le_one₀ huRatio.1 huRatio.2
  have hvc : (v / A) ^ (2 - c) ≤ 1 := by
    exact pow_le_one₀ hvRatio.1 hvRatio.2
  have hcoef : 0 ≤
      16 * A ^ (β - 4) * (4 * u * v / A ^ 2) ^ (m - 2) := by
    positivity
  calc
    16 * A ^ (β - 4) * (4 * u * v / A ^ 2) ^ (m - 2) *
          (u / A) ^ (2 - b) * (v / A) ^ (2 - c) ≤
        16 * A ^ (β - 4) * (4 * u * v / A ^ 2) ^ (m - 2) *
          1 * 1 := by
      gcongr
    _ = _ := by ring

noncomputable def evenAngularDerivativeCoefficient
    (α : ℝ) (m : ℕ) : ℝ :=
  |Ring.choose (α / 2) (2 * m)| *
    |normalizedCosineMoment (2 * m)| *
    ((m : ℝ) + 1) ^ (4 : ℕ)

theorem evenAngularDerivativeCoefficient_nonneg
    (α : ℝ) (m : ℕ) :
    0 ≤ evenAngularDerivativeCoefficient α m := by
  unfold evenAngularDerivativeCoefficient
  positivity

/-- The coefficient sequence surviving four height derivatives is normally
summable against every fixed geometric ratio `q<1`. -/
theorem summable_evenAngularDerivativeCoefficient_mul_pow
    (α : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℕ ↦
      evenAngularDerivativeCoefficient α m * q ^ m) := by
  have hsqrt0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsqrt1 : |Real.sqrt q| < 1 := by
    rw [abs_of_nonneg hsqrt0]
    exact (Real.sqrt_lt' zero_lt_one).2 (by simpa using hq1)
  have hbase :=
    (summable_nat_add_one_pow_mul_real_choose_mul_pow
      4 (α / 2) (Real.sqrt q) hsqrt1).norm
  have heven :
      Summable (fun m : ℕ ↦
        ‖(((2 * m : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
          Ring.choose (α / 2) (2 * m) *
          Real.sqrt q ^ (2 * m)‖) :=
    hbase.comp_injective (fun _ _ h ↦ by omega)
  apply heven.of_nonneg_of_le
  · intro m
    exact mul_nonneg
      (evenAngularDerivativeCoefficient_nonneg α m) (pow_nonneg hq0 m)
  · intro m
    have hmoment := abs_normalizedCosineMoment_le_one (2 * m)
    have hweight :
        ((m : ℝ) + 1) ^ (4 : ℕ) ≤
          (((2 * m : ℕ) : ℝ) + 1) ^ (4 : ℕ) := by
      apply pow_le_pow_left₀ (by positivity)
      norm_num
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
    have hsqrtSq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
    have hsqrtPow : Real.sqrt q ^ (2 * m) = q ^ m := by
      rw [pow_mul, hsqrtSq]
    unfold evenAngularDerivativeCoefficient
    rw [← hsqrtPow]
    simp only [norm_mul, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg hsqrt0]
    have hcoeff :
        |Ring.choose (α / 2) (2 * m)| *
              |normalizedCosineMoment (2 * m)| *
              ((m : ℝ) + 1) ^ (4 : ℕ) ≤
            |Ring.choose (α / 2) (2 * m)| *
              (((2 * m : ℕ) : ℝ) + 1) ^ (4 : ℕ) := by
      calc
        |Ring.choose (α / 2) (2 * m)| *
              |normalizedCosineMoment (2 * m)| *
              ((m : ℝ) + 1) ^ (4 : ℕ) ≤
            |Ring.choose (α / 2) (2 * m)| * 1 *
              ((m : ℝ) + 1) ^ (4 : ℕ) := by
          gcongr
        _ ≤
            |Ring.choose (α / 2) (2 * m)| *
              (((2 * m : ℕ) : ℝ) + 1) ^ (4 : ℕ) := by
          simpa using
            mul_le_mul_of_nonneg_left hweight
              (abs_nonneg (Ring.choose (α / 2) (2 * m)))
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hsqrt0 (2 * m))
    have hbaseNonneg : 0 ≤ (((2 * m : ℕ) : ℝ) + 1) := by positivity
    rw [abs_of_nonneg hbaseNonneg]
    simpa [Nat.cast_mul, mul_comm] using hcoeff

/-- The shifted sequence occurring after the first two even modes are
separated is also summable. -/
theorem summable_shifted_evenAngularDerivativeCoefficient_mul_pow
    (α : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun r : ℕ ↦
      evenAngularDerivativeCoefficient α (r + 2) * q ^ r) := by
  by_cases hq : q = 0
  · subst q
    apply summable_of_ne_finset_zero (s := {0})
    intro r hr
    simp only [Finset.mem_singleton] at hr
    simp [hr]
  · have hfull :=
      summable_evenAngularDerivativeCoefficient_mul_pow α hq0 hq1
    have htail :
        Summable (fun r : ℕ ↦
          evenAngularDerivativeCoefficient α (r + 2) * q ^ (r + 2)) :=
      hfull.comp_injective (fun _ _ h ↦ by omega)
    have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq
    have hscaled := htail.mul_left (q ^ 2)⁻¹
    convert hscaled using 1
    funext r
    rw [pow_add]
    field_simp
    ring

/-! ## Uniform bounds for the finite Leibniz formula -/

private theorem angularKernelA_le_four_of_mem
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    angularKernelA s t ≤ 4 := by
  unfold angularKernelA
  have habs : |s| * |t| ≤ 1 := by
    calc
      |s| * |t| ≤ 1 * 1 := by
        exact mul_le_mul (abs_le.mpr hs) (abs_le.mpr ht)
          (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hst : -1 ≤ s * t := by
    calc
      -1 ≤ -(|s| * |t|) := by linarith
      _ = -|s * t| := by rw [abs_mul]
      _ ≤ s * t := neg_abs_le _
  linarith

private theorem abs_height_le_one_of_mem
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    |s| ≤ 1 :=
  abs_le.mpr hs

/-- For `0 < α < 2`, every one of the four falling factors generated by
four differentiations is bounded by a fixed multiple of `m+1`. -/
theorem abs_latitude_even_exponent_sub_le
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (m r : ℕ) (hr : r ≤ 3) :
    |α / 2 - 2 * (m : ℝ) - r| ≤
      5 * ((m : ℝ) + 1) := by
  rw [abs_le]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hr3 : (r : ℝ) ≤ 3 := by exact_mod_cast hr
  constructor
  · have hm0 : (0 : ℝ) ≤ m := by positivity
    nlinarith
  ·
    nlinarith

/-- Product form of the preceding estimate.  This is intentionally
generous; the constant is kept numerical so the final normal majorant has
no hidden dependence on the mode. -/
theorem abs_latitude_even_falling_four_le
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (m : ℕ) :
    |(α / 2 - 2 * (m : ℝ)) *
        (α / 2 - 2 * (m : ℝ) - 1) *
        (α / 2 - 2 * (m : ℝ) - 2) *
        (α / 2 - 2 * (m : ℝ) - 3)| ≤
      625 * ((m : ℝ) + 1) ^ (4 : ℕ) := by
  rw [abs_mul, abs_mul, abs_mul]
  have h0 := abs_latitude_even_exponent_sub_le hα0 hα2 m 0 (by omega)
  have h1 := abs_latitude_even_exponent_sub_le hα0 hα2 m 1 (by omega)
  have h2 := abs_latitude_even_exponent_sub_le hα0 hα2 m 2 (by omega)
  have h3 := abs_latitude_even_exponent_sub_le hα0 hα2 m 3 (by omega)
  norm_num at h0
  norm_num at h1 h2 h3
  calc
    |α / 2 - 2 * (m : ℝ)| *
          |α / 2 - 2 * (m : ℝ) - 1| *
          |α / 2 - 2 * (m : ℝ) - 2| *
          |α / 2 - 2 * (m : ℝ) - 3| ≤
        (5 * ((m : ℝ) + 1)) *
          (5 * ((m : ℝ) + 1)) *
          (5 * ((m : ℝ) + 1)) *
          (5 * ((m : ℝ) + 1)) := by gcongr
    _ = 625 * ((m : ℝ) + 1) ^ (4 : ℕ) := by ring

private theorem latitude_common_factor_eq
    {α A u v : ℝ} (hA : 0 < A) (m : ℕ) (hm : 2 ≤ m) :
    (4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) *
        A ^ (α / 2 - 2 * (m : ℝ)) =
      16 * A ^ (α / 2 - 4) *
        (4 * u * v / A ^ 2) ^ (m - 2) := by
  have h := unequalDerivativeMonomial_eq_normalized
    (β := α / 2) (A := A) (u := u) (v := v)
    (m := m) (a := 0) (b := 2) (c := 2)
    hA (by omega) (by omega) (by omega) hm
  unfold unequalDerivativeMonomial at h
  have hr := Real.rpow_sub_natCast hA.ne' (α / 2) (2 * m)
  have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by norm_num
  rw [hcast] at hr
  simp only [Nat.add_zero, Nat.sub_self, pow_zero, mul_one] at h
  rw [← h]
  rw [hr]
  field_simp [pow_ne_zero _ hA.ne']
  ring

private theorem abs_unequalRadiusPower_le
    {A s : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hs : s ∈ Icc (-1 : ℝ) 1)
    (huA : 1 - s ^ 2 ≤ A) :
    |unequalRadiusPower m s| ≤
      A ^ 2 * (1 - s ^ 2) ^ (m - 2) := by
  have hu0 : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hA0 : 0 ≤ A := hu0.trans huA
  unfold unequalRadiusPower
  rw [abs_of_nonneg (pow_nonneg hu0 m)]
  rw [show m = (m - 2) + 2 by omega, pow_add]
  calc
    (1 - s ^ 2) ^ (m - 2) * (1 - s ^ 2) ^ 2 ≤
        (1 - s ^ 2) ^ (m - 2) * A ^ 2 := by
      gcongr
    _ = A ^ 2 * (1 - s ^ 2) ^ (m - 2) := by ring

private theorem abs_unequalRadiusPowerD1_le
    {A s : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hs : s ∈ Icc (-1 : ℝ) 1)
    (huA : 1 - s ^ 2 ≤ A) :
    |unequalRadiusPowerD1 m s| ≤
      2 * ((m : ℝ) + 1) * A * (1 - s ^ 2) ^ (m - 2) := by
  have hu0 : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hA0 : 0 ≤ A := hu0.trans huA
  have hsabs := abs_height_le_one_of_mem hs
  have hmcast : (0 : ℝ) ≤ m := by positivity
  have hmle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hpow :
      (1 - s ^ 2) ^ (m - 1) =
        (1 - s ^ 2) ^ (m - 2) * (1 - s ^ 2) := by
    rw [show m - 1 = (m - 2) + 1 by omega, pow_add, pow_one]
  unfold unequalRadiusPowerD1
  simp only [abs_mul, abs_of_nonneg hmcast, abs_pow,
    abs_of_nonneg hu0, abs_neg]
  norm_num
  rw [hpow]
  calc
    (m : ℝ) *
          ((1 - s ^ 2) ^ (m - 2) * (1 - s ^ 2)) *
          (2 * |s|) ≤
        ((m : ℝ) + 1) *
          ((1 - s ^ 2) ^ (m - 2) * A) * (2 * 1) := by
      gcongr
    _ = 2 * ((m : ℝ) + 1) * A *
          (1 - s ^ 2) ^ (m - 2) := by ring

private theorem abs_unequalRadiusPowerD2_le
    {A s : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hs : s ∈ Icc (-1 : ℝ) 1)
    (huA : 1 - s ^ 2 ≤ A) (hA4 : A ≤ 4) :
    |unequalRadiusPowerD2 m s| ≤
      16 * ((m : ℝ) + 1) ^ 2 *
        (1 - s ^ 2) ^ (m - 2) := by
  have hu0 : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hA0 : 0 ≤ A := hu0.trans huA
  have hsabs := abs_height_le_one_of_mem hs
  have hmcast : (0 : ℝ) ≤ m := by positivity
  have hm1 :
      |(m : ℝ) - 1| ≤ (m : ℝ) + 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hmle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hssq : (2 * |s|) ^ 2 ≤ 4 := by
    nlinarith [abs_nonneg s, sq_nonneg (|s| - 1)]
  have hu4 : 1 - s ^ 2 ≤ 4 := huA.trans hA4
  have hpow :
      (1 - s ^ 2) ^ (m - 1) =
        (1 - s ^ 2) ^ (m - 2) * (1 - s ^ 2) := by
    rw [show m - 1 = (m - 2) + 1 by omega, pow_add, pow_one]
  unfold unequalRadiusPowerD2
  calc
    |_ + _| ≤
        |(m : ℝ) * ((m : ℝ) - 1) *
            (1 - s ^ 2) ^ (m - 2) * (-2 * s) ^ 2| +
          |(m : ℝ) * (1 - s ^ 2) ^ (m - 1) * (-2)| :=
      abs_add _ _
    _ ≤
        ((m : ℝ) + 1) * ((m : ℝ) + 1) *
            (1 - s ^ 2) ^ (m - 2) * (2 * 1) ^ 2 +
          ((m : ℝ) + 1) *
            ((1 - s ^ 2) ^ (m - 2) * 4) * 2 := by
      simp only [abs_mul, abs_pow, abs_neg,
        abs_of_nonneg hmcast, abs_of_nonneg hu0]
      norm_num
      rw [hpow]
      gcongr
    _ ≤ 16 * ((m : ℝ) + 1) ^ 2 *
          (1 - s ^ 2) ^ (m - 2) := by
      have hw : 1 ≤ (m : ℝ) + 1 := by
        have : (0 : ℝ) ≤ m := by positivity
        linarith
      have hcoef :
          4 * ((m : ℝ) + 1) ^ 2 + 8 * ((m : ℝ) + 1) ≤
            16 * ((m : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg ((m : ℝ) + 1)]
      have hupow : 0 ≤ (1 - s ^ 2) ^ (m - 2) := pow_nonneg hu0 _
      calc
        _ = (4 * ((m : ℝ) + 1) ^ 2 + 8 * ((m : ℝ) + 1)) *
              (1 - s ^ 2) ^ (m - 2) := by ring
        _ ≤ (16 * ((m : ℝ) + 1) ^ 2) *
              (1 - s ^ 2) ^ (m - 2) :=
          mul_le_mul_of_nonneg_right hcoef hupow
        _ = _ := by ring

private theorem rpow_sub_nat_le_four_pow_mul
    {A e : ℝ} (hA : 0 < A) (hA4 : A ≤ 4)
    {r k : ℕ} (hrk : r ≤ k) :
    A ^ (e - r) ≤
      (4 : ℝ) ^ (k - r) * A ^ (e - k) := by
  have hexp :
      e - (r : ℝ) = (e - (k : ℝ)) + ((k - r : ℕ) : ℝ) := by
    rw [Nat.cast_sub hrk]
    ring
  rw [hexp, Real.rpow_add hA, Real.rpow_natCast]
  have hpow : A ^ (k - r) ≤ (4 : ℝ) ^ (k - r) :=
    pow_le_pow_left₀ hA.le hA4 _
  exact (mul_le_mul_of_nonneg_left hpow
    (Real.rpow_nonneg hA.le (e - k))).trans_eq (by ring)

private theorem abs_unequalAPow_le
    {e s t : ℝ} (hA : 0 < angularKernelA s t) :
    |unequalAPow e s t| = angularKernelA s t ^ e := by
  unfold unequalAPow
  exact abs_of_pos (Real.rpow_pos_of_pos hA _)

private theorem abs_unequalAPowS_le
    {α s t : ℝ} {m : ℕ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |unequalAPowS (α / 2 - 2 * (m : ℝ)) s t| ≤
      10 * ((m : ℝ) + 1) *
        angularKernelA s t ^
          (α / 2 - 2 * (m : ℝ) - 1) := by
  have he := abs_latitude_even_exponent_sub_le hα0 hα2 m 0 (by omega)
  norm_num at he
  have ht1 := abs_height_le_one_of_mem ht
  have hw : 0 ≤ (m : ℝ) + 1 := by positivity
  unfold unequalAPowS
  rw [abs_mul, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hA _), abs_mul, abs_neg]
  norm_num
  have hp : 0 ≤ angularKernelA s t ^
      (α / 2 - 2 * (m : ℝ) - 1) :=
    Real.rpow_nonneg hA.le _
  calc
    |α / 2 - 2 * (m : ℝ)| *
          angularKernelA s t ^ (α / 2 - 2 * (m : ℝ) - 1) *
          (2 * |t|) ≤
        (5 * ((m : ℝ) + 1)) *
          angularKernelA s t ^ (α / 2 - 2 * (m : ℝ) - 1) *
          (2 * 1) := by gcongr
    _ = _ := by ring

private theorem abs_unequalAPowT_le
    {α s t : ℝ} {m : ℕ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |unequalAPowT (α / 2 - 2 * (m : ℝ)) s t| ≤
      10 * ((m : ℝ) + 1) *
        angularKernelA s t ^
          (α / 2 - 2 * (m : ℝ) - 1) := by
  have hAsym : angularKernelA t s = angularKernelA s t := by
    unfold angularKernelA
    ring
  have hA' : 0 < angularKernelA t s := by rwa [hAsym]
  simpa [unequalAPowT, unequalAPowS, mul_comm, mul_left_comm,
    mul_assoc, hAsym] using
    (abs_unequalAPowS_le (α := α) (s := t) (t := s) (m := m)
      hα0 hα2 hs hA')

private theorem abs_unequalAPowSS_le
    {α s t : ℝ} {m : ℕ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |unequalAPowSS (α / 2 - 2 * (m : ℝ)) s t| ≤
      100 * ((m : ℝ) + 1) ^ 2 *
        angularKernelA s t ^
          (α / 2 - 2 * (m : ℝ) - 2) := by
  have he0 := abs_latitude_even_exponent_sub_le hα0 hα2 m 0 (by omega)
  have he1 := abs_latitude_even_exponent_sub_le hα0 hα2 m 1 (by omega)
  norm_num at he0 he1
  have ht1 := abs_height_le_one_of_mem ht
  unfold unequalAPowSS
  simp only [abs_mul, abs_pow, abs_neg,
    abs_of_pos (Real.rpow_pos_of_pos hA _)]
  norm_num
  calc
    |α / 2 - 2 * (m : ℝ)| *
          |α / 2 - 2 * (m : ℝ) - 1| *
          angularKernelA s t ^ (α / 2 - 2 * (m : ℝ) - 2) *
          (2 * |t|) ^ 2 ≤
        (5 * ((m : ℝ) + 1)) * (5 * ((m : ℝ) + 1)) *
          angularKernelA s t ^ (α / 2 - 2 * (m : ℝ) - 2) *
          (2 * 1) ^ 2 := by gcongr
    _ = _ := by ring

private theorem abs_unequalAPowTT_le
    {α s t : ℝ} {m : ℕ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |unequalAPowTT (α / 2 - 2 * (m : ℝ)) s t| ≤
      100 * ((m : ℝ) + 1) ^ 2 *
        angularKernelA s t ^
          (α / 2 - 2 * (m : ℝ) - 2) := by
  have hAsym : angularKernelA t s = angularKernelA s t := by
    unfold angularKernelA
    ring
  have hA' : 0 < angularKernelA t s := by rwa [hAsym]
  simpa [unequalAPowTT, unequalAPowSS, mul_comm, mul_left_comm,
    mul_assoc, hAsym] using
    (abs_unequalAPowSS_le (α := α) (s := t) (t := s) (m := m)
      hα0 hα2 hs hA')

private theorem abs_unequalAPowST_le
    {α s t : ℝ} {m : ℕ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |unequalAPowST (α / 2 - 2 * (m : ℝ)) s t| ≤
      256 * ((m : ℝ) + 1) ^ 2 *
        angularKernelA s t ^
          (α / 2 - 2 * (m : ℝ) - 2) := by
  let e := α / 2 - 2 * (m : ℝ)
  let A := angularKernelA s t
  let w := (m : ℝ) + 1
  have he0 := abs_latitude_even_exponent_sub_le hα0 hα2 m 0 (by omega)
  have he1 := abs_latitude_even_exponent_sub_le hα0 hα2 m 1 (by omega)
  norm_num at he0 he1
  have hs1 := abs_height_le_one_of_mem hs
  have ht1 := abs_height_le_one_of_mem ht
  have hA4 := angularKernelA_le_four_of_mem hs ht
  have hp12 : A ^ (e - 1) ≤ 4 * A ^ (e - 2) := by
    simpa [A, e] using
      (rpow_sub_nat_le_four_pow_mul (A := A) (e := e)
        hA hA4 (r := 1) (k := 2) (by omega))
  have hA2nonneg : 0 ≤ A ^ (e - 2) := Real.rpow_nonneg hA.le _
  have hw : 1 ≤ w := by
    dsimp [w]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  unfold unequalAPowST
  dsimp only [e, A, w] at *
  calc
    |_ + _| ≤
        |e * (e - 1) * A ^ (e - 2) *
          (-2 * s) * (-2 * t)| +
        |e * A ^ (e - 1) * (-2)| := abs_add _ _
    _ ≤
        100 * w ^ 2 * A ^ (e - 2) +
          10 * w * (4 * A ^ (e - 2)) := by
      simp only [abs_mul, abs_neg]
      norm_num
      rw [abs_of_pos (Real.rpow_pos_of_pos hA (e - 2)),
        abs_of_pos (Real.rpow_pos_of_pos hA (e - 1))]
      apply add_le_add
      · calc
          |e| * |e - 1| * A ^ (e - 2) *
                (2 * |s|) * (2 * |t|) ≤
              (5 * w) * (5 * w) * A ^ (e - 2) *
                (2 * 1) * (2 * 1) := by gcongr
          _ = 100 * w ^ 2 * A ^ (e - 2) := by ring
      · calc
          |e| * A ^ (e - 1) * 2 ≤
              (5 * w) * (4 * A ^ (e - 2)) * 2 := by gcongr
          _ = 10 * w * (4 * A ^ (e - 2)) := by ring
    _ ≤ 256 * w ^ 2 * A ^ (e - 2) := by
      have hcoeff : 140 * w ^ 2 ≤ 256 * w ^ 2 := by
        nlinarith [sq_nonneg w]
      calc
        _ ≤ 140 * w ^ 2 * A ^ (e - 2) := by
          have hww : 0 ≤ (w - 1) * w :=
            mul_nonneg (sub_nonneg.mpr hw) (zero_le_one.trans hw)
          have := mul_le_mul_of_nonneg_right
            (show 100 * w ^ 2 + 40 * w ≤ 140 * w ^ 2 by
              nlinarith) hA2nonneg
          convert this using 1 ; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hA2nonneg

private theorem abs_unequalAPowSST_le
    {α s t : ℝ} {m : ℕ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |unequalAPowSST (α / 2 - 2 * (m : ℝ)) s t| ≤
      2048 * ((m : ℝ) + 1) ^ 3 *
        angularKernelA s t ^
          (α / 2 - 2 * (m : ℝ) - 3) := by
  let e := α / 2 - 2 * (m : ℝ)
  let A := angularKernelA s t
  let w := (m : ℝ) + 1
  have he0 := abs_latitude_even_exponent_sub_le hα0 hα2 m 0 (by omega)
  have he1 := abs_latitude_even_exponent_sub_le hα0 hα2 m 1 (by omega)
  have he2 := abs_latitude_even_exponent_sub_le hα0 hα2 m 2 (by omega)
  norm_num at he0 he1 he2
  have hs1 := abs_height_le_one_of_mem hs
  have ht1 := abs_height_le_one_of_mem ht
  have hA4 := angularKernelA_le_four_of_mem hs ht
  have hp23 : A ^ (e - 2) ≤ 4 * A ^ (e - 3) := by
    simpa [A, e] using
      (rpow_sub_nat_le_four_pow_mul (A := A) (e := e)
        hA hA4 (r := 2) (k := 3) (by omega))
  have hA3nonneg : 0 ≤ A ^ (e - 3) := Real.rpow_nonneg hA.le _
  have hw : 1 ≤ w := by
    dsimp [w]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  unfold unequalAPowSST
  dsimp only [e, A, w] at *
  calc
    |_ + _| ≤
        |e * (e - 1) * (e - 2) * A ^ (e - 3) *
          (-2 * s) * (-2 * t) ^ 2| +
        |2 * e * (e - 1) * A ^ (e - 2) *
          (-2 * t) * (-2)| := abs_add _ _
    _ ≤
        1000 * w ^ 3 * A ^ (e - 3) +
          200 * w ^ 2 * (4 * A ^ (e - 3)) := by
      simp only [abs_mul, abs_pow, abs_neg]
      norm_num
      rw [abs_of_pos (Real.rpow_pos_of_pos hA (e - 3)),
        abs_of_pos (Real.rpow_pos_of_pos hA (e - 2))]
      apply add_le_add
      · calc
          |e| * |e - 1| * |e - 2| * A ^ (e - 3) *
                (2 * |s|) * (2 * |t|) ^ 2 ≤
              (5 * w) * (5 * w) * (5 * w) * A ^ (e - 3) *
                (2 * 1) * (2 * 1) ^ 2 := by gcongr
          _ = 1000 * w ^ 3 * A ^ (e - 3) := by ring
      · calc
          2 * |e| * |e - 1| * A ^ (e - 2) *
                (2 * |t|) * 2 ≤
              2 * (5 * w) * (5 * w) * (4 * A ^ (e - 3)) *
                (2 * 1) * 2 := by gcongr
          _ = 200 * w ^ 2 * (4 * A ^ (e - 3)) := by ring
    _ ≤ 2048 * w ^ 3 * A ^ (e - 3) := by
      have hcoef : 1800 * w ^ 3 ≤ 2048 * w ^ 3 := by
        have : 0 ≤ w ^ 3 := pow_nonneg (by positivity) _
        nlinarith
      calc
        _ ≤ 1800 * w ^ 3 * A ^ (e - 3) := by
          have hww : 0 ≤ (w - 1) * w ^ 2 :=
            mul_nonneg (sub_nonneg.mpr hw)
              (pow_nonneg (zero_le_one.trans hw) _)
          have := mul_le_mul_of_nonneg_right
            (show 1000 * w ^ 3 + 800 * w ^ 2 ≤ 1800 * w ^ 3 by
              nlinarith)
            hA3nonneg
          convert this using 1 ; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hA3nonneg

private theorem abs_unequalAPowSTT_le
    {α s t : ℝ} {m : ℕ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |unequalAPowSTT (α / 2 - 2 * (m : ℝ)) s t| ≤
      2048 * ((m : ℝ) + 1) ^ 3 *
        angularKernelA s t ^
          (α / 2 - 2 * (m : ℝ) - 3) := by
  have hAsym : angularKernelA t s = angularKernelA s t := by
    unfold angularKernelA
    ring
  have hA' : 0 < angularKernelA t s := by rwa [hAsym]
  simpa [unequalAPowSTT, unequalAPowSST, mul_comm, mul_left_comm,
    mul_assoc, hAsym] using
    (abs_unequalAPowSST_le (α := α) (s := t) (t := s) (m := m)
      hα0 hα2 ht hs hA')

private theorem abs_unequalAPowSSTT_le
    {α s t : ℝ} {m : ℕ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |unequalAPowSSTT (α / 2 - 2 * (m : ℝ)) s t| ≤
      32768 * ((m : ℝ) + 1) ^ 4 *
        angularKernelA s t ^
          (α / 2 - 2 * (m : ℝ) - 4) := by
  let e := α / 2 - 2 * (m : ℝ)
  let A := angularKernelA s t
  let w := (m : ℝ) + 1
  have he0 := abs_latitude_even_exponent_sub_le hα0 hα2 m 0 (by omega)
  have he1 := abs_latitude_even_exponent_sub_le hα0 hα2 m 1 (by omega)
  have he2 := abs_latitude_even_exponent_sub_le hα0 hα2 m 2 (by omega)
  have he3 := abs_latitude_even_exponent_sub_le hα0 hα2 m 3 (by omega)
  norm_num at he0 he1 he2 he3
  have hs1 := abs_height_le_one_of_mem hs
  have ht1 := abs_height_le_one_of_mem ht
  have hA4 := angularKernelA_le_four_of_mem hs ht
  have hp34 : A ^ (e - 3) ≤ 4 * A ^ (e - 4) := by
    simpa [A, e] using
      (rpow_sub_nat_le_four_pow_mul (A := A) (e := e)
        hA hA4 (r := 3) (k := 4) (by omega))
  have hp24 : A ^ (e - 2) ≤ 16 * A ^ (e - 4) := by
    convert
      (rpow_sub_nat_le_four_pow_mul (A := A) (e := e)
        hA hA4 (r := 2) (k := 4) (by omega)) using 1 ;
      norm_num [A, e]
  have hA4nonneg : 0 ≤ A ^ (e - 4) := Real.rpow_nonneg hA.le _
  have hw : 1 ≤ w := by
    dsimp [w]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  unfold unequalAPowSSTT
  dsimp only [e, A, w] at *
  calc
    |_ + _ + _| ≤
        |e * (e - 1) * (e - 2) * (e - 3) *
          A ^ (e - 4) * (-2 * s) ^ 2 * (-2 * t) ^ 2| +
        |4 * e * (e - 1) * (e - 2) *
          A ^ (e - 3) * (-2 * s) * (-2 * t) * (-2)| +
        |2 * e * (e - 1) * A ^ (e - 2) * (-2) ^ 2| := by
      exact (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤
        10000 * w ^ 4 * A ^ (e - 4) +
          4000 * w ^ 3 * (4 * A ^ (e - 4)) +
          200 * w ^ 2 * (16 * A ^ (e - 4)) := by
      simp only [abs_mul, abs_pow, abs_neg]
      norm_num
      rw [abs_of_pos (Real.rpow_pos_of_pos hA (e - 4)),
        abs_of_pos (Real.rpow_pos_of_pos hA (e - 3)),
        abs_of_pos (Real.rpow_pos_of_pos hA (e - 2))]
      apply add_le_add
      · apply add_le_add
        · calc
            |e| * |e - 1| * |e - 2| * |e - 3| *
                  A ^ (e - 4) * (2 * |s|) ^ 2 *
                  (2 * |t|) ^ 2 ≤
                (5 * w) * (5 * w) * (5 * w) * (5 * w) *
                  A ^ (e - 4) * (2 * 1) ^ 2 * (2 * 1) ^ 2 := by gcongr
            _ = 10000 * w ^ 4 * A ^ (e - 4) := by ring
        · calc
            4 * |e| * |e - 1| * |e - 2| * A ^ (e - 3) *
                  (2 * |s|) * (2 * |t|) * 2 ≤
                4 * (5 * w) * (5 * w) * (5 * w) *
                  (4 * A ^ (e - 4)) * (2 * 1) * (2 * 1) * 2 := by
              gcongr
            _ = 4000 * w ^ 3 * (4 * A ^ (e - 4)) := by ring
      · calc
          2 * |e| * |e - 1| *
              angularKernelA s t ^ (e - 2) * 4 ≤
              2 * (5 * w) * (5 * w) *
                (16 * angularKernelA s t ^ (e - 4)) * 4 := by
            gcongr
          _ = 200 * w ^ 2 * (16 * A ^ (e - 4)) := by ring
    _ ≤ 32768 * w ^ 4 * A ^ (e - 4) := by
      have hcoef : 29200 * w ^ 4 ≤ 32768 * w ^ 4 := by
        have : 0 ≤ w ^ 4 := pow_nonneg (by positivity) _
        nlinarith
      calc
        _ ≤ 29200 * w ^ 4 * A ^ (e - 4) := by
          have h23 : 0 ≤ (w - 1) * w ^ 2 :=
            mul_nonneg (sub_nonneg.mpr hw)
              (pow_nonneg (zero_le_one.trans hw) _)
          have h34 : 0 ≤ (w - 1) * w ^ 3 :=
            mul_nonneg (sub_nonneg.mpr hw)
              (pow_nonneg (zero_le_one.trans hw) _)
          have := mul_le_mul_of_nonneg_right
            (show 10000 * w ^ 4 + 16000 * w ^ 3 + 3200 * w ^ 2 ≤
                29200 * w ^ 4 by
              nlinarith)
            hA4nonneg
          convert this using 1 ; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hA4nonneg

private theorem rpow_sub_nat_mul_pow
    {A e : ℝ} (hA : 0 < A) (k : ℕ) :
    A ^ (e - k) * A ^ k = A ^ e := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hA]
  congr 1
  ring


theorem abs_separatedEvenPowerSummandDSSTT_le
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {s t q : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hApos : 0 < angularKernelA s t)
    (hq : separatedRatio s t ≤ q)
    {m : ℕ} (hm : 2 ≤ m) :
    |separatedEvenPowerSummandDSSTT α m s t| ≤
      4194304 * ((m : ℝ) + 1) ^ (4 : ℕ) *
        angularKernelA s t ^ (α / 2 - 4) * q ^ (m - 2) := by
  let A := angularKernelA s t
  let u := 1 - s ^ 2
  let v := 1 - t ^ 2
  let e := α / 2 - 2 * (m : ℝ)
  let w := (m : ℝ) + 1
  have hsSphere := hs
  have htSphere := ht
  have hA : 0 < A := hApos
  have hq0 : 0 ≤ q := (separatedRatio_nonneg hs ht).trans hq
  have hu0 : 0 ≤ u := by
    dsimp [u]
    nlinarith [hsSphere.1, hsSphere.2]
  have hv0 : 0 ≤ v := by
    dsimp [v]
    nlinarith [htSphere.1, htSphere.2]
  have huA : u ≤ A := by
    have hv0' : 0 ≤ 1 - t ^ 2 := by
      nlinarith [htSphere.1, htSphere.2]
    dsimp [u, A]
    rw [angularKernelA_eq_radiusSq_add]
    calc
      1 - s ^ 2 ≤ (1 - s ^ 2) + (1 - t ^ 2) :=
        le_add_of_nonneg_right hv0'
      _ ≤ (1 - s ^ 2) + (1 - t ^ 2) + (s - t) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg (s - t))
  have hvA : v ≤ A := by
    have hu0' : 0 ≤ 1 - s ^ 2 := by
      nlinarith [hsSphere.1, hsSphere.2]
    dsimp [v, A]
    rw [angularKernelA_eq_radiusSq_add]
    calc
      1 - t ^ 2 ≤ (1 - s ^ 2) + (1 - t ^ 2) :=
        le_add_of_nonneg_left hu0'
      _ ≤ (1 - s ^ 2) + (1 - t ^ 2) + (s - t) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg (s - t))
  have hA4 : A ≤ 4 := angularKernelA_le_four_of_mem hsSphere htSphere
  have hw : 1 ≤ w := by
    dsimp [w]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hP0 :
      |unequalAPow e s t| = A ^ e := by
    exact abs_unequalAPow_le hA
  have hP1s :
      |unequalAPowS e s t| ≤ 10 * w * A ^ (e - 1) := by
    exact abs_unequalAPowS_le hα0 hα2 htSphere hA
  have hP1t :
      |unequalAPowT e s t| ≤ 10 * w * A ^ (e - 1) := by
    exact abs_unequalAPowT_le hα0 hα2 hsSphere hA
  have hP2ss :
      |unequalAPowSS e s t| ≤ 256 * w ^ 2 * A ^ (e - 2) := by
    have hbase := abs_unequalAPowSS_le
      (α := α) (m := m) hα0 hα2 htSphere hA
    simpa [e, w, A] using hbase.trans (by
      have hp : 0 ≤ ((m : ℝ) + 1) ^ 2 *
          angularKernelA s t ^ (α / 2 - 2 * (m : ℝ) - 2) := by positivity
      nlinarith)
  have hP2st :
      |unequalAPowST e s t| ≤ 256 * w ^ 2 * A ^ (e - 2) :=
    abs_unequalAPowST_le hα0 hα2 hsSphere htSphere hA
  have hP2tt :
      |unequalAPowTT e s t| ≤ 256 * w ^ 2 * A ^ (e - 2) := by
    have hbase := abs_unequalAPowTT_le
      (α := α) (m := m) hα0 hα2 hsSphere hA
    simpa [e, w, A] using hbase.trans (by
      have hp : 0 ≤ ((m : ℝ) + 1) ^ 2 *
          angularKernelA s t ^ (α / 2 - 2 * (m : ℝ) - 2) := by positivity
      nlinarith)
  have hP3sst :
      |unequalAPowSST e s t| ≤ 2048 * w ^ 3 * A ^ (e - 3) :=
    abs_unequalAPowSST_le hα0 hα2 hsSphere htSphere hA
  have hP3stt :
      |unequalAPowSTT e s t| ≤ 2048 * w ^ 3 * A ^ (e - 3) :=
    abs_unequalAPowSTT_le hα0 hα2 hsSphere htSphere hA
  have hP4 :
      |unequalAPowSSTT e s t| ≤ 32768 * w ^ 4 * A ^ (e - 4) :=
    abs_unequalAPowSSTT_le hα0 hα2 hsSphere htSphere hA
  have hU0 :
      |unequalRadiusPower m s| ≤ A ^ 2 * u ^ (m - 2) :=
    abs_unequalRadiusPower_le hm hsSphere huA
  have hU1 :
      |unequalRadiusPowerD1 m s| ≤
        2 * w * A * u ^ (m - 2) :=
    abs_unequalRadiusPowerD1_le hm hsSphere huA
  have hU2 :
      |unequalRadiusPowerD2 m s| ≤
        16 * w ^ 2 * u ^ (m - 2) :=
    abs_unequalRadiusPowerD2_le hm hsSphere huA hA4
  have hV0 :
      |unequalRadiusPower m t| ≤ A ^ 2 * v ^ (m - 2) :=
    abs_unequalRadiusPower_le hm htSphere hvA
  have hV1 :
      |unequalRadiusPowerD1 m t| ≤
        2 * w * A * v ^ (m - 2) :=
    abs_unequalRadiusPowerD1_le hm htSphere hvA
  have hV2 :
      |unequalRadiusPowerD2 m t| ≤
        16 * w ^ 2 * v ^ (m - 2) :=
    abs_unequalRadiusPowerD2_le hm htSphere hvA hA4
  let X :=
    unequalAPowSS e s t * unequalRadiusPower m s +
      2 * unequalAPowS e s t * unequalRadiusPowerD1 m s +
      unequalAPow e s t * unequalRadiusPowerD2 m s
  let XT :=
    unequalAPowSST e s t * unequalRadiusPower m s +
      2 * unequalAPowST e s t * unequalRadiusPowerD1 m s +
      unequalAPowT e s t * unequalRadiusPowerD2 m s
  let XTT :=
    unequalAPowSSTT e s t * unequalRadiusPower m s +
      2 * unequalAPowSTT e s t * unequalRadiusPowerD1 m s +
      unequalAPowTT e s t * unequalRadiusPowerD2 m s
  have hAe21 : A ^ (e - 2) * A ^ 2 = A ^ e :=
    rpow_sub_nat_mul_pow hA 2
  have hAe11 : A ^ (e - 1) * A = A ^ e := by
    simpa using rpow_sub_nat_mul_pow hA 1
  have hAe32 : A ^ (e - 3) * A ^ 2 = A ^ (e - 1) := by
    have h := rpow_sub_nat_mul_pow (A := A) (e := e - 1) hA 2
    have hexp : e - 3 = (e - 1) - (2 : ℝ) := by ring
    rw [hexp]
    exact h
  have hAe21' : A ^ (e - 2) * A = A ^ (e - 1) := by
    have h := rpow_sub_nat_mul_pow (A := A) (e := e - 1) hA 1
    have hexp : e - 2 = (e - 1) - (1 : ℝ) := by ring
    rw [hexp]
    simpa using h
  have hAe42 : A ^ (e - 4) * A ^ 2 = A ^ (e - 2) := by
    have h := rpow_sub_nat_mul_pow (A := A) (e := e - 2) hA 2
    have hexp : e - 4 = (e - 2) - (2 : ℝ) := by ring
    rw [hexp]
    exact h
  have hAe31 : A ^ (e - 3) * A = A ^ (e - 2) := by
    have h := rpow_sub_nat_mul_pow (A := A) (e := e - 2) hA 1
    have hexp : e - 3 = (e - 2) - (1 : ℝ) := by ring
    rw [hexp]
    simpa using h
  have hX : |X| ≤ 1024 * w ^ 2 * A ^ e * u ^ (m - 2) := by
    dsimp only [X]
    calc
      |_ + _ + _| ≤
          |unequalAPowSS e s t| * |unequalRadiusPower m s| +
          2 * |unequalAPowS e s t| * |unequalRadiusPowerD1 m s| +
          |unequalAPow e s t| * |unequalRadiusPowerD2 m s| := by
        simpa [abs_mul] using
          (abs_add
            (unequalAPowSS e s t * unequalRadiusPower m s +
              2 * unequalAPowS e s t * unequalRadiusPowerD1 m s)
            (unequalAPow e s t * unequalRadiusPowerD2 m s)).trans
            (add_le_add_right
              (abs_add
                (unequalAPowSS e s t * unequalRadiusPower m s)
                (2 * unequalAPowS e s t * unequalRadiusPowerD1 m s)) _)
      _ ≤
          (256 * w ^ 2 * A ^ (e - 2)) * (A ^ 2 * u ^ (m - 2)) +
          2 * (10 * w * A ^ (e - 1)) *
            (2 * w * A * u ^ (m - 2)) +
          A ^ e * (16 * w ^ 2 * u ^ (m - 2)) := by
        have hP0le : |unequalAPow e s t| ≤ A ^ e := hP0.le
        gcongr
      _ = 312 * w ^ 2 * A ^ e * u ^ (m - 2) := by
        calc
          _ = (256 * w ^ 2 * (A ^ (e - 2) * A ^ 2) +
                40 * w ^ 2 * (A ^ (e - 1) * A) +
                16 * w ^ 2 * A ^ e) * u ^ (m - 2) := by ring
          _ = _ := by rw [hAe21, hAe11]; ring
      _ ≤ 1024 * w ^ 2 * A ^ e * u ^ (m - 2) := by
        have hp : 0 ≤ w ^ 2 * A ^ e * u ^ (m - 2) := by positivity
        nlinarith
  have hXT :
      |XT| ≤ 4096 * w ^ 3 * A ^ (e - 1) * u ^ (m - 2) := by
    dsimp only [XT]
    calc
      |_ + _ + _| ≤
          |unequalAPowSST e s t| * |unequalRadiusPower m s| +
          2 * |unequalAPowST e s t| * |unequalRadiusPowerD1 m s| +
          |unequalAPowT e s t| * |unequalRadiusPowerD2 m s| := by
        simpa [abs_mul] using
          (abs_add
            (unequalAPowSST e s t * unequalRadiusPower m s +
              2 * unequalAPowST e s t * unequalRadiusPowerD1 m s)
            (unequalAPowT e s t * unequalRadiusPowerD2 m s)).trans
            (add_le_add_right
              (abs_add
                (unequalAPowSST e s t * unequalRadiusPower m s)
                (2 * unequalAPowST e s t * unequalRadiusPowerD1 m s)) _)
      _ ≤
          (2048 * w ^ 3 * A ^ (e - 3)) * (A ^ 2 * u ^ (m - 2)) +
          2 * (256 * w ^ 2 * A ^ (e - 2)) *
            (2 * w * A * u ^ (m - 2)) +
          (10 * w * A ^ (e - 1)) *
            (16 * w ^ 2 * u ^ (m - 2)) := by gcongr
      _ = 3232 * w ^ 3 * A ^ (e - 1) * u ^ (m - 2) := by
        calc
          _ = (2048 * w ^ 3 * (A ^ (e - 3) * A ^ 2) +
                1024 * w ^ 3 * (A ^ (e - 2) * A) +
                160 * w ^ 3 * A ^ (e - 1)) * u ^ (m - 2) := by ring
          _ = _ := by rw [hAe32, hAe21']; ring
      _ ≤ 4096 * w ^ 3 * A ^ (e - 1) * u ^ (m - 2) := by
        have hp : 0 ≤ w ^ 3 * A ^ (e - 1) * u ^ (m - 2) := by positivity
        nlinarith
  have hXTT :
      |XTT| ≤ 65536 * w ^ 4 * A ^ (e - 2) * u ^ (m - 2) := by
    dsimp only [XTT]
    calc
      |_ + _ + _| ≤
          |unequalAPowSSTT e s t| * |unequalRadiusPower m s| +
          2 * |unequalAPowSTT e s t| * |unequalRadiusPowerD1 m s| +
          |unequalAPowTT e s t| * |unequalRadiusPowerD2 m s| := by
        simpa [abs_mul] using
          (abs_add
            (unequalAPowSSTT e s t * unequalRadiusPower m s +
              2 * unequalAPowSTT e s t * unequalRadiusPowerD1 m s)
            (unequalAPowTT e s t * unequalRadiusPowerD2 m s)).trans
            (add_le_add_right
              (abs_add
                (unequalAPowSSTT e s t * unequalRadiusPower m s)
                (2 * unequalAPowSTT e s t * unequalRadiusPowerD1 m s)) _)
      _ ≤
          (32768 * w ^ 4 * A ^ (e - 4)) * (A ^ 2 * u ^ (m - 2)) +
          2 * (2048 * w ^ 3 * A ^ (e - 3)) *
            (2 * w * A * u ^ (m - 2)) +
          (256 * w ^ 2 * A ^ (e - 2)) *
            (16 * w ^ 2 * u ^ (m - 2)) := by gcongr
      _ = 45056 * w ^ 4 * A ^ (e - 2) * u ^ (m - 2) := by
        calc
          _ = (32768 * w ^ 4 * (A ^ (e - 4) * A ^ 2) +
                8192 * w ^ 4 * (A ^ (e - 3) * A) +
                4096 * w ^ 4 * A ^ (e - 2)) * u ^ (m - 2) := by ring
          _ = _ := by rw [hAe42, hAe31]; ring
      _ ≤ 65536 * w ^ 4 * A ^ (e - 2) * u ^ (m - 2) := by
        have hp : 0 ≤ w ^ 4 * A ^ (e - 2) * u ^ (m - 2) := by positivity
        nlinarith
  have hraw :
      |separatedEvenPowerSummandDSSTT α m s t| ≤
        262144 * w ^ 4 * (4 : ℝ) ^ m *
          A ^ e * u ^ (m - 2) * v ^ (m - 2) := by
    unfold separatedEvenPowerSummandDSSTT
    dsimp only
    change |(4 : ℝ) ^ m *
      (XTT * unequalRadiusPower m t +
        2 * XT * unequalRadiusPowerD1 m t +
        X * unequalRadiusPowerD2 m t)| ≤ _
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by norm_num) m)]
    calc
      (4 : ℝ) ^ m * |_ + _ + _| ≤
          (4 : ℝ) ^ m *
            (|XTT| * |unequalRadiusPower m t| +
              2 * |XT| * |unequalRadiusPowerD1 m t| +
              |X| * |unequalRadiusPowerD2 m t|) := by
        gcongr
        simpa [abs_mul] using
          (abs_add
            (XTT * unequalRadiusPower m t +
              2 * XT * unequalRadiusPowerD1 m t)
            (X * unequalRadiusPowerD2 m t)).trans
            (add_le_add_right
              (abs_add
                (XTT * unequalRadiusPower m t)
                (2 * XT * unequalRadiusPowerD1 m t)) _)
      _ ≤ (4 : ℝ) ^ m *
          ((65536 * w ^ 4 * A ^ (e - 2) * u ^ (m - 2)) *
              (A ^ 2 * v ^ (m - 2)) +
            2 * (4096 * w ^ 3 * A ^ (e - 1) * u ^ (m - 2)) *
              (2 * w * A * v ^ (m - 2)) +
            (1024 * w ^ 2 * A ^ e * u ^ (m - 2)) *
              (16 * w ^ 2 * v ^ (m - 2))) := by gcongr
      _ = 98304 * w ^ 4 * (4 : ℝ) ^ m *
          A ^ e * u ^ (m - 2) * v ^ (m - 2) := by
        calc
          _ = (4 : ℝ) ^ m *
              (65536 * w ^ 4 * (A ^ (e - 2) * A ^ 2) +
                16384 * w ^ 4 * (A ^ (e - 1) * A) +
                16384 * w ^ 4 * A ^ e) *
              u ^ (m - 2) * v ^ (m - 2) := by ring
          _ = _ := by rw [hAe21, hAe11]; ring
      _ ≤ 262144 * w ^ 4 * (4 : ℝ) ^ m *
          A ^ e * u ^ (m - 2) * v ^ (m - 2) := by
        have hp : 0 ≤ w ^ 4 * (4 : ℝ) ^ m *
            A ^ e * u ^ (m - 2) * v ^ (m - 2) := by positivity
        convert mul_le_mul_of_nonneg_right
          (show (98304 : ℝ) ≤ 262144 by norm_num) hp using 1 <;> ring
  have hcommon :=
    latitude_common_factor_eq (α := α) (A := A) (u := u) (v := v)
      hA m hm
  have hQ := hq
  have hQ0 := separatedRatio_nonneg hsSphere htSphere
  have hpow :
      separatedRatio s t ^ (m - 2) ≤
        q ^ (m - 2) :=
    pow_le_pow_left₀ hQ0 hQ _
  calc
    |separatedEvenPowerSummandDSSTT α m s t| ≤
        262144 * w ^ 4 *
          ((4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) * A ^ e) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
    _ = 262144 * w ^ 4 *
        (16 * A ^ (α / 2 - 4) *
          separatedRatio s t ^ (m - 2)) := by
      rw [hcommon]
      rfl
    _ ≤ 262144 * w ^ 4 *
        (16 * A ^ (α / 2 - 4) *
          q ^ (m - 2)) := by
      gcongr
    _ = 4194304 * ((m : ℝ) + 1) ^ (4 : ℕ) *
        angularKernelA s t ^ (α / 2 - 4) *
        q ^ (m - 2) := by
      dsimp [w, A]
      ring


noncomputable def separatedEvenPowerDSSTTSeriesTerm
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  (Ring.choose (α / 2) (2 * m) *
    normalizedCosineMoment (2 * m)) *
    separatedEvenPowerSummandDSSTT α m s t

/-- The coefficient-weighted fourth derivative tail is normally
summable at every point of a left-small rectangle.  The first two modes
are absent from this shifted formulation and are inserted in the next
theorem as a finite prefix. -/
theorem summable_shifted_separatedEvenPowerDSSTTSeriesTerm
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {s t q : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hApos : 0 < angularKernelA s t)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hq : separatedRatio s t ≤ q) :
    Summable (fun r : ℕ ↦
      separatedEvenPowerDSSTTSeriesTerm α (r + 2) s t) := by
  have hcoef :=
    summable_shifted_evenAngularDerivativeCoefficient_mul_pow
      α (q := q) hq0 hq1
  have hmaj := hcoef.mul_left
    (4194304 * angularKernelA s t ^ (α / 2 - 4))
  apply hmaj.of_norm_bounded
  intro r
  have hterm :=
    abs_separatedEvenPowerSummandDSSTT_le
      hα0 hα2 hs ht hApos hq (m := r + 2) (by omega)
  rw [show r + 2 - 2 = r by omega] at hterm
  unfold separatedEvenPowerDSSTTSeriesTerm
  change |(Ring.choose (α / 2) (2 * (r + 2)) *
    normalizedCosineMoment (2 * (r + 2))) *
    separatedEvenPowerSummandDSSTT α (r + 2) s t| ≤ _
  rw [abs_mul]
  calc
    |Ring.choose (α / 2) (2 * (r + 2)) *
        normalizedCosineMoment (2 * (r + 2))| *
        |separatedEvenPowerSummandDSSTT α (r + 2) s t| ≤
      (|Ring.choose (α / 2) (2 * (r + 2))| *
        |normalizedCosineMoment (2 * (r + 2))|) *
      (4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
        angularKernelA s t ^ (α / 2 - 4) *
        q ^ r) := by
      rw [abs_mul]
      gcongr
    _ =
      4194304 * angularKernelA s t ^ (α / 2 - 4) *
        (evenAngularDerivativeCoefficient α (r + 2) *
          q ^ r) := by
      unfold evenAngularDerivativeCoefficient
      ring

/-- Normal convergence of the complete coefficient-weighted `(2,2)`
derivative series; modes `0` and `1` form a finite prefix. -/
theorem summable_separatedEvenPowerDSSTTSeriesTerm
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {s t q : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hApos : 0 < angularKernelA s t)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hq : separatedRatio s t ≤ q) :
    Summable (fun m : ℕ ↦
      separatedEvenPowerDSSTTSeriesTerm α m s t) := by
  rw [← summable_nat_add_iff 2]
  simpa [Nat.add_comm] using
    summable_shifted_separatedEvenPowerDSSTTSeriesTerm
      hα0 hα2 hs ht hApos hq0 hq1 hq


theorem abs_separatedEvenPowerDSSTTSeriesTerm_zero_le
    {α s t : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |separatedEvenPowerDSSTTSeriesTerm α 0 s t| ≤
      32768 * angularKernelA s t ^ (α / 2 - 4) := by
  have h :=
    abs_unequalAPowSSTT_le
      (α := α) (m := 0) hα0 hα2 hs ht hA
  unfold separatedEvenPowerDSSTTSeriesTerm
    separatedEvenPowerSummandDSSTT
  dsimp only
  norm_num [unequalRadiusPower, unequalRadiusPowerD1,
    unequalRadiusPowerD2]
  change
    |normalizedCosineMoment 0 * unequalAPowSSTT (α / 2) s t| ≤ _
  rw [abs_mul]
  calc
    |normalizedCosineMoment 0| * |unequalAPowSSTT (α / 2) s t| ≤
        1 * |unequalAPowSSTT (α / 2) s t| := by
      gcongr
      exact abs_normalizedCosineMoment_le_one 0
    _ ≤ 1 * (32768 * angularKernelA s t ^ (α / 2 - 4)) := by
      simpa using h
    _ = _ := by ring

theorem abs_separatedEvenPowerSummandDSSTT_one_le
    {α s t : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |separatedEvenPowerSummandDSSTT α 1 s t| ≤
      8388608 * angularKernelA s t ^ (α / 2 - 4) := by
  let A := angularKernelA s t
  let e := α / 2 - 2
  let U := unequalRadiusPower 1 s
  let U1 := unequalRadiusPowerD1 1 s
  let U2 := unequalRadiusPowerD2 1 s
  let V := unequalRadiusPower 1 t
  let V1 := unequalRadiusPowerD1 1 t
  let V2 := unequalRadiusPowerD2 1 t
  have hu0 : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hv0 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have huA : 1 - s ^ 2 ≤ A := by
    dsimp [A]
    rw [angularKernelA_eq_radiusSq_add]
    nlinarith [hv0, sq_nonneg (s - t)]
  have hvA : 1 - t ^ 2 ≤ A := by
    dsimp [A]
    rw [angularKernelA_eq_radiusSq_add]
    nlinarith [hu0, sq_nonneg (s - t)]
  have hA4 : A ≤ 4 := angularKernelA_le_four_of_mem hs ht
  have hsabs : |s| ≤ 1 := abs_le.2 hs
  have htabs : |t| ≤ 1 := abs_le.2 ht
  have hU : |U| ≤ A := by
    dsimp [U, unequalRadiusPower]
    simp only [pow_one]
    rw [abs_of_nonneg hu0]
    simpa using huA
  have hV : |V| ≤ A := by
    dsimp [V, unequalRadiusPower]
    simp only [pow_one]
    rw [abs_of_nonneg hv0]
    simpa using hvA
  have hU1 : |U1| ≤ 2 := by
    dsimp [U1, unequalRadiusPowerD1]
    norm_num
    change |(2 : ℝ) * s| ≤ 2
    rw [abs_mul]
    norm_num
    exact hsabs
  have hV1 : |V1| ≤ 2 := by
    dsimp [V1, unequalRadiusPowerD1]
    norm_num
    change |(2 : ℝ) * t| ≤ 2
    rw [abs_mul]
    norm_num
    exact htabs
  have hU2 : |U2| ≤ 2 := by
    dsimp [U2, unequalRadiusPowerD2]
    norm_num
  have hV2 : |V2| ≤ 2 := by
    dsimp [V2, unequalRadiusPowerD2]
    norm_num
  have hP0 : |unequalAPow e s t| = A ^ e := abs_unequalAPow_le hA
  have hP1s :
      |unequalAPowS e s t| ≤ 20 * A ^ (e - 1) := by
    convert
      (abs_unequalAPowS_le (α := α) (m := 1)
        hα0 hα2 ht hA) using 1 <;> norm_num [e, A]
  have hP1t :
      |unequalAPowT e s t| ≤ 20 * A ^ (e - 1) := by
    convert
      (abs_unequalAPowT_le (α := α) (m := 1)
        hα0 hα2 hs hA) using 1 <;> norm_num [e, A]
  have hP2ss :
      |unequalAPowSS e s t| ≤ 1024 * A ^ (e - 2) := by
    have hh := abs_unequalAPowSS_le
      (α := α) (m := 1) hα0 hα2 ht hA
    simpa [e, A] using hh.trans (by
      have hp : 0 ≤ A ^ (e - 2) := by positivity
      nlinarith)
  have hP2st :
      |unequalAPowST e s t| ≤ 1024 * A ^ (e - 2) := by
    convert
      (abs_unequalAPowST_le (α := α) (m := 1)
        hα0 hα2 hs ht hA) using 1 <;> norm_num [e, A]
  have hP2tt :
      |unequalAPowTT e s t| ≤ 1024 * A ^ (e - 2) := by
    have hh := abs_unequalAPowTT_le
      (α := α) (m := 1) hα0 hα2 hs hA
    simpa [e, A] using hh.trans (by
      have hp : 0 ≤ A ^ (e - 2) := by positivity
      nlinarith)
  have hP3sst :
      |unequalAPowSST e s t| ≤ 16384 * A ^ (e - 3) := by
    convert
      (abs_unequalAPowSST_le (α := α) (m := 1)
        hα0 hα2 hs ht hA) using 1 <;> norm_num [e, A]
  have hP3stt :
      |unequalAPowSTT e s t| ≤ 16384 * A ^ (e - 3) := by
    convert
      (abs_unequalAPowSTT_le (α := α) (m := 1)
        hα0 hα2 hs ht hA) using 1 <;> norm_num [e, A]
  have hP4 :
      |unequalAPowSSTT e s t| ≤ 524288 * A ^ (e - 4) := by
    convert
      (abs_unequalAPowSSTT_le (α := α) (m := 1)
        hα0 hα2 hs ht hA) using 1 <;> norm_num [e, A]
  have h43 : A ^ (e - 4) * A = A ^ (e - 3) := by
    have hh := rpow_sub_nat_mul_pow (A := A) (e := e - 3) hA 1
    norm_num at hh
    rw [show e - 4 = (e - 3) - (1 : ℝ) by ring]
    exact hh
  have h32 : A ^ (e - 3) * A = A ^ (e - 2) := by
    have hh := rpow_sub_nat_mul_pow (A := A) (e := e - 2) hA 1
    norm_num at hh
    rw [show e - 3 = (e - 2) - (1 : ℝ) by ring]
    exact hh
  have h21 : A ^ (e - 2) * A = A ^ (e - 1) := by
    have hh := rpow_sub_nat_mul_pow (A := A) (e := e - 1) hA 1
    norm_num at hh
    rw [show e - 2 = (e - 1) - (1 : ℝ) by ring]
    exact hh
  have h10 : A ^ (e - 1) * A = A ^ e := by
    simpa using rpow_sub_nat_mul_pow (A := A) (e := e) hA 1
  have he1 : A ^ (e - 1) ≤ 4 * A ^ (e - 2) := by
    rw [← h21]
    calc
      A ^ (e - 2) * A ≤ A ^ (e - 2) * 4 :=
        mul_le_mul_of_nonneg_left hA4 (by positivity)
      _ = 4 * A ^ (e - 2) := by ring
  have he0 : A ^ e ≤ 16 * A ^ (e - 2) := by
    rw [← h10, ← h21]
    have hA2 : A ^ 2 ≤ 16 := by
      convert pow_le_pow_left₀ hA.le hA4 2 using 1 ; norm_num
    nlinarith [hA2, show 0 ≤ A ^ (e - 2) by positivity]
  let X :=
    unequalAPowSS e s t * U + 2 * unequalAPowS e s t * U1 +
      unequalAPow e s t * U2
  let XT :=
    unequalAPowSST e s t * U + 2 * unequalAPowST e s t * U1 +
      unequalAPowT e s t * U2
  let XTT :=
    unequalAPowSSTT e s t * U + 2 * unequalAPowSTT e s t * U1 +
      unequalAPowTT e s t * U2
  have hX : |X| ≤ 2048 * A ^ (e - 1) := by
    dsimp [X]
    calc
      |_ + _ + _| ≤
          |unequalAPowSS e s t| * |U| +
          2 * |unequalAPowS e s t| * |U1| +
          |unequalAPow e s t| * |U2| := by
        simpa [abs_mul] using
          (abs_add
            (unequalAPowSS e s t * U +
              2 * unequalAPowS e s t * U1)
            (unequalAPow e s t * U2)).trans
            (add_le_add_right
              (abs_add (unequalAPowSS e s t * U)
                (2 * unequalAPowS e s t * U1)) _)
      _ ≤ 1024 * A ^ (e - 2) * A +
          2 * (20 * A ^ (e - 1)) * 2 + A ^ e * 2 := by
        rw [hP0]
        gcongr
      _ ≤ 2048 * A ^ (e - 1) := by
        have hfirst :
            1024 * A ^ (e - 2) * A = 1024 * A ^ (e - 1) := by
          calc
            1024 * A ^ (e - 2) * A =
                1024 * (A ^ (e - 2) * A) := by ring
            _ = 1024 * A ^ (e - 1) := by rw [h21]
        rw [hfirst]
        have hp : 0 ≤ A ^ (e - 1) := by positivity
        nlinarith [he0]
  have hXT : |XT| ≤ 32768 * A ^ (e - 2) := by
    dsimp [XT]
    calc
      |_ + _ + _| ≤
          |unequalAPowSST e s t| * |U| +
          2 * |unequalAPowST e s t| * |U1| +
          |unequalAPowT e s t| * |U2| := by
        simpa [abs_mul] using
          (abs_add
            (unequalAPowSST e s t * U +
              2 * unequalAPowST e s t * U1)
            (unequalAPowT e s t * U2)).trans
            (add_le_add_right
              (abs_add (unequalAPowSST e s t * U)
                (2 * unequalAPowST e s t * U1)) _)
      _ ≤ 16384 * A ^ (e - 3) * A +
          2 * (1024 * A ^ (e - 2)) * 2 +
          20 * A ^ (e - 1) * 2 := by gcongr
      _ ≤ 32768 * A ^ (e - 2) := by
        have hfirst :
            16384 * A ^ (e - 3) * A = 16384 * A ^ (e - 2) := by
          calc
            16384 * A ^ (e - 3) * A =
                16384 * (A ^ (e - 3) * A) := by ring
            _ = 16384 * A ^ (e - 2) := by rw [h32]
        rw [hfirst]
        have hp : 0 ≤ A ^ (e - 2) := by positivity
        nlinarith [he1]
  have hXTT : |XTT| ≤ 1048576 * A ^ (e - 3) := by
    dsimp [XTT]
    calc
      |_ + _ + _| ≤
          |unequalAPowSSTT e s t| * |U| +
          2 * |unequalAPowSTT e s t| * |U1| +
          |unequalAPowTT e s t| * |U2| := by
        simpa [abs_mul] using
          (abs_add
            (unequalAPowSSTT e s t * U +
              2 * unequalAPowSTT e s t * U1)
            (unequalAPowTT e s t * U2)).trans
            (add_le_add_right
              (abs_add (unequalAPowSSTT e s t * U)
                (2 * unequalAPowSTT e s t * U1)) _)
      _ ≤ 524288 * A ^ (e - 4) * A +
          2 * (16384 * A ^ (e - 3)) * 2 +
          1024 * A ^ (e - 2) * 2 := by gcongr
      _ ≤ 1048576 * A ^ (e - 3) := by
        have hfirst :
            524288 * A ^ (e - 4) * A =
              524288 * A ^ (e - 3) := by
          calc
            524288 * A ^ (e - 4) * A =
                524288 * (A ^ (e - 4) * A) := by ring
            _ = 524288 * A ^ (e - 3) := by rw [h43]
        rw [hfirst]
        have hp : 0 ≤ A ^ (e - 3) := by positivity
        have hh : A ^ (e - 2) ≤ 4 * A ^ (e - 3) := by
          rw [← h32]
          calc
            A ^ (e - 3) * A ≤ A ^ (e - 3) * 4 :=
              mul_le_mul_of_nonneg_left hA4 (by positivity)
            _ = 4 * A ^ (e - 3) := by ring
        nlinarith
  have hfinal :
      |4 * (XTT * V + 2 * XT * V1 + X * V2)| ≤
        8388608 * A ^ (e - 2) := by
    calc
    |4 * (XTT * V + 2 * XT * V1 + X * V2)| ≤
        4 * (|XTT| * |V| + 2 * |XT| * |V1| + |X| * |V2|) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      gcongr
      simpa [abs_mul] using
        (abs_add (XTT * V + 2 * XT * V1) (X * V2)).trans
          (add_le_add_right (abs_add (XTT * V) (2 * XT * V1)) _)
    _ ≤ 4 * (1048576 * A ^ (e - 3) * A +
        2 * (32768 * A ^ (e - 2)) * 2 +
        2048 * A ^ (e - 1) * 2) := by gcongr
    _ ≤ 8388608 * A ^ (e - 2) := by
      have hfirst :
          1048576 * A ^ (e - 3) * A =
            1048576 * A ^ (e - 2) := by
        calc
          1048576 * A ^ (e - 3) * A =
              1048576 * (A ^ (e - 3) * A) := by ring
          _ = 1048576 * A ^ (e - 2) := by rw [h32]
      rw [hfirst]
      have hp : 0 ≤ A ^ (e - 2) := by positivity
      nlinarith [he1]
  convert hfinal using 1
  · simp [separatedEvenPowerSummandDSSTT, X, XT, XTT,
      U, U1, U2, V, V1, V2, e]
  · dsimp [A, e]
    ring_nf

theorem abs_separatedEvenPowerDSSTTSeriesTerm_one_le
    {α s t : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |separatedEvenPowerDSSTTSeriesTerm α 1 s t| ≤
      (8388608 * |Ring.choose (α / 2) 2|) *
        angularKernelA s t ^ (α / 2 - 4) := by
  have h :=
    abs_separatedEvenPowerSummandDSSTT_one_le
      hα0 hα2 hs ht hA
  unfold separatedEvenPowerDSSTTSeriesTerm
  rw [abs_mul, abs_mul]
  calc
    |Ring.choose (α / 2) 2| * |normalizedCosineMoment 2| *
        |separatedEvenPowerSummandDSSTT α 1 s t| ≤
      |Ring.choose (α / 2) 2| * 1 *
        (8388608 * angularKernelA s t ^ (α / 2 - 4)) := by
      gcongr
      exact abs_normalizedCosineMoment_le_one 2
    _ = _ := by ring


noncomputable def separatedEvenPowerSummandDST
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  let e := α / 2 - 2 * (m : ℝ)
  let Y :=
    unequalAPowS e s t * unequalRadiusPower m s +
      unequalAPow e s t * unequalRadiusPowerD1 m s
  let YT :=
    unequalAPowST e s t * unequalRadiusPower m s +
      unequalAPowT e s t * unequalRadiusPowerD1 m s
  (4 : ℝ) ^ m *
    (YT * unequalRadiusPower m t + Y * unequalRadiusPowerD1 m t)

theorem abs_separatedEvenPower_lowerDerivatives_le
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {s t q : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hApos : 0 < angularKernelA s t)
    (hq : separatedRatio s t ≤ q)
    {m : ℕ} (hm : 2 ≤ m) :
    let R := 4194304 * ((m : ℝ) + 1) ^ (4 : ℕ) *
      angularKernelA s t ^ (α / 2 - 4) * q ^ (m - 2)
    |separatedEvenPowerSummandDS α m s t| ≤ R ∧
      |separatedEvenPowerSummandDSS α m s t| ≤ R ∧
      |separatedEvenPowerSummandDSST α m s t| ≤ R ∧
      |separatedEvenPowerSummandDST α m s t| ≤ R := by
  let A := angularKernelA s t
  let u := 1 - s ^ 2
  let v := 1 - t ^ 2
  let e := α / 2 - 2 * (m : ℝ)
  let w := (m : ℝ) + 1
  have hsSphere := hs
  have htSphere := ht
  have hA : 0 < A := hApos
  have hq0 : 0 ≤ q := (separatedRatio_nonneg hs ht).trans hq
  have hu0 : 0 ≤ u := by
    dsimp [u]
    nlinarith [hsSphere.1, hsSphere.2]
  have hv0 : 0 ≤ v := by
    dsimp [v]
    nlinarith [htSphere.1, htSphere.2]
  have huA : u ≤ A := by
    dsimp [u, A]
    rw [angularKernelA_eq_radiusSq_add]
    nlinarith [show 0 ≤ 1 - t ^ 2 by
      nlinarith [htSphere.1, htSphere.2], sq_nonneg (s - t)]
  have hvA : v ≤ A := by
    dsimp [v, A]
    rw [angularKernelA_eq_radiusSq_add]
    nlinarith [show 0 ≤ 1 - s ^ 2 by
      nlinarith [hsSphere.1, hsSphere.2], sq_nonneg (s - t)]
  have hA4 : A ≤ 4 := angularKernelA_le_four_of_mem hsSphere htSphere
  have hw : 1 ≤ w := by
    dsimp [w]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hP0 : |unequalAPow e s t| = A ^ e :=
    abs_unequalAPow_le hA
  have hP1 :
      |unequalAPowS e s t| ≤ 10 * w * A ^ (e - 1) :=
    abs_unequalAPowS_le hα0 hα2 htSphere hA
  have hP2 :
      |unequalAPowSS e s t| ≤ 256 * w ^ 2 * A ^ (e - 2) := by
    have hb := abs_unequalAPowSS_le
      (α := α) (m := m) hα0 hα2 htSphere hA
    simpa [e, w, A] using hb.trans (by
      have hp : 0 ≤ ((m : ℝ) + 1) ^ 2 *
          angularKernelA s t ^ (α / 2 - 2 * (m : ℝ) - 2) := by positivity
      nlinarith)
  have hP2st :
      |unequalAPowST e s t| ≤ 256 * w ^ 2 * A ^ (e - 2) :=
    abs_unequalAPowST_le hα0 hα2 hsSphere htSphere hA
  have hP3 :
      |unequalAPowSST e s t| ≤ 2048 * w ^ 3 * A ^ (e - 3) :=
    abs_unequalAPowSST_le hα0 hα2 hsSphere htSphere hA
  have hU0 : |unequalRadiusPower m s| ≤ A ^ 2 * u ^ (m - 2) :=
    abs_unequalRadiusPower_le hm hsSphere huA
  have hU1 : |unequalRadiusPowerD1 m s| ≤
      2 * w * A * u ^ (m - 2) :=
    abs_unequalRadiusPowerD1_le hm hsSphere huA
  have hU2 : |unequalRadiusPowerD2 m s| ≤
      16 * w ^ 2 * u ^ (m - 2) :=
    abs_unequalRadiusPowerD2_le hm hsSphere huA hA4
  have hV0 : |unequalRadiusPower m t| ≤ A ^ 2 * v ^ (m - 2) :=
    abs_unequalRadiusPower_le hm htSphere hvA
  have hV1 : |unequalRadiusPowerD1 m t| ≤
      2 * w * A * v ^ (m - 2) :=
    abs_unequalRadiusPowerD1_le hm htSphere hvA
  have hAe21 : A ^ (e - 2) * A ^ 2 = A ^ e :=
    rpow_sub_nat_mul_pow hA 2
  have hAe11 : A ^ (e - 1) * A = A ^ e := by
    simpa using rpow_sub_nat_mul_pow hA 1
  have hAe32 : A ^ (e - 3) * A ^ 2 = A ^ (e - 1) := by
    have hh := rpow_sub_nat_mul_pow (A := A) (e := e - 1) hA 2
    rw [show e - 3 = (e - 1) - (2 : ℝ) by ring]
    exact hh
  have hAe21' : A ^ (e - 2) * A = A ^ (e - 1) := by
    have hh := rpow_sub_nat_mul_pow (A := A) (e := e - 1) hA 1
    rw [show e - 2 = (e - 1) - (1 : ℝ) by ring]
    simpa using hh
  let X :=
    unequalAPowSS e s t * unequalRadiusPower m s +
      2 * unequalAPowS e s t * unequalRadiusPowerD1 m s +
      unequalAPow e s t * unequalRadiusPowerD2 m s
  let XT :=
    unequalAPowSST e s t * unequalRadiusPower m s +
      2 * unequalAPowST e s t * unequalRadiusPowerD1 m s +
      unequalAPowT e s t * unequalRadiusPowerD2 m s
  have hX : |X| ≤ 1024 * w ^ 2 * A ^ e * u ^ (m - 2) := by
    dsimp only [X]
    calc
      |_ + _ + _| ≤
          |unequalAPowSS e s t| * |unequalRadiusPower m s| +
          2 * |unequalAPowS e s t| * |unequalRadiusPowerD1 m s| +
          |unequalAPow e s t| * |unequalRadiusPowerD2 m s| := by
        simpa [abs_mul] using
          (abs_add
            (unequalAPowSS e s t * unequalRadiusPower m s +
              2 * unequalAPowS e s t * unequalRadiusPowerD1 m s)
            (unequalAPow e s t * unequalRadiusPowerD2 m s)).trans
            (add_le_add_right
              (abs_add
                (unequalAPowSS e s t * unequalRadiusPower m s)
                (2 * unequalAPowS e s t * unequalRadiusPowerD1 m s)) _)
      _ ≤
          (256 * w ^ 2 * A ^ (e - 2)) * (A ^ 2 * u ^ (m - 2)) +
          2 * (10 * w * A ^ (e - 1)) *
            (2 * w * A * u ^ (m - 2)) +
          A ^ e * (16 * w ^ 2 * u ^ (m - 2)) := by
        have hP0le : |unequalAPow e s t| ≤ A ^ e := hP0.le
        gcongr
      _ = 312 * w ^ 2 * A ^ e * u ^ (m - 2) := by
        calc
          _ = (256 * w ^ 2 * (A ^ (e - 2) * A ^ 2) +
                40 * w ^ 2 * (A ^ (e - 1) * A) +
                16 * w ^ 2 * A ^ e) * u ^ (m - 2) := by ring
          _ = _ := by rw [hAe21, hAe11]; ring
      _ ≤ 1024 * w ^ 2 * A ^ e * u ^ (m - 2) := by
        have hp : 0 ≤ w ^ 2 * A ^ e * u ^ (m - 2) := by positivity
        nlinarith
  have hXT : |XT| ≤ 4096 * w ^ 3 * A ^ (e - 1) * u ^ (m - 2) := by
    dsimp only [XT]
    calc
      |_ + _ + _| ≤
          |unequalAPowSST e s t| * |unequalRadiusPower m s| +
          2 * |unequalAPowST e s t| * |unequalRadiusPowerD1 m s| +
          |unequalAPowT e s t| * |unequalRadiusPowerD2 m s| := by
        simpa [abs_mul] using
          (abs_add
            (unequalAPowSST e s t * unequalRadiusPower m s +
              2 * unequalAPowST e s t * unequalRadiusPowerD1 m s)
            (unequalAPowT e s t * unequalRadiusPowerD2 m s)).trans
            (add_le_add_right
              (abs_add
                (unequalAPowSST e s t * unequalRadiusPower m s)
                (2 * unequalAPowST e s t * unequalRadiusPowerD1 m s)) _)
      _ ≤
          (2048 * w ^ 3 * A ^ (e - 3)) * (A ^ 2 * u ^ (m - 2)) +
          2 * (256 * w ^ 2 * A ^ (e - 2)) *
            (2 * w * A * u ^ (m - 2)) +
          (10 * w * A ^ (e - 1)) *
            (16 * w ^ 2 * u ^ (m - 2)) := by
        have hPt : |unequalAPowT e s t| ≤
            10 * w * A ^ (e - 1) := by
          simpa [e, w, A] using
            (abs_unequalAPowT_le (α := α) (m := m)
              hα0 hα2 hsSphere hA)
        gcongr
      _ = 3232 * w ^ 3 * A ^ (e - 1) * u ^ (m - 2) := by
        calc
          _ = (2048 * w ^ 3 * (A ^ (e - 3) * A ^ 2) +
                1024 * w ^ 3 * (A ^ (e - 2) * A) +
                160 * w ^ 3 * A ^ (e - 1)) * u ^ (m - 2) := by ring
          _ = _ := by rw [hAe32, hAe21']; ring
      _ ≤ 4096 * w ^ 3 * A ^ (e - 1) * u ^ (m - 2) := by
        have hp : 0 ≤ w ^ 3 * A ^ (e - 1) * u ^ (m - 2) := by positivity
        nlinarith
  have hDSCore :
      |unequalAPowS e s t * unequalRadiusPower m s +
          unequalAPow e s t * unequalRadiusPowerD1 m s| ≤
        16 * w * A ^ (e + 1) * u ^ (m - 2) := by
    calc
      |_ + _| ≤ |unequalAPowS e s t| * |unequalRadiusPower m s| +
          |unequalAPow e s t| * |unequalRadiusPowerD1 m s| := by
        simpa [abs_mul] using abs_add
          (unequalAPowS e s t * unequalRadiusPower m s)
          (unequalAPow e s t * unequalRadiusPowerD1 m s)
      _ ≤ (10 * w * A ^ (e - 1)) * (A ^ 2 * u ^ (m - 2)) +
          A ^ e * (2 * w * A * u ^ (m - 2)) := by
        have hP0le : |unequalAPow e s t| ≤ A ^ e := hP0.le
        gcongr
      _ = 12 * w * A ^ (e + 1) * u ^ (m - 2) := by
        have h1 : A ^ (e - 1) * A ^ 2 = A ^ (e + 1) := by
          have hh := rpow_sub_nat_mul_pow (A := A) (e := e + 1) hA 2
          rw [show e - 1 = (e + 1) - (2 : ℝ) by ring]
          exact hh
        have h2 : A ^ e * A = A ^ (e + 1) := by
          have hh := Real.rpow_add hA e 1
          rw [Real.rpow_one] at hh
          exact hh.symm
        calc
          _ = (10 * w * (A ^ (e - 1) * A ^ 2) +
                2 * w * (A ^ e * A)) * u ^ (m - 2) := by ring
          _ = _ := by rw [h1, h2]; ring
      _ ≤ 16 * w * A ^ (e + 1) * u ^ (m - 2) := by
        have hp : 0 ≤ w * A ^ (e + 1) * u ^ (m - 2) := by positivity
        nlinarith
  let YT :=
    unequalAPowST e s t * unequalRadiusPower m s +
      unequalAPowT e s t * unequalRadiusPowerD1 m s
  have hYT :
      |YT| ≤ 512 * w ^ 2 * A ^ e * u ^ (m - 2) := by
    dsimp only [YT]
    have hPt : |unequalAPowT e s t| ≤
        10 * w * A ^ (e - 1) := by
      simpa [e, w, A] using
        (abs_unequalAPowT_le (α := α) (m := m)
          hα0 hα2 hsSphere hA)
    calc
      |_ + _| ≤
          |unequalAPowST e s t| * |unequalRadiusPower m s| +
            |unequalAPowT e s t| * |unequalRadiusPowerD1 m s| := by
        simpa [abs_mul] using abs_add
          (unequalAPowST e s t * unequalRadiusPower m s)
          (unequalAPowT e s t * unequalRadiusPowerD1 m s)
      _ ≤
          (256 * w ^ 2 * A ^ (e - 2)) *
              (A ^ 2 * u ^ (m - 2)) +
            (10 * w * A ^ (e - 1)) *
              (2 * w * A * u ^ (m - 2)) := by
        gcongr
      _ = 276 * w ^ 2 * A ^ e * u ^ (m - 2) := by
        calc
          _ = (256 * w ^ 2 * (A ^ (e - 2) * A ^ 2) +
              20 * w ^ 2 * (A ^ (e - 1) * A)) *
                u ^ (m - 2) := by ring
          _ = _ := by rw [hAe21, hAe11]; ring
      _ ≤ 512 * w ^ 2 * A ^ e * u ^ (m - 2) := by
        have hp : 0 ≤ w ^ 2 * A ^ e * u ^ (m - 2) := by positivity
        nlinarith
  have hcommon :=
    latitude_common_factor_eq (α := α) (A := A) (u := u) (v := v)
      hA m hm
  have hQ := hq
  have hQ0 := separatedRatio_nonneg hsSphere htSphere
  have hqpow : separatedRatio s t ^ (m - 2) ≤
      q ^ (m - 2) :=
    pow_le_pow_left₀ hQ0 hQ _
  have hbase :
      (4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) * A ^ e ≤
        16 * A ^ (α / 2 - 4) * q ^ (m - 2) := by
    rw [hcommon]
    change 16 * A ^ (α / 2 - 4) *
      separatedRatio s t ^ (m - 2) ≤ _
    exact mul_le_mul_of_nonneg_left hqpow (by positivity)
  have hA2 : A ^ 2 ≤ 16 := by
    convert pow_le_pow_left₀ hA.le hA4 2 using 1 ; norm_num
  have hA3 : A ^ 3 ≤ 64 := by
    convert pow_le_pow_left₀ hA.le hA4 3 using 1 ; norm_num
  have hAe1 : A ^ (e + 1) = A ^ e * A := by
    simpa [Real.rpow_one] using Real.rpow_add hA e 1
  have hw14 : w ≤ w ^ 4 := by
    simpa using (pow_le_pow_right₀ hw (show 1 ≤ 4 by omega))
  have hw24 : w ^ 2 ≤ w ^ 4 := by
    exact pow_le_pow_right₀ hw (by omega)
  have hw34 : w ^ 3 ≤ w ^ 4 := by
    exact pow_le_pow_right₀ hw (by omega)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold separatedEvenPowerSummandDS
    dsimp only
    calc
      |(4 : ℝ) ^ m * _ * unequalRadiusPower m t| ≤
          (4 : ℝ) ^ m *
            (16 * w * A ^ (e + 1) * u ^ (m - 2)) *
            (A ^ 2 * v ^ (m - 2)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (by norm_num) m)]
        gcongr
      _ = 16 * w * A ^ 3 *
          ((4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) * A ^ e) := by
        rw [hAe1]
        ring
      _ ≤ 16 * w * A ^ 3 *
          (16 * A ^ (α / 2 - 4) * q ^ (m - 2)) := by
        gcongr
      _ ≤ 4194304 * w ^ 4 * A ^ (α / 2 - 4) *
          q ^ (m - 2) := by
        let P := A ^ (α / 2 - 4) * q ^ (m - 2)
        have hP : 0 ≤ P := by positivity
        have hcoef : 256 * w * A ^ 3 ≤ 4194304 * w ^ 4 := by
          calc
            256 * w * A ^ 3 ≤ 256 * w * 64 := by gcongr
            _ = 16384 * w := by ring
            _ ≤ 16384 * w ^ 4 :=
              mul_le_mul_of_nonneg_left hw14 (by norm_num)
            _ ≤ 4194304 * w ^ 4 :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        have hmul := mul_le_mul_of_nonneg_right hcoef hP
        dsimp [P] at hmul
        convert hmul using 1 <;> ring
  · unfold separatedEvenPowerSummandDSS
    dsimp only
    change |(4 : ℝ) ^ m * X * unequalRadiusPower m t| ≤ _
    calc
      |(4 : ℝ) ^ m * X * unequalRadiusPower m t| ≤
          (4 : ℝ) ^ m *
            (1024 * w ^ 2 * A ^ e * u ^ (m - 2)) *
            (A ^ 2 * v ^ (m - 2)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (by norm_num) m)]
        gcongr
      _ = 1024 * w ^ 2 * A ^ 2 *
          ((4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) * A ^ e) := by ring
      _ ≤ 1024 * w ^ 2 * A ^ 2 *
          (16 * A ^ (α / 2 - 4) * q ^ (m - 2)) := by
        gcongr
      _ ≤ 4194304 * w ^ 4 * A ^ (α / 2 - 4) *
          q ^ (m - 2) := by
        let P := A ^ (α / 2 - 4) * q ^ (m - 2)
        have hP : 0 ≤ P := by positivity
        have hcoef : 16384 * w ^ 2 * A ^ 2 ≤ 4194304 * w ^ 4 := by
          calc
            16384 * w ^ 2 * A ^ 2 ≤
                16384 * w ^ 2 * 16 := by gcongr
            _ = 262144 * w ^ 2 := by ring
            _ ≤ 262144 * w ^ 4 :=
              mul_le_mul_of_nonneg_left hw24 (by norm_num)
            _ ≤ 4194304 * w ^ 4 :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        have hmul := mul_le_mul_of_nonneg_right hcoef hP
        dsimp [P] at hmul
        convert hmul using 1 <;> ring
  · unfold separatedEvenPowerSummandDSST
    dsimp only
    change |(4 : ℝ) ^ m *
      (XT * unequalRadiusPower m t + X * unequalRadiusPowerD1 m t)| ≤ _
    calc
      |(4 : ℝ) ^ m * (XT * unequalRadiusPower m t +
          X * unequalRadiusPowerD1 m t)| ≤
        (4 : ℝ) ^ m *
          ((4096 * w ^ 3 * A ^ (e - 1) * u ^ (m - 2)) *
              (A ^ 2 * v ^ (m - 2)) +
            (1024 * w ^ 2 * A ^ e * u ^ (m - 2)) *
              (2 * w * A * v ^ (m - 2))) := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (by norm_num) m)]
        calc
          (4 : ℝ) ^ m * |XT * unequalRadiusPower m t +
              X * unequalRadiusPowerD1 m t| ≤
            (4 : ℝ) ^ m *
              (|XT| * |unequalRadiusPower m t| +
                |X| * |unequalRadiusPowerD1 m t|) := by
              gcongr
              simpa [abs_mul] using abs_add
                (XT * unequalRadiusPower m t)
                (X * unequalRadiusPowerD1 m t)
          _ ≤ _ := by gcongr
      _ = 6144 * w ^ 3 * A *
          ((4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) * A ^ e) := by
        have h13 : A ^ (e - 1) * A ^ 2 = A ^ (e + 1) := by
          have hh := rpow_sub_nat_mul_pow (A := A) (e := e + 1) hA 2
          rw [show e - 1 = (e + 1) - (2 : ℝ) by ring]
          exact hh
        calc
          _ = (4096 * w ^ 3 * (A ^ (e - 1) * A ^ 2) +
                2048 * w ^ 3 * (A ^ e * A)) *
              (4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) := by ring
          _ = _ := by rw [h13, hAe1]; ring
      _ ≤ 6144 * w ^ 3 * A *
          (16 * A ^ (α / 2 - 4) * q ^ (m - 2)) := by
        gcongr
      _ ≤ 4194304 * w ^ 4 * A ^ (α / 2 - 4) *
          q ^ (m - 2) := by
        let P := A ^ (α / 2 - 4) * q ^ (m - 2)
        have hP : 0 ≤ P := by positivity
        have hcoef : 98304 * w ^ 3 * A ≤ 4194304 * w ^ 4 := by
          calc
            98304 * w ^ 3 * A ≤ 98304 * w ^ 3 * 4 := by gcongr
            _ = 393216 * w ^ 3 := by ring
            _ ≤ 393216 * w ^ 4 :=
              mul_le_mul_of_nonneg_left hw34 (by norm_num)
            _ ≤ 4194304 * w ^ 4 :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        have hmul := mul_le_mul_of_nonneg_right hcoef hP
        dsimp [P] at hmul
        convert hmul using 1 <;> ring
  · unfold separatedEvenPowerSummandDST
    dsimp only
    change |(4 : ℝ) ^ m *
      (YT * unequalRadiusPower m t +
        (unequalAPowS e s t * unequalRadiusPower m s +
          unequalAPow e s t * unequalRadiusPowerD1 m s) *
            unequalRadiusPowerD1 m t)| ≤ _
    calc
      |(4 : ℝ) ^ m * _| ≤
          (4 : ℝ) ^ m *
            ((512 * w ^ 2 * A ^ e * u ^ (m - 2)) *
                (A ^ 2 * v ^ (m - 2)) +
              (16 * w * A ^ (e + 1) * u ^ (m - 2)) *
                (2 * w * A * v ^ (m - 2))) := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (by norm_num) m)]
        calc
          (4 : ℝ) ^ m * |_ + _| ≤
              (4 : ℝ) ^ m *
                (|YT| * |unequalRadiusPower m t| +
                  |unequalAPowS e s t * unequalRadiusPower m s +
                    unequalAPow e s t * unequalRadiusPowerD1 m s| *
                      |unequalRadiusPowerD1 m t|) := by
            gcongr
            simpa [abs_mul] using abs_add
              (YT * unequalRadiusPower m t)
              ((unequalAPowS e s t * unequalRadiusPower m s +
                unequalAPow e s t * unequalRadiusPowerD1 m s) *
                  unequalRadiusPowerD1 m t)
          _ ≤ _ := by gcongr
      _ = 544 * w ^ 2 * A ^ 2 *
          ((4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) * A ^ e) := by
        rw [hAe1]
        ring
      _ ≤ 544 * w ^ 2 * A ^ 2 *
          (16 * A ^ (α / 2 - 4) * q ^ (m - 2)) := by
        gcongr
      _ ≤ 4194304 * w ^ 4 * A ^ (α / 2 - 4) *
          q ^ (m - 2) := by
        let P := A ^ (α / 2 - 4) * q ^ (m - 2)
        have hP : 0 ≤ P := by positivity
        have hcoef : 8704 * w ^ 2 * A ^ 2 ≤ 4194304 * w ^ 4 := by
          calc
            8704 * w ^ 2 * A ^ 2 ≤ 8704 * w ^ 2 * 16 := by gcongr
            _ = 139264 * w ^ 2 := by ring
            _ ≤ 139264 * w ^ 4 :=
              mul_le_mul_of_nonneg_left hw24 (by norm_num)
            _ ≤ 4194304 * w ^ 4 :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        have hmul := mul_le_mul_of_nonneg_right hcoef hP
        dsimp [P] at hmul
        convert hmul using 1 <;> ring


noncomputable def separatedEvenPowerDSSeriesTerm
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  (Ring.choose (α / 2) (2 * m) *
    normalizedCosineMoment (2 * m)) *
    separatedEvenPowerSummandDS α m s t

noncomputable def separatedEvenPowerDSSSeriesTerm
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  (Ring.choose (α / 2) (2 * m) *
    normalizedCosineMoment (2 * m)) *
    separatedEvenPowerSummandDSS α m s t

noncomputable def separatedEvenPowerDSSTSeriesTerm
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  (Ring.choose (α / 2) (2 * m) *
    normalizedCosineMoment (2 * m)) *
    separatedEvenPowerSummandDSST α m s t

/-- The three lower differentiated tails are normally summable on every
left-small rectangle, with the same fourth-degree coefficient majorant as
the final `(2,2)` series. -/
theorem summable_shifted_separatedEvenPower_lowerSeriesTerms
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {s t q : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hU : 0 < angularKernelA s t)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hq : separatedRatio s t ≤ q) :
    Summable (fun r : ℕ ↦
      separatedEvenPowerDSSeriesTerm α (r + 2) s t) ∧
    Summable (fun r : ℕ ↦
      separatedEvenPowerDSSSeriesTerm α (r + 2) s t) ∧
    Summable (fun r : ℕ ↦
      separatedEvenPowerDSSTSeriesTerm α (r + 2) s t) := by
  let c : ℕ → ℝ := fun m ↦
    Ring.choose (α / 2) (2 * m) * normalizedCosineMoment (2 * m)
  let E : ℕ → ℝ := fun r ↦
    4194304 * angularKernelA s t ^ (α / 2 - 4) *
      (evenAngularDerivativeCoefficient α (r + 2) *
        q ^ r)
  have hcoef :=
    summable_shifted_evenAngularDerivativeCoefficient_mul_pow
      α (q := q) hq0 hq1
  have hE : Summable E := by
    dsimp [E]
    exact hcoef.mul_left
      (4194304 * angularKernelA s t ^ (α / 2 - 4))
  have hbound (F : ℕ → ℝ)
      (hF : ∀ r : ℕ,
        |F r| ≤
          4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
            angularKernelA s t ^ (α / 2 - 4) *
            q ^ r) :
      Summable (fun r : ℕ ↦ c (r + 2) * F r) := by
    apply hE.of_norm_bounded
    intro r
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |c (r + 2)| * |F r| ≤
          |c (r + 2)| *
            (4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
              angularKernelA s t ^ (α / 2 - 4) *
              q ^ r) := by
        exact mul_le_mul_of_nonneg_left (hF r) (abs_nonneg _)
      _ = E r := by
        dsimp [c, E, evenAngularDerivativeCoefficient]
        rw [abs_mul]
        ring
  have hlower (r : ℕ) :=
    abs_separatedEvenPower_lowerDerivatives_le
      hα0 hα2 hs ht hU hq (m := r + 2) (by omega)
  have hDS : Summable (fun r : ℕ ↦
      c (r + 2) * separatedEvenPowerSummandDS α (r + 2) s t) := by
    apply hbound
    intro r
    simpa [show r + 2 - 2 = r by omega] using (hlower r).1
  have hDSS : Summable (fun r : ℕ ↦
      c (r + 2) * separatedEvenPowerSummandDSS α (r + 2) s t) := by
    apply hbound
    intro r
    simpa [show r + 2 - 2 = r by omega] using (hlower r).2.1
  have hDSST : Summable (fun r : ℕ ↦
      c (r + 2) * separatedEvenPowerSummandDSST α (r + 2) s t) := by
    apply hbound
    intro r
    simpa [show r + 2 - 2 = r by omega] using (hlower r).2.2.1
  exact ⟨by
    simpa [separatedEvenPowerDSSeriesTerm, c] using hDS, by
    simpa [separatedEvenPowerDSSSeriesTerm, c] using hDSS, by
    simpa [separatedEvenPowerDSSTSeriesTerm, c] using hDSST⟩

theorem abs_separatedEvenPowerSummand_le
    {α s t q : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hApos : 0 < angularKernelA s t)
    (hq : separatedRatio s t ≤ q)
    {m : ℕ} (hm : 2 ≤ m) :
    |separatedEvenPowerSummand α m s t| ≤
      4096 * angularKernelA s t ^ (α / 2 - 4) * q ^ (m - 2) := by
  let A := angularKernelA s t
  let u := 1 - s ^ 2
  let v := 1 - t ^ 2
  let e := α / 2 - 2 * (m : ℝ)
  have hsSphere := hs
  have htSphere := ht
  have hA : 0 < A := hApos
  have hq0 : 0 ≤ q := (separatedRatio_nonneg hs ht).trans hq
  have hu0 : 0 ≤ u := by
    dsimp [u]
    nlinarith [hsSphere.1, hsSphere.2]
  have hv0 : 0 ≤ v := by
    dsimp [v]
    nlinarith [htSphere.1, htSphere.2]
  have huA : u ≤ A := by
    dsimp [u, A]
    rw [angularKernelA_eq_radiusSq_add]
    nlinarith [show 0 ≤ 1 - t ^ 2 by
      nlinarith [htSphere.1, htSphere.2], sq_nonneg (s - t)]
  have hvA : v ≤ A := by
    dsimp [v, A]
    rw [angularKernelA_eq_radiusSq_add]
    nlinarith [show 0 ≤ 1 - s ^ 2 by
      nlinarith [hsSphere.1, hsSphere.2], sq_nonneg (s - t)]
  have hA4 : A ≤ 4 := angularKernelA_le_four_of_mem hsSphere htSphere
  have hcommon := latitude_common_factor_eq
    (α := α) (A := A) (u := u) (v := v) hA m hm
  have hQ := hq
  have hQ0 : 0 ≤ separatedRatio s t :=
    separatedRatio_nonneg hsSphere htSphere
  have hqpow :
      separatedRatio s t ^ (m - 2) ≤
        q ^ (m - 2) :=
    pow_le_pow_left₀ hQ0 hQ _
  have hbase :
      (4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) * A ^ e ≤
        16 * A ^ (α / 2 - 4) * q ^ (m - 2) := by
    rw [hcommon]
    change 16 * A ^ (α / 2 - 4) *
      separatedRatio s t ^ (m - 2) ≤ _
    exact mul_le_mul_of_nonneg_left hqpow (by positivity)
  have hu2 : u ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hu0 huA 2
  have hv2 : v ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hv0 hvA 2
  have hA4pow : A ^ 4 ≤ 256 := by
    convert pow_le_pow_left₀ hA.le hA4 4 using 1 ; norm_num
  have huv : u ^ 2 * v ^ 2 ≤ A ^ 4 := by
    calc
      u ^ 2 * v ^ 2 ≤ A ^ 2 * A ^ 2 := by gcongr
      _ = A ^ 4 := by ring
  have hfactor :
      |separatedEvenPowerSummand α m s t| =
        ((4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) * A ^ e) *
          (u ^ 2 * v ^ 2) := by
    have hum : u ^ m = u ^ (m - 2) * u ^ 2 := by
      calc
        u ^ m = u ^ ((m - 2) + 2) := by congr 1 ; omega
        _ = u ^ (m - 2) * u ^ 2 := pow_add _ _ _
    have hvm : v ^ m = v ^ (m - 2) * v ^ 2 := by
      calc
        v ^ m = v ^ ((m - 2) + 2) := by congr 1 ; omega
        _ = v ^ (m - 2) * v ^ 2 := pow_add _ _ _
    have hfourm : (4 : ℝ) ^ m = (4 : ℝ) ^ (m - 2) * 16 := by
      calc
        (4 : ℝ) ^ m = 4 ^ ((m - 2) + 2) := by congr 1 ; omega
        _ = 4 ^ (m - 2) * 4 ^ 2 := pow_add _ _ _
        _ = 4 ^ (m - 2) * 16 := by norm_num
    change |A ^ e * (4 : ℝ) ^ m * u ^ m * v ^ m| = _
    rw [abs_of_nonneg (by positivity)]
    rw [hum, hvm, hfourm]
    ring
  rw [hfactor]
  calc
    ((4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) * A ^ e) *
        (u ^ 2 * v ^ 2) ≤
      (16 * A ^ (α / 2 - 4) * q ^ (m - 2)) *
        A ^ 4 := by
      exact mul_le_mul hbase huv (by positivity) (by positivity)
    _ ≤
      (16 * A ^ (α / 2 - 4) * q ^ (m - 2)) *
        256 := by
      gcongr
    _ = 4096 * angularKernelA s t ^ (α / 2 - 4) *
        q ^ (m - 2) := by
      dsimp [A]
      ring


noncomputable def separatedEvenPowerSeriesTerm
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  (Ring.choose (α / 2) (2 * m) *
    normalizedCosineMoment (2 * m)) *
    separatedEvenPowerSummand α m s t

theorem summable_shifted_separatedEvenPowerSeriesTerm
    {α s t q : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hq : separatedRatio s t ≤ q) :
    Summable (fun r : ℕ ↦
      separatedEvenPowerSeriesTerm α (r + 2) s t) := by
  have hcoef :=
    summable_shifted_evenAngularDerivativeCoefficient_mul_pow
      α (q := q) hq0 hq1
  have hmaj := hcoef.mul_left
    (4096 * angularKernelA s t ^ (α / 2 - 4))
  apply hmaj.of_norm_bounded
  intro r
  have hterm :=
    abs_separatedEvenPowerSummand_le
      (α := α) hs ht hA hq (m := r + 2) (by omega)
  rw [show r + 2 - 2 = r by omega] at hterm
  unfold separatedEvenPowerSeriesTerm
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |Ring.choose (α / 2) (2 * (r + 2)) *
        normalizedCosineMoment (2 * (r + 2))| *
        |separatedEvenPowerSummand α (r + 2) s t| ≤
      |Ring.choose (α / 2) (2 * (r + 2)) *
        normalizedCosineMoment (2 * (r + 2))| *
        (4096 * angularKernelA s t ^ (α / 2 - 4) *
          q ^ r) :=
      mul_le_mul_of_nonneg_left hterm (abs_nonneg _)
    _ ≤
      4096 * angularKernelA s t ^ (α / 2 - 4) *
        (evenAngularDerivativeCoefficient α (r + 2) *
          q ^ r) := by
      unfold evenAngularDerivativeCoefficient
      rw [abs_mul]
      have hw : (1 : ℝ) ≤ (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) := by
        apply one_le_pow₀
        have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        norm_num
        linarith
      have hc : 0 ≤
          |Ring.choose (α / 2) (2 * (r + 2))| *
            |normalizedCosineMoment (2 * (r + 2))| := by positivity
      have hqpow : 0 ≤ q ^ r := pow_nonneg hq0 _
      have hpow : 0 ≤ angularKernelA s t ^ (α / 2 - 4) :=
        Real.rpow_nonneg hA.le _
      let C := |Ring.choose (α / 2) (2 * (r + 2))| *
        |normalizedCosineMoment (2 * (r + 2))|
      let P := 4096 * angularKernelA s t ^ (α / 2 - 4) *
        q ^ r
      have hC : 0 ≤ C := by simpa [C] using hc
      have hP : 0 ≤ P := by dsimp [P]; positivity
      have hCw :
          C ≤ C * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) := by
        simpa using mul_le_mul_of_nonneg_left hw hC
      calc
        C * P ≤
            (C * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ)) * P := by
          exact mul_le_mul_of_nonneg_right hCw hP
        _ = 4096 * angularKernelA s t ^ (α / 2 - 4) *
            (C * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
              q ^ r) := by ring


noncomputable def separatedLatitudeTailMajorant
    (α L q : ℝ) (r : ℕ) : ℝ :=
  4194304 * L ^ (α / 2 - 4) *
    (evenAngularDerivativeCoefficient α (r + 2) *
      q ^ r)

theorem summable_separatedLatitudeTailMajorant
    (α L q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (separatedLatitudeTailMajorant α L q) := by
  exact
    (summable_shifted_evenAngularDerivativeCoefficient_mul_pow
      α (q := q) hq0 hq1).mul_left
        (4194304 * L ^ (α / 2 - 4))

/-- Uniform normal majorants for all four differentiated stages.  Unlike
the pointwise estimates above, this bound is independent of `s,t` inside
the fixed rectangle, so it is suitable for the termwise derivative
theorem. -/
theorem norm_separatedEvenPower_tailStages_le_majorant
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {a b c d L q : ℝ}
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    {s t : ℝ}
    (hs : s ∈ Icc a b)
    (ht : t ∈ Icc c d)
    (r : ℕ) :
    ‖separatedEvenPowerDSSeriesTerm α (r + 2) s t‖ ≤
        separatedLatitudeTailMajorant α L q r ∧
    ‖separatedEvenPowerDSSSeriesTerm α (r + 2) s t‖ ≤
        separatedLatitudeTailMajorant α L q r ∧
    ‖separatedEvenPowerDSSTSeriesTerm α (r + 2) s t‖ ≤
        separatedLatitudeTailMajorant α L q r ∧
    ‖separatedEvenPowerDSSTTSeriesTerm α (r + 2) s t‖ ≤
        separatedLatitudeTailMajorant α L q r := by
  have hLA : L ≤ angularKernelA s t := hgeo.base_le s hs t ht
  have hγ : α / 2 - 4 ≤ 0 := by linarith
  have hpow :
      angularKernelA s t ^ (α / 2 - 4) ≤ L ^ (α / 2 - 4) :=
    Real.rpow_le_rpow_of_nonpos hgeo.base_pos hLA hγ
  have hlower :=
    abs_separatedEvenPower_lowerDerivatives_le
      hα0 hα2 (hgeo.left_mem s hs) (hgeo.right_mem t ht)
      (hgeo.base_pos.trans_le (hgeo.base_le s hs t ht))
      (hgeo.ratio_le s hs t ht) (m := r + 2) (by omega)
  have hfourth :=
    abs_separatedEvenPowerSummandDSSTT_le
      hα0 hα2 (hgeo.left_mem s hs) (hgeo.right_mem t ht)
      (hgeo.base_pos.trans_le (hgeo.base_le s hs t ht))
      (hgeo.ratio_le s hs t ht) (m := r + 2) (by omega)
  rw [show r + 2 - 2 = r by omega] at hlower hfourth
  have hqpow : 0 ≤ q ^ r := pow_nonneg hgeo.ratio_nonneg _
  let c : ℝ :=
    Ring.choose (α / 2) (2 * (r + 2)) *
      normalizedCosineMoment (2 * (r + 2))
  have hstage (F : ℝ)
      (hF : |F| ≤
        4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
          angularKernelA s t ^ (α / 2 - 4) *
          q ^ r) :
      ‖c * F‖ ≤ separatedLatitudeTailMajorant α L q r := by
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |c| * |F| ≤
          |c| *
            (4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
              angularKernelA s t ^ (α / 2 - 4) *
              q ^ r) :=
        mul_le_mul_of_nonneg_left hF (abs_nonneg _)
      _ ≤ |c| *
            (4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
              L ^ (α / 2 - 4) *
              q ^ r) := by
        gcongr
      _ = separatedLatitudeTailMajorant α L q r := by
        dsimp [c, separatedLatitudeTailMajorant,
          evenAngularDerivativeCoefficient]
        rw [abs_mul]
        ring
  exact ⟨by
    simpa [separatedEvenPowerDSSeriesTerm, c] using
      hstage _ hlower.1, by
    simpa [separatedEvenPowerDSSSeriesTerm, c] using
      hstage _ hlower.2.1, by
    simpa [separatedEvenPowerDSSTSeriesTerm, c] using
      hstage _ hlower.2.2.1, by
    simpa [separatedEvenPowerDSSTTSeriesTerm, c] using
      hstage _ hfourth⟩

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
