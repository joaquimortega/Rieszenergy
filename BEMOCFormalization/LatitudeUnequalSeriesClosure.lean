import BEMOCFormalization.LatitudeAngularExpansion
import BEMOCFormalization.LatitudeUnequalPeanoBridge

/-!
# Normal convergence of the differentiated unequal-latitude series

This module packages the coefficient side of the termwise `(2,2)`
differentiation in (5.6).  The geometric factor is the squared angular
ratio `Q=(B/A)²`; the generalized binomial coefficient is sampled at the
even indices.  Four derivatives cost only a fourth-degree polynomial.
-/

open Set

namespace BEMOC

set_option maxHeartbeats 800000

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

/-- The base and angular-ratio part of the closed-rectangle geometry needed
by the four-pass even-series argument.  This weaker package deliberately
does not exclude polar endpoints: after angular averaging all even powers
are polynomial in the squared radii, so the normally convergent series and
its differentiated series remain meaningful when one radius vanishes. -/
structure LatitudeEvenPowerSeriesBaseGeometry
    (N : ℕ) (j k : Fin (bandTailCount N + 1)) (L : ℝ) : Prop where
  base_pos : 0 < L
  base_le : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j),
    ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k),
      L ≤ angularKernelA s t
  ratio_le : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j),
    ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k),
      unequalAngularRatio s t ≤ (15 : ℝ) / 16

/-- The stronger geometry used when identifying the differentiated even
series with the off-pole height-chart derivative of the original kernel. -/
structure LatitudeEvenPowerSeriesRectangleGeometry
    (N : ℕ) (j k : Fin (bandTailCount N + 1)) (L : ℝ) : Prop
    extends LatitudeEvenPowerSeriesBaseGeometry N j k L where
  interior_offDiagonal : ∀ s ∈ Icc
      (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j),
    ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k),
      s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧ s ≠ t

instance {N : ℕ} {j k : Fin (bandTailCount N + 1)} {L : ℝ} :
    Coe (LatitudeEvenPowerSeriesRectangleGeometry N j k L)
      (LatitudeEvenPowerSeriesBaseGeometry N j k L) :=
  ⟨LatitudeEvenPowerSeriesRectangleGeometry.toLatitudeEvenPowerSeriesBaseGeometry⟩

/-- The original unequal same-hemisphere geometry supplies the abstract
series rectangle with its sharp large-radius base. -/
theorem leftSmallSame_evenPowerSeriesRectangleGeometry
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : LeftSmallSameLatitudePair N j k) :
    LatitudeEvenPowerSeriesRectangleGeometry N j k
      (2 * (latitudeBandScale N k : ℝ) ^ 2 / N) where
  base_pos := by
    have hd : (0 : ℝ) < latitudeBandScale N k := by
      exact_mod_cast latitudeBandScale_pos N k
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  base_le s hs t ht :=
    (leftSmallSame_rectangle_angularKernelA_bounds
      hN j k hjk hs ht).2.1
  ratio_le s hs t ht :=
    leftSmallSame_rectangle_unequalAngularRatio_le hN j k hjk hs ht
  interior_offDiagonal s hs t ht :=
    leftSmallSame_rectangle_interior_offDiagonal hN hjk hs ht

/-- Explicit mode-by-mode `(2,2)` estimate on a left-small rectangle.
The deliberately generous constant absorbs the nine finite Leibniz
contributions, while preserving the sharp fourth-degree mode loss and the
uniform geometric ratio `15/16`. -/
theorem abs_latitudeEvenPowerSummandDSSTT_le_on_leftSmall_rectangle
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    {m : ℕ} (hm : 2 ≤ m) :
    |latitudeEvenPowerSummandDSSTT α m s t| ≤
      4194304 * ((m : ℝ) + 1) ^ (4 : ℕ) *
        angularKernelA s t ^ (α / 2 - 4) *
        ((15 : ℝ) / 16) ^ (m - 2) := by
  let A := angularKernelA s t
  let u := 1 - s ^ 2
  let v := 1 - t ^ 2
  let e := α / 2 - 2 * (m : ℝ)
  let w := (m : ℝ) + 1
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hA : 0 < A :=
    hgeo.base_pos.trans_le (hgeo.base_le s hs t ht)
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
      |latitudeEvenPowerSummandDSSTT α m s t| ≤
        262144 * w ^ 4 * (4 : ℝ) ^ m *
          A ^ e * u ^ (m - 2) * v ^ (m - 2) := by
    unfold latitudeEvenPowerSummandDSSTT
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
  have hQ := hgeo.ratio_le s hs t ht
  have hQ0 := unequalAngularRatio_nonneg hsSphere htSphere
  have hpow :
      unequalAngularRatio s t ^ (m - 2) ≤
        ((15 : ℝ) / 16) ^ (m - 2) :=
    pow_le_pow_left₀ hQ0 hQ _
  calc
    |latitudeEvenPowerSummandDSSTT α m s t| ≤
        262144 * w ^ 4 *
          ((4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) * A ^ e) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
    _ = 262144 * w ^ 4 *
        (16 * A ^ (α / 2 - 4) *
          unequalAngularRatio s t ^ (m - 2)) := by
      rw [hcommon]
      rfl
    _ ≤ 262144 * w ^ 4 *
        (16 * A ^ (α / 2 - 4) *
          ((15 : ℝ) / 16) ^ (m - 2)) := by
      gcongr
    _ = 4194304 * ((m : ℝ) + 1) ^ (4 : ℕ) *
        angularKernelA s t ^ (α / 2 - 4) *
        ((15 : ℝ) / 16) ^ (m - 2) := by
      dsimp [w, A]
      ring

noncomputable def latitudeEvenPowerDSSTTSeriesTerm
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  (Ring.choose (α / 2) (2 * m) *
    normalizedCosineMoment (2 * m)) *
    latitudeEvenPowerSummandDSSTT α m s t

/-- The coefficient-weighted fourth derivative tail is normally
summable at every point of a left-small rectangle.  The first two modes
are absent from this shifted formulation and are inserted in the next
theorem as a finite prefix. -/
theorem summable_shifted_latitudeEvenPowerDSSTTSeriesTerm
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    Summable (fun r : ℕ ↦
      latitudeEvenPowerDSSTTSeriesTerm α (r + 2) s t) := by
  have hA := hgeo.base_pos.trans_le (hgeo.base_le s hs t ht)
  have hcoef :=
    summable_shifted_evenAngularDerivativeCoefficient_mul_pow
      α (q := (15 : ℝ) / 16) (by norm_num) (by norm_num)
  have hmaj := hcoef.mul_left
    (4194304 * angularKernelA s t ^ (α / 2 - 4))
  apply hmaj.of_norm_bounded
  intro r
  have hterm :=
    abs_latitudeEvenPowerSummandDSSTT_le_on_leftSmall_rectangle
      hα0 hα2 hN hgeo hs ht (m := r + 2) (by omega)
  rw [show r + 2 - 2 = r by omega] at hterm
  unfold latitudeEvenPowerDSSTTSeriesTerm
  change |(Ring.choose (α / 2) (2 * (r + 2)) *
    normalizedCosineMoment (2 * (r + 2))) *
    latitudeEvenPowerSummandDSSTT α (r + 2) s t| ≤ _
  rw [abs_mul]
  calc
    |Ring.choose (α / 2) (2 * (r + 2)) *
        normalizedCosineMoment (2 * (r + 2))| *
        |latitudeEvenPowerSummandDSSTT α (r + 2) s t| ≤
      (|Ring.choose (α / 2) (2 * (r + 2))| *
        |normalizedCosineMoment (2 * (r + 2))|) *
      (4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
        angularKernelA s t ^ (α / 2 - 4) *
        ((15 : ℝ) / 16) ^ r) := by
      rw [abs_mul]
      gcongr
    _ =
      4194304 * angularKernelA s t ^ (α / 2 - 4) *
        (evenAngularDerivativeCoefficient α (r + 2) *
          ((15 : ℝ) / 16) ^ r) := by
      unfold evenAngularDerivativeCoefficient
      ring

/-- Normal convergence of the complete coefficient-weighted `(2,2)`
derivative series; modes `0` and `1` form a finite prefix. -/
theorem summable_latitudeEvenPowerDSSTTSeriesTerm
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    Summable (fun m : ℕ ↦
      latitudeEvenPowerDSSTTSeriesTerm α m s t) := by
  rw [← summable_nat_add_iff 2]
  simpa [Nat.add_comm] using
    summable_shifted_latitudeEvenPowerDSSTTSeriesTerm
      hα0 hα2 hN hgeo hs ht

/-! ## Lower derivative stages needed by the termwise transfer -/

/-- The mixed `(1,1)` derivative of one even-power summand.  It is needed
only for the endpoint-safe tensor Taylor decomposition; the main scale is
still governed by the `(2,2)` stage. -/
noncomputable def latitudeEvenPowerSummandDST
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

/-- The first three derivative stages have the same summable envelope as
the fourth stage.  Using one common (generous) constant makes the four
successive applications of the uniform derivative theorem transparent. -/
theorem abs_latitudeEvenPower_lowerDerivatives_le_on_leftSmall_rectangle
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    {m : ℕ} (hm : 2 ≤ m) :
    let R := 4194304 * ((m : ℝ) + 1) ^ (4 : ℕ) *
      angularKernelA s t ^ (α / 2 - 4) *
      ((15 : ℝ) / 16) ^ (m - 2)
    |latitudeEvenPowerSummandDS α m s t| ≤ R ∧
      |latitudeEvenPowerSummandDSS α m s t| ≤ R ∧
      |latitudeEvenPowerSummandDSST α m s t| ≤ R ∧
      |latitudeEvenPowerSummandDST α m s t| ≤ R := by
  let A := angularKernelA s t
  let u := 1 - s ^ 2
  let v := 1 - t ^ 2
  let e := α / 2 - 2 * (m : ℝ)
  let w := (m : ℝ) + 1
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hA : 0 < A :=
    hgeo.base_pos.trans_le (hgeo.base_le s hs t ht)
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
  have hQ := hgeo.ratio_le s hs t ht
  have hQ0 := unequalAngularRatio_nonneg hsSphere htSphere
  have hqpow : unequalAngularRatio s t ^ (m - 2) ≤
      ((15 : ℝ) / 16) ^ (m - 2) :=
    pow_le_pow_left₀ hQ0 hQ _
  have hbase :
      (4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) * A ^ e ≤
        16 * A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2) := by
    rw [hcommon]
    change 16 * A ^ (α / 2 - 4) *
      unequalAngularRatio s t ^ (m - 2) ≤ _
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
  · unfold latitudeEvenPowerSummandDS
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
          (16 * A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2)) := by
        gcongr
      _ ≤ 4194304 * w ^ 4 * A ^ (α / 2 - 4) *
          ((15 : ℝ) / 16) ^ (m - 2) := by
        let P := A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2)
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
  · unfold latitudeEvenPowerSummandDSS
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
          (16 * A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2)) := by
        gcongr
      _ ≤ 4194304 * w ^ 4 * A ^ (α / 2 - 4) *
          ((15 : ℝ) / 16) ^ (m - 2) := by
        let P := A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2)
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
  · unfold latitudeEvenPowerSummandDSST
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
          (16 * A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2)) := by
        gcongr
      _ ≤ 4194304 * w ^ 4 * A ^ (α / 2 - 4) *
          ((15 : ℝ) / 16) ^ (m - 2) := by
        let P := A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2)
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
  · unfold latitudeEvenPowerSummandDST
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
          (16 * A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2)) := by
        gcongr
      _ ≤ 4194304 * w ^ 4 * A ^ (α / 2 - 4) *
          ((15 : ℝ) / 16) ^ (m - 2) := by
        let P := A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2)
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

noncomputable def latitudeEvenPowerDSSeriesTerm
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  (Ring.choose (α / 2) (2 * m) *
    normalizedCosineMoment (2 * m)) *
    latitudeEvenPowerSummandDS α m s t

noncomputable def latitudeEvenPowerDSSSeriesTerm
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  (Ring.choose (α / 2) (2 * m) *
    normalizedCosineMoment (2 * m)) *
    latitudeEvenPowerSummandDSS α m s t

noncomputable def latitudeEvenPowerDSSTSeriesTerm
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  (Ring.choose (α / 2) (2 * m) *
    normalizedCosineMoment (2 * m)) *
    latitudeEvenPowerSummandDSST α m s t

/-- The three lower differentiated tails are normally summable on every
left-small rectangle, with the same fourth-degree coefficient majorant as
the final `(2,2)` series. -/
theorem summable_shifted_latitudeEvenPower_lowerSeriesTerms
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    Summable (fun r : ℕ ↦
      latitudeEvenPowerDSSeriesTerm α (r + 2) s t) ∧
    Summable (fun r : ℕ ↦
      latitudeEvenPowerDSSSeriesTerm α (r + 2) s t) ∧
    Summable (fun r : ℕ ↦
      latitudeEvenPowerDSSTSeriesTerm α (r + 2) s t) := by
  let c : ℕ → ℝ := fun m ↦
    Ring.choose (α / 2) (2 * m) * normalizedCosineMoment (2 * m)
  let E : ℕ → ℝ := fun r ↦
    4194304 * angularKernelA s t ^ (α / 2 - 4) *
      (evenAngularDerivativeCoefficient α (r + 2) *
        ((15 : ℝ) / 16) ^ r)
  have hcoef :=
    summable_shifted_evenAngularDerivativeCoefficient_mul_pow
      α (q := (15 : ℝ) / 16) (by norm_num) (by norm_num)
  have hE : Summable E := by
    dsimp [E]
    exact hcoef.mul_left
      (4194304 * angularKernelA s t ^ (α / 2 - 4))
  have hbound (F : ℕ → ℝ)
      (hF : ∀ r : ℕ,
        |F r| ≤
          4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
            angularKernelA s t ^ (α / 2 - 4) *
            ((15 : ℝ) / 16) ^ r) :
      Summable (fun r : ℕ ↦ c (r + 2) * F r) := by
    apply hE.of_norm_bounded
    intro r
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |c (r + 2)| * |F r| ≤
          |c (r + 2)| *
            (4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
              angularKernelA s t ^ (α / 2 - 4) *
              ((15 : ℝ) / 16) ^ r) := by
        exact mul_le_mul_of_nonneg_left (hF r) (abs_nonneg _)
      _ = E r := by
        dsimp [c, E, evenAngularDerivativeCoefficient]
        rw [abs_mul]
        ring
  have hlower (r : ℕ) :=
    abs_latitudeEvenPower_lowerDerivatives_le_on_leftSmall_rectangle
      hα0 hα2 hN hgeo hs ht (m := r + 2) (by omega)
  have hDS : Summable (fun r : ℕ ↦
      c (r + 2) * latitudeEvenPowerSummandDS α (r + 2) s t) := by
    apply hbound
    intro r
    simpa [show r + 2 - 2 = r by omega] using (hlower r).1
  have hDSS : Summable (fun r : ℕ ↦
      c (r + 2) * latitudeEvenPowerSummandDSS α (r + 2) s t) := by
    apply hbound
    intro r
    simpa [show r + 2 - 2 = r by omega] using (hlower r).2.1
  have hDSST : Summable (fun r : ℕ ↦
      c (r + 2) * latitudeEvenPowerSummandDSST α (r + 2) s t) := by
    apply hbound
    intro r
    simpa [show r + 2 - 2 = r by omega] using (hlower r).2.2.1
  exact ⟨by
    simpa [latitudeEvenPowerDSSeriesTerm, c] using hDS, by
    simpa [latitudeEvenPowerDSSSeriesTerm, c] using hDSS, by
    simpa [latitudeEvenPowerDSSTSeriesTerm, c] using hDSST⟩

/-- The undifferentiated tail is controlled by the same geometric ratio.
The smaller constant here reflects the four powers of `A` still present
before any height derivatives are taken. -/
theorem abs_latitudeEvenPowerSummand_le_on_leftSmall_rectangle
    {α : ℝ} {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    {m : ℕ} (hm : 2 ≤ m) :
    |latitudeEvenPowerSummand α m s t| ≤
      4096 * angularKernelA s t ^ (α / 2 - 4) *
        ((15 : ℝ) / 16) ^ (m - 2) := by
  let A := angularKernelA s t
  let u := 1 - s ^ 2
  let v := 1 - t ^ 2
  let e := α / 2 - 2 * (m : ℝ)
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hA : 0 < A :=
    hgeo.base_pos.trans_le (hgeo.base_le s hs t ht)
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
  have hQ := hgeo.ratio_le s hs t ht
  have hQ0 : 0 ≤ unequalAngularRatio s t :=
    unequalAngularRatio_nonneg hsSphere htSphere
  have hqpow :
      unequalAngularRatio s t ^ (m - 2) ≤
        ((15 : ℝ) / 16) ^ (m - 2) :=
    pow_le_pow_left₀ hQ0 hQ _
  have hbase :
      (4 : ℝ) ^ m * u ^ (m - 2) * v ^ (m - 2) * A ^ e ≤
        16 * A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2) := by
    rw [hcommon]
    change 16 * A ^ (α / 2 - 4) *
      unequalAngularRatio s t ^ (m - 2) ≤ _
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
      |latitudeEvenPowerSummand α m s t| =
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
      (16 * A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2)) *
        A ^ 4 := by
      exact mul_le_mul hbase huv (by positivity) (by positivity)
    _ ≤
      (16 * A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2)) *
        256 := by
      gcongr
    _ = 4096 * angularKernelA s t ^ (α / 2 - 4) *
        ((15 : ℝ) / 16) ^ (m - 2) := by
      dsimp [A]
      ring

noncomputable def latitudeEvenPowerSeriesTerm
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  (Ring.choose (α / 2) (2 * m) *
    normalizedCosineMoment (2 * m)) *
    latitudeEvenPowerSummand α m s t

theorem summable_shifted_latitudeEvenPowerSeriesTerm
    {α : ℝ} {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    Summable (fun r : ℕ ↦
      latitudeEvenPowerSeriesTerm α (r + 2) s t) := by
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le (hgeo.base_le s hs t ht)
  have hcoef :=
    summable_shifted_evenAngularDerivativeCoefficient_mul_pow
      α (q := (15 : ℝ) / 16) (by norm_num) (by norm_num)
  have hmaj := hcoef.mul_left
    (4096 * angularKernelA s t ^ (α / 2 - 4))
  apply hmaj.of_norm_bounded
  intro r
  have hterm :=
    abs_latitudeEvenPowerSummand_le_on_leftSmall_rectangle
      (α := α) hN hgeo hs ht (m := r + 2) (by omega)
  rw [show r + 2 - 2 = r by omega] at hterm
  unfold latitudeEvenPowerSeriesTerm
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |Ring.choose (α / 2) (2 * (r + 2)) *
        normalizedCosineMoment (2 * (r + 2))| *
        |latitudeEvenPowerSummand α (r + 2) s t| ≤
      |Ring.choose (α / 2) (2 * (r + 2)) *
        normalizedCosineMoment (2 * (r + 2))| *
        (4096 * angularKernelA s t ^ (α / 2 - 4) *
          ((15 : ℝ) / 16) ^ r) :=
      mul_le_mul_of_nonneg_left hterm (abs_nonneg _)
    _ ≤
      4096 * angularKernelA s t ^ (α / 2 - 4) *
        (evenAngularDerivativeCoefficient α (r + 2) *
          ((15 : ℝ) / 16) ^ r) := by
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
      have hq : 0 ≤ ((15 : ℝ) / 16) ^ r := by positivity
      have hpow : 0 ≤ angularKernelA s t ^ (α / 2 - 4) :=
        Real.rpow_nonneg hA.le _
      let C := |Ring.choose (α / 2) (2 * (r + 2))| *
        |normalizedCosineMoment (2 * (r + 2))|
      let P := 4096 * angularKernelA s t ^ (α / 2 - 4) *
        ((15 : ℝ) / 16) ^ r
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
              ((15 : ℝ) / 16) ^ r) := by ring

noncomputable def leftSmallLatitudeTailMajorant
    (α L : ℝ) (r : ℕ) : ℝ :=
  4194304 * L ^ (α / 2 - 4) *
    (evenAngularDerivativeCoefficient α (r + 2) *
      ((15 : ℝ) / 16) ^ r)

theorem summable_leftSmallLatitudeTailMajorant
    (α L : ℝ) :
    Summable (leftSmallLatitudeTailMajorant α L) := by
  exact
    (summable_shifted_evenAngularDerivativeCoefficient_mul_pow
      α (q := (15 : ℝ) / 16) (by norm_num) (by norm_num)).mul_left
        (4194304 * L ^ (α / 2 - 4))

/-- Uniform normal majorants for all four differentiated stages.  Unlike
the pointwise estimates above, this bound is independent of `s,t` inside
the fixed rectangle, so it is suitable for the termwise derivative
theorem. -/
theorem norm_latitudeEvenPower_tailStages_le_majorant
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (r : ℕ) :
    ‖latitudeEvenPowerDSSeriesTerm α (r + 2) s t‖ ≤
        leftSmallLatitudeTailMajorant α L r ∧
    ‖latitudeEvenPowerDSSSeriesTerm α (r + 2) s t‖ ≤
        leftSmallLatitudeTailMajorant α L r ∧
    ‖latitudeEvenPowerDSSTSeriesTerm α (r + 2) s t‖ ≤
        leftSmallLatitudeTailMajorant α L r ∧
    ‖latitudeEvenPowerDSSTTSeriesTerm α (r + 2) s t‖ ≤
        leftSmallLatitudeTailMajorant α L r := by
  have hLA : L ≤ angularKernelA s t := hgeo.base_le s hs t ht
  have hγ : α / 2 - 4 ≤ 0 := by linarith
  have hpow :
      angularKernelA s t ^ (α / 2 - 4) ≤ L ^ (α / 2 - 4) :=
    Real.rpow_le_rpow_of_nonpos hgeo.base_pos hLA hγ
  have hlower :=
    abs_latitudeEvenPower_lowerDerivatives_le_on_leftSmall_rectangle
      hα0 hα2 hN hgeo hs ht (m := r + 2) (by omega)
  have hfourth :=
    abs_latitudeEvenPowerSummandDSSTT_le_on_leftSmall_rectangle
      hα0 hα2 hN hgeo hs ht (m := r + 2) (by omega)
  rw [show r + 2 - 2 = r by omega] at hlower hfourth
  let c : ℝ :=
    Ring.choose (α / 2) (2 * (r + 2)) *
      normalizedCosineMoment (2 * (r + 2))
  have hstage (F : ℝ)
      (hF : |F| ≤
        4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
          angularKernelA s t ^ (α / 2 - 4) *
          ((15 : ℝ) / 16) ^ r) :
      ‖c * F‖ ≤ leftSmallLatitudeTailMajorant α L r := by
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |c| * |F| ≤
          |c| *
            (4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
              angularKernelA s t ^ (α / 2 - 4) *
              ((15 : ℝ) / 16) ^ r) :=
        mul_le_mul_of_nonneg_left hF (abs_nonneg _)
      _ ≤ |c| *
            (4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
              L ^ (α / 2 - 4) *
              ((15 : ℝ) / 16) ^ r) := by
        gcongr
      _ = leftSmallLatitudeTailMajorant α L r := by
        dsimp [c, leftSmallLatitudeTailMajorant,
          evenAngularDerivativeCoefficient]
        rw [abs_mul]
        ring
  exact ⟨by
    simpa [latitudeEvenPowerDSSeriesTerm, c] using
      hstage _ hlower.1, by
    simpa [latitudeEvenPowerDSSSeriesTerm, c] using
      hstage _ hlower.2.1, by
    simpa [latitudeEvenPowerDSSTSeriesTerm, c] using
      hstage _ hlower.2.2.1, by
    simpa [latitudeEvenPowerDSSTTSeriesTerm, c] using
      hstage _ hfourth⟩

/-- First pass of the termwise transfer: differentiate the shifted even
series once in the left height variable on the open band interior. -/
theorem hasDerivAt_shifted_latitudeEvenPowerSeries_left
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Ioo (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivAt
      (fun y ↦ ∑' r : ℕ,
        latitudeEvenPowerSeriesTerm α (r + 2) y t)
      (∑' r : ℕ,
        latitudeEvenPowerDSSeriesTerm α (r + 2) s t) s := by
  apply hasDerivAt_tsum_of_isPreconnected
    (u := leftSmallLatitudeTailMajorant α L)
    (t := Ioo (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (g := fun r y ↦ latitudeEvenPowerSeriesTerm α (r + 2) y t)
    (g' := fun r y ↦ latitudeEvenPowerDSSeriesTerm α (r + 2) y t)
    (y₀ := s)
  · exact summable_leftSmallLatitudeTailMajorant α L
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro r y hy
    have hy' : y ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j) := ⟨hy.1.le, hy.2.le⟩
    have hA : 0 < angularKernelA y t :=
      hgeo.base_pos.trans_le (hgeo.base_le y hy' t ht)
    simpa [latitudeEvenPowerSeriesTerm,
      latitudeEvenPowerDSSeriesTerm] using
      (hasDerivAt_latitudeEvenPowerSummand_left
        (α := α) (m := r + 2) hA).const_mul
          (Ring.choose (α / 2) (2 * (r + 2)) *
            normalizedCosineMoment (2 * (r + 2)))
  · intro r y hy
    exact
      (norm_latitudeEvenPower_tailStages_le_majorant
        hα0 hα2 hN hgeo ⟨hy.1.le, hy.2.le⟩ ht r).1
  · exact hs
  · exact summable_shifted_latitudeEvenPowerSeriesTerm
      hN hgeo ⟨hs.1.le, hs.2.le⟩ ht
  · exact hs

/-- Second left-height pass. -/
theorem hasDerivAt_shifted_latitudeEvenPowerDSSeries_left
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Ioo (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivAt
      (fun y ↦ ∑' r : ℕ,
        latitudeEvenPowerDSSeriesTerm α (r + 2) y t)
      (∑' r : ℕ,
        latitudeEvenPowerDSSSeriesTerm α (r + 2) s t) s := by
  apply hasDerivAt_tsum_of_isPreconnected
    (u := leftSmallLatitudeTailMajorant α L)
    (t := Ioo (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (g := fun r y ↦ latitudeEvenPowerDSSeriesTerm α (r + 2) y t)
    (g' := fun r y ↦ latitudeEvenPowerDSSSeriesTerm α (r + 2) y t)
    (y₀ := s)
  · exact summable_leftSmallLatitudeTailMajorant α L
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro r y hy
    have hy' : y ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j) := ⟨hy.1.le, hy.2.le⟩
    have hA : 0 < angularKernelA y t :=
      hgeo.base_pos.trans_le (hgeo.base_le y hy' t ht)
    simpa [latitudeEvenPowerDSSeriesTerm,
      latitudeEvenPowerDSSSeriesTerm] using
      (hasDerivAt_latitudeEvenPowerSummandDS_left
        (α := α) (m := r + 2) hA).const_mul
          (Ring.choose (α / 2) (2 * (r + 2)) *
            normalizedCosineMoment (2 * (r + 2)))
  · intro r y hy
    exact
      (norm_latitudeEvenPower_tailStages_le_majorant
        hα0 hα2 hN hgeo ⟨hy.1.le, hy.2.le⟩ ht r).2.1
  · exact hs
  · exact
      (summable_shifted_latitudeEvenPower_lowerSeriesTerms
        hα0 hα2 hN hgeo ⟨hs.1.le, hs.2.le⟩ ht).1
  · exact hs

/-- First right-height pass after the two left derivatives. -/
theorem hasDerivAt_shifted_latitudeEvenPowerDSSSeries_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivAt
      (fun y ↦ ∑' r : ℕ,
        latitudeEvenPowerDSSSeriesTerm α (r + 2) s y)
      (∑' r : ℕ,
        latitudeEvenPowerDSSTSeriesTerm α (r + 2) s t) t := by
  apply hasDerivAt_tsum_of_isPreconnected
    (u := leftSmallLatitudeTailMajorant α L)
    (t := Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (g := fun r y ↦ latitudeEvenPowerDSSSeriesTerm α (r + 2) s y)
    (g' := fun r y ↦ latitudeEvenPowerDSSTSeriesTerm α (r + 2) s y)
    (y₀ := t)
  · exact summable_leftSmallLatitudeTailMajorant α L
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro r y hy
    have hy' : y ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k) := ⟨hy.1.le, hy.2.le⟩
    have hA : 0 < angularKernelA s y :=
      hgeo.base_pos.trans_le (hgeo.base_le s hs y hy')
    simpa [latitudeEvenPowerDSSSeriesTerm,
      latitudeEvenPowerDSSTSeriesTerm] using
      (hasDerivAt_latitudeEvenPowerSummandDSS_right
        (α := α) (m := r + 2) hA).const_mul
          (Ring.choose (α / 2) (2 * (r + 2)) *
            normalizedCosineMoment (2 * (r + 2)))
  · intro r y hy
    exact
      (norm_latitudeEvenPower_tailStages_le_majorant
        hα0 hα2 hN hgeo hs ⟨hy.1.le, hy.2.le⟩ r).2.2.1
  · exact ht
  · exact
      (summable_shifted_latitudeEvenPower_lowerSeriesTerms
        hα0 hα2 hN hgeo hs ⟨ht.1.le, ht.2.le⟩).2.1
  · exact ht

/-- Final right-height pass, producing the shifted `(2,2)` series. -/
theorem hasDerivAt_shifted_latitudeEvenPowerDSSTSeries_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivAt
      (fun y ↦ ∑' r : ℕ,
        latitudeEvenPowerDSSTSeriesTerm α (r + 2) s y)
      (∑' r : ℕ,
        latitudeEvenPowerDSSTTSeriesTerm α (r + 2) s t) t := by
  apply hasDerivAt_tsum_of_isPreconnected
    (u := leftSmallLatitudeTailMajorant α L)
    (t := Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (g := fun r y ↦ latitudeEvenPowerDSSTSeriesTerm α (r + 2) s y)
    (g' := fun r y ↦ latitudeEvenPowerDSSTTSeriesTerm α (r + 2) s y)
    (y₀ := t)
  · exact summable_leftSmallLatitudeTailMajorant α L
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro r y hy
    have hy' : y ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k) := ⟨hy.1.le, hy.2.le⟩
    have hA : 0 < angularKernelA s y :=
      hgeo.base_pos.trans_le (hgeo.base_le s hs y hy')
    simpa [latitudeEvenPowerDSSTSeriesTerm,
      latitudeEvenPowerDSSTTSeriesTerm] using
      (hasDerivAt_latitudeEvenPowerSummandDSST_right
        (α := α) (m := r + 2) hA).const_mul
          (Ring.choose (α / 2) (2 * (r + 2)) *
            normalizedCosineMoment (2 * (r + 2)))
  · intro r y hy
    exact
      (norm_latitudeEvenPower_tailStages_le_majorant
        hα0 hα2 hN hgeo hs ⟨hy.1.le, hy.2.le⟩ r).2.2.2
  · exact ht
  · exact
      (summable_shifted_latitudeEvenPower_lowerSeriesTerms
        hα0 hα2 hN hgeo hs ⟨ht.1.le, ht.2.le⟩).2.2
  · exact ht

noncomputable def latitudeEvenPowerSeriesSum
    (α s t : ℝ) : ℝ :=
  latitudeEvenPowerSeriesTerm α 0 s t +
    latitudeEvenPowerSeriesTerm α 1 s t +
    ∑' r : ℕ, latitudeEvenPowerSeriesTerm α (r + 2) s t

noncomputable def latitudeEvenPowerDSSeriesSum
    (α s t : ℝ) : ℝ :=
  latitudeEvenPowerDSSeriesTerm α 0 s t +
    latitudeEvenPowerDSSeriesTerm α 1 s t +
    ∑' r : ℕ, latitudeEvenPowerDSSeriesTerm α (r + 2) s t

noncomputable def latitudeEvenPowerDSSSeriesSum
    (α s t : ℝ) : ℝ :=
  latitudeEvenPowerDSSSeriesTerm α 0 s t +
    latitudeEvenPowerDSSSeriesTerm α 1 s t +
    ∑' r : ℕ, latitudeEvenPowerDSSSeriesTerm α (r + 2) s t

noncomputable def latitudeEvenPowerDSSTSeriesSum
    (α s t : ℝ) : ℝ :=
  latitudeEvenPowerDSSTSeriesTerm α 0 s t +
    latitudeEvenPowerDSSTSeriesTerm α 1 s t +
    ∑' r : ℕ, latitudeEvenPowerDSSTSeriesTerm α (r + 2) s t

noncomputable def latitudeEvenPowerDSSTTSeriesSum
    (α s t : ℝ) : ℝ :=
  latitudeEvenPowerDSSTTSeriesTerm α 0 s t +
    latitudeEvenPowerDSSTTSeriesTerm α 1 s t +
    ∑' r : ℕ, latitudeEvenPowerDSSTTSeriesTerm α (r + 2) s t

theorem hasDerivAt_latitudeEvenPowerSeriesSum_left
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Ioo (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivAt (fun y ↦ latitudeEvenPowerSeriesSum α y t)
      (latitudeEvenPowerDSSeriesSum α s t) s := by
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le
      (hgeo.base_le s ⟨hs.1.le, hs.2.le⟩ t ht)
  have h0 :=
    (hasDerivAt_latitudeEvenPowerSummand_left
      (α := α) (m := 0) hA).const_mul
        (Ring.choose (α / 2) 0 * normalizedCosineMoment 0)
  have h1 :=
    (hasDerivAt_latitudeEvenPowerSummand_left
      (α := α) (m := 1) hA).const_mul
        (Ring.choose (α / 2) 2 * normalizedCosineMoment 2)
  have htail :=
    hasDerivAt_shifted_latitudeEvenPowerSeries_left
      hα0 hα2 hN hgeo hs ht
  simpa [latitudeEvenPowerSeriesSum, latitudeEvenPowerDSSeriesSum,
    latitudeEvenPowerSeriesTerm, latitudeEvenPowerDSSeriesTerm] using
      (h0.add h1).add htail

theorem hasDerivAt_latitudeEvenPowerDSSeriesSum_left
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Ioo (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivAt (fun y ↦ latitudeEvenPowerDSSeriesSum α y t)
      (latitudeEvenPowerDSSSeriesSum α s t) s := by
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le
      (hgeo.base_le s ⟨hs.1.le, hs.2.le⟩ t ht)
  have h0 :=
    (hasDerivAt_latitudeEvenPowerSummandDS_left
      (α := α) (m := 0) hA).const_mul
        (Ring.choose (α / 2) 0 * normalizedCosineMoment 0)
  have h1 :=
    (hasDerivAt_latitudeEvenPowerSummandDS_left
      (α := α) (m := 1) hA).const_mul
        (Ring.choose (α / 2) 2 * normalizedCosineMoment 2)
  have htail :=
    hasDerivAt_shifted_latitudeEvenPowerDSSeries_left
      hα0 hα2 hN hgeo hs ht
  simpa [latitudeEvenPowerDSSeriesSum, latitudeEvenPowerDSSSeriesSum,
    latitudeEvenPowerDSSeriesTerm, latitudeEvenPowerDSSSeriesTerm] using
      (h0.add h1).add htail

theorem hasDerivAt_latitudeEvenPowerDSSSeriesSum_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivAt (fun y ↦ latitudeEvenPowerDSSSeriesSum α s y)
      (latitudeEvenPowerDSSTSeriesSum α s t) t := by
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le
      (hgeo.base_le s hs t ⟨ht.1.le, ht.2.le⟩)
  have h0 :=
    (hasDerivAt_latitudeEvenPowerSummandDSS_right
      (α := α) (m := 0) hA).const_mul
        (Ring.choose (α / 2) 0 * normalizedCosineMoment 0)
  have h1 :=
    (hasDerivAt_latitudeEvenPowerSummandDSS_right
      (α := α) (m := 1) hA).const_mul
        (Ring.choose (α / 2) 2 * normalizedCosineMoment 2)
  have htail :=
    hasDerivAt_shifted_latitudeEvenPowerDSSSeries_right
      hα0 hα2 hN hgeo hs ht
  simpa [latitudeEvenPowerDSSSeriesSum, latitudeEvenPowerDSSTSeriesSum,
    latitudeEvenPowerDSSSeriesTerm, latitudeEvenPowerDSSTSeriesTerm] using
      (h0.add h1).add htail

theorem hasDerivAt_latitudeEvenPowerDSSTSeriesSum_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivAt (fun y ↦ latitudeEvenPowerDSSTSeriesSum α s y)
      (latitudeEvenPowerDSSTTSeriesSum α s t) t := by
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le
      (hgeo.base_le s hs t ⟨ht.1.le, ht.2.le⟩)
  have h0 :=
    (hasDerivAt_latitudeEvenPowerSummandDSST_right
      (α := α) (m := 0) hA).const_mul
        (Ring.choose (α / 2) 0 * normalizedCosineMoment 0)
  have h1 :=
    (hasDerivAt_latitudeEvenPowerSummandDSST_right
      (α := α) (m := 1) hA).const_mul
        (Ring.choose (α / 2) 2 * normalizedCosineMoment 2)
  have htail :=
    hasDerivAt_shifted_latitudeEvenPowerDSSTSeries_right
      hα0 hα2 hN hgeo hs ht
  simpa [latitudeEvenPowerDSSTSeriesSum, latitudeEvenPowerDSSTTSeriesSum,
    latitudeEvenPowerDSSTSeriesTerm, latitudeEvenPowerDSSTTSeriesTerm] using
      (h0.add h1).add htail

/-- On the complete closed left-small rectangle, the finite-prefix-plus-tail
series is exactly the angular latitude kernel. -/
theorem latitudeKernel_eq_latitudeEvenPowerSeriesSum
    {α : ℝ} {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    latitudeKernel α s t = latitudeEvenPowerSeriesSum α s t := by
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le (hgeo.base_le s hs t ht)
  have hQ := hgeo.ratio_le s hs t ht
  have hratioSq :
      (angularKernelB s t / angularKernelA s t) ^ 2 =
        unequalAngularRatio s t := by
    calc
      (angularKernelB s t / angularKernelA s t) ^ 2 =
          angularKernelB s t ^ 2 / angularKernelA s t ^ 2 :=
        div_pow _ _ _
      _ = unequalAngularRatio s t :=
        (unequalAngularRatio_eq_sq_div hsSphere htSphere).symm
  have habsSq :
      |angularKernelB s t / angularKernelA s t| ^ 2 =
        unequalAngularRatio s t := by
    rw [sq_abs]
    exact hratioSq
  have hq :
      |angularKernelB s t / angularKernelA s t| < 1 := by
    have habs0 :
        0 ≤ |angularKernelB s t / angularKernelA s t| := abs_nonneg _
    nlinarith
  have hkernel :=
    latitudeKernel_eq_evenPowerSeries
      (α := α) hsSphere htSphere hA hq
  have hsum : Summable (fun m : ℕ ↦
      latitudeEvenPowerSeriesTerm α m s t) := by
    rw [← summable_nat_add_iff 2]
    exact summable_shifted_latitudeEvenPowerSeriesTerm hN hgeo hs ht
  have hsplit := hsum.sum_add_tsum_nat_add 2
  calc
    latitudeKernel α s t =
        ∑' m : ℕ, latitudeEvenPowerSeriesTerm α m s t := by
      simpa [latitudeEvenPowerSeriesTerm] using hkernel
    _ = (∑ m ∈ Finset.range 2,
          latitudeEvenPowerSeriesTerm α m s t) +
        ∑' r : ℕ, latitudeEvenPowerSeriesTerm α (r + 2) s t :=
      hsplit.symm
    _ = latitudeEvenPowerSeriesSum α s t := by
      simp [latitudeEvenPowerSeriesSum, Finset.sum_range_succ]

/-- Uniqueness after the first left derivative. -/
theorem latitudeEvenPowerDSSeriesSum_eq_variableReducedLatitudeKernelDs
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesRectangleGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Ioo (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    latitudeEvenPowerDSSeriesSum α s t =
      variableReducedLatitudeKernelDs α s t := by
  have hs' : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j) := ⟨hs.1.le, hs.2.le⟩
  have hrect := hgeo.interior_offDiagonal s hs' t ht
  have heq :
      (fun y ↦ latitudeEvenPowerSeriesSum α y t) =ᶠ[nhds s]
        (fun y ↦ variableReducedLatitudeKernel α y t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with y hy
    have hy' : y ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j) := ⟨hy.1.le, hy.2.le⟩
    have hygeo := hgeo.interior_offDiagonal y hy' t ht
    calc
      latitudeEvenPowerSeriesSum α y t = latitudeKernel α y t :=
        (latitudeKernel_eq_latitudeEvenPowerSeriesSum
          (α := α) hN hgeo.toLatitudeEvenPowerSeriesBaseGeometry hy' ht).symm
      _ = variableReducedLatitudeKernel α y t :=
        latitudeKernel_eq_variableReducedLatitudeKernel
          hygeo.1 hygeo.2.1
  have hseries :=
    hasDerivAt_latitudeEvenPowerSeriesSum_left
      hα0 hα2 hN hgeo.toLatitudeEvenPowerSeriesBaseGeometry hs ht
  have hseries' :
      HasDerivAt (fun y ↦ variableReducedLatitudeKernel α y t)
        (latitudeEvenPowerDSSeriesSum α s t) s :=
    heq.hasDerivAt_iff.mp hseries
  exact hseries'.unique
    (hasDerivAt_variableReducedLatitudeKernel_left
      hrect.1 hrect.2.1 hrect.2.2)

/-- Uniqueness after the second left derivative. -/
theorem latitudeEvenPowerDSSSeriesSum_eq_variableReducedLatitudeKernelDss
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesRectangleGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Ioo (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    latitudeEvenPowerDSSSeriesSum α s t =
      variableReducedLatitudeKernelDss α s t := by
  have hs' : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j) := ⟨hs.1.le, hs.2.le⟩
  have hrect := hgeo.interior_offDiagonal s hs' t ht
  have heq :
      (fun y ↦ latitudeEvenPowerDSSeriesSum α y t) =ᶠ[nhds s]
        (fun y ↦ variableReducedLatitudeKernelDs α y t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with y hy
    exact latitudeEvenPowerDSSeriesSum_eq_variableReducedLatitudeKernelDs
      hα0 hα2 hN hgeo hy ht
  have hseries :=
    hasDerivAt_latitudeEvenPowerDSSeriesSum_left
      hα0 hα2 hN hgeo.toLatitudeEvenPowerSeriesBaseGeometry hs ht
  have hseries' :
      HasDerivAt (fun y ↦ variableReducedLatitudeKernelDs α y t)
        (latitudeEvenPowerDSSSeriesSum α s t) s :=
    heq.hasDerivAt_iff.mp hseries
  exact hseries'.unique
    (hasDerivAt_variableReducedLatitudeKernelDs_left
      hrect.1 hrect.2.1 hrect.2.2)

/-- Uniqueness after the first right derivative. -/
theorem latitudeEvenPowerDSSTSeriesSum_eq_variableReducedLatitudeKernelDsst
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesRectangleGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Ioo (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    latitudeEvenPowerDSSTSeriesSum α s t =
      variableReducedLatitudeKernelDsst α s t := by
  have hs' : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j) := ⟨hs.1.le, hs.2.le⟩
  have ht' : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k) := ⟨ht.1.le, ht.2.le⟩
  have hrect := hgeo.interior_offDiagonal s hs' t ht'
  have heq :
      (fun y ↦ latitudeEvenPowerDSSSeriesSum α s y) =ᶠ[nhds t]
        (fun y ↦ variableReducedLatitudeKernelDss α s y) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
    exact latitudeEvenPowerDSSSeriesSum_eq_variableReducedLatitudeKernelDss
      hα0 hα2 hN hgeo hs ⟨hy.1.le, hy.2.le⟩
  have hseries :=
    hasDerivAt_latitudeEvenPowerDSSSeriesSum_right
      hα0 hα2 hN hgeo.toLatitudeEvenPowerSeriesBaseGeometry hs' ht
  have hseries' :
      HasDerivAt (fun y ↦ variableReducedLatitudeKernelDss α s y)
        (latitudeEvenPowerDSSTSeriesSum α s t) t :=
    heq.hasDerivAt_iff.mp hseries
  exact hseries'.unique
    (hasDerivAt_variableReducedLatitudeKernelDss_right
      hrect.1 hrect.2.1 hrect.2.2)

/-- Interior identification of the genuine mixed `(2,2)` derivative with
the coefficient-weighted DSSTT series. -/
theorem latitudeEvenPowerDSSTTSeriesSum_eq_variableReducedLatitudeKernelDsstt
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesRectangleGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Ioo (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    latitudeEvenPowerDSSTTSeriesSum α s t =
      variableReducedLatitudeKernelDsstt α s t := by
  have hs' : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j) := ⟨hs.1.le, hs.2.le⟩
  have ht' : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k) := ⟨ht.1.le, ht.2.le⟩
  have hrect := hgeo.interior_offDiagonal s hs' t ht'
  have heq :
      (fun y ↦ latitudeEvenPowerDSSTSeriesSum α s y) =ᶠ[nhds t]
        (fun y ↦ variableReducedLatitudeKernelDsst α s y) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
    exact latitudeEvenPowerDSSTSeriesSum_eq_variableReducedLatitudeKernelDsst
      hα0 hα2 hN hgeo hs hy
  have hseries :=
    hasDerivAt_latitudeEvenPowerDSSTSeriesSum_right
      hα0 hα2 hN hgeo.toLatitudeEvenPowerSeriesBaseGeometry hs' ht
  have hseries' :
      HasDerivAt (fun y ↦ variableReducedLatitudeKernelDsst α s y)
        (latitudeEvenPowerDSSTTSeriesSum α s t) t :=
    heq.hasDerivAt_iff.mp hseries
  exact hseries'.unique
    (hasDerivAt_variableReducedLatitudeKernelDsst_right
      hrect.1 hrect.2.1 hrect.2.2)

private theorem abs_latitudeEvenPowerDSSTTSeriesTerm_zero_le
    {α s t : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |latitudeEvenPowerDSSTTSeriesTerm α 0 s t| ≤
      32768 * angularKernelA s t ^ (α / 2 - 4) := by
  have h :=
    abs_unequalAPowSSTT_le
      (α := α) (m := 0) hα0 hα2 hs ht hA
  unfold latitudeEvenPowerDSSTTSeriesTerm
    latitudeEvenPowerSummandDSSTT
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

private theorem abs_latitudeEvenPowerSummandDSSTT_one_le
    {α s t : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |latitudeEvenPowerSummandDSSTT α 1 s t| ≤
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
  · simp [latitudeEvenPowerSummandDSSTT, X, XT, XTT,
      U, U1, U2, V, V1, V2, e]
  · dsimp [A, e]
    ring_nf

private theorem abs_latitudeEvenPowerDSSTTSeriesTerm_one_le
    {α s t : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    |latitudeEvenPowerDSSTTSeriesTerm α 1 s t| ≤
      (8388608 * |Ring.choose (α / 2) 2|) *
        angularKernelA s t ^ (α / 2 - 4) := by
  have h :=
    abs_latitudeEvenPowerSummandDSSTT_one_le
      hα0 hα2 hs ht hA
  unfold latitudeEvenPowerDSSTTSeriesTerm
  rw [abs_mul, abs_mul]
  calc
    |Ring.choose (α / 2) 2| * |normalizedCosineMoment 2| *
        |latitudeEvenPowerSummandDSSTT α 1 s t| ≤
      |Ring.choose (α / 2) 2| * 1 *
        (8388608 * angularKernelA s t ^ (α / 2 - 4)) := by
      gcongr
      exact abs_normalizedCosineMoment_le_one 2
    _ = _ := by ring

private theorem continuousAt_latitudeEvenPower_lowerSeriesTerms_uncurry
    (α : ℝ) (m : ℕ) {p : ℝ × ℝ}
    (hA : 0 < angularKernelA p.1 p.2) :
    ContinuousAt
        (fun q : ℝ × ℝ ↦
          latitudeEvenPowerSeriesTerm α m q.1 q.2) p ∧
      ContinuousAt
        (fun q : ℝ × ℝ ↦
          latitudeEvenPowerDSSeriesTerm α m q.1 q.2) p ∧
      ContinuousAt
        (fun q : ℝ × ℝ ↦
          latitudeEvenPowerDSSSeriesTerm α m q.1 q.2) p ∧
      ContinuousAt
        (fun q : ℝ × ℝ ↦
          latitudeEvenPowerDSSTSeriesTerm α m q.1 q.2) p := by
  have hAc :
      ContinuousAt (fun q : ℝ × ℝ ↦ angularKernelA q.1 q.2) p := by
    unfold angularKernelA
    fun_prop
  have hpow (z : ℝ) :
      ContinuousAt (fun q : ℝ × ℝ ↦ angularKernelA q.1 q.2 ^ z) p :=
    hAc.rpow_const (Or.inl hA.ne')
  unfold latitudeEvenPowerSeriesTerm latitudeEvenPowerDSSeriesTerm
    latitudeEvenPowerDSSSeriesTerm latitudeEvenPowerDSSTSeriesTerm
    latitudeEvenPowerSummand latitudeEvenPowerSummandDS
    latitudeEvenPowerSummandDSS latitudeEvenPowerSummandDSST
    unequalAPow unequalAPowS unequalAPowT unequalAPowSS
    unequalAPowST unequalAPowSST
    unequalRadiusPower unequalRadiusPowerD1 unequalRadiusPowerD2
  dsimp only
  constructor
  · fun_prop
  constructor
  · fun_prop
  constructor <;> fun_prop

private theorem continuousAt_latitudeEvenPowerDSSTTSeriesTerm_uncurry
    (α : ℝ) (m : ℕ) {p : ℝ × ℝ}
    (hA : 0 < angularKernelA p.1 p.2) :
    ContinuousAt
      (fun q : ℝ × ℝ ↦
        latitudeEvenPowerDSSTTSeriesTerm α m q.1 q.2) p := by
  have hAc :
      ContinuousAt (fun q : ℝ × ℝ ↦ angularKernelA q.1 q.2) p := by
    unfold angularKernelA
    fun_prop
  have hpow (z : ℝ) :
      ContinuousAt (fun q : ℝ × ℝ ↦ angularKernelA q.1 q.2 ^ z) p :=
    hAc.rpow_const (Or.inl hA.ne')
  unfold latitudeEvenPowerDSSTTSeriesTerm
    latitudeEvenPowerSummandDSSTT
    unequalAPow unequalAPowS unequalAPowT unequalAPowSS
    unequalAPowST unequalAPowTT unequalAPowSST
    unequalAPowSTT unequalAPowSSTT
    unequalRadiusPower unequalRadiusPowerD1 unequalRadiusPowerD2
  dsimp only
  fun_prop

theorem continuousOn_latitudeEvenPowerDSSTTSeriesSum_uncurry
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦
        latitudeEvenPowerDSSTTSeriesSum α p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
  let S :=
    Icc (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) ×ˢ
      Icc (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k)
  have hterm (m : ℕ) :
      ContinuousOn
        (fun p : ℝ × ℝ ↦
          latitudeEvenPowerDSSTTSeriesTerm α m p.1 p.2) S := by
    intro p hp
    have hA :=
      hgeo.base_pos.trans_le (hgeo.base_le p.1 hp.1 p.2 hp.2)
    exact
      (continuousAt_latitudeEvenPowerDSSTTSeriesTerm_uncurry
        α m hA).continuousWithinAt
  have htail :
      ContinuousOn
        (fun p : ℝ × ℝ ↦ ∑' r : ℕ,
          latitudeEvenPowerDSSTTSeriesTerm α (r + 2) p.1 p.2) S := by
    apply continuousOn_tsum
      (fun r ↦ hterm (r + 2))
      (summable_leftSmallLatitudeTailMajorant α L)
    intro r p hp
    exact
      (norm_latitudeEvenPower_tailStages_le_majorant
        hα0 hα2 hN hgeo hp.1 hp.2 r).2.2.2
  dsimp [S] at hterm htail ⊢
  unfold latitudeEvenPowerDSSTTSeriesSum
  exact ((hterm 0).add (hterm 1)).add htail

/-- All four lower stages of the normally convergent even series are
continuous on the complete closed rectangle.  This is the endpoint-safe
input needed to extend the four derivative passes to one-sided derivatives
at a polar boundary. -/
theorem continuousOn_latitudeEvenPower_lowerSeriesSums_uncurry
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L) :
    let S :=
      Icc (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k)
    ContinuousOn
        (fun p : ℝ × ℝ ↦ latitudeEvenPowerSeriesSum α p.1 p.2) S ∧
      ContinuousOn
        (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSSeriesSum α p.1 p.2) S ∧
      ContinuousOn
        (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSSSeriesSum α p.1 p.2) S ∧
      ContinuousOn
        (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSSTSeriesSum α p.1 p.2) S := by
  dsimp only
  let S :=
    Icc (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) ×ˢ
      Icc (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k)
  have hterm (m : ℕ) :
      ContinuousOn
          (fun p : ℝ × ℝ ↦ latitudeEvenPowerSeriesTerm α m p.1 p.2) S ∧
        ContinuousOn
          (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSSeriesTerm α m p.1 p.2) S ∧
        ContinuousOn
          (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSSSeriesTerm α m p.1 p.2) S ∧
        ContinuousOn
          (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSSTSeriesTerm α m p.1 p.2) S := by
    have hstage :
        ∀ p ∈ S,
          ContinuousAt
              (fun q : ℝ × ℝ ↦
                latitudeEvenPowerSeriesTerm α m q.1 q.2) p ∧
            ContinuousAt
              (fun q : ℝ × ℝ ↦
                latitudeEvenPowerDSSeriesTerm α m q.1 q.2) p ∧
            ContinuousAt
              (fun q : ℝ × ℝ ↦
                latitudeEvenPowerDSSSeriesTerm α m q.1 q.2) p ∧
            ContinuousAt
              (fun q : ℝ × ℝ ↦
                latitudeEvenPowerDSSTSeriesTerm α m q.1 q.2) p := by
      intro p hp
      exact continuousAt_latitudeEvenPower_lowerSeriesTerms_uncurry α m
        (hgeo.base_pos.trans_le (hgeo.base_le p.1 hp.1 p.2 hp.2))
    exact
      ⟨fun p hp ↦ (hstage p hp).1.continuousWithinAt,
        fun p hp ↦ (hstage p hp).2.1.continuousWithinAt,
        fun p hp ↦ (hstage p hp).2.2.1.continuousWithinAt,
        fun p hp ↦ (hstage p hp).2.2.2.continuousWithinAt⟩
  have htail1 :
      ContinuousOn
        (fun p : ℝ × ℝ ↦ ∑' r : ℕ,
          latitudeEvenPowerDSSeriesTerm α (r + 2) p.1 p.2) S := by
    apply continuousOn_tsum
      (fun r ↦ (hterm (r + 2)).2.1)
      (summable_leftSmallLatitudeTailMajorant α L)
    intro r p hp
    exact (norm_latitudeEvenPower_tailStages_le_majorant
      hα0 hα2 hN hgeo hp.1 hp.2 r).1
  have htail2 :
      ContinuousOn
        (fun p : ℝ × ℝ ↦ ∑' r : ℕ,
          latitudeEvenPowerDSSSeriesTerm α (r + 2) p.1 p.2) S := by
    apply continuousOn_tsum
      (fun r ↦ (hterm (r + 2)).2.2.1)
      (summable_leftSmallLatitudeTailMajorant α L)
    intro r p hp
    exact (norm_latitudeEvenPower_tailStages_le_majorant
      hα0 hα2 hN hgeo hp.1 hp.2 r).2.1
  have htail3 :
      ContinuousOn
        (fun p : ℝ × ℝ ↦ ∑' r : ℕ,
          latitudeEvenPowerDSSTSeriesTerm α (r + 2) p.1 p.2) S := by
    apply continuousOn_tsum
      (fun r ↦ (hterm (r + 2)).2.2.2)
      (summable_leftSmallLatitudeTailMajorant α L)
    intro r p hp
    exact (norm_latitudeEvenPower_tailStages_le_majorant
      hα0 hα2 hN hgeo hp.1 hp.2 r).2.2.1
  dsimp [S] at hterm htail1 htail2 htail3 ⊢
  exact
    ⟨by
      intro p hp
      have hkernel :
          ContinuousAt (fun q : ℝ × ℝ ↦ latitudeKernel α q.1 q.2) p :=
        (continuous_latitudeKernel hα0).continuousAt
      apply hkernel.continuousWithinAt.congr
      · intro q hq
        exact (latitudeKernel_eq_latitudeEvenPowerSeriesSum
          hN hgeo hq.1 hq.2).symm
      · exact (latitudeKernel_eq_latitudeEvenPowerSeriesSum
          hN hgeo hp.1 hp.2).symm,
      by
        unfold latitudeEvenPowerDSSeriesSum
        exact (((hterm 0).2.1).add ((hterm 1).2.1)).add htail1,
      by
        unfold latitudeEvenPowerDSSSeriesSum
        exact (((hterm 0).2.2.1).add ((hterm 1).2.2.1)).add htail2,
      by
        unfold latitudeEvenPowerDSSTSeriesSum
        exact (((hterm 0).2.2.2).add ((hterm 1).2.2.2)).add htail3⟩

private theorem continuousAt_variableReducedLatitudeKernelDsstt_uncurry
    (α : ℝ) {p : ℝ × ℝ}
    (hs : p.1 ∈ Ioo (-1 : ℝ) 1)
    (ht : p.2 ∈ Ioo (-1 : ℝ) 1) (hst : p.1 ≠ p.2) :
    ContinuousAt
      (fun q : ℝ × ℝ ↦
        variableReducedLatitudeKernelDsstt α q.1 q.2) p := by
  have hscale : 0 < latitudeAngularScale p.1 p.2 := by
    unfold latitudeAngularScale
    exact mul_pos
      (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hgap : 0 < normalizedLatitudeGap p.1 p.2 :=
    normalizedLatitudeGap_pos hs ht hst
  have hrs : heightRadius p.1 ≠ 0 := (heightRadius_pos hs).ne'
  have hrt : heightRadius p.2 ≠ 0 := (heightRadius_pos ht).ne'
  have hRs :
      ContinuousAt (fun q : ℝ × ℝ ↦ heightRadius q.1) p := by
    unfold heightRadius
    fun_prop
  have hRt :
      ContinuousAt (fun q : ℝ × ℝ ↦ heightRadius q.2) p := by
    unfold heightRadius
    fun_prop
  have hSc :
      ContinuousAt
        (fun q : ℝ × ℝ ↦ latitudeAngularScale q.1 q.2) p := by
    unfold latitudeAngularScale
    fun_prop
  have hSpow (z : ℝ) :
      ContinuousAt
        (fun q : ℝ × ℝ ↦ latitudeAngularScale q.1 q.2 ^ z) p :=
    hSc.rpow_const (Or.inl hscale.ne')
  have hGc :
      ContinuousAt
        (fun q : ℝ × ℝ ↦ normalizedLatitudeGap q.1 q.2) p := by
    unfold normalizedLatitudeGap
    exact
      (((by fun_prop :
          ContinuousAt (fun q : ℝ × ℝ ↦ 1 - q.1 * q.2) p).div
        (hRs.mul hRt) (mul_ne_zero hrs hrt)).sub continuousAt_const)
  have hC0 :
      ContinuousAt
        (fun q : ℝ × ℝ ↦
          reducedLatitudeCusp α (normalizedLatitudeGap q.1 q.2)) p :=
    (hasDerivAt_reducedLatitudeCusp
      (α := α) hgap).continuousAt.tendsto.comp hGc
  have hC1 :
      ContinuousAt
        (fun q : ℝ × ℝ ↦
          reducedLatitudeCuspD1Value α
            (normalizedLatitudeGap q.1 q.2)) p :=
    (hasDerivAt_reducedLatitudeCuspD1Value
      (α := α) hgap).continuousAt.tendsto.comp hGc
  have hC2 :
      ContinuousAt
        (fun q : ℝ × ℝ ↦
          reducedLatitudeCuspD2Value α
            (normalizedLatitudeGap q.1 q.2)) p :=
    (hasDerivAt_reducedLatitudeCuspD2Value
      (α := α) hgap).continuousAt.tendsto.comp hGc
  have hC3 :
      ContinuousAt
        (fun q : ℝ × ℝ ↦
          reducedLatitudeCuspD3Value α
            (normalizedLatitudeGap q.1 q.2)) p :=
    (hasDerivAt_reducedLatitudeCuspD3Value
      (α := α) hgap).continuousAt.tendsto.comp hGc
  have hC4outer :
      ContinuousAt (reducedLatitudeCuspD4Value α)
        (normalizedLatitudeGap p.1 p.2) := by
    have hm :=
      (hasDerivAt_reducedCuspMoment
        (β := α / 2 - 4) hgap).continuousAt
    simpa [reducedLatitudeCuspD4Value] using
      hm.const_mul
        ((α / 2) * (α / 2 - 1) * (α / 2 - 2) * (α / 2 - 3))
  have hC4 :
      ContinuousAt
        (fun q : ℝ × ℝ ↦
          reducedLatitudeCuspD4Value α
            (normalizedLatitudeGap q.1 q.2)) p :=
    hC4outer.tendsto.comp hGc
  unfold variableReducedLatitudeKernelDsstt
    latitudeJetMulD2 latitudeJetMul3D2
    latitudePower latitudePowerDt latitudePowerDtt
    latitudePowerDs latitudePowerDst latitudePowerDstt
    latitudePowerDss latitudePowerDsst latitudePowerDsstt
    latitudeCusp0 latitudeCusp0Dt latitudeCusp0Dtt
    latitudeCusp1 latitudeCusp1Dt latitudeCusp1Dtt
    latitudeCusp2 latitudeCusp2Dt latitudeCusp2Dtt
    latitudeAngularScaleDt latitudeAngularScaleDtt
    latitudeAngularScaleDstt latitudeAngularScaleDs
    latitudeAngularScaleDss latitudeAngularScaleDst
    latitudeAngularScaleDsst latitudeAngularScaleDsstt
    normalizedLatitudeGapDt normalizedLatitudeGapDtt
    normalizedLatitudeGapDst normalizedLatitudeGapDstt
    normalizedLatitudeGapDs normalizedLatitudeGapDss
    normalizedLatitudeGapDsst normalizedLatitudeGapDsstt
    heightRadiusD1 heightRadiusD2
  fun_prop (disch := aesop)

/-- The interior series identification extends to the four sides of every
left-small rectangle.  This is the endpoint form needed by the Peano bridge. -/
theorem latitudeEvenPowerDSSTTSeriesSum_eq_variableReducedLatitudeKernelDsstt_on_rectangle
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesRectangleGeometry N j k L) :
    Set.EqOn
      (fun p : ℝ × ℝ ↦
        latitudeEvenPowerDSSTTSeriesSum α p.1 p.2)
      (fun p : ℝ × ℝ ↦
        variableReducedLatitudeKernelDsstt α p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
  let S :=
    Ioo (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) ×ˢ
      Ioo (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k)
  let T :=
    Icc (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) ×ˢ
      Icc (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k)
  have hjpop : 0 < finiteBandPopulation N j := by
    have hjthree := concrete_finiteBandPopulation_three_le hM j
    omega
  have hkpop : 0 < finiteBandPopulation N k := by
    have hkthree := concrete_finiteBandPopulation_three_le hM k
    omega
  have hjlt :
      bandBoundaryHeight N (j + 1) < bandBoundaryHeight N j := by
    rw [← sub_pos, bandBoundaryHeight_sub_succ]
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hjr : (0 : ℝ) < finiteBandPopulation N j := by
      exact_mod_cast hjpop
    positivity
  have hklt :
      bandBoundaryHeight N (k + 1) < bandBoundaryHeight N k := by
    rw [← sub_pos, bandBoundaryHeight_sub_succ]
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hkr : (0 : ℝ) < finiteBandPopulation N k := by
      exact_mod_cast hkpop
    positivity
  have hST : S ⊆ T := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hTS : T ⊆ closure S := by
    have hclosure : closure S = T := by
      dsimp [S, T]
      rw [closure_prod_eq, closure_Ioo hjlt.ne, closure_Ioo hklt.ne]
    rw [hclosure]
  have hinterior :
      Set.EqOn
        (fun p : ℝ × ℝ ↦
          latitudeEvenPowerDSSTTSeriesSum α p.1 p.2)
        (fun p : ℝ × ℝ ↦
          variableReducedLatitudeKernelDsstt α p.1 p.2) S := by
    intro p hp
    exact
      latitudeEvenPowerDSSTTSeriesSum_eq_variableReducedLatitudeKernelDsstt
        hα0 hα2 hN hgeo hp.1 hp.2
  have hseries :
      ContinuousOn
        (fun p : ℝ × ℝ ↦
          latitudeEvenPowerDSSTTSeriesSum α p.1 p.2) T := by
    simpa [T] using
      continuousOn_latitudeEvenPowerDSSTTSeriesSum_uncurry
        hα0 hα2 hN hgeo.toLatitudeEvenPowerSeriesBaseGeometry
  have hkernel :
      ContinuousOn
        (fun p : ℝ × ℝ ↦
          variableReducedLatitudeKernelDsstt α p.1 p.2) T := by
    intro p hp
    have hrect := hgeo.interior_offDiagonal p.1 hp.1 p.2 hp.2
    exact
      (continuousAt_variableReducedLatitudeKernelDsstt_uncurry
        α hrect.1 hrect.2.1 hrect.2.2).continuousWithinAt
  exact hinterior.of_subset_closure hseries hkernel hST hTS

/-- Explicit coefficient constant for the differentiated unequal-latitude
series.  Its only infinite component is an absolutely convergent,
one-dimensional numerical series. -/
noncomputable def unequalLatitudeDssttSeriesConstant (α : ℝ) : ℝ :=
  32768 + 8388608 * |Ring.choose (α / 2) 2| +
    4194304 * ∑' r : ℕ,
      evenAngularDerivativeCoefficient α (r + 2) *
        ((15 : ℝ) / 16) ^ r

theorem unequalLatitudeDssttSeriesConstant_nonneg (α : ℝ) :
    0 ≤ unequalLatitudeDssttSeriesConstant α := by
  unfold unequalLatitudeDssttSeriesConstant
  have hsum : 0 ≤ ∑' r : ℕ,
      evenAngularDerivativeCoefficient α (r + 2) *
        ((15 : ℝ) / 16) ^ r :=
    tsum_nonneg fun r ↦ mul_nonneg
      (evenAngularDerivativeCoefficient_nonneg α (r + 2)) (by positivity)
  positivity

/-- Absolute estimate for the differentiated even series on the full closed
rectangle.  Unlike the off-pole derivative identification below, this
statement is valid when either squared radius vanishes at a polar endpoint. -/
theorem abs_latitudeEvenPowerDSSTTSeriesSum_le_series_scale
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |latitudeEvenPowerDSSTTSeriesSum α s t| ≤
      unequalLatitudeDssttSeriesConstant α * L ^ (α / 2 - 4) := by
  let f : ℕ → ℝ := fun r ↦
    evenAngularDerivativeCoefficient α (r + 2) *
      ((15 : ℝ) / 16) ^ r
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le (hgeo.base_le s hs t ht)
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hγ : α / 2 - 4 ≤ 0 := by linarith
  have hpow :
      angularKernelA s t ^ (α / 2 - 4) ≤ L ^ (α / 2 - 4) :=
    Real.rpow_le_rpow_of_nonpos hgeo.base_pos
      (hgeo.base_le s hs t ht) hγ
  have hzero :
      |latitudeEvenPowerDSSTTSeriesTerm α 0 s t| ≤
        32768 * L ^ (α / 2 - 4) :=
    (abs_latitudeEvenPowerDSSTTSeriesTerm_zero_le
      hα0 hα2
      hsSphere htSphere
      hA).trans (by gcongr)
  have hone :
      |latitudeEvenPowerDSSTTSeriesTerm α 1 s t| ≤
        (8388608 * |Ring.choose (α / 2) 2|) *
          L ^ (α / 2 - 4) :=
    (abs_latitudeEvenPowerDSSTTSeriesTerm_one_le
      hα0 hα2
      hsSphere htSphere
      hA).trans (by gcongr)
  have hterms :=
    summable_shifted_latitudeEvenPowerDSSTTSeriesTerm
      hα0 hα2 hN hgeo hs ht
  have hmajor := summable_leftSmallLatitudeTailMajorant α L
  have htail :
      |∑' r : ℕ,
          latitudeEvenPowerDSSTTSeriesTerm α (r + 2) s t| ≤
        (4194304 * L ^ (α / 2 - 4)) * ∑' r : ℕ, f r := by
    have hnorm :
        ‖∑' r : ℕ,
            latitudeEvenPowerDSSTTSeriesTerm α (r + 2) s t‖ ≤
          ∑' r : ℕ, leftSmallLatitudeTailMajorant α L r :=
      (norm_tsum_le_tsum_norm hterms.norm).trans
        (hterms.norm.tsum_mono hmajor fun r ↦
          (norm_latitudeEvenPower_tailStages_le_majorant
            hα0 hα2 hN hgeo hs ht r).2.2.2)
    rw [Real.norm_eq_abs] at hnorm
    calc
      |∑' r : ℕ,
          latitudeEvenPowerDSSTTSeriesTerm α (r + 2) s t| ≤
          ∑' r : ℕ, leftSmallLatitudeTailMajorant α L r := hnorm
      _ = (4194304 * L ^ (α / 2 - 4)) * ∑' r : ℕ, f r := by
        dsimp [leftSmallLatitudeTailMajorant, f]
        rw [tsum_mul_left]
  unfold latitudeEvenPowerDSSTTSeriesSum
  calc
    |_ + _ + _| ≤
        |latitudeEvenPowerDSSTTSeriesTerm α 0 s t| +
          |latitudeEvenPowerDSSTTSeriesTerm α 1 s t| +
          |∑' r : ℕ,
            latitudeEvenPowerDSSTTSeriesTerm α (r + 2) s t| := by
      exact (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤ 32768 * L ^ (α / 2 - 4) +
        (8388608 * |Ring.choose (α / 2) 2|) * L ^ (α / 2 - 4) +
        (4194304 * L ^ (α / 2 - 4)) * ∑' r : ℕ, f r := by
      gcongr
    _ = unequalLatitudeDssttSeriesConstant α * L ^ (α / 2 - 4) := by
      dsimp [unequalLatitudeDssttSeriesConstant, f]
      ring
    _ = _ := by rfl

/-- Absolute DSSTT estimate for the actual off-pole height-chart kernel.
This is the preceding endpoint-safe series bound followed by the closed
rectangle identification. -/
theorem abs_variableReducedLatitudeKernelDsstt_le_series_scale
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesRectangleGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |variableReducedLatitudeKernelDsstt α s t| ≤
      unequalLatitudeDssttSeriesConstant α * L ^ (α / 2 - 4) := by
  have heq :
      latitudeEvenPowerDSSTTSeriesSum α s t =
        variableReducedLatitudeKernelDsstt α s t := by
    simpa using
      (latitudeEvenPowerDSSTTSeriesSum_eq_variableReducedLatitudeKernelDsstt_on_rectangle
        hα0 hα2 hN hM hgeo (x := (s, t)) ⟨hs, ht⟩)
  rw [← heq]
  exact abs_latitudeEvenPowerDSSTTSeriesSum_le_series_scale
    hα0 hα2 hN hgeo.toLatitudeEvenPowerSeriesBaseGeometry hs ht

/-- The final α-dependent constant after converting
`(2 d_k²/N)^(α/2-4)` to the manuscript scale. -/
noncomputable def unequalLatitudeDssttConstant (α : ℝ) : ℝ :=
  unequalLatitudeDssttSeriesConstant α * 10 ^ (4 - α / 2)

theorem unequalLatitudeDssttConstant_nonneg (α : ℝ) :
    0 ≤ unequalLatitudeDssttConstant α := by
  unfold unequalLatitudeDssttConstant
  exact mul_nonneg (unequalLatitudeDssttSeriesConstant_nonneg α)
    (Real.rpow_nonneg (by norm_num) _)

private theorem leftSmallLatitude_seriesScale_le_manuscriptScale
    {α : ℝ} (_hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    (k : Fin (bandTailCount N + 1)) :
    (2 * (latitudeBandScale N k : ℝ) ^ 2 / N) ^ (α / 2 - 4) ≤
      10 ^ (4 - α / 2) *
        (bandCount N : ℝ) ^ (8 - α) *
        (latitudeBandScale N k : ℝ) ^ (α - 8) := by
  let M : ℝ := bandCount N
  let d : ℝ := latitudeBandScale N k
  let L : ℝ := 2 * d ^ 2 / N
  let p : ℝ := 4 - α / 2
  have hMpos : 0 < M := by
    dsimp [M]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast latitudeBandScale_pos N k
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hp : 0 ≤ p := by
    dsimp [p]
    linarith
  have hNupper : (N : ℝ) ≤ 20 * M ^ 2 := by
    dsimp [M]
    exact_mod_cast bemoc_N_le_twenty_bandCount_sq hM
  have hLinv : L⁻¹ = (N : ℝ) / (2 * d ^ 2) := by
    dsimp [L]
    field_simp
  have hbase : L⁻¹ ≤ 10 * M ^ 2 / d ^ 2 := by
    rw [hLinv]
    calc
      (N : ℝ) / (2 * d ^ 2) ≤
          (20 * M ^ 2) / (2 * d ^ 2) := by
        exact div_le_div_of_nonneg_right hNupper (by positivity)
      _ = 10 * M ^ 2 / d ^ 2 := by ring
  have hrpow :
      L⁻¹ ^ p ≤ (10 * M ^ 2 / d ^ 2) ^ p :=
    Real.rpow_le_rpow (inv_nonneg.2 hL.le) hbase hp
  calc
    (2 * (latitudeBandScale N k : ℝ) ^ 2 / N) ^ (α / 2 - 4) =
        L ^ (-p) := by
      dsimp [L, d, p]
      congr 1
      ring
    _ = L⁻¹ ^ p := by
      rw [Real.rpow_neg hL.le, Real.inv_rpow hL.le]
    _ ≤ (10 * M ^ 2 / d ^ 2) ^ p := hrpow
    _ = 10 ^ p * M ^ (2 * p) * d ^ (-2 * p) := by
      rw [Real.div_rpow (mul_nonneg (by norm_num) (sq_nonneg M))
          (sq_nonneg d),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) (sq_nonneg M)]
      rw [show M ^ 2 = M ^ (2 : ℝ) by
          exact (Real.rpow_natCast M 2).symm,
        show d ^ 2 = d ^ (2 : ℝ) by
          exact (Real.rpow_natCast d 2).symm,
        ← Real.rpow_mul hMpos.le, ← Real.rpow_mul hdpos.le,
        div_eq_mul_inv, ← Real.rpow_neg hdpos.le]
      ring_nf
    _ = 10 ^ (4 - α / 2) *
        (bandCount N : ℝ) ^ (8 - α) *
        (latitudeBandScale N k : ℝ) ^ (α - 8) := by
      dsimp [M, d, p]
      congr 1 <;> ring_nf

/-- The analytic series proof supplies the exact pointwise hypothesis used
by the left-small mixed-Peano bridge. -/
theorem hasLeftSmallLatitudeDssttBound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    HasLeftSmallLatitudeDssttBound α N
      (unequalLatitudeDssttConstant α) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  intro j k hjk s hs t ht
  have hgeo :=
    leftSmallSame_evenPowerSeriesRectangleGeometry hN hjk
  have hseries :=
    abs_variableReducedLatitudeKernelDsstt_le_series_scale
      hα0 hα2 hN hM hgeo hs ht
  have hscale :=
    leftSmallLatitude_seriesScale_le_manuscriptScale
      hα0 hα2 hN (by omega) k
  calc
    |variableReducedLatitudeKernelDsstt α s t| ≤
        unequalLatitudeDssttSeriesConstant α *
          (2 * (latitudeBandScale N k : ℝ) ^ 2 / N) ^
            (α / 2 - 4) := hseries
    _ ≤ unequalLatitudeDssttSeriesConstant α *
        (10 ^ (4 - α / 2) *
          (bandCount N : ℝ) ^ (8 - α) *
          (latitudeBandScale N k : ℝ) ^ (α - 8)) := by
      exact mul_le_mul_of_nonneg_left hscale
        (unequalLatitudeDssttSeriesConstant_nonneg α)
    _ = unequalLatitudeDssttConstant α *
        (bandCount N : ℝ) ^ (8 - α) *
        (latitudeBandScale N k : ℝ) ^ (α - 8) := by
      unfold unequalLatitudeDssttConstant
      ring

/-- Unconditional left-small same-hemisphere block estimate obtained by
feeding the completed analytic DSSTT bound into the Peano bridge. -/
theorem leftSmallSame_block_bound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    ∀ j k, LeftSmallSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α
          (1024 * unequalLatitudeDssttConstant α) N j k := by
  exact leftSmallSame_block_bound_of_Dsstt
    (by omega) hα0 (unequalLatitudeDssttConstant_nonneg α)
    (hasLeftSmallLatitudeDssttBound_series hα0 hα2 hM)

end BEMOC
