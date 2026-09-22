import BEMOCFormalization.LatitudeCoefficientDerivatives
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Normally convergent majorants for unequal-scale latitude blocks

This file formalizes two pieces of the even-power argument in (5.6).

* Polynomial losses of any fixed order are summable against a geometric
  ratio strictly smaller than one.
* After two possible losses of `1-s²` and `1-t²`, every monomial occurring
  in the mixed `(2,2)` derivative has the common majorant
  `16 A^(β-4) Q^(m-2)`, where
  `Q = 4(1-s²)(1-t²)/A²`.

The second statement is deliberately valid when either squared radius is
zero: it only uses natural powers, and hence is the endpoint-safe algebraic
core of the manuscript's rewrite `B^(2m)=4^m(1-s²)^m(1-t²)^m`.
-/

open Set

namespace BEMOC

/-- The endpoint-safe even angular ratio from the unequal-scale expansion. -/
noncomputable def unequalAngularRatio (s t : ℝ) : ℝ :=
  4 * (1 - s ^ 2) * (1 - t ^ 2) / angularKernelA s t ^ 2

theorem unequalAngularRatio_nonneg
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    0 ≤ unequalAngularRatio s t := by
  have hu : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hv : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  unfold unequalAngularRatio
  positivity

/-- The polynomial ratio is exactly `(B/A)²` away from `A=0`. -/
theorem unequalAngularRatio_eq_sq_div
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    unequalAngularRatio s t =
      angularKernelB s t ^ 2 / angularKernelA s t ^ 2 := by
  have hu : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hv : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  unfold unequalAngularRatio angularKernelB
  rw [show
      (2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 =
        4 * Real.sqrt (1 - s ^ 2) ^ 2 *
          Real.sqrt (1 - t ^ 2) ^ 2 by ring,
    Real.sq_sqrt hu, Real.sq_sqrt hv]

theorem unequalAngularRatio_le_one
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t) :
    unequalAngularRatio s t ≤ 1 := by
  rw [unequalAngularRatio_eq_sq_div hs ht]
  have hBA := angularKernelB_le_A hs ht
  have hB0 := angularKernelB_nonneg s t
  have hsq : angularKernelB s t ^ 2 ≤ angularKernelA s t ^ 2 := by
    gcongr
  rw [div_le_one (sq_pos_of_pos hA)]
  exact hsq

/-- Fixed polynomial losses are normally summable against `q^m`. -/
theorem summable_natPolynomial_mul_geometric
    (degree : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℕ ↦ ((m : ℝ) + 1) ^ degree * q ^ m) := by
  have hnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hbase :
      Summable (fun n : ℕ ↦ ‖((n : ℝ) ^ degree * q ^ n : ℝ)‖) :=
    summable_norm_pow_mul_geometric_of_norm_lt_one degree hnorm
  have hshift :
      Summable (fun m : ℕ ↦ ‖(((m + 1 : ℕ) : ℝ) ^ degree *
        q ^ (m + 1) : ℝ)‖) :=
    hbase.comp_injective (fun _ _ h ↦ Nat.succ.inj h)
  by_cases hq : q = 0
  · subst q
    apply summable_of_ne_finset_zero (s := {0})
    intro m hm
    simp only [Finset.mem_singleton] at hm
    simp [hm]
  · have hqnorm : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
    have hscaled := hshift.mul_left ‖q‖⁻¹
    have heq :
        (fun m : ℕ ↦ ‖q‖⁻¹ *
            ‖(((m + 1 : ℕ) : ℝ) ^ degree * q ^ (m + 1) : ℝ)‖) =
          fun m : ℕ ↦ ((m : ℝ) + 1) ^ degree * q ^ m := by
      funext m
      rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hq0,
        pow_succ, Real.norm_natCast, Nat.cast_add, Nat.cast_one]
      field_simp
      rw [abs_of_nonneg hq0]
      ring
    simpa only [heq] using hscaled

/-- The shifted majorant which occurs literally in (5.6). -/
theorem summable_natPolynomial_mul_geometric_shift_two
    (degree : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℕ ↦
      ((m : ℝ) + 3) ^ degree * q ^ m) := by
  have hnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hbase :
      Summable (fun n : ℕ ↦ ‖((n : ℝ) ^ degree * q ^ n : ℝ)‖) :=
    summable_norm_pow_mul_geometric_of_norm_lt_one degree hnorm
  have hshift :
      Summable (fun m : ℕ ↦ ‖(((m + 3 : ℕ) : ℝ) ^ degree *
        q ^ (m + 3) : ℝ)‖) :=
    hbase.comp_injective (fun _ _ h ↦ by omega)
  by_cases hq : q = 0
  · subst q
    apply summable_of_ne_finset_zero (s := {0})
    intro m hm
    simp only [Finset.mem_singleton] at hm
    simp [hm]
  · have hq3 : ‖q‖ ^ 3 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hq)
    have hscaled := hshift.mul_left (‖q‖ ^ 3)⁻¹
    have heq :
        (fun m : ℕ ↦ (‖q‖ ^ 3)⁻¹ *
            ‖(((m + 3 : ℕ) : ℝ) ^ degree * q ^ (m + 3) : ℝ)‖) =
          fun m : ℕ ↦ ((m : ℝ) + 3) ^ degree * q ^ m := by
      funext m
      rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hq0,
        pow_add, Real.norm_natCast, Nat.cast_add, Nat.cast_ofNat]
      field_simp
      rw [abs_of_nonneg hq0]
      ring
    simpa only [heq] using hscaled

/-- The two terms in the manuscript majorant are normally summable,
uniformly for each fixed `q<1`. -/
theorem summable_polyseriesDerivative_majorant
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℕ ↦
      ((m : ℝ) + 3) ^ (4 : ℕ) * (q ^ m + q ^ (m + 2))) := by
  have h :=
    summable_natPolynomial_mul_geometric_shift_two 4 hq0 hq1
  have h2 : Summable (fun m : ℕ ↦
      ((m : ℝ) + 3) ^ (4 : ℕ) * q ^ (m + 2)) := by
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using
      h.mul_right (q ^ 2)
  simpa [mul_add] using h.add h2

/-- Abstract endpoint-safe monomial underlying every term after four
height derivatives.  `a` counts derivatives landing on `A`, while `b,c`
count factors removed from the two squared radii. -/
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

end BEMOC
