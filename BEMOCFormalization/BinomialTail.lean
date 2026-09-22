import BEMOCFormalization.SeparatedBinomialSeries
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.PSeries

open scoped BigOperators
namespace BEMOC.Definitive

/-- Positive coefficients of `1 - sqrt (1-z)`, starting at degree one. -/
noncomputable def chordBinomialCoeff (m : ℕ) : ℝ :=
  -((-1 : ℝ) ^ m * Ring.choose (1 / 2 : ℝ) m)

private theorem chordBinomialCoeff_one : chordBinomialCoeff 1 = 1 / 2 := by
  norm_num [chordBinomialCoeff]

/-- The coefficient recurrence, with its positive form after degree one. -/
theorem chordBinomialCoeff_succ (m : ℕ) (_hm : 1 ≤ m) :
    (m + 1 : ℝ) * chordBinomialCoeff (m + 1) =
      ((m : ℝ) - 1 / 2) * chordBinomialCoeff m := by
  unfold chordBinomialCoeff
  have h := real_choose_succ (1 / 2 : ℝ) m
  rw [pow_succ]
  calc
    (m + 1 : ℝ) * -(((-1 : ℝ) ^ m * -1) * Ring.choose (1 / 2 : ℝ) (m + 1)) =
        (-1 : ℝ) ^ m * ((m + 1 : ℝ) * Ring.choose (1 / 2 : ℝ) (m + 1)) := by ring
    _ = (-1 : ℝ) ^ m * ((1 / 2 - m) * Ring.choose (1 / 2 : ℝ) m) := by rw [h]
    _ = ((m : ℝ) - 1 / 2) * -((-1 : ℝ) ^ m * Ring.choose (1 / 2 : ℝ) m) := by ring

/-- Every nonconstant coefficient is positive. -/
theorem chordBinomialCoeff_pos (m : ℕ) (hm : 1 ≤ m) :
    0 < chordBinomialCoeff m := by
  induction m, hm using Nat.le_induction with
  | base => simp [chordBinomialCoeff_one]
  | succ m hm ih =>
      have h := chordBinomialCoeff_succ m hm
      have hh : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hfactor : (0 : ℝ) < (m : ℝ) - 1 / 2 := by linarith
      have hden : (0 : ℝ) < m + 1 := by positivity
      nlinarith [mul_pos hfactor ih]

private noncomputable def chordWallisCoeff (m : ℕ) : ℝ :=
  (2 * (m : ℝ) - 1) * chordBinomialCoeff m

private theorem chordWallisCoeff_one : chordWallisCoeff 1 = 1 / 2 := by
  norm_num [chordWallisCoeff, chordBinomialCoeff_one]

private theorem chordWallisCoeff_pos (m : ℕ) (hm : 1 ≤ m) :
    0 < chordWallisCoeff m := by
  unfold chordWallisCoeff
  have hh : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact mul_pos (by linarith) (chordBinomialCoeff_pos m hm)

private theorem chordWallisCoeff_succ (m : ℕ) (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 2) * chordWallisCoeff (m + 1) =
      (2 * (m : ℝ) + 1) * chordWallisCoeff m := by
  have h := chordBinomialCoeff_succ m hm
  unfold chordWallisCoeff
  push_cast
  nlinarith [h]

private theorem chordWallisCoeff_sq_lower (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ 4 * (m : ℝ) * chordWallisCoeff m ^ 2 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [chordWallisCoeff_one]
  | succ m hm ih =>
      have hrec := chordWallisCoeff_succ m hm
      have hb0 := chordWallisCoeff_pos m hm
      have hb1 := chordWallisCoeff_pos (m + 1) (by omega)
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      have hpoly : (m : ℝ) * (2 * m + 2) ^ 2 ≤
          (m + 1) * (2 * m + 1) ^ 2 := by nlinarith [sq_nonneg (m : ℝ)]
      have hrec_sq : (2 * (m : ℝ) + 2) ^ 2 * chordWallisCoeff (m + 1) ^ 2 =
          (2 * (m : ℝ) + 1) ^ 2 * chordWallisCoeff m ^ 2 := by nlinarith [congrArg (fun x : ℝ => x ^ 2) hrec]
      have hcompare : (m : ℝ) * chordWallisCoeff m ^ 2 ≤
          (m + 1) * chordWallisCoeff (m + 1) ^ 2 := by
        have hsq0 : 0 ≤ chordWallisCoeff m ^ 2 := sq_nonneg _
        have hmul := mul_le_mul_of_nonneg_right hpoly hsq0
        nlinarith
      push_cast
      nlinarith

private theorem chordWallisCoeff_sq_upper (m : ℕ) (hm : 1 ≤ m) :
    (m + 1 : ℝ) * chordWallisCoeff m ^ 2 ≤ 1 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [chordWallisCoeff_one]
  | succ m hm ih =>
      have hrec := chordWallisCoeff_succ m hm
      have hb0 := chordWallisCoeff_pos m hm
      have hb1 := chordWallisCoeff_pos (m + 1) (by omega)
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      have hpoly : (m + 2 : ℝ) * (2 * m + 1) ^ 2 ≤
          (m + 1) * (2 * m + 2) ^ 2 := by nlinarith [sq_nonneg (m : ℝ)]
      have hrec_sq : (2 * (m : ℝ) + 2) ^ 2 * chordWallisCoeff (m + 1) ^ 2 =
          (2 * (m : ℝ) + 1) ^ 2 * chordWallisCoeff m ^ 2 := by
        nlinarith [congrArg (fun x : ℝ => x ^ 2) hrec]
      have hcompare : (m + 2 : ℝ) * chordWallisCoeff (m + 1) ^ 2 ≤
          (m + 1) * chordWallisCoeff m ^ 2 := by
        have hsq0 : 0 ≤ chordWallisCoeff m ^ 2 := sq_nonneg _
        have hmul := mul_le_mul_of_nonneg_right hpoly hsq0
        nlinarith
      push_cast
      nlinarith

/-- Elementary inverse-three-halves majorant. -/
theorem chordBinomialCoeff_upper (m : ℕ) (hm : 1 ≤ m) :
    chordBinomialCoeff m ≤ 1 / ((m : ℝ) * Real.sqrt m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm0
  have hsqroot : (Real.sqrt (m : ℝ)) ^ 2 = m := Real.sq_sqrt hm0.le
  have ha := chordBinomialCoeff_pos m hm
  have hb := chordWallisCoeff_sq_upper m hm
  unfold chordWallisCoeff at hb
  have hfactor : (m : ℝ) ^ 2 ≤ (2 * m - 1) ^ 2 := by nlinarith
  have hsqnonneg : 0 ≤ (m : ℝ) * chordBinomialCoeff m ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfactor hsqnonneg
  have hscaled : ((m : ℝ) * Real.sqrt m * chordBinomialCoeff m) ^ 2 ≤ 1 := by
    nlinarith [hsqroot]
  have hscaled_pos : 0 ≤ (m : ℝ) * Real.sqrt m * chordBinomialCoeff m := by positivity
  have hlinear : (m : ℝ) * Real.sqrt m * chordBinomialCoeff m ≤ 1 := by nlinarith
  apply (le_div_iff₀ (by positivity : 0 < (m : ℝ) * Real.sqrt m)).2
  nlinarith

/-- A concrete inverse-three-halves lower bound for every coefficient. -/
theorem chordBinomialCoeff_lower (m : ℕ) (hm : 1 ≤ m) :
    1 / (4 * (m : ℝ) * Real.sqrt m) ≤ chordBinomialCoeff m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm0
  have hsqroot : (Real.sqrt (m : ℝ)) ^ 2 = m := Real.sq_sqrt hm0.le
  have ha := chordBinomialCoeff_pos m hm
  have hb := chordWallisCoeff_sq_lower m hm
  unfold chordWallisCoeff at hb
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hfactor : (2 * (m : ℝ) - 1) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by nlinarith
  have hsqnonneg : 0 ≤ (m : ℝ) * chordBinomialCoeff m ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfactor hsqnonneg
  have hscaled : 1 ≤ (4 * (m : ℝ) * Real.sqrt m * chordBinomialCoeff m) ^ 2 := by
    nlinarith [hsqroot]
  have hscaled_pos : 0 ≤ 4 * (m : ℝ) * Real.sqrt m * chordBinomialCoeff m := by positivity
  have hlinear : 1 ≤ 4 * (m : ℝ) * Real.sqrt m * chordBinomialCoeff m := by
    nlinarith
  apply (div_le_iff₀ (by positivity : 0 < 4 * (m : ℝ) * Real.sqrt m)).2
  nlinarith

/-- A dyadic block already contains the required square-root mass. -/
theorem chordBinomialCoeff_even_block_lower (n : ℕ) (hn : 1 ≤ n) :
    1 / (32 * Real.sqrt (n : ℝ)) ≤
      ∑ r ∈ Finset.Ico n (2 * n), chordBinomialCoeff (2 * r) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hterm (r : ℕ) (hr : r ∈ Finset.Ico n (2 * n)) :
      1 / (32 * (n : ℝ) * Real.sqrt n) ≤ chordBinomialCoeff (2 * r) := by
    have hrlo : n ≤ r := (Finset.mem_Ico.mp hr).1
    have hrhi : r < 2 * n := (Finset.mem_Ico.mp hr).2
    have hm1 : 1 ≤ 2 * r := by omega
    have hm0 : (0 : ℝ) < 2 * r := by exact_mod_cast hm1
    have hmle : (2 * r : ℝ) ≤ 4 * n := by exact_mod_cast (by omega : 2 * r ≤ 4 * n)
    have hsqrtle : Real.sqrt (2 * r : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
      calc
        Real.sqrt (2 * r : ℝ) ≤ Real.sqrt (4 * (n : ℝ)) := Real.sqrt_le_sqrt hmle
        _ = 2 * Real.sqrt (n : ℝ) := by
          have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
            norm_num
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
    have hden : 4 * (2 * r : ℝ) * Real.sqrt (2 * r : ℝ) ≤
        32 * (n : ℝ) * Real.sqrt n := by
      have hprod := mul_le_mul hmle hsqrtle
        (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 4 * n)
      nlinarith
    have hden0 : 0 < 4 * (2 * r : ℝ) * Real.sqrt (2 * r : ℝ) := by positivity
    have hden1 : 0 < 32 * (n : ℝ) * Real.sqrt n := by positivity
    have hlow := chordBinomialCoeff_lower (2 * r) hm1
    push_cast at hlow
    exact (one_div_le_one_div_of_le hden0 hden).trans hlow
  have hsum := Finset.sum_le_sum (s := Finset.Ico n (2 * n)) (fun r hr => hterm r hr)
  simp only [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul] at hsum
  convert hsum using 1
  field_simp [hn0, hsqrt0]
  ring

/-- The block lower bound in the exponent convention of Beck's theorem. -/
theorem chordBinomialCoeff_even_block_lower_rpow (n : ℕ) (hn : 1 ≤ n) :
    (1 / 32 : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
      ∑ r ∈ Finset.Ico n (2 * n), chordBinomialCoeff (2 * r) := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  convert chordBinomialCoeff_even_block_lower n hn using 1
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hn0,
    ← Real.sqrt_eq_rpow]
  ring

/-- Absolute summability of the endpoint binomial coefficients. -/
theorem summable_chordBinomialCoeff : Summable chordBinomialCoeff := by
  have hp : Summable (fun m : ℕ => 1 / (m : ℝ) ^ (3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hp' : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) :=
    hp.comp_injective (fun _ _ h => Nat.succ.inj h)
  have heq (n : ℕ) :
      1 / ((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) =
        1 / (((n + 1 : ℕ) : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add hn,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hupper : Summable (fun n : ℕ => chordBinomialCoeff (n + 1)) := by
    apply Summable.of_nonneg_of_le
      (fun n => (chordBinomialCoeff_pos (n + 1) (by omega)).le)
      (fun n => (chordBinomialCoeff_upper (n + 1) (by omega)).trans_eq (heq n).symm)
    simpa only [heq] using hp'
  exact (summable_nat_add_iff 1).mp hupper

end BEMOC.Definitive
