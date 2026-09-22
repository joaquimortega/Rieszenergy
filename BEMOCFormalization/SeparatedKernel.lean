import BEMOCFormalization.KernelDerivatives
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.Binomial

/-!
# Algebraic estimates for the separated angular kernel

The even angular expansion uses the polynomial squared radius `1-s²`.
This avoids differentiating square roots at either pole.  The estimates
below hold on the closed height square, including its boundary.
-/

namespace BEMOC.Definitive

open Set

/-- The polynomial ratio of the two squared radii to the squared axial distance. -/
noncomputable def separatedRatio (s t : ℝ) : ℝ :=
  4 * (1 - s ^ 2) * (1 - t ^ 2) / (2 - 2 * s * t) ^ 2

theorem radiusSq_nonneg {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    0 ≤ 1 - s ^ 2 := by
  rcases hs with ⟨hl, hr⟩
  nlinarith

theorem radiusSq_le_axial {s t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    1 - s ^ 2 ≤ 2 - 2 * s * t := by
  have h := radiusSq_nonneg ht
  nlinarith [sq_nonneg (s - t)]

theorem radiusSq_right_le_axial {s t : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    1 - t ^ 2 ≤ 2 - 2 * s * t := by
  have h := radiusSq_le_axial (s := t) (t := s) hs
  nlinarith

theorem axial_le_four {s t : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    2 - 2 * s * t ≤ 4 := by
  have hst : -1 ≤ s * t := by
    nlinarith [mul_nonneg (show 0 ≤ s + 1 by linarith [hs.1])
      (show 0 ≤ t + 1 by linarith [ht.1]),
      mul_nonneg (show 0 ≤ 1 - s by linarith [hs.2])
      (show 0 ≤ 1 - t by linarith [ht.2])]
  linarith

theorem axial_pos_of_separated {s t : ℝ}
    (h : 0 < 2 - 2 * s * t) : 0 < (2 - 2 * s * t) ^ 2 :=
  sq_pos_of_pos h

theorem separatedRatio_nonneg {s t : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    0 ≤ separatedRatio s t := by
  have hA := radiusSq_nonneg hs
  have hB := radiusSq_nonneg ht
  unfold separatedRatio
  positivity

/-- Under the manuscript's separation hypothesis the squared polynomial
ratio is bounded strictly below one, including when a radius vanishes. -/
theorem separatedRatio_le_sq_one_sub
    {s t ε : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hU : 0 < 2 - 2 * s * t)
    (_hε : 0 < ε) (hε1 : ε < 1)
    (hsep : 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
      (1 - ε) * (2 - 2 * s * t)) :
    separatedRatio s t ≤ (1 - ε) ^ 2 := by
  have hA := radiusSq_nonneg hs
  have hB := radiusSq_nonneg ht
  have hV : 0 ≤ 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) := by
    positivity
  have hright : 0 ≤ (1 - ε) * (2 - 2 * s * t) := by
    have : 0 ≤ 1 - ε := by linarith
    positivity
  have hsq := (sq_le_sq₀ hV hright).mpr hsep
  have hident :
      (2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 =
        4 * (1 - s ^ 2) * (1 - t ^ 2) := by
    rw [show
      (2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 =
        4 * Real.sqrt (1 - s ^ 2) ^ 2 * Real.sqrt (1 - t ^ 2) ^ 2 by ring,
      Real.sq_sqrt hA, Real.sq_sqrt hB]
  rw [hident] at hsq
  unfold separatedRatio
  rw [div_le_iff₀ (sq_pos_of_pos hU)]
  nlinarith

theorem separatedRatio_lt_one
    {s t ε : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hU : 0 < 2 - 2 * s * t)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hsep : 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
      (1 - ε) * (2 - 2 * s * t)) :
    separatedRatio s t < 1 := by
  have hq := separatedRatio_le_sq_one_sub hs ht hU hε hε1 hsep
  have hε0 : 0 ≤ 1 - ε := by linarith
  have hεlt : 1 - ε < 1 := by linarith
  nlinarith

/-- Exact endpoint-safe factorization after up to two derivatives hit each
squared radius.  All exponents of the radii remain natural numbers. -/
theorem separated_tail_factorization
    {u v : ℝ} {m a b : ℕ} (hm : 2 ≤ m)
    (ha : a ≤ 2) (hb : b ≤ 2) :
    (4 : ℝ) ^ m * u ^ (m - a) * v ^ (m - b) =
      16 * (4 * u * v) ^ (m - 2) * u ^ (2 - a) * v ^ (2 - b) := by
  have hma : m - a = (m - 2) + (2 - a) := by omega
  have hmb : m - b = (m - 2) + (2 - b) := by omega
  have hfour : (4 : ℝ) ^ m = 16 * 4 ^ (m - 2) := by
    calc
      (4 : ℝ) ^ m = 4 ^ ((m - 2) + 2) := by congr 1; omega
      _ = 16 * 4 ^ (m - 2) := by rw [pow_add]; ring
  rw [hma, hmb, hfour, pow_add, pow_add]
  simp only [mul_pow]
  ring

/-- The tail numerator is controlled by the square of the angular ratio,
with no division by a vanishing radius. -/
theorem separated_tail_radius_bound
    {u v U : ℝ} {m a b : ℕ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hU : 0 ≤ U)
    (huU : u ≤ U) (hvU : v ≤ U)
    (hm : 2 ≤ m) (ha : a ≤ 2) (hb : b ≤ 2) :
    (4 : ℝ) ^ m * u ^ (m - a) * v ^ (m - b) ≤
      16 * (4 * u * v) ^ (m - 2) * U ^ (4 - a - b) := by
  rw [separated_tail_factorization hm ha hb]
  have hexp : 4 - a - b = (2 - a) + (2 - b) := by omega
  calc
    16 * (4 * u * v) ^ (m - 2) * u ^ (2 - a) * v ^ (2 - b) ≤
        16 * (4 * u * v) ^ (m - 2) * U ^ (2 - a) * U ^ (2 - b) := by
          gcongr
    _ = 16 * (4 * u * v) ^ (m - 2) * U ^ (4 - a - b) := by
      rw [hexp, pow_add]
      ring

/-- Polynomial losses from differentiating four times remain summable
against every separated geometric ratio. -/
theorem summable_separated_polynomial
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
  · have hscaled := hshift.mul_left ‖q‖⁻¹
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

/-- For the manuscript range `0 < α < 2`, the binomial coefficients of
`α/2` have a uniform bound.  The angular moments are bounded by one too. -/
theorem abs_choose_le_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (n : ℕ) : |Ring.choose β n| ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hrec :
          ((n : ℝ) + 1) * Ring.choose β (n + 1) =
            (β - n) * Ring.choose β n := by
        have h := Ring.choose_smul_choose (R := ℝ) β (Nat.le_succ n)
        simp only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.succ_sub,
          Nat.sub_self, Ring.choose_one_right] at h
        simpa [mul_comm] using h
      have hn : 0 < (n : ℝ) + 1 := by positivity
      have hfactor : |β - (n : ℝ)| ≤ (n : ℝ) + 1 := by
        have hn0 : (0 : ℝ) ≤ n := by positivity
        rw [abs_le]
        constructor <;> linarith
      have hnum : |(β - n) * Ring.choose β n| ≤ (n : ℝ) + 1 := by
        rw [abs_mul]
        calc
          |β - (n : ℝ)| * |Ring.choose β n| ≤ |β - (n : ℝ)| * 1 := by
            gcongr
          _ ≤ (n : ℝ) + 1 := by simpa using hfactor
      rw [← hrec] at hnum
      rw [abs_mul, abs_of_pos hn] at hnum
      nlinarith

end BEMOC.Definitive
