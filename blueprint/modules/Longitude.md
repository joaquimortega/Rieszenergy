# `BEMOCFormalization.Longitude` proof guide

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Trapezoid
import BEMOCFormalization.AngularQuadrature
import BEMOCFormalization.GridMultiplicity
import BEMOCFormalization.Geometry
import BEMOCFormalization.EnergyDecomposition

open scoped BigOperators Topology Real
open Filter Set
namespace BEMOC.Definitive

/-- The arithmetic double sum after reducing angular quadrature to gcd/lcm. -/
noncomputable def gcdSum (α : ℝ) (T : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 T, ∑ v ∈ Finset.Icc 1 T,
    (Nat.gcd u v : ℝ) ^ (1 + α) / ((u : ℝ) * v) ^ (α / 2)

/-- The two zeta sums are finite because α>0. -/
def GcdSumBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, gcdSum α T ≤ C * (T : ℝ) ^ 2

/-- Phase-uniform longitude estimate for the actual Diamond energy. -/
def LongitudeBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N,
    |longitudeError α N φ| ≤ C * scale α N


/-! The arithmetic lemmas below adapt the proved divisor majorization from
`legacy/BEMOCFormalization/CrossRingEstimate.lean` to this exact gcd sum. -/

/-! ## Power sums -/

noncomputable def negativePowerSumConstant (a : ℝ) : ℝ :=
  1 + 1 / (1 - a)

theorem negativePowerSumConstant_pos {a : ℝ} (ha1 : a < 1) :
    0 < negativePowerSumConstant a := by
  unfold negativePowerSumConstant
  have hden : 0 < 1 - a := by linarith
  have hinv : 0 < 1 / (1 - a) := one_div_pos.mpr hden
  linarith

theorem sum_range_one_add_rpow_neg_le
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {X : ℕ} (hX : 1 ≤ X) :
    (∑ u ∈ Finset.range X, ((u + 1 : ℕ) : ℝ) ^ (-a)) ≤
      negativePowerSumConstant a * (X : ℝ) ^ (1 - a) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-a)
  have hanti : AntitoneOn f (Set.Icc (1 : ℝ) X) := by
    intro x hx y hy hxy
    dsimp [f]
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx.1) hxy
      (by linarith)
  have hXdecomp : X = (X - 1) + 1 := by omega
  have hend :
      (1 : ℝ) + ((X - 1 : ℕ) : ℝ) = (X : ℝ) := by
    have hNat : 1 + (X - 1) = X := by omega
    exact_mod_cast hNat
  have hanti' : AntitoneOn f
      (Set.Icc (1 : ℝ) ((1 : ℝ) + ((X - 1 : ℕ) : ℝ))) := by
    simpa [hend] using hanti
  have hsumInt := hanti'.sum_le_integral
    (x₀ := (1 : ℝ)) (a := X - 1)
  have hsumSplit :
      (∑ u ∈ Finset.range X, ((u + 1 : ℕ) : ℝ) ^ (-a)) =
        (∑ u ∈ Finset.range (X - 1),
          (((1 : ℝ) + (u + 1 : ℕ)) : ℝ) ^ (-a)) + 1 := by
    rw [hXdecomp, Finset.sum_range_succ']
    norm_num [Nat.cast_add]
    ring_nf
  have hInt :
      (∫ x : ℝ in (1 : ℝ)..X, x ^ (-a)) =
        ((X : ℝ) ^ (1 - a) - 1) / (1 - a) := by
    rw [integral_rpow (a := (1 : ℝ)) (b := (X : ℝ))
      (r := -a) (Or.inl (by linarith))]
    norm_num [Real.one_rpow]
    ring_nf
  have hXpow : 1 ≤ (X : ℝ) ^ (1 - a) := by
    have h1X : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hexp : 0 ≤ 1 - a := by linarith
    have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) h1X hexp
    simpa only [Real.one_rpow] using hpow
  rw [hsumSplit]
  calc
    (∑ u ∈ Finset.range (X - 1),
          (((1 : ℝ) + (u + 1 : ℕ)) : ℝ) ^ (-a)) + 1 ≤
        (∫ x : ℝ in (1 : ℝ)..X, x ^ (-a)) + 1 := by
      exact add_le_add_right (by simpa [f, hend] using hsumInt) 1
    _ = ((X : ℝ) ^ (1 - a) - 1) / (1 - a) + 1 := by rw [hInt]
    _ ≤ negativePowerSumConstant a * (X : ℝ) ^ (1 - a) := by
      unfold negativePowerSumConstant
      have hden : 0 < 1 - a := by linarith
      have hpow0 : 0 ≤ (X : ℝ) ^ (1 - a) := by positivity
      have hinv : 0 < (1 - a)⁻¹ := inv_pos.mpr hden
      rw [div_eq_mul_inv, one_div]
      calc
        ((X : ℝ) ^ (1 - a) - 1) * (1 - a)⁻¹ + 1 =
            (X : ℝ) ^ (1 - a) * (1 - a)⁻¹ +
              1 - (1 - a)⁻¹ := by ring
        _ ≤ (X : ℝ) ^ (1 - a) * (1 - a)⁻¹ +
              (X : ℝ) ^ (1 - a) := by nlinarith
        _ = (1 + (1 - a)⁻¹) * (X : ℝ) ^ (1 - a) := by ring

theorem sum_Icc_rpow_neg_le
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {X : ℕ} (hX : 1 ≤ X) :
    (∑ u ∈ Finset.Icc 1 X, (u : ℝ) ^ (-a)) ≤
      negativePowerSumConstant a * (X : ℝ) ^ (1 - a) := by
  have hEq :
      (∑ u ∈ Finset.Icc 1 X, (u : ℝ) ^ (-a)) =
        ∑ u ∈ Finset.range X, ((u + 1 : ℕ) : ℝ) ^ (-a) := by
    have hsets : Finset.Icc 1 X = Finset.Ico 1 (X + 1) := by
      ext u
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    calc
      (∑ u ∈ Finset.Icc 1 X, (u : ℝ) ^ (-a)) =
          ∑ u ∈ Finset.Ico 1 (X + 1), (u : ℝ) ^ (-a) := by
        rw [hsets]
      _ = ∑ u ∈ Finset.range ((X + 1) - 1),
          ((1 + u : ℕ) : ℝ) ^ (-a) :=
        Finset.sum_Ico_eq_sum_range (fun u : ℕ ↦ (u : ℝ) ^ (-a)) 1 (X + 1)
      _ = ∑ u ∈ Finset.range X, ((u + 1 : ℕ) : ℝ) ^ (-a) := by
        have hsub : X + 1 - 1 = X := by omega
        rw [hsub]
        simp only [add_comm]
  rw [hEq]
  exact sum_range_one_add_rpow_neg_le ha0 ha1 hX

noncomputable def powerSumConstant (α : ℝ) : ℝ :=
  if α < 1 then negativePowerSumConstant (1 - α) else 1

theorem powerSumConstant_pos {α : ℝ} (hα0 : 0 < α) :
    0 < powerSumConstant α := by
  unfold powerSumConstant
  split_ifs with hα1
  · exact negativePowerSumConstant_pos (by linarith)
  · norm_num

theorem sum_Icc_rpow_alpha_sub_one_le
    {α : ℝ} (hα0 : 0 < α) {X : ℕ} (hX : 1 ≤ X) :
    (∑ u ∈ Finset.Icc 1 X, (u : ℝ) ^ (α - 1)) ≤
      powerSumConstant α * (X : ℝ) ^ α := by
  by_cases hα1 : α < 1
  · rw [powerSumConstant, if_pos hα1]
    rw [show α - 1 = -(1 - α) by ring]
    have hsum := sum_Icc_rpow_neg_le (a := 1 - α)
      (by linarith) (by linarith) hX
    convert hsum using 1 ; ring_nf
  · rw [powerSumConstant, if_neg hα1, one_mul]
    have hexp : 0 ≤ α - 1 := by linarith
    calc
      (∑ u ∈ Finset.Icc 1 X, (u : ℝ) ^ (α - 1)) ≤
          ∑ _u ∈ Finset.Icc 1 X, (X : ℝ) ^ (α - 1) := by
        apply Finset.sum_le_sum
        intro u hu
        exact Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast (Finset.mem_Icc.mp hu).2) hexp
      _ = (Finset.Icc 1 X).card * (X : ℝ) ^ (α - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (X : ℝ) * (X : ℝ) ^ (α - 1) := by
        gcongr
        have hcard : (Finset.Icc 1 X).card ≤ X := by
          simp
        exact_mod_cast hcard
      _ = (X : ℝ) ^ α := by
        have hXpos : (0 : ℝ) < X := by
          exact_mod_cast (show 0 < X by omega)
        calc
          (X : ℝ) * (X : ℝ) ^ (α - 1) =
              (X : ℝ) ^ (1 : ℝ) * (X : ℝ) ^ (α - 1) := by
            rw [Real.rpow_one]
          _ = (X : ℝ) ^ ((1 : ℝ) + (α - 1)) :=
            (Real.rpow_add hXpos 1 (α - 1)).symm
          _ = (X : ℝ) ^ α := by ring_nf

/-! ## Divisor majorization of the gcd sum -/

noncomputable def gcdArithmeticWeight (α : ℝ) (q r : ℕ) : ℝ :=
  (Nat.gcd q r : ℝ) ^ (1 + α) *
    (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)

theorem gcdArithmeticWeight_nonneg (α : ℝ) (q r : ℕ) :
    0 ≤ gcdArithmeticWeight α q r := by
  unfold gcdArithmeticWeight
  positivity

private theorem sum_divisible_rpow_neg_eq
    {a : ℝ} {k X : ℕ} (hk : 1 ≤ k) :
    (∑ q ∈ Finset.Icc 1 X with k ∣ q, (q : ℝ) ^ (-a)) =
      (k : ℝ) ^ (-a) *
        ∑ u ∈ Finset.Icc 1 (X / k), (u : ℝ) ^ (-a) := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij
    (s := (Finset.Icc 1 X).filter (fun q ↦ k ∣ q))
    (t := Finset.Icc 1 (X / k))
    (f := fun q : ℕ ↦ (q : ℝ) ^ (-a))
    (g := fun u : ℕ ↦ (k : ℝ) ^ (-a) * (u : ℝ) ^ (-a))
    (fun q hq ↦ q / k) ?_ ?_ ?_ ?_
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hkdvd⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq1, hqX⟩
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_div_iff hk |>.2 (Nat.le_of_dvd hq1 hkdvd)
    · exact (Nat.div_le_div_right hqX)
  · intro q hq r hr hdiv
    have hqk := (Finset.mem_filter.mp hq).2
    have hrk := (Finset.mem_filter.mp hr).2
    have hdiv' : q / k = r / k := by simpa using hdiv
    calc
      q = k * (q / k) := (Nat.mul_div_cancel' hqk).symm
      _ = k * (r / k) := by rw [hdiv']
      _ = r := Nat.mul_div_cancel' hrk
  · intro u hu
    rcases Finset.mem_Icc.mp hu with ⟨hu1, huX⟩
    refine ⟨k * u, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by
      exact Nat.mul_pos (by omega) (by omega), ?_⟩, dvd_mul_right k u⟩, ?_⟩
    · rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hk).mp huX
    · exact Nat.mul_div_cancel_left u hk
  · intro q hq
    have hkdvd := (Finset.mem_filter.mp hq).2
    have hqpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    have hkpos : 0 < k := by omega
    have hkq : k ≤ q := Nat.le_of_dvd hqpos hkdvd
    have hudiv : 0 < q / k := Nat.div_pos hkq hkpos
    have hqeq : q = k * (q / k) := (Nat.mul_div_cancel' hkdvd).symm
    calc
      (q : ℝ) ^ (-a) =
          ((k * (q / k) : ℕ) : ℝ) ^ (-a) := by rw [← hqeq]
      _ = ((k : ℝ) * ((q / k : ℕ) : ℝ)) ^ (-a) := by push_cast; rfl
      _ = (k : ℝ) ^ (-a) * ((q / k : ℕ) : ℝ) ^ (-a) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]

private theorem sum_divisible_rpow_neg_le
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {k X : ℕ} (hk : 1 ≤ k) (hkX : k ≤ X) :
    (∑ q ∈ Finset.Icc 1 X with k ∣ q, (q : ℝ) ^ (-a)) ≤
      negativePowerSumConstant a * (X : ℝ) ^ (1 - a) *
        (k : ℝ) ^ (-(1 : ℝ)) := by
  rw [sum_divisible_rpow_neg_eq hk]
  have hXdiv : 1 ≤ X / k := Nat.one_le_div_iff hk |>.2 hkX
  have hsum := sum_Icc_rpow_neg_le ha0 ha1 hXdiv
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcastDiv : ((X / k : ℕ) : ℝ) ≤ (X : ℝ) / (k : ℝ) := by
    exact Nat.cast_div_le
  have hpowDiv :
      ((X / k : ℕ) : ℝ) ^ (1 - a) ≤
        ((X : ℝ) / (k : ℝ)) ^ (1 - a) :=
    Real.rpow_le_rpow (by positivity) hcastDiv (by linarith)
  calc
    (k : ℝ) ^ (-a) *
          ∑ u ∈ Finset.Icc 1 (X / k), (u : ℝ) ^ (-a) ≤
        (k : ℝ) ^ (-a) *
          (negativePowerSumConstant a *
            ((X / k : ℕ) : ℝ) ^ (1 - a)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (k : ℝ) ^ (-a) *
          (negativePowerSumConstant a *
            ((X : ℝ) / (k : ℝ)) ^ (1 - a)) := by
      have hK0 : 0 ≤ negativePowerSumConstant a :=
        (negativePowerSumConstant_pos ha1).le
      gcongr
    _ = negativePowerSumConstant a * (X : ℝ) ^ (1 - a) *
          (k : ℝ) ^ (-(1 : ℝ)) := by
      rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ X) hkpos.le]
      rw [div_eq_mul_inv, ← Real.rpow_neg hkpos.le]
      calc
        (k : ℝ) ^ (-a) *
            (negativePowerSumConstant a *
              ((X : ℝ) ^ (1 - a) * (k : ℝ) ^ (-(1 - a)))) =
            negativePowerSumConstant a * (X : ℝ) ^ (1 - a) *
              ((k : ℝ) ^ (-a) * (k : ℝ) ^ (-(1 - a))) := by ring
        _ = negativePowerSumConstant a * (X : ℝ) ^ (1 - a) *
              (k : ℝ) ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_add hkpos]
          congr 2
          ring

private theorem gcdArithmeticWeight_le_divisor_sum
    {α : ℝ} {q r X : ℕ}
    (hq : 1 ≤ q) (hqX : q ≤ X) (hr : 1 ≤ r) (_hrX : r ≤ X) :
    gcdArithmeticWeight α q r ≤
      ∑ k ∈ Finset.Icc 1 X,
        if k ∣ q ∧ k ∣ r then
          (k : ℝ) ^ (1 + α) *
            (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
        else 0 := by
  let d := Nat.gcd q r
  have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr <| by
    exact Nat.gcd_ne_zero_left (by omega)
  have hdX : d ≤ X :=
    (Nat.gcd_le_left r hq).trans hqX
  have hdmem : d ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨hdpos, hdX⟩
  have hdvd : d ∣ q ∧ d ∣ r :=
    ⟨Nat.gcd_dvd_left q r, Nat.gcd_dvd_right q r⟩
  unfold gcdArithmeticWeight
  change
    (d : ℝ) ^ (1 + α) * (q : ℝ) ^ (-α / 2) *
        (r : ℝ) ^ (-α / 2) ≤ _
  have hsingle := Finset.single_le_sum
    (s := Finset.Icc 1 X)
    (f := fun k : ℕ ↦
      if k ∣ q ∧ k ∣ r then
        (k : ℝ) ^ (1 + α) *
          (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
      else 0)
    (fun k hk ↦ by
      dsimp
      split_ifs <;> positivity) hdmem
  simpa [hdvd] using hsingle

private theorem divisor_triple_sum_factorization
    (α : ℝ) (X : ℕ) :
    (∑ q ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
      ∑ k ∈ Finset.Icc 1 X,
        if k ∣ q ∧ k ∣ r then
          (k : ℝ) ^ (1 + α) *
            (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
        else 0) =
      ∑ k ∈ Finset.Icc 1 X,
        (k : ℝ) ^ (1 + α) *
          (∑ q ∈ Finset.Icc 1 X with k ∣ q,
            (q : ℝ) ^ (-α / 2)) *
          (∑ r ∈ Finset.Icc 1 X with k ∣ r,
            (r : ℝ) ^ (-α / 2)) := by
  have hswap (q : ℕ) :
      (∑ r ∈ Finset.Icc 1 X, ∑ k ∈ Finset.Icc 1 X,
        if k ∣ q ∧ k ∣ r then
          (k : ℝ) ^ (1 + α) *
            (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
        else 0) =
      ∑ k ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
        if k ∣ q ∧ k ∣ r then
          (k : ℝ) ^ (1 + α) *
            (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
        else 0 :=
    Finset.sum_comm
  simp_rw [hswap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  let D : ℝ := ∑ q ∈ Finset.Icc 1 X with k ∣ q,
    (q : ℝ) ^ (-α / 2)
  have hinner (q : ℕ) :
      (∑ r ∈ Finset.Icc 1 X,
          if k ∣ q ∧ k ∣ r then
            (k : ℝ) ^ (1 + α) *
              (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
          else 0) =
        if k ∣ q then
          (k : ℝ) ^ (1 + α) * (q : ℝ) ^ (-α / 2) * D
        else 0 := by
    by_cases hkq : k ∣ q
    · simp only [hkq, true_and, if_true]
      dsimp [D]
      rw [Finset.mul_sum]
      rw [Finset.sum_filter]
    · simp [hkq]
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  change
    (∑ q ∈ (Finset.Icc 1 X).filter (fun q ↦ k ∣ q),
      (k : ℝ) ^ (1 + α) * (q : ℝ) ^ (-α / 2) * D) =
      (k : ℝ) ^ (1 + α) * D * D
  have hC :
      (∑ q ∈ (Finset.Icc 1 X).filter (fun q ↦ k ∣ q),
        (k : ℝ) ^ (1 + α) * (q : ℝ) ^ (-α / 2)) =
        (k : ℝ) ^ (1 + α) * D := by
    dsimp [D]
    exact (Finset.mul_sum _ _ _).symm
  calc
    (∑ q ∈ (Finset.Icc 1 X).filter (fun q ↦ k ∣ q),
        (k : ℝ) ^ (1 + α) * (q : ℝ) ^ (-α / 2) * D) =
        (∑ q ∈ (Finset.Icc 1 X).filter (fun q ↦ k ∣ q),
          (k : ℝ) ^ (1 + α) * (q : ℝ) ^ (-α / 2)) * D := by
      exact (Finset.sum_mul _ _ D).symm
    _ = (k : ℝ) ^ (1 + α) * D * D := by rw [hC]

noncomputable def gcdArithmeticConstant (α : ℝ) : ℝ :=
  negativePowerSumConstant (α / 2) ^ 2 * powerSumConstant α

theorem gcdArithmeticConstant_pos
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    0 < gcdArithmeticConstant α := by
  unfold gcdArithmeticConstant
  exact mul_pos (sq_pos_of_pos (negativePowerSumConstant_pos (by linarith)))
    (powerSumConstant_pos hα0)

set_option maxHeartbeats 800000 in
theorem gcd_arithmetic_double_sum_le
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {X : ℕ} (hX : 1 ≤ X) :
    (∑ q ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
      gcdArithmeticWeight α q r) ≤
        gcdArithmeticConstant α * (X : ℝ) ^ 2 := by
  let a : ℝ := α / 2
  let K₀ : ℝ := negativePowerSumConstant a
  let K₁ : ℝ := powerSumConstant α
  have ha0 : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hK₀ : 0 < K₀ := negativePowerSumConstant_pos ha1
  have hK₁ : 0 < K₁ := powerSumConstant_pos hα0
  have hmajor :
      (∑ q ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
        gcdArithmeticWeight α q r) ≤
      ∑ q ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
        ∑ k ∈ Finset.Icc 1 X,
          if k ∣ q ∧ k ∣ r then
            (k : ℝ) ^ (1 + α) *
              (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
          else 0 := by
    apply Finset.sum_le_sum
    intro q hq
    apply Finset.sum_le_sum
    intro r hr
    exact gcdArithmeticWeight_le_divisor_sum
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
      (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2
  rw [divisor_triple_sum_factorization] at hmajor
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 X) :
      (k : ℝ) ^ (1 + α) *
          (∑ q ∈ Finset.Icc 1 X with k ∣ q,
            (q : ℝ) ^ (-α / 2)) *
          (∑ r ∈ Finset.Icc 1 X with k ∣ r,
            (r : ℝ) ^ (-α / 2)) ≤
        K₀ ^ 2 * (X : ℝ) ^ (2 - α) *
          (k : ℝ) ^ (α - 1) := by
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hkX⟩
    let D : ℝ := ∑ q ∈ Finset.Icc 1 X with k ∣ q,
      (q : ℝ) ^ (-α / 2)
    let B : ℝ := K₀ * (X : ℝ) ^ (1 - a) *
      (k : ℝ) ^ (-(1 : ℝ))
    have hD :
        D ≤ B := by
      have hraw := sum_divisible_rpow_neg_le ha0 ha1 hk1 hkX
      convert hraw using 1 ; dsimp [D, B, a, K₀] ; ring_nf
    have hD0 : 0 ≤ D := by
      dsimp [D]
      positivity
    have hB0 : 0 ≤ B := by
      dsimp [B]
      positivity
    have hsq : D * D ≤ B * B := by
      exact mul_le_mul hD hD hD0 hB0
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    change (k : ℝ) ^ (1 + α) * D * D ≤ _
    calc
      (k : ℝ) ^ (1 + α) * D * D =
          (k : ℝ) ^ (1 + α) * (D * D) := by ring
      _ ≤ (k : ℝ) ^ (1 + α) * (B * B) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = K₀ ^ 2 * (X : ℝ) ^ (2 - α) *
          (k : ℝ) ^ (α - 1) := by
        dsimp [B]
        calc
          (k : ℝ) ^ (1 + α) *
              (K₀ * (X : ℝ) ^ (1 - a) * (k : ℝ) ^ (-(1 : ℝ)) *
                (K₀ * (X : ℝ) ^ (1 - a) *
                  (k : ℝ) ^ (-(1 : ℝ)))) =
              K₀ ^ 2 *
                ((X : ℝ) ^ (1 - a) * (X : ℝ) ^ (1 - a)) *
                (((k : ℝ) ^ (1 + α) * (k : ℝ) ^ (-(1 : ℝ))) *
                  (k : ℝ) ^ (-(1 : ℝ))) := by ring
          _ = K₀ ^ 2 * (X : ℝ) ^ ((1 - a) + (1 - a)) *
                (k : ℝ) ^ (((1 + α) + (-(1 : ℝ))) + (-(1 : ℝ))) := by
            have hXcombine :
                (X : ℝ) ^ (1 - a) * (X : ℝ) ^ (1 - a) =
                  (X : ℝ) ^ ((1 - a) + (1 - a)) :=
              (Real.rpow_add hXpos (1 - a) (1 - a)).symm
            have hkcombine :
                ((k : ℝ) ^ (1 + α) * (k : ℝ) ^ (-(1 : ℝ))) *
                    (k : ℝ) ^ (-(1 : ℝ)) =
                  (k : ℝ) ^
                    (((1 + α) + (-(1 : ℝ))) + (-(1 : ℝ))) := by
              rw [← Real.rpow_add hkpos, ← Real.rpow_add hkpos]
            rw [hXcombine, hkcombine]
          _ = K₀ ^ 2 * (X : ℝ) ^ (2 - α) *
                (k : ℝ) ^ (α - 1) := by
            dsimp [a]
            ring_nf
  calc
    (∑ q ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
        gcdArithmeticWeight α q r) ≤
        ∑ k ∈ Finset.Icc 1 X,
          (k : ℝ) ^ (1 + α) *
            (∑ q ∈ Finset.Icc 1 X with k ∣ q,
              (q : ℝ) ^ (-α / 2)) *
            (∑ r ∈ Finset.Icc 1 X with k ∣ r,
              (r : ℝ) ^ (-α / 2)) := hmajor
    _ ≤ ∑ k ∈ Finset.Icc 1 X,
          K₀ ^ 2 * (X : ℝ) ^ (2 - α) *
            (k : ℝ) ^ (α - 1) :=
      Finset.sum_le_sum hterm
    _ = K₀ ^ 2 * (X : ℝ) ^ (2 - α) *
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ) ^ (α - 1)) := by
      rw [Finset.mul_sum]
    _ ≤ K₀ ^ 2 * (X : ℝ) ^ (2 - α) *
          (K₁ * (X : ℝ) ^ α) := by
      apply mul_le_mul_of_nonneg_left
        (sum_Icc_rpow_alpha_sub_one_le hα0 hX)
      positivity
    _ = gcdArithmeticConstant α * (X : ℝ) ^ 2 := by
      have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
      calc
        K₀ ^ 2 * (X : ℝ) ^ (2 - α) * (K₁ * (X : ℝ) ^ α) =
            (K₀ ^ 2 * K₁) *
              ((X : ℝ) ^ (2 - α) * (X : ℝ) ^ α) := by ring
        _ = (K₀ ^ 2 * K₁) * (X : ℝ) ^ ((2 - α) + α) := by
          rw [Real.rpow_add hXpos]
        _ = gcdArithmeticConstant α * (X : ℝ) ^ 2 := by
          dsimp [gcdArithmeticConstant, K₀, K₁, a]
          ring_nf
          have hrpow :
              (X : ℝ) ^ (2 : ℝ) = (X : ℝ) ^ (2 : ℕ) :=
            Real.rpow_natCast (X : ℝ) 2
          rw [hrpow]


private theorem gcdSum_eq_arithmeticWeight (α : ℝ) (T : ℕ) :
    gcdSum α T =
      ∑ u ∈ Finset.Icc 1 T, ∑ v ∈ Finset.Icc 1 T,
        gcdArithmeticWeight α u v := by
  unfold gcdSum gcdArithmeticWeight
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hu0 : 0 ≤ (u : ℝ) := by positivity
  have hv0 : 0 ≤ (v : ℝ) := by positivity
  rw [Real.mul_rpow hu0 hv0]
  rw [show -α / 2 = -(α / 2) by ring]
  rw [Real.rpow_neg hu0, Real.rpow_neg hv0]
  rw [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem gcd_sum_bound_lt_two {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    GcdSumBound α := by
  refine ⟨gcdArithmeticConstant α, gcdArithmeticConstant_pos hα0 hα2, ?_⟩
  intro T
  by_cases hT : 1 ≤ T
  · rw [gcdSum_eq_arithmeticWeight]
    exact gcd_arithmetic_double_sum_le hα0 hα2 hT
  · have : T = 0 := by omega
    subst T
    simp [gcdSum]


private theorem gcdArithmeticWeight_eq_ratio (α : ℝ) {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) :
    gcdArithmeticWeight α q r =
      (Nat.gcd q r : ℝ) *
      ((Nat.gcd q r : ℝ) / q) ^ (α / 2) *
      ((Nat.gcd q r : ℝ) / r) ^ (α / 2) := by
  have hd0 : 0 < (Nat.gcd q r : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left r hq
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  unfold gcdArithmeticWeight
  rw [Real.div_rpow hd0.le hq0.le, Real.div_rpow hd0.le hr0.le]
  rw [show 1 + α = 1 + α / 2 + α / 2 by ring]
  rw [Real.rpow_add hd0, Real.rpow_add hd0, Real.rpow_one]
  rw [show -α / 2 = -(α / 2) by ring]
  rw [Real.rpow_neg hq0.le, Real.rpow_neg hr0.le]
  ring

private theorem gcdArithmeticWeight_mono {α β : ℝ} (hβα : β ≤ α)
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    gcdArithmeticWeight α q r ≤ gcdArithmeticWeight β q r := by
  rw [gcdArithmeticWeight_eq_ratio α hq hr,
      gcdArithmeticWeight_eq_ratio β hq hr]
  have hd0 : 0 < (Nat.gcd q r : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left r hq
  have hdq : Nat.gcd q r ≤ q := Nat.gcd_le_left r hq
  have hdr : Nat.gcd q r ≤ r := Nat.gcd_le_right r hr
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hx0 : 0 < (Nat.gcd q r : ℝ) / q := div_pos hd0 hq0
  have hy0 : 0 < (Nat.gcd q r : ℝ) / r := div_pos hd0 hr0
  have hx1 : (Nat.gcd q r : ℝ) / q ≤ 1 := by
    apply (div_le_one hq0).2
    exact_mod_cast hdq
  have hy1 : (Nat.gcd q r : ℝ) / r ≤ 1 := by
    apply (div_le_one hr0).2
    exact_mod_cast hdr
  have hpowx := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith : β / 2 ≤ α / 2)
  have hpowy := Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (by linarith : β / 2 ≤ α / 2)
  have hnonnegx : 0 ≤ ((Nat.gcd q r : ℝ) / q) ^ (α / 2) := by positivity
  have hnonnegy : 0 ≤ ((Nat.gcd q r : ℝ) / r) ^ (β / 2) := by positivity
  calc
    (Nat.gcd q r : ℝ) * ((Nat.gcd q r : ℝ) / q) ^ (α / 2) *
      ((Nat.gcd q r : ℝ) / r) ^ (α / 2) ≤
        (Nat.gcd q r : ℝ) * ((Nat.gcd q r : ℝ) / q) ^ (β / 2) *
      ((Nat.gcd q r : ℝ) / r) ^ (α / 2) := by
        gcongr
    _ ≤ (Nat.gcd q r : ℝ) * ((Nat.gcd q r : ℝ) / q) ^ (β / 2) *
      ((Nat.gcd q r : ℝ) / r) ^ (β / 2) := by
        gcongr

private theorem gcdSum_mono {α β : ℝ} (hβα : β ≤ α) (T : ℕ) :
    gcdSum α T ≤ gcdSum β T := by
  rw [gcdSum_eq_arithmeticWeight, gcdSum_eq_arithmeticWeight]
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro r hr
  exact gcdArithmeticWeight_mono hβα (Finset.mem_Icc.mp hq).1
    (Finset.mem_Icc.mp hr).1

theorem gcd_sum_bound {α : ℝ} (hα0 : 0 < α) : GcdSumBound α := by
  by_cases hα2 : α < 2
  · exact gcd_sum_bound_lt_two hα0 hα2
  · have hone := gcd_sum_bound_lt_two (α := 1) (by norm_num) (by norm_num)
    obtain ⟨C, hC, hbound⟩ := hone
    refine ⟨C, hC, ?_⟩
    intro T
    exact (gcdSum_mono (β := 1) (by linarith) T).trans (hbound T)

/-! ## Geometric angular kernel for the actual polygon vertices -/

private theorem parallelPoint_dist_sq {s t θ φ : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    dist (parallelPoint s θ hs) (parallelPoint t φ ht) ^ 2 =
      2 - 2 * s * t -
        2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * Real.cos (θ - φ) := by
  have hrs : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hrt : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  change dist (parallelVector s θ) (parallelVector t φ) ^ 2 = _
  rw [EuclideanSpace.dist_eq]
  have hsum : 0 ≤ ∑ i : Fin 3,
      dist (parallelVector s θ i) (parallelVector t φ i) ^ 2 := by positivity
  rw [Real.sq_sqrt hsum]
  simp [parallelPoint, parallelVector, Fin.sum_univ_succ, Real.dist_eq,
    sq_abs, Real.sq_sqrt hrs, Real.sq_sqrt hrt, Real.cos_sub]
  ring_nf
  rw [Real.sq_sqrt hrs, Real.sq_sqrt hrt]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]

private theorem angular_coefficients {s t : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ∧
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
        2 - 2 * s * t := by
  have hrs : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hrt : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hB : 0 ≤ 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) := by
    positivity
  have hA : 0 ≤ 2 - 2 * s * t := by
    have hst : s * t ≤ 1 := by
      calc
        s * t ≤ |s * t| := le_abs_self _
        _ = |s| * |t| := abs_mul s t
        _ ≤ 1 * 1 := mul_le_mul (abs_le.mpr hs) (abs_le.mpr ht)
          (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    linarith
  constructor
  · exact hB
  · have hsq :
        (2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 ≤
          (2 - 2 * s * t) ^ 2 := by
        nlinarith [Real.sq_sqrt hrs, Real.sq_sqrt hrt, sq_nonneg (s - t)]
    nlinarith

private noncomputable def ringPairDiscreteEnergy (α : ℝ) (N : ℕ)
    (φ : Phases N) (j k : RingIndex N) : ℝ :=
  ∑ i : Fin (population N (j.val + 1)),
    ∑ l : Fin (population N (k.val + 1)),
      dist (point N φ ⟨j, i⟩) (point N φ ⟨k, l⟩) ^ α

private theorem point_distance_power_eq_angularKernel
    {α : ℝ} {N : ℕ} (hN : 4 ≤ N) (φ : Phases N)
    (j k : RingIndex N) (i : Fin (population N (j.val + 1)))
    (l : Fin (population N (k.val + 1))) :
    dist (point N φ ⟨j, i⟩) (point N φ ⟨k, l⟩) ^ α =
      angularKernel α
        (2 - 2 * height N (j.val + 1) * height N (k.val + 1))
        (2 * radius N (j.val + 1) * radius N (k.val + 1))
        (φ j - φ k + 2 * Real.pi *
          ((i.val : ℝ) / population N (j.val + 1) -
            (l.val : ℝ) / population N (k.val + 1))) := by
  let s := height N (j.val + 1)
  let t := height N (k.val + 1)
  let θ := φ j + 2 * Real.pi * (i.val : ℝ) / population N (j.val + 1)
  let ψ := φ k + 2 * Real.pi * (l.val : ℝ) / population N (k.val + 1)
  have hs : s ∈ Set.Icc (-1 : ℝ) 1 :=
    Set.Ioo_subset_Icc_self (height_in_open_unit hN
      (by omega) (by have hj := j.isLt; omega))
  have ht : t ∈ Set.Icc (-1 : ℝ) 1 :=
    Set.Ioo_subset_Icc_self (height_in_open_unit hN
      (by omega) (by have hk := k.isLt; omega))
  rw [point_eq_parallelPoint hN φ ⟨j, i⟩,
    point_eq_parallelPoint hN φ ⟨k, l⟩]
  have hd := parallelPoint_dist_sq hs ht (θ := θ) (φ := ψ)
  change dist (parallelPoint s θ hs) (parallelPoint t ψ ht) ^ α = _
  calc
    dist (parallelPoint s θ hs) (parallelPoint t ψ ht) ^ α =
        (dist (parallelPoint s θ hs) (parallelPoint t ψ ht) ^ 2) ^
          (α / 2) := (distance_sq_rpow_half_alpha _ _).symm
    _ = angularKernel α (2 - 2 * s * t)
          (2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2))
          (θ - ψ) := by rw [hd]; rfl
    _ = _ := by
      change (2 - 2 * s * t -
          2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) *
            Real.cos (θ - ψ)) ^ (α / 2) = _
      have hang : θ - ψ = φ j - φ k + 2 * Real.pi *
          ((i.val : ℝ) / population N (j.val + 1) -
            (l.val : ℝ) / population N (k.val + 1)) := by
        dsimp [θ, ψ]
        ring
      rw [hang]
      rfl



private theorem angularKernel_periodic (α A B : ℝ) :
    Function.Periodic (angularKernel α A B) (2 * Real.pi) := by
  intro θ
  unfold angularKernel
  rw [Real.cos_add_two_pi]

private theorem ringPairDiscreteEnergy_eq_grid {α : ℝ} {N : ℕ}
    (hN : 4 ≤ N) (φ : Phases N) (j k : RingIndex N) :
    ringPairDiscreteEnergy α N φ j k =
      (Nat.gcd (population N (j.val + 1))
        (population N (k.val + 1)) : ℝ) *
      ∑ u : Fin (Nat.lcm (population N (j.val + 1))
        (population N (k.val + 1))),
        angularKernel α
          (2 - 2 * height N (j.val + 1) * height N (k.val + 1))
          (2 * radius N (j.val + 1) * radius N (k.val + 1))
          (φ j - φ k + 2 * Real.pi * (u.val : ℝ) /
            Nat.lcm (population N (j.val + 1))
              (population N (k.val + 1))) := by
  let q := population N (j.val + 1)
  let r := population N (k.val + 1)
  have hq : 0 < q := population_pos hN (by omega)
    (by have hj := j.isLt; omega)
  have hr : 0 < r := population_pos hN (by omega)
    (by have hk := k.isLt; omega)
  let A := 2 - 2 * height N (j.val + 1) * height N (k.val + 1)
  let B := 2 * radius N (j.val + 1) * radius N (k.val + 1)
  let G : ℝ → ℝ := angularKernel α A B
  have hgrid := Grid.grid_multiplicity q r hq hr G
    (angularKernel_periodic α A B) (φ j - φ k)
  unfold ringPairDiscreteEnergy
  simp_rw [point_distance_power_eq_angularKernel hN φ j k]
  simpa [q, r, A, B, G] using hgrid


private theorem generic_pair_grid_error_bound {α C A B phase : ℝ}
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (htrap : ∀ A B : ℝ, 0 ≤ B → B ≤ A →
      ∀ L : ℕ, 1 ≤ L → ∀ φ : ℝ,
        |angularAverage L φ (angularKernel α A B) -
          (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
            angularKernel α A B θ| ≤
          C * B ^ (α / 2) * (L : ℝ) ^ (-1 - α))
    (hB : 0 ≤ B) (hAB : B ≤ A) :
    |(q : ℝ) * r * ((2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * Real.pi, angularKernel α A B θ) -
      (Nat.gcd q r : ℝ) *
        ∑ u : Fin (Nat.lcm q r),
          angularKernel α A B
            (phase + 2 * Real.pi * (u.val : ℝ) / Nat.lcm q r)| ≤
      C * B ^ (α / 2) * (Nat.gcd q r : ℝ) *
        (Nat.lcm q r : ℝ) ^ (-α) := by
  let d := Nat.gcd q r
  let L := Nat.lcm q r
  have hL : 0 < L := Nat.lcm_pos hq hr
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hdr : (0 : ℝ) ≤ d := by positivity
  have hqrd : (q : ℝ) * r = (d : ℝ) * L := by
    exact_mod_cast (Nat.gcd_mul_lcm q r).symm
  have hsum :
      (d : ℝ) * (∑ u : Fin L,
        angularKernel α A B (phase + 2 * Real.pi * (u.val : ℝ) / L)) =
      (d : ℝ) * L * angularAverage L phase (angularKernel α A B) := by
    unfold angularAverage
    field_simp
    ring
  have ht := htrap A B hB hAB L hL phase
  change |(q : ℝ) * r * ((2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * Real.pi, angularKernel α A B θ) -
    (d : ℝ) * (∑ u : Fin L,
      angularKernel α A B (phase + 2 * Real.pi * (u.val : ℝ) / L))| ≤ _
  rw [hqrd, hsum]
  calc
    |(d : ℝ) * L * ((2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * Real.pi, angularKernel α A B θ) -
      (d : ℝ) * L * angularAverage L phase (angularKernel α A B)| =
      (d : ℝ) * L *
        |angularAverage L phase (angularKernel α A B) -
          (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
            angularKernel α A B θ| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg hdr hLr.le), abs_sub_comm]
    _ ≤ (d : ℝ) * L * (C * B ^ (α / 2) * (L : ℝ) ^ (-1 - α)) := by
      exact mul_le_mul_of_nonneg_left ht (mul_nonneg hdr hLr.le)
    _ = C * B ^ (α / 2) * (d : ℝ) * (L : ℝ) ^ (-α) := by
      have hpow : (L : ℝ) * (L : ℝ) ^ (-1 - α) =
          (L : ℝ) ^ (-α) := by
        calc
          (L : ℝ) * (L : ℝ) ^ (-1 - α) =
              (L : ℝ) ^ (1 : ℝ) * (L : ℝ) ^ (-1 - α) := by rw [Real.rpow_one]
          _ = (L : ℝ) ^ ((1 : ℝ) + (-1 - α)) :=
            (Real.rpow_add hLr _ _).symm
          _ = (L : ℝ) ^ (-α) := by ring_nf
      rw [show (d : ℝ) * (L : ℝ) * (C * B ^ (α / 2) *
        (L : ℝ) ^ (-1 - α)) =
        C * B ^ (α / 2) * (d : ℝ) *
          ((L : ℝ) * (L : ℝ) ^ (-1 - α)) by ring, hpow]


private theorem gcd_mul_lcm_rpow_identity {α : ℝ} {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) :
    (Nat.gcd q r : ℝ) * (Nat.lcm q r : ℝ) ^ (-α) =
      (Nat.gcd q r : ℝ) ^ (1 + α) /
        ((q : ℝ) * (r : ℝ)) ^ α := by
  have hd : 0 < (Nat.gcd q r : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left r hq
  have hL : 0 < (Nat.lcm q r : ℝ) := by
    exact_mod_cast Nat.lcm_pos hq hr
  have hprod : (q : ℝ) * (r : ℝ) =
      (Nat.gcd q r : ℝ) * (Nat.lcm q r : ℝ) := by
    exact_mod_cast (Nat.gcd_mul_lcm q r).symm
  rw [hprod, Real.mul_rpow hd.le hL.le, Real.rpow_add hd]
  rw [Real.rpow_one, Real.rpow_neg hL.le]
  field_simp [(Real.rpow_pos_of_pos hd α).ne',
    (Real.rpow_pos_of_pos hL α).ne']
  ring

private theorem gcd_weight_algebra {α : ℝ} {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) :
    (Nat.gcd q r : ℝ) * (Nat.lcm q r : ℝ) ^ (-α) *
        ((q : ℝ) * r) ^ (α / 2) =
      (Nat.gcd q r : ℝ) ^ (1 + α) /
        ((q : ℝ) * r) ^ (α / 2) := by
  have hprod : 0 < (q : ℝ) * r := by positivity
  rw [gcd_mul_lcm_rpow_identity hq hr]
  have hpow : ((q : ℝ) * r) ^ α =
      (((q : ℝ) * r) ^ (α / 2)) ^ 2 := by
    rw [← Real.rpow_mul_natCast hprod.le]
    congr 1
    ring
  rw [hpow]
  have hx : ((q : ℝ) * r) ^ (α / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hprod _).ne'
  field_simp [hx]
  ring


private theorem generic_pair_weight_bound {α C B : ℝ} {M q r : ℕ}
    (hα0 : 0 < α) (hC : 0 ≤ C) (hM : 0 < M)
    (hq : 0 < q) (hr : 0 < r) (hB : 0 ≤ B)
    (hBbound : B ≤ ((q : ℝ) * r) / (M : ℝ) ^ 2) :
    C * B ^ (α / 2) * (Nat.gcd q r : ℝ) *
        (Nat.lcm q r : ℝ) ^ (-α) ≤
      C * (M : ℝ) ^ (-α) *
        ((Nat.gcd q r : ℝ) ^ (1 + α) /
          ((q : ℝ) * r) ^ (α / 2)) := by
  have ha : 0 ≤ α / 2 := by linarith
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hprod : 0 < (q : ℝ) * r := by positivity
  have hBpow := Real.rpow_le_rpow hB hBbound ha
  have hscale : (((q : ℝ) * r) / (M : ℝ) ^ 2) ^ (α / 2) =
      ((q : ℝ) * r) ^ (α / 2) * (M : ℝ) ^ (-α) := by
    rw [Real.div_rpow hprod.le (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ 2)]
    rw [← Real.rpow_natCast (M : ℝ) 2,
      ← Real.rpow_mul hMr.le]
    have hexp : (2 : ℝ) * (α / 2) = α := by ring
    norm_num only [Nat.cast_ofNat]
    rw [hexp, div_eq_mul_inv, Real.rpow_neg hMr.le]
  calc
    C * B ^ (α / 2) * (Nat.gcd q r : ℝ) *
        (Nat.lcm q r : ℝ) ^ (-α) ≤
      C * ((((q : ℝ) * r) / (M : ℝ) ^ 2) ^ (α / 2)) *
        (Nat.gcd q r : ℝ) * (Nat.lcm q r : ℝ) ^ (-α) := by
      gcongr
    _ = C * (M : ℝ) ^ (-α) *
        ((Nat.gcd q r : ℝ) ^ (1 + α) /
          ((q : ℝ) * r) ^ (α / 2)) := by
      rw [hscale]
      rw [show C * (((q : ℝ) * r) ^ (α / 2) * (M : ℝ) ^ (-α)) *
          (Nat.gcd q r : ℝ) * (Nat.lcm q r : ℝ) ^ (-α) =
        C * (M : ℝ) ^ (-α) *
          ((Nat.gcd q r : ℝ) * (Nat.lcm q r : ℝ) ^ (-α) *
            ((q : ℝ) * r) ^ (α / 2)) by ring]
      rw [gcd_weight_algebra hq hr]


private theorem ring_pair_B_bound {N : ℕ} (hN : 4 ≤ N)
    (j k : RingIndex N) :
    2 * radius N (j.val + 1) * radius N (k.val + 1) ≤
      ((population N (j.val + 1) : ℝ) *
        population N (k.val + 1)) / (bandParameter N : ℝ) ^ 2 := by
  let M := bandParameter N
  let ρ := radius N (j.val + 1)
  let σ := radius N (k.val + 1)
  let q := population N (j.val + 1)
  let r := population N (k.val + 1)
  have hM : 0 < M := bandParameter_pos hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hρ : 0 ≤ ρ := Real.sqrt_nonneg _
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  have hq : 2 * (M : ℝ) * ρ ≤ q :=
    (population_radius_comparison hN (by omega)
      (by have hj := j.isLt; omega)).1
  have hr : 2 * (M : ℝ) * σ ≤ r :=
    (population_radius_comparison hN (by omega)
      (by have hk := k.isLt; omega)).1
  have hprod : (2 * (M : ℝ) * ρ) * (2 * (M : ℝ) * σ) ≤
      (q : ℝ) * r :=
    mul_le_mul hq hr (by positivity) (by positivity)
  have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  apply (le_div_iff₀ hM2).2
  dsimp [M, ρ, σ, q, r] at *
  nlinarith


private theorem gcdArithmeticWeight_eq_div {α : ℝ} {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) :
    gcdArithmeticWeight α q r =
      (Nat.gcd q r : ℝ) ^ (1 + α) /
        ((q : ℝ) * r) ^ (α / 2) := by
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hr0 : 0 ≤ (r : ℝ) := by positivity
  unfold gcdArithmeticWeight
  rw [Real.mul_rpow hq0 hr0]
  rw [show -α / 2 = -(α / 2) by ring]
  rw [Real.rpow_neg hq0, Real.rpow_neg hr0]
  field_simp [(Real.rpow_pos_of_pos (by exact_mod_cast hq : (0 : ℝ) < q) (α / 2)).ne',
    (Real.rpow_pos_of_pos (by exact_mod_cast hr : (0 : ℝ) < r) (α / 2)).ne']

private theorem ring_pair_error_bound {α C : ℝ}
    (hα0 : 0 < α) (hC : 0 ≤ C)
    (htrap : ∀ A B : ℝ, 0 ≤ B → B ≤ A →
      ∀ L : ℕ, 1 ≤ L → ∀ φ : ℝ,
        |angularAverage L φ (angularKernel α A B) -
          (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
            angularKernel α A B θ| ≤
          C * B ^ (α / 2) * (L : ℝ) ^ (-1 - α))
    {N : ℕ} (hN : 4 ≤ N) (φ : Phases N) (j k : RingIndex N) :
    |(population N (j.val + 1) : ℝ) * population N (k.val + 1) *
        latitudeKernel α (height N (j.val + 1)) (height N (k.val + 1)) -
      ringPairDiscreteEnergy α N φ j k| ≤
    C * (bandParameter N : ℝ) ^ (-α) *
      gcdArithmeticWeight α (population N (j.val + 1))
        (population N (k.val + 1)) := by
  let q := population N (j.val + 1)
  let r := population N (k.val + 1)
  let s := height N (j.val + 1)
  let t := height N (k.val + 1)
  let A := 2 - 2 * s * t
  let B := 2 * radius N (j.val + 1) * radius N (k.val + 1)
  let M := bandParameter N
  have hq : 0 < q := population_pos hN (by omega)
    (by have hj := j.isLt; omega)
  have hr : 0 < r := population_pos hN (by omega)
    (by have hk := k.isLt; omega)
  have hM : 0 < M := bandParameter_pos hN
  have hs : s ∈ Set.Icc (-1 : ℝ) 1 :=
    Set.Ioo_subset_Icc_self (height_in_open_unit hN
      (by omega) (by have hj := j.isLt; omega))
  have ht : t ∈ Set.Icc (-1 : ℝ) 1 :=
    Set.Ioo_subset_Icc_self (height_in_open_unit hN
      (by omega) (by have hk := k.isLt; omega))
  have hcoeff : 0 ≤ B ∧ B ≤ A := angular_coefficients hs ht
  have hmean : latitudeKernel α s t =
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        angularKernel α A B θ := by rfl
  have hgrid := ringPairDiscreteEnergy_eq_grid (α := α) hN φ j k
  have hraw := generic_pair_grid_error_bound hq hr htrap hcoeff.1 hcoeff.2
    (phase := φ j - φ k)
  dsimp [q, r, A, B, s, t] at hraw
  rw [← hmean, ← hgrid] at hraw
  have hBbound : B ≤ ((q : ℝ) * r) / (M : ℝ) ^ 2 :=
    ring_pair_B_bound hN j k
  have hweight := generic_pair_weight_bound hα0 hC hM hq hr
    hcoeff.1 hBbound
  change |(q : ℝ) * r * latitudeKernel α s t -
    ringPairDiscreteEnergy α N φ j k| ≤ _
  rw [gcdArithmeticWeight_eq_div hq hr]
  exact hraw.trans hweight


private theorem diamondEnergy_eq_sum_ringPairDiscreteEnergy
    (α : ℝ) (N : ℕ) (φ : Phases N) :
    diamondEnergy α N φ =
      ∑ j : RingIndex N, ∑ k : RingIndex N,
        ringPairDiscreteEnergy α N φ j k := by
  unfold diamondEnergy energy ringPairDiscreteEnergy
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]

private theorem population_sum_le_three {N : ℕ} (hN : 4 ≤ N)
    (g : ℕ → ℝ) (hg : ∀ q, 0 ≤ g q) :
    (∑ j : RingIndex N, g (population N (j.val + 1))) ≤
      3 * ∑ q ∈ Finset.Icc 1 (15 * bandParameter N), g q := by
  classical
  let w : RingIndex N → ℕ := fun j ↦ population N (j.val + 1)
  let T := Finset.Icc 1 (15 * bandParameter N)
  have hmaps : ∀ j ∈ (Finset.univ : Finset (RingIndex N)), w j ∈ T := by
    intro j hj
    exact Finset.mem_Icc.mpr
      ⟨population_pos hN (by omega) (by have hj' := j.isLt; omega),
        population_le_fifteen hN (by omega) (by have hj' := j.isLt; omega)⟩
  have hfiber :
      (∑ q ∈ T, ∑ j ∈ (Finset.univ : Finset (RingIndex N))
          with w j = q, g q) =
        ∑ j : RingIndex N, g (w j) :=
    Finset.sum_fiberwise_of_maps_to' hmaps g
  rw [← hfiber]
  calc
    (∑ q ∈ T, ∑ j ∈ (Finset.univ : Finset (RingIndex N))
        with w j = q, g q) ≤
        ∑ q ∈ T, 3 * g q := by
      apply Finset.sum_le_sum
      intro q hq
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast population_multiplicity_le_three N q hN)
        (hg q)
    _ = 3 * ∑ q ∈ T, g q := by rw [Finset.mul_sum]

private theorem population_double_gcd_sum_le
    {α : ℝ} {N : ℕ} (hN : 4 ≤ N) :
    (∑ j : RingIndex N, ∑ k : RingIndex N,
      gcdArithmeticWeight α (population N (j.val + 1))
        (population N (k.val + 1))) ≤
      9 * gcdSum α (15 * bandParameter N) := by
  let T := 15 * bandParameter N
  have hinner (j : RingIndex N) :
      (∑ k : RingIndex N,
        gcdArithmeticWeight α (population N (j.val + 1))
          (population N (k.val + 1))) ≤
        3 * ∑ v ∈ Finset.Icc 1 T,
          gcdArithmeticWeight α (population N (j.val + 1)) v := by
    exact population_sum_le_three hN
      (fun v ↦ gcdArithmeticWeight α (population N (j.val + 1)) v)
      (fun v ↦ gcdArithmeticWeight_nonneg α _ v)
  calc
    (∑ j : RingIndex N, ∑ k : RingIndex N,
        gcdArithmeticWeight α (population N (j.val + 1))
          (population N (k.val + 1))) ≤
      ∑ j : RingIndex N,
        3 * ∑ v ∈ Finset.Icc 1 T,
          gcdArithmeticWeight α (population N (j.val + 1)) v :=
      Finset.sum_le_sum fun j hj ↦ hinner j
    _ = 3 * ∑ v ∈ Finset.Icc 1 T,
          ∑ j : RingIndex N,
            gcdArithmeticWeight α (population N (j.val + 1)) v := by
      rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ 3 * ∑ v ∈ Finset.Icc 1 T,
          (3 * ∑ u ∈ Finset.Icc 1 T,
            gcdArithmeticWeight α u v) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro v hv
        exact population_sum_le_three hN
          (fun u ↦ gcdArithmeticWeight α u v)
          (fun u ↦ gcdArithmeticWeight_nonneg α u v)
      · norm_num
    _ = 9 * gcdSum α T := by
      rw [gcdSum_eq_arithmeticWeight]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      ring_nf

private theorem longitudeError_eq_sum_pair_errors
    (α : ℝ) (N : ℕ) (φ : Phases N) :
    longitudeError α N φ =
      ∑ j : RingIndex N, ∑ k : RingIndex N,
        ((population N (j.val + 1) : ℝ) * population N (k.val + 1) *
          latitudeKernel α (height N (j.val + 1))
            (height N (k.val + 1)) -
          ringPairDiscreteEnergy α N φ j k) := by
  unfold longitudeError ringEnergy
  rw [diamondEnergy_eq_sum_ringPairDiscreteEnergy]
  simp_rw [Finset.sum_sub_distrib]

private theorem M_power_le_scale {α : ℝ} (hα2 : α < 2)
    {N : ℕ} (hN : 4 ≤ N) :
    (bandParameter N : ℝ) ^ (2 - α) ≤ scale α N := by
  let M := bandParameter N
  have hM : 0 ≤ (M : ℝ) := by positivity
  have hM2N : (M : ℝ) ^ 2 ≤ N := by
    have h := (bandParameter_bounds N).1
    change 4 * M ^ 2 ≤ N at h
    exact_mod_cast (by omega : M ^ 2 ≤ N)
  have hβ : 0 ≤ 1 - α / 2 := by linarith
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (M : ℝ) ^ 2)
    hM2N hβ
  unfold scale
  calc
    (M : ℝ) ^ (2 - α) =
        (M : ℝ) ^ ((2 : ℝ) * (1 - α / 2)) := by congr 1; ring
    _ = ((M : ℝ) ^ 2) ^ (1 - α / 2) := by
      rw [Real.rpow_mul hM]
      congr 1
      exact Real.rpow_natCast (M : ℝ) 2
    _ ≤ (N : ℝ) ^ (1 - α / 2) := hpow

private theorem longitude_error_le_gcd_sum {α C : ℝ}
    (hα0 : 0 < α) (hC : 0 ≤ C)
    (htrap : ∀ A B : ℝ, 0 ≤ B → B ≤ A →
      ∀ L : ℕ, 1 ≤ L → ∀ φ : ℝ,
        |angularAverage L φ (angularKernel α A B) -
          (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
            angularKernel α A B θ| ≤
          C * B ^ (α / 2) * (L : ℝ) ^ (-1 - α))
    {N : ℕ} (hN : 4 ≤ N) (φ : Phases N) :
    |longitudeError α N φ| ≤
      C * (bandParameter N : ℝ) ^ (-α) *
        (9 * gcdSum α (15 * bandParameter N)) := by
  let E : RingIndex N → RingIndex N → ℝ := fun j k ↦
    (population N (j.val + 1) : ℝ) * population N (k.val + 1) *
      latitudeKernel α (height N (j.val + 1))
        (height N (k.val + 1)) -
      ringPairDiscreteEnergy α N φ j k
  let W : RingIndex N → RingIndex N → ℝ := fun j k ↦
    gcdArithmeticWeight α (population N (j.val + 1))
      (population N (k.val + 1))
  have hpair (j k : RingIndex N) :
      |E j k| ≤ C * (bandParameter N : ℝ) ^ (-α) * W j k :=
    ring_pair_error_bound hα0 hC htrap hN φ j k
  rw [longitudeError_eq_sum_pair_errors]
  change |∑ j : RingIndex N, ∑ k : RingIndex N, E j k| ≤ _
  calc
    |∑ j : RingIndex N, ∑ k : RingIndex N, E j k| ≤
        ∑ j : RingIndex N, ∑ k : RingIndex N, |E j k| := by
      calc
        _ ≤ ∑ j : RingIndex N, |∑ k : RingIndex N, E j k| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : RingIndex N, ∑ k : RingIndex N, |E j k| := by
          apply Finset.sum_le_sum
          intro j hj
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : RingIndex N, ∑ k : RingIndex N,
          C * (bandParameter N : ℝ) ^ (-α) * W j k := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact hpair j k
    _ = C * (bandParameter N : ℝ) ^ (-α) *
          (∑ j : RingIndex N, ∑ k : RingIndex N, W j k) := by
      simp_rw [Finset.mul_sum]
    _ ≤ C * (bandParameter N : ℝ) ^ (-α) *
          (9 * gcdSum α (15 * bandParameter N)) := by
      apply mul_le_mul_of_nonneg_left
        (population_double_gcd_sum_le hN)
      positivity

/-- The angular discretization error for the actual Diamond configuration is
uniform in every choice of ring phases. -/
theorem longitude_bound {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    LongitudeBound α := by
  obtain ⟨Ct, hCt, htrap⟩ := trapezoid_bound hα0 hα2
  obtain ⟨Cg, hCg, hgcd⟩ := gcd_sum_bound hα0
  refine ⟨2025 * Ct * Cg, by positivity, ?_⟩
  intro N hN φ
  let M := bandParameter N
  have hM : 0 < M := bandParameter_pos hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hscale : (M : ℝ) ^ (2 - α) ≤ scale α N :=
    M_power_le_scale hα2 hN
  have hsum := hgcd (15 * M)
  have hraw := longitude_error_le_gcd_sum hα0 hCt.le htrap hN φ
  have hpow : (M : ℝ) ^ (-α) * (M : ℝ) ^ 2 =
      (M : ℝ) ^ (2 - α) := by
    calc
      (M : ℝ) ^ (-α) * (M : ℝ) ^ 2 =
          (M : ℝ) ^ (-α) * (M : ℝ) ^ (2 : ℝ) := by
            congr 1
            exact (Real.rpow_natCast (M : ℝ) 2).symm
      _ = (M : ℝ) ^ (-α + 2) :=
        (Real.rpow_add hMr (-α) 2).symm
      _ = (M : ℝ) ^ (2 - α) := by ring_nf
  calc
    |longitudeError α N φ| ≤
        Ct * (M : ℝ) ^ (-α) * (9 * gcdSum α (15 * M)) := hraw
    _ ≤ Ct * (M : ℝ) ^ (-α) *
          (9 * (Cg * (15 * M : ℕ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hsum (by norm_num)
      · positivity
    _ = (2025 * Ct * Cg) * (M : ℝ) ^ (2 - α) := by
      push_cast
      rw [mul_pow]
      calc
        Ct * (M : ℝ) ^ (-α) *
            (9 * (Cg * (15 ^ 2 * (M : ℝ) ^ 2))) =
          (2025 * Ct * Cg) *
            ((M : ℝ) ^ (-α) * (M : ℝ) ^ 2) := by ring
        _ = (2025 * Ct * Cg) * (M : ℝ) ^ (2 - α) := by
          rw [hpow]
    _ ≤ (2025 * Ct * Cg) * scale α N := by
      exact mul_le_mul_of_nonneg_left hscale (by positivity)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->

**Status, source, and dependencies.** `Longitude.lean` now proves both `gcd_sum_bound` for every `0<α` and `longitude_bound` for `0<α<2`. The latter inhabits the exact `LongitudeBound α` contract for the actual Diamond point energy and every choice of phases. Its source is `definitive.tex`, Lemma `BalphaN` and its proof at lines 433–548, together with `eq:geometry` and `eq:decomp`. It imports the checked `AngularQuadrature.trapezoid_bound` and `Grid.grid_multiplicity` theorems, plus the proved construction, geometry, and energy definitions through `Geometry` and `EnergyDecomposition`. No unproved proposition contract is assumed in `longitude_bound`. The `LongitudeBound α` definition itself is parameterized for every real α; its proved theorem explicitly requires `0<α` and `α<2`.

**Connection to the actual energy.** The checked proof uses `N≥4`, `M=bandParameter N`, and `RingIndex N=Fin (2M-1)`. `height_in_open_unit` and `point_eq_parallelPoint` remove the unreachable north-pole fallback from every occupied vertex. A locally proved `parallelPoint_dist_sq` computes the squared chordal distance, and `distance_sq_rpow_half_alpha` from `NegativeType` turns it into the angular distance-power kernel. `Grid.grid_multiplicity` then rewrites each ordered vertex-pair sum as gcd times the lcm-grid sum. `diamondEnergy_eq_sum_ringPairDiscreteEnergy` applies `Fintype.sum_sigma` twice and swaps finite sums, so `longitudeError_eq_sum_pair_errors` is the exact manuscript decomposition. The diagonal `j=k` remains present, including self-pairs; no unordered-energy convention enters.

**Distance and pair kernel.** Set `ρ_j=radius N (j+1)`, `A=2-2 h_j h_k`, and `B=2ρ_jρ_k`. Prove `0≤B≤A` by identifying `A-B` as the squared distance between points on the two parallels at a common longitude, or by Cauchy–Schwarz for `(h_j,ρ_j)` and `(h_k,ρ_k)`. Prove the squared Euclidean distance of the two actual vertices is `A-B cos(θ_j-θ_k)`, with `θ_j=φ j+2π i/r_j` and `θ_k=φ k+2π i'/r_k`. This requires the sphere point definitions, trigonometric difference formula, and `dist_eq_norm`. Then use `Real.sqrt_sq_eq_abs`/positive-base real-power identities to relate `dist ^ α` to `(A-B cos(...))^(α/2)`. The same kernel appears definitionally in `latitudeKernel` after unfolding. Establish periodicity of `angularKernel` in its angular argument; with `φ=φ j-φ k`, `GridMultiplicity` converts the vertex double sum into `d * ∑_{u<L} angularKernel α A B (φ+2πu/L)`, where `d=gcd(r_j,r_k)` and `L=lcm(r_j,r_k)`.

**Pair error and critical exponents.** Since `r_j*r_k=d*L`, the ring-pair discrepancy is `d*L` times the difference between the angular integral and `angularAverage L φ`. Apply `TrapezoidBound α`, including its `L=1` and `A=B` cases, to get `C B^(α/2) d L^(-α)`. Use `Nat.gcd_mul_lcm`, positivity of `d,L,r_j,r_k`, and real-power laws to rewrite this as `C B^(α/2) d^(1+α)/(r_j*r_k)^α`. The power `1+α` on the gcd is essential. The manuscript's `eq:geometry` gives `r_j≥c Mρ_j`, or `ρ_j≤r_j/(cM)`; the lower comparison field in `GeometryBounds` has precisely this direction. Because `B=2ρ_jρ_k`, absorb `2^(α/2)c^(-α)` into the constant and obtain the usable weight
`|pairError(j,k)| ≤ C' M^(-α) gcd(r_j,r_k)^(1+α)/(r_j*r_k)^(α/2)`.
All factors raised to negative exponents are positive, including `M`, populations, gcd, and lcm. The constant cannot depend on `N`, rings, or phases. Use the triangle inequality for a finite ordered double sum to pass to `|longitudeError|`.

**Population reduction.** The proved geometry lemmas give `r_j≤15M`, `2Mρ_j≤r_j`, and a population fiber cardinality at most three. `ring_pair_B_bound` uses the second inequality in the required direction to obtain `B=2ρ_jρ_k≤r_jr_k/M²`. The trapezoid estimate, `r_jr_k=gcd(r_j,r_k)lcm(r_j,r_k)`, and real-power algebra yield a pair error bounded by `C_t M^(-α)` times the exact `gcdArithmeticWeight`. `population_sum_le_three` regroups one nonnegative finite sum by population; applying it twice gives the factor nine in `population_double_gcd_sum_le`. The latter sum is exactly `gcdSum α (15M)`, and the proved `gcd_sum_bound` controls it by `C_g(15M)²`. Thus the checked error bound is `C_t C_g · 2025 · M^(2-α)`.

**Checked arithmetic proof of `GcdSumBound`.** The module uses divisor majorization adapted from legacy `CrossRingEstimate.lean`. For `0<α<2`, it bounds each gcd weight by a sum over common divisors, interchanges finite sums, estimates the sum of negative powers over multiples of a divisor, and then bounds `∑_{d≤T}d^(α-1)` by a constant times `T^α`. This gives the required `C T²`. It handles `T=0` separately, since `Icc 1 0` is empty. A real-power identity bridges the legacy weight `gcd^(1+α)*u^(-α/2)*v^(-α/2)` to the exact denominator in `gcdSum`. The final theorem has only `0<α`: for `α≥2`, the weight is pointwise no larger than at `α=1`, since `gcd(u,v)/u` and `gcd(u,v)/v` lie in `(0,1]` and powers of these ratios decrease as the exponent increases. The proven `α=1` bound then applies. This extension matters because the contract itself did not restrict α below two. The manuscript's alternative coprime-factor/zeta argument remains mathematically valid but is not the route implemented here.

The arithmetic proof was ported from legacy `BEMOCFormalization/CrossRingEstimate.lean`, whose `gcd_arithmetic_double_sum_le` has the same growth for a related weight. `gcdArithmeticWeight` and the exact `gcdSum` summand are connected by a proved identity with positive integer bases. The legacy file is outside the current import graph; its unrelated population estimates were not imported. Legacy `CrossRingPair.lean` remains a useful candidate for the later gcd/lcm pair estimate. The factorization approach in manuscript lines 506–533 could replace the port in a later cleanup, but is not needed for the checked theorem.

**Final scale and checks.** `M_power_le_scale` uses `4M²≤N` and `1-α/2>0` to prove `M^(2-α)≤N^(1-α/2)` directly. `longitude_bound` chooses the positive constant `2025 C_t C_g`; its witness does not depend on `N`, ring indices, or phases. The proof covers `N=4`, `M=1`, equal rings, self-pairs, and arbitrary independent phases. The analytic import already handles `B=0`, `A=B`, and `L=1`; `gcd_sum_bound` handles `T=0` even though `15M>0` here. `lake build BEMOCFormalization.Longitude` elaborates the whole module, and the shortcut audit finds no `sorry`, `admit`, custom `axiom`, or `opaque` proof.
