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


end BEMOC.Definitive
