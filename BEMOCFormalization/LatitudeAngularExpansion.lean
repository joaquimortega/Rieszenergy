import BEMOCFormalization.LatitudeUnequalSummand
import BEMOCFormalization.RealBinomialSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual even binomial expansion of the latitude angular average

This module evaluates the generalized binomial series under the angular
integral, removes its odd terms by symmetry, and identifies the remaining
height-dependent factor with `latitudeEvenPowerSummand`.
-/

open MeasureTheory Set

namespace BEMOC

noncomputable section

/-- The normalized cosine moment on the full circle. -/
def normalizedCosineMoment (n : ℕ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos θ ^ n

/-- A term of the generalized binomial series before angular integration. -/
def angularBinomialTerm (β q : ℝ) (n : ℕ) (θ : ℝ) : ℝ :=
  Ring.choose β n * (-q * Real.cos θ) ^ n

theorem continuous_angularBinomialTerm (β q : ℝ) (n : ℕ) :
    Continuous (angularBinomialTerm β q n) := by
  unfold angularBinomialTerm
  fun_prop

theorem summable_angularBinomialTerm (β q θ : ℝ) (hq : |q| < 1) :
    Summable (fun n ↦ angularBinomialTerm β q n θ) := by
  apply summable_real_choose_mul_pow β (-q * Real.cos θ)
  calc
    |-q * Real.cos θ| = |q| * |Real.cos θ| := by rw [abs_mul, abs_neg]
    _ ≤ |q| * 1 := mul_le_mul_of_nonneg_left
      (abs_le.2 ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩) (abs_nonneg q)
    _ < 1 := by simpa using hq

/-- Normal convergence on the angular interval, in the exact form needed
by the interval-integral sum theorem. -/
private theorem summable_restricted_angularBinomialTerm_norm
    (β q : ℝ) (hq : |q| < 1) :
    Summable (fun n : ℕ ↦
      ‖(⟨angularBinomialTerm β q n,
          continuous_angularBinomialTerm β q n⟩ : C(ℝ, ℝ)).restrict
        (⟨uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ :
          TopologicalSpace.Compacts ℝ)‖) := by
  have habs :
      Summable (fun n : ℕ ↦ |Ring.choose β n * |q| ^ n|) := by
    have h := (summable_real_choose_mul_pow β |q|
      (by simpa [abs_abs] using hq)).norm
    simpa [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs] using h
  apply habs.of_nonneg_of_le
  · intro n
    exact norm_nonneg _
  · intro n
    apply (ContinuousMap.norm_le _ (abs_nonneg _)).2
    intro θ
    simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk,
      angularBinomialTerm, Real.norm_eq_abs, abs_mul, abs_pow]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have harg : |-q * Real.cos (θ : ℝ)| ≤ |q| := by
      rw [abs_mul, abs_neg]
      simpa using mul_le_mul_of_nonneg_left
        (abs_le.2 ⟨Real.neg_one_le_cos (θ : ℝ),
          Real.cos_le_one (θ : ℝ)⟩) (abs_nonneg q)
    simpa only [abs_mul, abs_neg, abs_abs] using
      pow_le_pow_left₀ (abs_nonneg _) harg n

/-- The generalized binomial sum may be integrated term by term on the
full angular circle. -/
theorem tsum_intervalIntegral_angularBinomialTerm
    (β q : ℝ) (hq : |q| < 1) :
    ∑' n : ℕ, ∫ θ in (0 : ℝ)..2 * Real.pi,
        angularBinomialTerm β q n θ =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        ∑' n : ℕ, angularBinomialTerm β q n θ := by
  let f : ℕ → C(ℝ, ℝ) := fun n ↦
    ⟨angularBinomialTerm β q n, continuous_angularBinomialTerm β q n⟩
  simpa [f] using
    intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (summable_restricted_angularBinomialTerm_norm β q hq)

/-- Pointwise evaluation of the angular generalized-binomial series. -/
theorem tsum_angularBinomialTerm_eq_rpow
    (β q θ : ℝ) (hq : |q| < 1) :
    ∑' n : ℕ, angularBinomialTerm β q n θ =
      (1 - q * Real.cos θ) ^ β := by
  unfold angularBinomialTerm
  rw [tsum_real_choose_mul_pow_eq_rpow]
  · ring_nf
  · calc
      |-q * Real.cos θ| ≤ |q| := by
        rw [abs_mul, abs_neg]
        simpa using mul_le_mul_of_nonneg_left
          (abs_le.2 ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
          (abs_nonneg q)
      _ < 1 := hq

/-- The normalized angular real-power average is the series of normalized
cosine moments. -/
theorem normalized_angular_rpow_eq_tsum
    (β q : ℝ) (hq : |q| < 1) :
    (1 / (2 * Real.pi)) *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          (1 - q * Real.cos θ) ^ β =
      ∑' n : ℕ,
        Ring.choose β n * (-q) ^ n * normalizedCosineMoment n := by
  have hint :
      (∫ θ in (0 : ℝ)..2 * Real.pi,
          (1 - q * Real.cos θ) ^ β) =
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          ∑' n : ℕ, angularBinomialTerm β q n θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    exact (tsum_angularBinomialTerm_eq_rpow β q θ hq).symm
  rw [hint, ← tsum_intervalIntegral_angularBinomialTerm β q hq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hi :
      (∫ θ in (0 : ℝ)..2 * Real.pi,
          angularBinomialTerm β q n θ) =
        (Ring.choose β n * (-q) ^ n) *
          ∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos θ ^ n := by
    unfold angularBinomialTerm
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    change Ring.choose β n * (-q * Real.cos θ) ^ n =
      Ring.choose β n * (-q) ^ n * Real.cos θ ^ n
    rw [mul_pow]
    ring
  rw [hi]
  unfold normalizedCosineMoment
  ring

/-! ## Removal of the odd angular modes -/

theorem intervalIntegral_cos_pow_odd_two_pi (m : ℕ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos θ ^ (2 * m + 1)) = 0 := by
  let f : ℝ → ℝ := fun θ ↦ Real.cos θ ^ (2 * m + 1)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have h₀π : IntervalIntegrable f volume 0 Real.pi :=
    hf.intervalIntegrable _ _
  have hπ₂π : IntervalIntegrable f volume Real.pi (2 * Real.pi) :=
    hf.intervalIntegrable _ _
  have hshift :
      (∫ θ in Real.pi..2 * Real.pi, f θ) =
        -(∫ θ in (0 : ℝ)..Real.pi, f θ) := by
    have htranslate :=
      intervalIntegral.integral_comp_add_right
        (a := (0 : ℝ)) (b := Real.pi) f Real.pi
    have hend : Real.pi + Real.pi = 2 * Real.pi := by ring
    rw [zero_add, hend] at htranslate
    calc
      (∫ θ in Real.pi..2 * Real.pi, f θ) =
          ∫ θ in (0 : ℝ)..Real.pi, f (θ + Real.pi) := htranslate.symm
      _ = ∫ θ in (0 : ℝ)..Real.pi, -f θ := by
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp [f]
        rw [Real.cos_add_pi]
        exact (odd_two_mul_add_one m).neg_pow _
      _ = -(∫ θ in (0 : ℝ)..Real.pi, f θ) := by
        rw [intervalIntegral.integral_neg]
  change (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) = 0
  rw [← intervalIntegral.integral_add_adjacent_intervals h₀π hπ₂π,
    hshift, add_neg_cancel]

theorem normalizedCosineMoment_odd (m : ℕ) :
    normalizedCosineMoment (2 * m + 1) = 0 := by
  unfold normalizedCosineMoment
  rw [intervalIntegral_cos_pow_odd_two_pi, mul_zero]

theorem abs_normalizedCosineMoment_le_one (n : ℕ) :
    |normalizedCosineMoment n| ≤ 1 := by
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hint :
      ‖∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos θ ^ n‖ ≤
        1 * |2 * Real.pi - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ _
    simp only [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _)
      (abs_le.2 ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
  unfold normalizedCosineMoment
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hpi)]
  have habs : |2 * Real.pi - 0| = 2 * Real.pi := by
    rw [sub_zero, abs_of_pos hpi]
  rw [habs, one_mul] at hint
  change
    1 / (2 * Real.pi) *
        |∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos θ ^ n| ≤ 1
  rw [Real.norm_eq_abs] at hint
  calc
    1 / (2 * Real.pi) * |∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.cos θ ^ n| ≤
        1 / (2 * Real.pi) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (one_div_nonneg.mpr hpi.le)
    _ = 1 := by field_simp

theorem summable_normalized_angular_moment_series
    (β q : ℝ) (hq : |q| < 1) :
    Summable (fun n : ℕ ↦
      Ring.choose β n * (-q) ^ n * normalizedCosineMoment n) := by
  have hbase :=
    (summable_real_choose_mul_pow β |q|
      (by simpa [abs_abs] using hq)).norm
  apply Summable.of_norm_bounded
    (fun n : ℕ ↦ ‖Ring.choose β n * |q| ^ n‖) hbase
  intro n
  simp only [norm_mul, norm_pow, norm_neg, Real.norm_eq_abs, abs_abs]
  change
    |Ring.choose β n| * |q| ^ n * |normalizedCosineMoment n| ≤
      |Ring.choose β n| * |q| ^ n
  calc
    |Ring.choose β n| * |q| ^ n * |normalizedCosineMoment n| ≤
        |Ring.choose β n| * |q| ^ n * 1 := by
      gcongr
      exact abs_normalizedCosineMoment_le_one n
    _ = |Ring.choose β n| * |q| ^ n := by ring

/-- After angular integration the generalized binomial expansion contains
only its even modes. -/
theorem normalized_angular_rpow_eq_even_tsum
    (β q : ℝ) (hq : |q| < 1) :
    (1 / (2 * Real.pi)) *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          (1 - q * Real.cos θ) ^ β =
      ∑' m : ℕ,
        Ring.choose β (2 * m) * q ^ (2 * m) *
          normalizedCosineMoment (2 * m) := by
  let f : ℕ → ℝ := fun n ↦
    Ring.choose β n * (-q) ^ n * normalizedCosineMoment n
  have hf : Summable f := summable_normalized_angular_moment_series β q hq
  have he : Summable (fun m ↦ f (2 * m)) :=
    hf.comp_injective (fun _ _ h ↦ by omega)
  have ho : Summable (fun m ↦ f (2 * m + 1)) :=
    hf.comp_injective (fun _ _ h ↦ by omega)
  rw [normalized_angular_rpow_eq_tsum β q hq]
  rw [← tsum_even_add_odd he ho]
  have hodd : (∑' m : ℕ, f (2 * m + 1)) = 0 := by
    have hz : (fun m : ℕ ↦ f (2 * m + 1)) = 0 := by
      funext m
      simp [f, normalizedCosineMoment_odd]
    rw [hz]
    exact tsum_zero
  rw [hodd, add_zero]
  apply tsum_congr
  intro m
  dsimp [f]
  rw [(even_two_mul m).neg_pow]

/-! ## The even expansion in the original latitude variables -/

theorem angularKernelB_sq_eq_four_radiusSq
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    angularKernelB s t ^ 2 =
      4 * (1 - s ^ 2) * (1 - t ^ 2) := by
  have hu : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hv : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  unfold angularKernelB
  rw [show
      (2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 =
        4 * Real.sqrt (1 - s ^ 2) ^ 2 *
          Real.sqrt (1 - t ^ 2) ^ 2 by ring,
    Real.sq_sqrt hu, Real.sq_sqrt hv]

theorem angularKernelB_even_pow_eq
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) (m : ℕ) :
    angularKernelB s t ^ (2 * m) =
      (4 : ℝ) ^ m * (1 - s ^ 2) ^ m * (1 - t ^ 2) ^ m := by
  rw [pow_mul, angularKernelB_sq_eq_four_radiusSq hs ht, mul_pow, mul_pow]

private theorem rpow_mul_div_even_pow
    {A B β : ℝ} (hA : 0 < A) (m : ℕ) :
    A ^ β * (B / A) ^ (2 * m) =
      A ^ (β - 2 * (m : ℝ)) * B ^ (2 * m) := by
  rw [div_pow]
  have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by norm_num
  have hr := Real.rpow_sub_natCast hA.ne' β (2 * m)
  rw [hcast] at hr
  rw [hr]
  field_simp [pow_ne_zero _ hA.ne']

/-- The actual latitude kernel equals the even series (5.6).  The
hypothesis is deliberately stated with the local ratio `|B/A|<1`; the
unequal, opposite, and central geometry modules provide uniform numerical
instances of it. -/
theorem latitudeKernel_eq_evenPowerSeries
    {α s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 0 < angularKernelA s t)
    (hq : |angularKernelB s t / angularKernelA s t| < 1) :
    latitudeKernel α s t =
      ∑' m : ℕ,
        (Ring.choose (α / 2) (2 * m) *
          normalizedCosineMoment (2 * m)) *
          latitudeEvenPowerSummand α m s t := by
  let A := angularKernelA s t
  let B := angularKernelB s t
  let β := α / 2
  have hfactor :
      (∫ θ in (0 : ℝ)..2 * Real.pi,
          (A - B * Real.cos θ) ^ β) =
        A ^ β * ∫ θ in (0 : ℝ)..2 * Real.pi,
          (1 - (B / A) * Real.cos θ) ^ β := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    have hsecond : 0 < 1 - (B / A) * Real.cos θ := by
      have hc : |(B / A) * Real.cos θ| < 1 := lt_of_le_of_lt
        (by
          rw [abs_mul]
          simpa using mul_le_mul_of_nonneg_left
            (abs_le.2 ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
            (abs_nonneg (B / A)))
        hq
      exact sub_pos.mpr (lt_of_le_of_lt (le_abs_self _) hc)
    have hprod : A - B * Real.cos θ =
        A * (1 - (B / A) * Real.cos θ) := by
      field_simp [hA.ne']
    change (A - B * Real.cos θ) ^ β =
      A ^ β * (1 - B / A * Real.cos θ) ^ β
    rw [hprod, Real.mul_rpow hA.le hsecond.le]
  rw [latitudeKernel_eq_A_B_interval]
  change
    (1 / (2 * Real.pi)) *
      (∫ θ in (0 : ℝ)..2 * Real.pi, (A - B * Real.cos θ) ^ β) = _
  rw [hfactor]
  rw [show (1 / (2 * Real.pi)) *
      (A ^ β * ∫ θ in (0 : ℝ)..2 * Real.pi,
        (1 - B / A * Real.cos θ) ^ β) =
      A ^ β * ((1 / (2 * Real.pi)) *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          (1 - (B / A) * Real.cos θ) ^ β) by ring]
  rw [normalized_angular_rpow_eq_even_tsum β (B / A) hq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  dsimp [A, B, β]
  unfold latitudeEvenPowerSummand
  rw [show
      angularKernelA s t ^ (α / 2) *
        (Ring.choose (α / 2) (2 * m) *
          (angularKernelB s t / angularKernelA s t) ^ (2 * m) *
          normalizedCosineMoment (2 * m)) =
        (Ring.choose (α / 2) (2 * m) *
          normalizedCosineMoment (2 * m)) *
          (angularKernelA s t ^ (α / 2) *
            (angularKernelB s t / angularKernelA s t) ^ (2 * m)) by ring]
  rw [rpow_mul_div_even_pow hA m,
    angularKernelB_even_pow_eq hs ht m]
  ring

end

end BEMOC
