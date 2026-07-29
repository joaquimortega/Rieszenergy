import BEMOCFormalization.CrossRingKernel

/-!
# Fourier decay of the angular cusp

The critical estimate is obtained from a first-order recurrence for
`∫₀^π sin(x)^α cos(2 n x) dx`.  It uses only one integration by parts,
with `sin(x)^(α+1)`; this remains continuously differentiable at the
endpoints for every `α > 0`.
-/

open scoped BigOperators Topology Real
open Filter Set Complex MeasureTheory

namespace BEMOC

/-- Cosine moments of the sine-power profile on the half circle. -/
noncomputable def sinePowerCosMoment (α : ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ in (0)..Real.pi,
    Real.sin x ^ α * Real.cos (2 * (n : ℝ) * x)

theorem continuous_sinePowerCosMoment_integrand
    {α : ℝ} (hα : 0 ≤ α) (n : ℕ) :
    Continuous (fun x : ℝ ↦
      Real.sin x ^ α * Real.cos (2 * (n : ℝ) * x)) := by
  exact (Real.continuous_sin.rpow_const (fun _ ↦ Or.inr hα)).mul
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))

theorem intervalIntegrable_sinePowerCosMoment
    {α : ℝ} (hα : 0 ≤ α) (n : ℕ) :
    IntervalIntegrable
      (fun x : ℝ ↦ Real.sin x ^ α * Real.cos (2 * (n : ℝ) * x))
      volume 0 Real.pi :=
  (continuous_sinePowerCosMoment_integrand hα n).intervalIntegrable _ _

/-- First-order recurrence for the sine-power cosine moments. -/
theorem sinePowerCosMoment_succ
    {α : ℝ} (hα : 0 < α) (n : ℕ) :
    (α + 2 * (n : ℝ) + 2) * sinePowerCosMoment α (n + 1) =
      (2 * (n : ℝ) - α) * sinePowerCosMoment α n := by
  let u : ℝ → ℝ := fun x ↦ Real.sin x ^ (α + 1)
  let u' : ℝ → ℝ := fun x ↦
    (α + 1) * Real.sin x ^ α * Real.cos x
  let m : ℝ := 2 * (n : ℝ) + 1
  let v : ℝ → ℝ := fun x ↦ Real.cos (m * x)
  let v' : ℝ → ℝ := fun x ↦ -m * Real.sin (m * x)
  have hu : ∀ x : ℝ, HasDerivAt u (u' x) x := by
    intro x
    dsimp [u, u']
    convert (Real.hasDerivAt_sin x).rpow_const
      (Or.inr (by linarith : 1 ≤ α + 1)) using 1 ; ring_nf
  have hv : ∀ x : ℝ, HasDerivAt v (v' x) x := by
    intro x
    dsimp [v, v', m]
    convert (Real.hasDerivAt_cos (m * x)).comp x
      ((hasDerivAt_id x).const_mul m) using 1 ; ring
  have hu'int : IntervalIntegrable u' volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    dsimp [u']
    simpa only [mul_assoc] using
      (continuous_const.mul
        ((Real.continuous_sin.rpow_const (fun _ ↦ Or.inr hα.le)).mul
          Real.continuous_cos))
  have hv'int : IntervalIntegrable v' volume 0 Real.pi := by
    dsimp [v', m]
    exact (continuous_const.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ hu x) (fun x _ ↦ hv x) hu'int hv'int
  have hboundary : u Real.pi * v Real.pi - u 0 * v 0 = 0 := by
    dsimp [u]
    simp [Real.zero_rpow (by linarith : α + 1 ≠ 0)]
  rw [hboundary, zero_sub] at hparts
  have hsinpow (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
      Real.sin x ^ (α + 1) =
        Real.sin x ^ α * Real.sin x := by
    have hs : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2
    rw [Real.rpow_add_of_nonneg hs hα.le (by norm_num), Real.rpow_one]
  have hleft :
      (∫ x : ℝ in (0)..Real.pi, u x * v' x) =
        (-m / 2) *
          (sinePowerCosMoment α n - sinePowerCosMoment α (n + 1)) := by
    calc
      (∫ x : ℝ in (0)..Real.pi, u x * v' x) =
          ∫ x : ℝ in (0)..Real.pi,
            (-m / 2) *
              (Real.sin x ^ α * Real.cos (2 * (n : ℝ) * x) -
                Real.sin x ^ α *
                  Real.cos (2 * ((n + 1 : ℕ) : ℝ) * x)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hx' : x ∈ Set.Icc (0 : ℝ) Real.pi := by
              simpa only [Set.uIcc_of_le Real.pi_pos.le] using hx
            dsimp [u, v', m]
            rw [hsinpow x hx']
            have htrig := Real.two_mul_sin_mul_sin x ((2 * (n : ℝ) + 1) * x)
            rw [show x - (2 * (n : ℝ) + 1) * x =
                -(2 * (n : ℝ) * x) by ring,
              show x + (2 * (n : ℝ) + 1) * x =
                2 * ((n + 1 : ℕ) : ℝ) * x by push_cast; ring,
              Real.cos_neg] at htrig
            calc
              (Real.sin x ^ α * Real.sin x) *
                  (-(2 * (n : ℝ) + 1) *
                    Real.sin ((2 * (n : ℝ) + 1) * x)) =
                  (-(2 * (n : ℝ) + 1) / 2) * Real.sin x ^ α *
                    (2 * Real.sin x *
                      Real.sin ((2 * (n : ℝ) + 1) * x)) := by ring
              _ = _ := by rw [htrig]; ring
      _ = (-m / 2) *
          (sinePowerCosMoment α n - sinePowerCosMoment α (n + 1)) := by
            rw [intervalIntegral.integral_const_mul,
              intervalIntegral.integral_sub
                (intervalIntegrable_sinePowerCosMoment hα.le n)
                (intervalIntegrable_sinePowerCosMoment hα.le (n + 1))]
            rfl
  have hright :
      (∫ x : ℝ in (0)..Real.pi, u' x * v x) =
        ((α + 1) / 2) *
          (sinePowerCosMoment α n + sinePowerCosMoment α (n + 1)) := by
    calc
      (∫ x : ℝ in (0)..Real.pi, u' x * v x) =
          ∫ x : ℝ in (0)..Real.pi,
            ((α + 1) / 2) *
              (Real.sin x ^ α * Real.cos (2 * (n : ℝ) * x) +
                Real.sin x ^ α *
                  Real.cos (2 * ((n + 1 : ℕ) : ℝ) * x)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            dsimp [u', v, m]
            have htrig :=
              Real.two_mul_cos_mul_cos x ((2 * (n : ℝ) + 1) * x)
            rw [show x - (2 * (n : ℝ) + 1) * x =
                -(2 * (n : ℝ) * x) by ring,
              show x + (2 * (n : ℝ) + 1) * x =
                2 * ((n + 1 : ℕ) : ℝ) * x by push_cast; ring,
              Real.cos_neg] at htrig
            calc
              (α + 1) * Real.sin x ^ α * Real.cos x *
                  Real.cos ((2 * (n : ℝ) + 1) * x) =
                  ((α + 1) / 2) * Real.sin x ^ α *
                    (2 * Real.cos x *
                      Real.cos ((2 * (n : ℝ) + 1) * x)) := by ring
              _ = _ := by rw [htrig]; ring
      _ = ((α + 1) / 2) *
          (sinePowerCosMoment α n + sinePowerCosMoment α (n + 1)) := by
            rw [intervalIntegral.integral_const_mul,
              intervalIntegral.integral_add
                (intervalIntegrable_sinePowerCosMoment hα.le n)
                (intervalIntegrable_sinePowerCosMoment hα.le (n + 1))]
            rfl
  rw [hleft, hright] at hparts
  dsimp [m] at hparts
  nlinarith

/-! ## Unit-period chord coefficients -/

noncomputable def unitChordCosCoeff (α : ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ in (0)..1,
    (2 * Real.sin (Real.pi * x)) ^ α *
      Real.cos (2 * Real.pi * (n : ℝ) * x)

noncomputable def unitChordSinCoeff (α : ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ in (0)..1,
    (2 * Real.sin (Real.pi * x)) ^ α *
      Real.sin (2 * Real.pi * (n : ℝ) * x)

theorem unitChordSinCoeff_eq_zero {α : ℝ} (_hα : 0 < α) (n : ℕ) :
    unitChordSinCoeff α n = 0 := by
  let f : ℝ → ℝ := fun x ↦
    (2 * Real.sin (Real.pi * x)) ^ α *
      Real.sin (2 * Real.pi * (n : ℝ) * x)
  have hreflect (x : ℝ) :
      f (1 - x) = -f x := by
    dsimp [f]
    rw [show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring,
      Real.sin_pi_sub]
    rw [show 2 * Real.pi * (n : ℝ) * (1 - x) =
        n * (2 * Real.pi) - (2 * Real.pi * (n : ℝ) * x) by
          ring,
      Real.sin_nat_mul_two_pi_sub]
    ring
  have hchange := intervalIntegral.integral_comp_sub_left f 1
    (a := (0 : ℝ)) (b := 1)
  norm_num only [sub_self, sub_zero] at hchange
  have hneg :
      (∫ x : ℝ in (0)..1, f (1 - x)) =
        -(∫ x : ℝ in (0)..1, f x) := by
    calc
      _ = ∫ x : ℝ in (0)..1, -f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hreflect x
      _ = _ := intervalIntegral.integral_neg
  have : (∫ x : ℝ in (0)..1, f x) = 0 := by linarith
  simpa [unitChordSinCoeff, f] using this

theorem unitChordCosCoeff_eq_sinePowerCosMoment
    {α : ℝ} (_hα : 0 < α) (n : ℕ) :
    unitChordCosCoeff α n =
      (2 : ℝ) ^ α / Real.pi * sinePowerCosMoment α n := by
  let g : ℝ → ℝ := fun y ↦
    Real.sin y ^ α * Real.cos (2 * (n : ℝ) * y)
  have hchange := intervalIntegral.integral_comp_mul_left g Real.pi_ne_zero
    (a := (0 : ℝ)) (b := 1)
  norm_num only [mul_zero, mul_one, one_div] at hchange
  calc
    unitChordCosCoeff α n =
        ∫ x : ℝ in (0)..1, (2 : ℝ) ^ α * g (Real.pi * x) := by
      rw [unitChordCosCoeff]
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
        simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      dsimp [g]
      have hs : 0 ≤ Real.sin (Real.pi * x) :=
        Real.sin_nonneg_of_nonneg_of_le_pi
          (mul_nonneg Real.pi_pos.le hx'.1)
          (by
            calc
              Real.pi * x ≤ Real.pi * 1 :=
                mul_le_mul_of_nonneg_left hx'.2 Real.pi_pos.le
              _ = Real.pi := by ring)
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hs]
      ring_nf
    _ = (2 : ℝ) ^ α * ∫ x : ℝ in (0)..1, g (Real.pi * x) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (2 : ℝ) ^ α / Real.pi * sinePowerCosMoment α n := by
      rw [hchange]
      dsimp [g, sinePowerCosMoment]
      field_simp [Real.pi_ne_zero]

theorem unitChordCosCoeff_succ
    {α : ℝ} (hα : 0 < α) (n : ℕ) :
    (α + 2 * (n : ℝ) + 2) * unitChordCosCoeff α (n + 1) =
      (2 * (n : ℝ) - α) * unitChordCosCoeff α n := by
  rw [unitChordCosCoeff_eq_sinePowerCosMoment hα,
    unitChordCosCoeff_eq_sinePowerCosMoment hα]
  have hrec := sinePowerCosMoment_succ hα n
  linear_combination ((2 : ℝ) ^ α / Real.pi) * hrec

theorem CircleFourier.chordCoeffIntegral_nat_eq_cosCoeff
    {α : ℝ} (hα : 0 < α) (n : ℕ) :
    CircleFourier.chordCoeffIntegral α (n : ℤ) =
      (unitChordCosCoeff α n : ℂ) := by
  unfold CircleFourier.chordCoeffIntegral
  have hcontCos : IntervalIntegrable
      (fun x : ℝ ↦
        (2 * Real.sin (Real.pi * x)) ^ α *
          Real.cos (2 * Real.pi * (n : ℝ) * x)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact ((continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).rpow_const
        (fun _ ↦ Or.inr hα.le)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hcontSin : IntervalIntegrable
      (fun x : ℝ ↦
        (2 * Real.sin (Real.pi * x)) ^ α *
          Real.sin (2 * Real.pi * (n : ℝ) * x)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact ((continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).rpow_const
        (fun _ ↦ Or.inr hα.le)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hcontCosC : IntervalIntegrable
      (fun x : ℝ ↦
        (((2 * Real.sin (Real.pi * x)) ^ α *
          Real.cos (2 * Real.pi * (n : ℝ) * x) : ℝ) : ℂ)) volume 0 1 := by
    exact ⟨Complex.ofRealCLM.integrable_comp hcontCos.1,
      Complex.ofRealCLM.integrable_comp hcontCos.2⟩
  have hcontSinC : IntervalIntegrable
      (fun x : ℝ ↦
        (((2 * Real.sin (Real.pi * x)) ^ α *
          Real.sin (2 * Real.pi * (n : ℝ) * x) : ℝ) : ℂ)) volume 0 1 := by
    exact ⟨Complex.ofRealCLM.integrable_comp hcontSin.1,
      Complex.ofRealCLM.integrable_comp hcontSin.2⟩
  have hpoint (x : ℝ) :
      Complex.exp (-(2 * Real.pi * Complex.I * (n : ℤ) * x)) *
          ((2 * Real.sin (Real.pi * x)) ^ α : ℝ) =
        ((2 * Real.sin (Real.pi * x)) ^ α *
            Real.cos (2 * Real.pi * (n : ℝ) * x) : ℝ) -
          Complex.I *
            ((2 * Real.sin (Real.pi * x)) ^ α *
              Real.sin (2 * Real.pi * (n : ℝ) * x) : ℝ) := by
    rw [show -(2 * Real.pi * Complex.I * (n : ℤ) * x) =
        ((-(2 * Real.pi * (n : ℝ) * x) : ℝ) : ℂ) * Complex.I by
          push_cast
          ring,
      Complex.exp_mul_I]
    simp only [Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.ofReal_neg,
      Real.cos_neg, Real.sin_neg]
    apply Complex.ext <;> norm_num <;> ring
  calc
    (∫ x : ℝ in (0)..1,
        Complex.exp (-(2 * Real.pi * Complex.I * (n : ℤ) * x)) *
          ((2 * Real.sin (Real.pi * x)) ^ α : ℝ)) =
        ∫ x : ℝ in (0)..1,
          (((2 * Real.sin (Real.pi * x)) ^ α *
              Real.cos (2 * Real.pi * (n : ℝ) * x) : ℝ) -
            Complex.I *
              ((2 * Real.sin (Real.pi * x)) ^ α *
                Real.sin (2 * Real.pi * (n : ℝ) * x) : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hpoint x
    _ = (unitChordCosCoeff α n : ℂ) -
          Complex.I * (unitChordSinCoeff α n : ℂ) := by
      rw [intervalIntegral.integral_sub hcontCosC
        (hcontSinC.const_mul Complex.I),
        intervalIntegral.integral_ofReal,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_ofReal]
      rfl
    _ = (unitChordCosCoeff α n : ℂ) := by
      rw [unitChordSinCoeff_eq_zero hα]
      simp

theorem CircleFourier.fourierCoeff_chordProfile_nat_eq_cosCoeff
    {α : ℝ} (hα : 0 < α) (n : ℕ) :
    fourierCoeff (CircleFourier.chordProfileCircle α hα) (n : ℤ) =
      (unitChordCosCoeff α n : ℂ) := by
  rw [CircleFourier.fourierCoeff_chordProfile_eq_integral hα,
    CircleFourier.chordCoeffIntegral_nat_eq_cosCoeff hα]

theorem CircleFourier.chordFourierCoeffGamma_ne_zero
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {n : ℕ} (hn : 1 ≤ n) :
    CircleFourier.chordFourierCoeffGamma α n ≠ 0 := by
  unfold CircleFourier.chordFourierCoeffGamma
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnum : 0 < Real.Gamma ((n : ℝ) - α / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hden : 0 < Real.Gamma ((n : ℝ) + α / 2 + 1) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hsin : 0 < Real.sin (Real.pi * α / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  have hG : 0 < Real.Gamma (1 + α) :=
    Real.Gamma_pos_of_pos (by linarith)
  exact mul_ne_zero
    (div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hG.ne') hsin.ne')
      Real.pi_ne_zero)
    (div_ne_zero hnum.ne' hden.ne')

theorem CircleFourier.chordFourierCoeffGamma_succ
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {n : ℕ} (hn : 1 ≤ n) :
    (α + 2 * (n : ℝ) + 2) *
        CircleFourier.chordFourierCoeffGamma α (n + 1) =
      (2 * (n : ℝ) - α) *
        CircleFourier.chordFourierCoeffGamma α n := by
  unfold CircleFourier.chordFourierCoeffGamma
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnumArg : (n : ℝ) - α / 2 ≠ 0 := by linarith
  have hdenArg : (n : ℝ) + α / 2 + 1 ≠ 0 := by positivity
  have hden : Real.Gamma ((n : ℝ) + α / 2 + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hdenSucc :
      Real.Gamma (((n + 1 : ℕ) : ℝ) + α / 2 + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [show (((n + 1 : ℕ) : ℝ) - α / 2) =
      ((n : ℝ) - α / 2) + 1 by push_cast; ring,
    Real.Gamma_add_one hnumArg]
  rw [show (((n + 1 : ℕ) : ℝ) + α / 2 + 1) =
      ((n : ℝ) + α / 2 + 1) + 1 by push_cast; ring,
    Real.Gamma_add_one hdenArg]
  field_simp [hden, hdenSucc]
  ring

/-- All positive chord coefficients are a single `α`-dependent multiple of
the Gamma model.  The multiple is immaterial for uniform Fourier decay. -/
theorem unitChordCosCoeff_eq_model_multiple
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {n : ℕ} (hn : 1 ≤ n) :
    unitChordCosCoeff α n =
      (unitChordCosCoeff α 1 /
          CircleFourier.chordFourierCoeffGamma α 1) *
        CircleFourier.chordFourierCoeffGamma α n := by
  let K : ℝ :=
    unitChordCosCoeff α 1 /
      CircleFourier.chordFourierCoeffGamma α 1
  change unitChordCosCoeff α n =
    K * CircleFourier.chordFourierCoeffGamma α n
  induction n, hn using Nat.le_induction with
  | base =>
      dsimp [K]
      field_simp [CircleFourier.chordFourierCoeffGamma_ne_zero
        hα0 hα2 (n := 1) (by norm_num)]
  | succ n hn ih =>
      have hA : α + 2 * (n : ℝ) + 2 ≠ 0 := by positivity
      apply mul_left_cancel₀ hA
      calc
        (α + 2 * (n : ℝ) + 2) * unitChordCosCoeff α (n + 1) =
            (2 * (n : ℝ) - α) * unitChordCosCoeff α n :=
          unitChordCosCoeff_succ hα0 n
        _ = K * ((2 * (n : ℝ) - α) *
              CircleFourier.chordFourierCoeffGamma α n) := by
          rw [ih]
          ring
        _ = K * ((α + 2 * (n : ℝ) + 2) *
              CircleFourier.chordFourierCoeffGamma α (n + 1)) := by
          rw [CircleFourier.chordFourierCoeffGamma_succ hα0 hα2 hn]
        _ = (α + 2 * (n : ℝ) + 2) *
              (K * CircleFourier.chordFourierCoeffGamma α (n + 1)) := by
          ring

theorem tendsto_scaled_unitChordCosCoeff
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (1 + α) * unitChordCosCoeff α n)
      atTop
      (𝓝 ((unitChordCosCoeff α 1 /
          CircleFourier.chordFourierCoeffGamma α 1) *
        CircleFourier.fourierCuspConstant α)) := by
  let K : ℝ :=
    unitChordCosCoeff α 1 /
      CircleFourier.chordFourierCoeffGamma α 1
  have ht :=
    (CircleFourier.tendsto_scaled_chordFourierCoeffGamma hα0 hα2).const_mul K
  have ht' : Tendsto
      (fun n : ℕ ↦ K * ((n : ℝ) ^ (1 + α) *
        CircleFourier.chordFourierCoeffGamma α n))
      atTop (𝓝 (K * CircleFourier.fourierCuspConstant α)) := by
    simpa using ht
  apply ht'.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn ↦ hn⟩] with n hn
  rw [unitChordCosCoeff_eq_model_multiple hα0 hα2 hn]
  ring

/-- Uniform positive-frequency decay of the intrinsic chord profile. -/
theorem exists_unitChordCosCoeff_power_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |unitChordCosCoeff α n| ≤ C * (n : ℝ) ^ (-1 - α) := by
  have ht := tendsto_scaled_unitChordCosCoeff hα0 hα2
  have hnorm := tendsto_norm.comp ht
  rcases hnorm.bddAbove_range with ⟨D, hD⟩
  let C : ℝ := max 1 D
  refine ⟨C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hscale : 0 < (n : ℝ) ^ (1 + α) :=
    Real.rpow_pos_of_pos hnpos _
  have hscaled :
      |(n : ℝ) ^ (1 + α) * unitChordCosCoeff α n| ≤ C := by
    calc
      _ = ‖(n : ℝ) ^ (1 + α) * unitChordCosCoeff α n‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ D := hD (Set.mem_range_self n)
      _ ≤ C := le_max_right _ _
  rw [abs_mul, abs_of_pos hscale] at hscaled
  calc
    |unitChordCosCoeff α n| =
        ((n : ℝ) ^ (1 + α) * |unitChordCosCoeff α n|) /
          (n : ℝ) ^ (1 + α) := by
      field_simp [hscale.ne']
    _ ≤ C / (n : ℝ) ^ (1 + α) :=
      div_le_div_of_nonneg_right hscaled hscale.le
    _ = C * (n : ℝ) ^ (-1 - α) := by
      rw [show -1 - α = -(1 + α) by ring, Real.rpow_neg hnpos.le]
      ring

theorem exists_fourierCoeff_chordProfile_power_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ‖fourierCoeff (CircleFourier.chordProfileCircle α hα0) (n : ℤ)‖ ≤
        C * (n : ℝ) ^ (-1 - α) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_unitChordCosCoeff_power_bound hα0 hα2
  refine ⟨C, hC, fun n hn ↦ ?_⟩
  rw [CircleFourier.fourierCoeff_chordProfile_nat_eq_cosCoeff hα0,
    Complex.norm_real, Real.norm_eq_abs]
  exact hbound n hn

end BEMOC
