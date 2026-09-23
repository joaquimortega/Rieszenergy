# Exact all-degree scalar distance coefficients

`BEMOCFormalization/DistanceZonalCoefficients.lean` proves the real-exponent moment formula for the genuine Rodrigues `legendrePolynomial` defined in `DistanceZonal.lean`. It also identifies the scaled moment with `distanceHarmonicCoefficient` from `SobolevKernel.lean`. Thus the later pointwise harmonic expansion can use a checked scalar coefficient, without a free coefficient contract or an energy-defined substitute. The public result `shiftedLegendreMoment_distanceCoefficient` applies for `1<s<2` and every positive degree `ℓ+1`.

The first step is the exact affine Rodrigues rule. Under `t=1−2y`, the numerator `(t²−1)^ℓ` becomes `(-4)^ℓ y^ℓ(1−y)^ℓ`. Differentiation in `t` contributes `(-2)^{-ℓ}`, so the normalized polynomial satisfies `P_ℓ(1−2y)=(ℓ!)^{-1}D_y^ℓ[y^ℓ(1−y)^ℓ]`. `legendrePolynomial_shifted_eval` proves precisely this identity using two polynomial identities exported from `DistanceZonal`: `iterate_derivative_comp_one_sub_two_X` and `legendreRodriguesBase_comp_shift`. The proof tracks the signs and powers of two rather than relying on a named Legendre normalization.

A direct repeated integration by parts against `y^(s−1)` would introduce exponents below `−1` when `ℓ` grows. The module instead factors each intermediate derivative as `X^(ℓ−r)*shiftedLegendreCore ℓ r`. The core recurrence is `T_(r+1)=XT_r' +(ℓ−r)T_r`, an Euler operator. `shiftedLegendreCore_derivative` proves this decomposition by induction with Mathlib's polynomial product and power derivative rules. For `r<ℓ`, the base polynomial has a root of order `ℓ` at `y=1`; the derivative still has a root there. `shiftedLegendreBase_endpoint_vanish` proves this via root divisibility, and `shiftedLegendreCore_endpoint_vanish` transfers it to `T_r`.

`weighted_euler_integral` is the analytic step. With `p(1)=0` and `s>1`, interval integration by parts for `u(y)=y^s` and `v(y)=p(y)` proves

\[
 \int_0^1 y^{s-1}(yp'(y)+j p(y))\,dy
 = (j-s)\int_0^1 y^{s-1}p(y)\,dy.
\]

The `y=0` boundary term vanishes because `s>0`; the `y=1` term vanishes by `p(1)=0`. Continuity and interval integrability are discharged explicitly using `Real.continuous_rpow_const` and polynomial continuity. Applying this identity at each core step yields `shiftedCoreMoment_product`, a finite product of `ℓ−r−s` factors. `shiftedCore_product_reflect` reindexes that product to `∏_{j<ℓ}(j+1−s)` using Mathlib's finite range reflection theorem.

The undifferentiated core is `(1−y)^ℓ`, leaving the elementary beta integral `B_ℓ(s)=∫_0^1 y^(s−1)(1−y)^ℓ dy`. `shiftedBeta_split` inserts `1=(1−y)+y`. A second use of the weighted Euler identity on `(1−X)^(ℓ+1)` gives `(s+ℓ+1)B_(ℓ+1)=(ℓ+1)B_ℓ`. The base `B_0=1/s` follows from Mathlib's real-power interval integral. Induction proves `shiftedBetaIntegral_product`: `B_ℓ=ℓ!/[s∏_{j<ℓ}(s+j+1)]`. The proof explicitly establishes that each denominator is nonzero from `s>1`.

Combining Rodrigues, the Euler product, and the beta product gives the exact formula

\[
 \int_0^1 y^{s-1}P_\ell(1-2y)\,dy
 = rac{\prod_{j=0}^{\ell-1}(j+1-s)}
 {s\prod_{j=0}^{\ell-1}(s+j+1)}.
\]

The first factor is negative when `ℓ≥1` and `1<s<2`, while all subsequent factors are positive. `shiftedLegendreMoment_one` checks the first degree; `shiftedLegendreMoment_succ_succ` establishes the same successive ratio as the repository's `distanceHarmonicCoefficient_succ_succ`. Finally, `continuousEnergy_two_s_sub_two` proves `continuousEnergy (2s−2)=2^(2s−2)/s` from its actual definition, including the factor of two in the manuscript's ordered-pair normalization. Induction then yields `shiftedLegendreMoment_distanceCoefficient`:

\[
 2^{2s-2}\int_0^1 y^{s-1}P_{\ell+1}(1-2y)\,dy
 =-\mathrm{distanceHarmonicCoefficient}(s,\ell+1).
\]

The remaining affine substitution from the normalized `t∈[-1,1]` chordal-power integral to this `y∈[0,1]` integral is being proved in a downstream bridge that imports this module. This module itself proves the full scalar product and coefficient identity; it does not assume the desired distance-kernel expansion. The exact Lean source follows for review.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.DistanceZonal
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open scoped BigOperators
open MeasureTheory

namespace BEMOC.Definitive

/-- Rodrigues numerator after the affine change `t = 1 - 2y`. -/
noncomputable def shiftedLegendreBase (ℓ : ℕ) : Polynomial ℝ :=
  Polynomial.X ^ ℓ * (1 - Polynomial.X) ^ ℓ

/-- The affine Rodrigues identity, with the exact normalization. -/
theorem legendrePolynomial_shifted_eval (ℓ : ℕ) (y : ℝ) :
    (legendrePolynomial ℓ).eval (1 - 2 * y) =
      ((ℓ.factorial : ℝ)⁻¹) *
        ((Polynomial.derivative^[ℓ]) (shiftedLegendreBase ℓ)).eval y := by
  have hchain := iterate_derivative_comp_one_sub_two_X
    (legendreRodriguesBase ℓ) ℓ
  have hbase := legendreRodriguesBase_comp_shift ℓ
  have h := congrArg (Polynomial.eval y) (congrArg
    (Polynomial.derivative^[ℓ]) hbase)
  rw [hchain, Polynomial.iterate_derivative_C_mul] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_X] at h
  unfold legendrePolynomial shiftedLegendreBase
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_X]
  have hpow : (-4 : ℝ) ^ ℓ = (2 : ℝ) ^ ℓ * (-2 : ℝ) ^ ℓ := by
    rw [show (-4 : ℝ) = 2 * (-2) by norm_num, mul_pow]
  rw [hpow] at h
  norm_num at h
  have h2 : (-2 : ℝ) ^ ℓ ≠ 0 := by positivity
  have h3 : ((ℓ.factorial : ℝ)) ≠ 0 := by positivity
  have h4 : (2 : ℝ) ^ ℓ ≠ 0 := by positivity
  have h' :
      ((Polynomial.derivative^[ℓ]) (legendreRodriguesBase ℓ)).eval (1 - 2 * y) =
        (2 : ℝ) ^ ℓ *
          ((Polynomial.derivative^[ℓ])
            (Polynomial.X ^ ℓ * (1 - Polynomial.X) ^ ℓ)).eval y := by
    apply (mul_left_cancel₀ h2)
    calc
      _ = (2 : ℝ) ^ ℓ * ((-2 : ℝ) ^ ℓ *
          ((Polynomial.derivative^[ℓ])
            (Polynomial.X ^ ℓ * (1 - Polynomial.X) ^ ℓ)).eval y) := by
              simpa only [mul_assoc] using h
      _ = _ := by ring
  rw [h']
  field_simp [h3, h4]
  ring

private theorem rpow_sub_one_mul_self {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) :
    y ^ (s - 1) * y = y ^ s := by
  by_cases hy0 : y = 0
  · subst y
    simp [Real.zero_rpow (by linarith : s ≠ 0)]
  · rw [← Real.rpow_add_one hy0 (s - 1)]
    ring

/-- One weighted Euler-operator integration step. The endpoint condition removes
the boundary term at `1`; positive exponent removes it at `0`. -/
theorem weighted_euler_integral (s : ℝ) (hs : 1 < s)
    (j : ℕ) (p : Polynomial ℝ) (hp : p.eval 1 = 0) :
    (∫ y : ℝ in (0 : ℝ)..1,
      y ^ (s - 1) *
        ((Polynomial.X * p.derivative + Polynomial.C (j : ℝ) * p).eval y)) =
      ((j : ℝ) - s) *
        (∫ y : ℝ in (0 : ℝ)..1, y ^ (s - 1) * p.eval y) := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1)
    (u := fun y : ℝ => y ^ s)
    (v := fun y : ℝ => p.eval y)
    (u' := fun y : ℝ => s * y ^ (s - 1))
    (v' := fun y : ℝ => p.derivative.eval y)
    (fun y _ => Real.hasDerivAt_rpow_const (Or.inr (by linarith : 1 ≤ s)))
    (fun y _ => p.hasDerivAt y)
    (by exact ((continuous_const.mul
      (Real.continuous_rpow_const (by linarith : 0 ≤ s - 1))).intervalIntegrable _ _))
    (by exact p.derivative.differentiable.continuous.intervalIntegrable _ _)
  dsimp only at hibp
  rw [hp] at hibp
  simp only [mul_zero, sub_zero, zero_sub,
    Real.zero_rpow (by linarith : s ≠ 0), zero_mul] at hibp
  have hpoint (y : ℝ) (hy : y ∈ Set.uIcc (0 : ℝ) 1) :
      y ^ (s - 1) * y * p.derivative.eval y =
        y ^ s * p.derivative.eval y := by
    have hy0 : 0 ≤ y := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
      exact hy.1
    rw [rpow_sub_one_mul_self (by linarith : 0 < s) hy0]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, mul_add]
  rw [intervalIntegral.integral_add]
  · have hcongr : (∫ y : ℝ in (0 : ℝ)..1,
        y ^ (s - 1) * (y * p.derivative.eval y)) =
        ∫ y : ℝ in (0 : ℝ)..1, y ^ s * p.derivative.eval y := by
      apply intervalIntegral.integral_congr
      intro y hy
      simpa only [mul_assoc] using hpoint y (by simpa using hy)
    rw [hcongr, hibp]
    have hmul (y : ℝ) : y ^ (s - 1) * ((j : ℝ) * p.eval y) =
        (j : ℝ) * (y ^ (s - 1) * p.eval y) := by ring
    simp_rw [hmul]
    have hmul2 (y : ℝ) : s * y ^ (s - 1) * p.eval y =
        s * (y ^ (s - 1) * p.eval y) := by ring
    simp_rw [hmul2]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  · exact ((Real.continuous_rpow_const (by linarith : 0 ≤ s - 1)).mul
      (continuous_id.mul p.derivative.differentiable.continuous)).intervalIntegrable _ _
  · exact ((Real.continuous_rpow_const (by linarith : 0 ≤ s - 1)).mul
      (continuous_const.mul p.differentiable.continuous)).intervalIntegrable _ _

/-- Intermediate polynomials produced by successive differentiation of
`X^ℓ(1-X)^ℓ` after factoring the remaining power of `X`. -/
noncomputable def shiftedLegendreCore (ℓ : ℕ) : ℕ → Polynomial ℝ
  | 0 => (1 - Polynomial.X) ^ ℓ
  | r + 1 =>
      Polynomial.X * (shiftedLegendreCore ℓ r).derivative +
        Polynomial.C ((ℓ - r : ℕ) : ℝ) * shiftedLegendreCore ℓ r

theorem shiftedLegendreCore_derivative (ℓ r : ℕ) (hr : r ≤ ℓ) :
    (Polynomial.derivative^[r]) (shiftedLegendreBase ℓ) =
      Polynomial.X ^ (ℓ - r) * shiftedLegendreCore ℓ r := by
  induction r with
  | zero =>
      simp [shiftedLegendreBase, shiftedLegendreCore]
  | succ r ih =>
      have hrlt : r < ℓ := by omega
      rw [Function.iterate_succ_apply', ih (by omega : r ≤ ℓ),
        Polynomial.derivative_mul, Polynomial.derivative_X_pow]
      have hsub : ℓ - r = (ℓ - (r + 1)) + 1 := by omega
      rw [hsub, pow_succ]
      simp only [shiftedLegendreCore]
      rw [show ℓ - (r + 1) + 1 = ℓ - r by omega,
        show ℓ - r - 1 = ℓ - (r + 1) by omega]
      ring

theorem shiftedLegendreBase_endpoint_vanish (ℓ r : ℕ) (hr : r < ℓ) :
    ((Polynomial.derivative^[r]) (shiftedLegendreBase ℓ)).eval 1 = 0 := by
  let q : Polynomial ℝ := Polynomial.X - 1
  have hq : q ∣ (1 - Polynomial.X : Polynomial ℝ) := by
    have heq : (1 - Polynomial.X : Polynomial ℝ) = -q := by dsimp [q]; ring
    rw [heq]
    exact dvd_neg.mpr dvd_rfl
  have hpow : q ^ ℓ ∣ shiftedLegendreBase ℓ := by
    unfold shiftedLegendreBase
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hq _) _
  have hder := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd r hpow
  have hroot : q ∣ (Polynomial.derivative^[r]) (shiftedLegendreBase ℓ) :=
    (dvd_pow_self q (by omega : ℓ - r ≠ 0)).trans hder
  exact Polynomial.dvd_iff_isRoot.mp hroot

theorem shiftedLegendreCore_endpoint_vanish (ℓ r : ℕ) (hr : r < ℓ) :
    (shiftedLegendreCore ℓ r).eval 1 = 0 := by
  have h := shiftedLegendreBase_endpoint_vanish ℓ r hr
  rw [shiftedLegendreCore_derivative ℓ r (by omega)] at h
  simpa using h

/-- Weighted moment of an intermediate Euler polynomial. -/
noncomputable def shiftedCoreMoment (s : ℝ) (ℓ r : ℕ) : ℝ :=
  ∫ y : ℝ in (0 : ℝ)..1, y ^ (s - 1) * (shiftedLegendreCore ℓ r).eval y

theorem shiftedCoreMoment_step (s : ℝ) (hs : 1 < s) (ℓ r : ℕ) (hr : r < ℓ) :
    shiftedCoreMoment s ℓ (r + 1) =
      (((ℓ - r : ℕ) : ℝ) - s) * shiftedCoreMoment s ℓ r := by
  change (∫ y : ℝ in (0 : ℝ)..1,
      y ^ (s - 1) *
        ((Polynomial.X * (shiftedLegendreCore ℓ r).derivative +
          Polynomial.C ((ℓ - r : ℕ) : ℝ) * shiftedLegendreCore ℓ r).eval y)) = _
  exact weighted_euler_integral s hs (ℓ - r) (shiftedLegendreCore ℓ r)
    (shiftedLegendreCore_endpoint_vanish ℓ r hr)

theorem shiftedCoreMoment_product (s : ℝ) (hs : 1 < s)
    (ℓ r : ℕ) (hr : r ≤ ℓ) :
    shiftedCoreMoment s ℓ r =
      (∏ j ∈ Finset.range r, (((ℓ - j : ℕ) : ℝ) - s)) *
        shiftedCoreMoment s ℓ 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [shiftedCoreMoment_step s hs ℓ r (by omega), ih (by omega),
        Finset.prod_range_succ]
      ring

/-- Elementary beta integral left after all Euler derivatives. -/
noncomputable def shiftedBetaIntegral (s : ℝ) (ℓ : ℕ) : ℝ :=
  ∫ y : ℝ in (0 : ℝ)..1, y ^ (s - 1) * (1 - y) ^ ℓ

theorem shiftedCoreMoment_zero (s : ℝ) (ℓ : ℕ) :
    shiftedCoreMoment s ℓ 0 = shiftedBetaIntegral s ℓ := by
  simp [shiftedCoreMoment, shiftedLegendreCore, shiftedBetaIntegral]

private theorem shiftedBeta_split (s : ℝ) (hs : 1 < s) (ℓ : ℕ) :
    shiftedBetaIntegral s ℓ = shiftedBetaIntegral s (ℓ + 1) +
      (∫ y : ℝ in (0 : ℝ)..1, y ^ s * (1 - y) ^ ℓ) := by
  unfold shiftedBetaIntegral
  rw [← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_congr
    intro y hy
    dsimp only
    have hy0 : 0 ≤ y := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
      exact hy.1
    rw [pow_succ, ← rpow_sub_one_mul_self (by linarith : 0 < s) hy0]
    ring
  · exact ((Real.continuous_rpow_const (by linarith : 0 ≤ s - 1)).mul
      ((continuous_const.sub continuous_id).pow (ℓ + 1))).intervalIntegrable _ _
  · exact ((Real.continuous_rpow_const (by linarith : 0 ≤ s)).mul
      ((continuous_const.sub continuous_id).pow ℓ)).intervalIntegrable _ _

private theorem shiftedBeta_derivative (ℓ : ℕ) :
    Polynomial.derivative ((1 - Polynomial.X : Polynomial ℝ) ^ (ℓ + 1)) =
      Polynomial.C (-(ℓ + 1 : ℝ)) * (1 - Polynomial.X) ^ ℓ := by
  rw [Polynomial.derivative_pow]
  simp
  ring

theorem shiftedBetaIntegral_succ (s : ℝ) (hs : 1 < s) (ℓ : ℕ) :
    (s + ℓ + 1) * shiftedBetaIntegral s (ℓ + 1) =
      (ℓ + 1 : ℝ) * shiftedBetaIntegral s ℓ := by
  let p : Polynomial ℝ := (1 - Polynomial.X) ^ (ℓ + 1)
  have hp : p.eval 1 = 0 := by simp [p]
  have h := weighted_euler_integral s hs 0 p hp
  simp only [zero_sub, zero_mul, add_zero] at h
  have hder (y : ℝ) : p.derivative.eval y =
      -(ℓ + 1 : ℝ) * (1 - y) ^ ℓ := by
    rw [show p.derivative = Polynomial.C (-(ℓ + 1 : ℝ)) *
        (1 - Polynomial.X) ^ ℓ from shiftedBeta_derivative ℓ]
    simp [Polynomial.eval_mul]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Nat.cast_zero, zero_mul, add_zero, zero_sub] at h
  simp_rw [hder] at h
  have hpow (y : ℝ) (hy : y ∈ Set.uIcc (0 : ℝ) 1) :
      y ^ (s - 1) * (y * (-(ℓ + 1 : ℝ) * (1 - y) ^ ℓ)) =
        -(ℓ + 1 : ℝ) * (y ^ s * (1 - y) ^ ℓ) := by
    have hy0 : 0 ≤ y := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
      exact hy.1
    rw [← mul_assoc, rpow_sub_one_mul_self (by linarith : 0 < s) hy0]
    ring
  have hcongr :
      (∫ y : ℝ in (0 : ℝ)..1,
        y ^ (s - 1) * (y * (-(ℓ + 1 : ℝ) * (1 - y) ^ ℓ))) =
        -(ℓ + 1 : ℝ) *
          (∫ y : ℝ in (0 : ℝ)..1, y ^ s * (1 - y) ^ ℓ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y hy
    exact hpow y hy
  rw [hcongr] at h
  have hsplit := shiftedBeta_split s hs ℓ
  simp only [p, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X] at h
  change -(ℓ + 1 : ℝ) *
      (∫ y : ℝ in (0 : ℝ)..1, y ^ s * (1 - y) ^ ℓ) =
      -s * shiftedBetaIntegral s (ℓ + 1) at h
  nlinarith [congrArg (fun x : ℝ => (ℓ + 1 : ℝ) * x) hsplit]

theorem shiftedBetaIntegral_zero (s : ℝ) (hs : 1 < s) :
    shiftedBetaIntegral s 0 = 1 / s := by
  unfold shiftedBetaIntegral
  simp only [pow_zero, mul_one]
  rw [integral_rpow (Or.inl (by linarith : -1 < s - 1))]
  have hs0 : s ≠ 0 := by linarith
  simp [show s - 1 + 1 = s by ring, Real.zero_rpow hs0]

theorem shiftedBetaIntegral_product (s : ℝ) (hs : 1 < s) (ℓ : ℕ) :
    shiftedBetaIntegral s ℓ =
      (ℓ.factorial : ℝ) /
        (s * ∏ j ∈ Finset.range ℓ, (s + (j : ℝ) + 1)) := by
  induction ℓ with
  | zero => simp [shiftedBetaIntegral_zero s hs]
  | succ ℓ ih =>
      have hrec := shiftedBetaIntegral_succ s hs ℓ
      rw [ih] at hrec
      rw [Finset.prod_range_succ, Nat.factorial_succ]
      push_cast
      have hd : s * ∏ j ∈ Finset.range ℓ, (s + (j : ℝ) + 1) ≠ 0 := by
        apply mul_ne_zero (by linarith)
        apply Finset.prod_ne_zero_iff.mpr
        intro j hj
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      have hd' : s + (ℓ : ℝ) + 1 ≠ 0 := by
        have hj0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
        linarith
      have hB : shiftedBetaIntegral s (ℓ + 1) =
          ((ℓ + 1 : ℝ) *
            ((ℓ.factorial : ℝ) /
              (s * ∏ j ∈ Finset.range ℓ, (s + (j : ℝ) + 1)))) /
                (s + (ℓ : ℝ) + 1) := (eq_div_iff hd').2 (by simpa [mul_comm] using hrec)
      rw [hB]
      field_simp [hd, hd']
      ring

/-- The scalar moment of the actual shifted Legendre polynomial. -/
noncomputable def shiftedLegendreMoment (s : ℝ) (ℓ : ℕ) : ℝ :=
  ∫ y : ℝ in (0 : ℝ)..1,
    y ^ (s - 1) * (legendrePolynomial ℓ).eval (1 - 2 * y)

theorem shiftedLegendreMoment_core (s : ℝ) (ℓ : ℕ) :
    shiftedLegendreMoment s ℓ =
      ((ℓ.factorial : ℝ)⁻¹) * shiftedCoreMoment s ℓ ℓ := by
  unfold shiftedLegendreMoment shiftedCoreMoment
  have hpoint (y : ℝ) :
      (legendrePolynomial ℓ).eval (1 - 2 * y) =
        ((ℓ.factorial : ℝ)⁻¹) * (shiftedLegendreCore ℓ ℓ).eval y := by
    rw [legendrePolynomial_shifted_eval,
      shiftedLegendreCore_derivative ℓ ℓ le_rfl]
    simp
  simp_rw [hpoint]
  have hmul (y : ℝ) :
      y ^ (s - 1) * ((ℓ.factorial : ℝ)⁻¹ * (shiftedLegendreCore ℓ ℓ).eval y) =
        ((ℓ.factorial : ℝ)⁻¹) *
          (y ^ (s - 1) * (shiftedLegendreCore ℓ ℓ).eval y) := by ring
  simp_rw [hmul]
  rw [intervalIntegral.integral_const_mul]

private theorem shiftedCore_product_reflect (s : ℝ) (ℓ : ℕ) :
    (∏ j ∈ Finset.range ℓ, (((ℓ - j : ℕ) : ℝ) - s)) =
      ∏ j ∈ Finset.range ℓ, (((j + 1 : ℕ) : ℝ) - s) := by
  have href := Finset.prod_range_reflect
    (fun j : ℕ => (((j + 1 : ℕ) : ℝ) - s)) ℓ
  calc
    _ = ∏ j ∈ Finset.range ℓ,
        (((ℓ - 1 - j + 1 : ℕ) : ℝ) - s) := by
          apply Finset.prod_congr rfl
          intro j hj
          congr 2
          have hjlt := Finset.mem_range.mp hj
          omega
    _ = _ := href

/-- Exact all-degree Legendre moment for a real exponent `1<s<2`.
The formula also holds for any `s>1`; the upper bound is kept in the public
contract to match the distance-kernel application. -/
theorem shiftedLegendreMoment_product {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (ℓ : ℕ) :
    shiftedLegendreMoment s ℓ =
      (∏ j ∈ Finset.range ℓ, (((j + 1 : ℕ) : ℝ) - s)) /
        (s * ∏ j ∈ Finset.range ℓ, (s + (j : ℝ) + 1)) := by
  rw [shiftedLegendreMoment_core,
    shiftedCoreMoment_product s hs1 ℓ ℓ le_rfl,
    shiftedCoreMoment_zero, shiftedBetaIntegral_product s hs1,
    shiftedCore_product_reflect]
  have hfac : ((ℓ.factorial : ℝ)) ≠ 0 := by positivity
  have hden : s * ∏ j ∈ Finset.range ℓ, (s + (j : ℝ) + 1) ≠ 0 := by
    apply mul_ne_zero (by linarith)
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  field_simp [hfac, hden]

theorem shiftedLegendreMoment_one {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    shiftedLegendreMoment s 1 = (1 - s) / (s * (s + 1)) := by
  rw [shiftedLegendreMoment_product hs1 hs2]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num

theorem shiftedLegendreMoment_succ_succ {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (ℓ : ℕ) :
    shiftedLegendreMoment s (ℓ + 2) =
      shiftedLegendreMoment s (ℓ + 1) *
        (((ℓ : ℝ) + 2 - s) / ((ℓ : ℝ) + 2 + s)) := by
  rw [shiftedLegendreMoment_product hs1 hs2,
    shiftedLegendreMoment_product hs1 hs2]
  simp only [show ℓ + 2 = (ℓ + 1) + 1 by omega,
    Finset.prod_range_succ]
  have hs0 : s ≠ 0 := by linarith
  have hd : ∀ j : ℕ, s + (j : ℝ) + 1 ≠ 0 := by
    intro j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hprod : s * ∏ j ∈ Finset.range (ℓ + 1), (s + (j : ℝ) + 1) ≠ 0 := by
    exact mul_ne_zero hs0 (Finset.prod_ne_zero_iff.mpr (fun j _ => hd j))
  have hd' : s + (ℓ : ℝ) + 2 ≠ 0 := by
    have hj0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith
  push_cast
  field_simp [hprod, hd']
  ring

theorem continuousEnergy_two_s_sub_two {s : ℝ} (hs : 0 < s) :
    continuousEnergy (2 * s - 2) = (2 : ℝ) ^ (2 * s - 2) / s := by
  unfold continuousEnergy
  rw [show 2 * s - 2 + 1 = (2 * s - 2) + 1 by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num
  have hs0 : s ≠ 0 := ne_of_gt hs
  field_simp [hs0]
  ring

/-- The shifted scalar Legendre moment is exactly the negative distance-kernel
coefficient after the chordal-power scale is restored. -/
theorem shiftedLegendreMoment_distanceCoefficient {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) (ℓ : ℕ) :
    (2 : ℝ) ^ (2 * s - 2) * shiftedLegendreMoment s (ℓ + 1) =
      -distanceHarmonicCoefficient s (ℓ + 1) := by
  induction ℓ with
  | zero =>
      rw [shiftedLegendreMoment_one hs1 hs2]
      simp only [distanceHarmonicCoefficient, Nat.add_sub_cancel,
        Finset.prod_range_zero, mul_one]
      rw [continuousEnergy_two_s_sub_two (by linarith : 0 < s)]
      have hs0 : s ≠ 0 := by linarith
      have hs1' : s + 1 ≠ 0 := by linarith
      field_simp [hs0, hs1']
      ring
  | succ ℓ ih =>
      rw [shiftedLegendreMoment_succ_succ hs1 hs2,
        distanceHarmonicCoefficient_succ_succ]
      rw [← mul_assoc, ih]
      ring

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
