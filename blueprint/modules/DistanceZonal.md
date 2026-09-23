# `BEMOCFormalization.DistanceZonal` proof guide

This helper gives an all-degree Legendre polynomial from Rodrigues' formula,
independently of the even-degree zonal polynomial used for the lower-bound
corollary. It imports `SobolevKernel` for the distance-kernel context and
mathlib's polynomial derivative and interval integration APIs.

Define `R_ℓ=(X²−1)^ℓ` and `P_ℓ=(2^ℓℓ!)⁻¹D^ℓR_ℓ`. Every derivative
`D^rR_ℓ` with `r<ℓ` vanishes at both `−1` and `1`: the factor
`X−a` divides `X²−1` at either endpoint, hence its `ℓ`th power divides
`R_ℓ`, and after `r` derivatives at least one factor remains. This is
`legendreRodrigues_endpoint_vanish`.

Repeated endpoint-safe integration by parts then gives

```text
∫_{−1}¹ t^m D^rR_ℓ(t) dt
  = (−1)^r m_(r) ∫_{−1}¹ t^(m−r)R_ℓ(t) dt,  r≤ℓ,
```

where `m_(r)` is the descending factorial. If `m<ℓ`, that factorial is
zero, so `legendrePolynomial_orthogonal_monomial` proves
`∫t^mP_ℓ(t)dt=0`. The degree calculation and nonzero leading coefficient
show that these polynomials span the polynomial ring. `DistanceZonalCoefficients`
proves the noninteger chordal-power coefficient, and `DistanceScalarBridge`
uses this orthogonality and polynomial density to prove the scalar series
equality under harmonic addition.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.SobolevKernel
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.Polynomial.Sequence

/-! All-degree Rodrigues polynomials for the distance-kernel expansion. -/

open scoped BigOperators
open MeasureTheory

namespace BEMOC.Definitive

/-- The unnormalized Rodrigues numerator for degree `ℓ`. -/
noncomputable def legendreRodriguesBase (ℓ : ℕ) : Polynomial ℝ :=
  ((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ ℓ

/-- The standard Legendre polynomial, directly normalized by Rodrigues' rule. -/
noncomputable def legendrePolynomial (ℓ : ℕ) : Polynomial ℝ :=
  Polynomial.C (((2 : ℝ) ^ ℓ * (ℓ.factorial : ℝ))⁻¹) *
    (Polynomial.derivative^[ℓ]) (legendreRodriguesBase ℓ)

theorem legendrePolynomial_zero : legendrePolynomial 0 = 1 := by
  simp [legendrePolynomial, legendreRodriguesBase]

theorem legendrePolynomial_one : legendrePolynomial 1 = Polynomial.X := by
  apply Polynomial.funext
  intro x
  simp [legendrePolynomial, legendreRodriguesBase]
  ring

theorem iterate_derivative_comp_one_sub_two_X
    (p : Polynomial ℝ) (r : ℕ) :
    (Polynomial.derivative^[r])
      (p.comp (1 - 2 * (Polynomial.X : Polynomial ℝ))) =
      Polynomial.C ((-2 : ℝ) ^ r) *
        ((Polynomial.derivative^[r]) p).comp
          (1 - 2 * (Polynomial.X : Polynomial ℝ)) := by
  induction r generalizing p with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, Polynomial.derivative_C_mul,
        Polynomial.derivative_comp]
      have hq : Polynomial.derivative (1 - 2 * (Polynomial.X : Polynomial ℝ)) =
          Polynomial.C (-2 : ℝ) := by
        simp
        rfl
      rw [hq]
      simp only [Function.iterate_succ_apply', pow_succ, map_mul]
      ring

theorem legendreRodriguesBase_comp_shift (ℓ : ℕ) :
    (legendreRodriguesBase ℓ).comp
        (1 - 2 * (Polynomial.X : Polynomial ℝ)) =
      Polynomial.C ((-4 : ℝ) ^ ℓ) *
        ((Polynomial.X : Polynomial ℝ) ^ ℓ * (1 - Polynomial.X) ^ ℓ) := by
  unfold legendreRodriguesBase
  simp only [Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.one_comp,
    Polynomial.X_pow_comp, Polynomial.X_comp, Polynomial.mul_comp]
  have hbase :
      (1 - 2 * (Polynomial.X : Polynomial ℝ)) ^ 2 - 1 =
        Polynomial.C (-4 : ℝ) * (Polynomial.X * (1 - Polynomial.X)) := by
    simp only [map_neg, map_ofNat]
    ring
  rw [hbase]
  simp only [mul_pow, map_neg, map_ofNat, map_pow]

theorem legendreRodrigues_endpoint_vanish (ℓ r : ℕ) (hr : r < ℓ)
    (a : ℝ) (ha : a ^ 2 = 1) :
    ((Polynomial.derivative^[r]) (legendreRodriguesBase ℓ)).eval a = 0 := by
  let q : Polynomial ℝ := Polynomial.X - Polynomial.C a
  have hroot : (((Polynomial.X : Polynomial ℝ) ^ 2 - 1)).IsRoot a := by
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, ha, sub_self]
  have hq : q ∣ ((Polynomial.X : Polynomial ℝ) ^ 2 - 1) := by
    exact Polynomial.dvd_iff_isRoot.mpr hroot
  have hqpow : q ^ ℓ ∣ legendreRodriguesBase ℓ := by
    exact pow_dvd_pow_of_dvd hq _
  have hder := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd r hqpow
  have hqdiv : q ∣ q ^ (ℓ - r) := by
    exact dvd_pow_self q (by omega)
  have hrootder : ((Polynomial.derivative^[r])
      (legendreRodriguesBase ℓ)).IsRoot a :=
    Polynomial.dvd_iff_isRoot.mp (hqdiv.trans hder)
  exact hrootder

private theorem legendre_interval_moment_derivative (p : Polynomial ℝ) (m : ℕ)
    (hp1 : p.eval 1 = 0) (hpm1 : p.eval (-1) = 0) :
    (∫ t : ℝ in (-1)..1, t ^ m * p.derivative.eval t) =
      -(m : ℝ) * (∫ t : ℝ in (-1)..1, t ^ (m - 1) * p.eval t) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (-1 : ℝ)) (b := 1)
    (u := fun t : ℝ => t ^ m) (v := fun t : ℝ => p.eval t)
    (u' := fun t : ℝ => (m : ℝ) * t ^ (m - 1))
    (v' := fun t : ℝ => p.derivative.eval t)
    (fun x _ => hasDerivAt_pow m x)
    (fun x _ => p.hasDerivAt x)
    (by exact ((continuous_const.mul (continuous_id.pow (m - 1))).intervalIntegrable _ _))
    (by exact p.derivative.differentiable.continuous.intervalIntegrable _ _)
  dsimp only at h
  rw [hp1, hpm1] at h
  simp only [mul_zero, sub_zero, zero_sub] at h
  rw [h]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Repeated integration by parts for arbitrary Legendre degree. -/
theorem legendreRodrigues_interval_moment (ℓ r : ℕ) (hr : r ≤ ℓ)
    (m : ℕ) :
    (∫ t : ℝ in (-1)..1, t ^ m *
      ((Polynomial.derivative^[r]) (legendreRodriguesBase ℓ)).eval t) =
      (-1 : ℝ) ^ r * (m.descFactorial r : ℝ) *
        (∫ t : ℝ in (-1)..1, t ^ (m - r) *
          (legendreRodriguesBase ℓ).eval t) := by
  induction r generalizing m with
  | zero => simp
  | succ r ih =>
      have hrlt : r < ℓ := by omega
      let p : Polynomial ℝ :=
        (Polynomial.derivative^[r]) (legendreRodriguesBase ℓ)
      have hp1 : p.eval 1 = 0 := legendreRodrigues_endpoint_vanish ℓ r hrlt 1 (by norm_num)
      have hpm1 : p.eval (-1) = 0 :=
        legendreRodrigues_endpoint_vanish ℓ r hrlt (-1) (by norm_num)
      rw [Function.iterate_succ_apply']
      change (∫ t : ℝ in (-1)..1, t ^ m * p.derivative.eval t) = _
      rw [legendre_interval_moment_derivative p m hp1 hpm1]
      have hrec := ih (by omega : r ≤ ℓ) (m - 1)
      change (∫ t : ℝ in (-1)..1, t ^ (m - 1) * p.eval t) = _ at hrec
      rw [hrec]
      by_cases hm : m = 0
      · subst m
        simp
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
        rw [Nat.succ_descFactorial_succ]
        have hsub : j + 1 - 1 - r = j + 1 - (r + 1) := by omega
        rw [hsub]
        push_cast
        ring

/-- A degree-`ℓ` Legendre polynomial is orthogonal to every lower monomial. -/
theorem legendrePolynomial_orthogonal_monomial (ℓ m : ℕ) (hm : m < ℓ) :
    (∫ t : ℝ in (-1)..1, t ^ m * (legendrePolynomial ℓ).eval t) = 0 := by
  have h := legendreRodrigues_interval_moment ℓ ℓ le_rfl m
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr hm] at h
  simp only [Nat.cast_zero, mul_zero, zero_mul] at h
  unfold legendrePolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  conv_lhs =>
    arg 1
    ext t
    rw [mul_left_comm]
  rw [intervalIntegral.integral_const_mul]
  simp [h]

/-- Rodrigues' polynomial has exactly degree `ℓ`; hence the Legendre family
is triangular with nonzero leading coefficients. -/
theorem legendrePolynomial_natDegree (ℓ : ℕ) :
    (legendrePolynomial ℓ).natDegree = ℓ := by
  have hbase : (legendreRodriguesBase ℓ).natDegree = 2 * ℓ := by
    unfold legendreRodriguesBase
    rw [Polynomial.natDegree_pow, ← Polynomial.C_1,
      Polynomial.natDegree_X_pow_sub_C]
    omega
  have hmonic : (legendreRodriguesBase ℓ).Monic := by
    unfold legendreRodriguesBase
    exact (Polynomial.monic_X_pow_sub_C (1 : ℝ) (by norm_num)).pow ℓ
  have hcoeff : (legendreRodriguesBase ℓ).coeff (2 * ℓ) = 1 := by
    rw [← hbase]
    exact hmonic
  have htop : (legendrePolynomial ℓ).coeff ℓ ≠ 0 := by
    unfold legendrePolynomial
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_iterate_derivative]
    rw [show ℓ + ℓ = 2 * ℓ by omega, hcoeff]
    simp only [nsmul_eq_mul, mul_one]
    have hfac : (ℓ.factorial : ℝ) ≠ 0 := by positivity
    have hdesc : ((2 * ℓ).descFactorial ℓ : ℝ) ≠ 0 := by
      have hnat : (2 * ℓ).descFactorial ℓ ≠ 0 := by
        intro hz
        have hlt := Nat.descFactorial_eq_zero_iff_lt.mp hz
        omega
      exact_mod_cast hnat
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero (by positivity) hfac)) hdesc
  apply Polynomial.eq_natDegree_of_le_mem_support
  · unfold legendrePolynomial
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (by simpa [hbase, show 2 * ℓ - ℓ = ℓ by omega] using
        Polynomial.natDegree_iterate_derivative (legendreRodriguesBase ℓ) ℓ)
  · exact Polynomial.mem_support_iff.mpr htop

theorem legendrePolynomial_ne_zero (ℓ : ℕ) : legendrePolynomial ℓ ≠ 0 := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp [legendrePolynomial_zero]
  · intro hz
    have hdegree := legendrePolynomial_natDegree ℓ
    rw [hz, Polynomial.natDegree_zero] at hdegree
    omega

/-- The Rodrigues Legendre polynomials form an algebraic basis of real
polynomials, by their strictly increasing degrees. -/
theorem legendrePolynomial_span :
    Submodule.span ℝ (Set.range legendrePolynomial) = ⊤ := by
  let S : Polynomial.Sequence ℝ := {
    elems' := legendrePolynomial
    degree_eq' := fun ℓ => by
      rw [Polynomial.degree_eq_natDegree (legendrePolynomial_ne_zero ℓ),
        legendrePolynomial_natDegree]
  }
  have hCoeff : ∀ ℓ, IsUnit (S ℓ).leadingCoeff := by
    intro ℓ
    exact isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr
      (legendrePolynomial_ne_zero ℓ))
  simpa only [S] using S.span hCoeff

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
