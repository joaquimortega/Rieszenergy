# Even zonal Legendre polynomials and their moments

`BEMOCFormalization/ZonalPolynomials.lean` constructs the even Legendre polynomial of degree `2k` as a genuine polynomial over `ℝ`, proves its Rodrigues identity, and evaluates every even-power zonal moment against normalized sphere measure. It imports `SobolevLowerBound.lean` for the already verified projection-moment integration theorem. No new abstract mathematical assumption is introduced here.

The final result is `evenLegendre_zonal_integral_eq_model`. For every unit direction `u`, and natural numbers `n,k`, the integral of `⟪u,x⟫^(2n) P_(2k)(⟪u,x⟫)` over `sigma` equals `evenMomentModelCoefficient n k`. In particular it vanishes when `k>n`. This is the exact bridge needed to apply the degree-dependent bounds in `SobolevLowerBound.lean` to an actual zonal harmonic integral. The theorem does not assert that the zonal polynomial is itself a member of a chosen harmonic orthonormal basis; that separate addition/Funk–Hecke bridge belongs to the harmonic module.

The coefficient definition uses the binomial expansion of `(X²−1)^(2k)` and the falling factorial produced by differentiating a monomial `2k` times. The finite sum only contains even powers `X^(2j)` for `0≤j≤k`. `evenRodriguesBase_eq` verifies the binomial base. `evenRodrigues_derivative_expanded` invokes Mathlib's iterated polynomial-derivative formulas term by term, which is safe because the sum is finite. For `j<k`, the falling factorial is zero. Reindexing the remaining terms proves `evenLegendrePolynomial_rodrigues`:

\[
 2^{2k}(2k)!P_{2k}(X)
 = \left(\frac{d}{dX}\right)^{2k}(X^2-1)^{2k}.
\]

The public `evenLegendrePolynomial_zero` and `_one` checks recover `P_0=1` and `P_2=(3X²−1)/2`, guarding the normalization. `evenLegendre_zonal_integral` first evaluates the sphere integral as an explicit finite rational sum by expanding the polynomial and applying `even_projection_polynomial_integral`. Independently, `evenLegendre_interval_moment` evaluates the corresponding normalized scalar interval integral to that same sum. Their equality, `evenLegendre_sphere_eq_interval`, uses the established uniform-height projection law and avoids constructing a new pushforward-measure argument.

The product evaluation is proved by Rodrigues and integration by parts. `evenRodrigues_endpoint_vanish` shows that every derivative of `(X²−1)^(2k)` below order `2k` vanishes at both endpoints. It derives polynomial root divisibility from the factors `X−1` and `X+1` and applies Mathlib's theorem that derivatives of a divisible power retain the remaining root multiplicity. `polynomial_interval_moment_derivative` is one interval integration-by-parts step with its boundary terms zero. Induction gives `evenRodrigues_interval_moment`; the factor is `(-1)^r m.descFactorial r`, and the formula also covers `r>m` because the falling factorial then vanishes. `evenLegendre_interval_moment_rodrigues` specializes `r=2k`, accounts for the Rodrigues denominator, and identifies the remaining integral with `evenBetaIntegral (n-k) (2k)`.

The beta integral is `∫_-1^1 t^(2a)(1−t²)^b dt`. `evenBetaIntegral_split` inserts `1=(1−t²)+t²`; `evenBetaIntegral_succ` applies integration by parts to `t^(2a+1)(1−t²)^(b+1)`. These give a closed finite product and, more usefully for the moment, `evenBetaIntegral_shift_two`, which changes `(a,b)` to `(a−1,b+2)`. The latter is written without division so its algebraic use is direct and no nonzero beta-integral assumption is needed.

`evenLegendreMoment_step` combines that two-step beta recurrence with `Nat.descFactorial_succ` and `Nat.factorial_succ`. For `k<n`, it proves the exact ratio

\[
 M(n,k+1)=\frac{2(n-k)}{2n+2k+3}M(n,k).
\]

The base `M(n,0)=1/(2n+1)` follows from the beta integral at exponent zero. Induction matches the finite product defining `evenMomentModelCoefficient`. When `k≥n`, the next falling factorial is zero, so the moment and model coefficient both vanish. All denominator nonzero facts in the recurrence follow from natural-number inequalities and factorial positivity; Lean checks the final rational identity with `field_simp` and a linear combination of the beta recurrence.


The module also supplies an exact scalar bridge for the radial differential route. `radialEvenMomentCoefficient n k` is the quotient

\[
 rac{2^{2k}(n+k)_{\underline{2k}}}
 {(2n+2k+1)(2n+2k)_{\underline{2k}}}.
\]

`radialNumerator_step` and `radialDenominator_step` use Mathlib's `Nat.succ_descFactorial_succ` to obtain its degree recurrence. The ratio is again `2(n−k)/(2n+2k+3)`. Its degree-zero value is `1/(2n+1)`, and for `k>n` its numerator falling factorial vanishes. Induction proves `radialEvenMomentCoefficient_eq_model n k` for all natural `n,k`. This links the differential/Hobson calculation to the very same checked finite product, without assuming a general Funk–Hecke theorem or changing the Sobolev model definition.

The exact checked source below is included for line-by-line review. The module should be rebuilt with `lake build BEMOCFormalization.ZonalPolynomials`; a direct `lake env lean` check has also passed. The repository-wide build still depends on concurrently edited downstream modules.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.SobolevLowerBound
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open scoped BigOperators
open MeasureTheory
namespace BEMOC.Definitive

/-- Finite Rodrigues coefficient of the even Legendre polynomial of degree `2k`.
The index `j` is the exponent `2j`; coefficients outside `0 ≤ j ≤ k` vanish. -/
noncomputable def evenLegendreCoefficient (k j : ℕ) : ℝ :=
  if j ≤ k then
    ((-1 : ℝ) ^ (k - j) * (Nat.choose (2 * k) (k + j) : ℝ) *
      ((2 * (k + j)).descFactorial (2 * k) : ℝ)) /
      ((2 : ℝ) ^ (2 * k) * ((2 * k).factorial : ℝ))
  else 0

/-- The explicit finite even Legendre polynomial. -/
noncomputable def evenLegendrePolynomial (k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    Polynomial.C (evenLegendreCoefficient k j) * Polynomial.X ^ (2 * j)

/-- Evaluation is exactly its finite even-monomial expansion. -/
theorem evenLegendrePolynomial_eval (k : ℕ) (t : ℝ) :
    (evenLegendrePolynomial k).eval t =
      ∑ j ∈ Finset.range (k + 1), evenLegendreCoefficient k j * t ^ (2 * j) := by
  simp [evenLegendrePolynomial, Polynomial.eval_finset_sum]

/-- The binomial expansion before differentiating the Rodrigues numerator. -/
noncomputable def evenRodriguesBase (k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (2 * k + 1),
    Polynomial.C ((-1 : ℝ) ^ (2 * k - j) * (Nat.choose (2 * k) j : ℝ)) *
      Polynomial.X ^ (2 * j)

/-- The finite binomial expansion is exactly `(X² - 1)^(2k)`. -/
theorem evenRodriguesBase_eq (k : ℕ) :
    evenRodriguesBase k = ((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k) := by
  rw [sub_eq_add_neg, add_pow]
  unfold evenRodriguesBase
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul, map_pow, map_natCast, map_neg, map_one]
  ring

/-- Differentiating the binomial expansion gives an exact finite Rodrigues sum. -/
theorem evenRodrigues_derivative_expanded (k : ℕ) :
    (Polynomial.derivative^[2 * k]) (evenRodriguesBase k) =
      ∑ j ∈ Finset.range (2 * k + 1),
        Polynomial.C ((-1 : ℝ) ^ (2 * k - j) * (Nat.choose (2 * k) j : ℝ) *
          ((2 * j).descFactorial (2 * k) : ℝ)) *
          Polynomial.X ^ (2 * j - 2 * k) := by
  unfold evenRodriguesBase
  rw [Polynomial.iterate_derivative_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.iterate_derivative_C_mul,
    Polynomial.iterate_derivative_X_pow_eq_C_mul]
  simp only [map_mul, mul_assoc]

/-- The finite polynomial is exactly Rodrigues' normalized derivative. -/
theorem evenLegendrePolynomial_rodrigues (k : ℕ) :
    Polynomial.C ((2 : ℝ) ^ (2 * k) * ((2 * k).factorial : ℝ)) *
      evenLegendrePolynomial k =
      (Polynomial.derivative^[2 * k])
        (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k)) := by
  rw [← evenRodriguesBase_eq, evenRodrigues_derivative_expanded]
  rw [show 2 * k + 1 = k + (k + 1) by omega, Finset.sum_range_add]
  have hzero :
      (∑ j ∈ Finset.range k,
        Polynomial.C ((-1 : ℝ) ^ (2 * k - j) * (Nat.choose (2 * k) j : ℝ) *
          ((2 * j).descFactorial (2 * k) : ℝ)) *
          Polynomial.X ^ (2 * j - 2 * k)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : 2 * j < 2 * k)]
    simp
  rw [hzero, zero_add]
  unfold evenLegendrePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
  simp only [evenLegendreCoefficient, if_pos hjk]
  have hden : (2 : ℝ) ^ (2 * k) * ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have hsub : 2 * (k + j) - 2 * k = 2 * j := by omega
  have hsub2 : 2 * k - (k + j) = k - j := by omega
  rw [hsub, hsub2]
  rw [← mul_assoc, ← map_mul]
  congr 1
  field_simp [hden]

/-- Before the final Rodrigues derivative, every endpoint derivative vanishes. -/
theorem evenRodrigues_endpoint_vanish (k r : ℕ) (hr : r < 2 * k)
    (a : ℝ) (ha : a ^ 2 = 1) :
    ((Polynomial.derivative^[r])
      (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k))).eval a = 0 := by
  let q : Polynomial ℝ := Polynomial.X - Polynomial.C a
  have hroot : (((Polynomial.X : Polynomial ℝ) ^ 2 - 1)).IsRoot a := by
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, ha, sub_self]
  have hq : q ∣ ((Polynomial.X : Polynomial ℝ) ^ 2 - 1) := by
    exact Polynomial.dvd_iff_isRoot.mpr hroot
  have hqpow : q ^ (2 * k) ∣
      (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k)) := pow_dvd_pow_of_dvd hq _
  have hder := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd r hqpow
  have hqdiv : q ∣ q ^ (2 * k - r) := by
    exact dvd_pow_self q (by omega)
  have hrootder : ((Polynomial.derivative^[r])
      (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k))).IsRoot a :=
    Polynomial.dvd_iff_isRoot.mp (hqdiv.trans hder)
  exact hrootder

/-- One integration-by-parts step for a polynomial vanishing at both endpoints. -/
theorem polynomial_interval_moment_derivative (p : Polynomial ℝ) (m : ℕ)
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

/-- Repeated endpoint-safe integration by parts for the Rodrigues numerator. -/
theorem evenRodrigues_interval_moment (k r : ℕ) (hr : r ≤ 2 * k)
    (m : ℕ) :
    (∫ t : ℝ in (-1)..1, t ^ m *
      ((Polynomial.derivative^[r])
        (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k))).eval t) =
      (-1 : ℝ) ^ r * (m.descFactorial r : ℝ) *
        (∫ t : ℝ in (-1)..1, t ^ (m - r) *
          (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k)).eval t) := by
  induction r generalizing m with
  | zero => simp
  | succ r ih =>
      have hrlt : r < 2 * k := by omega
      let p : Polynomial ℝ := (Polynomial.derivative^[r])
        (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k))
      have hp1 : p.eval 1 = 0 := evenRodrigues_endpoint_vanish k r hrlt 1 (by norm_num)
      have hpm1 : p.eval (-1) = 0 := evenRodrigues_endpoint_vanish k r hrlt (-1) (by norm_num)
      rw [Function.iterate_succ_apply']
      change (∫ t : ℝ in (-1)..1, t ^ m * p.derivative.eval t) = _
      rw [polynomial_interval_moment_derivative p m hp1 hpm1]
      have hrec := ih (by omega : r ≤ 2 * k) (m - 1)
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

/-- Elementary beta-type integral for nonnegative even exponents. -/
noncomputable def evenBetaIntegral (a b : ℕ) : ℝ :=
  ∫ t : ℝ in (-1)..1, t ^ (2 * a) * (1 - t ^ 2) ^ b

/-- Splitting one factor `1 = (1-t²)+t²` inside the beta integral. -/
theorem evenBetaIntegral_split (a b : ℕ) :
    evenBetaIntegral a b =
      evenBetaIntegral a (b + 1) + evenBetaIntegral (a + 1) b := by
  unfold evenBetaIntegral
  rw [← intervalIntegral.integral_add]
  · congr 1
    funext t
    rw [pow_succ]
    ring
  · exact (by fun_prop : Continuous (fun t : ℝ => t ^ (2 * a) *
        (1 - t ^ 2) ^ (b + 1))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun t : ℝ => t ^ (2 * (a + 1)) *
        (1 - t ^ 2) ^ b)).intervalIntegrable _ _

/-- A one-step beta recurrence from integration by parts. -/
theorem evenBetaIntegral_succ (a b : ℕ) :
    (2 * (a : ℝ) + 2 * b + 3) * evenBetaIntegral a (b + 1) =
      2 * (b + 1 : ℝ) * evenBetaIntegral a b := by
  have hinner (t : ℝ) : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * t) t := by
    convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_pow 2 t) using 1 <;> norm_num
  have hpow (t : ℝ) : HasDerivAt (fun x : ℝ => (1 - x ^ 2) ^ (b + 1))
      (-2 * (b + 1 : ℝ) * t * (1 - t ^ 2) ^ b) t := by
    convert (hinner t).pow (b + 1) using 1 <;> push_cast <;> ring
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (-1 : ℝ)) (b := 1)
    (u := fun t : ℝ => t ^ (2 * a + 1))
    (v := fun t : ℝ => (1 - t ^ 2) ^ (b + 1))
    (u' := fun t : ℝ => (2 * a + 1 : ℝ) * t ^ (2 * a))
    (v' := fun t : ℝ => -2 * (b + 1 : ℝ) * t * (1 - t ^ 2) ^ b)
    (fun x _ => by convert hasDerivAt_pow (2 * a + 1) x using 1 <;> simp)
    (fun x _ => hpow x)
    (by exact ((continuous_const.mul (continuous_id.pow (2 * a))).intervalIntegrable _ _))
    (by exact (by fun_prop : Continuous (fun t : ℝ =>
      -2 * (b + 1 : ℝ) * t * (1 - t ^ 2) ^ b)).intervalIntegrable _ _)
  have hsplit := evenBetaIntegral_split a b
  simp only [show (1 - (1 : ℝ) ^ 2) ^ (b + 1) = 0 by simp,
    show (1 - (-1 : ℝ) ^ 2) ^ (b + 1) = 0 by simp,
    mul_zero, sub_zero, zero_sub] at h
  have hleft : (∫ t : ℝ in (-1)..1,
      t ^ (2 * a + 1) * (-2 * (b + 1 : ℝ) * t * (1 - t ^ 2) ^ b)) =
      -2 * (b + 1 : ℝ) * evenBetaIntegral (a + 1) b := by
    unfold evenBetaIntegral
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  have hright : (∫ t : ℝ in (-1)..1,
      (2 * a + 1 : ℝ) * t ^ (2 * a) * (1 - t ^ 2) ^ (b + 1)) =
      (2 * a + 1 : ℝ) * evenBetaIntegral a (b + 1) := by
    unfold evenBetaIntegral
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
  rw [hleft, hright] at h
  nlinarith [congrArg (fun x : ℝ => 2 * (b + 1 : ℝ) * x) hsplit]

/-- Moving one even power from the monomial to the beta weight. -/
theorem evenBetaIntegral_prev (a b : ℕ) (ha : 0 < a) :
    (2 * (a : ℝ) - 1) * evenBetaIntegral (a - 1) b =
      (2 * (a : ℝ) + 2 * b + 1) * evenBetaIntegral a b := by
  have hsplit := evenBetaIntegral_split (a - 1) b
  have hsucc := evenBetaIntegral_succ (a - 1) b
  have hcast : (a - 1 : ℕ) + 1 = a := by omega
  rw [hcast] at hsplit
  have hcast' : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub ha]
    norm_num
  rw [hcast'] at hsucc
  nlinarith [congrArg (fun x : ℝ => 2 * (b + 1 : ℝ) * x) hsplit]

/-- Two successive beta recurrences, expressed without division. -/
theorem evenBetaIntegral_shift_two (a b : ℕ) (ha : 0 < a) :
    (2 * (a : ℝ) - 1) * (2 * (a : ℝ) + 2 * b + 3) *
        evenBetaIntegral (a - 1) (b + 2) =
      4 * (b + 1 : ℝ) * (b + 2 : ℝ) * evenBetaIntegral a b := by
  have h1 := evenBetaIntegral_succ (a - 1) b
  have h2 := evenBetaIntegral_succ (a - 1) (b + 1)
  have h3 := evenBetaIntegral_prev a b ha
  have hcast' : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
    rw [Nat.cast_sub ha]
    norm_num
  rw [hcast'] at h1 h2
  push_cast at h1 h2
  nlinarith [congrArg (fun x : ℝ => (2 * (a : ℝ) - 1) * x) h1,
    congrArg (fun x : ℝ => (2 * (a : ℝ) - 1) * (2 * (a : ℝ) + 2 * b + 3) * x) h2,
    congrArg (fun x : ℝ => 4 * (b + 1 : ℝ) * (b + 2 : ℝ) * x) h3]

/-- Closed finite product for the elementary beta-type integral. -/
theorem evenBetaIntegral_product (a b : ℕ) :
    evenBetaIntegral a b =
      (2 / (2 * (a : ℝ) + 1)) *
        ∏ j ∈ Finset.range b,
          (2 * (j + 1 : ℝ)) / (2 * (a : ℝ) + 2 * j + 3) := by
  induction b with
  | zero =>
      unfold evenBetaIntegral
      simp only [pow_zero, mul_one, Finset.prod_range_zero, mul_one]
      rw [integral_pow]
      push_cast
      have ha : (2 * (a : ℝ) + 1) ≠ 0 := by positivity
      field_simp [ha]
      ring
  | succ b ih =>
      have hrec := evenBetaIntegral_succ a b
      rw [Finset.prod_range_succ]
      rw [ih] at hrec
      have hden : (2 * (a : ℝ) + 2 * b + 3) ≠ 0 := by positivity
      have hA : evenBetaIntegral a (b + 1) =
          (2 * (b + 1 : ℝ) *
            (2 / (2 * (a : ℝ) + 1) *
              ∏ j ∈ Finset.range b,
                (2 * (j + 1 : ℝ)) / (2 * (a : ℝ) + 2 * j + 3))) /
            (2 * (a : ℝ) + 2 * b + 3) := by
        apply (eq_div_iff hden).2
        nlinarith [hrec]
      rw [hA]
      ring

/-- The first even Legendre polynomial is constant one. -/
theorem evenLegendrePolynomial_zero : evenLegendrePolynomial 0 = 1 := by
  norm_num [evenLegendrePolynomial, evenLegendreCoefficient]

/-- The first nonconstant even Legendre polynomial has the standard normalization. -/
theorem evenLegendrePolynomial_one :
    evenLegendrePolynomial 1 =
      Polynomial.C (-1 / 2 : ℝ) + Polynomial.C (3 / 2 : ℝ) * Polynomial.X ^ 2 := by
  norm_num [evenLegendrePolynomial, evenLegendreCoefficient, Finset.sum_range_succ]

/-- Every zonal moment is an explicit finite rational sum, with no analytic interchange. -/
theorem evenLegendre_zonal_integral (u : Sphere) (n k : ℕ) :
    (∫ x : Sphere,
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) *
        (evenLegendrePolynomial k).eval
          (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ∂sigma) =
      ∑ j ∈ Finset.range (k + 1),
        evenLegendreCoefficient k j / ((2 * (n + j) + 1 : ℕ) : ℝ) := by
  simp_rw [evenLegendrePolynomial_eval]
  exact even_projection_polynomial_integral u n (Finset.range (k + 1))
    (evenLegendreCoefficient k)

/-- The scalar interval moment has the same rational sum as the sphere moment. -/
theorem evenLegendre_interval_moment (n k : ℕ) :
    (1 / 2 : ℝ) * (∫ t : ℝ in (-1)..1,
      t ^ (2 * n) * (evenLegendrePolynomial k).eval t) =
      ∑ j ∈ Finset.range (k + 1),
        evenLegendreCoefficient k j / ((2 * (n + j) + 1 : ℕ) : ℝ) := by
  simp_rw [evenLegendrePolynomial_eval, Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hpoint (t : ℝ) :
        t ^ (2 * n) * (evenLegendreCoefficient k j * t ^ (2 * j)) =
          evenLegendreCoefficient k j * t ^ (2 * (n + j)) := by
      rw [mul_left_comm, ← pow_add]
      congr 1
      ring
    simp_rw [hpoint]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    have hden : (2 * (n + j : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hden]
    ring
  · intro j hj
    exact (by fun_prop : Continuous (fun t : ℝ =>
      t ^ (2 * n) * (evenLegendreCoefficient k j * t ^ (2 * j)))).intervalIntegrable _ _

/-- Sphere and scalar interval integrals agree with normalized uniform height. -/
theorem evenLegendre_sphere_eq_interval (u : Sphere) (n k : ℕ) :
    (∫ x : Sphere,
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) *
        (evenLegendrePolynomial k).eval
          (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ∂sigma) =
      (1 / 2 : ℝ) * (∫ t : ℝ in (-1)..1,
        t ^ (2 * n) * (evenLegendrePolynomial k).eval t) := by
  rw [evenLegendre_zonal_integral, evenLegendre_interval_moment]

/-- Rodrigues plus repeated integration by parts reduces every Legendre moment
    to one elementary beta-type integral. -/
theorem evenLegendre_interval_moment_rodrigues (n k : ℕ) :
    (1 / 2 : ℝ) * (∫ t : ℝ in (-1)..1,
      t ^ (2 * n) * (evenLegendrePolynomial k).eval t) =
      ((2 * n).descFactorial (2 * k) : ℝ) /
        (2 * ((2 : ℝ) ^ (2 * k) * ((2 * k).factorial : ℝ))) *
        evenBetaIntegral (n - k) (2 * k) := by
  let D : ℝ := (2 : ℝ) ^ (2 * k) * ((2 * k).factorial : ℝ)
  have hD : D ≠ 0 := by dsimp [D]; positivity
  have hpoint (t : ℝ) :
      (evenLegendrePolynomial k).eval t =
        ((Polynomial.derivative^[2 * k])
          (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k))).eval t / D := by
    have h := congrArg (Polynomial.eval t) (evenLegendrePolynomial_rodrigues k)
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at h
    apply (eq_div_iff hD).2
    simpa only [D, mul_comm] using h
  simp_rw [hpoint]
  have hfactor :
      (1 / 2 : ℝ) * (∫ t : ℝ in (-1)..1,
        t ^ (2 * n) *
          (((Polynomial.derivative^[2 * k])
            (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k))).eval t / D)) =
      1 / (2 * D) * (∫ t : ℝ in (-1)..1,
        t ^ (2 * n) *
          ((Polynomial.derivative^[2 * k])
            (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k))).eval t) := by
    have hdiv (t : ℝ) : t ^ (2 * n) *
        (((Polynomial.derivative^[2 * k])
          (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k))).eval t / D) =
        (t ^ (2 * n) *
          ((Polynomial.derivative^[2 * k])
            (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k))).eval t) / D := by ring
    simp_rw [hdiv]
    rw [intervalIntegral.integral_div]
    ring
  rw [hfactor, evenRodrigues_interval_moment k (2 * k) (by omega) (2 * n)]
  have hpow : (-1 : ℝ) ^ (2 * k) = 1 := by
    rw [pow_mul]
    norm_num
  rw [hpow, one_mul]
  have hsub : 2 * n - 2 * k = 2 * (n - k) := by omega
  rw [hsub]
  have hbase (t : ℝ) :
      (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (2 * k)).eval t =
        (1 - t ^ 2) ^ (2 * k) := by
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    rw [show t ^ 2 - 1 = -(1 - t ^ 2) by ring, neg_pow]
    simp
  simp_rw [hbase]
  unfold evenBetaIntegral
  dsimp [D]
  ring

/-- The normalized scalar moment of an even Legendre polynomial. -/
noncomputable def evenLegendreMoment (n k : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (∫ t : ℝ in (-1)..1,
    t ^ (2 * n) * (evenLegendrePolynomial k).eval t)

theorem evenLegendreMoment_rodrigues (n k : ℕ) :
    evenLegendreMoment n k =
      ((2 * n).descFactorial (2 * k) : ℝ) /
        (2 * ((2 : ℝ) ^ (2 * k) * ((2 * k).factorial : ℝ))) *
        evenBetaIntegral (n - k) (2 * k) :=
  evenLegendre_interval_moment_rodrigues n k

theorem evenLegendreMoment_zero (n : ℕ) :
    evenLegendreMoment n 0 = 1 / (2 * (n : ℝ) + 1) := by
  rw [evenLegendreMoment_rodrigues]
  simp only [mul_zero, pow_zero, Nat.factorial_zero, Nat.descFactorial_zero,
    Nat.sub_zero, Nat.cast_one, mul_one, one_div]
  rw [evenBetaIntegral_product]
  simp only [Finset.prod_range_zero, mul_one]
  ring

private theorem evenLegendre_descFactorial_step (n k : ℕ) (hk : k < n) :
    ((2 * n).descFactorial (2 * (k + 1)) : ℝ) =
      (2 * (n : ℝ) - 2 * k - 1) * (2 * (n : ℝ) - 2 * k) *
        ((2 * n).descFactorial (2 * k) : ℝ) := by
  have hnat : (2 * n).descFactorial (2 * (k + 1)) =
      (2 * n - (2 * k + 1)) * (2 * n - 2 * k) *
        (2 * n).descFactorial (2 * k) := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
      Nat.descFactorial_succ, Nat.descFactorial_succ]
    ring
  rw [hnat]
  have h1 : ((2 * n - (2 * k + 1) : ℕ) : ℝ) =
        2 * (n : ℝ) - 2 * k - 1 := by
    rw [Nat.cast_sub (by omega : 2 * k + 1 ≤ 2 * n)]
    push_cast; ring
  have h2 : ((2 * n - 2 * k : ℕ) : ℝ) = 2 * (n : ℝ) - 2 * k := by
    rw [Nat.cast_sub (by omega : 2 * k ≤ 2 * n)]
    push_cast; ring
  push_cast
  rw [h1, h2]

private theorem evenLegendre_denominator_step (k : ℕ) :
    (2 : ℝ) ^ (2 * (k + 1)) * ((2 * (k + 1)).factorial : ℝ) =
      4 * (2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2) *
        ((2 : ℝ) ^ (2 * k) * ((2 * k).factorial : ℝ)) := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

theorem evenLegendreMoment_step (n k : ℕ) (hk : k < n) :
    evenLegendreMoment n (k + 1) =
      (2 * ((n : ℝ) - k) / (2 * (n : ℝ) + 2 * k + 3)) *
        evenLegendreMoment n k := by
  rw [evenLegendreMoment_rodrigues, evenLegendreMoment_rodrigues]
  have hF := evenLegendre_descFactorial_step n k hk
  have hD := evenLegendre_denominator_step k
  have hB := evenBetaIntegral_shift_two (n - k) (2 * k) (by omega)
  have hnk : (((n - k : ℕ) : ℝ)) = (n : ℝ) - k := by
    rw [Nat.cast_sub (by omega : k ≤ n)]
  have hsub : n - (k + 1) = n - k - 1 := by omega
  rw [hF, hD, hsub]
  rw [hnk] at hB
  push_cast at hB
  have hd1 : (2 * (n : ℝ) + 2 * k + 3) ≠ 0 := by positivity
  have hd2 : (2 * (n : ℝ) - 2 * k - 1) ≠ 0 := by
    have : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
    linarith
  have hd3 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have hd4 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  have hd5 : ((2 : ℝ) ^ (2 * k) * ((2 * k).factorial : ℝ)) ≠ 0 := by positivity
  rw [show 2 * (k + 1) = 2 * k + 2 by omega]
  field_simp
  linear_combination
    (2 * (2 * (n : ℝ) - 2 * k) *
      ((2 * n).descFactorial (2 * k) : ℝ) *
        ((2 : ℝ) ^ (2 * k) * ((2 * k).factorial : ℝ))) * hB

/-- The scalar Rodrigues moment is exactly the model coefficient used in the
    Sobolev lower bound, in every degree (including vanishing above degree `n`). -/
theorem evenLegendreMoment_eq_model (n k : ℕ) :
    evenLegendreMoment n k = evenMomentModelCoefficient n k := by
  induction k with
  | zero =>
      rw [evenLegendreMoment_zero]
      simp [evenMomentModelCoefficient]
  | succ k ih =>
      by_cases hk : k < n
      · rw [evenLegendreMoment_step n k hk, ih]
        unfold evenMomentModelCoefficient
        simp only [if_pos (by omega : k + 1 ≤ n),
          if_pos (by omega : k ≤ n), Finset.prod_range_succ]
        conv_rhs =>
          rhs
          rhs
          change 2 * ((n : ℝ) - k) / (2 * (n : ℝ) + 2 * k + 3)
        ring
      · rw [evenLegendreMoment_rodrigues]
        have hzero : (2 * n).descFactorial (2 * (k + 1)) = 0 :=
          Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        rw [hzero]
        simp [evenMomentModelCoefficient, show ¬k + 1 ≤ n by omega]

/-- Actual normalized sphere zonal moments agree with the finite product. -/
theorem evenLegendre_zonal_integral_eq_model (u : Sphere) (n k : ℕ) :
    (∫ x : Sphere,
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) *
        (evenLegendrePolynomial k).eval
          (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ∂sigma) =
      evenMomentModelCoefficient n k := by
  rw [evenLegendre_sphere_eq_interval]
  exact evenLegendreMoment_eq_model n k

/-- The scalar coefficient arising from the radial differential (Hobson)
calculation, with its descending-factorial normalization exposed. -/
noncomputable def radialEvenMomentCoefficient (n k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((n + k).descFactorial (2 * k) : ℝ) /
    (((2 * n + 2 * k + 1 : ℕ) : ℝ) *
      ((2 * n + 2 * k).descFactorial (2 * k) : ℝ))

theorem radialEvenMomentCoefficient_zero (n : ℕ) :
    radialEvenMomentCoefficient n 0 = 1 / (2 * (n : ℝ) + 1) := by
  simp [radialEvenMomentCoefficient]

private theorem radialNumerator_step (n k : ℕ) (hk : k < n) :
    (((n + (k + 1)).descFactorial (2 * (k + 1)) : ℕ) : ℝ) =
      (n + (k : ℝ) + 1) * (n - (k : ℝ)) *
        ((n + k).descFactorial (2 * k) : ℝ) := by
  have hnat : (n + (k + 1)).descFactorial (2 * (k + 1)) =
      (n + k + 1) * (n + k - 2 * k) *
        (n + k).descFactorial (2 * k) := by
    rw [show n + (k + 1) = (n + k) + 1 by omega,
      show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
      Nat.succ_descFactorial_succ, Nat.descFactorial_succ]
    ring
  rw [hnat]
  have hsub : (((n + k - 2 * k : ℕ) : ℝ)) = (n : ℝ) - k := by
    rw [Nat.cast_sub (by omega : 2 * k ≤ n + k)]
    push_cast; ring
  push_cast
  rw [hsub]

private theorem radialDenominator_step (n k : ℕ) :
    (((2 * n + 2 * (k + 1)).descFactorial (2 * (k + 1)) : ℕ) : ℝ) =
      (2 * (n : ℝ) + 2 * k + 2) *
        (2 * (n : ℝ) + 2 * k + 1) *
          ((2 * n + 2 * k).descFactorial (2 * k) : ℝ) := by
  have hnat : (2 * n + 2 * (k + 1)).descFactorial (2 * (k + 1)) =
      (2 * n + 2 * k + 2) * (2 * n + 2 * k + 1) *
        (2 * n + 2 * k).descFactorial (2 * k) := by
    rw [show 2 * n + 2 * (k + 1) = (2 * n + 2 * k + 1) + 1 by omega,
      show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
      Nat.succ_descFactorial_succ,
      show 2 * n + 2 * k + 1 = (2 * n + 2 * k) + 1 by omega,
      Nat.succ_descFactorial_succ]
    ring
  rw [hnat]
  push_cast
  ring

theorem radialEvenMomentCoefficient_step (n k : ℕ) (hk : k < n) :
    radialEvenMomentCoefficient n (k + 1) =
      (2 * ((n : ℝ) - k) / (2 * (n : ℝ) + 2 * k + 3)) *
        radialEvenMomentCoefficient n k := by
  unfold radialEvenMomentCoefficient
  rw [radialNumerator_step n k hk, radialDenominator_step n k]
  have hpow : (2 : ℝ) ^ (2 * (k + 1)) = 4 * (2 : ℝ) ^ (2 * k) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
    norm_num
    ring
  rw [hpow]
  push_cast
  have hF : (((2 * n + 2 * k).descFactorial (2 * k) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by
      intro h
      have hh := Nat.descFactorial_eq_zero_iff_lt.mp h
      omega : (2 * n + 2 * k).descFactorial (2 * k) ≠ 0)
  have hd1 : 2 * (n : ℝ) + 2 * k + 1 ≠ 0 := by positivity
  have hd2 : 2 * (n : ℝ) + 2 * k + 2 ≠ 0 := by positivity
  have hd3 : 2 * (n : ℝ) + 2 * k + 3 ≠ 0 := by positivity
  field_simp [hF, hd1, hd2, hd3]
  ring

/-- The radial-differential coefficient is the same exact finite product as
the zonal Legendre moment and the Sobolev lower-bound model. -/
theorem radialEvenMomentCoefficient_eq_model (n k : ℕ) :
    radialEvenMomentCoefficient n k = evenMomentModelCoefficient n k := by
  induction k with
  | zero =>
      rw [radialEvenMomentCoefficient_zero]
      simp [evenMomentModelCoefficient]
  | succ k ih =>
      by_cases hk : k < n
      · rw [radialEvenMomentCoefficient_step n k hk, ih]
        unfold evenMomentModelCoefficient
        simp only [if_pos (by omega : k + 1 ≤ n),
          if_pos (by omega : k ≤ n), Finset.prod_range_succ]
        conv_rhs =>
          rhs
          rhs
          change 2 * ((n : ℝ) - k) / (2 * (n : ℝ) + 2 * k + 3)
        ring
      · unfold radialEvenMomentCoefficient
        have hzero : (n + (k + 1)).descFactorial (2 * (k + 1)) = 0 :=
          Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        rw [hzero]
        simp [evenMomentModelCoefficient, show ¬k + 1 ≤ n by omega]

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
