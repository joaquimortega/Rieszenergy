# SobolevMomentAction: exact even projection kernel action

This module proves the Funk–Hecke action needed for the universal Sobolev cubature lower bound. For every homogeneous harmonic polynomial `H` of degree `2k`, every unit direction `u`, and every `n`, `even_projection_harmonic_action` identifies the sphere integral of `H(x) ⟪u,x⟫^(2n)` with `evenMomentModelCoefficient n k * H(u)`. The formula includes `k > n`, where the coefficient is zero. `odd_projection_harmonic_action` proves zero action in every odd harmonic degree.

The proof uses the finite coefficient integration and polynomial differential bridge in `SobolevLowerBound`, the harmonic radial differentiation theorem in `HarmonicRadialDifferentiation`, and the exact scalar coefficient equality in `ZonalPolynomials`. The action theorem is unconditional and uses the actual surface measure and harmonic polynomial subspace. `SobolevMomentSpectral` uses this action to identify the centered test's Fourier coefficients and prove its spectral norm estimate.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.HarmonicRadialDifferentiation
import BEMOCFormalization.ZonalPolynomials

/-! The actual Funk–Hecke action of the even projection-power kernel on
homogeneous spherical harmonics. -/

open scoped BigOperators
open MeasureTheory

namespace BEMOC.Definitive

/-- Every even harmonic degree is an eigenfunction of the even projection
kernel with the explicit positive coefficient used in the Sobolev estimate. -/
theorem even_projection_harmonic_action
    {H : MvPolynomial (Fin 3) ℝ} {k : ℕ}
    (hH : H ∈ harmonicPolynomialSubmodule (2 * k))
    (u : Sphere) (n : ℕ) :
    (∫ x : Sphere,
      MvPolynomial.eval (fun i => (x : Ambient) i) H *
        (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) ∂sigma) =
      evenMomentModelCoefficient n k *
        MvPolynomial.eval (fun i => (u : Ambient) i) H := by
  have hhom := (mem_harmonicPolynomialSubmodule.mp hH).1
  have hbridge := polynomialDifferentialOperator_radial_moment hhom
    (n + k) (2 * n) (by omega : 2 * n + 2 * k = 2 * (n + k)) (u : Ambient)
  rw [harmonic_radial_differentiation (n + k) (2 * k) H hH] at hbridge
  simp only [map_mul, MvPolynomial.eval_C, map_pow,
    radialSquare_eval_sphere, one_pow, one_mul, mul_one] at hbridge
  rw [← radialEvenMomentCoefficient_eq_model n k]
  have hdenNat : (2 * (n + k)).descFactorial (2 * k) ≠ 0 := by
    simp only [ne_eq, Nat.descFactorial_eq_zero_iff_lt]
    omega
  have hden : (((2 * (n + k)).descFactorial (2 * k) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hdenNat
  have hbase : (((2 * (n + k) + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hcast : (((2 * n + 2 * k + 1 : ℕ) : ℝ)) =
      (((2 * (n + k) + 1 : ℕ) : ℝ)) := by
    congr 1
    omega
  have hcastFac : ((2 * n + 2 * k).descFactorial (2 * k) : ℕ) =
      (2 * (n + k)).descFactorial (2 * k) := by
    congr 1
    omega
  rw [radialEvenMomentCoefficient, hcast, hcastFac]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero hbase hden)).2
  calc
    _ = (((2 * (n + k)).descFactorial (2 * k) : ℕ) : ℝ) *
          (∫ x : Sphere,
            MvPolynomial.eval (fun i => (x : Ambient) i) H *
              (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^
                (2 * n) ∂sigma) *
          (((2 * (n + k) + 1 : ℕ) : ℝ)) := by ring
    _ = (2 : ℝ) ^ (2 * k) *
          ((n + k).descFactorial (2 * k) : ℝ) *
          MvPolynomial.eval (fun i => (u : Ambient) i) H := by
            have hmul := congrArg (fun t : ℝ =>
              t * (((2 * (n + k) + 1 : ℕ) : ℝ))) hbridge
            have hcancel :
                (1 / (((2 * (n + k) + 1 : ℕ) : ℝ)) *
                  (((2 ^ (2 * k) * (n + k).descFactorial (2 * k) : ℕ) : ℝ) *
                    MvPolynomial.eval (fun i => (u : Ambient) i) H)) *
                  (((2 * (n + k) + 1 : ℕ) : ℝ)) =
                (((2 ^ (2 * k) * (n + k).descFactorial (2 * k) : ℕ) : ℝ) *
                  MvPolynomial.eval (fun i => (u : Ambient) i) H) := by
                    field_simp
            dsimp only at hmul
            rw [hcancel] at hmul
            push_cast at hmul ⊢
            nlinarith [hmul]

/-- The even projection kernel annihilates every odd harmonic degree. -/
theorem odd_projection_harmonic_action
    {H : MvPolynomial (Fin 3) ℝ} {k : ℕ}
    (hH : H ∈ harmonicPolynomialSubmodule (2 * k + 1))
    (u : Sphere) (n : ℕ) :
    (∫ x : Sphere,
      MvPolynomial.eval (fun i => (x : Ambient) i) H *
        (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) ∂sigma) =
      0 := by
  exact homogeneous_odd_projection_moment_zero
    (mem_harmonicPolynomialSubmodule.mp hH).1 (2 * n) (n + k)
    (by omega) (u : Ambient)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
