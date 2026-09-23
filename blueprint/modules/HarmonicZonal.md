# HarmonicZonal: an all-degree Rodrigues zonal harmonic

This module constructs a degree-`ℓ` homogeneous harmonic polynomial centered at any point `u` of the unit sphere. Its restriction is **exactly** the existing all-degree Rodrigues polynomial `(legendrePolynomial ℓ).eval (sphereInnerKernel u x)`. It imports `DistanceZonal` for that Rodrigues definition and `HarmonicBasis` for the polynomial Laplacian, radial square, and harmonic-submodule interface.

`zonalRodriguesCoefficient` records the coefficient obtained by expanding `(X²−1)^ℓ` and differentiating `ℓ` times. `legendrePolynomial_eq_zonalRodrigues_sum` proves the finite expansion in Lean. Terms with `2j<ℓ` have zero descending factorial. `zonalLinear u` is the multivariate polynomial `u·X`; its sphere evaluation is `sphereInnerKernel u x`, and the radial square evaluates to one. `zonalHomogenized` replaces each scalar monomial of degree `2j−ℓ` by `(u·X)^(2j−ℓ) radialSquare^(ℓ−j)`. The zero low coefficients permit a uniform degree-`ℓ` homogeneity proof, while evaluation on the sphere recovers the Rodrigues polynomial term for term.

For harmonicity, `zonalLinear_pow_laplacian_general` computes the Laplacian of every power of `u·X`, using `‖u‖²=1`. `radialPower_zonal_laplacian` combines this with `HarmonicBasis.radialPower_laplacian`. The two resulting contributions for adjacent Rodrigues modes cancel: `zonal_descFactorial_step` and `Nat.choose_succ_right_eq` prove the exact coefficient recurrence, and `zonalForward_add_backward_succ` translates it to multivariate terms. `zonalHomogenized_laplacian_zero` sums the cancellation, with the first backward and last forward terms zero.

`zonalHarmonic ℓ u` is therefore an actual member of `harmonicPolynomialSubmodule ℓ`. `restrict_zonalHarmonic` gives the exact Legendre evaluation identity, and `zonal_isSphericalHarmonic` gives the corresponding continuous spherical harmonic predicate. These results construct the zonal witness needed by the addition/Legendre identity; they do not themselves prove the addition kernel's normalization or reproducing pairing.

`legendrePolynomial_eval_one` independently verifies the Rodrigues normalization at `1`. It factors the Rodrigues numerator as `(X−1)^ℓ(X+1)^ℓ`, applies the finite Leibniz rule, and observes that only the term taking all `ℓ` derivatives of `(X−1)^ℓ` survives at `X=1`.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.DistanceZonal
import BEMOCFormalization.HarmonicBasis

/-! Homogeneous zonal polynomials from the all-degree Rodrigues expansion. -/

open scoped BigOperators

namespace BEMOC.Definitive

/-- Coefficients before eliminating zero terms in the Rodrigues expansion. -/
noncomputable def zonalRodriguesCoefficient (ℓ j : ℕ) : ℝ :=
  ((-1 : ℝ) ^ (ℓ - j) * (Nat.choose ℓ j : ℝ) *
    ((2 * j).descFactorial ℓ : ℝ)) /
    ((2 : ℝ) ^ ℓ * (ℓ.factorial : ℝ))

private noncomputable def zonalRodriguesBaseExpanded (ℓ : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (ℓ + 1),
    Polynomial.C ((-1 : ℝ) ^ (ℓ - j) * (Nat.choose ℓ j : ℝ)) *
      Polynomial.X ^ (2 * j)

private theorem zonalRodriguesBaseExpanded_eq (ℓ : ℕ) :
    zonalRodriguesBaseExpanded ℓ = legendreRodriguesBase ℓ := by
  unfold zonalRodriguesBaseExpanded legendreRodriguesBase
  rw [sub_eq_add_neg, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul, map_pow, map_natCast, map_neg, map_one]
  ring_nf

/-- The full Rodrigues polynomial as a finite monomial sum. The terms with
`2*j < ℓ` vanish through the falling factorial. -/
theorem legendrePolynomial_eq_zonalRodrigues_sum (ℓ : ℕ) :
    legendrePolynomial ℓ =
      ∑ j ∈ Finset.range (ℓ + 1),
        Polynomial.C (zonalRodriguesCoefficient ℓ j) *
          Polynomial.X ^ (2 * j - ℓ) := by
  unfold legendrePolynomial
  rw [← zonalRodriguesBaseExpanded_eq]
  unfold zonalRodriguesBaseExpanded
  rw [Polynomial.iterate_derivative_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.iterate_derivative_C_mul,
    Polynomial.iterate_derivative_X_pow_eq_C_mul]
  unfold zonalRodriguesCoefficient
  have hden : (2 : ℝ) ^ ℓ * (ℓ.factorial : ℝ) ≠ 0 := by positivity
  simp only [← mul_assoc]
  rw [← map_mul, ← map_mul]
  congr 1
  field_simp [hden]

/-- The linear polynomial `X ↦ u · X`. -/
noncomputable def zonalLinear (u : Sphere) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, MvPolynomial.C ((u : Ambient) i) * MvPolynomial.X i

theorem zonalLinear_isHomogeneous (u : Sphere) :
    (zonalLinear u).IsHomogeneous 1 := by
  unfold zonalLinear
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact (MvPolynomial.isHomogeneous_X ℝ i).C_mul _

theorem zonalLinear_eval_sphere (u x : Sphere) :
    MvPolynomial.eval (fun i => (x : Ambient) i) (zonalLinear u) =
      sphereInnerKernel u x := by
  simp [zonalLinear, sphereInnerKernel]

theorem zonalLinear_pderiv (u : Sphere) (i : Fin 3) :
    (MvPolynomial.pderiv i) (zonalLinear u) =
      MvPolynomial.C ((u : Ambient) i) := by
  classical
  unfold zonalLinear
  simp [map_sum, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
    Pi.single_apply]

theorem zonalLinear_unit (u : Sphere) :
    ∑ i : Fin 3, ((u : Ambient) i) ^ 2 = 1 := by
  simpa [EuclideanSpace.sphere_zero_eq 1 (by positivity)] using u.property

theorem zonalLinear_pow_laplacian (u : Sphere) (n : ℕ) :
    polynomialLaplacian (zonalLinear u ^ (n + 2)) =
      (((n + 2 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ))) •
        zonalLinear u ^ n := by
  classical
  have hstep (i : Fin 3) (m : ℕ) :
      (MvPolynomial.pderiv i) (zonalLinear u ^ (m + 1)) =
        (m + 1 : MvPolynomial (Fin 3) ℝ) * zonalLinear u ^ m *
          MvPolynomial.C ((u : Ambient) i) := by
    rw [MvPolynomial.pderiv_pow, zonalLinear_pderiv]
    simp
  have hconst (i : Fin 3) (m : ℕ) :
      (MvPolynomial.pderiv i) (m : MvPolynomial (Fin 3) ℝ) = 0 := by
    change (MvPolynomial.pderiv i) (MvPolynomial.C (m : ℝ)) = 0
    simp
  have htwice (i : Fin 3) :
      (MvPolynomial.pderiv i) ((MvPolynomial.pderiv i)
        (zonalLinear u ^ (n + 2))) =
        (MvPolynomial.C ((((n + 2 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ))))) *
          zonalLinear u ^ n * MvPolynomial.C (((u : Ambient) i) ^ 2) := by
    rw [show n + 2 = (n + 1) + 1 by omega, hstep i (n + 1)]
    simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
      zero_mul, mul_zero, zero_add, add_zero]
    rw [hstep i n]
    have hnat :
        (((n + 1 : ℕ) : MvPolynomial (Fin 3) ℝ) + 1) =
          ((n + 2 : ℕ) : MvPolynomial (Fin 3) ℝ) := by
      push_cast
      ring
    rw [hnat, hconst]
    simp only [← map_mul]
    push_cast
    simp only [map_add, map_mul, map_ofNat, map_natCast, map_one, map_pow]
    ring
  unfold polynomialLaplacian
  simp_rw [htwice]
  rw [← Finset.mul_sum]
  simp only [← map_sum]
  rw [zonalLinear_unit]
  simp [smul_eq_mul, MvPolynomial.smul_eq_C_mul]

theorem zonalLinear_pow_laplacian_general (u : Sphere) (n : ℕ) :
    polynomialLaplacian (zonalLinear u ^ n) =
      ((n * (n - 1) : ℕ) : ℝ) • zonalLinear u ^ (n - 2) := by
  rcases n with _ | _ | n
  · simp [polynomialLaplacian]
  · simp [polynomialLaplacian, zonalLinear_pderiv]
  · change polynomialLaplacian (zonalLinear u ^ (n + 2)) =
        (((n + 2 : ℕ) * (n + 1 : ℕ) : ℕ) : ℝ) • zonalLinear u ^ n
    simpa only [Nat.cast_mul] using zonalLinear_pow_laplacian u n

private theorem radialPower_zonal_laplacian
    (u : Sphere) (k n : ℕ) :
    polynomialLaplacian (radialSquare ^ k * zonalLinear u ^ n) =
      (2 * (k : ℝ) * (2 * (n : ℝ) + 2 * (k : ℝ) + 1)) •
        (radialSquare ^ (k - 1) * zonalLinear u ^ n) +
      ((n * (n - 1) : ℕ) : ℝ) •
        (radialSquare ^ k * zonalLinear u ^ (n - 2)) := by
  cases k with
  | zero =>
      simpa using zonalLinear_pow_laplacian_general u n
  | succ k =>
      have hhom := (zonalLinear_isHomogeneous u).pow n
      have hrad := radialPower_laplacian hhom k
      rw [hrad, zonalLinear_pow_laplacian_general]
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right,
        mul_smul, smul_mul_assoc]
      congr 1
      · congr 1
        push_cast
        ring
      · simp [MvPolynomial.smul_eq_C_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Homogenization of the Rodrigues polynomial in the radial square and the
linear form `u · X`. Vanishing low Rodrigues coefficients remove the apparent
degree mismatch when `2*j < ℓ`. -/
noncomputable def zonalHomogenized (ℓ : ℕ) (u : Sphere) :
    MvPolynomial (Fin 3) ℝ :=
  ∑ j ∈ Finset.range (ℓ + 1),
    MvPolynomial.C (zonalRodriguesCoefficient ℓ j) *
      radialSquare ^ (ℓ - j) * zonalLinear u ^ (2 * j - ℓ)

private noncomputable def zonalTerm (ℓ : ℕ) (u : Sphere) (j : ℕ) :
    MvPolynomial (Fin 3) ℝ :=
  zonalRodriguesCoefficient ℓ j •
    (radialSquare ^ (ℓ - j) * zonalLinear u ^ (2 * j - ℓ))

private noncomputable def zonalForward (ℓ : ℕ) (u : Sphere) (j : ℕ) :
    MvPolynomial (Fin 3) ℝ :=
  (zonalRodriguesCoefficient ℓ j *
      (2 * (ℓ - j : ℕ) * (2 * j + 1) : ℝ)) •
    (radialSquare ^ (ℓ - j - 1) * zonalLinear u ^ (2 * j - ℓ))

private noncomputable def zonalBackward (ℓ : ℕ) (u : Sphere) (j : ℕ) :
    MvPolynomial (Fin 3) ℝ :=
  (zonalRodriguesCoefficient ℓ j *
      (((2 * j - ℓ) * (2 * j - ℓ - 1) : ℕ) : ℝ)) •
    (radialSquare ^ (ℓ - j) * zonalLinear u ^ (2 * j - ℓ - 2))

private theorem zonalHomogenized_eq_sum_terms (ℓ : ℕ) (u : Sphere) :
    zonalHomogenized ℓ u =
      ∑ j ∈ Finset.range (ℓ + 1), zonalTerm ℓ u j := by
  unfold zonalHomogenized zonalTerm
  apply Finset.sum_congr rfl
  intro j hj
  simp only [MvPolynomial.smul_eq_C_mul, mul_assoc]

private theorem zonalTerm_laplacian
    (ℓ : ℕ) (u : Sphere) {j : ℕ} (hj : j ≤ ℓ) :
    polynomialLaplacian (zonalTerm ℓ u j) =
      zonalForward ℓ u j + zonalBackward ℓ u j := by
  by_cases hvalid : ℓ ≤ 2 * j
  · have hdeg :
        2 * (2 * j - ℓ) + 2 * (ℓ - j) + 1 = 2 * j + 1 := by omega
    have hdegR :
        2 * ((2 * j - ℓ : ℕ) : ℝ) + 2 * ((ℓ - j : ℕ) : ℝ) + 1 =
          2 * (j : ℝ) + 1 := by exact_mod_cast hdeg
    unfold zonalTerm zonalForward zonalBackward
    rw [polynomialLaplacian_smul, radialPower_zonal_laplacian]
    rw [smul_add, smul_smul, smul_smul]
    congr 1
    · congr 1
      rw [hdegR]
  · have hzero : zonalRodriguesCoefficient ℓ j = 0 := by
      unfold zonalRodriguesCoefficient
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : 2 * j < ℓ)]
      simp
    simp [zonalTerm, zonalForward, zonalBackward, hzero,
      polynomialLaplacian]

theorem zonalRodriguesCoefficient_eq_zero_of_lt
    {ℓ j : ℕ} (hj : 2 * j < ℓ) :
    zonalRodriguesCoefficient ℓ j = 0 := by
  unfold zonalRodriguesCoefficient
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr hj]
  simp

private theorem zonal_descFactorial_step (ℓ j : ℕ) :
    (2 * j + 2 - ℓ) * (2 * j + 1 - ℓ) *
        (2 * j + 2).descFactorial ℓ =
      (2 * j + 2) * (2 * j + 1) *
        (2 * j).descFactorial ℓ := by
  have h₁ := Nat.succ_descFactorial (2 * j + 1) ℓ
  have h₂ := Nat.succ_descFactorial (2 * j) ℓ
  change (2 * j + 2 - ℓ) * (2 * j + 2).descFactorial ℓ =
    (2 * j + 2) * (2 * j + 1).descFactorial ℓ at h₁
  change (2 * j + 1 - ℓ) * (2 * j + 1).descFactorial ℓ =
    (2 * j + 1) * (2 * j).descFactorial ℓ at h₂
  calc
    (2 * j + 2 - ℓ) * (2 * j + 1 - ℓ) *
        (2 * j + 2).descFactorial ℓ =
      (2 * j + 1 - ℓ) *
        ((2 * j + 2 - ℓ) * (2 * j + 2).descFactorial ℓ) := by ring
    _ = (2 * j + 2) *
        ((2 * j + 1 - ℓ) * (2 * j + 1).descFactorial ℓ) := by rw [h₁]; ring
    _ = (2 * j + 2) * (2 * j + 1) *
        (2 * j).descFactorial ℓ := by rw [h₂]; ring

private theorem zonal_coefficient_numerator_step (ℓ j : ℕ) :
    2 * (ℓ.choose j) * (ℓ - j) * (2 * j + 1) *
        (2 * j).descFactorial ℓ =
      (ℓ.choose (j + 1)) * (2 * j + 2 - ℓ) *
        (2 * j + 1 - ℓ) * (2 * j + 2).descFactorial ℓ := by
  have hdf := zonal_descFactorial_step ℓ j
  have hc := Nat.choose_succ_right_eq ℓ j
  calc
    2 * (ℓ.choose j) * (ℓ - j) * (2 * j + 1) *
        (2 * j).descFactorial ℓ =
      2 * ((ℓ.choose (j + 1)) * (j + 1)) * (2 * j + 1) *
        (2 * j).descFactorial ℓ := by rw [hc]; ring
    _ = (ℓ.choose (j + 1)) *
        ((2 * j + 2) * (2 * j + 1) * (2 * j).descFactorial ℓ) := by ring
    _ = (ℓ.choose (j + 1)) *
        ((2 * j + 2 - ℓ) * (2 * j + 1 - ℓ) *
          (2 * j + 2).descFactorial ℓ) := by rw [hdf]
    _ = _ := by ring

private theorem zonalRodriguesCoefficient_recurrence
    {ℓ j : ℕ} (hj : j < ℓ) :
    zonalRodriguesCoefficient ℓ j *
        (2 * (ℓ - j : ℕ) * (2 * j + 1) : ℝ) +
      zonalRodriguesCoefficient ℓ (j + 1) *
        ((2 * j + 2 - ℓ : ℕ) * (2 * j + 1 - ℓ : ℕ) : ℝ) = 0 := by
  have hsub : ℓ - j = (ℓ - (j + 1)) + 1 := by omega
  have hsign : (-1 : ℝ) ^ (ℓ - j) =
      -((-1 : ℝ) ^ (ℓ - (j + 1))) := by
    rw [hsub, pow_succ]
    ring
  have hnum := zonal_coefficient_numerator_step ℓ j
  have hnumR := congrArg (fun z : ℕ => (z : ℝ)) hnum
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hnumR
  unfold zonalRodriguesCoefficient
  rw [hsign]
  have hden : (2 : ℝ) ^ ℓ * (ℓ.factorial : ℝ) ≠ 0 := by positivity
  rw [show 2 * (j + 1) = 2 * j + 2 by omega]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  linear_combination
    (-((-1 : ℝ) ^ (ℓ - (j + 1))) *
      (((2 : ℝ) ^ ℓ * (ℓ.factorial : ℝ))⁻¹)) * hnumR

private theorem zonalBackward_zero (ℓ : ℕ) (u : Sphere) :
    zonalBackward ℓ u 0 = 0 := by
  simp [zonalBackward]

private theorem zonalForward_last (ℓ : ℕ) (u : Sphere) :
    zonalForward ℓ u ℓ = 0 := by
  simp [zonalForward]

private theorem zonalForward_add_backward_succ
    (ℓ : ℕ) (u : Sphere) {j : ℕ} (hj : j < ℓ) :
    zonalForward ℓ u j + zonalBackward ℓ u (j + 1) = 0 := by
  by_cases hvalid : ℓ ≤ 2 * j
  · have hrad : ℓ - j - 1 = ℓ - (j + 1) := by omega
    have hdot : 2 * (j + 1) - ℓ - 2 = 2 * j - ℓ := by omega
    have hfac1 : 2 * (j + 1) - ℓ = 2 * j + 2 - ℓ := by omega
    have hfac2 : 2 * j + 2 - ℓ - 1 = 2 * j + 1 - ℓ := by omega
    unfold zonalForward zonalBackward
    rw [hrad, hdot, hfac1, hfac2]
    rw [← add_smul]
    norm_num only [Nat.cast_mul]
    rw [zonalRodriguesCoefficient_recurrence hj]
    simp
  · have hc : zonalRodriguesCoefficient ℓ j = 0 :=
      zonalRodriguesCoefficient_eq_zero_of_lt (by omega)
    have hsmall : 2 * (j + 1) - ℓ ≤ 1 := by omega
    have hcases : 2 * (j + 1) - ℓ = 0 ∨
        2 * (j + 1) - ℓ = 1 := by omega
    have hprod :
        (2 * (j + 1) - ℓ) * (2 * (j + 1) - ℓ - 1) = 0 := by
      rcases hcases with h0 | h1
      · simp [h0]
      · simp [h1]
    simp [zonalForward, zonalBackward, hc, hprod]

theorem zonalHomogenized_eval_sphere (ℓ : ℕ) (u x : Sphere) :
    MvPolynomial.eval (fun i => (x : Ambient) i)
      (zonalHomogenized ℓ u) =
      (legendrePolynomial ℓ).eval (sphereInnerKernel u x) := by
  rw [legendrePolynomial_eq_zonalRodrigues_sum]
  simp [zonalHomogenized, Polynomial.eval_finset_sum,
    radialSquare_eval_sphere, zonalLinear_eval_sphere]

theorem zonalHomogenized_isHomogeneous (ℓ : ℕ) (u : Sphere) :
    (zonalHomogenized ℓ u).IsHomogeneous ℓ := by
  unfold zonalHomogenized
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  by_cases hvalid : ℓ ≤ 2 * j
  · have hjle : j ≤ ℓ := by
      have := Finset.mem_range.mp hj
      omega
    have hdeg : 2 * (ℓ - j) + (2 * j - ℓ) = ℓ := by omega
    have h := ((radialPower_isHomogeneous (ℓ - j)).mul
      ((zonalLinear_isHomogeneous u).pow (2 * j - ℓ))).C_mul
        (zonalRodriguesCoefficient ℓ j)
    simpa only [mul_assoc, one_mul, hdeg] using h
  · have hzero : zonalRodriguesCoefficient ℓ j = 0 :=
      zonalRodriguesCoefficient_eq_zero_of_lt (by omega)
    simpa only [hzero, map_zero, zero_mul] using
      (MvPolynomial.isHomogeneous_zero (σ := Fin 3) (R := ℝ) ℓ)

/-- The Rodrigues homogenization is a genuine harmonic polynomial in three
variables. Adjacent radial and linear-power Laplacian terms cancel by the
coefficient recurrence. -/
theorem zonalHomogenized_laplacian_zero (ℓ : ℕ) (u : Sphere) :
    polynomialLaplacian (zonalHomogenized ℓ u) = 0 := by
  rw [zonalHomogenized_eq_sum_terms, polynomialLaplacian_sum]
  have hterms :
      (∑ j ∈ Finset.range (ℓ + 1),
        polynomialLaplacian (zonalTerm ℓ u j)) =
      ∑ j ∈ Finset.range (ℓ + 1),
        (zonalForward ℓ u j + zonalBackward ℓ u j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact zonalTerm_laplacian ℓ u (by
      have := Finset.mem_range.mp hj
      omega)
  rw [hterms, Finset.sum_add_distrib]
  have hforward :
      (∑ j ∈ Finset.range (ℓ + 1), zonalForward ℓ u j) =
        ∑ j ∈ Finset.range ℓ, zonalForward ℓ u j := by
    rw [Finset.sum_range_succ, zonalForward_last, add_zero]
  have hbackward :
      (∑ j ∈ Finset.range (ℓ + 1), zonalBackward ℓ u j) =
        ∑ j ∈ Finset.range ℓ, zonalBackward ℓ u (j + 1) := by
    rw [Finset.sum_range_succ', zonalBackward_zero, add_zero]
  rw [hforward, hbackward, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  exact zonalForward_add_backward_succ ℓ u (Finset.mem_range.mp hj)

/-- The degree-`ℓ` zonal harmonic centered at `u`. -/
noncomputable def zonalHarmonic (ℓ : ℕ) (u : Sphere) :
    harmonicPolynomialSubmodule ℓ :=
  ⟨zonalHomogenized ℓ u,
    mem_harmonicPolynomialSubmodule.mpr
      ⟨zonalHomogenized_isHomogeneous ℓ u,
        zonalHomogenized_laplacian_zero ℓ u⟩⟩

theorem restrict_zonalHarmonic (ℓ : ℕ) (u x : Sphere) :
    restrictPolynomial (zonalHarmonic ℓ u).val x =
      (legendrePolynomial ℓ).eval (sphereInnerKernel u x) := by
  exact zonalHomogenized_eval_sphere ℓ u x

theorem zonal_isSphericalHarmonic (ℓ : ℕ) (u : Sphere) :
    IsSphericalHarmonic ℓ (restrictPolynomial (zonalHarmonic ℓ u).val) :=
  restrictPolynomial_isSphericalHarmonic (zonalHarmonic ℓ u).property

/-- Rodrigues normalization at the north pole. -/
theorem legendrePolynomial_eval_one (ℓ : ℕ) :
    (legendrePolynomial ℓ).eval 1 = 1 := by
  have hbase : legendreRodriguesBase ℓ =
      ((Polynomial.X : Polynomial ℝ) - 1) ^ ℓ *
        (Polynomial.X + 1) ^ ℓ := by
    unfold legendreRodriguesBase
    have hfactor :
        (Polynomial.X : Polynomial ℝ) ^ 2 - 1 =
          (Polynomial.X - 1) * (Polynomial.X + 1) := by ring
    rw [hfactor, mul_pow]
  have hder :
      ((Polynomial.derivative^[ℓ]) (legendreRodriguesBase ℓ)).eval 1 =
        (ℓ.factorial : ℝ) * 2 ^ ℓ := by
    rw [hbase, Polynomial.iterate_derivative_mul,
      Polynomial.eval_finset_sum]
    rw [Finset.sum_eq_single 0]
    · simp only [Nat.sub_zero, Function.iterate_zero, id_eq,
        Nat.choose_zero_right, one_nsmul]
      rw [show (1 : Polynomial ℝ) = Polynomial.C 1 by rfl,
        Polynomial.iterate_derivative_X_sub_pow_self]
      norm_num
    · intro j hj hj0
      have hle : j ≤ ℓ := by
        have := Finset.mem_range.mp hj
        omega
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      rw [show (1 : Polynomial ℝ) = Polynomial.C 1 by rfl,
        Polynomial.iterate_derivative_X_sub_pow]
      simp [hjpos, hle, Nat.sub_sub_self hle, hj0]
    · simp
  unfold legendrePolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_C, hder]
  have hden : (2 : ℝ) ^ ℓ * (ℓ.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
