# HarmonicAdditionLegendre: exact all-degree addition formula

This module proves `harmonic_addition_legendre (Y : HarmonicBasis) : HarmonicAdditionLegendre Y` without an additional hypothesis. It imports the explicit zonal harmonic from `HarmonicZonal`, the target statement from `DistanceKernelExpansion`, finite harmonic spans, and the existing radial moment identity. The result identifies the basis kernel with `(2ℓ+1) Pℓ(⟪x,y⟫)` for every degree and both sphere points.

`top_projection_harmonic_action` applies the proved polynomial differential-operator radial moment identity and harmonic radial differentiation to a degree-`ℓ` harmonic multiplied by the top monomial `⟪u,x⟫^ℓ`. `harmonic_orthogonal_lower_homogeneous` uses Fischer decomposition to place the restriction of any homogeneous polynomial of lower degree in the span of lower-degree harmonics, then applies the proved cross-degree orthogonality. `lower_projection_harmonic_zero` specializes this to the lower powers of the zonal linear polynomial.

`legendre_projection_harmonic_action` expands the Rodrigues polynomial into finite monomials. Terms with exponent below `ℓ` vanish by orthogonality (or have zero coefficient); the leading coefficient cancels the scalar in the top-monomial action exactly, giving `1/(2ℓ+1)` times evaluation at the center. Finally, `harmonic_addition_legendre` expands `zonalHarmonic ℓ u` in the complete finite orthonormal basis `harmonicBasisDegree Y ℓ`. The projection formula supplies every basis coefficient, and pointwise evaluation yields the stated addition kernel identity. No Legendre norm theorem or scalar distance expansion is used in this proof.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.HarmonicZonal
import BEMOCFormalization.DistanceKernelExpansion
import BEMOCFormalization.HarmonicFiniteSpan
import BEMOCFormalization.SobolevMomentAction

/-! The all-degree addition identity from the explicit zonal harmonic. -/

open scoped BigOperators
open scoped InnerProductSpace
open MeasureTheory

namespace BEMOC.Definitive

/-- The top projection monomial acts by a scalar on every degree-`ℓ`
harmonic. This is Hobson's radial differentiation identity at matching
polynomial degrees. -/
theorem top_projection_harmonic_action
    {H : MvPolynomial (Fin 3) ℝ} {ℓ : ℕ}
    (hH : H ∈ harmonicPolynomialSubmodule ℓ) (u : Sphere) :
    (∫ x : Sphere,
      MvPolynomial.eval (fun i => (x : Ambient) i) H *
        (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ ℓ ∂sigma) =
      ((2 : ℝ) ^ ℓ * (ℓ.factorial : ℝ) /
        (((2 * ℓ + 1 : ℕ) : ℝ) *
          ((2 * ℓ).descFactorial ℓ : ℝ))) *
        MvPolynomial.eval (fun i => (u : Ambient) i) H := by
  have hhom := (mem_harmonicPolynomialSubmodule.mp hH).1
  have hbridge := polynomialDifferentialOperator_radial_moment
    hhom ℓ ℓ (by omega : ℓ + ℓ = 2 * ℓ) (u : Ambient)
  rw [harmonic_radial_differentiation ℓ ℓ H hH] at hbridge
  simp only [map_mul, MvPolynomial.eval_C, map_pow,
    radialSquare_eval_sphere, one_pow, one_mul, mul_one,
    Nat.sub_self, pow_zero] at hbridge
  have hden : (((2 * ℓ).descFactorial ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show (2 * ℓ).descFactorial ℓ ≠ 0 by
      simp only [ne_eq, Nat.descFactorial_eq_zero_iff_lt]
      omega)
  have hbase : (((2 * ℓ + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [Nat.descFactorial_self] at hbridge
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero hbase hden)).2
  push_cast at hbridge ⊢
  let I : ℝ := ∫ x : Sphere,
    MvPolynomial.eval (fun i => (x : Ambient) i) H *
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ ℓ ∂sigma
  change 1 / (2 * (ℓ : ℝ) + 1) *
      (2 ^ ℓ * (ℓ.factorial : ℝ) *
        MvPolynomial.eval (fun i => (u : Ambient) i) H) =
      ((2 * ℓ).descFactorial ℓ : ℝ) * I at hbridge
  change I * ((2 * (ℓ : ℝ) + 1) *
      ((2 * ℓ).descFactorial ℓ : ℝ)) = _
  have hbase' : (2 * (ℓ : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hbase'] at hbridge
  nlinarith [hbridge]

/-- A harmonic of degree `ℓ` is orthogonal to every lower-degree
homogeneous polynomial on the sphere. -/
theorem harmonic_orthogonal_lower_homogeneous
    {H p : MvPolynomial (Fin 3) ℝ} {ℓ q : ℕ}
    (hH : H ∈ harmonicPolynomialSubmodule ℓ)
    (hp : p.IsHomogeneous q) (hq : q < ℓ) :
    (∫ x : Sphere, restrictPolynomial H x * restrictPolynomial p x ∂sigma) = 0 := by
  let zeroSet : Submodule ℝ C(Sphere, ℝ) := {
    carrier := {f | (∫ x : Sphere, restrictPolynomial H x * f x ∂sigma) = 0}
    zero_mem' := by simp
    add_mem' := by
      intro f g hf hg
      change (∫ x : Sphere, restrictPolynomial H x * (f + g) x ∂sigma) = 0
      simp only [ContinuousMap.add_apply, mul_add]
      change (∫ x : Sphere, (restrictPolynomial H * f) x +
        (restrictPolynomial H * g) x ∂sigma) = 0
      rw [integral_add
        (continuous_integrable_sigma (restrictPolynomial H * f))
        (continuous_integrable_sigma (restrictPolynomial H * g))]
      simp only [Set.mem_setOf_eq] at hf hg
      rw [show (∫ x : Sphere, (restrictPolynomial H * f) x ∂sigma) = 0 from hf,
        show (∫ x : Sphere, (restrictPolynomial H * g) x ∂sigma) = 0 from hg]
      simp
    smul_mem' := by
      intro c f hf
      change (∫ x : Sphere, restrictPolynomial H x * (c • f) x ∂sigma) = 0
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      have hfun : (fun x : Sphere => restrictPolynomial H x * (c * f x)) =
          fun x : Sphere => c * (restrictPolynomial H * f) x := by
        funext x
        simp only [ContinuousMap.mul_apply]
        ring
      rw [hfun]
      rw [integral_const_mul]
      exact mul_eq_zero_of_right c hf }
  have hs : harmonicRestrictionSpanUpTo q ≤ zeroSet := by
    apply Submodule.span_le.mpr
    intro f hf
    obtain ⟨n, hn, ⟨h, hh, hlap, hpoint⟩⟩ := hf
    have hfeq : f = restrictPolynomial h := by
      ext x
      exact hpoint x
    rw [hfeq]
    change (∫ x : Sphere, restrictPolynomial H x * restrictPolynomial h x ∂sigma) = 0
    exact crossDegreeHarmonicOrthogonality (by omega : ℓ ≠ n) hH ⟨hh, hlap⟩
  exact hs (homogeneous_restriction_mem_spanUpTo hp le_rfl)

theorem lower_projection_harmonic_zero
    {H : MvPolynomial (Fin 3) ℝ} {ℓ q : ℕ}
    (hH : H ∈ harmonicPolynomialSubmodule ℓ) (u : Sphere)
    (hq : q < ℓ) :
    (∫ x : Sphere,
      restrictPolynomial H x *
        (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ q ∂sigma) = 0 := by
  have h := harmonic_orthogonal_lower_homogeneous hH
    ((zonalLinear_isHomogeneous u).pow q) (by simpa using hq)
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [restrictPolynomial_apply, map_pow, zonalLinear_eval_sphere,
    sphereInnerKernel_eq_inner]

/-- Rodrigues orthogonality leaves only its leading monomial. Its coefficient
exactly cancels the scalar in the top monomial projection formula. -/
theorem legendre_projection_harmonic_action
    {H : MvPolynomial (Fin 3) ℝ} {ℓ : ℕ}
    (hH : H ∈ harmonicPolynomialSubmodule ℓ) (u : Sphere) :
    (∫ x : Sphere, restrictPolynomial H x *
      (legendrePolynomial ℓ).eval (sphereInnerKernel u x) ∂sigma) =
      (1 / (2 * (ℓ : ℝ) + 1)) * restrictPolynomial H u := by
  classical
  let t (x : Sphere) : ℝ := sphereInnerKernel u x
  have hterm (j : ℕ) (hj : j ≤ ℓ) :
      (∫ x : Sphere, restrictPolynomial H x *
        (zonalRodriguesCoefficient ℓ j * t x ^ (2 * j - ℓ)) ∂sigma) =
        if j = ℓ then
          (1 / (2 * (ℓ : ℝ) + 1)) * restrictPolynomial H u else 0 := by
    by_cases hlast : j = ℓ
    · subst j
      simp only [if_pos rfl, t, show 2 * ℓ - ℓ = ℓ by omega]
      rw [show (∫ x : Sphere,
          restrictPolynomial H x *
            (zonalRodriguesCoefficient ℓ ℓ *
              sphereInnerKernel u x ^ ℓ) ∂sigma) =
          zonalRodriguesCoefficient ℓ ℓ *
            (∫ x : Sphere, restrictPolynomial H x *
              sphereInnerKernel u x ^ ℓ ∂sigma) by
            simp_rw [mul_left_comm (restrictPolynomial H _) _]
            rw [integral_const_mul]]
      rw [show (∫ x : Sphere, restrictPolynomial H x *
          sphereInnerKernel u x ^ ℓ ∂sigma) =
            ((2 : ℝ) ^ ℓ * (ℓ.factorial : ℝ) /
              (((2 * ℓ + 1 : ℕ) : ℝ) *
                ((2 * ℓ).descFactorial ℓ : ℝ))) *
              restrictPolynomial H u by
            simpa only [sphereInnerKernel_eq_inner, restrictPolynomial_apply]
              using top_projection_harmonic_action hH u]
      unfold zonalRodriguesCoefficient
      simp only [Nat.sub_self, pow_zero, one_mul, Nat.choose_self]
      have hfact : ((ℓ.factorial : ℕ) : ℝ) ≠ 0 := by positivity
      have hdesc : (((2 * ℓ).descFactorial ℓ : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show (2 * ℓ).descFactorial ℓ ≠ 0 by
          simp only [ne_eq, Nat.descFactorial_eq_zero_iff_lt]
          omega)
      push_cast
      field_simp [hfact, hdesc]
      ring
    · simp only [if_neg hlast]
      by_cases hsmall : 2 * j < ℓ
      · rw [zonalRodriguesCoefficient_eq_zero_of_lt hsmall]
        simp
      · have hq : 2 * j - ℓ < ℓ := by omega
        have hzero := lower_projection_harmonic_zero hH u hq
        simp only [← sphereInnerKernel_eq_inner] at hzero
        convert congrArg (fun z : ℝ => zonalRodriguesCoefficient ℓ j * z) hzero using 1
        · rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with x
          ring
        · simp
  rw [legendrePolynomial_eq_zonalRodrigues_sum]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  simp_rw [Finset.mul_sum]
  change (∫ x : Sphere, ∑ j ∈ Finset.range (ℓ + 1),
      restrictPolynomial H x *
        (zonalRodriguesCoefficient ℓ j * t x ^ (2 * j - ℓ)) ∂sigma) = _
  rw [integral_finset_sum]
  · rw [Finset.sum_congr rfl (fun j hj => hterm j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))]
    simp
  · intro j hj
    have ht : t = restrictPolynomial (zonalLinear u) := by
      funext x
      exact (zonalLinear_eval_sphere u x).symm
    rw [ht]
    simpa only [ContinuousMap.mul_apply, ContinuousMap.pow_apply,
      ContinuousMap.coe_const, Pi.mul_apply] using
      continuous_integrable_sigma
        (restrictPolynomial H *
          (ContinuousMap.const Sphere (zonalRodriguesCoefficient ℓ j) *
            (restrictPolynomial (zonalLinear u)) ^ (2 * j - ℓ)))

/-- The addition formula in every degree, with the exact Rodrigues
normalization and the same basis used by the energy expansion. -/
theorem harmonic_addition_legendre (Y : HarmonicBasis) :
    HarmonicAdditionLegendre Y := by
  intro ℓ u y
  let b := harmonicBasisDegree Y ℓ
  let p := zonalHarmonic ℓ u
  have hcoef (k : Fin (2 * ℓ + 1)) :
      ⟪b k, p⟫_ℝ =
        (1 / (2 * (ℓ : ℝ) + 1)) * Y.function ℓ k u := by
    change harmonicL2Inner ℓ (b k) p = _
    rw [harmonicBasisDegree_apply]
    unfold harmonicL2Inner
    rw [harmonicBasisPolynomial_restrict]
    simp_rw [show restrictPolynomial p.val =
        fun x : Sphere => (legendrePolynomial ℓ).eval (sphereInnerKernel u x) from
      by ext x; exact restrict_zonalHarmonic ℓ u x]
    have h := legendre_projection_harmonic_action
      (harmonicBasisPolynomial Y ℓ k).property u
    rw [harmonicBasisPolynomial_restrict] at h
    exact h
  have hexp := b.sum_repr' p
  have heval := congrArg (fun q : harmonicPolynomialSubmodule ℓ =>
      restrictPolynomial q.val y) hexp
  change (restrictHarmonicLinearMap ℓ
      (∑ k, ⟪b k, p⟫_ℝ • b k)) y =
    (restrictHarmonicLinearMap ℓ p) y at heval
  simp only [map_sum, map_smul, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul] at heval
  change (∑ k, ⟪b k, p⟫_ℝ * restrictPolynomial (b k).val y) =
    restrictPolynomial p.val y at heval
  rw [show restrictPolynomial p.val y =
      (legendrePolynomial ℓ).eval (sphereInnerKernel u y) from
    restrict_zonalHarmonic ℓ u y] at heval
  have hbase (k : Fin (2 * ℓ + 1)) :
      restrictPolynomial (b k).val y = Y.function ℓ k y := by
    rw [harmonicBasisDegree_apply, harmonicBasisPolynomial_restrict]
  simp_rw [hcoef, hbase] at heval
  unfold harmonicAdditionKernel
  -- Multiply the basis expansion by the nonzero dimension.
  have hdim : (2 * (ℓ : ℝ) + 1) ≠ 0 := by positivity
  have hterm (k : Fin (2 * ℓ + 1)) :
      (1 / (2 * (ℓ : ℝ) + 1) * Y.function ℓ k u) * Y.function ℓ k y =
        (Y.function ℓ k u * Y.function ℓ k y) /
          (2 * (ℓ : ℝ) + 1) := by ring
  simp_rw [hterm] at heval
  rw [← Finset.sum_div] at heval
  have hresult := (div_eq_iff hdim).mp (show
    (∑ k : Fin (2 * ℓ + 1), Y.function ℓ k u * Y.function ℓ k y) /
      (2 * (ℓ : ℝ) + 1) =
      (legendrePolynomial ℓ).eval (sphereInnerKernel u y) by
    simpa only [div_eq_mul_inv] using heval)
  simpa only [mul_comm] using hresult

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.HarmonicZonal
import BEMOCFormalization.DistanceKernelExpansion
import BEMOCFormalization.HarmonicFiniteSpan
import BEMOCFormalization.SobolevMomentAction

/-! The all-degree addition identity from the explicit zonal harmonic. -/

open scoped BigOperators
open scoped InnerProductSpace
open MeasureTheory

namespace BEMOC.Definitive

/-- The top projection monomial acts by a scalar on every degree-`ℓ`
harmonic. This is Hobson's radial differentiation identity at matching
polynomial degrees. -/
theorem top_projection_harmonic_action
    {H : MvPolynomial (Fin 3) ℝ} {ℓ : ℕ}
    (hH : H ∈ harmonicPolynomialSubmodule ℓ) (u : Sphere) :
    (∫ x : Sphere,
      MvPolynomial.eval (fun i => (x : Ambient) i) H *
        (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ ℓ ∂sigma) =
      ((2 : ℝ) ^ ℓ * (ℓ.factorial : ℝ) /
        (((2 * ℓ + 1 : ℕ) : ℝ) *
          ((2 * ℓ).descFactorial ℓ : ℝ))) *
        MvPolynomial.eval (fun i => (u : Ambient) i) H := by
  have hhom := (mem_harmonicPolynomialSubmodule.mp hH).1
  have hbridge := polynomialDifferentialOperator_radial_moment
    hhom ℓ ℓ (by omega : ℓ + ℓ = 2 * ℓ) (u : Ambient)
  rw [harmonic_radial_differentiation ℓ ℓ H hH] at hbridge
  simp only [map_mul, MvPolynomial.eval_C, map_pow,
    radialSquare_eval_sphere, one_pow, one_mul, mul_one,
    Nat.sub_self, pow_zero] at hbridge
  have hden : (((2 * ℓ).descFactorial ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show (2 * ℓ).descFactorial ℓ ≠ 0 by
      simp only [ne_eq, Nat.descFactorial_eq_zero_iff_lt]
      omega)
  have hbase : (((2 * ℓ + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [Nat.descFactorial_self] at hbridge
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero hbase hden)).2
  push_cast at hbridge ⊢
  let I : ℝ := ∫ x : Sphere,
    MvPolynomial.eval (fun i => (x : Ambient) i) H *
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ ℓ ∂sigma
  change 1 / (2 * (ℓ : ℝ) + 1) *
      (2 ^ ℓ * (ℓ.factorial : ℝ) *
        MvPolynomial.eval (fun i => (u : Ambient) i) H) =
      ((2 * ℓ).descFactorial ℓ : ℝ) * I at hbridge
  change I * ((2 * (ℓ : ℝ) + 1) *
      ((2 * ℓ).descFactorial ℓ : ℝ)) = _
  have hbase' : (2 * (ℓ : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hbase'] at hbridge
  nlinarith [hbridge]

/-- A harmonic of degree `ℓ` is orthogonal to every lower-degree
homogeneous polynomial on the sphere. -/
theorem harmonic_orthogonal_lower_homogeneous
    {H p : MvPolynomial (Fin 3) ℝ} {ℓ q : ℕ}
    (hH : H ∈ harmonicPolynomialSubmodule ℓ)
    (hp : p.IsHomogeneous q) (hq : q < ℓ) :
    (∫ x : Sphere, restrictPolynomial H x * restrictPolynomial p x ∂sigma) = 0 := by
  let zeroSet : Submodule ℝ C(Sphere, ℝ) := {
    carrier := {f | (∫ x : Sphere, restrictPolynomial H x * f x ∂sigma) = 0}
    zero_mem' := by simp
    add_mem' := by
      intro f g hf hg
      change (∫ x : Sphere, restrictPolynomial H x * (f + g) x ∂sigma) = 0
      simp only [ContinuousMap.add_apply, mul_add]
      change (∫ x : Sphere, (restrictPolynomial H * f) x +
        (restrictPolynomial H * g) x ∂sigma) = 0
      rw [integral_add
        (continuous_integrable_sigma (restrictPolynomial H * f))
        (continuous_integrable_sigma (restrictPolynomial H * g))]
      simp only [Set.mem_setOf_eq] at hf hg
      rw [show (∫ x : Sphere, (restrictPolynomial H * f) x ∂sigma) = 0 from hf,
        show (∫ x : Sphere, (restrictPolynomial H * g) x ∂sigma) = 0 from hg]
      simp
    smul_mem' := by
      intro c f hf
      change (∫ x : Sphere, restrictPolynomial H x * (c • f) x ∂sigma) = 0
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      have hfun : (fun x : Sphere => restrictPolynomial H x * (c * f x)) =
          fun x : Sphere => c * (restrictPolynomial H * f) x := by
        funext x
        simp only [ContinuousMap.mul_apply]
        ring
      rw [hfun]
      rw [integral_const_mul]
      exact mul_eq_zero_of_right c hf }
  have hs : harmonicRestrictionSpanUpTo q ≤ zeroSet := by
    apply Submodule.span_le.mpr
    intro f hf
    obtain ⟨n, hn, ⟨h, hh, hlap, hpoint⟩⟩ := hf
    have hfeq : f = restrictPolynomial h := by
      ext x
      exact hpoint x
    rw [hfeq]
    change (∫ x : Sphere, restrictPolynomial H x * restrictPolynomial h x ∂sigma) = 0
    exact crossDegreeHarmonicOrthogonality (by omega : ℓ ≠ n) hH ⟨hh, hlap⟩
  exact hs (homogeneous_restriction_mem_spanUpTo hp le_rfl)

theorem lower_projection_harmonic_zero
    {H : MvPolynomial (Fin 3) ℝ} {ℓ q : ℕ}
    (hH : H ∈ harmonicPolynomialSubmodule ℓ) (u : Sphere)
    (hq : q < ℓ) :
    (∫ x : Sphere,
      restrictPolynomial H x *
        (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ q ∂sigma) = 0 := by
  have h := harmonic_orthogonal_lower_homogeneous hH
    ((zonalLinear_isHomogeneous u).pow q) (by simpa using hq)
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [restrictPolynomial_apply, map_pow, zonalLinear_eval_sphere,
    sphereInnerKernel_eq_inner]

/-- Rodrigues orthogonality leaves only its leading monomial. Its coefficient
exactly cancels the scalar in the top monomial projection formula. -/
theorem legendre_projection_harmonic_action
    {H : MvPolynomial (Fin 3) ℝ} {ℓ : ℕ}
    (hH : H ∈ harmonicPolynomialSubmodule ℓ) (u : Sphere) :
    (∫ x : Sphere, restrictPolynomial H x *
      (legendrePolynomial ℓ).eval (sphereInnerKernel u x) ∂sigma) =
      (1 / (2 * (ℓ : ℝ) + 1)) * restrictPolynomial H u := by
  classical
  let t (x : Sphere) : ℝ := sphereInnerKernel u x
  have hterm (j : ℕ) (hj : j ≤ ℓ) :
      (∫ x : Sphere, restrictPolynomial H x *
        (zonalRodriguesCoefficient ℓ j * t x ^ (2 * j - ℓ)) ∂sigma) =
        if j = ℓ then
          (1 / (2 * (ℓ : ℝ) + 1)) * restrictPolynomial H u else 0 := by
    by_cases hlast : j = ℓ
    · subst j
      simp only [if_pos rfl, t, show 2 * ℓ - ℓ = ℓ by omega]
      rw [show (∫ x : Sphere,
          restrictPolynomial H x *
            (zonalRodriguesCoefficient ℓ ℓ *
              sphereInnerKernel u x ^ ℓ) ∂sigma) =
          zonalRodriguesCoefficient ℓ ℓ *
            (∫ x : Sphere, restrictPolynomial H x *
              sphereInnerKernel u x ^ ℓ ∂sigma) by
            simp_rw [mul_left_comm (restrictPolynomial H _) _]
            rw [integral_const_mul]]
      rw [show (∫ x : Sphere, restrictPolynomial H x *
          sphereInnerKernel u x ^ ℓ ∂sigma) =
            ((2 : ℝ) ^ ℓ * (ℓ.factorial : ℝ) /
              (((2 * ℓ + 1 : ℕ) : ℝ) *
                ((2 * ℓ).descFactorial ℓ : ℝ))) *
              restrictPolynomial H u by
            simpa only [sphereInnerKernel_eq_inner, restrictPolynomial_apply]
              using top_projection_harmonic_action hH u]
      unfold zonalRodriguesCoefficient
      simp only [Nat.sub_self, pow_zero, one_mul, Nat.choose_self]
      have hfact : ((ℓ.factorial : ℕ) : ℝ) ≠ 0 := by positivity
      have hdesc : (((2 * ℓ).descFactorial ℓ : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show (2 * ℓ).descFactorial ℓ ≠ 0 by
          simp only [ne_eq, Nat.descFactorial_eq_zero_iff_lt]
          omega)
      push_cast
      field_simp [hfact, hdesc]
      ring
    · simp only [if_neg hlast]
      by_cases hsmall : 2 * j < ℓ
      · rw [zonalRodriguesCoefficient_eq_zero_of_lt hsmall]
        simp
      · have hq : 2 * j - ℓ < ℓ := by omega
        have hzero := lower_projection_harmonic_zero hH u hq
        simp only [← sphereInnerKernel_eq_inner] at hzero
        convert congrArg (fun z : ℝ => zonalRodriguesCoefficient ℓ j * z) hzero using 1
        · rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with x
          ring
        · simp
  rw [legendrePolynomial_eq_zonalRodrigues_sum]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  simp_rw [Finset.mul_sum]
  change (∫ x : Sphere, ∑ j ∈ Finset.range (ℓ + 1),
      restrictPolynomial H x *
        (zonalRodriguesCoefficient ℓ j * t x ^ (2 * j - ℓ)) ∂sigma) = _
  rw [integral_finset_sum]
  · rw [Finset.sum_congr rfl (fun j hj => hterm j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))]
    simp
  · intro j hj
    have ht : t = restrictPolynomial (zonalLinear u) := by
      funext x
      exact (zonalLinear_eval_sphere u x).symm
    rw [ht]
    simpa only [ContinuousMap.mul_apply, ContinuousMap.pow_apply,
      ContinuousMap.coe_const, Pi.mul_apply] using
      continuous_integrable_sigma
        (restrictPolynomial H *
          (ContinuousMap.const Sphere (zonalRodriguesCoefficient ℓ j) *
            (restrictPolynomial (zonalLinear u)) ^ (2 * j - ℓ)))

/-- The addition formula in every degree, with the exact Rodrigues
normalization and the same basis used by the energy expansion. -/
theorem harmonic_addition_legendre (Y : HarmonicBasis) :
    HarmonicAdditionLegendre Y := by
  intro ℓ u y
  let b := harmonicBasisDegree Y ℓ
  let p := zonalHarmonic ℓ u
  have hcoef (k : Fin (2 * ℓ + 1)) :
      ⟪b k, p⟫_ℝ =
        (1 / (2 * (ℓ : ℝ) + 1)) * Y.function ℓ k u := by
    change harmonicL2Inner ℓ (b k) p = _
    rw [harmonicBasisDegree_apply]
    unfold harmonicL2Inner
    rw [harmonicBasisPolynomial_restrict]
    simp_rw [show restrictPolynomial p.val =
        fun x : Sphere => (legendrePolynomial ℓ).eval (sphereInnerKernel u x) from
      by ext x; exact restrict_zonalHarmonic ℓ u x]
    have h := legendre_projection_harmonic_action
      (harmonicBasisPolynomial Y ℓ k).property u
    rw [harmonicBasisPolynomial_restrict] at h
    exact h
  have hexp := b.sum_repr' p
  have heval := congrArg (fun q : harmonicPolynomialSubmodule ℓ =>
      restrictPolynomial q.val y) hexp
  change (restrictHarmonicLinearMap ℓ
      (∑ k, ⟪b k, p⟫_ℝ • b k)) y =
    (restrictHarmonicLinearMap ℓ p) y at heval
  simp only [map_sum, map_smul, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul] at heval
  change (∑ k, ⟪b k, p⟫_ℝ * restrictPolynomial (b k).val y) =
    restrictPolynomial p.val y at heval
  rw [show restrictPolynomial p.val y =
      (legendrePolynomial ℓ).eval (sphereInnerKernel u y) from
    restrict_zonalHarmonic ℓ u y] at heval
  have hbase (k : Fin (2 * ℓ + 1)) :
      restrictPolynomial (b k).val y = Y.function ℓ k y := by
    rw [harmonicBasisDegree_apply, harmonicBasisPolynomial_restrict]
  simp_rw [hcoef, hbase] at heval
  unfold harmonicAdditionKernel
  -- Multiply the basis expansion by the nonzero dimension.
  have hdim : (2 * (ℓ : ℝ) + 1) ≠ 0 := by positivity
  have hterm (k : Fin (2 * ℓ + 1)) :
      (1 / (2 * (ℓ : ℝ) + 1) * Y.function ℓ k u) * Y.function ℓ k y =
        (Y.function ℓ k u * Y.function ℓ k y) /
          (2 * (ℓ : ℝ) + 1) := by ring
  simp_rw [hterm] at heval
  rw [← Finset.sum_div] at heval
  have hresult := (div_eq_iff hdim).mp (show
    (∑ k : Fin (2 * ℓ + 1), Y.function ℓ k u * Y.function ℓ k y) /
      (2 * (ℓ : ℝ) + 1) =
      (legendrePolynomial ℓ).eval (sphereInnerKernel u y) by
    simpa only [div_eq_mul_inv] using heval)
  simpa only [mul_comm] using hresult

end BEMOC.Definitive
```
