# Harmonic Casimir algebra

`BEMOCFormalization/HarmonicCasimir.lean` imports `HarmonicBasis.lean` and contains the polynomial identity needed for orthogonality of spherical harmonics of different degrees. It has no integration or geometric invariance assumptions.

For `p : Poly3 := MvPolynomial (Fin 3) ℝ`, `angularDerivation i j p` is exactly `X i * pderiv j p - X j * pderiv i p`. The definition is an `ℝ`-linear map. `angularDerivation_mul` proves Leibniz's rule, which allows integration by parts after restricting to the sphere. `polynomialEuler p` is `∑ i, X i * pderiv i p`. `angularCasimir p` is the sum of the squares of the three plane derivations `(0,1)`, `(0,2)`, and `(1,2)`. `angularCasimir_eq_pair_sum` identifies it with the finite `i<j` sum.

`angularCasimir_eq` proves the exact algebraic identity

```text
angularCasimir p = radialSquare * polynomialLaplacian p
                    - polynomialEuler (polynomialEuler p) - polynomialEuler p.
```

The calculation expands each polynomial derivative using Leibniz's rule and uses `Fin.sum_univ_three`; no commutation of mixed partial derivatives is needed because both orders occur in the identity. At `p.IsHomogeneous ℓ` and `polynomialLaplacian p = 0`, Euler's identity gives `angularCasimir_harmonic`:

```text
angularCasimir p = -((ℓ : ℝ) * (ℓ + 1)) • p.
```

`angularCasimir_pair_sum_harmonic` gives the same result directly in the `i<j` notation. On the unit sphere `radialSquare` restricts to one, but the harmonic specialization already eliminates the radial term. The orthogonality proof can combine this eigenvalue with skew-adjointness of each restricted `angularDerivation i j` under `sigma`; that analytic step belongs in `HarmonicOrthogonality.lean`.

Checked with `lake env lean BEMOCFormalization/HarmonicCasimir.lean` on Lean 4.19.0. No axioms, `sorry`, `admit`, or `opaque` declarations were introduced.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.HarmonicBasis

open scoped BigOperators
namespace BEMOC.Definitive

/-- Real polynomials in three Cartesian coordinates. -/
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- Infinitesimal rotation in the coordinate plane spanned by `i,j`. -/
noncomputable def angularDerivation (i j : Fin 3) : Poly3 →ₗ[ℝ] Poly3 where
  toFun p := MvPolynomial.X i * MvPolynomial.pderiv j p -
    MvPolynomial.X j * MvPolynomial.pderiv i p
  map_add' p q := by simp only [map_add]; ring
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul, RingHom.id_apply]
    ring

@[simp] theorem angularDerivation_apply (i j : Fin 3) (p : Poly3) :
    angularDerivation i j p = MvPolynomial.X i * MvPolynomial.pderiv j p -
      MvPolynomial.X j * MvPolynomial.pderiv i p := rfl

/-- The rotation operator satisfies the polynomial Leibniz rule. -/
theorem angularDerivation_mul (i j : Fin 3) (p q : Poly3) :
    angularDerivation i j (p * q) =
      angularDerivation i j p * q + p * angularDerivation i j q := by
  simp only [angularDerivation_apply, MvPolynomial.pderiv_mul]
  ring

/-- Polynomial Euler operator. -/
noncomputable def polynomialEuler (p : Poly3) : Poly3 :=
  ∑ i : Fin 3, MvPolynomial.X i * MvPolynomial.pderiv i p

/-- Sum of the three squared infinitesimal rotations. -/
noncomputable def angularCasimir (p : Poly3) : Poly3 :=
  angularDerivation 0 1 (angularDerivation 0 1 p) +
  angularDerivation 0 2 (angularDerivation 0 2 p) +
  angularDerivation 1 2 (angularDerivation 1 2 p)

/-- The explicit three-term Casimir is the sum over coordinate planes `i < j`. -/
theorem angularCasimir_eq_pair_sum (p : Poly3) :
    angularCasimir p =
      ∑ i : Fin 3, ∑ j : Fin 3,
        if i < j then angularDerivation i j (angularDerivation i j p) else 0 := by
  simp [angularCasimir, Fin.sum_univ_three]

/-- The algebraic rotation-Casimir identity in three dimensions. -/
theorem angularCasimir_eq (p : Poly3) :
    angularCasimir p = radialSquare * polynomialLaplacian p -
      polynomialEuler (polynomialEuler p) - polynomialEuler p := by
  classical
  simp only [angularCasimir, angularDerivation_apply, polynomialEuler,
    radialSquare, polynomialLaplacian, Fin.sum_univ_three,
    map_add, map_sub, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X, Pi.single_apply]
  simp only [Fin.reduceEq, ↓reduceIte, mul_zero, add_zero, sub_zero]
  ring

/-- On degree-`ℓ` harmonic polynomials, the Casimir is the usual spherical eigenvalue. -/
theorem angularCasimir_harmonic {ℓ : ℕ} {p : Poly3}
    (hp : p.IsHomogeneous ℓ) (hlap : polynomialLaplacian p = 0) :
    angularCasimir p = -((ℓ : ℝ) * (ℓ + 1)) • p := by
  have hEuler : polynomialEuler p = (ℓ : ℝ) • p := by
    unfold polynomialEuler
    rw [hp.sum_X_mul_pderiv]
    simp [nsmul_eq_mul, MvPolynomial.smul_eq_C_mul]
  have hEuler_smul (c : ℝ) (q : Poly3) :
      polynomialEuler (c • q) = c • polynomialEuler q := by
    unfold polynomialEuler
    simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hEuler2 : polynomialEuler (polynomialEuler p) =
      ((ℓ : ℝ) ^ 2) • p := by
    rw [hEuler, hEuler_smul, hEuler, smul_smul]
    ring
  rw [angularCasimir_eq, hlap, hEuler2, hEuler]
  simp only [mul_zero, zero_sub, MvPolynomial.smul_eq_C_mul]
  simp only [map_pow, map_add, map_neg, map_mul, map_one]
  ring

/-- Casimir eigenvalue in the coordinate-plane sum notation. -/
theorem angularCasimir_pair_sum_harmonic {ℓ : ℕ} {p : Poly3}
    (hp : p.IsHomogeneous ℓ) (hlap : polynomialLaplacian p = 0) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      if i < j then angularDerivation i j (angularDerivation i j p) else 0) =
      -((ℓ : ℝ) * (ℓ + 1)) • p := by
  rw [← angularCasimir_eq_pair_sum]
  exact angularCasimir_harmonic hp hlap

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
