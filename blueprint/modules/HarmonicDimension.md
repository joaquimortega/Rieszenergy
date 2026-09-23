# HarmonicDimension proof guide

This module establishes the exact dimension required by `HarmonicBasis.function`: in degree `ℓ`, the space of restrictions of genuine harmonic polynomials has `2ℓ+1` coordinates. The algebraic part concerns the real vector space `harmonicPolynomialSubmodule ℓ`; `homogeneous_restrict_injective` from `HarmonicBasis` ensures the same count applies to the restricted functions. The proof is based on rank-nullity for the *actual* Euclidean polynomial Laplacian, with no harmonic basis assumed.

The dependency chain is deliberate. `HarmonicMonomialCount` identifies degree-`m` exponent vectors in three variables with `Sym (Fin 3) m` and proves that their number is `Nat.choose (m+2) 2`. `HarmonicBasis.finrank_homogeneous_eq_degreeMonomials_card` turns this combinatorial result into the dimension of homogeneous polynomials. `FischerDecomposition.homogeneous_mem_radialHarmonicSpan` supplies a constructive Laplacian preimage for every homogeneous polynomial. Together, these are exactly the hypotheses of the finite-dimensional rank-nullity theorem.

`homogeneousLaplacian m` is a linear map from the degree-`m+2` homogeneous submodule to the degree-`m` submodule. The target degree is justified by two applications of homogeneous differentiation; the map is additive and scalar-linear because the polynomial Laplacian is a real linear map. `homogeneousLaplacian_surjective` first uses Fischer spanning for a target polynomial, obtains a preimage inside `radialHarmonicSpan (m+2)`, and then uses the span's homogeneity inclusion to put that preimage in the map's domain. This is genuine surjectivity for every `m≥0`, including the low-degree endpoints.

The kernel of this homogeneous Laplacian is definitionally the degree-`m+2` harmonic polynomial space, but the types are nested subtypes. `homogeneousLaplacianKerEquiv` packages the exact linear equivalence between them; its forward and inverse maps retain both the degree and Laplacian-zero proofs. Rank-nullity now states `dim P_m + dim H_(m+2) = dim P_(m+2)`. The proof rewrites both polynomial dimensions as binomial coefficients. Two applications of Pascal's identity show that the difference is `(m+3)+(m+2)=2(m+2)+1`; this avoids fragile manipulations of natural-number division by two.

The theorem `finrank_harmonicPolynomialSubmodule_succ_succ` covers degree at least two. Degree zero and one are already explicit equivalences in `HarmonicBasis` with dimensions one and three, so a three-case split gives the public `finrank_harmonicPolynomialSubmodule (ℓ) = 2*ℓ+1` for every natural `ℓ`. The dimension of the continuous harmonic subspace follows from the injective restriction map and its exact range characterisation. This theorem is consumed by `HarmonicOrthonormal` to reindex mathlib's finite orthonormal basis with `Fin (2*ℓ+1)`. It proves cardinality only; it does not assert cross-degree L² orthogonality, which remains a separate geometric integral theorem.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.FischerDecomposition
import BEMOCFormalization.HarmonicMonomialCount

namespace BEMOC.Definitive

noncomputable def homogeneousLaplacian (m : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (m + 2) →ₗ[ℝ]
      MvPolynomial.homogeneousSubmodule (Fin 3) ℝ m where
  toFun p := ⟨polynomialLaplacian p.val, by
    simpa only [Nat.add_sub_cancel_right] using
      polynomialLaplacian_isHomogeneous p.property⟩
  map_add' p q := by
    apply Subtype.ext
    simp [← polynomialLaplacianLinearMap_apply]
  map_smul' c p := by
    apply Subtype.ext
    simp [polynomialLaplacian_smul]

theorem homogeneousLaplacian_surjective (m : ℕ) :
    Function.Surjective (homogeneousLaplacian m) := by
  intro p
  have hspan := homogeneous_mem_radialHarmonicSpan m p.val p.property
  obtain ⟨q, hq, hΔq⟩ := radialHarmonicSpan_laplacian_preimage hspan
  refine ⟨⟨q, radialHarmonicSpan_le_homogeneous (m + 2) hq⟩, ?_⟩
  exact Subtype.ext hΔq

noncomputable def homogeneousLaplacianKerEquiv (m : ℕ) :
    LinearMap.ker (homogeneousLaplacian m) ≃ₗ[ℝ]
      harmonicPolynomialSubmodule (m + 2) where
  toFun p := ⟨p.val.val, by
    apply mem_harmonicPolynomialSubmodule.mpr
    have hzero : polynomialLaplacian p.val.val = 0 :=
      congrArg Subtype.val p.property
    exact ⟨p.val.property, hzero⟩⟩
  invFun p := ⟨⟨p.val, (mem_harmonicPolynomialSubmodule.mp p.property).1⟩, by
    apply Subtype.ext
    exact (mem_harmonicPolynomialSubmodule.mp p.property).2⟩
  left_inv p := by ext; rfl
  right_inv p := by ext; rfl
  map_add' p q := by ext; rfl
  map_smul' c p := by ext; rfl

theorem finrank_homogeneous_eq_choose (m : ℕ) :
    Module.finrank ℝ (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ m) =
      Nat.choose (m + 2) 2 := by
  rw [finrank_homogeneous_eq_degreeMonomials_card,
    degreeMonomials_card_choose]

theorem finrank_harmonicPolynomialSubmodule_succ_succ (m : ℕ) :
    Module.finrank ℝ (harmonicPolynomialSubmodule (m + 2)) =
      2 * (m + 2) + 1 := by
  letI := finiteDimensional_homogeneousPolynomial (m + 2)
  have hrank := (homogeneousLaplacian m).finrank_range_add_finrank_ker
  have htop : LinearMap.range (homogeneousLaplacian m) = ⊤ :=
    LinearMap.range_eq_top.mpr (homogeneousLaplacian_surjective m)
  rw [htop, finrank_top,
    (homogeneousLaplacianKerEquiv m).finrank_eq,
    finrank_homogeneous_eq_choose,
    finrank_homogeneous_eq_choose] at hrank
  have h1 : Nat.choose (m + 4) 2 = (m + 3) + Nat.choose (m + 3) 2 := by
    simpa [Nat.choose_one_right, Nat.add_assoc] using
      Nat.choose_succ_succ' (m + 3) 1
  have h2 : Nat.choose (m + 3) 2 = (m + 2) + Nat.choose (m + 2) 2 := by
    simpa [Nat.choose_one_right, Nat.add_assoc] using
      Nat.choose_succ_succ' (m + 2) 1
  rw [show m + 2 + 2 = m + 4 by omega] at hrank
  omega

theorem finrank_harmonicPolynomialSubmodule (ℓ : ℕ) :
    Module.finrank ℝ (harmonicPolynomialSubmodule ℓ) = 2 * ℓ + 1 := by
  rcases ℓ with _ | _ | m
  · simpa using finrank_harmonicPolynomialSubmodule_zero
  · simpa using finrank_harmonicPolynomialSubmodule_one
  · simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      finrank_harmonicPolynomialSubmodule_succ_succ m

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
