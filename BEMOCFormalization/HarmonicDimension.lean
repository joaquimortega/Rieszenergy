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
