import BEMOCFormalization.HarmonicBasis

/-! Orthogonal pullback of homogeneous harmonic polynomials. -/

open scoped BigOperators
namespace BEMOC.Definitive

private noncomputable def orthogonalCoordinate (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    (j : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, MvPolynomial.C ((T (EuclideanSpace.single i 1)) j) * MvPolynomial.X i

/-- Polynomial substitution by an ambient orthogonal transformation. -/
noncomputable def orthogonalPolynomialPullback (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval (orthogonalCoordinate T) p

private theorem orthogonalCoordinate_eval (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    (x : Ambient) (j : Fin 3) :
    MvPolynomial.eval (fun i => x i) (orthogonalCoordinate T j) = (T x) j := by
  simp only [orthogonalCoordinate, map_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  have hx : x = ∑ i : Fin 3, x i • EuclideanSpace.single i 1 := by
    ext k
    change x k = ∑ i : Fin 3, x i * (EuclideanSpace.single i (1 : ℝ)) k
    simp [EuclideanSpace.single_apply, mul_ite, Finset.sum_ite_eq']
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, Finset.sum_apply, smul_eq_mul]
  change (∑ i : Fin 3, (T (EuclideanSpace.single i 1)) j * x i) =
    ∑ i : Fin 3, x i * (T (EuclideanSpace.single i 1)) j
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Evaluating a pullback is evaluating the original polynomial at the transformed point. -/
theorem orthogonalPolynomialPullback_eval (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    (p : MvPolynomial (Fin 3) ℝ) (x : Ambient) :
    MvPolynomial.eval (fun i => x i) (orthogonalPolynomialPullback T p) =
      MvPolynomial.eval (fun i => (T x) i) p := by
  unfold orthogonalPolynomialPullback
  rw [MvPolynomial.aeval_def, MvPolynomial.eval_eval₂]
  have hring : (MvPolynomial.eval (fun i => x i)).comp
      (algebraMap ℝ (MvPolynomial (Fin 3) ℝ)) = RingHom.id ℝ := by
    ext c
    simp
  rw [hring]
  simp only [orthogonalCoordinate_eval, MvPolynomial.eval₂_id]

private theorem orthogonalCoordinate_isHomogeneous (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    (j : Fin 3) : (orthogonalCoordinate T j).IsHomogeneous 1 := by
  unfold orthogonalCoordinate
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- Orthogonal substitution preserves homogeneous degree. -/
theorem orthogonalPolynomialPullback_isHomogeneous (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    {ℓ : ℕ} {p : MvPolynomial (Fin 3) ℝ} (hp : p.IsHomogeneous ℓ) :
    (orthogonalPolynomialPullback T p).IsHomogeneous ℓ := by
  simpa [orthogonalPolynomialPullback] using
    hp.aeval (orthogonalCoordinate T) (orthogonalCoordinate_isHomogeneous T)

private theorem pderiv_orthogonalCoordinate (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    (i j : Fin 3) :
    MvPolynomial.pderiv i (orthogonalCoordinate T j) =
      MvPolynomial.C ((T (EuclideanSpace.single i 1)) j) := by
  classical
  simp only [orthogonalCoordinate, map_sum, MvPolynomial.pderiv_C_mul,
    MvPolynomial.pderiv_X]
  simp [Pi.single_apply, Finset.sum_ite_eq', eq_comm]

private theorem fin3_sum_ite_add (A B : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (j : Fin 3) :
    (∑ x : Fin 3, if j = x then A x + B x else A x) =
      (∑ x : Fin 3, A x) + B j := by
  calc
    (∑ x : Fin 3, if j = x then A x + B x else A x) =
        (∑ x : Fin 3, (A x + (if j = x then B x else 0))) := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = (∑ x : Fin 3, A x) + B j := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_ite_eq', eq_comm]

private theorem pderiv_orthogonalPolynomialPullback
    (T : Ambient ≃ₗᵢ[ℝ] Ambient) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv i (orthogonalPolynomialPullback T p) =
      ∑ j : Fin 3, MvPolynomial.C ((T (EuclideanSpace.single i 1)) j) *
        orthogonalPolynomialPullback T (MvPolynomial.pderiv j p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [orthogonalPolynomialPullback, MvPolynomial.pderiv_C]
  | add p q hp hq =>
      simp only [orthogonalPolynomialPullback, map_add, map_add, mul_add,
        Finset.sum_add_distrib] at hp hq ⊢
      rw [hp, hq]
  | mul_X p j hp =>
      simp only [orthogonalPolynomialPullback, map_mul, MvPolynomial.aeval_X,
        MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        map_add, map_mul, mul_add] at hp ⊢
      rw [hp, pderiv_orthogonalCoordinate]
      simp_rw [Pi.single_apply]
      simp only [apply_ite, map_one, map_zero]
      simp only [mul_one, mul_zero, add_zero]
      rw [fin3_sum_ite_add]
      simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

private theorem orthogonal_matrix_coeff_transpose
    (T : Ambient ≃ₗᵢ[ℝ] Ambient) (i j : Fin 3) :
    (T (EuclideanSpace.single i 1)) j =
      (T.symm (EuclideanSpace.single j 1)) i := by
  have h := T.inner_map_map
    (T.symm (EuclideanSpace.single j 1)) (EuclideanSpace.single i 1)
  simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    real_inner_comm] using h

private theorem orthogonal_matrix_coeff_sum
    (T : Ambient ≃ₗᵢ[ℝ] Ambient) (j k : Fin 3) :
    (∑ i : Fin 3, (T (EuclideanSpace.single i 1)) j *
      (T (EuclideanSpace.single i 1)) k) = if j = k then 1 else 0 := by
  simp_rw [orthogonal_matrix_coeff_transpose T]
  have h := T.symm.inner_map_map
    (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [dotProduct, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply, Pi.single_apply, mul_comm, eq_comm] using h

/-- The Euclidean polynomial Laplacian commutes with orthogonal substitution. -/
theorem polynomialLaplacian_orthogonalPolynomialPullback
    (T : Ambient ≃ₗᵢ[ℝ] Ambient) (p : MvPolynomial (Fin 3) ℝ) :
    polynomialLaplacian (orthogonalPolynomialPullback T p) =
      orthogonalPolynomialPullback T (polynomialLaplacian p) := by
  classical
  let e : Fin 3 → Fin 3 → ℝ :=
    fun i j => (T (EuclideanSpace.single i 1)) j
  have hderiv (i j : Fin 3) :
      MvPolynomial.pderiv i
        (MvPolynomial.C (e i j) * orthogonalPolynomialPullback T
          (MvPolynomial.pderiv j p)) =
      ∑ k : Fin 3, MvPolynomial.C (e i j * e i k) *
        orthogonalPolynomialPullback T
          (MvPolynomial.pderiv k (MvPolynomial.pderiv j p)) := by
    rw [MvPolynomial.pderiv_C_mul, pderiv_orthogonalPolynomialPullback]
    simp only [e, Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  calc
    polynomialLaplacian (orthogonalPolynomialPullback T p) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          MvPolynomial.C (e i j * e i k) *
            orthogonalPolynomialPullback T
              (MvPolynomial.pderiv k (MvPolynomial.pderiv j p)) := by
      simp only [polynomialLaplacian, pderiv_orthogonalPolynomialPullback,
        map_sum, hderiv, e]
    _ = ∑ j : Fin 3, ∑ k : Fin 3,
          MvPolynomial.C (∑ i : Fin 3, e i j * e i k) *
            orthogonalPolynomialPullback T
              (MvPolynomial.pderiv k (MvPolynomial.pderiv j p)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      simp only [← Finset.sum_mul, ← map_sum]
    _ = orthogonalPolynomialPullback T (polynomialLaplacian p) := by
      simp only [e, orthogonal_matrix_coeff_sum, polynomialLaplacian]
      simp only [map_sum, orthogonalPolynomialPullback]
      apply Finset.sum_congr rfl
      intro j _
      simp [Finset.sum_ite_eq', eq_comm]

/-- Orthogonal substitution preserves the degree-`ℓ` harmonic subspace. -/
theorem orthogonalPolynomialPullback_mem_harmonicPolynomialSubmodule
    (T : Ambient ≃ₗᵢ[ℝ] Ambient) {ℓ : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p ∈ harmonicPolynomialSubmodule ℓ) :
    orthogonalPolynomialPullback T p ∈ harmonicPolynomialSubmodule ℓ := by
  obtain ⟨hhom, hlap⟩ := mem_harmonicPolynomialSubmodule.mp hp
  apply mem_harmonicPolynomialSubmodule.mpr
  constructor
  · exact orthogonalPolynomialPullback_isHomogeneous T hhom
  · rw [polynomialLaplacian_orthogonalPolynomialPullback, hlap]
    simp [orthogonalPolynomialPullback]

/-- Linear orthogonal action on genuine algebraic degree-`ℓ` harmonics. -/
noncomputable def orthogonalHarmonicPullback (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    (ℓ : ℕ) :
    harmonicPolynomialSubmodule ℓ →ₗ[ℝ] harmonicPolynomialSubmodule ℓ where
  toFun p := ⟨orthogonalPolynomialPullback T p,
    orthogonalPolynomialPullback_mem_harmonicPolynomialSubmodule T p.property⟩
  map_add' := by
    intro p q
    apply Subtype.ext
    simp [orthogonalPolynomialPullback]
  map_smul' := by
    intro c p
    apply Subtype.ext
    simp [orthogonalPolynomialPullback, smul_eq_mul]

/-- Polynomial restriction after pullback is spherical composition by `T`. -/
theorem restrictPolynomial_orthogonalPolynomialPullback
    (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    (p : MvPolynomial (Fin 3) ℝ) (x : Sphere) :
    restrictPolynomial (orthogonalPolynomialPullback T p) x =
      restrictPolynomial p (sphereLinearIsometryEquiv T x) := by
  rw [restrictPolynomial_apply, restrictPolynomial_apply,
    orthogonalPolynomialPullback_eval]
  rfl

/-- The restricted image of a harmonic is the original harmonic composed with `T`. -/
theorem restrictPolynomial_orthogonalHarmonicPullback
    (T : Ambient ≃ₗᵢ[ℝ] Ambient) (ℓ : ℕ)
    (p : harmonicPolynomialSubmodule ℓ) (x : Sphere) :
    restrictPolynomial (orthogonalHarmonicPullback T ℓ p).val x =
      restrictPolynomial p.val (sphereLinearIsometryEquiv T x) :=
  restrictPolynomial_orthogonalPolynomialPullback T p.val x

end BEMOC.Definitive
