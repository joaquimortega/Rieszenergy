import BEMOCFormalization.HarmonicOrthonormal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.Dual
import BEMOCFormalization.HarmonicOrthogonality
import BEMOCFormalization.HarmonicPullback

open scoped BigOperators
open scoped InnerProductSpace
open MeasureTheory
namespace BEMOC.Definitive

/-- The unique homogeneous harmonic polynomial underlying a basis function. -/
noncomputable def harmonicBasisPolynomial (Y : HarmonicBasis) (ℓ : ℕ)
    (k : Fin (2 * ℓ + 1)) : harmonicPolynomialSubmodule ℓ :=
  Classical.choose ((isSphericalHarmonic_iff_range ℓ (Y.function ℓ k)).mp
    (Y.harmonic ℓ k))

@[simp] theorem harmonicBasisPolynomial_restrict (Y : HarmonicBasis) (ℓ : ℕ)
    (k : Fin (2 * ℓ + 1)) :
    restrictPolynomial (harmonicBasisPolynomial Y ℓ k).val = Y.function ℓ k :=
  (Classical.choose_spec ((isSphericalHarmonic_iff_range ℓ (Y.function ℓ k)).mp
    (Y.harmonic ℓ k))).symm

/-- An arbitrary system's degree-`ℓ` members form an orthonormal basis of the
full degree-`ℓ` polynomial harmonic space. -/
noncomputable def harmonicBasisDegree (Y : HarmonicBasis) (ℓ : ℕ) :
    OrthonormalBasis (Fin (2 * ℓ + 1)) ℝ (harmonicPolynomialSubmodule ℓ) := by
  letI := finiteDimensional_harmonicPolynomial ℓ
  have hon : Orthonormal ℝ (harmonicBasisPolynomial Y ℓ) := by
    rw [orthonormal_iff_ite]
    intro k j
    change harmonicL2Inner ℓ (harmonicBasisPolynomial Y ℓ k)
      (harmonicBasisPolynomial Y ℓ j) = _
    simp only [harmonicL2Inner, harmonicBasisPolynomial_restrict]
    simpa only [eq_self_iff_true, true_and, Fin.val_inj] using
      Y.orthonormal ℓ ℓ k j
  have hcard : Fintype.card (Fin (2 * ℓ + 1)) =
      Module.finrank ℝ (harmonicPolynomialSubmodule ℓ) := by
    simpa using (finrank_harmonicPolynomialSubmodule ℓ).symm
  exact OrthonormalBasis.mk hon
    ((Orthonormal.linearIndependent hon).span_eq_top_of_card_eq_finrank hcard).ge

@[simp] theorem harmonicBasisDegree_apply (Y : HarmonicBasis) (ℓ : ℕ)
    (k : Fin (2 * ℓ + 1)) :
    harmonicBasisDegree Y ℓ k = harmonicBasisPolynomial Y ℓ k := by
  simp [harmonicBasisDegree]

/-- The sum of squared evaluations depends only on the finite-dimensional
inner-product space, not on its chosen orthonormal basis. -/
theorem orthonormalBasis_sum_sq_linearMap {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E)
    (f : E →ₗ[ℝ] ℝ) :
    (∑ i, f (b i) ^ 2) = ∑ j, f (c j) ^ 2 := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let v : E := (InnerProductSpace.toDual ℝ E).symm f.toContinuousLinearMap
  have hf (q : E) : f q = ⟪v, q⟫_ℝ := by
    exact (InnerProductSpace.toDual_symm_apply
      (x := q) (y := f.toContinuousLinearMap)).symm
  simp_rw [hf, pow_two]
  simpa only [real_inner_comm v] using
    (b.sum_inner_mul_inner v v).trans (c.sum_inner_mul_inner v v).symm

/-- Evaluation of a harmonic polynomial at a point of the sphere. -/
noncomputable def harmonicEvaluation (ℓ : ℕ) (x : Sphere) :
    harmonicPolynomialSubmodule ℓ →ₗ[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x).toLinearMap.comp (restrictHarmonicLinearMap ℓ)

@[simp] theorem harmonicEvaluation_apply (ℓ : ℕ) (x : Sphere)
    (p : harmonicPolynomialSubmodule ℓ) :
    harmonicEvaluation ℓ x p = restrictPolynomial p.val x := rfl

/-- The pointwise diagonal is the same for every complete orthonormal harmonic
system, even when the systems use different degree bases. -/
theorem harmonicAddition_diag_basis_independent (Y Z : HarmonicBasis)
    (ℓ : ℕ) (x : Sphere) :
    (∑ k : Fin (2 * ℓ + 1), Y.function ℓ k x ^ 2) =
      ∑ k : Fin (2 * ℓ + 1), Z.function ℓ k x ^ 2 := by
  letI := finiteDimensional_harmonicPolynomial ℓ
  have h := orthonormalBasis_sum_sq_linearMap
    (harmonicBasisDegree Y ℓ) (harmonicBasisDegree Z ℓ)
    (harmonicEvaluation ℓ x)
  simpa only [harmonicBasisDegree_apply, harmonicEvaluation_apply,
    harmonicBasisPolynomial_restrict] using h

/-- Any second orthonormal polynomial family of full degree has the same
pointwise squared evaluation sum as a specified harmonic basis. -/
theorem harmonicAddition_diag_of_orthonormal_family (Y : HarmonicBasis)
    (ℓ : ℕ) (x : Sphere)
    (p : Fin (2 * ℓ + 1) → harmonicPolynomialSubmodule ℓ)
    (hp : Orthonormal ℝ p) :
    (∑ k : Fin (2 * ℓ + 1), restrictPolynomial (p k).val x ^ 2) =
      ∑ k : Fin (2 * ℓ + 1), Y.function ℓ k x ^ 2 := by
  letI := finiteDimensional_harmonicPolynomial ℓ
  have hcard : Fintype.card (Fin (2 * ℓ + 1)) =
      Module.finrank ℝ (harmonicPolynomialSubmodule ℓ) := by
    simpa using (finrank_harmonicPolynomialSubmodule ℓ).symm
  let b := OrthonormalBasis.mk hp
    ((Orthonormal.linearIndependent hp).span_eq_top_of_card_eq_finrank hcard).ge
  have h := orthonormalBasis_sum_sq_linearMap b (harmonicBasisDegree Y ℓ)
    (harmonicEvaluation ℓ x)
  simpa only [b, OrthonormalBasis.coe_mk, harmonicBasisDegree_apply,
    harmonicEvaluation_apply, harmonicBasisPolynomial_restrict] using h

/-- A harmonic polynomial family whose restrictions are rotated basis
functions is automatically orthonormal. -/
theorem harmonicAddition_rotated_family_orthonormal (Y : HarmonicBasis)
    (ℓ : ℕ) (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    (p : Fin (2 * ℓ + 1) → harmonicPolynomialSubmodule ℓ)
    (hp : ∀ k x, restrictPolynomial (p k).val x =
      Y.function ℓ k (sphereLinearIsometryEquiv T x)) :
    Orthonormal ℝ p := by
  rw [orthonormal_iff_ite]
  intro k j
  change harmonicL2Inner ℓ (p k) (p j) = _
  simp only [harmonicL2Inner, hp]
  rw [integral_sigma_comp_linear_isometry T
    (fun x => Y.function ℓ k x * Y.function ℓ j x)]
  simpa only [eq_self_iff_true, true_and, Fin.val_inj] using
    Y.orthonormal ℓ ℓ k j

/-- Orthogonal-pullback membership and the correct evaluation identity are
the only geometric inputs to invariance of the addition diagonal. -/
theorem harmonicAddition_diag_rotated_of_family (Y : HarmonicBasis)
    (ℓ : ℕ) (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    (p : Fin (2 * ℓ + 1) → harmonicPolynomialSubmodule ℓ)
    (hp : ∀ k x, restrictPolynomial (p k).val x =
      Y.function ℓ k (sphereLinearIsometryEquiv T x))
    (x : Sphere) :
    (∑ k : Fin (2 * ℓ + 1),
      Y.function ℓ k (sphereLinearIsometryEquiv T x) ^ 2) =
      ∑ k : Fin (2 * ℓ + 1), Y.function ℓ k x ^ 2 := by
  have hon := harmonicAddition_rotated_family_orthonormal Y ℓ T p hp
  simpa only [hp] using harmonicAddition_diag_of_orthonormal_family Y ℓ x p hon

/-- Degree-`ℓ` kernel formed from an arbitrary orthonormal harmonic system. -/
noncomputable def harmonicAdditionKernel (Y : HarmonicBasis) (ℓ : ℕ)
    (x y : Sphere) : ℝ :=
  ∑ k : Fin (2 * ℓ + 1), Y.function ℓ k x * Y.function ℓ k y

/-- The diagonal has the correct spherical average in every degree. -/
theorem harmonicAddition_diag_integral (Y : HarmonicBasis) (ℓ : ℕ) :
    (∫ x : Sphere, (∑ k : Fin (2 * ℓ + 1), Y.function ℓ k x ^ 2) ∂sigma) =
      (2 * ℓ + 1 : ℝ) := by
  rw [integral_finset_sum]
  · have hterm (k : Fin (2 * ℓ + 1)) :
        (∫ x : Sphere, Y.function ℓ k x ^ 2 ∂sigma) = 1 := by
      simpa only [pow_two, if_pos (show ℓ = ℓ ∧ k.val = k.val from ⟨rfl, rfl⟩)]
        using Y.orthonormal ℓ ℓ k k
    simp_rw [hterm]
    simp
  · intro k hk
    simpa [pow_two] using
      continuous_integrable_sigma ((Y.function ℓ k) * (Y.function ℓ k))

/-- The exact diagonal normalization needed for the spectral kernel. -/
def HarmonicAdditionDiagonal (Y : HarmonicBasis) : Prop :=
  ∀ (ℓ : ℕ) (x : Sphere),
    (∑ k : Fin (2 * ℓ + 1), Y.function ℓ k x ^ 2) = (2 * ℓ + 1 : ℝ)

/-- Pointwise rotation invariance is the remaining geometric addition-theorem input. -/
def HarmonicAdditionRotationInvariant (Y : HarmonicBasis) : Prop :=
  ∀ (ℓ : ℕ) (T : Ambient ≃ₗᵢ[ℝ] Ambient) (x : Sphere),
    (∑ k : Fin (2 * ℓ + 1),
      Y.function ℓ k (sphereLinearIsometryEquiv T x) ^ 2) =
    ∑ k : Fin (2 * ℓ + 1), Y.function ℓ k x ^ 2

/-- Orthogonal pullback of the basis proves the finite-degree addition
diagonal is invariant under every ambient orthogonal transformation. -/
theorem harmonicAddition_rotationInvariant (Y : HarmonicBasis) :
    HarmonicAdditionRotationInvariant Y := by
  intro ℓ T x
  let p : Fin (2 * ℓ + 1) → harmonicPolynomialSubmodule ℓ :=
    fun k => orthogonalHarmonicPullback T ℓ (harmonicBasisPolynomial Y ℓ k)
  have hp (k : Fin (2 * ℓ + 1)) (y : Sphere) :
      restrictPolynomial (p k).val y =
        Y.function ℓ k (sphereLinearIsometryEquiv T y) := by
    rw [show p k = orthogonalHarmonicPullback T ℓ
      (harmonicBasisPolynomial Y ℓ k) from rfl]
    rw [restrictPolynomial_orthogonalHarmonicPullback,
      harmonicBasisPolynomial_restrict]
  exact harmonicAddition_diag_rotated_of_family Y ℓ T p hp x

/-- Rotation invariance and the average identity force the exact pointwise diagonal. -/
theorem harmonicAddition_diag_of_rotationInvariant (Y : HarmonicBasis)
    (hinv : HarmonicAdditionRotationInvariant Y) :
    HarmonicAdditionDiagonal Y := by
  intro ℓ x
  let R : Ambient ≃ₗᵢ[ℝ] Ambient :=
    (ℝ ∙ ((x : Ambient) - (northPole : Ambient)))ᗮ.reflection
  have hnorm : ‖(x : Ambient)‖ = ‖(northPole : Ambient)‖ := by
    rw [norm_eq_of_mem_sphere x, norm_eq_of_mem_sphere northPole]
  have hRx : sphereLinearIsometryEquiv R x = northPole := by
    apply Subtype.ext
    exact Submodule.reflection_sub hnorm
  have hconst (y : Sphere) :
      (∑ k : Fin (2 * ℓ + 1), Y.function ℓ k y ^ 2) =
      ∑ k : Fin (2 * ℓ + 1), Y.function ℓ k northPole ^ 2 := by
    let S : Ambient ≃ₗᵢ[ℝ] Ambient :=
      (ℝ ∙ ((y : Ambient) - (northPole : Ambient)))ᗮ.reflection
    have hyNorm : ‖(y : Ambient)‖ = ‖(northPole : Ambient)‖ := by
      rw [norm_eq_of_mem_sphere y, norm_eq_of_mem_sphere northPole]
    have hSy : sphereLinearIsometryEquiv S y = northPole := by
      apply Subtype.ext
      exact Submodule.reflection_sub hyNorm
    simpa [hSy] using (hinv ℓ S y).symm
  have havg := harmonicAddition_diag_integral Y ℓ
  simp_rw [hconst] at havg
  simp [Measure.real_def, sigma_apply_univ] at havg
  calc
    (∑ k : Fin (2 * ℓ + 1), Y.function ℓ k x ^ 2) =
        ∑ k : Fin (2 * ℓ + 1), Y.function ℓ k northPole ^ 2 := hconst x
    _ = (2 * ℓ + 1 : ℝ) := havg

/-- Exact finite-degree diagonal addition identity for every harmonic basis. -/
theorem harmonicAddition_diag (Y : HarmonicBasis) (ℓ : ℕ) (x : Sphere) :
    (∑ k : Fin (2 * ℓ + 1), Y.function ℓ k x ^ 2) =
      (2 * ℓ + 1 : ℝ) :=
  harmonicAddition_diag_of_rotationInvariant Y (harmonicAddition_rotationInvariant Y) ℓ x

/-- Finite Cauchy–Schwarz gives the off-diagonal addition bound from the diagonal identity. -/
theorem harmonicAddition_abs_le_dim_of_diag (Y : HarmonicBasis)
    (hdiag : HarmonicAdditionDiagonal Y) (ℓ : ℕ) (x y : Sphere) :
    |harmonicAdditionKernel Y ℓ x y| ≤ (2 * ℓ + 1 : ℝ) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (2 * ℓ + 1)))
    (fun k => Y.function ℓ k x) (fun k => Y.function ℓ k y)
  have hdim : (0 : ℝ) ≤ (2 * ℓ + 1 : ℕ) := by positivity
  change (harmonicAdditionKernel Y ℓ x y) ^ 2 ≤
    (∑ k : Fin (2 * ℓ + 1), Y.function ℓ k x ^ 2) *
      ∑ k : Fin (2 * ℓ + 1), Y.function ℓ k y ^ 2 at hcs
  rw [hdiag ℓ x, hdiag ℓ y] at hcs
  have hsq : (harmonicAdditionKernel Y ℓ x y) ^ 2 ≤ ((2 * ℓ + 1 : ℝ)) ^ 2 := by
    simpa [pow_two] using hcs
  rw [abs_le]
  constructor <;> nlinarith

/-- The degree addition kernel has absolute value at most its dimension. -/
theorem harmonicAddition_abs_le_dim (Y : HarmonicBasis)
    (ℓ : ℕ) (x y : Sphere) :
    |harmonicAdditionKernel Y ℓ x y| ≤ (2 * ℓ + 1 : ℝ) :=
  harmonicAddition_abs_le_dim_of_diag Y (harmonicAddition_diag Y) ℓ x y

end BEMOC.Definitive
