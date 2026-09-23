import BEMOCFormalization.HarmonicOrthonormal

open MeasureTheory
namespace BEMOC.Definitive

noncomputable def harmonicFunction (m : ℕ) (k : Fin (2 * m + 1)) : C(Sphere, ℝ) :=
  restrictPolynomial ((harmonicOrthonormalBasis m) k).val

theorem harmonicFunction_isSphericalHarmonic (m : ℕ) (k : Fin (2 * m + 1)) :
    IsSphericalHarmonic m (harmonicFunction m k) :=
  restrictPolynomial_isSphericalHarmonic
    ((harmonicOrthonormalBasis m) k).property

theorem harmonicFunction_orthonormal_same (m : ℕ)
    (k l : Fin (2 * m + 1)) :
    (∫ x, harmonicFunction m k x * harmonicFunction m l x ∂sigma) =
      if k = l then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (harmonicOrthonormalBasis m).orthonormal) k l
  simpa [harmonicFunction, harmonicL2Inner, harmonicInnerCore,
    harmonicInnerProductSpace] using h

noncomputable def sigmaPairingLinearMap (f : C(Sphere, ℝ)) :
    C(Sphere, ℝ) →ₗ[ℝ] ℝ where
  toFun g := ∫ x, f x * g x ∂sigma
  map_add' g h := by
    simp only [ContinuousMap.add_apply, mul_add]
    exact integral_add
      (continuous_integrable_sigma (f * g))
      (continuous_integrable_sigma (f * h))
  map_smul' c g := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm (f _) c]
    exact integral_const_mul c _

noncomputable def sigmaPairingCLM (f : C(Sphere, ℝ)) :
    C(Sphere, ℝ) →L[ℝ] ℝ := by
  apply (sigmaPairingLinearMap f).mkContinuous ‖f‖
  intro g
  have hbound : ∀ᵐ x ∂sigma, ‖f x * g x‖ ≤ ‖f‖ * ‖g‖ := by
    apply Filter.Eventually.of_forall
    intro x
    rw [norm_mul]
    exact mul_le_mul (f.norm_coe_le_norm x) (g.norm_coe_le_norm x)
      (norm_nonneg _) (norm_nonneg _)
  simpa [sigmaPairingLinearMap, sigma_apply_univ] using
    (norm_integral_le_of_norm_le_const (μ := sigma) hbound)

theorem sigmaPairing_zero_on_harmonics (f : C(Sphere, ℝ))
    (hf : ∀ m k, (sigmaPairingCLM f) (harmonicFunction m k) = 0)
    (m : ℕ) (p : harmonicPolynomialSubmodule m) :
    (sigmaPairingCLM f) (restrictPolynomial p.val) = 0 := by
  let L : harmonicPolynomialSubmodule m →ₗ[ℝ] ℝ :=
    (sigmaPairingCLM f).toLinearMap.comp (restrictHarmonicLinearMap m)
  have hL : L = 0 := (harmonicOrthonormalBasis m).toBasis.ext (by
    intro k
    simpa [L, harmonicFunction, restrictHarmonicLinearMap] using hf m k)
  exact congrArg (fun T : harmonicPolynomialSubmodule m →ₗ[ℝ] ℝ => T p) hL

theorem harmonicFunction_complete (f : C(Sphere, ℝ))
    (hf : ∀ m k, (∫ x, f x * harmonicFunction m k x ∂sigma) = 0) :
    f = 0 := by
  have hf' : ∀ m k, (sigmaPairingCLM f) (harmonicFunction m k) = 0 := hf
  have hspan : harmonicRestrictionSpan ≤ LinearMap.ker (sigmaPairingCLM f).toLinearMap := by
    apply Submodule.span_le.mpr
    intro g hg
    obtain ⟨m, hm⟩ := hg
    obtain ⟨p, rfl⟩ := (isSphericalHarmonic_iff_range m g).mp hm
    exact sigmaPairing_zero_on_harmonics f hf' m p
  have hzero : ∀ g : C(Sphere, ℝ), (sigmaPairingCLM f) g = 0 := by
    have heq : (fun g : C(Sphere, ℝ) => (sigmaPairingCLM f) g) =
        (fun _ => (0 : ℝ)) :=
      Continuous.ext_on harmonicRestrictionSpan_dense
        (sigmaPairingCLM f).continuous continuous_const
        (by intro g hg; exact hspan hg)
    intro g
    exact congrFun heq g
  by_contra hne
  have hpos := sigma_integral_sq_pos hne
  apply (ne_of_gt hpos)
  simpa [sigmaPairingCLM, sigmaPairingLinearMap, pow_two] using hzero f

/-- The remaining geometric integral identity needed to join the per-degree
orthonormal bases into a global spherical harmonic system. -/
def CrossDegreeHarmonicOrthogonality : Prop :=
  ∀ {ℓ m : ℕ} (_ : ℓ ≠ m)
    {p q : MvPolynomial (Fin 3) ℝ},
    p ∈ harmonicPolynomialSubmodule ℓ →
    q ∈ harmonicPolynomialSubmodule m →
    (∫ x, restrictPolynomial p x * restrictPolynomial q x ∂sigma) = 0

theorem harmonicBasis_nonempty_of_crossDegree
    (hcross : CrossDegreeHarmonicOrthogonality) :
    Nonempty HarmonicBasis := by
  refine ⟨⟨harmonicFunction, harmonicFunction_isSphericalHarmonic, ?_, ?_⟩⟩
  · intro ℓ m k l
    by_cases heq : ℓ = m
    · subst m
      simpa [Fin.ext_iff] using harmonicFunction_orthonormal_same ℓ k l
    · have hzero := hcross heq
        ((harmonicOrthonormalBasis ℓ) k).property
        ((harmonicOrthonormalBasis m) l).property
      simpa [harmonicFunction, heq] using hzero
  · intro f hf
    exact harmonicFunction_complete f hf

end BEMOC.Definitive
