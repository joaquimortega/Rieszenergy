# HarmonicBasisAssembly proof guide

This module connects the finite-dimensional algebraic and analytic foundations to the exact `HarmonicBasis` structure declared in `Sobolev.lean`. Its chosen degree-`m` functions are `harmonicFunction m k`, the sphere restrictions of `harmonicOrthonormalBasis m k`. Each is a genuine restriction of a homogeneous polynomial annihilated by the manuscript's Euclidean Laplacian. The `Fin (2*m+1)` index comes from the proven dimension formula, and same-degree orthonormality comes from the integral inner product in `HarmonicOrthonormal`. No new basis is postulated.

The central unconditional result is `harmonicFunction_complete`. Let `f : C(Sphere,ℝ)` be orthogonal to every chosen harmonic function in the exact ordered product integral appearing in `HarmonicBasis.complete`. For each degree `m`, surface integration against `f` defines a real linear functional on the harmonic polynomial submodule through restriction. This functional vanishes on every vector of `harmonicOrthonormalBasis m` by hypothesis, so mathlib's `Basis.ext` makes it zero on the entire degree-`m` harmonic space. Using `isSphericalHarmonic_iff_range`, it therefore vanishes on every function satisfying the original `IsSphericalHarmonic m` predicate.

The proof must extend this vanishing to all continuous functions without silently treating L² convergence as uniform convergence. `sigmaPairingLinearMap f` integrates `f*g`, and `sigmaPairingCLM f` upgrades it to a continuous linear map for the supremum norm on `C(Sphere,ℝ)`. The operator bound is `‖∫ f g dσ‖ ≤ ‖f‖∞‖g‖∞`: the pointwise continuous-map norm estimates bound the integrand, `norm_integral_le_of_norm_le_const` bounds the integral, and `sigma_apply_univ=1` removes the mass factor. The kernel is closed. Since it contains every genuine harmonic restriction, it contains `harmonicRestrictionSpan`; the checked theorem `harmonicRestrictionSpan_dense` and `Continuous.ext_on` then force the pairing map to vanish everywhere. Evaluating it at `g=f` gives `∫ f² dσ=0`, and `sigma_integral_sq_pos` forces `f=0`. This proves completeness independently of cross-degree orthogonality.

`CrossDegreeHarmonicOrthogonality` states the geometric integral identity precisely: if `ℓ≠m` and `p`, `q` are genuine homogeneous harmonic polynomials of degrees `ℓ`, `m`, their restrictions have zero surface product integral. The theorem `harmonicBasis_nonempty_of_crossDegree` constructs a `HarmonicBasis` from that proposition. Its `harmonic` field is immediate from restriction membership, its equal-degree `orthonormal` cases use `OrthonormalBasis.orthonormal`, its unequal-degree cases invoke the hypothesis, and its `complete` field is the unconditional result above. The hypothesis is now discharged in `HarmonicBasisExistence.lean`: `PlaneRotation.lean` and `AngularIntegralZero.lean` establish infinitesimal rotation invariance, and `HarmonicOrthogonality.lean` uses the polynomial Casimir identity to prove cross-degree orthogonality. Consequently `harmonicBasis_nonempty` is an unconditional checked theorem.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
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
```

<!-- END_LEAN_STATEMENTS -->
