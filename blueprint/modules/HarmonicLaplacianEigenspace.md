# HarmonicLaplacianEigenspace: polynomial eigenfunctions

The intrinsic polynomial sphere Laplacian has precisely the genuine degree-`ℓ` harmonic restrictions as its `−ℓ(ℓ+1)` eigenspace. The reverse implication uses the independently proved weak `L²` differential equation and its harmonic eigenspace theorem: self-adjointness puts every polynomial eigenfunction in the weak graph, and injectivity of continuous functions into `L²` pulls the resulting harmonic representative back to the polynomial sphere subspace. The theorem is also exposed without choosing a basis, using the proved existence of a complete harmonic basis.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.HarmonicL2Laplacian
import BEMOCFormalization.HarmonicBasisExistence

/-! Polynomial eigenspaces of the intrinsic sphere Laplacian. -/

open MeasureTheory
namespace BEMOC.Definitive

/-- Every polynomial restriction belongs to the weak graph of the intrinsic
sphere Laplacian, with its Casimir image as weak derivative. -/
theorem weakSphereLaplacian_polynomial (p : Poly3) :
    WeakSphereLaplacian (continuousToLp (restrictPolynomial p))
      (continuousToLp (restrictPolynomial (angularCasimir p))) := by
  apply (weakSphereLaplacian_iff_polynomial _ _).2
  intro q
  have hp := continuousToLp_ae (restrictPolynomial p)
  have hcp := continuousToLp_ae (restrictPolynomial (angularCasimir p))
  calc
    (∫ x : Sphere, (continuousToLp (restrictPolynomial p) : Sphere → ℝ) x *
        restrictPolynomial (angularCasimir q) x ∂sigma) =
      ∫ x : Sphere, restrictPolynomial p x *
        restrictPolynomial (angularCasimir q) x ∂sigma := by
          apply integral_congr_ae
          filter_upwards [hp] with x hx
          rw [hx]
    _ = ∫ x : Sphere, restrictPolynomial (angularCasimir p) x *
        restrictPolynomial q x ∂sigma :=
          (angularCasimir_integral_selfAdjoint p q).symm
    _ = ∫ x : Sphere,
        (continuousToLp (restrictPolynomial (angularCasimir p)) : Sphere → ℝ) x *
          restrictPolynomial q x ∂sigma := by
          apply integral_congr_ae
          filter_upwards [hcp] with x hx
          rw [hx]

/-- On polynomial sphere functions, the `-ℓ(ℓ+1)` eigenspace is exactly
the restrictions of genuine degree-`ℓ` homogeneous harmonic polynomials. -/
theorem spherePolynomialLaplacian_eigen_iff
    (Y : HarmonicBasis) (ℓ : ℕ) (f : PolynomialSphere) :
    spherePolynomialLaplacian f =
      (-((ℓ : ℝ) * (ℓ + 1))) • f ↔
      ∃ H : harmonicPolynomialSubmodule ℓ,
        f = polynomialSphereOf H.val := by
  let eig : ℝ := -((ℓ : ℝ) * (ℓ + 1))
  constructor
  · intro hf
    obtain ⟨p, hp⟩ := f.property
    have hfp : f = polynomialSphereOf p := Subtype.ext hp.symm
    have hcas : restrictPolynomial (angularCasimir p) =
        eig • restrictPolynomial p := by
      have he : spherePolynomialLaplacian (polynomialSphereOf p) =
          eig • polynomialSphereOf p := by simpa only [hfp] using hf
      rw [spherePolynomialLaplacian_restrict] at he
      exact congrArg Subtype.val he
    have hLpeq : continuousToLp (restrictPolynomial (angularCasimir p)) =
        eig • continuousToLp (restrictPolynomial p) := by
      apply Lp.ext
      filter_upwards [continuousToLp_ae (restrictPolynomial (angularCasimir p)),
        continuousToLp_ae (restrictPolynomial p),
        Lp.coeFn_smul eig (continuousToLp (restrictPolynomial p))]
        with x hx hy hz
      rw [hx, hz]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hy, hcas]
      simp [smul_eq_mul]
    have hweak : WeakSphereLaplacian
        (continuousToLp (restrictPolynomial p))
        (eig • continuousToLp (restrictPolynomial p)) := by
      rw [← hLpeq]
      exact weakSphereLaplacian_polynomial p
    obtain ⟨H, hH⟩ :=
      (weakSphereLaplacian_eigen_iff Y ℓ
        (continuousToLp (restrictPolynomial p))).mp hweak
    have hcont : restrictPolynomial p = restrictPolynomial H.val :=
      continuousToLp_injective hH
    exact ⟨H, by rw [hfp]; exact Subtype.ext hcont⟩
  · rintro ⟨H, rfl⟩
    exact spherePolynomialLaplacian_harmonic H.property

/-- The polynomial eigenspace characterization needs no chosen basis: one
exists by the proved harmonic-basis construction. -/
theorem spherePolynomialLaplacian_eigen_iff_unconditional
    (ℓ : ℕ) (f : PolynomialSphere) :
    spherePolynomialLaplacian f =
      (-((ℓ : ℝ) * (ℓ + 1))) • f ↔
      ∃ H : harmonicPolynomialSubmodule ℓ,
        f = polynomialSphereOf H.val := by
  exact spherePolynomialLaplacian_eigen_iff
    (Classical.choice harmonicBasis_nonempty) ℓ f

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
