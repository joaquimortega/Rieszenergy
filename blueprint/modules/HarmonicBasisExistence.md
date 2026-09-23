# HarmonicBasisExistence proof guide

This module proves the actual existence statement required by `Sobolev.lean`: `harmonicBasis_nonempty : Nonempty HarmonicBasis`. The `HarmonicBasis` structure has a function in each degree and index `Fin (2ℓ+1)`, requires each function to satisfy the original `IsSphericalHarmonic` predicate, requires orthonormality across every pair of degrees, and requires completeness against all continuous functions on the sphere. The proof does not replace those conditions with a surrogate family and does not assume a basis or an addition theorem.

The construction was staged to keep algebra, measure theory, and geometry separate. `HarmonicDimension.lean` proves that the vector space of homogeneous harmonic polynomials of degree `ℓ` has real dimension `2ℓ+1`; it uses homogeneous monomial counting, surjectivity of the homogeneous polynomial Laplacian, and rank-nullity. `SphereSupport.lean` proves that a nonzero continuous function has strictly positive integral of its square under normalized surface area. This makes the surface integral pairing positive definite on restrictions of harmonic polynomials. `HarmonicOrthonormal.lean` consequently constructs an actual orthonormal basis of every degree-`ℓ` harmonic polynomial space. `HarmonicBasisAssembly.lean` restricts these polynomials to the sphere and proves both same-degree orthonormality and global completeness. Completeness uses Fischer decomposition and Stone–Weierstrass density of genuine harmonic restrictions; it does not assume any preexisting spectral completeness theorem.

The only remaining condition for the assembled family was cross-degree orthogonality. `HarmonicOrthogonality.lean` proves the conditional theorem `harmonic_restrictions_orthogonal_of_angular_integral_zero`. Its proof uses the polynomial Casimir identity from `HarmonicCasimir.lean`, showing that a degree-`m` harmonic polynomial is an eigenvector with eigenvalue `−m(m+1)`. To transfer the Casimir between two factors under the surface integral, it needs angular derivatives to integrate to zero. That exact analytic identity is proved unconditionally in `AngularIntegralZero.lean` by differentiating a norm-continuous polynomial orbit of coordinate-plane rotations and applying rotational invariance of `sigma`.

`crossDegreeHarmonicOrthogonality` packages the conditional Casimir theorem and the unconditional angular identity into the proposition `CrossDegreeHarmonicOrthogonality` declared by `HarmonicBasisAssembly.lean`. Its quantifiers are over arbitrary distinct natural degrees and arbitrary members of the corresponding harmonic polynomial submodules, so it covers every pair of basis vectors. The final line invokes `harmonicBasis_nonempty_of_crossDegree` with that now-proved proposition. This supplies all four fields of `HarmonicBasis` from checked definitions and theorems.

The result is existential and noncomputable because orthonormal bases in finite-dimensional real inner-product spaces are chosen nonconstructively. This does not weaken the mathematical claim: it states existence of functions satisfying the manuscript's exact harmonicity, orthonormality, and completeness contracts. A downstream proof may obtain a witness with `Classical.choose harmonicBasis_nonempty` or `rcases harmonicBasis_nonempty with ⟨Y⟩`. The construction does not by itself prove a zonal addition formula, a spectral expansion of the Riesz kernel, or the final discrepancy inequalities; those are proved in the downstream addition, scalar kernel, and corollary modules.

The required check is `lake build BEMOCFormalization.HarmonicBasisExistence`, followed by the repository-wide shortcut audit. The canonical root `BEMOCFormalization.lean` imports this module transitively, exposing the unconditional theorem in the complete build. Since `HarmonicBasisExistence` imports `AngularIntegralZero`, it also brings the plane-rotation and Casimir chain into the dependency graph. The source order matters: importing this module before the conditional assembly is unavailable, while importing it after the assembly closes the exact premise without a circular dependency.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.AngularIntegralZero

namespace BEMOC.Definitive

/-- Restrictions of genuine homogeneous harmonic polynomials in distinct
degrees are orthogonal for normalized surface area. -/
theorem crossDegreeHarmonicOrthogonality : CrossDegreeHarmonicOrthogonality := by
  intro ℓ m hne p q hp hq
  exact harmonic_restrictions_orthogonal_of_angular_integral_zero
    angular_integral_zero hp hq hne

/-- An actual orthonormal and complete spherical harmonic basis exists. -/
theorem harmonicBasis_nonempty : Nonempty HarmonicBasis :=
  harmonicBasis_nonempty_of_crossDegree crossDegreeHarmonicOrthogonality

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
