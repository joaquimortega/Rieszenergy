# Manuscript proof guide

## Source and scope

Theorem `thm:main` of `definitive.tex` is stated for the canonical finite
set of deterministic Diamond points. The checked phase-uniform theorem
`MainTheorem.main_theorem` is stronger: it handles all rotations of every
parallel. `diamond_energy_bound` specializes it to zero phases and exposes
the actual ordered finite-set sum, the explicit continuous energy
`2^(α+1)/(α+2)`, and exact cardinality N in one statement.

`ManuscriptTargets` also packages the cap discrepancy result, existence of
the harmonic model, and both rates for the genuine L² Sobolev worst-case
error. The latter includes every L² class in the spectral unit ball:
`SobolevL2` constructs its unique continuous representative, and
`SobolevL2Corollary` evaluates that representative in the quadrature rule.
Thus the supremum is not restricted to an assumed representable subset.
The proof of `manuscript_targets` uses `main_theorem_target`,
`cap_corollary`, `harmonicBasis_nonempty`, `l2_sobolev_corollary`, and
`l2_sobolev_optimality`; their hypotheses are exactly the stated open ranges.

`manuscript_sobolev_model` explicitly records the two presentation bridges.
For each spectral unit-ball class at s>1 it supplies the unique continuous
representative, and for every degree ℓ it identifies the weak L² eigenspace
of eigenvalue −ℓ(ℓ+1) with the actual harmonic polynomial restrictions.
The weak operator is defined by integration against the intrinsic angular
Laplacian on polynomial restrictions, independently of its later spectral
characterization. This is the sphere-specific polynomial-core formulation;
no separate general-manifold Laplace–Beltrami API or maximal-domain
self-adjoint realization is claimed. The two conjuncts come directly from
`l2Sobolev_continuousRepresentative` and `weakSphereLaplacian_eigen_iff`.

## Dependencies and argument

`Corollaries` supplies the complete energy and discrepancy chain. The
construction module supplies `diamondPoints`, `zeroPhases`,
`diamondPoints_card`, and `diamondPoints_energy`. The last theorem uses
injectivity of the labelled construction to replace its double sum by the
ordered double sum over the finite set. This includes diagonal pairs; their
contribution is zero because α>0.

Fix α with 0<α<2. Obtain the single positive constant C from `main_theorem`.
For every N≥4, construction gives cardinality N. Rewrite the finite-set
energy using `diamondPoints_energy`, and apply the phase-uniform bound to
`zeroPhases N`. Expanding `continuousEnergy`, `deficit`, and `scale` is
definitional, so the displayed formula has exactly the manuscript’s
normalization and exponent. No new analytic estimate is introduced here.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Corollaries
import BEMOCFormalization.SobolevL2Corollary
import BEMOCFormalization.HarmonicLaplacianEigenspace

open scoped BigOperators
open MeasureTheory

namespace BEMOC.Definitive

/-- The main theorem and both corollaries, with the Sobolev supremum taken
over every class in the genuine L² spectral unit ball. -/
def ManuscriptTargets : Prop :=
  MainTheoremTarget ∧ CapDiscrepancyCorollary ∧ Nonempty HarmonicBasis ∧
    ∀ Y : HarmonicBasis, ∀ s : ℝ, ∀ hs : 1 < s, s < 2 →
      L2SobolevCorollary Y s hs ∧ L2SobolevOptimality Y s hs

/-- The unconditional energy and discrepancy results in the manuscript's
L² Sobolev formulation, including the matching universal lower bound. -/
theorem manuscript_targets : ManuscriptTargets := by
  refine ⟨main_theorem_target, cap_corollary, harmonicBasis_nonempty, ?_⟩
  intro Y s hs1 hs2
  exact ⟨l2_sobolev_corollary Y hs1 hs2, l2_sobolev_optimality Y hs1 hs2⟩

/-- The spectral Sobolev model uses all L² classes with their unique
continuous representatives, and its harmonic spaces are exactly the weak
eigenspaces of the intrinsic sphere Laplacian. -/
theorem manuscript_sobolev_model (Y : HarmonicBasis) {s : ℝ} (hs : 1 < s) :
    (∀ f : Lp ℝ 2 sigma, L2SobolevUnitBall Y s f →
      ∃! g : C(Sphere, ℝ),
        (∀ᵐ x ∂sigma, g x = f x) ∧ SobolevUnitBall Y s g) ∧
    (∀ ℓ : ℕ, ∀ f : Lp ℝ 2 sigma,
      WeakSphereLaplacian f ((-((ℓ : ℝ) * (ℓ + 1))) • f) ↔
        ∃ p : harmonicPolynomialSubmodule ℓ,
          f = continuousToLp (restrictPolynomial p.val)) :=
  ⟨fun f hf => l2Sobolev_continuousRepresentative Y hs f hf,
    weakSphereLaplacian_eigen_iff Y⟩

/-- The manuscript's deterministic N-point set has the stated ordered-pair
energy deficit, with a constant uniform in N and exact cardinality. -/
theorem diamond_energy_bound {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
      (diamondPoints N).card = N ∧
      0 ≤ 2 ^ (α + 1) / (α + 2) * (N : ℝ) ^ 2 -
        (∑ x ∈ diamondPoints N, ∑ y ∈ diamondPoints N, dist x y ^ α) ∧
      2 ^ (α + 1) / (α + 2) * (N : ℝ) ^ 2 -
        (∑ x ∈ diamondPoints N, ∑ y ∈ diamondPoints N, dist x y ^ α) ≤
          C * (N : ℝ) ^ (1 - α / 2) := by
  obtain ⟨C, hC, hbound⟩ := main_theorem hα0 hα2
  refine ⟨C, hC, ?_⟩
  intro N hN
  refine ⟨diamondPoints_card hN, ?_⟩
  rw [diamondPoints_energy hN]
  exact hbound N hN (zeroPhases N)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
