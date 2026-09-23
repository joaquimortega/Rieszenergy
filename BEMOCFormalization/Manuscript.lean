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
