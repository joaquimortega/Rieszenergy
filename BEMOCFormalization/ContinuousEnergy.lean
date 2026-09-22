import BEMOCFormalization.Core

open MeasureTheory
namespace BEMOC.Definitive

/-- Geometric normalized surface area has the height-angle integration formula. -/
def SurfaceIntegration : Prop :=
  IsProbabilityMeasure sigma ∧
  ∀ f : Ambient → ℝ, Continuous f →
    (∫ x : Sphere, f x ∂sigma) =
      (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
        (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f (parallelVector t θ)

/-- Rotational invariance and the beta integral give a constant potential. -/
def ConstantPotential (α : ℝ) : Prop :=
  ∀ x : Sphere, (∫ y : Sphere, dist x y ^ α ∂sigma) = continuousEnergy α

/-- Finite-configuration nonnegativity, for the actual geometric surface constant. -/
def EnergyNonnegative (α : ℝ) : Prop :=
  ∀ n : ℕ, ∀ X : Fin n → Sphere,
    0 ≤ continuousEnergy α * (n : ℝ) ^ 2 - energy X α

/-- Measure-level negative type, stated using differences of positive finite measures. -/
def MeasureNegativeType (α : ℝ) : Prop :=
  ∀ μ ν : Measure Sphere, IsFiniteMeasure μ → IsFiniteMeasure ν →
    μ Set.univ = ν Set.univ →
    (∫ x, ∫ y, dist x y ^ α ∂μ ∂μ) +
      (∫ x, ∫ y, dist x y ^ α ∂ν ∂ν) -
        2 * (∫ x, ∫ y, dist x y ^ α ∂ν ∂μ) ≤ 0

end BEMOC.Definitive
