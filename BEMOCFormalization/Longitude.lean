import BEMOCFormalization.Trapezoid
import BEMOCFormalization.Geometry
import BEMOCFormalization.EnergyDecomposition

open scoped BigOperators
namespace BEMOC.Definitive

/-- The arithmetic double sum after reducing angular quadrature to gcd/lcm. -/
noncomputable def gcdSum (α : ℝ) (T : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 T, ∑ v ∈ Finset.Icc 1 T,
    (Nat.gcd u v : ℝ) ^ (1 + α) / ((u : ℝ) * v) ^ (α / 2)

/-- The two zeta sums are finite because α>0. -/
def GcdSumBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, gcdSum α T ≤ C * (T : ℝ) ^ 2

/-- Phase-uniform longitude estimate for the actual Diamond energy. -/
def LongitudeBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N,
    |longitudeError α N φ| ≤ C * scale α N

end BEMOC.Definitive
