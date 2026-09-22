import BEMOCFormalization.ComparableBlocks
import BEMOCFormalization.UnequalBlocks

namespace BEMOC.Definitive

/-- Latitude bound after summing the three block regimes. -/
def LatitudeBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N →
    |latitudeError α N| ≤ C * scale α N

/-- Uniform finite-size bound, also uniform over the continuously varying phases. -/
def SmallSizeBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → N < 1024 →
    ∀ φ : Phases N, deficit α N φ ≤ C * scale α N

end BEMOC.Definitive
