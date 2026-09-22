import BEMOCFormalization.Construction
import BEMOCFormalization.ContinuousEnergy

open scoped BigOperators
namespace BEMOC.Definitive

/-- Energy of the weighted union of uniform parallels. -/
noncomputable def ringEnergy (α : ℝ) (N : ℕ) : ℝ :=
  ∑ j : RingIndex N, ∑ k : RingIndex N,
    (population N (j.val + 1) : ℝ) * population N (k.val + 1) *
      latitudeKernel α (height N (j.val + 1)) (height N (k.val + 1))
/-- Latitude error A. -/
noncomputable def latitudeError (α : ℝ) (N : ℕ) : ℝ :=
  continuousEnergy α * (N : ℝ) ^ 2 - ringEnergy α N
/-- Angular discretization error B; phases are retained. -/
noncomputable def longitudeError (α : ℝ) (N : ℕ) (φ : Phases N) : ℝ :=
  ringEnergy α N - diamondEnergy α N φ
/-- The actual energy deficit appearing in Theorem 1. -/
noncomputable def deficit (α : ℝ) (N : ℕ) (φ : Phases N) : ℝ :=
  continuousEnergy α * (N : ℝ) ^ 2 - diamondEnergy α N φ

/-- The two-term decomposition is algebraic and already proved. -/
theorem deficit_eq_latitude_add_longitude (α : ℝ) (N : ℕ) (φ : Phases N) :
    deficit α N φ = latitudeError α N + longitudeError α N φ := by
  unfold deficit latitudeError longitudeError
  ring

/-- Required geometric identification, including the finite-label cardinality. -/
def DiamondNonnegative (α : ℝ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N, 0 ≤ deficit α N φ

end BEMOC.Definitive
