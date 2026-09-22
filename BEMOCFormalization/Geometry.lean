import BEMOCFormalization.Construction

open scoped BigOperators
namespace BEMOC.Definitive

/-- Uniform geometric estimates; constants never depend on N or phases. -/
def GeometryBounds : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
    (∀ j : RingIndex N,
      c * bandParameter N * radius N (j.val + 1) ≤ population N (j.val + 1) ∧
      (population N (j.val + 1) : ℝ) ≤
        C * bandParameter N * radius N (j.val + 1)) ∧
    (∀ j : RingIndex N, population N (j.val + 1) ≤ 15 * bandParameter N) ∧
    (∀ n : ℕ, (Finset.univ.filter
      (fun j : RingIndex N => population N (j.val + 1) = n)).card ≤ 3)

/-- Polar interval in increasing angular coordinates. -/
def polarBand (N j : ℕ) : Set ℝ :=
  Set.Icc (Real.arccos (boundary N (j - 1))) (Real.arccos (boundary N j))

/-- Polar geometry used for block estimates, after the explicit large-N cutoff. -/
def AngularGeometry : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 16 ≤ bandParameter N →
    (∀ j : RingIndex N,
      c / bandParameter N ≤ Real.arccos (boundary N (j.val + 1)) -
        Real.arccos (boundary N j.val) ∧
      Real.arccos (boundary N (j.val + 1)) - Real.arccos (boundary N j.val)
        ≤ C / bandParameter N) ∧
    (∀ j : RingIndex N, j.val ≠ 0 → j.val + 1 ≠ 2 * bandParameter N - 1 →
      ∀ θ ∈ polarBand N (j.val + 1),
        c * population N (j.val + 1) / bandParameter N ≤ Real.sin θ ∧
        Real.sin θ ≤ C * population N (j.val + 1) / bandParameter N) ∧
    (∀ j k : RingIndex N, 2 ≤ |(j.val : ℤ) - k.val| →
      ∀ θ ∈ polarBand N (j.val + 1), ∀ ψ ∈ polarBand N (k.val + 1),
        c * |(j.val : ℝ) - k.val| / bandParameter N ≤ |θ - ψ| ∧
        |θ - ψ| ≤ C * |(j.val : ℝ) - k.val| / bandParameter N)

end BEMOC.Definitive
