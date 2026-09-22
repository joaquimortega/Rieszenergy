import BEMOCFormalization.FourierDecay

open scoped BigOperators
namespace BEMOC.Definitive

/-- Phase-shifted equally spaced quadrature on a full angular period. -/
noncomputable def angularAverage (L : ℕ) (φ : ℝ) (f : ℝ → ℝ) : ℝ :=
  (L : ℝ)⁻¹ * ∑ k : Fin L, f (φ + 2 * Real.pi * (k.val : ℝ) / L)
/-- The angular distance-power model. -/
noncomputable def angularKernel (α A B θ : ℝ) : ℝ := (A - B * Real.cos θ) ^ (α / 2)

/-- Lemma trap, with B=0, A=B, L=1 and arbitrary phase all retained. -/
def TrapezoidBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ A B : ℝ, 0 ≤ B → B ≤ A →
    ∀ L : ℕ, 1 ≤ L → ∀ φ : ℝ,
      |angularAverage L φ (angularKernel α A B) -
        (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, angularKernel α A B θ| ≤
        C * B ^ (α / 2) * (L : ℝ) ^ (-1 - α)

/-- Finite group counting identity underlying the angular aliasing. -/
def GridMultiplicity : Prop :=
  ∀ q r : ℕ, 0 < q → 0 < r → ∀ f : ℝ → ℝ,
    Function.Periodic f (2 * Real.pi) → ∀ φ : ℝ,
      (∑ i : Fin q, ∑ j : Fin r,
        f (φ + 2 * Real.pi * ((i.val : ℝ) / q - (j.val : ℝ) / r))) =
      (Nat.gcd q r : ℝ) * ∑ k : Fin (Nat.lcm q r),
        f (φ + 2 * Real.pi * (k.val : ℝ) / Nat.lcm q r)

end BEMOC.Definitive
