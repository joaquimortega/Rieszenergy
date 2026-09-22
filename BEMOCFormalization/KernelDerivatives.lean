import BEMOCFormalization.Taylor

namespace BEMOC.Definitive

/-- Distance power in polar coordinates, used only away from zero distance for differentiation. -/
noncomputable def polarKernel (α θ φ ψ : ℝ) : ℝ :=
  (2 - 2 * (Real.cos φ * Real.cos ψ +
    Real.sin φ * Real.sin ψ * Real.cos θ)) ^ (α / 2)

/-- The angular derivative estimate from Lemma derivative-bounds. -/
def PolarDerivativeBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, m + n ≤ 4 → ∀ θ φ ψ : ℝ,
    0 < 2 - 2 * (Real.cos φ * Real.cos ψ +
      Real.sin φ * Real.sin ψ * Real.cos θ) →
    |iteratedDeriv m (fun u => iteratedDeriv n (fun v => polarKernel α θ u v) ψ) φ| ≤
      C * (2 - 2 * (Real.cos φ * Real.cos ψ +
        Real.sin φ * Real.sin ψ * Real.cos θ)) ^ ((α - m - n) / 2)

/-- Smooth extension of the separated averaged kernel, including polar boundaries. -/
def SeparatedDerivativeBound (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧
    ∀ s ∈ Set.Icc (-1 : ℝ) 1, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      0 < 2 - 2 * s * t →
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
        (1 - ε) * (2 - 2 * s * t) →
      ∃ G : ℝ × ℝ → ℝ, ∃ W : Set (ℝ × ℝ), IsOpen W ∧ (s, t) ∈ W ∧
        ContDiffOn ℝ 4 G W ∧
        (∀ p ∈ W, p.1 ∈ Set.Icc (-1 : ℝ) 1 → p.2 ∈ Set.Icc (-1 : ℝ) 1 →
          G p = latitudeKernel α p.1 p.2) ∧
        |mixedFourth G s t| ≤ C * (2 - 2 * s * t) ^ (α / 2 - 4)

end BEMOC.Definitive
