import BEMOCFormalization.Core

namespace BEMOC.Definitive

/-- The even real profile used in Appendix 1, including the cusp at δ=0. -/
noncomputable def fourierProfile (a δ θ : ℝ) : ℝ := (1 + δ - Real.cos θ) ^ a
/-- Real cosine coefficient; the sine coefficient vanishes by evenness. -/
noncomputable def cosineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f θ * Real.cos (n * θ)

/-- Appendix 1 monotonicity, including δ=0 and all positive frequencies. -/
def FourierDomination (a : ℝ) : Prop :=
  ∀ δ : ℝ, 0 ≤ δ → ∀ n : ℕ, 1 ≤ n →
    cosineCoefficient (fourierProfile a 0) n ≤ cosineCoefficient (fourierProfile a δ) n ∧
    cosineCoefficient (fourierProfile a δ) n ≤ 0

/-- Gamma formula for the cusp profile; positive n avoids the zero mode. -/
def CuspCoefficientFormula (a : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    cosineCoefficient (fourierProfile a 0) n =
      -(2 : ℝ) ^ (-a) * Real.Gamma (2 * a + 1) * Real.sin (Real.pi * a) /
        Real.pi * (Real.Gamma (n - a) / Real.Gamma (n + a + 1))

/-- Uniform Fourier decay; the constant is outside all geometric parameters. -/
def FourierDecayBound (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 ≤ δ → ∀ n : ℕ, 1 ≤ n →
    |cosineCoefficient (fourierProfile a δ) n| ≤ C * (n : ℝ) ^ (-1 - 2 * a)

end BEMOC.Definitive
