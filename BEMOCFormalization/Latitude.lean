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

/-- Every term of the actual ordered energy is nonnegative. -/
theorem diamondEnergy_nonneg (α : ℝ) (N : ℕ) (φ : Phases N) :
    0 ≤ diamondEnergy α N φ := by
  unfold diamondEnergy energy
  positivity

/-- Uniform finite-size closure; no compactness argument over ring phases is needed. -/
theorem small_size_bound {α : ℝ} (hα2 : α < 2) : SmallSizeBound α := by
  refine ⟨(|continuousEnergy α| + 1) * 1024 ^ 2, by positivity, ?_⟩
  intro N hN hNsmall φ
  have hNreal : (N : ℝ) < 1024 := by exact_mod_cast hNsmall
  have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hNlarge : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hscale : 1 ≤ scale α N :=
    Real.one_le_rpow hNlarge (by linarith : 0 ≤ 1 - α / 2)
  have henergy := diamondEnergy_nonneg α N φ
  have hcoeff : continuousEnergy α ≤ |continuousEnergy α| := le_abs_self _
  have hsq : (N : ℝ) ^ 2 ≤ (1024 : ℝ) ^ 2 := by nlinarith
  have hstep : continuousEnergy α * (N : ℝ) ^ 2 ≤
      |continuousEnergy α| * (1024 : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hsq (abs_nonneg _))
  unfold deficit
  nlinarith [mul_nonneg (show 0 ≤ (|continuousEnergy α| + 1) * 1024 ^ 2 by positivity)
    (sub_nonneg.mpr hscale)]

end BEMOC.Definitive
