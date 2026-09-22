import BEMOCFormalization.Latitude
import BEMOCFormalization.Longitude

namespace BEMOC.Definitive

/-- Main theorem target, with constants uniform over every N and every choice of phases. -/
def MainTheorem (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N,
    0 ≤ deficit α N φ ∧ deficit α N φ ≤ C * scale α N

/-- Proved assembly; analytic estimates and geometric nonnegativity remain explicit inputs. -/
theorem main_theorem_of_estimates {α : ℝ}
    (hlat : LatitudeBound α) (hlong : LongitudeBound α)
    (hsmall : SmallSizeBound α) (hnonneg : DiamondNonnegative α) : MainTheorem α := by
  obtain ⟨A, hA, hlat⟩ := hlat
  obtain ⟨B, hB, hlong⟩ := hlong
  obtain ⟨S, hS, hsmall⟩ := hsmall
  refine ⟨A + B + S, by positivity, ?_⟩
  intro N hN φ
  refine ⟨hnonneg N hN φ, ?_⟩
  have hscale : 0 ≤ scale α N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  by_cases hlarge : 1024 ≤ N
  · have ha := (le_abs_self (latitudeError α N)).trans (hlat N hlarge)
    have hb := (le_abs_self (longitudeError α N φ)).trans (hlong N hN φ)
    rw [deficit_eq_latitude_add_longitude]
    nlinarith [mul_nonneg (le_of_lt hS) hscale]
  · have hs := hsmall N hN (by omega) φ
    nlinarith [mul_nonneg (le_of_lt hA) hscale, mul_nonneg (le_of_lt hB) hscale]

/-- Complete unconditional statement to be proved; no proof of this target is asserted. -/
def MainTheoremTarget : Prop := ∀ α : ℝ, 0 < α → α < 2 → MainTheorem α

end BEMOC.Definitive
