import BEMOCFormalization.LatitudeFiniteFallback
import BEMOCFormalization.LatitudeUnequalPointwiseClosure

/-!
# Final latitude endpoint assembly

All oriented unequal-scale cases are unconditional.  This module records
the exact remaining seam: a uniform comparable-scale pointwise bound for
`M ≥ 600` automatically supplies the very-large row estimate, the finite
fallback, and the concrete latitude deficit bound.
-/

namespace BEMOC

/-- Uniform comparable-scale pointwise control in the range where all
fixed neighboring charts are available. -/
def HasVeryLargeComparableLatitudeBlockBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36, 600 ≤ bandCount N →
    HasComparableLatitudeBlockBound α N C

/-- The remaining comparable-scale package combines with the unconditional
unequal-scale package to give the very-large row interface. -/
theorem hasVeryLargeLatitudeBlockRowBound_of_comparable
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hcomp : HasVeryLargeComparableLatitudeBlockBound α) :
    HasVeryLargeLatitudeBlockRowBound α := by
  obtain ⟨Ccomp, hCcomp, hcomp⟩ := hcomp
  let Cunequal := latitudeUnequalGeometricConstant α
  let C := Ccomp + Cunequal
  let Crow :=
    C * latitudeComparableSumConstant α +
      C * latitudeComparableSumConstant α + 2 * C
  have hCunequal : 0 < Cunequal := by
    exact latitudeUnequalGeometricConstant_pos α
  have hC : 0 < C := add_pos hCcomp hCunequal
  have hCrow : 0 < Crow := by
    dsimp [Crow]
    have hsum := latitudeComparableSumConstant_pos hα2
    positivity
  refine ⟨Crow, hCrow, ?_⟩
  intro N hN hM
  have hcompC : HasComparableLatitudeBlockBound α N C :=
    (hcomp N hN hM).mono (by
      dsimp [C]
      linarith [hCunequal])
  have hunequalC : HasUnequalLatitudeBlockBound α N C :=
    (hasUnequalLatitudeBlockBound_series hα0 hα2 (by omega)).mono (by
      dsimp [C, Cunequal]
      linarith [hCcomp])
  have hcomplete :=
    hasCompleteLatitudeBlockEstimate_of_pointwise
      hα0 hα2 hC.le (by omega) hcompC hunequalC
  simpa [Crow, C] using hcomplete.rowBound

/-- Public concrete latitude endpoint reduced only to the uniform
comparable-scale pointwise estimate. -/
theorem exists_bemocLatitudeDeficit_concrete_bound_of_comparable
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hcomp : HasVeryLargeComparableLatitudeBlockBound α) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      |bemocLatitudeDeficit α N| ≤
        C * (N : ℝ) ^ (1 - α / 2) :=
  exists_bemocLatitudeDeficit_concrete_bound_of_veryLargeRows
    hα0 hα2
      (hasVeryLargeLatitudeBlockRowBound_of_comparable hα0 hα2 hcomp)

end BEMOC
