import BEMOCFormalization.LatitudeExceptionalComparablePointwiseClosure
import BEMOCFormalization.LatitudeNeighboringSmoothPointwiseClosure
import BEMOCFormalization.LatitudeResonantOscillationClosure
import BEMOCFormalization.LatitudeCentralResonantPointwiseClosure
import BEMOCFormalization.LatitudeFinalAssembly

/-!
# Unconditional comparable latitude closure

This module packages the completed exceptional and central estimates with
constants independent of the depth.  The final neighboring and resonant
constructors are inserted below once their analytic modules have been
checked.
-/

namespace BEMOC

theorem neighboringResonantFullBlockConstant_nonneg :
    0 ≤ neighboringResonantFullBlockConstant := by
  unfold neighboringResonantFullBlockConstant
  exact add_nonneg neighboringSmallDepthBlockConstant_pos.le
    neighboringResonantLargeDepthBlockConstant_nonneg

noncomputable def neighboringUpperComparableBlockConstant (α : ℝ) : ℝ :=
  neighboringSmallDepthBlockConstant α +
    neighboringUpperSmoothBlockConstant α +
      neighboringUpperBranchBlockConstant α

noncomputable def neighboringLowerComparableBlockConstant (α : ℝ) : ℝ :=
  neighboringSmallDepthBlockConstant α +
    neighboringLowerSmoothBlockConstant α +
      neighboringLowerBranchBlockConstant α

theorem neighboringUpperBranchBlockConstant_nonneg
    {α : ℝ} (hα1 : 1 < α) :
    0 ≤ neighboringUpperBranchBlockConstant α := by
  unfold neighboringUpperBranchBlockConstant
  have hden :
      0 ≤ (reducedCuspUpperNu α - 1) * reducedCuspUpperNu α := by
    unfold reducedCuspUpperNu
    exact mul_nonneg (by linarith) (by linarith)
  have hquot :
      0 ≤ reducedCuspD2MajorantCoefficient α /
        ((reducedCuspUpperNu α - 1) * reducedCuspUpperNu α) :=
    div_nonneg (reducedCuspD2MajorantCoefficient_nonneg α) hden
  positivity

theorem neighboringLowerBranchBlockConstant_nonneg
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 ≤ neighboringLowerBranchBlockConstant α := by
  unfold neighboringLowerBranchBlockConstant
  have hnu : 0 ≤ reducedCuspUpperNu α := by
    unfold reducedCuspUpperNu
    linarith
  have hquot :
      0 ≤ reducedCuspLowerD1MajorantCoefficient α /
        reducedCuspUpperNu α :=
    div_nonneg (reducedCuspLowerD1MajorantCoefficient_nonneg hα1) hnu
  positivity

theorem neighboringUpperComparableBlockConstant_nonneg
    {α : ℝ} (hα1 : 1 < α) :
    0 ≤ neighboringUpperComparableBlockConstant α := by
  unfold neighboringUpperComparableBlockConstant
  exact add_nonneg
    (add_nonneg neighboringSmallDepthBlockConstant_pos.le
      (neighboringUpperSmoothBlockConstant_nonneg α))
    (neighboringUpperBranchBlockConstant_nonneg hα1)

theorem neighboringLowerComparableBlockConstant_nonneg
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 ≤ neighboringLowerComparableBlockConstant α := by
  unfold neighboringLowerComparableBlockConstant
  exact add_nonneg
    (add_nonneg neighboringSmallDepthBlockConstant_pos.le
      (neighboringLowerSmoothBlockConstant_nonneg α))
    (neighboringLowerBranchBlockConstant_nonneg hα0 hα1)

theorem hasNeighboringComparableLatitudeBlockBound_upper
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    HasNeighboringComparableLatitudeBlockBound α N
      (neighboringUpperComparableBlockConstant α) := by
  simpa [HasNeighboringComparableLatitudeBlockBound,
    neighboringUpperComparableBlockConstant] using
      neighboringComparable_upper_block_bound hα1 hα2 hM

theorem hasNeighboringComparableLatitudeBlockBound_lower
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    HasNeighboringComparableLatitudeBlockBound α N
      (neighboringLowerComparableBlockConstant α) := by
  simpa [HasNeighboringComparableLatitudeBlockBound,
    neighboringLowerComparableBlockConstant] using
      neighboringComparable_lower_block_bound hα0 hα1 hM

noncomputable def smoothOppositeComparableBlockConstant (α : ℝ) : ℝ :=
  65536 * exceptionalLatitudeDssttConstant α +
    8192 * exceptionalComparableSharpConstant α

theorem smoothOppositeComparableBlockConstant_nonneg (α : ℝ) :
    0 ≤ smoothOppositeComparableBlockConstant α := by
  unfold smoothOppositeComparableBlockConstant
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (exceptionalLatitudeDssttConstant_nonneg α))
    (mul_nonneg (by norm_num)
      (exceptionalComparableSharpConstant_nonneg α))

theorem hasSmoothOppositeComparableLatitudeBlockBound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N) :
    HasSmoothOppositeComparableLatitudeBlockBound α N
      (smoothOppositeComparableBlockConstant α) := by
  simpa [smoothOppositeComparableBlockConstant] using
    hasSmoothOppositeComparableLatitudeBlockBound_generic
      hα0 hα2 hM

noncomputable def centralUpperComparableBlockConstant (α : ℝ) : ℝ :=
  centralUpperNeighboringBlockConstant α +
    (15 : ℝ) ^ 6 / 2 * exceptionalComparableSharpConstant α

noncomputable def centralLowerComparableBlockConstant (α : ℝ) : ℝ :=
  centralLowerNeighboringBlockConstant α +
    (15 : ℝ) ^ 6 / 2 * exceptionalComparableSharpConstant α

theorem centralUpperComparableBlockConstant_nonneg
    {α : ℝ} (hα1 : 1 < α) :
    0 ≤ centralUpperComparableBlockConstant α := by
  unfold centralUpperComparableBlockConstant
  exact add_nonneg
    (centralUpperNeighboringBlockConstant_nonneg hα1)
    (mul_nonneg (by positivity)
      (exceptionalComparableSharpConstant_nonneg α))

theorem centralLowerComparableBlockConstant_nonneg
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 ≤ centralLowerComparableBlockConstant α := by
  unfold centralLowerComparableBlockConstant
  exact add_nonneg
    (centralLowerNeighboringBlockConstant_nonneg hα0 hα1)
    (mul_nonneg (by positivity)
      (exceptionalComparableSharpConstant_nonneg α))

theorem hasCentralComparableLatitudeBlockBound_upper
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N) :
    HasCentralComparableLatitudeBlockBound α N
      (centralUpperComparableBlockConstant α) := by
  simpa [centralUpperComparableBlockConstant] using
    centralComparable_upper_block_bound_of_separated
      hα1 hα2 (exceptionalComparableSharpConstant_nonneg α) hM
      (hasCentralComparableSeparatedDssttBound_generic
        (by linarith) hα2 (by omega))

theorem hasCentralComparableLatitudeBlockBound_lower
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 600 ≤ bandCount N) :
    HasCentralComparableLatitudeBlockBound α N
      (centralLowerComparableBlockConstant α) := by
  simpa [centralLowerComparableBlockConstant] using
    centralComparable_lower_block_bound_of_separated
      hα0 hα1 (exceptionalComparableSharpConstant_nonneg α) hM
      (hasCentralComparableSeparatedDssttBound_generic
        hα0 (by linarith) (by omega))

/-- All remaining comparable fields away from the resonant exponent. -/
noncomputable def veryLargeRemainingComparableLatitudeBounds_of_ne_one
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hα1 : α ≠ 1) :
    VeryLargeRemainingComparableLatitudeBounds α := by
  by_cases hlt : α < 1
  · exact
      { Cneighbor := neighboringLowerComparableBlockConstant α
        Ccentral := centralLowerComparableBlockConstant α
        Copposite := smoothOppositeComparableBlockConstant α
        Cneighbor_nonneg :=
          neighboringLowerComparableBlockConstant_nonneg hα0 hlt
        Ccentral_nonneg :=
          centralLowerComparableBlockConstant_nonneg hα0 hlt
        Copposite_nonneg :=
          smoothOppositeComparableBlockConstant_nonneg α
        neighboring := by
          intro N _ hM
          exact hasNeighboringComparableLatitudeBlockBound_lower
            hα0 hlt (by omega)
        central := by
          intro N _ hM
          exact hasCentralComparableLatitudeBlockBound_lower
            hα0 hlt hM
        opposite := by
          intro N _ hM
          exact hasSmoothOppositeComparableLatitudeBlockBound
            hα0 hα2 hM }
  · have hgt : 1 < α :=
      lt_of_le_of_ne (le_of_not_gt hlt) hα1.symm
    exact
      { Cneighbor := neighboringUpperComparableBlockConstant α
        Ccentral := centralUpperComparableBlockConstant α
        Copposite := smoothOppositeComparableBlockConstant α
        Cneighbor_nonneg :=
          neighboringUpperComparableBlockConstant_nonneg hgt
        Ccentral_nonneg :=
          centralUpperComparableBlockConstant_nonneg hgt
        Copposite_nonneg :=
          smoothOppositeComparableBlockConstant_nonneg α
        neighboring := by
          intro N _ hM
          exact hasNeighboringComparableLatitudeBlockBound_upper
            hgt hα2 (by omega)
        central := by
          intro N _ hM
          exact hasCentralComparableLatitudeBlockBound_upper
            hgt hα2 hM
        opposite := by
          intro N _ hM
          exact hasSmoothOppositeComparableLatitudeBlockBound
            hα0 hα2 hM }

/-- Uniform neighboring, central, and opposite bounds for every exponent in
the open Riesz range, including the resonant exponent. -/
noncomputable def veryLargeRemainingComparableLatitudeBounds
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    VeryLargeRemainingComparableLatitudeBounds α := by
  by_cases hα1 : α = 1
  · subst α
    exact
      { Cneighbor := neighboringResonantFullBlockConstant
        Ccentral := centralResonantComparableBlockConstant
        Copposite := smoothOppositeComparableBlockConstant 1
        Cneighbor_nonneg :=
          neighboringResonantFullBlockConstant_nonneg
        Ccentral_nonneg :=
          centralResonantComparableBlockConstant_nonneg
        Copposite_nonneg :=
          smoothOppositeComparableBlockConstant_nonneg 1
        neighboring := by
          intro N _ hM
          exact hasNeighboringComparableLatitudeBlockBound_one
            (by omega)
        central := by
          intro N _ hM
          exact hasCentralComparableLatitudeBlockBound_resonant hM
        opposite := by
          intro N _ hM
          exact hasSmoothOppositeComparableLatitudeBlockBound
            (by norm_num) (by norm_num) hM }
  · exact veryLargeRemainingComparableLatitudeBounds_of_ne_one
      hα0 hα2 hα1

/-- The formerly conditional very-large comparable package is
unconditional throughout `0 < α < 2`. -/
theorem hasVeryLargeComparableLatitudeBlockBound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    HasVeryLargeComparableLatitudeBlockBound α :=
  (veryLargeRemainingComparableLatitudeBounds hα0 hα2).toComparable
    hα0 hα2

/-- Unconditional concrete latitude deficit bound. -/
theorem exists_bemocLatitudeDeficit_concrete_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      |bemocLatitudeDeficit α N| ≤
        C * (N : ℝ) ^ (1 - α / 2) :=
  exists_bemocLatitudeDeficit_concrete_bound_of_comparable
    hα0 hα2
      (hasVeryLargeComparableLatitudeBlockBound hα0 hα2)

end BEMOC
