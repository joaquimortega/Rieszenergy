import BEMOCFormalization.ConcreteWithinRing
import BEMOCFormalization.CrossRingEstimate
import BEMOCFormalization.LatitudeUnconditionalComparableClosure

/-!
# Assembly of the concrete BEMOC upper bound

This module contains the purely logical last step of the upper-bound proof.
Once the latitude deficit is controlled at the target scale, the already
proved within-ring and cross-ring estimates give a common component bound,
and conditional negative definiteness supplies nonnegativity.
-/

namespace BEMOC

/-- Combine a concrete latitude estimate with the unconditional within-ring
and cross-ring estimates.  All three estimates use the same threshold `36`,
so their constants can be combined by addition without any maximum
bookkeeping. -/
theorem exists_bemocComponentBounds_of_latitude
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hlatitude :
      ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
        |bemocLatitudeDeficit α N| ≤
          C * (N : ℝ) ^ (1 - α / 2)) :
    Nonempty (BemocComponentBounds α) := by
  obtain ⟨Clat, hClat, hlat⟩ := hlatitude
  obtain ⟨Cwithin, hCwithin, hwithin⟩ :=
    exists_bemocWithinRingDeficit_concrete_bound hα0 hα2
  obtain ⟨Ccross, hCcross, hcross⟩ :=
    exists_bemocCrossRingDeficit_concrete_bound hα0 hα2
  let C := Clat + Cwithin + Ccross
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨
    { C := C
      C_pos := hC
      N₀ := 36
      latitude := ?_
      withinRing := ?_
      crossRing := ?_ }⟩
  · intro N hN
    exact (hlat N hN).trans <|
      mul_le_mul_of_nonneg_right
        (show Clat ≤ C by
          dsimp [C]
          linarith [hCwithin, hCcross])
        (by positivity)
  · intro N hN
    exact (hwithin N hN).trans <|
      mul_le_mul_of_nonneg_right
        (show Cwithin ≤ C by
          dsimp [C]
          linarith [hClat, hCcross])
        (by positivity)
  · intro N hN
    exact (hcross N hN).trans <|
      mul_le_mul_of_nonneg_right
        (show Ccross ≤ C by
          dsimp [C]
          linarith [hClat, hCwithin])
        (by positivity)

/-- The final nonnegative upper estimate follows from the latitude estimate
alone, since the other two analytic components are already unconditional. -/
theorem bemoc_deficit_bound_of_latitude
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hlatitude :
      ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
        |bemocLatitudeDeficit α N| ≤
          C * (N : ℝ) ^ (1 - α / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      0 ≤ continuousEnergy α * (N : ℝ) ^ 2 -
          bemocFiniteEnergy α N ∧
        continuousEnergy α * (N : ℝ) ^ 2 -
          bemocFiniteEnergy α N ≤
            C * (N : ℝ) ^ (1 - α / 2) := by
  obtain ⟨hcomponents⟩ :=
    exists_bemocComponentBounds_of_latitude hα0 hα2 hlatitude
  simpa [bemocEnergyDeficit] using
    bemoc_deficit_bound_of_component_bounds hα0 hα2 hcomponents

/-- The complete BEMOC upper estimate reduced only to the uniform
very-large comparable-scale latitude package.  Unequal scales, finite
fallback, within-ring energy, cross-ring energy, and nonnegativity are all
discharged internally. -/
theorem bemoc_deficit_bound_of_comparable
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hcomp : HasVeryLargeComparableLatitudeBlockBound α) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      0 ≤ continuousEnergy α * (N : ℝ) ^ 2 -
          bemocFiniteEnergy α N ∧
        continuousEnergy α * (N : ℝ) ^ 2 -
          bemocFiniteEnergy α N ≤
            C * (N : ℝ) ^ (1 - α / 2) :=
  bemoc_deficit_bound_of_latitude hα0 hα2
    (exists_bemocLatitudeDeficit_concrete_bound_of_comparable
      hα0 hα2 hcomp)

/-- All three analytic component bounds are unconditional in the full open
Riesz range. -/
theorem exists_bemocComponentBounds
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Nonempty (BemocComponentBounds α) :=
  exists_bemocComponentBounds_of_latitude hα0 hα2
    (exists_bemocLatitudeDeficit_concrete_bound hα0 hα2)

/-- Unconditional formalization of the BEMOC upper energy bound. -/
theorem bemoc_deficit_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      0 ≤ continuousEnergy α * (N : ℝ) ^ 2 -
          bemocFiniteEnergy α N ∧
        continuousEnergy α * (N : ℝ) ^ 2 -
          bemocFiniteEnergy α N ≤
            C * (N : ℝ) ^ (1 - α / 2) :=
  bemoc_deficit_bound_of_latitude hα0 hα2
    (exists_bemocLatitudeDeficit_concrete_bound hα0 hα2)

end BEMOC
