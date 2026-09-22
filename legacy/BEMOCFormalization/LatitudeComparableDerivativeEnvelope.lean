import BEMOCFormalization.LatitudeComparableRadiusBounds
import BEMOCFormalization.LatitudePowerJetBounds

/-!
# Explicit mixed-derivative envelope on literal comparable bands

This module inserts the concrete BEMOC radius floor into the complete
mixed `(2,2)` derivative chain.  The result has no analytic premise: every
quantity in the majorant is an explicit function of the point, exponent,
and band scale.  The subsequent sharp step is purely quantitative
simplification of this envelope to the power law in (5.5).
-/

open Set

namespace BEMOC

noncomputable def comparableLatitudeRadiusFloor
    (N : ℕ) (j : Fin (bandTailCount N + 1)) : ℝ :=
  (latitudeBandScale N j : ℝ) / (10 * (bandCount N : ℝ))

noncomputable def variableLatitudeMixedExplicitEnvelope
    (α s t R : ℝ) : ℝ :=
  4 *
      (15 * latitudePowerCoefficientEnvelope α *
        latitudePowerRpowEnvelope α s t *
        latitudeAngularDerivativeJetEnvelope s t ^ 4) *
      (2 * latitudeCuspValueEnvelope α (normalizedLatitudeGap s t) *
        latitudeGapRadiusEnvelope R ^ 2) +
    36 *
      (15 * latitudePowerCoefficientEnvelope α *
        latitudePowerRpowEnvelope α s t *
        latitudeAngularDerivativeJetEnvelope s t ^ 4) *
      (2 * latitudeCuspValueEnvelope α (normalizedLatitudeGap s t) *
        latitudeGapRadiusEnvelope R ^ 2) *
      (4 * latitudeGapRadiusEnvelope R ^ 2)

theorem mem_Ioo_of_mem_Icc_heightRadius_pos
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (hr : 0 < heightRadius s) :
    s ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · by_contra h
    have hse : s = -1 := by linarith [hs.1]
    subst s
    norm_num [heightRadius] at hr
  · by_contra h
    have hse : s = 1 := by linarith [hs.2]
    subst s
    norm_num [heightRadius] at hr

/-- The actual mixed derivative on every off-diagonal point of a classified
comparable same-hemisphere band rectangle is bounded by the completely
explicit envelope with the literal BEMOC radius floor. -/
theorem comparableSame_rectangle_variableMixedDerivative_le_explicitEnvelope
    {α : ℝ} (hα : α ≤ 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : ComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hst : s ≠ t) :
    |variableReducedLatitudeKernelDsstt α s t| ≤
      variableLatitudeMixedExplicitEnvelope α s t
        (comparableLatitudeRadiusFloor N j) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hfloor := (comparableSame_rectangle_geometry hM hjk hs ht).1
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hdreal : (0 : ℝ) < latitudeBandScale N j := by
    exact_mod_cast latitudeBandScale_pos N j
  have hR :
      0 < comparableLatitudeRadiusFloor N j := by
    unfold comparableLatitudeRadiusFloor
    positivity
  have hspos : 0 < heightRadius s := hR.trans_le hfloor.1
  have htpos : 0 < heightRadius t := hR.trans_le hfloor.2
  have hsInterior := mem_Ioo_of_mem_Icc_heightRadius_pos hsSphere hspos
  have htInterior := mem_Ioo_of_mem_Icc_heightRadius_pos htSphere htpos
  exact abs_variableReducedLatitudeKernelDsstt_le_explicitEnvelope
    hsInterior htInterior hst hα hR hfloor.1 hfloor.2

end BEMOC
