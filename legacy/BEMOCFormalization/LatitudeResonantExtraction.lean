import BEMOCFormalization.LatitudeCentralNeighboringGapScale

/-!
# Exact extraction of the resonant physical cusp

The identity `r² q(q+2) = (s-t)²` writes the normalized gap as a positive,
smooth variable coefficient times `(s-t)²`.  Applying the already-proved
quadratic resonant identity then separates the physical
`(s-t)² log |s-t|` cusp from a quadratic correction.
-/

open Set

namespace BEMOC

noncomputable def latitudeQuadraticGapCoefficient (s t : ℝ) : ℝ :=
  (((heightRadius s * heightRadius t) ^ 2) *
    (normalizedLatitudeGap s t + 2))⁻¹

theorem latitudeQuadraticGapCoefficient_pos
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 < latitudeQuadraticGapCoefficient s t := by
  have hq : 0 ≤ normalizedLatitudeGap s t := by
    rw [normalizedLatitudeGap_eq hs ht]
    exact div_nonneg (latitudeRadialGapSq_nonneg s t)
      (by unfold latitudeAngularScale; positivity)
  have hrs : 0 < heightRadius s := heightRadius_pos hs
  have hrt : 0 < heightRadius t := heightRadius_pos ht
  have hden :
      0 < (heightRadius s * heightRadius t) ^ 2 *
          (normalizedLatitudeGap s t + 2) := by
    positivity
  unfold latitudeQuadraticGapCoefficient
  exact inv_pos.mpr hden

theorem normalizedLatitudeGap_eq_quadraticCoefficient_mul_sq
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    normalizedLatitudeGap s t =
      latitudeQuadraticGapCoefficient s t * (s - t) ^ 2 := by
  have hq : 0 ≤ normalizedLatitudeGap s t := by
    rw [normalizedLatitudeGap_eq hs ht]
    exact div_nonneg (latitudeRadialGapSq_nonneg s t)
      (by unfold latitudeAngularScale; positivity)
  have hden :
      (heightRadius s * heightRadius t) ^ 2 *
          (normalizedLatitudeGap s t + 2) ≠ 0 := by
    have hrs : 0 < heightRadius s := heightRadius_pos hs
    have hrt : 0 < heightRadius t := heightRadius_pos ht
    positivity
  have hid := normalizedLatitudeGap_mul_add_two hs ht
  unfold latitudeQuadraticGapCoefficient
  rw [inv_mul_eq_div]
  field_simp [hden]
  nlinarith

/-- Exact pointwise extraction of the resonant branch.  The second term is
quadratic in the physical difference; when its displayed coefficient is
frozen, that constant quadratic part is annihilated by the paired
two-moment rule. -/
theorem normalizedGap_mul_log_eq_resonant_extraction
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    normalizedLatitudeGap s t *
        Real.log (normalizedLatitudeGap s t) =
      2 * latitudeQuadraticGapCoefficient s t *
          resonantLatitudeBranch (s - t) +
        latitudeQuadraticGapCoefficient s t *
          Real.log (latitudeQuadraticGapCoefficient s t) *
            (s - t) ^ 2 := by
  let c := latitudeQuadraticGapCoefficient s t
  have hc : 0 < c := latitudeQuadraticGapCoefficient_pos hs ht
  have hq := normalizedLatitudeGap_eq_quadraticCoefficient_mul_sq hs ht
  have hres := quadraticReducedResonantBranch_eq
    (c := c) (w := s - t) hc
  unfold quadraticReducedResonantBranch at hres
  rw [hq]
  dsimp [c] at hres ⊢
  linarith

/-- The principal term of the actual resonant neighboring model, including
its angular prefactor and universal reduced-cusp coefficient. -/
theorem neighboringResonantPrincipal_eq_physical_extraction
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    latitudeAngularScale s t ^ (1 / 2 : ℝ) *
        (reducedCuspResonantPrincipalCoefficient *
          normalizedLatitudeGap s t *
            Real.log (normalizedLatitudeGap s t)) =
      2 * (latitudeAngularScale s t ^ (1 / 2 : ℝ) *
          reducedCuspResonantPrincipalCoefficient *
            latitudeQuadraticGapCoefficient s t) *
          resonantLatitudeBranch (s - t) +
        (latitudeAngularScale s t ^ (1 / 2 : ℝ) *
          reducedCuspResonantPrincipalCoefficient *
            latitudeQuadraticGapCoefficient s t *
              Real.log (latitudeQuadraticGapCoefficient s t)) *
          (s - t) ^ 2 := by
  have hres := normalizedGap_mul_log_eq_resonant_extraction hs ht
  calc
    latitudeAngularScale s t ^ (1 / 2 : ℝ) *
        (reducedCuspResonantPrincipalCoefficient *
          normalizedLatitudeGap s t *
            Real.log (normalizedLatitudeGap s t)) =
      latitudeAngularScale s t ^ (1 / 2 : ℝ) *
        reducedCuspResonantPrincipalCoefficient *
          (normalizedLatitudeGap s t *
            Real.log (normalizedLatitudeGap s t)) := by ring
    _ = _ := by rw [hres]; ring

end BEMOC
