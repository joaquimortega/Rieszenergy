import BEMOCFormalization.LatitudeComparableFourTerm

/-!
# Final separated comparable four-term assembly

This file is intentionally downstream of the frozen sharp power and raw
cusp jets.  It contains the product-jet algebra and the remaining composed
normalized-gap estimates.
-/

open Set

namespace BEMOC

set_option maxHeartbeats 800000

theorem SeparatedScaledAbs.latitudeJetMulD2
    {R d a b C₁ C₂ C₃ a₀ a₁ a₂ b₀ b₁ b₂ : ℝ}
    (h₁ : SeparatedScaledAbs R d a b C₁ (a₂ * b₀))
    (h₂ : SeparatedScaledAbs R d a b C₂ (a₁ * b₁))
    (h₃ : SeparatedScaledAbs R d a b C₃ (a₀ * b₂)) :
    SeparatedScaledAbs R d a b
      (C₁ + 2 * C₂ + C₃)
      (BEMOC.latitudeJetMulD2 a₀ a₁ a₂ b₀ b₁ b₂) := by
  unfold BEMOC.latitudeJetMulD2
  have hh₂ := h₂.const_mul (c := (2 : ℝ))
  convert (h₁.add hh₂).add h₃ using 1 <;> norm_num <;> ring

theorem SeparatedScaledAbs.latitudeJetMul3D2
    {R d a b C₁ C₂ C₃ C₄ C₅ C₆
      a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ : ℝ}
    (h₁ : SeparatedScaledAbs R d a b C₁ (a₂ * b₀ * c₀))
    (h₂ : SeparatedScaledAbs R d a b C₂ (a₀ * b₂ * c₀))
    (h₃ : SeparatedScaledAbs R d a b C₃ (a₀ * b₀ * c₂))
    (h₄ : SeparatedScaledAbs R d a b C₄ (a₁ * b₁ * c₀))
    (h₅ : SeparatedScaledAbs R d a b C₅ (a₁ * b₀ * c₁))
    (h₆ : SeparatedScaledAbs R d a b C₆ (a₀ * b₁ * c₁)) :
    SeparatedScaledAbs R d a b
      (C₁ + C₂ + C₃ + 2 * C₄ + 2 * C₅ + 2 * C₆)
      (BEMOC.latitudeJetMul3D2
        a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂) := by
  unfold BEMOC.latitudeJetMul3D2
  have hh₄ := h₄.const_mul (c := (2 : ℝ))
  have hh₅ := h₅.const_mul (c := (2 : ℝ))
  have hh₆ := h₆.const_mul (c := (2 : ℝ))
  convert (((((h₁.add h₂).add h₃).add hh₄).add hh₅).add hh₆)
    using 1 <;> norm_num <;> ring

/-- The right pure gap derivatives have the same fixed-chart grading as
the left ones, using the same common radius floor. -/
theorem separatedComparableSame_rectangle_rightGapJet
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : SeparatedComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |normalizedLatitudeGapDt s t| ≤
        |s - t| * (comparableLatitudeRadiusFloor N j)⁻¹ ^ 4 ∧
    |normalizedLatitudeGapDtt s t| ≤
        (1600 + 3 * 3200) *
          (comparableLatitudeRadiusFloor N j)⁻¹ ^ 4 := by
  let R := comparableLatitudeRadiusFloor N j
  have hrect :=
    separatedComparableSame_rectangle_interior_offDiagonal hM hjk hs ht
  have hgeom := comparableSame_rectangle_geometry hM hjk.1 hs ht
  have hupper :=
    comparableSame_rectangle_common_radius_ceiling hM hjk.1 hs ht
  have hgap :=
    comparableSame_rectangle_normalizedLatitudeGap_le hM hjk.1 hs ht
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hdr : (0 : ℝ) < latitudeBandScale N j := by
      exact_mod_cast latitudeBandScale_pos N j
    positivity
  have hsep : |t - s| ≤ 3200 * R ^ 2 := by
    rw [abs_sub_comm]
    simpa [R] using
      (comparableSame_rectangle_abs_sub_le_radiusFloor_sq
        hM hjk.1 hs ht)
  have hswap := latitudeComparableGradedGapBound
    ⟨hrect.2.1.1.le, hrect.2.1.2.le⟩
    ⟨hrect.1.1.le, hrect.1.2.le⟩ hR
    (by norm_num : (0 : ℝ) ≤ 3200)
    hgeom.1.2 hgeom.1.1 hupper.2 hupper.1 hsep
    (by simpa [normalizedLatitudeGap_comm] using hgap)
  rcases hswap with ⟨hDt, _, hDtt, _⟩
  unfold normalizedLatitudeGapDt normalizedLatitudeGapDtt
  constructor
  · simpa [R, abs_sub_comm] using hDt
  · simpa [R] using hDtt

end BEMOC
