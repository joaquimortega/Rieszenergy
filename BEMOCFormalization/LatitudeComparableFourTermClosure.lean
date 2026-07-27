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

/-- A one-variable radius grading is the special case with zero separation
degree.  This bridge lets the frozen power jet participate in the
two-variable separated product calculus. -/
theorem ScaledAbs.toSeparated
    {R d a C x : ℝ} (h : ScaledAbs R a C x) :
    SeparatedScaledAbs R d a 0 C x := by
  unfold ScaledAbs at h
  unfold SeparatedScaledAbs
  simpa using h

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

/-- The first top-level Leibniz block has the sharp separated scale.  The
four expanded products use respectively the homogeneity shifts
`3-α`, `2`, `2`, and `1`. -/
theorem separatedComparableSame_rectangle_firstMixedBlock
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : SeparatedComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    ∃ C : ℝ, 0 ≤ C ∧
      |latitudeJetMulD2
          (latitudePowerDss α s t) (latitudePowerDsst α s t)
            (latitudePowerDsstt α s t)
          (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
            (latitudeCusp0Dtt α s t)| ≤
        C * latitudePowerDerivativeScale α
          (comparableLatitudeRadiusFloor N j) |s - t| := by
  let R := comparableLatitudeRadiusFloor N j
  let d := |s - t|
  let P := latitudeComparablePowerJetConstant α
  let H := latitudeComparableRawCuspSeparatedConstant α
  let K : ℝ := 3200
  let Q : ℝ := 1600 + 3 * 3200
  have hrect :=
    separatedComparableSame_rectangle_interior_offDiagonal hM hjk hs ht
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hdr : (0 : ℝ) < latitudeBandScale N j := by
      exact_mod_cast latitudeBandScale_pos N j
    positivity
  have hd : 0 < d := by
    dsimp [d]
    exact abs_pos.mpr (sub_ne_zero.mpr hrect.2.2)
  have hsep : d ≤ K * R ^ 2 := by
    dsimp [d, K, R]
    exact comparableSame_rectangle_abs_sub_le_radiusFloor_sq
      hM hjk.1 hs ht
  have hP0 : 0 ≤ P := by
    dsimp [P, latitudeComparablePowerJetConstant,
      latitudePowerCoefficientEnvelope,
      latitudeComparablePowerRpowConstant]
    positivity
  have hH0 : 0 ≤ H := by
    dsimp [H, latitudeComparableRawCuspSeparatedConstant,
      latitudeComparableCuspDerivativeConstant]
    positivity
  have hK0 : 0 ≤ K := by norm_num [K]
  have hQ0 : 0 ≤ Q := by norm_num [Q]
  rcases comparableSame_rectangle_powerJetGradedBound
      hα0 hα2 hM hjk.1 hs ht with
    ⟨_, _hp0, _hps, _hpt, hpss, _hpst, _hptt,
      hpsst, _hpstt, hpsstt⟩
  rcases separatedComparableSame_rectangle_rawCuspSeparatedBound
      hα0 hα2 hM hjk hs ht with
    ⟨hh0, hh1, hh2, _hh3, _hh4⟩
  rcases separatedComparableSame_rectangle_rightGapJet hM hjk hs ht with
    ⟨hqtRaw, hqttRaw⟩
  have hpss' :
      SeparatedScaledAbs R d (α - 4) 0 P
        (latitudePowerDss α s t) := hpss.toSeparated
  have hpsst' :
      SeparatedScaledAbs R d (α - 6) 0 P
        (latitudePowerDsst α s t) := hpsst.toSeparated
  have hpsstt' :
      SeparatedScaledAbs R d (α - 8) 0 P
        (latitudePowerDsstt α s t) := hpsstt.toSeparated
  have hqt :
      SeparatedScaledAbs R d (-4) 1 1
        (normalizedLatitudeGapDt s t) := by
    unfold SeparatedScaledAbs
    dsimp [R, d] at hqtRaw ⊢
    rw [Real.rpow_one]
    have hpow :
        (comparableLatitudeRadiusFloor N j)⁻¹ ^ 4 =
          (comparableLatitudeRadiusFloor N j) ^ (-4 : ℝ) := by
      symm
      rw [Real.rpow_neg hR.le]
      simpa only [R, inv_pow] using congrArg Inv.inv
        (Real.rpow_natCast (comparableLatitudeRadiusFloor N j) 4)
    rw [hpow] at hqtRaw
    nlinarith [Real.rpow_nonneg hR.le (-4 : ℝ)]
  have hqtt :
      SeparatedScaledAbs R d (-4) 0 Q
        (normalizedLatitudeGapDtt s t) := by
    unfold SeparatedScaledAbs
    dsimp [R, d, Q] at hqttRaw ⊢
    have hpow :
        (comparableLatitudeRadiusFloor N j)⁻¹ ^ 4 =
          (comparableLatitudeRadiusFloor N j) ^ (-4 : ℝ) := by
      symm
      rw [Real.rpow_neg hR.le]
      simpa only [R, inv_pow] using congrArg Inv.inv
        (Real.rpow_natCast (comparableLatitudeRadiusFloor N j) 4)
    rw [hpow] at hqttRaw
    simpa using hqttRaw
  have hqt2 :
      SeparatedScaledAbs R d (-8) 2 1
        (normalizedLatitudeGapDt s t ^ 2) := by
    have hm := hqt.mul hR hd hqt (by norm_num) (by norm_num)
    convert hm using 1 <;> norm_num <;> ring
  have hc0 :
      SeparatedScaledAbs R d 0 0 H
        (latitudeCusp0 α s t) := by
    unfold latitudeCusp0
    exact hh0
  have hc0t :
      SeparatedScaledAbs R d (-2 * α) (α - 1) H
        (latitudeCusp0Dt α s t) := by
    unfold latitudeCusp0Dt
    have hm := hh1.mul hR hd hqt hH0 (by norm_num)
    convert hm using 1 <;> ring
  have hc0ttA :
      SeparatedScaledAbs R d (-2 - 2 * α) (α - 1) H
        (reducedLatitudeCuspD2Value α
          (normalizedLatitudeGap s t) *
            normalizedLatitudeGapDt s t ^ 2) := by
    have hm := hh2.mul hR hd hqt2 hH0 (by norm_num)
    convert hm using 1 <;> ring
  have hc0ttB :
      SeparatedScaledAbs R d (-2 * α) (α - 2) (H * Q)
        (reducedLatitudeCuspD1Value α
          (normalizedLatitudeGap s t) *
            normalizedLatitudeGapDtt s t) := by
    have hm := hh1.mul hR hd hqtt hH0 hQ0
    convert hm using 1 <;> ring
  have hz1raw := hpsstt'.mul hR hd hc0 hP0 hH0
  have hz1 := hz1raw.shift hR hd hK0
    (by linarith : 0 ≤ 3 - α) hsep
    (mul_nonneg hP0 hH0)
  have hz1' :
      SeparatedScaledAbs R d (-2 - α) (α - 3)
        (P * H * K ^ (3 - α))
        (latitudePowerDsstt α s t * latitudeCusp0 α s t) := by
    convert hz1 using 1 <;> ring
  have hz2raw := hpsst'.mul hR hd hc0t hP0 hH0
  have hz2 := hz2raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 2) hsep
    (mul_nonneg hP0 hH0)
  have hz2' :
      SeparatedScaledAbs R d (-2 - α) (α - 3)
        (P * H * K ^ (2 : ℝ))
        (latitudePowerDsst α s t * latitudeCusp0Dt α s t) := by
    convert hz2 using 1 <;> ring
  have hz3Araw := hpss'.mul hR hd hc0ttA hP0 hH0
  have hz3A := hz3Araw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 2) hsep
    (mul_nonneg hP0 hH0)
  have hz3A' :
      SeparatedScaledAbs R d (-2 - α) (α - 3)
        (P * H * K ^ (2 : ℝ))
        (latitudePowerDss α s t *
          (reducedLatitudeCuspD2Value α
            (normalizedLatitudeGap s t) *
              normalizedLatitudeGapDt s t ^ 2)) := by
    convert hz3A using 1 <;> ring
  have hz3Braw := hpss'.mul hR hd hc0ttB hP0
    (mul_nonneg hH0 hQ0)
  have hz3B := hz3Braw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep
    (mul_nonneg hP0 (mul_nonneg hH0 hQ0))
  have hz3B' :
      SeparatedScaledAbs R d (-2 - α) (α - 3)
        (P * (H * Q) * K ^ (1 : ℝ))
        (latitudePowerDss α s t *
          (reducedLatitudeCuspD1Value α
            (normalizedLatitudeGap s t) *
              normalizedLatitudeGapDtt s t)) := by
    convert hz3B using 1 <;> ring
  have hz3 :
      SeparatedScaledAbs R d (-2 - α) (α - 3)
        (P * H * K ^ (2 : ℝ) +
          P * (H * Q) * K ^ (1 : ℝ))
        (latitudePowerDss α s t * latitudeCusp0Dtt α s t) := by
    unfold latitudeCusp0Dtt
    convert hz3A'.add hz3B' using 1 <;> ring
  let C : ℝ :=
    P * H * K ^ (3 - α) +
      2 * (P * H * K ^ (2 : ℝ)) +
      (P * H * K ^ (2 : ℝ) +
        P * (H * Q) * K ^ (1 : ℝ))
  have hblock :
      SeparatedScaledAbs R d (-2 - α) (α - 3) C
        (latitudeJetMulD2
          (latitudePowerDss α s t) (latitudePowerDsst α s t)
            (latitudePowerDsstt α s t)
          (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
            (latitudeCusp0Dtt α s t)) := by
    dsimp [C]
    exact SeparatedScaledAbs.latitudeJetMulD2 hz1' hz2' hz3
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  unfold SeparatedScaledAbs at hblock
  unfold latitudePowerDerivativeScale
  simpa [R, d, mul_assoc] using hblock

end BEMOC
