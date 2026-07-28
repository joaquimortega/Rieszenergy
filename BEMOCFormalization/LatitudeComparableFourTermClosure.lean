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

noncomputable def latitudeComparableFirstMixedConstant (α : ℝ) : ℝ :=
  let P := latitudeComparablePowerJetConstant α
  let H := latitudeComparableRawCuspSeparatedConstant α
  let K : ℝ := 3200
  let Q : ℝ := 1600 + 3 * 3200
  P * H * K ^ (3 - α) +
    2 * (P * H * K ^ (2 : ℝ)) +
    (P * H * K ^ (2 : ℝ) +
      P * (H * Q) * K)

theorem latitudeComparableFirstMixedConstant_nonneg (α : ℝ) :
    0 ≤ latitudeComparableFirstMixedConstant α := by
  unfold latitudeComparableFirstMixedConstant
    latitudeComparablePowerJetConstant
    latitudePowerCoefficientEnvelope
    latitudeComparablePowerRpowConstant
    latitudeComparableRawCuspSeparatedConstant
    latitudeComparableCuspDerivativeConstant
  positivity

private theorem inv_pow_eq_rpow_neg_nat {R : ℝ} (hR : 0 < R) (n : ℕ) :
    R⁻¹ ^ n = R ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg hR.le]
  simpa only [inv_pow] using
    congrArg Inv.inv (Real.rpow_natCast R n).symm

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
    |latitudeJetMulD2
        (latitudePowerDss α s t) (latitudePowerDsst α s t)
          (latitudePowerDsstt α s t)
        (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
          (latitudeCusp0Dtt α s t)| ≤
      latitudeComparableFirstMixedConstant α *
        latitudePowerDerivativeScale α
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
  unfold SeparatedScaledAbs at hblock
  unfold latitudePowerDerivativeScale
  simpa [R, d, C, P, H, K, Q,
    latitudeComparableFirstMixedConstant, mul_assoc] using hblock

noncomputable def latitudeComparableSecondMixedConstant (α : ℝ) : ℝ :=
  let P := latitudeComparablePowerJetConstant α
  let H := latitudeComparableRawCuspSeparatedConstant α
  let K : ℝ := 3200
  let Q : ℝ := 1600 + 3 * 3200
  let G₁ : ℝ := 5121600
  let G₂ : ℝ := 15364801
  P * H * K ^ (2 : ℝ) +
    P * (H + H * Q) * K +
    P * (H * G₂) * K +
    2 * (P * H * K ^ (2 : ℝ)) +
    2 * (P * (H * G₁) * K) +
    2 * (P * (H * G₁) * K)

theorem latitudeComparableSecondMixedConstant_nonneg (α : ℝ) :
    0 ≤ latitudeComparableSecondMixedConstant α := by
  unfold latitudeComparableSecondMixedConstant
    latitudeComparablePowerJetConstant
    latitudePowerCoefficientEnvelope
    latitudeComparablePowerRpowConstant
    latitudeComparableRawCuspSeparatedConstant
    latitudeComparableCuspDerivativeConstant
  positivity

/-- The second top-level Leibniz block, containing one left gap derivative,
has the same sharp physical scale. -/
theorem separatedComparableSame_rectangle_secondMixedBlock
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : SeparatedComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |latitudeJetMul3D2
        (latitudePowerDs α s t) (latitudePowerDst α s t)
          (latitudePowerDstt α s t)
        (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
        (normalizedLatitudeGapDs s t) (normalizedLatitudeGapDst s t)
          (normalizedLatitudeGapDstt s t)| ≤
      latitudeComparableSecondMixedConstant α *
        latitudePowerDerivativeScale α
          (comparableLatitudeRadiusFloor N j) |s - t| := by
  let R := comparableLatitudeRadiusFloor N j
  let d := |s - t|
  let P := latitudeComparablePowerJetConstant α
  let H := latitudeComparableRawCuspSeparatedConstant α
  let K : ℝ := 3200
  let Q : ℝ := 1600 + 3 * 3200
  let G₁ : ℝ := 5121600
  let G₂ : ℝ := 15364801
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
  have hG₁0 : 0 ≤ G₁ := by norm_num [G₁]
  have hG₂0 : 0 ≤ G₂ := by norm_num [G₂]
  rcases comparableSame_rectangle_powerJetGradedBound
      hα0 hα2 hM hjk.1 hs ht with
    ⟨_, _hp0, hps, _hpt, _hpss, hpst, _hptt,
      _hpsst, hpstt, _hpsstt⟩
  rcases separatedComparableSame_rectangle_rawCuspSeparatedBound
      hα0 hα2 hM hjk hs ht with
    ⟨_hh0, hh1, hh2, hh3, _hh4⟩
  have hgap :=
    comparableSame_rectangle_normalizedLatitudeGap_le hM hjk.1 hs ht
  rcases comparableSame_rectangle_gradedGapBound
      hM hjk.1 hs ht hgap with
    ⟨hqsRaw, hqstRaw, _hqssRaw, _hqsstRaw, hqsttRaw, _hqssttRaw⟩
  rcases separatedComparableSame_rectangle_rightGapJet hM hjk hs ht with
    ⟨hqtRaw, hqttRaw⟩
  have hps' :
      SeparatedScaledAbs R d (α - 2) 0 P
        (latitudePowerDs α s t) := hps.toSeparated
  have hpst' :
      SeparatedScaledAbs R d (α - 4) 0 P
        (latitudePowerDst α s t) := hpst.toSeparated
  have hpstt' :
      SeparatedScaledAbs R d (α - 6) 0 P
        (latitudePowerDstt α s t) := hpstt.toSeparated
  have hqs :
      SeparatedScaledAbs R d (-4) 1 1
        (normalizedLatitudeGapDs s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDs s t| ≤ d * R⁻¹ ^ 4 at hqsRaw
    dsimp [d] at hqsRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 4] at hqsRaw
    simpa [mul_assoc, mul_comm] using hqsRaw
  have hqt :
      SeparatedScaledAbs R d (-4) 1 1
        (normalizedLatitudeGapDt s t) := by
    unfold SeparatedScaledAbs
    dsimp [R, d] at hqtRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 4] at hqtRaw
    simpa [mul_assoc, mul_comm] using hqtRaw
  have hqst :
      SeparatedScaledAbs R d (-4) 0 G₁
        (normalizedLatitudeGapDst s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDst s t| ≤ G₁ * R⁻¹ ^ 4 at hqstRaw
    dsimp [d, G₁] at hqstRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 4] at hqstRaw
    simpa using hqstRaw
  have hqstt :
      SeparatedScaledAbs R d (-6) 0 G₂
        (normalizedLatitudeGapDstt s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDstt s t| ≤ G₂ * R⁻¹ ^ 6 at hqsttRaw
    dsimp [d, G₂] at hqsttRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 6] at hqsttRaw
    simpa using hqsttRaw
  have hqtt :
      SeparatedScaledAbs R d (-4) 0 Q
        (normalizedLatitudeGapDtt s t) := by
    unfold SeparatedScaledAbs
    dsimp [R, d, Q] at hqttRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 4] at hqttRaw
    simpa using hqttRaw
  have hqt2 :
      SeparatedScaledAbs R d (-8) 2 1
        (normalizedLatitudeGapDt s t ^ 2) := by
    have hm := hqt.mul hR hd hqt (by norm_num) (by norm_num)
    convert hm using 1 <;> norm_num <;> ring
  have hc1 :
      SeparatedScaledAbs R d (4 - 2 * α) (α - 2) H
        (latitudeCusp1 α s t) := by
    unfold latitudeCusp1
    exact hh1
  have hc1t :
      SeparatedScaledAbs R d (2 - 2 * α) (α - 2) H
        (latitudeCusp1Dt α s t) := by
    unfold latitudeCusp1Dt
    have hm := hh2.mul hR hd hqt hH0 (by norm_num)
    convert hm using 1 <;> ring
  have hc1ttA :
      SeparatedScaledAbs R d (2 - 2 * α) (α - 3) H
        (reducedLatitudeCuspD3Value α
          (normalizedLatitudeGap s t) *
            normalizedLatitudeGapDt s t ^ 2) := by
    have hm := hh3.mul hR hd hqt2 hH0 (by norm_num)
    convert hm using 1 <;> ring
  have hc1ttB :
      SeparatedScaledAbs R d (2 - 2 * α) (α - 3) (H * Q)
        (reducedLatitudeCuspD2Value α
          (normalizedLatitudeGap s t) *
            normalizedLatitudeGapDtt s t) := by
    have hm := hh2.mul hR hd hqtt hH0 hQ0
    convert hm using 1 <;> ring
  have hc1tt :
      SeparatedScaledAbs R d (2 - 2 * α) (α - 3)
        (H + H * Q) (latitudeCusp1Dtt α s t) := by
    unfold latitudeCusp1Dtt
    exact hc1ttA.add hc1ttB
  have hz1raw := (hpstt'.mul hR hd hc1 hP0 hH0).mul
    hR hd hqs (mul_nonneg hP0 hH0) (by norm_num)
  have hz1 := hz1raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 2) hsep
    (by positivity)
  have hz1' :
      SeparatedScaledAbs R d (-2 - α) (α - 3)
        (P * H * K ^ (2 : ℝ))
        (latitudePowerDstt α s t * latitudeCusp1 α s t *
          normalizedLatitudeGapDs s t) := by
    convert hz1 using 1 <;> ring
  have hz2raw := (hps'.mul hR hd hc1tt hP0
    (add_nonneg hH0 (mul_nonneg hH0 hQ0))).mul
      hR hd hqs (by positivity) (by norm_num)
  have hz2 := hz2raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep (by positivity)
  have hz2' :
      SeparatedScaledAbs R d (-2 - α) (α - 3)
        (P * (H + H * Q) * K)
        (latitudePowerDs α s t * latitudeCusp1Dtt α s t *
          normalizedLatitudeGapDs s t) := by
    convert hz2 using 1 <;> ring
  have hz3raw := (hps'.mul hR hd hc1 hP0 hH0).mul
    hR hd hqstt (mul_nonneg hP0 hH0) hG₂0
  have hz3 := hz3raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep (by positivity)
  have hz3' :
      SeparatedScaledAbs R d (-2 - α) (α - 3)
        (P * (H * G₂) * K)
        (latitudePowerDs α s t * latitudeCusp1 α s t *
          normalizedLatitudeGapDstt s t) := by
    convert hz3 using 1 <;> ring
  have hz4raw := (hpst'.mul hR hd hc1t hP0 hH0).mul
    hR hd hqs (mul_nonneg hP0 hH0) (by norm_num)
  have hz4 := hz4raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 2) hsep (by positivity)
  have hz4' :
      SeparatedScaledAbs R d (-2 - α) (α - 3)
        (P * (H * 1) * K ^ (2 : ℝ))
        (latitudePowerDst α s t * latitudeCusp1Dt α s t *
          normalizedLatitudeGapDs s t) := by
    convert hz4 using 1 <;> ring
  have hz5raw := (hpst'.mul hR hd hc1 hP0 hH0).mul
    hR hd hqst (mul_nonneg hP0 hH0) hG₁0
  have hz5 := hz5raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep (by positivity)
  have hz5' :
      SeparatedScaledAbs R d (-2 - α) (α - 3)
        (P * (H * G₁) * K)
        (latitudePowerDst α s t * latitudeCusp1 α s t *
          normalizedLatitudeGapDst s t) := by
    convert hz5 using 1 <;> ring
  have hz6raw := (hps'.mul hR hd hc1t hP0 hH0).mul
    hR hd hqst (mul_nonneg hP0 hH0) hG₁0
  have hz6 := hz6raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep (by positivity)
  have hz6' :
      SeparatedScaledAbs R d (-2 - α) (α - 3)
        (P * (H * G₁) * K)
        (latitudePowerDs α s t * latitudeCusp1Dt α s t *
          normalizedLatitudeGapDst s t) := by
    convert hz6 using 1 <;> ring
  have hblock :=
    SeparatedScaledAbs.latitudeJetMul3D2
      hz1' hz2' hz3' hz4' hz5' hz6'
  unfold SeparatedScaledAbs at hblock
  unfold latitudePowerDerivativeScale
  simpa [R, d, P, H, K, Q, G₁, G₂,
    latitudeComparableSecondMixedConstant, mul_assoc] using hblock

noncomputable def latitudeComparableThirdMixedConstant (α : ℝ) : ℝ :=
  let P := latitudeComparablePowerJetConstant α
  let H := latitudeComparableRawCuspSeparatedConstant α
  let K : ℝ := 3200
  let Q : ℝ := 1600 + 3 * 3200
  let G₁ : ℝ := 5121600
  let G₂ : ℝ := 15364801
  let Gsq : ℝ := 2 * G₁ ^ 2 + 2 * G₂ * K
  P * H * K ^ (2 : ℝ) +
    P * (H + H * Q) +
    P * (H * Gsq) +
    2 * (P * H * K) +
    2 * (P * (H * (2 * G₁)) * K) +
    2 * (P * (H * (2 * G₁)))

theorem latitudeComparableThirdMixedConstant_nonneg (α : ℝ) :
    0 ≤ latitudeComparableThirdMixedConstant α := by
  unfold latitudeComparableThirdMixedConstant
    latitudeComparablePowerJetConstant
    latitudePowerCoefficientEnvelope
    latitudeComparablePowerRpowConstant
    latitudeComparableRawCuspSeparatedConstant
    latitudeComparableCuspDerivativeConstant
  positivity

/-- The third top-level block contains the square of the first gap
derivative.  Keeping that square graded avoids the loss from a common jet
envelope. -/
theorem separatedComparableSame_rectangle_thirdMixedBlock
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : SeparatedComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |latitudeJetMul3D2
        (latitudePower α s t) (latitudePowerDt α s t)
          (latitudePowerDtt α s t)
        (latitudeCusp2 α s t) (latitudeCusp2Dt α s t)
          (latitudeCusp2Dtt α s t)
        (normalizedLatitudeGapDs s t ^ 2)
          (2 * normalizedLatitudeGapDs s t *
            normalizedLatitudeGapDst s t)
          (2 * normalizedLatitudeGapDst s t ^ 2 +
            2 * normalizedLatitudeGapDs s t *
              normalizedLatitudeGapDstt s t)| ≤
      latitudeComparableThirdMixedConstant α *
        latitudePowerDerivativeScale α
          (comparableLatitudeRadiusFloor N j) |s - t| := by
  let R := comparableLatitudeRadiusFloor N j
  let d := |s - t|
  let P := latitudeComparablePowerJetConstant α
  let H := latitudeComparableRawCuspSeparatedConstant α
  let K : ℝ := 3200
  let Q : ℝ := 1600 + 3 * 3200
  let G₁ : ℝ := 5121600
  let G₂ : ℝ := 15364801
  let Gsq : ℝ := 2 * G₁ ^ 2 + 2 * G₂ * K
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
  have hG₁0 : 0 ≤ G₁ := by norm_num [G₁]
  have hG₂0 : 0 ≤ G₂ := by norm_num [G₂]
  have hGsq0 : 0 ≤ Gsq := by dsimp [Gsq]; positivity
  rcases comparableSame_rectangle_powerJetGradedBound
      hα0 hα2 hM hjk.1 hs ht with
    ⟨_, hp, _hps, hpt, _hpss, _hpst, hptt,
      _hpsst, _hpstt, _hpsstt⟩
  rcases separatedComparableSame_rectangle_rawCuspSeparatedBound
      hα0 hα2 hM hjk hs ht with
    ⟨_hh0, _hh1, hh2, hh3, hh4⟩
  have hgap :=
    comparableSame_rectangle_normalizedLatitudeGap_le hM hjk.1 hs ht
  rcases comparableSame_rectangle_gradedGapBound
      hM hjk.1 hs ht hgap with
    ⟨hqsRaw, hqstRaw, _hqssRaw, _hqsstRaw, hqsttRaw, _hqssttRaw⟩
  rcases separatedComparableSame_rectangle_rightGapJet hM hjk hs ht with
    ⟨hqtRaw, hqttRaw⟩
  have hp' : SeparatedScaledAbs R d α 0 P
      (latitudePower α s t) := hp.toSeparated
  have hpt' : SeparatedScaledAbs R d (α - 2) 0 P
      (latitudePowerDt α s t) := hpt.toSeparated
  have hptt' : SeparatedScaledAbs R d (α - 4) 0 P
      (latitudePowerDtt α s t) := hptt.toSeparated
  have hqs : SeparatedScaledAbs R d (-4) 1 1
      (normalizedLatitudeGapDs s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDs s t| ≤ d * R⁻¹ ^ 4 at hqsRaw
    dsimp [d] at hqsRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 4] at hqsRaw
    simpa [mul_assoc, mul_comm] using hqsRaw
  have hqt : SeparatedScaledAbs R d (-4) 1 1
      (normalizedLatitudeGapDt s t) := by
    unfold SeparatedScaledAbs
    dsimp [R, d] at hqtRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 4] at hqtRaw
    simpa [mul_assoc, mul_comm] using hqtRaw
  have hqst : SeparatedScaledAbs R d (-4) 0 G₁
      (normalizedLatitudeGapDst s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDst s t| ≤ G₁ * R⁻¹ ^ 4 at hqstRaw
    dsimp [d, G₁] at hqstRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 4] at hqstRaw
    simpa using hqstRaw
  have hqstt : SeparatedScaledAbs R d (-6) 0 G₂
      (normalizedLatitudeGapDstt s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDstt s t| ≤ G₂ * R⁻¹ ^ 6 at hqsttRaw
    dsimp [d, G₂] at hqsttRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 6] at hqsttRaw
    simpa using hqsttRaw
  have hqtt : SeparatedScaledAbs R d (-4) 0 Q
      (normalizedLatitudeGapDtt s t) := by
    unfold SeparatedScaledAbs
    dsimp [R, d, Q] at hqttRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 4] at hqttRaw
    simpa using hqttRaw
  have hqs2 : SeparatedScaledAbs R d (-8) 2 1
      (normalizedLatitudeGapDs s t ^ 2) := by
    have hm := hqs.mul hR hd hqs (by norm_num) (by norm_num)
    convert hm using 1 <;> norm_num <;> ring
  have hqt2 : SeparatedScaledAbs R d (-8) 2 1
      (normalizedLatitudeGapDt s t ^ 2) := by
    have hm := hqt.mul hR hd hqt (by norm_num) (by norm_num)
    convert hm using 1 <;> norm_num <;> ring
  have hgap1 : SeparatedScaledAbs R d (-8) 1 (2 * G₁)
      (2 * normalizedLatitudeGapDs s t *
        normalizedLatitudeGapDst s t) := by
    have hm := hqs.mul hR hd hqst (by norm_num) hG₁0
    have hc := hm.const_mul (c := (2 : ℝ))
    convert hc using 1 <;> norm_num <;> ring
  have hgap2A : SeparatedScaledAbs R d (-8) 0 (2 * G₁ ^ 2)
      (2 * normalizedLatitudeGapDst s t ^ 2) := by
    have hm := hqst.mul hR hd hqst hG₁0 hG₁0
    have hc := hm.const_mul (c := (2 : ℝ))
    convert hc using 1 <;> norm_num <;> ring
  have hgap2Braw : SeparatedScaledAbs R d (-10) 1 (2 * G₂)
      (2 * normalizedLatitudeGapDs s t *
        normalizedLatitudeGapDstt s t) := by
    have hm := hqs.mul hR hd hqstt (by norm_num) hG₂0
    have hc := hm.const_mul (c := (2 : ℝ))
    convert hc using 1 <;> norm_num <;> ring
  have hgap2B := hgap2Braw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep (by positivity)
  have hgap2B' : SeparatedScaledAbs R d (-8) 0 (2 * G₂ * K)
      (2 * normalizedLatitudeGapDs s t *
        normalizedLatitudeGapDstt s t) := by
    convert hgap2B using 1 <;> ring
  have hgap2 : SeparatedScaledAbs R d (-8) 0 Gsq
      (2 * normalizedLatitudeGapDst s t ^ 2 +
        2 * normalizedLatitudeGapDs s t *
          normalizedLatitudeGapDstt s t) := by
    dsimp [Gsq]
    exact hgap2A.add hgap2B'
  have hc2 : SeparatedScaledAbs R d (6 - 2 * α) (α - 3) H
      (latitudeCusp2 α s t) := by
    unfold latitudeCusp2
    exact hh2
  have hc2t : SeparatedScaledAbs R d (6 - 2 * α) (α - 4) H
      (latitudeCusp2Dt α s t) := by
    unfold latitudeCusp2Dt
    have hm := hh3.mul hR hd hqt hH0 (by norm_num)
    convert hm using 1 <;> ring
  have hc2ttA : SeparatedScaledAbs R d (6 - 2 * α) (α - 5) H
      (reducedLatitudeCuspD4Value α
        (normalizedLatitudeGap s t) *
          normalizedLatitudeGapDt s t ^ 2) := by
    have hm := hh4.mul hR hd hqt2 hH0 (by norm_num)
    convert hm using 1 <;> ring
  have hc2ttB : SeparatedScaledAbs R d (6 - 2 * α) (α - 5)
      (H * Q)
      (reducedLatitudeCuspD3Value α
        (normalizedLatitudeGap s t) *
          normalizedLatitudeGapDtt s t) := by
    have hm := hh3.mul hR hd hqtt hH0 hQ0
    convert hm using 1 <;> ring
  have hc2tt : SeparatedScaledAbs R d (6 - 2 * α) (α - 5)
      (H + H * Q) (latitudeCusp2Dtt α s t) := by
    unfold latitudeCusp2Dtt
    exact hc2ttA.add hc2ttB
  have hz1raw := (hptt'.mul hR hd hc2 hP0 hH0).mul
    hR hd hqs2 (mul_nonneg hP0 hH0) (by norm_num)
  have hz1 := hz1raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 2) hsep (by positivity)
  have hz1' : SeparatedScaledAbs R d (-2 - α) (α - 3)
      (P * H * K ^ (2 : ℝ))
      (latitudePowerDtt α s t * latitudeCusp2 α s t *
        normalizedLatitudeGapDs s t ^ 2) := by
    convert hz1 using 1 <;> ring
  have hz2raw := (hp'.mul hR hd hc2tt hP0
    (add_nonneg hH0 (mul_nonneg hH0 hQ0))).mul
      hR hd hqs2 (by positivity) (by norm_num)
  have hz2' : SeparatedScaledAbs R d (-2 - α) (α - 3)
      (P * (H + H * Q))
      (latitudePower α s t * latitudeCusp2Dtt α s t *
        normalizedLatitudeGapDs s t ^ 2) := by
    convert hz2raw using 1 <;> ring
  have hz3raw := (hp'.mul hR hd hc2 hP0 hH0).mul
    hR hd hgap2 (mul_nonneg hP0 hH0) hGsq0
  have hz3' : SeparatedScaledAbs R d (-2 - α) (α - 3)
      (P * (H * Gsq))
      (latitudePower α s t * latitudeCusp2 α s t *
        (2 * normalizedLatitudeGapDst s t ^ 2 +
          2 * normalizedLatitudeGapDs s t *
            normalizedLatitudeGapDstt s t)) := by
    convert hz3raw using 1 <;> ring
  have hz4raw := (hpt'.mul hR hd hc2t hP0 hH0).mul
    hR hd hqs2 (mul_nonneg hP0 hH0) (by norm_num)
  have hz4 := hz4raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep (by positivity)
  have hz4' : SeparatedScaledAbs R d (-2 - α) (α - 3)
      (P * H * K)
      (latitudePowerDt α s t * latitudeCusp2Dt α s t *
        normalizedLatitudeGapDs s t ^ 2) := by
    convert hz4 using 1 <;> ring
  have hz5raw := (hpt'.mul hR hd hc2 hP0 hH0).mul
    hR hd hgap1 (mul_nonneg hP0 hH0) (by positivity)
  have hz5 := hz5raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep (by positivity)
  have hz5' : SeparatedScaledAbs R d (-2 - α) (α - 3)
      (P * (H * (2 * G₁)) * K)
      (latitudePowerDt α s t * latitudeCusp2 α s t *
        (2 * normalizedLatitudeGapDs s t *
          normalizedLatitudeGapDst s t)) := by
    convert hz5 using 1 <;> ring
  have hz6raw := (hp'.mul hR hd hc2t hP0 hH0).mul
    hR hd hgap1 (mul_nonneg hP0 hH0) (by positivity)
  have hz6' : SeparatedScaledAbs R d (-2 - α) (α - 3)
      (P * (H * (2 * G₁)))
      (latitudePower α s t * latitudeCusp2Dt α s t *
        (2 * normalizedLatitudeGapDs s t *
          normalizedLatitudeGapDst s t)) := by
    convert hz6raw using 1 <;> ring
  have hblock :=
    SeparatedScaledAbs.latitudeJetMul3D2
      hz1' hz2' hz3' hz4' hz5' hz6'
  unfold SeparatedScaledAbs at hblock
  unfold latitudePowerDerivativeScale
  simpa [R, d, P, H, K, Q, G₁, G₂, Gsq,
    latitudeComparableThirdMixedConstant, mul_assoc] using hblock

noncomputable def latitudeComparableFourthMixedConstant (α : ℝ) : ℝ :=
  let P := latitudeComparablePowerJetConstant α
  let H := latitudeComparableRawCuspSeparatedConstant α
  let K : ℝ := 3200
  let Q : ℝ := 1600 + 3 * 3200
  let G₂ : ℝ := 15364801
  let G₃ : ℝ := 46094407
  P * (H * Q) * K +
    P * ((H + H * Q) * Q) +
    P * (H * G₃) * K +
    2 * (P * (H * Q) * K) +
    2 * (P * (H * G₂) * K) +
    2 * (P * (H * G₂) * K)

theorem latitudeComparableFourthMixedConstant_nonneg (α : ℝ) :
    0 ≤ latitudeComparableFourthMixedConstant α := by
  unfold latitudeComparableFourthMixedConstant
    latitudeComparablePowerJetConstant
    latitudePowerCoefficientEnvelope
    latitudeComparablePowerRpowConstant
    latitudeComparableRawCuspSeparatedConstant
    latitudeComparableCuspDerivativeConstant
  positivity

/-- The fourth top-level block contains the pure second left-gap jet and
again has the sharp physical scale. -/
theorem separatedComparableSame_rectangle_fourthMixedBlock
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : SeparatedComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |latitudeJetMul3D2
        (latitudePower α s t) (latitudePowerDt α s t)
          (latitudePowerDtt α s t)
        (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
        (normalizedLatitudeGapDss s t) (normalizedLatitudeGapDsst s t)
          (normalizedLatitudeGapDsstt s t)| ≤
      latitudeComparableFourthMixedConstant α *
        latitudePowerDerivativeScale α
          (comparableLatitudeRadiusFloor N j) |s - t| := by
  let R := comparableLatitudeRadiusFloor N j
  let d := |s - t|
  let P := latitudeComparablePowerJetConstant α
  let H := latitudeComparableRawCuspSeparatedConstant α
  let K : ℝ := 3200
  let Q : ℝ := 1600 + 3 * 3200
  let G₂ : ℝ := 15364801
  let G₃ : ℝ := 46094407
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
  have hG₂0 : 0 ≤ G₂ := by norm_num [G₂]
  have hG₃0 : 0 ≤ G₃ := by norm_num [G₃]
  rcases comparableSame_rectangle_powerJetGradedBound
      hα0 hα2 hM hjk.1 hs ht with
    ⟨_, hp, _hps, hpt, _hpss, _hpst, hptt,
      _hpsst, _hpstt, _hpsstt⟩
  rcases separatedComparableSame_rectangle_rawCuspSeparatedBound
      hα0 hα2 hM hjk hs ht with
    ⟨_hh0, hh1, hh2, hh3, _hh4⟩
  have hgap :=
    comparableSame_rectangle_normalizedLatitudeGap_le hM hjk.1 hs ht
  rcases comparableSame_rectangle_gradedGapBound
      hM hjk.1 hs ht hgap with
    ⟨_hqsRaw, _hqstRaw, hqssRaw, hqsstRaw, _hqsttRaw, hqssttRaw⟩
  rcases separatedComparableSame_rectangle_rightGapJet hM hjk hs ht with
    ⟨hqtRaw, hqttRaw⟩
  have hp' : SeparatedScaledAbs R d α 0 P
      (latitudePower α s t) := hp.toSeparated
  have hpt' : SeparatedScaledAbs R d (α - 2) 0 P
      (latitudePowerDt α s t) := hpt.toSeparated
  have hptt' : SeparatedScaledAbs R d (α - 4) 0 P
      (latitudePowerDtt α s t) := hptt.toSeparated
  have hqt : SeparatedScaledAbs R d (-4) 1 1
      (normalizedLatitudeGapDt s t) := by
    unfold SeparatedScaledAbs
    dsimp [R, d] at hqtRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 4] at hqtRaw
    simpa [mul_assoc, mul_comm] using hqtRaw
  have hqtt : SeparatedScaledAbs R d (-4) 0 Q
      (normalizedLatitudeGapDtt s t) := by
    unfold SeparatedScaledAbs
    dsimp [R, d, Q] at hqttRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 4] at hqttRaw
    simpa using hqttRaw
  have hqt2 : SeparatedScaledAbs R d (-8) 2 1
      (normalizedLatitudeGapDt s t ^ 2) := by
    have hm := hqt.mul hR hd hqt (by norm_num) (by norm_num)
    convert hm using 1 <;> norm_num <;> ring
  have hqss : SeparatedScaledAbs R d (-4) 0 Q
      (normalizedLatitudeGapDss s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDss s t| ≤ Q * R⁻¹ ^ 4 at hqssRaw
    dsimp [d, Q] at hqssRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 4] at hqssRaw
    simpa using hqssRaw
  have hqsst : SeparatedScaledAbs R d (-6) 0 G₂
      (normalizedLatitudeGapDsst s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDsst s t| ≤ G₂ * R⁻¹ ^ 6 at hqsstRaw
    dsimp [d, G₂] at hqsstRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 6] at hqsstRaw
    simpa using hqsstRaw
  have hqsstt : SeparatedScaledAbs R d (-8) 0 G₃
      (normalizedLatitudeGapDsstt s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDsstt s t| ≤ G₃ * R⁻¹ ^ 8 at hqssttRaw
    dsimp [d, G₃] at hqssttRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat hR 8] at hqssttRaw
    simpa using hqssttRaw
  have hc1 : SeparatedScaledAbs R d (4 - 2 * α) (α - 2) H
      (latitudeCusp1 α s t) := by
    unfold latitudeCusp1
    exact hh1
  have hc1t : SeparatedScaledAbs R d (2 - 2 * α) (α - 2) H
      (latitudeCusp1Dt α s t) := by
    unfold latitudeCusp1Dt
    have hm := hh2.mul hR hd hqt hH0 (by norm_num)
    convert hm using 1 <;> ring
  have hc1ttA : SeparatedScaledAbs R d (2 - 2 * α) (α - 3) H
      (reducedLatitudeCuspD3Value α
        (normalizedLatitudeGap s t) *
          normalizedLatitudeGapDt s t ^ 2) := by
    have hm := hh3.mul hR hd hqt2 hH0 (by norm_num)
    convert hm using 1 <;> ring
  have hc1ttB : SeparatedScaledAbs R d (2 - 2 * α) (α - 3)
      (H * Q)
      (reducedLatitudeCuspD2Value α
        (normalizedLatitudeGap s t) *
          normalizedLatitudeGapDtt s t) := by
    have hm := hh2.mul hR hd hqtt hH0 hQ0
    convert hm using 1 <;> ring
  have hc1tt : SeparatedScaledAbs R d (2 - 2 * α) (α - 3)
      (H + H * Q) (latitudeCusp1Dtt α s t) := by
    unfold latitudeCusp1Dtt
    exact hc1ttA.add hc1ttB
  have hz1raw := (hptt'.mul hR hd hc1 hP0 hH0).mul
    hR hd hqss (mul_nonneg hP0 hH0) hQ0
  have hz1 := hz1raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep (by positivity)
  have hz1' : SeparatedScaledAbs R d (-2 - α) (α - 3)
      (P * (H * Q) * K)
      (latitudePowerDtt α s t * latitudeCusp1 α s t *
        normalizedLatitudeGapDss s t) := by
    convert hz1 using 1 <;> ring
  have hz2raw := (hp'.mul hR hd hc1tt hP0
    (add_nonneg hH0 (mul_nonneg hH0 hQ0))).mul
      hR hd hqss (by positivity) hQ0
  have hz2' : SeparatedScaledAbs R d (-2 - α) (α - 3)
      (P * ((H + H * Q) * Q))
      (latitudePower α s t * latitudeCusp1Dtt α s t *
        normalizedLatitudeGapDss s t) := by
    convert hz2raw using 1 <;> ring
  have hz3raw := (hp'.mul hR hd hc1 hP0 hH0).mul
    hR hd hqsstt (mul_nonneg hP0 hH0) hG₃0
  have hz3 := hz3raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep (by positivity)
  have hz3' : SeparatedScaledAbs R d (-2 - α) (α - 3)
      (P * (H * G₃) * K)
      (latitudePower α s t * latitudeCusp1 α s t *
        normalizedLatitudeGapDsstt s t) := by
    convert hz3 using 1 <;> ring
  have hz4raw := (hpt'.mul hR hd hc1t hP0 hH0).mul
    hR hd hqss (mul_nonneg hP0 hH0) hQ0
  have hz4 := hz4raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep (by positivity)
  have hz4' : SeparatedScaledAbs R d (-2 - α) (α - 3)
      (P * (H * Q) * K)
      (latitudePowerDt α s t * latitudeCusp1Dt α s t *
        normalizedLatitudeGapDss s t) := by
    convert hz4 using 1 <;> ring
  have hz5raw := (hpt'.mul hR hd hc1 hP0 hH0).mul
    hR hd hqsst (mul_nonneg hP0 hH0) hG₂0
  have hz5 := hz5raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep (by positivity)
  have hz5' : SeparatedScaledAbs R d (-2 - α) (α - 3)
      (P * (H * G₂) * K)
      (latitudePowerDt α s t * latitudeCusp1 α s t *
        normalizedLatitudeGapDsst s t) := by
    convert hz5 using 1 <;> ring
  have hz6raw := (hp'.mul hR hd hc1t hP0 hH0).mul
    hR hd hqsst (mul_nonneg hP0 hH0) hG₂0
  have hz6 := hz6raw.shift hR hd hK0
    (by norm_num : (0 : ℝ) ≤ 1) hsep (by positivity)
  have hz6' : SeparatedScaledAbs R d (-2 - α) (α - 3)
      (P * (H * G₂) * K)
      (latitudePower α s t * latitudeCusp1Dt α s t *
        normalizedLatitudeGapDsst s t) := by
    convert hz6 using 1 <;> ring
  have hblock :=
    SeparatedScaledAbs.latitudeJetMul3D2
      hz1' hz2' hz3' hz4' hz5' hz6'
  unfold SeparatedScaledAbs at hblock
  unfold latitudePowerDerivativeScale
  simpa [R, d, P, H, K, Q, G₂, G₃,
    latitudeComparableFourthMixedConstant, mul_assoc] using hblock

/-- One uniform constant for all four top-level mixed-derivative blocks. -/
noncomputable def latitudeComparableMixedConstant (α : ℝ) : ℝ :=
  latitudeComparableFirstMixedConstant α +
    latitudeComparableSecondMixedConstant α +
    latitudeComparableThirdMixedConstant α +
    latitudeComparableFourthMixedConstant α

theorem latitudeComparableMixedConstant_nonneg (α : ℝ) :
    0 ≤ latitudeComparableMixedConstant α := by
  have h1 := latitudeComparableFirstMixedConstant_nonneg α
  have h2 := latitudeComparableSecondMixedConstant_nonneg α
  have h3 := latitudeComparableThirdMixedConstant_nonneg α
  have h4 := latitudeComparableFourthMixedConstant_nonneg α
  unfold latitudeComparableMixedConstant
  linarith

/-- Premise-free sharp four-term package on every separated comparable
same-hemisphere rectangle. -/
theorem separatedComparableSame_rectangle_mixedTermBound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : SeparatedComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    LatitudeComparableMixedTermBound α s t
      (comparableLatitudeRadiusFloor N j)
      (latitudeComparableMixedConstant α) := by
  have h1 := separatedComparableSame_rectangle_firstMixedBlock
    hα0 hα2 hM hjk hs ht
  have h2 := separatedComparableSame_rectangle_secondMixedBlock
    hα0 hα2 hM hjk hs ht
  have h3 := separatedComparableSame_rectangle_thirdMixedBlock
    hα0 hα2 hM hjk hs ht
  have h4 := separatedComparableSame_rectangle_fourthMixedBlock
    hα0 hα2 hM hjk hs ht
  have hscale :
      0 ≤ latitudePowerDerivativeScale α
        (comparableLatitudeRadiusFloor N j) |s - t| := by
    unfold latitudePowerDerivativeScale
    have hR0 : 0 ≤ comparableLatitudeRadiusFloor N j := by
      unfold comparableLatitudeRadiusFloor
      exact div_nonneg (by positivity) (by positivity)
    exact mul_nonneg (Real.rpow_nonneg hR0 _)
      (Real.rpow_nonneg (abs_nonneg _) _)
  have hC1 := latitudeComparableFirstMixedConstant_nonneg α
  have hC2 := latitudeComparableSecondMixedConstant_nonneg α
  have hC3 := latitudeComparableThirdMixedConstant_nonneg α
  have hC4 := latitudeComparableFourthMixedConstant_nonneg α
  unfold LatitudeComparableMixedTermBound
  constructor
  · exact h1.trans <|
      mul_le_mul_of_nonneg_right
        (show latitudeComparableFirstMixedConstant α ≤
            latitudeComparableMixedConstant α by
          unfold latitudeComparableMixedConstant
          linarith)
        hscale
  constructor
  · exact h2.trans <|
      mul_le_mul_of_nonneg_right
        (show latitudeComparableSecondMixedConstant α ≤
            latitudeComparableMixedConstant α by
          unfold latitudeComparableMixedConstant
          linarith)
        hscale
  constructor
  · exact h3.trans <|
      mul_le_mul_of_nonneg_right
        (show latitudeComparableThirdMixedConstant α ≤
            latitudeComparableMixedConstant α by
          unfold latitudeComparableMixedConstant
          linarith)
        hscale
  · exact h4.trans <|
      mul_le_mul_of_nonneg_right
        (show latitudeComparableFourthMixedConstant α ≤
            latitudeComparableMixedConstant α by
          unfold latitudeComparableMixedConstant
          linarith)
        hscale

/-- Final unconditional separated comparable block estimate. -/
theorem separatedComparableSame_block_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N) :
    ∀ j k, SeparatedComparableSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α
          (8192 * (comparableDerivativeScaleConversionConstant α *
            latitudeComparableMixedConstant α)) N j k := by
  exact separatedComparableSame_block_bound_of_comparableTerms
    hM hα0 hα2 (latitudeComparableMixedConstant_nonneg α)
    (fun j k hjk s hs t ht ↦
      separatedComparableSame_rectangle_mixedTermBound
        hα0 hα2 hM hjk hs ht)

end BEMOC
