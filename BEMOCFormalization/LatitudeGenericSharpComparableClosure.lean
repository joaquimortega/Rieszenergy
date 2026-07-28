import BEMOCFormalization.LatitudeCentralComparableClosure

/-!
# Generic sharp comparable closure

The sharp four-term calculation is local: its real hypotheses are a common
radius chart and a quadratic upper bound for the physical separation, not a
particular latitude-pair classifier.  This module records that classifier-free
interface for the central and smooth-opposite exceptional comparable classes.
-/

open Set

namespace BEMOC

set_option maxHeartbeats 800000

/-- The common local chart used by the sharp comparable calculation. -/
def LatitudeGenericComparableRadiusChart
    (s t R K : ℝ) : Prop :=
  s ∈ Ioo (-1 : ℝ) 1 ∧
  t ∈ Ioo (-1 : ℝ) 1 ∧
  s ≠ t ∧
  0 < R ∧
  0 ≤ K ∧
  R ≤ heightRadius s ∧
  R ≤ heightRadius t ∧
  heightRadius s ≤ 40 * R ∧
  heightRadius t ≤ 40 * R ∧
  |s - t| ≤ K * R ^ 2 ∧
  K ≤ 3200

theorem LatitudeGenericComparableRadiusChart.diameter
    {s t R K : ℝ} (h : LatitudeGenericComparableRadiusChart s t R K) :
    |s - t| ≤ K * R ^ 2 := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hd, _⟩
  exact hd

private theorem inv_pow_eq_rpow_neg_nat_generic
    {R : ℝ} (hR : 0 < R) (n : ℕ) :
    R⁻¹ ^ n = R ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg hR.le]
  simpa only [inv_pow] using
    congrArg Inv.inv (Real.rpow_natCast R n).symm

private theorem genericDerivativeScale_identity
    {α d M D : ℝ} (hd : 0 < d) (hM : 0 < M) (hD : 0 < D) :
    (d / (10 * M)) ^ (-2 - α) *
        (d * D / (30 * M ^ 2)) ^ (α - 3) =
      (10 : ℝ) ^ (2 + α) * (30 : ℝ) ^ (3 - α) *
        M ^ (8 - α) * d ^ (-5 : ℝ) * D ^ (α - 3) := by
  rw [Real.div_rpow hd.le (by positivity : 0 ≤ 10 * M),
    Real.div_rpow (mul_nonneg hd.le hD.le)
      (by positivity : 0 ≤ 30 * M ^ 2)]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [← Real.rpow_neg (by positivity : 0 ≤ 10 * M),
    ← Real.rpow_neg (by positivity : 0 ≤ 30 * M ^ 2)]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) hM.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 30) (sq_nonneg M),
    Real.mul_rpow hd.le hD.le]
  rw [← Real.rpow_natCast M 2]
  rw [← Real.rpow_mul hM.le]
  calc
    d ^ (-2 - α) * (10 ^ (-(-2 - α)) * M ^ (-(-2 - α))) *
          (d ^ (α - 3) * D ^ (α - 3) *
            (30 ^ (-(α - 3)) * M ^ ((2 : ℝ) * -(α - 3)))) =
        (10 ^ (-(-2 - α)) * 30 ^ (-(α - 3))) *
          (M ^ (-(-2 - α)) * M ^ ((2 : ℝ) * -(α - 3))) *
          (d ^ (-2 - α) * d ^ (α - 3)) * D ^ (α - 3) := by ring
    _ = (10 ^ (-(-2 - α)) * 30 ^ (-(α - 3))) *
          M ^ (-(-2 - α) + (2 : ℝ) * -(α - 3)) *
          d ^ ((-2 - α) + (α - 3)) * D ^ (α - 3) := by
      rw [Real.rpow_add hM, Real.rpow_add hd]
    _ = _ := by ring_nf

private theorem centralDerivativeScale_identity
    {α M D : ℝ} (hM : 0 < M) (hD : 0 < D) :
    ((1 : ℝ) / 10) ^ (-2 - α) *
        (D / (30 * M)) ^ (α - 3) =
      (10 : ℝ) ^ (2 + α) * (30 : ℝ) ^ (3 - α) *
        M ^ (3 - α) * D ^ (α - 3) := by
  have hi := genericDerivativeScale_identity
    (α := α) (d := M) (M := M) (D := D) hM hM hD
  have hR : M / (10 * M) = (1 : ℝ) / 10 := by
    field_simp [hM.ne']
    ring
  have hsep : M * D / (30 * M ^ 2) = D / (30 * M) := by
    field_simp [hM.ne']
    ring
  have hpow :
      M ^ (8 - α) * M ^ (-5 : ℝ) = M ^ (3 - α) := by
    rw [← Real.rpow_add hM]
    congr 1
    ring
  rw [hR, hsep] at hi
  calc
    ((1 : ℝ) / 10) ^ (-2 - α) *
        (D / (30 * M)) ^ (α - 3) =
      (10 : ℝ) ^ (2 + α) * (30 : ℝ) ^ (3 - α) *
        M ^ (8 - α) * M ^ (-5 : ℝ) * D ^ (α - 3) := hi
    _ = (10 : ℝ) ^ (2 + α) * (30 : ℝ) ^ (3 - α) *
        (M ^ (8 - α) * M ^ (-5 : ℝ)) * D ^ (α - 3) := by ring
    _ = _ := by rw [hpow]

theorem LatitudeGenericComparableRadiusChart.gap_pos
    {s t R K : ℝ} (h : LatitudeGenericComparableRadiusChart s t R K) :
    0 < normalizedLatitudeGap s t :=
  normalizedLatitudeGap_pos h.1 h.2.1 h.2.2.1

/-- A radius chart with quadratic diameter at most `3200 R²` lies in the
same fixed normalized-gap chart used by the regular comparable proof. -/
theorem LatitudeGenericComparableRadiusChart.normalizedGap_le
    {s t R K : ℝ} (h : LatitudeGenericComparableRadiusChart s t R K) :
    normalizedLatitudeGap s t ≤ 3200 := by
  rcases h with
    ⟨hs, ht, hst, hR, hK, hsfloor, htfloor, hsupper, htupper,
      hdiam, hKupper⟩
  have hgap0 : 0 ≤ normalizedLatitudeGap s t :=
    (normalizedLatitudeGap_pos hs ht hst).le
  have hid := normalizedLatitudeGap_mul_add_two hs ht
  have hprodFloor :
      R ^ 2 ≤ heightRadius s * heightRadius t := by
    have hrs0 : 0 ≤ heightRadius s := by
      unfold heightRadius
      positivity
    nlinarith [mul_le_mul hsfloor htfloor hR.le hrs0]
  have hprodSq :
      R ^ 4 ≤ (heightRadius s * heightRadius t) ^ 2 := by
    nlinarith [sq_nonneg
      (heightRadius s * heightRadius t - R ^ 2)]
  have hdiam' : |s - t| ≤ 3200 * R ^ 2 :=
    hdiam.trans (by gcongr)
  have hdiamSq : (s - t) ^ 2 ≤ 3200 ^ 2 * R ^ 4 := by
    nlinarith [sq_abs (s - t), abs_nonneg (s - t)]
  have hprodPos : 0 < (heightRadius s * heightRadius t) ^ 2 := by
    have hrs : 0 < heightRadius s := hR.trans_le hsfloor
    have hrt : 0 < heightRadius t := hR.trans_le htfloor
    positivity
  have hmul :
      (heightRadius s * heightRadius t) ^ 2 *
          (normalizedLatitudeGap s t *
            (normalizedLatitudeGap s t + 2)) ≤
        (heightRadius s * heightRadius t) ^ 2 * 3200 ^ 2 := by
    rw [hid]
    calc
      (s - t) ^ 2 ≤ 3200 ^ 2 * R ^ 4 := hdiamSq
      _ ≤ 3200 ^ 2 *
          (heightRadius s * heightRadius t) ^ 2 := by gcongr
      _ = (heightRadius s * heightRadius t) ^ 2 * 3200 ^ 2 := by ring
  have hquad :
      normalizedLatitudeGap s t *
          (normalizedLatitudeGap s t + 2) ≤ 3200 ^ 2 := by
    exact (mul_le_mul_left hprodPos).mp
      (by simpa only [mul_assoc] using hmul)
  nlinarith

/-- The generic chart supplies the sharp angular power jet. -/
theorem LatitudeGenericComparableRadiusChart.powerJet
    {α s t R K : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (h : LatitudeGenericComparableRadiusChart s t R K) :
    LatitudeComparablePowerJetGradedBound α s t R
      (latitudeComparablePowerJetConstant α) := by
  rcases h with
    ⟨hs, ht, hst, hR, hK, hsfloor, htfloor, hsupper, htupper,
      hdiam, hKupper⟩
  apply latitudeComparablePowerJetGradedBound hα2 hR
  apply latitudeComparableAngularJetBound
    ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩
    hR hsfloor htfloor hsupper htupper

/-- The generic chart supplies the complete normalized-gap jet. -/
theorem LatitudeGenericComparableRadiusChart.gapJet
    {s t R K : ℝ} (h : LatitudeGenericComparableRadiusChart s t R K) :
    LatitudeComparableGradedGapBound s t R K := by
  rcases h with
    ⟨hs, ht, hst, hR, hK, hsfloor, htfloor, hsupper, htupper,
      hdiam, hKupper⟩
  exact latitudeComparableGradedGapBound
    ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩
    hR hK hsfloor htfloor hsupper htupper hdiam
    (LatitudeGenericComparableRadiusChart.normalizedGap_le
      ⟨hs, ht, hst, hR, hK, hsfloor, htfloor, hsupper, htupper,
        hdiam, hKupper⟩)

/-- The two pure right gap entries follow by symmetry from the generic
graded gap jet. -/
theorem LatitudeGenericComparableRadiusChart.rightGapJet
    {s t R K : ℝ} (h : LatitudeGenericComparableRadiusChart s t R K) :
    |normalizedLatitudeGapDt s t| ≤ |s - t| * R⁻¹ ^ 4 ∧
    |normalizedLatitudeGapDtt s t| ≤
      (1600 + 3 * K) * R⁻¹ ^ 4 := by
  rcases h with
    ⟨hs, ht, hst, hR, hK, hsfloor, htfloor, hsupper, htupper,
      hdiam, hKupper⟩
  have hswap : LatitudeGenericComparableRadiusChart t s R K :=
    ⟨ht, hs, Ne.symm hst, hR, hK, htfloor, hsfloor, htupper, hsupper,
      by simpa [abs_sub_comm] using hdiam, hKupper⟩
  rcases hswap.gapJet with ⟨hDs, _, hDss, _⟩
  unfold normalizedLatitudeGapDt normalizedLatitudeGapDtt
  constructor
  · simpa [abs_sub_comm] using hDs
  · simpa using hDss

/-- Quadratic lower gap estimate in a generic radius chart. -/
theorem LatitudeGenericComparableRadiusChart.gap_quadratic_lower
    {s t R K : ℝ} (h : LatitudeGenericComparableRadiusChart s t R K) :
    (((3202 : ℝ) * 40 ^ 4)⁻¹) * (s - t) ^ 2 *
        (R ^ 4)⁻¹ ≤ normalizedLatitudeGap s t := by
  rcases h with
    ⟨hs, ht, hst, hR, hK, hsfloor, htfloor, hsupper, htupper,
      hdiam, hKupper⟩
  exact normalizedLatitudeGap_quadratic_lower_fixedChart
    hs ht hR hsupper htupper
    (LatitudeGenericComparableRadiusChart.gap_pos
      ⟨hs, ht, hst, hR, hK, hsfloor, htfloor, hsupper, htupper,
        hdiam, hKupper⟩).le
    (LatitudeGenericComparableRadiusChart.normalizedGap_le
      ⟨hs, ht, hst, hR, hK, hsfloor, htfloor, hsupper, htupper,
        hdiam, hKupper⟩)

/-- Nonpositive powers of the normalized gap retain the exact physical
separation/radius grading in any generic comparable chart. -/
theorem LatitudeGenericComparableRadiusChart.gap_rpow_le
    {e s t R K : ℝ} (he : e ≤ 0)
    (h : LatitudeGenericComparableRadiusChart s t R K) :
    normalizedLatitudeGap s t ^ e ≤
      (((3202 : ℝ) * 40 ^ 4)⁻¹) ^ e *
        |s - t| ^ (2 * e) * R ^ ((-4) * e) := by
  have hd : 0 < |s - t| :=
    abs_pos.mpr (sub_ne_zero.mpr h.2.2.1)
  have habs : |s - t| ^ (2 : ℝ) = (s - t) ^ 2 := by
    rw [Real.rpow_two]
    exact sq_abs (s - t)
  have hRpow : R ^ (-4 : ℝ) = (R ^ 4)⁻¹ := by
    rw [Real.rpow_neg h.2.2.2.1.le]
    exact congrArg Inv.inv (Real.rpow_natCast _ 4)
  apply rpow_le_of_comparable_quadratic_gap h.gap_pos
    (by positivity) hd h.2.2.2.1 he
  rw [habs, hRpow]
  exact h.gap_quadratic_lower

/-- The raw cusp jet on a generic comparable chart has the same sharp
separation grading as in the regular comparable case. -/
theorem LatitudeGenericComparableRadiusChart.rawCuspSeparated
    {α s t R K : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (h : LatitudeGenericComparableRadiusChart s t R K) :
    LatitudeComparableRawCuspSeparatedBound α s t R
      (latitudeComparableRawCuspSeparatedConstant α) := by
  let d := |s - t|
  let A := latitudeComparableCuspDerivativeConstant α
  let c : ℝ := ((3202 : ℝ) * 40 ^ 4)⁻¹
  let C := latitudeComparableRawCuspSeparatedConstant α
  have hRpos : 0 < R := h.2.2.2.1
  have hdpos : 0 < d := by
    dsimp [d]
    exact abs_pos.mpr (sub_ne_zero.mpr h.2.2.1)
  have hq := h.gap_pos
  rcases latitudeComparableCuspDerivativeBound
      hα0 hα2 hq h.normalizedGap_le with
    ⟨hA0, hv0, hv1, hv2, hv3, hv4⟩
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hC0 : 0 ≤ C := by
    dsimp [C, latitudeComparableRawCuspSeparatedConstant, A, c]
    positivity
  have hp1 : 0 ≤ c ^ (α / 2 - 1) := by positivity
  have hp2 : 0 ≤ c ^ (α / 2 - 3 / 2) := by positivity
  have hp3 : 0 ≤ c ^ (α / 2 - 5 / 2) := by positivity
  have hp4 : 0 ≤ c ^ (α / 2 - 7 / 2) := by positivity
  have hcoef0 : A ≤ C := by
    dsimp [C, latitudeComparableRawCuspSeparatedConstant]
    dsimp [c] at hp1 hp2 hp3 hp4
    nlinarith
  have hcoef1 : A * c ^ (α / 2 - 1) ≤ C := by
    dsimp [C, latitudeComparableRawCuspSeparatedConstant]
    dsimp [c] at hp1 hp2 hp3 hp4 ⊢
    nlinarith
  have hcoef2 : A * c ^ (α / 2 - 3 / 2) ≤ C := by
    dsimp [C, latitudeComparableRawCuspSeparatedConstant]
    dsimp [c] at hp1 hp2 hp3 hp4 ⊢
    nlinarith
  have hcoef3 : A * c ^ (α / 2 - 5 / 2) ≤ C := by
    dsimp [C, latitudeComparableRawCuspSeparatedConstant]
    dsimp [c] at hp1 hp2 hp3 hp4 ⊢
    nlinarith
  have hcoef4 : A * c ^ (α / 2 - 7 / 2) ≤ C := by
    dsimp [C, latitudeComparableRawCuspSeparatedConstant]
    dsimp [c] at hp1 hp2 hp3 hp4 ⊢
    nlinarith
  have hpow1 := h.gap_rpow_le
    (e := α / 2 - 1) (by linarith)
  have hpow2 := h.gap_rpow_le
    (e := α / 2 - 3 / 2) (by linarith)
  have hpow3 := h.gap_rpow_le
    (e := α / 2 - 5 / 2) (by linarith)
  have hpow4 := h.gap_rpow_le
    (e := α / 2 - 7 / 2) (by linarith)
  have h0 : SeparatedScaledAbs R d 0 0 C
      (reducedLatitudeCusp α (normalizedLatitudeGap s t)) := by
    unfold SeparatedScaledAbs
    simpa [d] using hv0.trans hcoef0
  have h1 : SeparatedScaledAbs R d (4 - 2 * α) (α - 2) C
      (reducedLatitudeCuspD1Value α (normalizedLatitudeGap s t)) := by
    unfold SeparatedScaledAbs
    calc
      |_| ≤ A * normalizedLatitudeGap s t ^ (α / 2 - 1) := hv1
      _ ≤ A * (c ^ (α / 2 - 1) * d ^ (α - 2) *
          R ^ (4 - 2 * α)) := by
        dsimp [d, c] at hpow1 ⊢
        gcongr
        convert hpow1 using 1 <;> ring
      _ ≤ C * R ^ (4 - 2 * α) * d ^ (α - 2) := by
        have hnon : 0 ≤ R ^ (4 - 2 * α) * d ^ (α - 2) := by
          positivity
        nlinarith
  have h2 : SeparatedScaledAbs R d (6 - 2 * α) (α - 3) C
      (reducedLatitudeCuspD2Value α (normalizedLatitudeGap s t)) := by
    unfold SeparatedScaledAbs
    calc
      |_| ≤ A * normalizedLatitudeGap s t ^ (α / 2 - 3 / 2) := hv2
      _ ≤ A * (c ^ (α / 2 - 3 / 2) * d ^ (α - 3) *
          R ^ (6 - 2 * α)) := by
        dsimp [d, c] at hpow2 ⊢
        gcongr
        convert hpow2 using 1 <;> ring
      _ ≤ C * R ^ (6 - 2 * α) * d ^ (α - 3) := by
        have hnon : 0 ≤ R ^ (6 - 2 * α) * d ^ (α - 3) := by
          positivity
        nlinarith
  have h3 : SeparatedScaledAbs R d (10 - 2 * α) (α - 5) C
      (reducedLatitudeCuspD3Value α (normalizedLatitudeGap s t)) := by
    unfold SeparatedScaledAbs
    calc
      |_| ≤ A * normalizedLatitudeGap s t ^ (α / 2 - 5 / 2) := hv3
      _ ≤ A * (c ^ (α / 2 - 5 / 2) * d ^ (α - 5) *
          R ^ (10 - 2 * α)) := by
        dsimp [d, c] at hpow3 ⊢
        gcongr
        convert hpow3 using 1 <;> ring
      _ ≤ C * R ^ (10 - 2 * α) * d ^ (α - 5) := by
        have hnon : 0 ≤ R ^ (10 - 2 * α) * d ^ (α - 5) := by
          positivity
        nlinarith
  have h4 : SeparatedScaledAbs R d (14 - 2 * α) (α - 7) C
      (reducedLatitudeCuspD4Value α (normalizedLatitudeGap s t)) := by
    unfold SeparatedScaledAbs
    calc
      |_| ≤ A * normalizedLatitudeGap s t ^ (α / 2 - 7 / 2) := hv4
      _ ≤ A * (c ^ (α / 2 - 7 / 2) * d ^ (α - 7) *
          R ^ (14 - 2 * α)) := by
        dsimp [d, c] at hpow4 ⊢
        gcongr
        convert hpow4 using 1 <;> ring
      _ ≤ C * R ^ (14 - 2 * α) * d ^ (α - 7) := by
        have hnon : 0 ≤ R ^ (14 - 2 * α) * d ^ (α - 7) := by
          positivity
        nlinarith
  exact ⟨h0, h1, h2, h3, h4⟩



/-! ## Generic four-term product closure -/

theorem genericComparableChart_firstMixedBlock
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {s t R L : ℝ}
    (hchart0 : LatitudeGenericComparableRadiusChart s t R L) :
    |latitudeJetMulD2
        (latitudePowerDss α s t) (latitudePowerDsst α s t)
          (latitudePowerDsstt α s t)
        (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
          (latitudeCusp0Dtt α s t)| ≤
      latitudeComparableFirstMixedConstant α *
        latitudePowerDerivativeScale α
          R |s - t| := by
  have hchart : LatitudeGenericComparableRadiusChart s t R 3200 := by
    rcases hchart0 with
      ⟨hs, ht, hst, hR0, hL, hsf, htf, hsu, htu, hd0, hLu⟩
    exact ⟨hs, ht, hst, hR0, by norm_num, hsf, htf, hsu, htu,
      hd0.trans (by gcongr), le_rfl⟩
  let d := |s - t|
  let P := latitudeComparablePowerJetConstant α
  let H := latitudeComparableRawCuspSeparatedConstant α
  let K : ℝ := 3200
  let Q : ℝ := 1600 + 3 * 3200
  have hR : 0 < R := hchart.2.2.2.1
  have hd : 0 < d := by
    dsimp [d]
    exact abs_pos.mpr (sub_ne_zero.mpr hchart.2.2.1)
  have hsep : d ≤ K * R ^ 2 := by
    dsimp [d, K]
    exact hchart.diameter
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
  rcases hchart.powerJet hα0 hα2 with
    ⟨_, _hp0, _hps, _hpt, hpss, _hpst, _hptt,
      hpsst, _hpstt, hpsstt⟩
  rcases hchart.rawCuspSeparated hα0 hα2 with
    ⟨hh0, hh1, hh2, _hh3, _hh4⟩
  rcases hchart.rightGapJet with
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
    dsimp [d] at hqtRaw ⊢
    rw [Real.rpow_one]
    have hpow :
        R⁻¹ ^ 4 =
          R ^ (-4 : ℝ) := by
      symm
      rw [Real.rpow_neg hR.le]
      simpa only [inv_pow] using congrArg Inv.inv
        (Real.rpow_natCast R 4)
    rw [hpow] at hqtRaw
    nlinarith [Real.rpow_nonneg hR.le (-4 : ℝ)]
  have hqtt :
      SeparatedScaledAbs R d (-4) 0 Q
        (normalizedLatitudeGapDtt s t) := by
    unfold SeparatedScaledAbs
    dsimp [d, Q] at hqttRaw ⊢
    have hpow :
        R⁻¹ ^ 4 =
          R ^ (-4 : ℝ) := by
      symm
      rw [Real.rpow_neg hR.le]
      simpa only [inv_pow] using congrArg Inv.inv
        (Real.rpow_natCast R 4)
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
  simpa [d, C, P, H, K, Q,
    latitudeComparableFirstMixedConstant, mul_assoc] using hblock


theorem genericComparableChart_secondMixedBlock
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {s t R L : ℝ}
    (hchart0 : LatitudeGenericComparableRadiusChart s t R L) :
    |latitudeJetMul3D2
        (latitudePowerDs α s t) (latitudePowerDst α s t)
          (latitudePowerDstt α s t)
        (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
        (normalizedLatitudeGapDs s t) (normalizedLatitudeGapDst s t)
          (normalizedLatitudeGapDstt s t)| ≤
      latitudeComparableSecondMixedConstant α *
        latitudePowerDerivativeScale α
          R |s - t| := by
  have hchart : LatitudeGenericComparableRadiusChart s t R 3200 := by
    rcases hchart0 with
      ⟨hs, ht, hst, hR0, hL, hsf, htf, hsu, htu, hd0, hLu⟩
    exact ⟨hs, ht, hst, hR0, by norm_num, hsf, htf, hsu, htu,
      hd0.trans (by gcongr), le_rfl⟩
  let d := |s - t|
  let P := latitudeComparablePowerJetConstant α
  let H := latitudeComparableRawCuspSeparatedConstant α
  let K : ℝ := 3200
  let Q : ℝ := 1600 + 3 * 3200
  let G₁ : ℝ := 5121600
  let G₂ : ℝ := 15364801
  have hR : 0 < R := hchart.2.2.2.1
  have hd : 0 < d := by
    dsimp [d]
    exact abs_pos.mpr (sub_ne_zero.mpr hchart.2.2.1)
  have hsep : d ≤ K * R ^ 2 := by
    dsimp [d, K]
    exact hchart.diameter
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
  rcases hchart.powerJet hα0 hα2 with
    ⟨_, _hp0, hps, _hpt, _hpss, hpst, _hptt,
      _hpsst, hpstt, _hpsstt⟩
  rcases hchart.rawCuspSeparated hα0 hα2 with
    ⟨_hh0, hh1, hh2, hh3, _hh4⟩
  have hgap := hchart.normalizedGap_le
  rcases hchart.gapJet with
    ⟨hqsRaw, hqstRaw, _hqssRaw, _hqsstRaw, hqsttRaw, _hqssttRaw⟩
  rcases hchart.rightGapJet with
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
    rw [inv_pow_eq_rpow_neg_nat_generic hR 4] at hqsRaw
    simpa [mul_assoc, mul_comm] using hqsRaw
  have hqt :
      SeparatedScaledAbs R d (-4) 1 1
        (normalizedLatitudeGapDt s t) := by
    unfold SeparatedScaledAbs
    dsimp [d] at hqtRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat_generic hR 4] at hqtRaw
    simpa [mul_assoc, mul_comm] using hqtRaw
  have hqst :
      SeparatedScaledAbs R d (-4) 0 G₁
        (normalizedLatitudeGapDst s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDst s t| ≤ G₁ * R⁻¹ ^ 4 at hqstRaw
    dsimp [d, G₁] at hqstRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat_generic hR 4] at hqstRaw
    simpa using hqstRaw
  have hqstt :
      SeparatedScaledAbs R d (-6) 0 G₂
        (normalizedLatitudeGapDstt s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDstt s t| ≤ G₂ * R⁻¹ ^ 6 at hqsttRaw
    dsimp [d, G₂] at hqsttRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat_generic hR 6] at hqsttRaw
    simpa using hqsttRaw
  have hqtt :
      SeparatedScaledAbs R d (-4) 0 Q
        (normalizedLatitudeGapDtt s t) := by
    unfold SeparatedScaledAbs
    dsimp [d, Q] at hqttRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat_generic hR 4] at hqttRaw
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
  simpa [d, P, H, K, Q, G₁, G₂,
    latitudeComparableSecondMixedConstant, mul_assoc] using hblock


theorem genericComparableChart_thirdMixedBlock
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {s t R L : ℝ}
    (hchart0 : LatitudeGenericComparableRadiusChart s t R L) :
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
          R |s - t| := by
  have hchart : LatitudeGenericComparableRadiusChart s t R 3200 := by
    rcases hchart0 with
      ⟨hs, ht, hst, hR0, hL, hsf, htf, hsu, htu, hd0, hLu⟩
    exact ⟨hs, ht, hst, hR0, by norm_num, hsf, htf, hsu, htu,
      hd0.trans (by gcongr), le_rfl⟩
  let d := |s - t|
  let P := latitudeComparablePowerJetConstant α
  let H := latitudeComparableRawCuspSeparatedConstant α
  let K : ℝ := 3200
  let Q : ℝ := 1600 + 3 * 3200
  let G₁ : ℝ := 5121600
  let G₂ : ℝ := 15364801
  let Gsq : ℝ := 2 * G₁ ^ 2 + 2 * G₂ * K
  have hR : 0 < R := hchart.2.2.2.1
  have hd : 0 < d := by
    dsimp [d]
    exact abs_pos.mpr (sub_ne_zero.mpr hchart.2.2.1)
  have hsep : d ≤ K * R ^ 2 := by
    dsimp [d, K]
    exact hchart.diameter
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
  rcases hchart.powerJet hα0 hα2 with
    ⟨_, hp, _hps, hpt, _hpss, _hpst, hptt,
      _hpsst, _hpstt, _hpsstt⟩
  rcases hchart.rawCuspSeparated hα0 hα2 with
    ⟨_hh0, _hh1, hh2, hh3, hh4⟩
  have hgap := hchart.normalizedGap_le
  rcases hchart.gapJet with
    ⟨hqsRaw, hqstRaw, _hqssRaw, _hqsstRaw, hqsttRaw, _hqssttRaw⟩
  rcases hchart.rightGapJet with
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
    rw [inv_pow_eq_rpow_neg_nat_generic hR 4] at hqsRaw
    simpa [mul_assoc, mul_comm] using hqsRaw
  have hqt : SeparatedScaledAbs R d (-4) 1 1
      (normalizedLatitudeGapDt s t) := by
    unfold SeparatedScaledAbs
    dsimp [d] at hqtRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat_generic hR 4] at hqtRaw
    simpa [mul_assoc, mul_comm] using hqtRaw
  have hqst : SeparatedScaledAbs R d (-4) 0 G₁
      (normalizedLatitudeGapDst s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDst s t| ≤ G₁ * R⁻¹ ^ 4 at hqstRaw
    dsimp [d, G₁] at hqstRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat_generic hR 4] at hqstRaw
    simpa using hqstRaw
  have hqstt : SeparatedScaledAbs R d (-6) 0 G₂
      (normalizedLatitudeGapDstt s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDstt s t| ≤ G₂ * R⁻¹ ^ 6 at hqsttRaw
    dsimp [d, G₂] at hqsttRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat_generic hR 6] at hqsttRaw
    simpa using hqsttRaw
  have hqtt : SeparatedScaledAbs R d (-4) 0 Q
      (normalizedLatitudeGapDtt s t) := by
    unfold SeparatedScaledAbs
    dsimp [d, Q] at hqttRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat_generic hR 4] at hqttRaw
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
  simpa [d, P, H, K, Q, G₁, G₂, Gsq,
    latitudeComparableThirdMixedConstant, mul_assoc] using hblock


theorem genericComparableChart_fourthMixedBlock
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {s t R L : ℝ}
    (hchart0 : LatitudeGenericComparableRadiusChart s t R L) :
    |latitudeJetMul3D2
        (latitudePower α s t) (latitudePowerDt α s t)
          (latitudePowerDtt α s t)
        (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
        (normalizedLatitudeGapDss s t) (normalizedLatitudeGapDsst s t)
          (normalizedLatitudeGapDsstt s t)| ≤
      latitudeComparableFourthMixedConstant α *
        latitudePowerDerivativeScale α
          R |s - t| := by
  have hchart : LatitudeGenericComparableRadiusChart s t R 3200 := by
    rcases hchart0 with
      ⟨hs, ht, hst, hR0, hL, hsf, htf, hsu, htu, hd0, hLu⟩
    exact ⟨hs, ht, hst, hR0, by norm_num, hsf, htf, hsu, htu,
      hd0.trans (by gcongr), le_rfl⟩
  let d := |s - t|
  let P := latitudeComparablePowerJetConstant α
  let H := latitudeComparableRawCuspSeparatedConstant α
  let K : ℝ := 3200
  let Q : ℝ := 1600 + 3 * 3200
  let G₂ : ℝ := 15364801
  let G₃ : ℝ := 46094407
  have hR : 0 < R := hchart.2.2.2.1
  have hd : 0 < d := by
    dsimp [d]
    exact abs_pos.mpr (sub_ne_zero.mpr hchart.2.2.1)
  have hsep : d ≤ K * R ^ 2 := by
    dsimp [d, K]
    exact hchart.diameter
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
  rcases hchart.powerJet hα0 hα2 with
    ⟨_, hp, _hps, hpt, _hpss, _hpst, hptt,
      _hpsst, _hpstt, _hpsstt⟩
  rcases hchart.rawCuspSeparated hα0 hα2 with
    ⟨_hh0, hh1, hh2, hh3, _hh4⟩
  have hgap := hchart.normalizedGap_le
  rcases hchart.gapJet with
    ⟨_hqsRaw, _hqstRaw, hqssRaw, hqsstRaw, _hqsttRaw, hqssttRaw⟩
  rcases hchart.rightGapJet with
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
    dsimp [d] at hqtRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat_generic hR 4] at hqtRaw
    simpa [mul_assoc, mul_comm] using hqtRaw
  have hqtt : SeparatedScaledAbs R d (-4) 0 Q
      (normalizedLatitudeGapDtt s t) := by
    unfold SeparatedScaledAbs
    dsimp [d, Q] at hqttRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat_generic hR 4] at hqttRaw
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
    rw [inv_pow_eq_rpow_neg_nat_generic hR 4] at hqssRaw
    simpa using hqssRaw
  have hqsst : SeparatedScaledAbs R d (-6) 0 G₂
      (normalizedLatitudeGapDsst s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDsst s t| ≤ G₂ * R⁻¹ ^ 6 at hqsstRaw
    dsimp [d, G₂] at hqsstRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat_generic hR 6] at hqsstRaw
    simpa using hqsstRaw
  have hqsstt : SeparatedScaledAbs R d (-8) 0 G₃
      (normalizedLatitudeGapDsstt s t) := by
    unfold SeparatedScaledAbs
    change |normalizedLatitudeGapDsstt s t| ≤ G₃ * R⁻¹ ^ 8 at hqssttRaw
    dsimp [d, G₃] at hqssttRaw ⊢
    rw [inv_pow_eq_rpow_neg_nat_generic hR 8] at hqssttRaw
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
  simpa [d, P, H, K, Q, G₂, G₃,
    latitudeComparableFourthMixedConstant, mul_assoc] using hblock

/-- The complete four-term package depends only on the generic radius chart,
not on the latitude-pair classifier that produced it. -/
theorem genericComparableChart_mixedTermBound
    {α s t R K : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hchart : LatitudeGenericComparableRadiusChart s t R K) :
    LatitudeComparableMixedTermBound α s t R
      (latitudeComparableMixedConstant α) := by
  have h1 := genericComparableChart_firstMixedBlock hα0 hα2 hchart
  have h2 := genericComparableChart_secondMixedBlock hα0 hα2 hchart
  have h3 := genericComparableChart_thirdMixedBlock hα0 hα2 hchart
  have h4 := genericComparableChart_fourthMixedBlock hα0 hα2 hchart
  have hscale : 0 ≤ latitudePowerDerivativeScale α R |s - t| := by
    unfold latitudePowerDerivativeScale
    exact mul_nonneg (Real.rpow_nonneg hchart.2.2.2.1.le _)
      (Real.rpow_nonneg (abs_nonneg _) _)
  have hC1 := latitudeComparableFirstMixedConstant_nonneg α
  have hC2 := latitudeComparableSecondMixedConstant_nonneg α
  have hC3 := latitudeComparableThirdMixedConstant_nonneg α
  have hC4 := latitudeComparableFourthMixedConstant_nonneg α
  unfold LatitudeComparableMixedTermBound
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h1.trans <| mul_le_mul_of_nonneg_right
      (show latitudeComparableFirstMixedConstant α ≤
          latitudeComparableMixedConstant α by
        unfold latitudeComparableMixedConstant
        linarith) hscale
  · exact h2.trans <| mul_le_mul_of_nonneg_right
      (show latitudeComparableSecondMixedConstant α ≤
          latitudeComparableMixedConstant α by
        unfold latitudeComparableMixedConstant
        linarith) hscale
  · exact h3.trans <| mul_le_mul_of_nonneg_right
      (show latitudeComparableThirdMixedConstant α ≤
          latitudeComparableMixedConstant α by
        unfold latitudeComparableMixedConstant
        linarith) hscale
  · exact h4.trans <| mul_le_mul_of_nonneg_right
      (show latitudeComparableFourthMixedConstant α ≤
          latitudeComparableMixedConstant α by
        unfold latitudeComparableMixedConstant
        linarith) hscale

/-- Generic pointwise sharp mixed derivative bound. -/
theorem genericComparableChart_Dsstt_bound
    {α s t R K : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hchart : LatitudeGenericComparableRadiusChart s t R K) :
    |variableReducedLatitudeKernelDsstt α s t| ≤
      5 * latitudeComparableMixedConstant α *
        latitudePowerDerivativeScale α R |s - t| := by
  apply abs_variableReducedLatitudeKernelDsstt_le_of_comparableTerms
    (latitudeComparableMixedConstant_nonneg α)
  · unfold latitudePowerDerivativeScale
    exact mul_nonneg (Real.rpow_nonneg hchart.2.2.2.1.le _)
      (Real.rpow_nonneg (abs_nonneg _) _)
  · exact genericComparableChart_mixedTermBound hα0 hα2 hchart

/-- Separated central-comparable rectangles lie in a fixed generic chart. -/
theorem centralComparable_separated_genericRadiusChart
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hc : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hsep : 2 ≤ Nat.dist (j : ℕ) (k : ℕ))
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    LatitudeGenericComparableRadiusChart s t ((1 : ℝ) / 10) 200 := by
  have hgeo :=
    centralComparable_separated_rectangle_geometry
      hM hc hcomp hsep hs ht
  have hfloor :=
    centralComparable_rectangle_heightRadius_floor
      hM hc hcomp hs ht
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨hgeo.1.1.le, hgeo.1.2.le⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨hgeo.2.1.1.le, hgeo.2.1.2.le⟩
  have hdiam : |s - t| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [hsSphere.1, hsSphere.2,
      htSphere.1, htSphere.2]
  refine ⟨hgeo.1, hgeo.2.1, ?_, by norm_num, by norm_num,
    hfloor.1, hfloor.2, ?_, ?_, ?_, by norm_num⟩
  · exact sub_ne_zero.mp (abs_pos.mp
      ((by positivity :
        0 < (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
          (30 * (bandCount N : ℝ))).trans_le hgeo.2.2))
  · exact (heightRadius_le_one hsSphere).trans (by norm_num)
  · exact (heightRadius_le_one htSphere).trans (by norm_num)
  · norm_num
    exact hdiam

/-- The residual central sharp derivative predicate is unconditional. -/
theorem hasCentralComparableSeparatedDssttBound_generic
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 15 ≤ bandCount N) :
    HasCentralComparableSeparatedDssttBound α N
      (comparableDerivativeScaleConversionConstant α *
        latitudeComparableMixedConstant α) := by
  intro j k hc hcomp hsep
  constructor
  · intro s hs t ht
    have hgeo :=
      centralComparable_separated_rectangle_geometry
        hM hc hcomp hsep hs ht
    exact ⟨hgeo.1, hgeo.2.1, sub_ne_zero.mp (abs_pos.mp
      ((by positivity :
        0 < (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
          (30 * (bandCount N : ℝ))).trans_le hgeo.2.2))⟩
  · intro s hs t ht
    let M : ℝ := bandCount N
    let D : ℝ := 1 + Nat.dist (j : ℕ) (k : ℕ)
    have hMr : 0 < M := by dsimp [M]; positivity
    have hD : 0 < D := by dsimp [D]; positivity
    have hchart :=
      centralComparable_separated_genericRadiusChart
        hM hc hcomp hsep hs ht
    have hraw :=
      genericComparableChart_Dsstt_bound hα0 hα2 hchart
    have hgeo :=
      centralComparable_separated_rectangle_geometry
        hM hc hcomp hsep hs ht
    have hlower : D / (30 * M) ≤ |s - t| := by
      simpa [D, M] using hgeo.2.2
    have he : α - 3 ≤ 0 := by linarith
    have hpow :
        |s - t| ^ (α - 3) ≤
          (D / (30 * M)) ^ (α - 3) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlower he
    have hcoef :
        0 ≤ 5 * latitudeComparableMixedConstant α := by
      exact mul_nonneg (by norm_num)
        (latitudeComparableMixedConstant_nonneg α)
    calc
      |variableReducedLatitudeKernelDsstt α s t| ≤
          5 * latitudeComparableMixedConstant α *
            (((1 : ℝ) / 10) ^ (-2 - α) *
              |s - t| ^ (α - 3)) := by
        simpa [latitudePowerDerivativeScale] using hraw
      _ ≤ 5 * latitudeComparableMixedConstant α *
            (((1 : ℝ) / 10) ^ (-2 - α) *
              (D / (30 * M)) ^ (α - 3)) := by gcongr
      _ = (comparableDerivativeScaleConversionConstant α *
            latitudeComparableMixedConstant α) *
          M ^ (3 - α) * D ^ (α - 3) := by
        rw [centralDerivativeScale_identity hMr hD]
        unfold comparableDerivativeScaleConversionConstant
        ring
      _ = (comparableDerivativeScaleConversionConstant α *
            latitudeComparableMixedConstant α) *
          (bandCount N : ℝ) ^ (3 - α) *
            (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
        rfl

private theorem northern_rectangle_centralDist_lower
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {j : Fin (bandTailCount N + 1)}
    (hjN : IsNorthernLatitudeBand N j)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    (1 + Nat.dist (concreteCentralBandIndex N : ℕ) (j : ℕ) : ℝ) /
        (30 * (bandCount N : ℝ)) ≤ s := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  by_cases hsep :
      2 ≤ Nat.dist (concreteCentralBandIndex N : ℕ) (j : ℕ)
  · have hzero := zero_mem_central_band_rectangle
      (N := N) (by omega : 1 ≤ bandCount N)
    simpa using central_northern_rectangle_dist_separation
      (by omega : 1 ≤ bandCount N) hjN hsep hzero hs
  · have hjlt :
        (j : ℕ) < (concreteCentralBandIndex N : ℕ) := by
      unfold IsNorthernLatitudeBand at hjN
      simp [concreteCentralBandIndex]
      omega
    have hdist :
        Nat.dist (concreteCentralBandIndex N : ℕ) (j : ℕ) = 1 := by
      have hdistle :
          Nat.dist (concreteCentralBandIndex N : ℕ) (j : ℕ) ≤ 1 := by
        omega
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hjlt.le] at hdistle
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hjlt.le]
      omega
    have hsucc :
        (j : ℕ) + 1 = (concreteCentralBandIndex N : ℕ) := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hjlt.le] at hdist
      omega
    have hboundary :
        bandBoundaryHeight N (j + 1) =
          (centralPopulation N : ℝ) / N := by
      rw [show (j : ℕ) + 1 =
        (concreteCentralBandIndex N : ℕ) from hsucc]
      exact central_bandBoundaryHeight_eq hN (by omega)
    have hMpos : (0 : ℝ) < bandCount N := by positivity
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hNupper :
        (N : ℝ) ≤ 20 * (bandCount N : ℝ) ^ 2 := by
      exact_mod_cast bemoc_N_le_twenty_bandCount_sq
        (by omega : 1 ≤ bandCount N)
    have hpopNat : 3 * bandCount N ≤ centralPopulation N := by
      have hp := concrete_centralPopulation_lower
        (N := N) (by omega : 1 ≤ bandCount N)
      omega
    have hpop :
        3 * (bandCount N : ℝ) ≤ (centralPopulation N : ℝ) := by
      exact_mod_cast hpopNat
    have hratio :
        (2 : ℝ) / (30 * (bandCount N : ℝ)) ≤
          (centralPopulation N : ℝ) / N := by
      apply (div_le_div_iff₀ (by positivity :
        0 < 30 * (bandCount N : ℝ)) hNpos).2
      nlinarith [sq_nonneg ((bandCount N : ℝ) - 1)]
    rw [hdist]
    norm_num
    exact hratio.trans (by simpa [hboundary] using hs.1)

private theorem northern_southern_rectangle_dist_separation
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjN : IsNorthernLatitudeBand N j)
    (hkS : IsSouthernLatitudeBand N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
        (30 * (bandCount N : ℝ)) ≤ |s - t| := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let kr := concreteReflectBandIndex N k
  have hkrN : IsNorthernLatitudeBand N kr :=
    reflect_southern_is_northern hkS
  have htr := neg_mem_reflected_band_rectangle_unequal hN k ht
  have hsj := northern_rectangle_centralDist_lower hM hjN hs
  have htk := northern_rectangle_centralDist_lower hM hkrN htr
  have hjlt : (j : ℕ) < bandCount N - 1 := hjN
  have hkgt : bandCount N - 1 < (k : ℕ) := hkS
  have hkrval :
      (kr : ℕ) = bandTailCount N - (k : ℕ) := rfl
  have hkTail : (k : ℕ) ≤ bandTailCount N := by omega
  have hdist :
      Nat.dist (concreteCentralBandIndex N : ℕ) (j : ℕ) +
          Nat.dist (concreteCentralBandIndex N : ℕ) (kr : ℕ) =
        Nat.dist (j : ℕ) (k : ℕ) := by
    have hkrlt : (kr : ℕ) < bandCount N - 1 := hkrN
    have hjk : (j : ℕ) ≤ (k : ℕ) := by omega
    rw [Nat.dist_comm,
      Nat.dist_eq_sub_of_le
        (show (j : ℕ) ≤
          (concreteCentralBandIndex N : ℕ) by
            simpa [concreteCentralBandIndex] using hjlt.le),
      Nat.dist_comm,
      Nat.dist_eq_sub_of_le
        (show (kr : ℕ) ≤
          (concreteCentralBandIndex N : ℕ) by
            simpa [concreteCentralBandIndex] using hkrlt.le),
      Nat.dist_eq_sub_of_le hjk]
    have hcval :
        (concreteCentralBandIndex N : ℕ) = bandCount N - 1 := rfl
    have htailval :
        bandTailCount N = 2 * (bandCount N - 1) := by
      simp [bandTailCount]
    have hkrval' :
        (kr : ℕ) = 2 * (bandCount N - 1) - (k : ℕ) := by
      exact hkrval.trans
        (congrArg (fun u : ℕ ↦ u - (k : ℕ)) htailval)
    rw [hcval]
    omega
  have hsum :
      (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
          (30 * (bandCount N : ℝ)) ≤ s - t := by
    have hden : 0 < (30 * (bandCount N : ℝ)) := by positivity
    rw [div_le_iff₀ hden]
    rw [div_le_iff₀ hden] at hsj htk
    calc
      (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ≤
          (1 + Nat.dist
            (concreteCentralBandIndex N : ℕ) (j : ℕ) : ℝ) +
          (1 + Nat.dist
            (concreteCentralBandIndex N : ℕ) (kr : ℕ) : ℝ) := by
        rw [← hdist]
        push_cast
        linarith
      _ ≤ s * (30 * (bandCount N : ℝ)) +
          (-t) * (30 * (bandCount N : ℝ)) :=
        add_le_add hsj htk
      _ = (s - t) * (30 * (bandCount N : ℝ)) := by ring
  have hst0 : 0 ≤ s - t := by
    have hleft :
        0 < (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
          (30 * (bandCount N : ℝ)) := by positivity
    linarith
  rw [abs_of_nonneg hst0]
  exact hsum

/-- Every smooth opposite rectangle has the physical index separation
needed by the generic sharp derivative conversion. -/
theorem smoothOpposite_rectangle_dist_separation
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (ho : SmoothOppositeLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
        (30 * (bandCount N : ℝ)) ≤ |s - t| := by
  rcases ho.2.2 with hNS | hSN
  · exact northern_southern_rectangle_dist_separation
      hM hNS.1 hNS.2 hs ht
  · simpa [abs_sub_comm, Nat.dist_comm] using
      (northern_southern_rectangle_dist_separation
        hM hSN.2 hSN.1 ht hs)

/-- The already-established near-equatorial opposite radius chart is an
instance of the generic sharp chart once off-diagonality is supplied. -/
theorem smoothOpposite_nearEquator_genericRadiusChart
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (ho : SmoothOppositeLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hjdeep : bandCount N < 2 * latitudeBandScale N j)
    (hkdeep : bandCount N < 2 * latitudeBandScale N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hst : s ≠ t) :
    LatitudeGenericComparableRadiusChart s t
      (comparableLatitudeRadiusFloor N j) 800 := by
  have hchart :=
    smoothOpposite_comparable_nearEquator_rectangle_radiusChart
      hM ho hcomp hjdeep hkdeep hs ht
  exact ⟨hchart.1, hchart.2.1, hst,
    by
      unfold comparableLatitudeRadiusFloor
      have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
      have hdr : (0 : ℝ) < latitudeBandScale N j := by
        exact_mod_cast latitudeBandScale_pos N j
      positivity,
    by norm_num, hchart.2.2.1, hchart.2.2.2.1,
    hchart.2.2.2.2.1, hchart.2.2.2.2.2.1,
    hchart.2.2.2.2.2.2, by norm_num⟩

/-- The near-equatorial smooth-opposite sharp derivative predicate is
unconditional. -/
theorem hasSmoothOppositeComparableNearEquatorDssttBound_generic
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N) :
    HasSmoothOppositeComparableNearEquatorDssttBound α N
      (comparableDerivativeScaleConversionConstant α *
        latitudeComparableMixedConstant α) := by
  intro j k ho hcomp hjdeep hkdeep s hs t ht
  let d : ℝ := latitudeBandScale N j
  let M : ℝ := bandCount N
  let D : ℝ := 1 + Nat.dist (j : ℕ) (k : ℕ)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast latitudeBandScale_pos N j
  have hMr : 0 < M := by dsimp [M]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hdM : d ≤ M := by
    dsimp [d, M]
    exact_mod_cast latitudeBandScale_le_bandCount
      (by omega : 1 ≤ bandCount N) j
  have hsep :=
    smoothOpposite_rectangle_dist_separation
      (by omega : 15 ≤ bandCount N) ho hs ht
  have hlower :
      d * D / (30 * M ^ 2) ≤ |s - t| := by
    calc
      d * D / (30 * M ^ 2) ≤
          M * D / (30 * M ^ 2) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdM hD.le) (by positivity)
      _ = D / (30 * M) := by
        field_simp [hMr.ne']
        ring
      _ ≤ |s - t| := by simpa [D, M] using hsep
  have hst : s ≠ t := sub_ne_zero.mp (abs_pos.mp
    ((by positivity : 0 < d * D / (30 * M ^ 2)).trans_le hlower))
  have hchart :=
    smoothOpposite_nearEquator_genericRadiusChart
      (by omega : 1 ≤ bandCount N) ho hcomp hjdeep hkdeep hs ht hst
  have hraw :=
    genericComparableChart_Dsstt_bound hα0 hα2 hchart
  have he : α - 3 ≤ 0 := by linarith
  have hpow :
      |s - t| ^ (α - 3) ≤
        (d * D / (30 * M ^ 2)) ^ (α - 3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hlower he
  have hcoef :
      0 ≤ 5 * latitudeComparableMixedConstant α :=
    mul_nonneg (by norm_num) (latitudeComparableMixedConstant_nonneg α)
  calc
    |variableReducedLatitudeKernelDsstt α s t| ≤
        5 * latitudeComparableMixedConstant α *
          ((d / (10 * M)) ^ (-2 - α) *
            |s - t| ^ (α - 3)) := by
      simpa [latitudePowerDerivativeScale, comparableLatitudeRadiusFloor,
        d, M] using hraw
    _ ≤ 5 * latitudeComparableMixedConstant α *
          ((d / (10 * M)) ^ (-2 - α) *
            (d * D / (30 * M ^ 2)) ^ (α - 3)) := by gcongr
    _ = 5 * latitudeComparableMixedConstant α *
          ((10 : ℝ) ^ (2 + α) * (30 : ℝ) ^ (3 - α) *
            M ^ (8 - α) * d ^ (-5 : ℝ) * D ^ (α - 3)) := by
      rw [genericDerivativeScale_identity hd hMr hD]
    _ = (comparableDerivativeScaleConversionConstant α *
          latitudeComparableMixedConstant α) *
        (bandCount N : ℝ) ^ (8 - α) *
        (latitudeBandScale N j : ℝ) ^ (-5 : ℝ) *
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
      unfold comparableDerivativeScaleConversionConstant
      dsimp [d, M, D]
      ring

end BEMOC
