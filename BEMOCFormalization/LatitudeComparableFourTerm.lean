import BEMOCFormalization.LatitudeComparableCuspJet

/-!
# Homogeneous sharp jets for the comparable mixed derivative

This module keeps radius degrees through the explicit product rules.  The
small `ScaledAbs` calculus prevents a common-envelope argument from erasing
the homogeneity.
-/

open Set

namespace BEMOC

set_option maxHeartbeats 800000

def ScaledAbs (R e C x : ℝ) : Prop :=
  |x| ≤ C * R ^ e

theorem ScaledAbs.mul {R e f C D x y : ℝ} (hR : 0 < R)
    (hx : ScaledAbs R e C x) (hy : ScaledAbs R f D y)
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ScaledAbs R (e + f) (C * D) (x * y) := by
  unfold ScaledAbs at *
  rw [abs_mul]
  calc
    |x| * |y| ≤ (C * R ^ e) * (D * R ^ f) := by gcongr
    _ = (C * D) * R ^ (e + f) := by
      rw [Real.rpow_add hR]
      ring

theorem ScaledAbs.add {R e C D x y : ℝ}
    (hx : ScaledAbs R e C x) (hy : ScaledAbs R e D y) :
    ScaledAbs R e (C + D) (x + y) := by
  unfold ScaledAbs at *
  calc
    |x + y| ≤ |x| + |y| := abs_add _ _
    _ ≤ C * R ^ e + D * R ^ e := add_le_add hx hy
    _ = (C + D) * R ^ e := by ring

theorem ScaledAbs.const_mul {R e C c x : ℝ}
    (hx : ScaledAbs R e C x) :
    ScaledAbs R e (|c| * C) (c * x) := by
  unfold ScaledAbs at *
  rw [abs_mul]
  calc
    |c| * |x| ≤ |c| * (C * R ^ e) :=
      mul_le_mul_of_nonneg_left hx (abs_nonneg c)
    _ = (|c| * C) * R ^ e := by ring

theorem ScaledAbs.mono_const {R e C D x : ℝ}
    (hR : 0 < R) (hx : ScaledAbs R e C x) (hCD : C ≤ D) :
    ScaledAbs R e D x := by
  unfold ScaledAbs at *
  exact hx.trans (mul_le_mul_of_nonneg_right hCD
    (Real.rpow_nonneg hR.le _))

theorem ScaledAbs.congr_exp {R e f C x : ℝ}
    (hx : ScaledAbs R e C x) (hef : e = f) :
    ScaledAbs R f C x := by rwa [← hef]

def LatitudeComparablePowerJetGradedBound
    (α s t R P : ℝ) : Prop :=
  0 ≤ P ∧
  ScaledAbs R α P (latitudePower α s t) ∧
  ScaledAbs R (α - 2) P (latitudePowerDs α s t) ∧
  ScaledAbs R (α - 2) P (latitudePowerDt α s t) ∧
  ScaledAbs R (α - 4) P (latitudePowerDss α s t) ∧
  ScaledAbs R (α - 4) P (latitudePowerDst α s t) ∧
  ScaledAbs R (α - 4) P (latitudePowerDtt α s t) ∧
  ScaledAbs R (α - 6) P (latitudePowerDsst α s t) ∧
  ScaledAbs R (α - 6) P (latitudePowerDstt α s t) ∧
  ScaledAbs R (α - 8) P (latitudePowerDsstt α s t)

noncomputable def latitudeComparablePowerJetConstant (α : ℝ) : ℝ :=
  1000000000 * latitudePowerCoefficientEnvelope α *
    latitudeComparablePowerRpowConstant α

private theorem scaled_coefficient
    {α B c R : ℝ} (hB : LatitudePowerCoefficientBound α B)
    (hc : |c| ≤ B) :
    ScaledAbs R 0 B c := by
  unfold ScaledAbs
  simpa using hc

private theorem scaled_rpow
    {α s t R A e : ℝ}
    (h : |latitudeAngularScale s t ^ e| ≤ A * R ^ (2 * e)) :
    ScaledAbs R (2 * e) A (latitudeAngularScale s t ^ e) := h

private theorem scaled_angular_zero
    {R C x : ℝ} (hx : |x| ≤ C) :
    ScaledAbs R 0 C x := by
  unfold ScaledAbs
  simpa using hx

theorem latitudeComparablePowerJetGradedBound
    {α s t R : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hR : 0 < R)
    (hang : LatitudeComparableAngularJetBound s t R) :
    LatitudeComparablePowerJetGradedBound α s t R
      (latitudeComparablePowerJetConstant α) := by
  let A := latitudeComparablePowerRpowConstant α
  let B := latitudePowerCoefficientEnvelope α
  let P := latitudeComparablePowerJetConstant α
  rcases latitudePowerCoefficientBound_envelope α with
    ⟨hB1, hc1, hc2, hc3, hc4⟩
  have hB0 : 0 ≤ B := by
    dsimp [B, latitudePowerCoefficientEnvelope]
    positivity
  have hB1' : 1 ≤ B := by simpa [B] using hB1
  rcases latitudeComparablePowerRpowGradedBound hα0 hα2 hR hang with
    ⟨hA0, hu0, hu1, hu2, hu3, hu4⟩
  rcases hang with
    ⟨_, _, hps, hpt, hpss, hptt, hpst, hpsst, hpstt, hpsstt⟩
  have hBA : 0 ≤ B * A := mul_nonneg hB0 hA0
  have hP0 : 0 ≤ P := by
    dsimp [P, latitudeComparablePowerJetConstant]
    positivity
  have hPbig : 900000000 * B * A ≤ P := by
    dsimp [P, latitudeComparablePowerJetConstant]
    nlinarith
  have hAB : B * A ≤ P := by nlinarith
  have sB1 : ScaledAbs R 0 B (α / 2) :=
    scaled_coefficient ⟨hB1, hc1, hc2, hc3, hc4⟩ hc1
  have sB2 : ScaledAbs R 0 B ((α / 2) * (α / 2 - 1)) :=
    scaled_coefficient ⟨hB1, hc1, hc2, hc3, hc4⟩ hc2
  have sB3 : ScaledAbs R 0 B
      ((α / 2) * (α / 2 - 1) * (α / 2 - 2)) :=
    scaled_coefficient ⟨hB1, hc1, hc2, hc3, hc4⟩ hc3
  have sB4 : ScaledAbs R 0 B
      ((α / 2) * (α / 2 - 1) * (α / 2 - 2) *
        (α / 2 - 3)) :=
    scaled_coefficient ⟨hB1, hc1, hc2, hc3, hc4⟩ hc4
  have su0 : ScaledAbs R α A
      (latitudeAngularScale s t ^ (α / 2)) := by
    exact hu0
  have su1 : ScaledAbs R (α - 2) A
      (latitudeAngularScale s t ^ (α / 2 - 1)) := hu1
  have su2 : ScaledAbs R (α - 4) A
      (latitudeAngularScale s t ^ (α / 2 - 2)) := hu2
  have su3 : ScaledAbs R (α - 6) A
      (latitudeAngularScale s t ^ (α / 2 - 3)) := hu3
  have su4 : ScaledAbs R (α - 8) A
      (latitudeAngularScale s t ^ (α / 2 - 4)) := hu4
  have sps : ScaledAbs R 0 80 (latitudeAngularScaleDs s t) :=
    scaled_angular_zero hps
  have spt : ScaledAbs R 0 80 (latitudeAngularScaleDt s t) :=
    scaled_angular_zero hpt
  have spss : ScaledAbs R (-2) 80 (latitudeAngularScaleDss s t) := by
    unfold ScaledAbs
    simpa [Real.rpow_neg hR.le, Real.rpow_natCast] using hpss
  have sptt : ScaledAbs R (-2) 80 (latitudeAngularScaleDtt s t) := by
    unfold ScaledAbs
    simpa [Real.rpow_neg hR.le, Real.rpow_natCast] using hptt
  have spst : ScaledAbs R (-2) 2 (latitudeAngularScaleDst s t) := by
    unfold ScaledAbs
    simpa [Real.rpow_neg hR.le, Real.rpow_natCast] using hpst
  have spsst : ScaledAbs R (-4) 2 (latitudeAngularScaleDsst s t) := by
    unfold ScaledAbs
    have hpow : R ^ (-4 : ℝ) = (R ^ 4)⁻¹ := by
      rw [Real.rpow_neg hR.le]
      exact congrArg Inv.inv (Real.rpow_natCast _ 4)
    rw [hpow]
    simpa only [inv_pow] using hpsst
  have spstt : ScaledAbs R (-4) 2 (latitudeAngularScaleDstt s t) := by
    unfold ScaledAbs
    have hpow : R ^ (-4 : ℝ) = (R ^ 4)⁻¹ := by
      rw [Real.rpow_neg hR.le]
      exact congrArg Inv.inv (Real.rpow_natCast _ 4)
    rw [hpow]
    simpa only [inv_pow] using hpstt
  have spsstt : ScaledAbs R (-6) 2
      (latitudeAngularScaleDsstt s t) := by
    unfold ScaledAbs
    have hpow : R ^ (-6 : ℝ) = (R ^ 6)⁻¹ := by
      rw [Real.rpow_neg hR.le]
      exact congrArg Inv.inv (Real.rpow_natCast _ 6)
    rw [hpow]
    simpa only [inv_pow] using hpsstt
  have hzero : ScaledAbs R α P (latitudePower α s t) := by
    unfold latitudePower
    have hAP : A ≤ P := by
      simpa [A] using
        ((mul_le_mul_of_nonneg_right hB1' hA0).trans hAB)
    exact su0.mono_const hR hAP
  have hds0 := (sB1.mul hR su1 hB0 hA0).mul hR sps hBA (by norm_num)
  have hds : ScaledAbs R (α - 2) P (latitudePowerDs α s t) := by
    unfold latitudePowerDs
    exact (hds0.congr_exp (by ring)).mono_const hR
      (by nlinarith)
  have hdt0 := (sB1.mul hR su1 hB0 hA0).mul hR spt hBA (by norm_num)
  have hdt : ScaledAbs R (α - 2) P (latitudePowerDt α s t) := by
    unfold latitudePowerDt
    exact (hdt0.congr_exp (by ring)).mono_const hR
      (by nlinarith)
  have hss1 := ((sB2.mul hR su2 hB0 hA0).mul hR sps hBA
    (by norm_num)).mul hR sps (by positivity) (by norm_num)
  have hss2 := (sB1.mul hR su1 hB0 hA0).mul hR spss hBA (by norm_num)
  have hss : ScaledAbs R (α - 4) P (latitudePowerDss α s t) := by
    unfold latitudePowerDss
    have ha := hss1.congr_exp (show 0 + (α - 4) + 0 + 0 = α - 4 by ring)
    have hb := hss2.congr_exp (show 0 + (α - 2) + -2 = α - 4 by ring)
    convert (ha.add hb).mono_const hR (by nlinarith) using 1 <;> ring
  have htt1 := ((sB2.mul hR su2 hB0 hA0).mul hR spt hBA
    (by norm_num)).mul hR spt (by positivity) (by norm_num)
  have htt2 := (sB1.mul hR su1 hB0 hA0).mul hR sptt hBA (by norm_num)
  have htt : ScaledAbs R (α - 4) P (latitudePowerDtt α s t) := by
    unfold latitudePowerDtt
    have ha := htt1.congr_exp (show 0 + (α - 4) + 0 + 0 = α - 4 by ring)
    have hb := htt2.congr_exp (show 0 + (α - 2) + -2 = α - 4 by ring)
    convert (ha.add hb).mono_const hR (by nlinarith) using 1 <;> ring
  have hst1 := ((sB2.mul hR su2 hB0 hA0).mul hR spt hBA
    (by norm_num)).mul hR sps (by positivity) (by norm_num)
  have hst2 := (sB1.mul hR su1 hB0 hA0).mul hR spst hBA (by norm_num)
  have hst : ScaledAbs R (α - 4) P (latitudePowerDst α s t) := by
    unfold latitudePowerDst
    have ha := hst1.congr_exp (show 0 + (α - 4) + 0 + 0 = α - 4 by ring)
    have hb := hst2.congr_exp (show 0 + (α - 2) + -2 = α - 4 by ring)
    convert (ha.add hb).mono_const hR (by nlinarith) using 1 <;> ring
  have hsst1 := (((sB3.mul hR su3 hB0 hA0).mul hR spt hBA
    (by norm_num)).mul hR sps (by positivity) (by norm_num)).mul hR sps
      (by positivity) (by norm_num)
  have hsst2base := (sB2.mul hR su2 hB0 hA0).mul hR sps hBA (by norm_num)
  have hsst2 := ((hsst2base.mul hR spst (by positivity) (by norm_num)).const_mul
    (c := (2 : ℝ)))
  have hsst3 := ((sB2.mul hR su2 hB0 hA0).mul hR spt hBA
    (by norm_num)).mul hR spss (by positivity) (by norm_num)
  have hsst4 := (sB1.mul hR su1 hB0 hA0).mul hR spsst hBA (by norm_num)
  have hsst : ScaledAbs R (α - 6) P (latitudePowerDsst α s t) := by
    unfold latitudePowerDsst
    have h1 := hsst1.congr_exp (show
      0 + (α - 6) + 0 + 0 + 0 = α - 6 by ring)
    have h2 := hsst2.congr_exp (show
      0 + (α - 4) + 0 + -2 = α - 6 by ring)
    have h3 := hsst3.congr_exp (show
      0 + (α - 4) + 0 + -2 = α - 6 by ring)
    have h4 := hsst4.congr_exp (show
      0 + (α - 2) + -4 = α - 6 by ring)
    convert (((h1.add h2).add h3).add h4).mono_const (D := P) hR
      (by norm_num; nlinarith) using 1 <;> ring
  have hstt1 := (((sB3.mul hR su3 hB0 hA0).mul hR spt hBA
    (by norm_num)).mul hR spt (by positivity) (by norm_num)).mul hR sps
      (by positivity) (by norm_num)
  have hstt2 := ((sB2.mul hR su2 hB0 hA0).mul hR sptt hBA
    (by norm_num)).mul hR sps (by positivity) (by norm_num)
  have hstt3base := ((sB2.mul hR su2 hB0 hA0).mul hR spt hBA
    (by norm_num)).mul hR spst (by positivity) (by norm_num)
  have hstt3 := hstt3base.const_mul (c := (2 : ℝ))
  have hstt4 := (sB1.mul hR su1 hB0 hA0).mul hR spstt hBA (by norm_num)
  have hstt : ScaledAbs R (α - 6) P (latitudePowerDstt α s t) := by
    unfold latitudePowerDstt
    have h1 := hstt1.congr_exp (show
      0 + (α - 6) + 0 + 0 + 0 = α - 6 by ring)
    have h2 := hstt2.congr_exp (show
      0 + (α - 4) + -2 + 0 = α - 6 by ring)
    have h3 := hstt3.congr_exp (show
      0 + (α - 4) + 0 + -2 = α - 6 by ring)
    have h4 := hstt4.congr_exp (show
      0 + (α - 2) + -4 = α - 6 by ring)
    convert (((h1.add h2).add h3).add h4).mono_const (D := P) hR
      (by norm_num; nlinarith) using 1 <;> ring
  have z1 := ((((sB4.mul hR su4 hB0 hA0).mul hR spt hBA
    (by norm_num)).mul hR spt (by positivity) (by norm_num)).mul hR sps
      (by positivity) (by norm_num)).mul hR sps (by positivity) (by norm_num)
  have z2 := (((sB3.mul hR su3 hB0 hA0).mul hR sptt hBA
    (by norm_num)).mul hR sps (by positivity) (by norm_num)).mul hR sps
      (by positivity) (by norm_num)
  have z3base := (((sB3.mul hR su3 hB0 hA0).mul hR spt hBA
    (by norm_num)).mul hR sps (by positivity) (by norm_num)).mul hR spst
      (by positivity) (by norm_num)
  have z3 := z3base.const_mul (c := (4 : ℝ))
  have z4base := ((sB2.mul hR su2 hB0 hA0).mul hR spst hBA
    (by norm_num)).mul hR spst (by positivity) (by norm_num)
  have z4 := z4base.const_mul (c := (2 : ℝ))
  have z5base := ((sB2.mul hR su2 hB0 hA0).mul hR sps hBA
    (by norm_num)).mul hR spstt (by positivity) (by norm_num)
  have z5 := z5base.const_mul (c := (2 : ℝ))
  have z6 := (((sB3.mul hR su3 hB0 hA0).mul hR spt hBA
    (by norm_num)).mul hR spt (by positivity) (by norm_num)).mul hR spss
      (by positivity) (by norm_num)
  have z7 := ((sB2.mul hR su2 hB0 hA0).mul hR sptt hBA
    (by norm_num)).mul hR spss (by positivity) (by norm_num)
  have z8base := ((sB2.mul hR su2 hB0 hA0).mul hR spt hBA
    (by norm_num)).mul hR spsst (by positivity) (by norm_num)
  have z8 := z8base.const_mul (c := (2 : ℝ))
  have z9 := (sB1.mul hR su1 hB0 hA0).mul hR spsstt hBA (by norm_num)
  have hsstt : ScaledAbs R (α - 8) P (latitudePowerDsstt α s t) := by
    unfold latitudePowerDsstt
    have h1 := z1.congr_exp (show
      0 + (α - 8) + 0 + 0 + 0 + 0 = α - 8 by ring)
    have h2 := z2.congr_exp (show
      0 + (α - 6) + -2 + 0 + 0 = α - 8 by ring)
    have h3 := z3.congr_exp (show
      0 + (α - 6) + 0 + 0 + -2 = α - 8 by ring)
    have h4 := z4.congr_exp (show
      0 + (α - 4) + -2 + -2 = α - 8 by ring)
    have h5 := z5.congr_exp (show
      0 + (α - 4) + 0 + -4 = α - 8 by ring)
    have h6 := z6.congr_exp (show
      0 + (α - 6) + 0 + 0 + -2 = α - 8 by ring)
    have h7 := z7.congr_exp (show
      0 + (α - 4) + -2 + -2 = α - 8 by ring)
    have h8 := z8.congr_exp (show
      0 + (α - 4) + 0 + -4 = α - 8 by ring)
    have h9 := z9.congr_exp (show
      0 + (α - 2) + -6 = α - 8 by ring)
    convert ((((((((h1.add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).mono_const
      (D := P) hR (by norm_num; nlinarith) using 1 <;> ring
  exact ⟨hP0, hzero, hds, hdt, hss, hst, htt, hsst, hstt, hsstt⟩

theorem comparableSame_rectangle_powerJetGradedBound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : ComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    LatitudeComparablePowerJetGradedBound α s t
      (comparableLatitudeRadiusFloor N j)
      (latitudeComparablePowerJetConstant α) := by
  have hR : 0 < comparableLatitudeRadiusFloor N j := by
    unfold comparableLatitudeRadiusFloor
    have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hdr : (0 : ℝ) < latitudeBandScale N j := by
      exact_mod_cast latitudeBandScale_pos N j
    positivity
  exact latitudeComparablePowerJetGradedBound hα0 hα2 hR
    (comparableSame_rectangle_angularJetBound hM hjk hs ht)

/-- Moving `n` powers from the separation variable into two radius powers
under the comparable-chart inequality `d ≤ K R²`.  This is the exact
homogeneity conversion used by every one of the four Leibniz blocks. -/
theorem rpow_monomial_shift_le
    {R d K a b n : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hK : 0 ≤ K) (hn : 0 ≤ n) (hsep : d ≤ K * R ^ 2) :
    R ^ a * d ^ b ≤
      K ^ n * (R ^ (a + 2 * n) * d ^ (b - n)) := by
  have hdn : d ^ n ≤ (K * R ^ 2) ^ n :=
    Real.rpow_le_rpow hd.le hsep hn
  have hKR :
      (K * R ^ 2) ^ n = K ^ n * R ^ (2 * n) := by
    rw [Real.mul_rpow hK (sq_nonneg R)]
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le]
    norm_num
  have hbase : 0 ≤ R ^ a * d ^ (b - n) := by positivity
  calc
    R ^ a * d ^ b =
        (R ^ a * d ^ (b - n)) * d ^ n := by
      rw [show b = (b - n) + n by ring, Real.rpow_add hd]
      ring
    _ ≤ (R ^ a * d ^ (b - n)) * (K ^ n * R ^ (2 * n)) := by
      rw [← hKR]
      exact mul_le_mul_of_nonneg_left hdn hbase
    _ = K ^ n * (R ^ (a + 2 * n) * d ^ (b - n)) := by
      rw [Real.rpow_add hR]
      ring

def SeparatedScaledAbs (R d a b C x : ℝ) : Prop :=
  |x| ≤ C * R ^ a * d ^ b

theorem SeparatedScaledAbs.mul
    {R d a b a' b' C D x y : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hx : SeparatedScaledAbs R d a b C x)
    (hy : SeparatedScaledAbs R d a' b' D y)
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    SeparatedScaledAbs R d (a + a') (b + b') (C * D) (x * y) := by
  unfold SeparatedScaledAbs at *
  rw [abs_mul]
  calc
    |x| * |y| ≤ (C * R ^ a * d ^ b) *
        (D * R ^ a' * d ^ b') := by gcongr
    _ = (C * D) * R ^ (a + a') * d ^ (b + b') := by
      rw [Real.rpow_add hR, Real.rpow_add hd]
      ring

theorem SeparatedScaledAbs.add
    {R d a b C D x y : ℝ}
    (hx : SeparatedScaledAbs R d a b C x)
    (hy : SeparatedScaledAbs R d a b D y) :
    SeparatedScaledAbs R d a b (C + D) (x + y) := by
  unfold SeparatedScaledAbs at *
  calc
    |x + y| ≤ |x| + |y| := abs_add _ _
    _ ≤ C * R ^ a * d ^ b + D * R ^ a * d ^ b :=
      add_le_add hx hy
    _ = (C + D) * R ^ a * d ^ b := by ring

theorem SeparatedScaledAbs.const_mul
    {R d a b C c x : ℝ}
    (hx : SeparatedScaledAbs R d a b C x) :
    SeparatedScaledAbs R d a b (|c| * C) (c * x) := by
  unfold SeparatedScaledAbs at *
  rw [abs_mul]
  calc
    |c| * |x| ≤ |c| * (C * R ^ a * d ^ b) :=
      mul_le_mul_of_nonneg_left hx (abs_nonneg c)
    _ = (|c| * C) * R ^ a * d ^ b := by ring

theorem SeparatedScaledAbs.shift
    {R d K a b n C x : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hK : 0 ≤ K) (hn : 0 ≤ n) (hsep : d ≤ K * R ^ 2)
    (hC : 0 ≤ C) (hx : SeparatedScaledAbs R d a b C x) :
    SeparatedScaledAbs R d (a + 2 * n) (b - n)
      (C * K ^ n) x := by
  unfold SeparatedScaledAbs at *
  calc
    |x| ≤ C * (R ^ a * d ^ b) := by simpa [mul_assoc] using hx
    _ ≤ C * (K ^ n * (R ^ (a + 2 * n) * d ^ (b - n))) :=
      mul_le_mul_of_nonneg_left
        (rpow_monomial_shift_le hR hd hK hn hsep) hC
    _ = (C * K ^ n) * R ^ (a + 2 * n) * d ^ (b - n) := by ring

def LatitudeComparableRawCuspSeparatedBound
    (α s t R C : ℝ) : Prop :=
  SeparatedScaledAbs R |s - t| 0 0 C
      (reducedLatitudeCusp α (normalizedLatitudeGap s t)) ∧
  SeparatedScaledAbs R |s - t| (4 - 2 * α) (α - 2) C
      (reducedLatitudeCuspD1Value α (normalizedLatitudeGap s t)) ∧
  SeparatedScaledAbs R |s - t| (6 - 2 * α) (α - 3) C
      (reducedLatitudeCuspD2Value α (normalizedLatitudeGap s t)) ∧
  SeparatedScaledAbs R |s - t| (10 - 2 * α) (α - 5) C
      (reducedLatitudeCuspD3Value α (normalizedLatitudeGap s t)) ∧
  SeparatedScaledAbs R |s - t| (14 - 2 * α) (α - 7) C
      (reducedLatitudeCuspD4Value α (normalizedLatitudeGap s t))

noncomputable def latitudeComparableRawCuspSeparatedConstant (α : ℝ) : ℝ :=
  let A := latitudeComparableCuspDerivativeConstant α
  let c : ℝ := ((3202 : ℝ) * 40 ^ 4)⁻¹
  A * (1 + c ^ (α / 2 - 1) + c ^ (α / 2 - 3 / 2) +
    c ^ (α / 2 - 5 / 2) + c ^ (α / 2 - 7 / 2))

theorem separatedComparableSame_rectangle_rawCuspSeparatedBound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : SeparatedComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    LatitudeComparableRawCuspSeparatedBound α s t
      (comparableLatitudeRadiusFloor N j)
      (latitudeComparableRawCuspSeparatedConstant α) := by
  let R := comparableLatitudeRadiusFloor N j
  let d := |s - t|
  let A := latitudeComparableCuspDerivativeConstant α
  let c : ℝ := ((3202 : ℝ) * 40 ^ 4)⁻¹
  let C := latitudeComparableRawCuspSeparatedConstant α
  have hrect :=
    separatedComparableSame_rectangle_interior_offDiagonal hM hjk hs ht
  have hRpos : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hdr : (0 : ℝ) < latitudeBandScale N j := by
      exact_mod_cast latitudeBandScale_pos N j
    positivity
  have hdpos : 0 < d := by
    dsimp [d]
    exact abs_pos.mpr (sub_ne_zero.mpr hrect.2.2)
  have hq : 0 < normalizedLatitudeGap s t :=
    normalizedLatitudeGap_pos hrect.1 hrect.2.1 hrect.2.2
  have hqUpper :=
    comparableSame_rectangle_normalizedLatitudeGap_le hM hjk.1 hs ht
  rcases latitudeComparableCuspDerivativeBound hα0 hα2 hq hqUpper with
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
  have hpow1 :=
    separatedComparableSame_rectangle_normalizedGap_rpow_le
      (e := α / 2 - 1) (by linarith) hM hjk hs ht
  have hpow2 :=
    separatedComparableSame_rectangle_normalizedGap_rpow_le
      (e := α / 2 - 3 / 2) (by linarith) hM hjk hs ht
  have hpow3 :=
    separatedComparableSame_rectangle_normalizedGap_rpow_le
      (e := α / 2 - 5 / 2) (by linarith) hM hjk hs ht
  have hpow4 :=
    separatedComparableSame_rectangle_normalizedGap_rpow_le
      (e := α / 2 - 7 / 2) (by linarith) hM hjk hs ht
  have h0 : SeparatedScaledAbs R d 0 0 C
      (reducedLatitudeCusp α (normalizedLatitudeGap s t)) := by
    unfold SeparatedScaledAbs
    simpa [R, d] using hv0.trans hcoef0
  have h1 : SeparatedScaledAbs R d (4 - 2 * α) (α - 2) C
      (reducedLatitudeCuspD1Value α (normalizedLatitudeGap s t)) := by
    unfold SeparatedScaledAbs
    calc
      |_| ≤ A * normalizedLatitudeGap s t ^ (α / 2 - 1) := hv1
      _ ≤ A * (c ^ (α / 2 - 1) * d ^ (α - 2) *
          R ^ (4 - 2 * α)) := by
        dsimp [R, d, c] at hpow1 ⊢
        gcongr
        convert hpow1 using 1 <;> ring
      _ ≤ C * R ^ (4 - 2 * α) * d ^ (α - 2) := by
        have hnon : 0 ≤ R ^ (4 - 2 * α) * d ^ (α - 2) := by positivity
        nlinarith
  have h2 : SeparatedScaledAbs R d (6 - 2 * α) (α - 3) C
      (reducedLatitudeCuspD2Value α (normalizedLatitudeGap s t)) := by
    unfold SeparatedScaledAbs
    calc
      |_| ≤ A * normalizedLatitudeGap s t ^ (α / 2 - 3 / 2) := hv2
      _ ≤ A * (c ^ (α / 2 - 3 / 2) * d ^ (α - 3) *
          R ^ (6 - 2 * α)) := by
        dsimp [R, d, c] at hpow2 ⊢
        gcongr
        convert hpow2 using 1 <;> ring
      _ ≤ C * R ^ (6 - 2 * α) * d ^ (α - 3) := by
        have hnon : 0 ≤ R ^ (6 - 2 * α) * d ^ (α - 3) := by positivity
        nlinarith
  have h3 : SeparatedScaledAbs R d (10 - 2 * α) (α - 5) C
      (reducedLatitudeCuspD3Value α (normalizedLatitudeGap s t)) := by
    unfold SeparatedScaledAbs
    calc
      |_| ≤ A * normalizedLatitudeGap s t ^ (α / 2 - 5 / 2) := hv3
      _ ≤ A * (c ^ (α / 2 - 5 / 2) * d ^ (α - 5) *
          R ^ (10 - 2 * α)) := by
        dsimp [R, d, c] at hpow3 ⊢
        gcongr
        convert hpow3 using 1 <;> ring
      _ ≤ C * R ^ (10 - 2 * α) * d ^ (α - 5) := by
        have hnon : 0 ≤ R ^ (10 - 2 * α) * d ^ (α - 5) := by positivity
        nlinarith
  have h4 : SeparatedScaledAbs R d (14 - 2 * α) (α - 7) C
      (reducedLatitudeCuspD4Value α (normalizedLatitudeGap s t)) := by
    unfold SeparatedScaledAbs
    calc
      |_| ≤ A * normalizedLatitudeGap s t ^ (α / 2 - 7 / 2) := hv4
      _ ≤ A * (c ^ (α / 2 - 7 / 2) * d ^ (α - 7) *
          R ^ (14 - 2 * α)) := by
        dsimp [R, d, c] at hpow4 ⊢
        gcongr
        convert hpow4 using 1 <;> ring
      _ ≤ C * R ^ (14 - 2 * α) * d ^ (α - 7) := by
        have hnon : 0 ≤ R ^ (14 - 2 * α) * d ^ (α - 7) := by positivity
        nlinarith
  exact ⟨h0, h1, h2, h3, h4⟩

end BEMOC
