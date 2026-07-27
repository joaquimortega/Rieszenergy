import BEMOCFormalization.LatitudeComparableBlocks

/-!
# The actual mixed `(2,2)` latitude-kernel derivative

This file completes the off-diagonal chain rule for the variable-coefficient
normal form

`p(s,t)^(α/2) * hα(q(s,t))`.

The large fourth-order value is intentionally assembled from named two-jets.
This keeps the proof auditable: the coefficient, gap, and reduced-cusp
contributions can be bounded separately without expanding one enormous
expression.
-/

open Set

namespace BEMOC

noncomputable def latitudeAngularScaleDt (s t : ℝ) : ℝ :=
  latitudeAngularScaleDs t s

noncomputable def latitudeAngularScaleDtt (s t : ℝ) : ℝ :=
  latitudeAngularScaleDss t s

noncomputable def latitudeAngularScaleDstt (s t : ℝ) : ℝ :=
  latitudeAngularScaleDsst t s

theorem hasDerivAt_latitudeAngularScale_right
    {s t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudeAngularScale s y)
      (latitudeAngularScaleDt s t) t := by
  unfold latitudeAngularScale latitudeAngularScaleDt latitudeAngularScaleDs
    heightRadius
  convert
    ((hasDerivAt_const t (2 * Real.sqrt (1 - s ^ 2))).mul
      (hasDerivAt_heightRadius ht)) using 1 <;> ring

theorem hasDerivAt_latitudeAngularScaleDt_right
    {s t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudeAngularScaleDt s y)
      (latitudeAngularScaleDtt s t) t := by
  unfold latitudeAngularScaleDt latitudeAngularScaleDtt
    latitudeAngularScaleDs latitudeAngularScaleDss
  convert
    (hasDerivAt_const t (2 * heightRadius s)).mul
      (hasDerivAt_heightRadiusD1 ht) using 1
  · funext y
    ring
  · ring

theorem hasDerivAt_latitudeAngularScaleDs_right
    {s t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudeAngularScaleDs s y)
      (latitudeAngularScaleDst s t) t := by
  unfold latitudeAngularScaleDs latitudeAngularScaleDst
  convert
    (hasDerivAt_const t (2 * heightRadiusD1 s)).mul
      (hasDerivAt_heightRadius ht) using 1 <;> ring

theorem hasDerivAt_latitudeAngularScaleDst_right
    {s t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudeAngularScaleDst s y)
      (latitudeAngularScaleDstt s t) t := by
  unfold latitudeAngularScaleDst latitudeAngularScaleDstt
    latitudeAngularScaleDsst
  convert
    (hasDerivAt_const t (2 * heightRadiusD1 s)).mul
      (hasDerivAt_heightRadiusD1 ht) using 1 <;> ring

theorem normalizedLatitudeGap_comm (s t : ℝ) :
    normalizedLatitudeGap s t = normalizedLatitudeGap t s := by
  unfold normalizedLatitudeGap
  rw [mul_comm s t, mul_comm (heightRadius s) (heightRadius t)]

noncomputable def normalizedLatitudeGapDt (s t : ℝ) : ℝ :=
  normalizedLatitudeGapDs t s

noncomputable def normalizedLatitudeGapDtt (s t : ℝ) : ℝ :=
  normalizedLatitudeGapDss t s

noncomputable def normalizedLatitudeGapDst (s t : ℝ) : ℝ :=
  (s * t - 1) / (heightRadius s ^ 3 * heightRadius t ^ 3)

noncomputable def normalizedLatitudeGapDstt (s t : ℝ) : ℝ :=
  normalizedLatitudeGapDsst t s

theorem hasDerivAt_normalizedLatitudeGap_right
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ normalizedLatitudeGap s y)
      (normalizedLatitudeGapDt s t) t := by
  have h := hasDerivAt_normalizedLatitudeGap_left
    (s := t) (t := s) ht hs
  unfold normalizedLatitudeGapDt
  convert h using 1
  funext y
  exact normalizedLatitudeGap_comm s y

theorem hasDerivAt_normalizedLatitudeGapDt_right
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ normalizedLatitudeGapDt s y)
      (normalizedLatitudeGapDtt s t) t := by
  unfold normalizedLatitudeGapDt normalizedLatitudeGapDtt
  exact hasDerivAt_normalizedLatitudeGapDs_left ht hs

theorem hasDerivAt_normalizedLatitudeGapDs_right
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ normalizedLatitudeGapDs s y)
      (normalizedLatitudeGapDst s t) t := by
  have hrs : heightRadius s ≠ 0 := (heightRadius_pos hs).ne'
  have hrt : heightRadius t ≠ 0 := (heightRadius_pos ht).ne'
  have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hrtsq := heightRadius_sq ht'
  have hden :
      HasDerivAt (fun y ↦ heightRadius s ^ 3 * heightRadius y)
        (heightRadius s ^ 3 * heightRadiusD1 t) t := by
    convert
      (hasDerivAt_const t (heightRadius s ^ 3)).mul
        (hasDerivAt_heightRadius ht) using 1 <;> ring
  unfold normalizedLatitudeGapDs normalizedLatitudeGapDst
  convert
    ((hasDerivAt_const t s).sub (hasDerivAt_id t)).div hden
      (mul_ne_zero (pow_ne_zero 3 hrs) hrt) using 1
  unfold heightRadiusD1
  field_simp [hrs, hrt]
  ring_nf at hrtsq ⊢
  linear_combination heightRadius t ^ 3 * heightRadius s ^ 6 * hrtsq

theorem hasDerivAt_normalizedLatitudeGapDst_right
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ normalizedLatitudeGapDst s y)
      (normalizedLatitudeGapDstt s t) t := by
  have hrs : heightRadius s ≠ 0 := (heightRadius_pos hs).ne'
  have hrt : heightRadius t ≠ 0 := (heightRadius_pos ht).ne'
  have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hrtsq := heightRadius_sq ht'
  have hden :
      HasDerivAt (fun y ↦ heightRadius s ^ 3 * heightRadius y ^ 3)
        (heightRadius s ^ 3 *
          (3 * heightRadius t ^ 2 * heightRadiusD1 t)) t := by
    convert
      (hasDerivAt_const t (heightRadius s ^ 3)).mul
        ((hasDerivAt_heightRadius ht).pow 3) using 1 <;> ring
  unfold normalizedLatitudeGapDst normalizedLatitudeGapDstt
    normalizedLatitudeGapDsst
  convert
    (((hasDerivAt_const t s).mul (hasDerivAt_id t)).sub_const 1).div
      hden (mul_ne_zero (pow_ne_zero 3 hrs) (pow_ne_zero 3 hrt)) using 1
  unfold heightRadiusD1
  field_simp [hrs, hrt]
  ring_nf at hrtsq ⊢

/-! Named coefficient two-jets in the second height variable. -/

noncomputable def latitudePower (α s t : ℝ) : ℝ :=
  latitudeAngularScale s t ^ (α / 2)

noncomputable def latitudePowerDt (α s t : ℝ) : ℝ :=
  (α / 2) * latitudeAngularScale s t ^ (α / 2 - 1) *
    latitudeAngularScaleDt s t

noncomputable def latitudePowerDtt (α s t : ℝ) : ℝ :=
  (α / 2) * (α / 2 - 1) *
      latitudeAngularScale s t ^ (α / 2 - 2) *
      latitudeAngularScaleDt s t ^ 2 +
    (α / 2) * latitudeAngularScale s t ^ (α / 2 - 1) *
      latitudeAngularScaleDtt s t

noncomputable def latitudePowerDs (α s t : ℝ) : ℝ :=
  (α / 2) * latitudeAngularScale s t ^ (α / 2 - 1) *
    latitudeAngularScaleDs s t

noncomputable def latitudePowerDst (α s t : ℝ) : ℝ :=
  (α / 2) * ((α / 2 - 1) *
      latitudeAngularScale s t ^ (α / 2 - 2) *
      latitudeAngularScaleDt s t * latitudeAngularScaleDs s t +
    latitudeAngularScale s t ^ (α / 2 - 1) *
      latitudeAngularScaleDst s t)

noncomputable def latitudePowerDstt (α s t : ℝ) : ℝ :=
  (α / 2) * (
    (α / 2 - 1) * (α / 2 - 2) *
      latitudeAngularScale s t ^ (α / 2 - 3) *
      latitudeAngularScaleDt s t ^ 2 * latitudeAngularScaleDs s t +
    (α / 2 - 1) * latitudeAngularScale s t ^ (α / 2 - 2) *
      latitudeAngularScaleDtt s t * latitudeAngularScaleDs s t +
    2 * (α / 2 - 1) * latitudeAngularScale s t ^ (α / 2 - 2) *
      latitudeAngularScaleDt s t * latitudeAngularScaleDst s t +
    latitudeAngularScale s t ^ (α / 2 - 1) *
      latitudeAngularScaleDstt s t)

noncomputable def latitudePowerDss (α s t : ℝ) : ℝ :=
  (α / 2) * (α / 2 - 1) *
      latitudeAngularScale s t ^ (α / 2 - 2) *
      latitudeAngularScaleDs s t ^ 2 +
    (α / 2) * latitudeAngularScale s t ^ (α / 2 - 1) *
      latitudeAngularScaleDss s t

noncomputable def latitudePowerDsst (α s t : ℝ) : ℝ :=
  (α / 2) * (α / 2 - 1) * (
      (α / 2 - 2) * latitudeAngularScale s t ^ (α / 2 - 3) *
        latitudeAngularScaleDt s t * latitudeAngularScaleDs s t ^ 2 +
      2 * latitudeAngularScale s t ^ (α / 2 - 2) *
        latitudeAngularScaleDs s t * latitudeAngularScaleDst s t) +
    (α / 2) * (
      (α / 2 - 1) * latitudeAngularScale s t ^ (α / 2 - 2) *
        latitudeAngularScaleDt s t * latitudeAngularScaleDss s t +
      latitudeAngularScale s t ^ (α / 2 - 1) *
        latitudeAngularScaleDsst s t)

noncomputable def latitudePowerDsstt (α s t : ℝ) : ℝ :=
  (α / 2) * (α / 2 - 1) * (
    (α / 2 - 2) * (α / 2 - 3) *
      latitudeAngularScale s t ^ (α / 2 - 4) *
      latitudeAngularScaleDt s t ^ 2 * latitudeAngularScaleDs s t ^ 2 +
    (α / 2 - 2) * latitudeAngularScale s t ^ (α / 2 - 3) *
      latitudeAngularScaleDtt s t * latitudeAngularScaleDs s t ^ 2 +
    4 * (α / 2 - 2) * latitudeAngularScale s t ^ (α / 2 - 3) *
      latitudeAngularScaleDt s t * latitudeAngularScaleDs s t *
        latitudeAngularScaleDst s t +
    2 * latitudeAngularScale s t ^ (α / 2 - 2) *
      latitudeAngularScaleDst s t ^ 2 +
    2 * latitudeAngularScale s t ^ (α / 2 - 2) *
      latitudeAngularScaleDs s t * latitudeAngularScaleDstt s t) +
  (α / 2) * (
    (α / 2 - 1) * (α / 2 - 2) *
      latitudeAngularScale s t ^ (α / 2 - 3) *
      latitudeAngularScaleDt s t ^ 2 * latitudeAngularScaleDss s t +
    (α / 2 - 1) * latitudeAngularScale s t ^ (α / 2 - 2) *
      latitudeAngularScaleDtt s t * latitudeAngularScaleDss s t +
    2 * (α / 2 - 1) * latitudeAngularScale s t ^ (α / 2 - 2) *
      latitudeAngularScaleDt s t * latitudeAngularScaleDsst s t +
    latitudeAngularScale s t ^ (α / 2 - 1) *
      latitudeAngularScaleDsstt s t)

theorem hasDerivAt_latitudePower_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudePower α s y)
      (latitudePowerDt α s t) t := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos
      (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  unfold latitudePower latitudePowerDt
  convert
    (Real.hasDerivAt_rpow_const (x := latitudeAngularScale s t)
      (p := α / 2) (Or.inl hp.ne')).comp t
        (hasDerivAt_latitudeAngularScale_right (s := s) ht) using 1 <;>
    simp only [Function.comp_apply] <;> ring

theorem hasDerivAt_latitudePowerDt_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudePowerDt α s y)
      (latitudePowerDtt α s t) t := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos
      (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hpow (e : ℝ) :
      HasDerivAt (fun y ↦ latitudeAngularScale s y ^ e)
        (e * latitudeAngularScale s t ^ (e - 1) *
          latitudeAngularScaleDt s t) t := by
    convert
      (Real.hasDerivAt_rpow_const (x := latitudeAngularScale s t)
        (p := e) (Or.inl hp.ne')).comp t
          (hasDerivAt_latitudeAngularScale_right (s := s) ht) using 1 <;>
      simp only [Function.comp_apply] <;> ring
  unfold latitudePowerDt latitudePowerDtt
  convert
    (((hasDerivAt_const t (α / 2)).mul (hpow (α / 2 - 1))).mul
      (hasDerivAt_latitudeAngularScaleDt_right (s := s) ht)) using 1 <;>
    ring

theorem hasDerivAt_latitudePowerDs_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudePowerDs α s y)
      (latitudePowerDst α s t) t := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos
      (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hpow :
      HasDerivAt
        (fun y ↦ latitudeAngularScale s y ^ (α / 2 - 1))
        ((α / 2 - 1) * latitudeAngularScale s t ^ (α / 2 - 2) *
          latitudeAngularScaleDt s t) t := by
    have he : α / 2 - 1 - 1 = α / 2 - 2 := by ring
    simpa only [Function.comp_apply, he] using
      (Real.hasDerivAt_rpow_const (x := latitudeAngularScale s t)
        (p := α / 2 - 1) (Or.inl hp.ne')).comp t
          (hasDerivAt_latitudeAngularScale_right (s := s) ht)
  unfold latitudePowerDs latitudePowerDst
  convert
    (((hasDerivAt_const t (α / 2)).mul hpow).mul
      (hasDerivAt_latitudeAngularScaleDs_right (s := s) ht)) using 1 <;>
    ring

theorem hasDerivAt_latitudePowerDst_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudePowerDst α s y)
      (latitudePowerDstt α s t) t := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos
      (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hpow (e : ℝ) :
      HasDerivAt (fun y ↦ latitudeAngularScale s y ^ e)
        (e * latitudeAngularScale s t ^ (e - 1) *
          latitudeAngularScaleDt s t) t := by
    convert
      (Real.hasDerivAt_rpow_const (x := latitudeAngularScale s t)
        (p := e) (Or.inl hp.ne')).comp t
          (hasDerivAt_latitudeAngularScale_right (s := s) ht) using 1 <;>
      simp only [Function.comp_apply] <;> ring
  unfold latitudePowerDst latitudePowerDstt
  have hinside :=
    (((((hasDerivAt_const t (α / 2 - 1)).mul
        (hpow (α / 2 - 2))).mul
        (hasDerivAt_latitudeAngularScaleDt_right (s := s) ht)).mul
        (hasDerivAt_latitudeAngularScaleDs_right (s := s) ht)).add
      ((hpow (α / 2 - 1)).mul
        (hasDerivAt_latitudeAngularScaleDst_right (s := s) ht)))
  convert
    (hasDerivAt_const t (α / 2)).mul hinside using 1 <;>
    ring

theorem hasDerivAt_latitudePowerDss_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudePowerDss α s y)
      (latitudePowerDsst α s t) t := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos
      (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hpow (e : ℝ) :
      HasDerivAt (fun y ↦ latitudeAngularScale s y ^ e)
        (e * latitudeAngularScale s t ^ (e - 1) *
          latitudeAngularScaleDt s t) t := by
    convert
      (Real.hasDerivAt_rpow_const (x := latitudeAngularScale s t)
        (p := e) (Or.inl hp.ne')).comp t
          (hasDerivAt_latitudeAngularScale_right (s := s) ht) using 1 <;>
      simp only [Function.comp_apply] <;> ring
  unfold latitudePowerDss latitudePowerDsst
  convert
    (((((hasDerivAt_const t ((α / 2) * (α / 2 - 1))).mul
        (hpow (α / 2 - 2))).mul
        ((hasDerivAt_latitudeAngularScaleDs_right (s := s) ht).pow 2))).add
      (((hasDerivAt_const t (α / 2)).mul
        (hpow (α / 2 - 1))).mul
        (hasDerivAt_latitudeAngularScaleDss_right (s := s) ht))) using 1 <;>
    ring

theorem hasDerivAt_latitudePowerDsst_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudePowerDsst α s y)
      (latitudePowerDsstt α s t) t := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos
      (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hpow (e : ℝ) :
      HasDerivAt (fun y ↦ latitudeAngularScale s y ^ e)
        (e * latitudeAngularScale s t ^ (e - 1) *
          latitudeAngularScaleDt s t) t := by
    convert
      (Real.hasDerivAt_rpow_const (x := latitudeAngularScale s t)
        (p := e) (Or.inl hp.ne')).comp t
          (hasDerivAt_latitudeAngularScale_right (s := s) ht) using 1 <;>
      simp only [Function.comp_apply] <;> ring
  have hpT := hasDerivAt_latitudeAngularScaleDt_right (s := s) ht
  have hpS := hasDerivAt_latitudeAngularScaleDs_right (s := s) ht
  have hpST := hasDerivAt_latitudeAngularScaleDst_right (s := s) ht
  have hpSS := hasDerivAt_latitudeAngularScaleDss_right (s := s) ht
  have hpSST := hasDerivAt_latitudeAngularScaleDsst_right (s := s) ht
  unfold latitudePowerDsst latitudePowerDsstt
  convert
    ((hasDerivAt_const t ((α / 2) * (α / 2 - 1))).mul
      (((((hasDerivAt_const t (α / 2 - 2)).mul
          (hpow (α / 2 - 3))).mul hpT).mul (hpS.pow 2)).add
        ((((hasDerivAt_const t 2).mul
          (hpow (α / 2 - 2))).mul hpS).mul hpST))).add
    ((hasDerivAt_const t (α / 2)).mul
      (((((hasDerivAt_const t (α / 2 - 1)).mul
          (hpow (α / 2 - 2))).mul hpT).mul hpSS).add
        ((hpow (α / 2 - 1)).mul hpSST))) using 1 <;>
    ring

/-! The three reduced-cusp two-jets needed by the mixed chain. -/

noncomputable def latitudeCusp0 (α s t : ℝ) : ℝ :=
  reducedLatitudeCusp α (normalizedLatitudeGap s t)

noncomputable def latitudeCusp0Dt (α s t : ℝ) : ℝ :=
  reducedLatitudeCuspD1Value α (normalizedLatitudeGap s t) *
    normalizedLatitudeGapDt s t

noncomputable def latitudeCusp0Dtt (α s t : ℝ) : ℝ :=
  reducedLatitudeCuspD2Value α (normalizedLatitudeGap s t) *
      normalizedLatitudeGapDt s t ^ 2 +
    reducedLatitudeCuspD1Value α (normalizedLatitudeGap s t) *
      normalizedLatitudeGapDtt s t

noncomputable def latitudeCusp1 (α s t : ℝ) : ℝ :=
  reducedLatitudeCuspD1Value α (normalizedLatitudeGap s t)

noncomputable def latitudeCusp1Dt (α s t : ℝ) : ℝ :=
  reducedLatitudeCuspD2Value α (normalizedLatitudeGap s t) *
    normalizedLatitudeGapDt s t

noncomputable def latitudeCusp1Dtt (α s t : ℝ) : ℝ :=
  reducedLatitudeCuspD3Value α (normalizedLatitudeGap s t) *
      normalizedLatitudeGapDt s t ^ 2 +
    reducedLatitudeCuspD2Value α (normalizedLatitudeGap s t) *
      normalizedLatitudeGapDtt s t

noncomputable def latitudeCusp2 (α s t : ℝ) : ℝ :=
  reducedLatitudeCuspD2Value α (normalizedLatitudeGap s t)

noncomputable def latitudeCusp2Dt (α s t : ℝ) : ℝ :=
  reducedLatitudeCuspD3Value α (normalizedLatitudeGap s t) *
    normalizedLatitudeGapDt s t

noncomputable def latitudeCusp2Dtt (α s t : ℝ) : ℝ :=
  reducedLatitudeCuspD4Value α (normalizedLatitudeGap s t) *
      normalizedLatitudeGapDt s t ^ 2 +
    reducedLatitudeCuspD3Value α (normalizedLatitudeGap s t) *
      normalizedLatitudeGapDtt s t

theorem hasDerivAt_latitudeCusp0_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ latitudeCusp0 α s y)
      (latitudeCusp0Dt α s t) t := by
  have hq := normalizedLatitudeGap_pos hs ht hst
  unfold latitudeCusp0 latitudeCusp0Dt
  convert
    (hasDerivAt_reducedLatitudeCusp (α := α) hq).comp t
      (hasDerivAt_normalizedLatitudeGap_right hs ht) using 1 <;>
    simp only [Function.comp_apply] <;> ring

theorem hasDerivAt_latitudeCusp0Dt_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ latitudeCusp0Dt α s y)
      (latitudeCusp0Dtt α s t) t := by
  have hq := normalizedLatitudeGap_pos hs ht hst
  unfold latitudeCusp0Dt latitudeCusp0Dtt
  convert
    (((hasDerivAt_reducedLatitudeCuspD1Value (α := α) hq).comp t
      (hasDerivAt_normalizedLatitudeGap_right hs ht)).mul
      (hasDerivAt_normalizedLatitudeGapDt_right hs ht)) using 1 <;>
    simp only [Function.comp_apply] <;> ring

theorem hasDerivAt_latitudeCusp1_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ latitudeCusp1 α s y)
      (latitudeCusp1Dt α s t) t := by
  have hq := normalizedLatitudeGap_pos hs ht hst
  unfold latitudeCusp1 latitudeCusp1Dt
  convert
    (hasDerivAt_reducedLatitudeCuspD1Value (α := α) hq).comp t
      (hasDerivAt_normalizedLatitudeGap_right hs ht) using 1 <;>
    simp only [Function.comp_apply] <;> ring

theorem hasDerivAt_latitudeCusp1Dt_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ latitudeCusp1Dt α s y)
      (latitudeCusp1Dtt α s t) t := by
  have hq := normalizedLatitudeGap_pos hs ht hst
  unfold latitudeCusp1Dt latitudeCusp1Dtt
  convert
    (((hasDerivAt_reducedLatitudeCuspD2Value (α := α) hq).comp t
      (hasDerivAt_normalizedLatitudeGap_right hs ht)).mul
      (hasDerivAt_normalizedLatitudeGapDt_right hs ht)) using 1 <;>
    simp only [Function.comp_apply] <;> ring

theorem hasDerivAt_latitudeCusp2_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ latitudeCusp2 α s y)
      (latitudeCusp2Dt α s t) t := by
  have hq := normalizedLatitudeGap_pos hs ht hst
  unfold latitudeCusp2 latitudeCusp2Dt
  convert
    (hasDerivAt_reducedLatitudeCuspD2Value (α := α) hq).comp t
      (hasDerivAt_normalizedLatitudeGap_right hs ht) using 1 <;>
    simp only [Function.comp_apply] <;> ring

theorem hasDerivAt_latitudeCusp2Dt_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ latitudeCusp2Dt α s y)
      (latitudeCusp2Dtt α s t) t := by
  have hq := normalizedLatitudeGap_pos hs ht hst
  unfold latitudeCusp2Dt latitudeCusp2Dtt
  convert
    (((hasDerivAt_reducedLatitudeCuspD3Value (α := α) hq).comp t
      (hasDerivAt_normalizedLatitudeGap_right hs ht)).mul
      (hasDerivAt_normalizedLatitudeGapDt_right hs ht)) using 1 <;>
    simp only [Function.comp_apply] <;> ring

/-! Small algebraic constructors for named first- and second-order product
jets. -/

def latitudeJetMulD1 (a a₁ b b₁ : ℝ) : ℝ :=
  a₁ * b + a * b₁

def latitudeJetMulD2 (a a₁ a₂ b b₁ b₂ : ℝ) : ℝ :=
  a₂ * b + 2 * a₁ * b₁ + a * b₂

def latitudeJetMul3D1 (a a₁ b b₁ c c₁ : ℝ) : ℝ :=
  a₁ * b * c + a * b₁ * c + a * b * c₁

def latitudeJetMul3D2
    (a a₁ a₂ b b₁ b₂ c c₁ c₂ : ℝ) : ℝ :=
  a₂ * b * c + a * b₂ * c + a * b * c₂ +
    2 * a₁ * b₁ * c + 2 * a₁ * b * c₁ + 2 * a * b₁ * c₁

theorem hasDerivAt_latitudeJetMulD1
    {a a₁ b b₁ : ℝ → ℝ} {a₂ b₂ x : ℝ}
    (ha : HasDerivAt a (a₁ x) x) (ha₁ : HasDerivAt a₁ a₂ x)
    (hb : HasDerivAt b (b₁ x) x) (hb₁ : HasDerivAt b₁ b₂ x) :
    HasDerivAt
      (fun y ↦ latitudeJetMulD1 (a y) (a₁ y) (b y) (b₁ y))
      (latitudeJetMulD2 (a x) (a₁ x) a₂ (b x) (b₁ x) b₂) x := by
  unfold latitudeJetMulD1 latitudeJetMulD2
  convert (ha₁.mul hb).add (ha.mul hb₁) using 1 <;> ring

theorem hasDerivAt_latitudeJetMul3D1
    {a a₁ b b₁ c c₁ : ℝ → ℝ} {a₂ b₂ c₂ x : ℝ}
    (ha : HasDerivAt a (a₁ x) x) (ha₁ : HasDerivAt a₁ a₂ x)
    (hb : HasDerivAt b (b₁ x) x) (hb₁ : HasDerivAt b₁ b₂ x)
    (hc : HasDerivAt c (c₁ x) x) (hc₁ : HasDerivAt c₁ c₂ x) :
    HasDerivAt
      (fun y ↦ latitudeJetMul3D1
        (a y) (a₁ y) (b y) (b₁ y) (c y) (c₁ y))
      (latitudeJetMul3D2
        (a x) (a₁ x) a₂ (b x) (b₁ x) b₂ (c x) (c₁ x) c₂) x := by
  unfold latitudeJetMul3D1 latitudeJetMul3D2
  convert
    (((ha₁.mul hb).mul hc).add ((ha.mul hb₁).mul hc)).add
      ((ha.mul hb).mul hc₁) using 1 <;> ring

noncomputable def variableReducedLatitudeKernelDsst
    (α s t : ℝ) : ℝ :=
  latitudeJetMulD1
      (latitudePowerDss α s t) (latitudePowerDsst α s t)
      (latitudeCusp0 α s t) (latitudeCusp0Dt α s t) +
    2 * latitudeJetMul3D1
      (latitudePowerDs α s t) (latitudePowerDst α s t)
      (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
      (normalizedLatitudeGapDs s t) (normalizedLatitudeGapDst s t) +
    latitudeJetMul3D1
      (latitudePower α s t) (latitudePowerDt α s t)
      (latitudeCusp2 α s t) (latitudeCusp2Dt α s t)
      (normalizedLatitudeGapDs s t ^ 2)
        (2 * normalizedLatitudeGapDs s t *
          normalizedLatitudeGapDst s t) +
    latitudeJetMul3D1
      (latitudePower α s t) (latitudePowerDt α s t)
      (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
      (normalizedLatitudeGapDss s t) (normalizedLatitudeGapDsst s t)

noncomputable def variableReducedLatitudeKernelDsstt
    (α s t : ℝ) : ℝ :=
  latitudeJetMulD2
      (latitudePowerDss α s t) (latitudePowerDsst α s t)
        (latitudePowerDsstt α s t)
      (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
        (latitudeCusp0Dtt α s t) +
    2 * latitudeJetMul3D2
      (latitudePowerDs α s t) (latitudePowerDst α s t)
        (latitudePowerDstt α s t)
      (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
        (latitudeCusp1Dtt α s t)
      (normalizedLatitudeGapDs s t) (normalizedLatitudeGapDst s t)
        (normalizedLatitudeGapDstt s t) +
    latitudeJetMul3D2
      (latitudePower α s t) (latitudePowerDt α s t)
        (latitudePowerDtt α s t)
      (latitudeCusp2 α s t) (latitudeCusp2Dt α s t)
        (latitudeCusp2Dtt α s t)
      (normalizedLatitudeGapDs s t ^ 2)
        (2 * normalizedLatitudeGapDs s t *
          normalizedLatitudeGapDst s t)
        (2 * normalizedLatitudeGapDst s t ^ 2 +
          2 * normalizedLatitudeGapDs s t *
            normalizedLatitudeGapDstt s t) +
    latitudeJetMul3D2
      (latitudePower α s t) (latitudePowerDt α s t)
        (latitudePowerDtt α s t)
      (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
        (latitudeCusp1Dtt α s t)
      (normalizedLatitudeGapDss s t) (normalizedLatitudeGapDsst s t)
        (normalizedLatitudeGapDsstt s t)

/-- First derivative in the second height variable after taking the two
first-height derivatives of the actual variable-coefficient kernel. -/
theorem hasDerivAt_variableReducedLatitudeKernelDss_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ variableReducedLatitudeKernelDss α s y)
      (variableReducedLatitudeKernelDsst α s t) t := by
  have hP := hasDerivAt_latitudePower_right (α := α) hs ht
  have hPs := hasDerivAt_latitudePowerDs_right (α := α) hs ht
  have hPss := hasDerivAt_latitudePowerDss_right (α := α) hs ht
  have hH0 := hasDerivAt_latitudeCusp0_right (α := α) hs ht hst
  have hH1 := hasDerivAt_latitudeCusp1_right (α := α) hs ht hst
  have hH2 := hasDerivAt_latitudeCusp2_right (α := α) hs ht hst
  have hQs := hasDerivAt_normalizedLatitudeGapDs_right hs ht
  have hQss := hasDerivAt_normalizedLatitudeGapDss_right hs ht
  have htwo :
      HasDerivAt (fun _y : ℝ ↦ (2 : ℝ)) 0 t := hasDerivAt_const t 2
  have hterm1 := hPss.mul hH0
  have hterm2 := ((htwo.mul hPs).mul hH1).mul hQs
  have hterm3 := (hP.mul hH2).mul (hQs.pow 2)
  have hterm4 := (hP.mul hH1).mul hQss
  change HasDerivAt
    (fun y ↦
      latitudePowerDss α s y * latitudeCusp0 α s y +
      2 * latitudePowerDs α s y * latitudeCusp1 α s y *
        normalizedLatitudeGapDs s y +
      latitudePower α s y *
        (latitudeCusp2 α s y * normalizedLatitudeGapDs s y ^ 2 +
          latitudeCusp1 α s y * normalizedLatitudeGapDss s y))
    (variableReducedLatitudeKernelDsst α s t) t
  unfold variableReducedLatitudeKernelDsst latitudeJetMulD1
    latitudeJetMul3D1
  convert ((hterm1.add hterm2).add hterm3).add hterm4 using 1 <;> ring

/-- The genuine mixed `(2,2)` derivative chain for
`p(s,t)^(α/2) hα(q(s,t))`, hence for `latitudeKernel` on every interior
off-diagonal point. -/
theorem hasDerivAt_variableReducedLatitudeKernelDsst_right
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ variableReducedLatitudeKernelDsst α s y)
      (variableReducedLatitudeKernelDsstt α s t) t := by
  have hP := hasDerivAt_latitudePower_right (α := α) hs ht
  have hPt := hasDerivAt_latitudePowerDt_right (α := α) hs ht
  have hPs := hasDerivAt_latitudePowerDs_right (α := α) hs ht
  have hPst := hasDerivAt_latitudePowerDst_right (α := α) hs ht
  have hPss := hasDerivAt_latitudePowerDss_right (α := α) hs ht
  have hPsst := hasDerivAt_latitudePowerDsst_right (α := α) hs ht
  have hH0 := hasDerivAt_latitudeCusp0_right (α := α) hs ht hst
  have hH0t := hasDerivAt_latitudeCusp0Dt_right (α := α) hs ht hst
  have hH1 := hasDerivAt_latitudeCusp1_right (α := α) hs ht hst
  have hH1t := hasDerivAt_latitudeCusp1Dt_right (α := α) hs ht hst
  have hH2 := hasDerivAt_latitudeCusp2_right (α := α) hs ht hst
  have hH2t := hasDerivAt_latitudeCusp2Dt_right (α := α) hs ht hst
  have hQs := hasDerivAt_normalizedLatitudeGapDs_right hs ht
  have hQst := hasDerivAt_normalizedLatitudeGapDst_right hs ht
  have hQss := hasDerivAt_normalizedLatitudeGapDss_right hs ht
  have hQsst := hasDerivAt_normalizedLatitudeGapDsst_right hs ht
  have hQsSq :
      HasDerivAt (fun y ↦ normalizedLatitudeGapDs s y ^ 2)
        (2 * normalizedLatitudeGapDs s t *
          normalizedLatitudeGapDst s t) t := by
    convert hQs.pow 2 using 1 <;> ring
  have hQsSqD :
      HasDerivAt
        (fun y ↦ 2 * normalizedLatitudeGapDs s y *
          normalizedLatitudeGapDst s y)
        (2 * normalizedLatitudeGapDst s t ^ 2 +
          2 * normalizedLatitudeGapDs s t *
            normalizedLatitudeGapDstt s t) t := by
    convert ((hasDerivAt_const t 2).mul hQs).mul hQst using 1 <;> ring
  have hterm1 :=
    hasDerivAt_latitudeJetMulD1 hPss hPsst hH0 hH0t
  have hterm2 :=
    hasDerivAt_latitudeJetMul3D1 hPs hPst hH1 hH1t hQs hQst
  have hterm3 :=
    hasDerivAt_latitudeJetMul3D1 hP hPt hH2 hH2t hQsSq hQsSqD
  have hterm4 :=
    hasDerivAt_latitudeJetMul3D1 hP hPt hH1 hH1t hQss hQsst
  unfold variableReducedLatitudeKernelDsst
    variableReducedLatitudeKernelDsstt
  convert
    ((hterm1.add ((hasDerivAt_const t 2).mul hterm2)).add hterm3).add
      hterm4 using 1 <;> ring

end BEMOC
