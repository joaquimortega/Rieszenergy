import BEMOCFormalization.ReducedCuspQuadratic

/-!
# Derivative bounds for the variable latitude coefficients

This file supplies the explicit off-pole calculus for
`ρ(s) = sqrt (1-s²)` and the angular scale `p(s,t)=2ρ(s)ρ(t)`.
The hypotheses are phrased in terms of a common nonpolar radius floor `R`;
they are the local assumptions available on a comparable nonpolar block.
-/

open Set

namespace BEMOC

noncomputable def heightRadius (s : ℝ) : ℝ :=
  Real.sqrt (1 - s ^ 2)

noncomputable def heightRadiusD1 (s : ℝ) : ℝ :=
  -s / heightRadius s

noncomputable def heightRadiusD2 (s : ℝ) : ℝ :=
  -1 / heightRadius s ^ 3

theorem heightRadius_eq (s : ℝ) :
    heightRadius s = Real.sqrt (1 - s ^ 2) := rfl

theorem heightRadius_pos {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    0 < heightRadius s := by
  unfold heightRadius
  apply Real.sqrt_pos.2
  nlinarith [hs.1, hs.2]

theorem heightRadius_sq {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    heightRadius s ^ 2 = 1 - s ^ 2 := by
  unfold heightRadius
  rw [Real.sq_sqrt]
  nlinarith [hs.1, hs.2]

theorem heightRadius_le_one {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    heightRadius s ≤ 1 := by
  have hsq := heightRadius_sq hs
  have hnonneg : 0 ≤ heightRadius s := by
    unfold heightRadius
    positivity
  nlinarith [sq_nonneg s]

theorem hasDerivAt_heightRadius
    {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt heightRadius (heightRadiusD1 s) s := by
  have hbase : 1 - s ^ 2 ≠ 0 := by
    nlinarith [hs.1, hs.2]
  have hinner :
      HasDerivAt (fun y : ℝ ↦ 1 - y ^ 2) (-2 * s) s := by
    convert (hasDerivAt_const s 1).sub (hasDerivAt_pow 2 s) using 1 <;> ring
  unfold heightRadiusD1
  unfold heightRadius
  convert (Real.hasDerivAt_sqrt hbase).comp s hinner using 1
  have hr : Real.sqrt (1 - s ^ 2) ≠ 0 := by
    apply (Real.sqrt_pos.2 ?_).ne'
    nlinarith [hs.1, hs.2]
  field_simp [hr]
  ring

theorem hasDerivAt_heightRadiusD1
    {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt heightRadiusD1 (heightRadiusD2 s) s := by
  have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have hrpos := heightRadius_pos hs
  have hrne : heightRadius s ≠ 0 := hrpos.ne'
  have hrad := hasDerivAt_heightRadius hs
  rw [heightRadiusD1] at hrad
  unfold heightRadiusD1 heightRadiusD2
  convert (hasDerivAt_id s).neg.div hrad hrne using 1
  have hr2 := heightRadius_sq hs'
  have hone : heightRadius s ^ 2 + s ^ 2 = 1 := by
    nlinarith [hr2]
  have hmul := congrArg
    (fun z : ℝ ↦ z * heightRadius s ^ 3) hone
  field_simp [hrne]
  ring_nf at hmul ⊢
  nlinarith

/-- Quantitative radius derivative bounds under a radius floor. -/
theorem abs_heightRadiusD1_le
    {s R : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (hR : 0 < R) (hfloor : R ≤ heightRadius s) :
    |heightRadiusD1 s| ≤ R⁻¹ := by
  have hsabs : |s| ≤ 1 := abs_le.mpr hs
  have hrpos : 0 < heightRadius s := hR.trans_le hfloor
  unfold heightRadiusD1
  rw [abs_div, abs_neg]
  calc
    |s| / |heightRadius s| ≤ 1 / heightRadius s := by
      rw [abs_of_pos hrpos]
      exact div_le_div_of_nonneg_right hsabs hrpos.le
    _ ≤ 1 / R := one_div_le_one_div_of_le hR hfloor
    _ = R⁻¹ := one_div _

theorem abs_heightRadiusD2_le
    {s R : ℝ} (hR : 0 < R) (hfloor : R ≤ heightRadius s) :
    |heightRadiusD2 s| ≤ R⁻¹ ^ 3 := by
  have hrpos : 0 < heightRadius s := hR.trans_le hfloor
  unfold heightRadiusD2
  rw [abs_div, abs_neg, abs_one, abs_pow, abs_of_pos hrpos]
  have hinv : (heightRadius s)⁻¹ ≤ R⁻¹ :=
    (inv_le_inv₀ hrpos hR).2 hfloor
  simpa [one_div, inv_pow] using
    (pow_le_pow_left₀ (inv_nonneg.mpr hrpos.le) hinv 3)

/-- The angular scale rewritten through the local radius notation. -/
theorem latitudeAngularScale_eq_heightRadius (s t : ℝ) :
    latitudeAngularScale s t = 2 * heightRadius s * heightRadius t := rfl

noncomputable def latitudeAngularScaleDs (s t : ℝ) : ℝ :=
  2 * heightRadiusD1 s * heightRadius t

noncomputable def latitudeAngularScaleDss (s t : ℝ) : ℝ :=
  2 * heightRadiusD2 s * heightRadius t

noncomputable def latitudeAngularScaleDst (s t : ℝ) : ℝ :=
  2 * heightRadiusD1 s * heightRadiusD1 t

noncomputable def latitudeAngularScaleDsst (s t : ℝ) : ℝ :=
  2 * heightRadiusD2 s * heightRadiusD1 t

noncomputable def latitudeAngularScaleDsstt (s t : ℝ) : ℝ :=
  2 * heightRadiusD2 s * heightRadiusD2 t

theorem hasDerivAt_latitudeAngularScale_left
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudeAngularScale y t)
      (latitudeAngularScaleDs s t) s := by
  unfold latitudeAngularScale latitudeAngularScaleDs heightRadius
  convert
    ((hasDerivAt_const s 2).mul (hasDerivAt_heightRadius hs)).mul_const
      (Real.sqrt (1 - t ^ 2)) using 1 <;> ring

theorem hasDerivAt_latitudeAngularScaleDs_left
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudeAngularScaleDs y t)
      (latitudeAngularScaleDss s t) s := by
  unfold latitudeAngularScaleDs latitudeAngularScaleDss
  convert
    ((hasDerivAt_const s 2).mul
      (hasDerivAt_heightRadiusD1 hs)).mul_const (heightRadius t) using 1 <;>
    ring

theorem hasDerivAt_latitudeAngularScaleDss_right
    {s t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudeAngularScaleDss s y)
      (latitudeAngularScaleDsst s t) t := by
  unfold latitudeAngularScaleDss latitudeAngularScaleDsst
  convert
    (hasDerivAt_const t (2 * heightRadiusD2 s)).mul
      (hasDerivAt_heightRadius ht) using 1 <;> ring

theorem hasDerivAt_latitudeAngularScaleDsst_right
    {s t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ latitudeAngularScaleDsst s y)
      (latitudeAngularScaleDsstt s t) t := by
  unfold latitudeAngularScaleDsst latitudeAngularScaleDsstt
  convert
    (hasDerivAt_const t (2 * heightRadiusD2 s)).mul
      (hasDerivAt_heightRadiusD1 ht) using 1 <;> ring

/-- Mixed `(2,2)` coefficient bound for the angular scale. -/
theorem abs_latitudeAngularScaleDsstt_le
    {s t R : ℝ} (hR : 0 < R)
    (hsfloor : R ≤ heightRadius s) (htfloor : R ≤ heightRadius t) :
    |latitudeAngularScaleDsstt s t| ≤ 2 * R⁻¹ ^ 6 := by
  have hs := abs_heightRadiusD2_le hR hsfloor
  have ht := abs_heightRadiusD2_le hR htfloor
  unfold latitudeAngularScaleDsstt
  rw [abs_mul, abs_mul]
  norm_num
  calc
    2 * |heightRadiusD2 s| * |heightRadiusD2 t| ≤
        2 * (R⁻¹ ^ 3) * (R⁻¹ ^ 3) := by
      gcongr
    _ = 2 * R⁻¹ ^ 6 := by ring
    _ = 2 * (R ^ 6)⁻¹ := by rw [inv_pow]

theorem abs_latitudeAngularScaleDss_le
    {s t R : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (hR : 0 < R) (hsfloor : R ≤ heightRadius s) :
    |latitudeAngularScaleDss s t| ≤ 2 * R⁻¹ ^ 3 := by
  have hs := abs_heightRadiusD2_le hR hsfloor
  have ht0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
  have ht1 := heightRadius_le_one ht
  unfold latitudeAngularScaleDss
  rw [abs_mul, abs_mul, abs_of_nonneg ht0]
  norm_num
  rw [← inv_pow]
  calc
    2 * |heightRadiusD2 s| * heightRadius t ≤
        2 * (R⁻¹ ^ 3) * 1 := by gcongr
    _ = 2 * R⁻¹ ^ 3 := by ring

theorem abs_latitudeAngularScaleDsst_le
    {s t R : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (hR : 0 < R) (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t) :
    |latitudeAngularScaleDsst s t| ≤ 2 * R⁻¹ ^ 4 := by
  have hs := abs_heightRadiusD2_le hR hsfloor
  have ht := abs_heightRadiusD1_le ht hR htfloor
  unfold latitudeAngularScaleDsst
  rw [abs_mul, abs_mul]
  norm_num
  rw [← inv_pow]
  calc
    2 * |heightRadiusD2 s| * |heightRadiusD1 t| ≤
        2 * (R⁻¹ ^ 3) * R⁻¹ := by gcongr
    _ = 2 * R⁻¹ ^ 4 := by ring

/-- Normalized radial gap `q/p` in a form with explicit height
coefficients. -/
noncomputable def normalizedLatitudeGap (s t : ℝ) : ℝ :=
  (1 - s * t) / (heightRadius s * heightRadius t) - 1

theorem normalizedLatitudeGap_eq
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    normalizedLatitudeGap s t =
      latitudeRadialGapSq s t / latitudeAngularScale s t := by
  have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hrs : heightRadius s ≠ 0 := (heightRadius_pos hs).ne'
  have hrt : heightRadius t ≠ 0 := (heightRadius_pos ht).ne'
  have hsqr := heightRadius_sq hs'
  have htqr := heightRadius_sq ht'
  unfold normalizedLatitudeGap latitudeAngularScale latitudeRadialGapSq
  change
    (1 - s * t) / (heightRadius s * heightRadius t) - 1 =
      ((s - t) ^ 2 + (heightRadius s - heightRadius t) ^ 2) /
        (2 * heightRadius s * heightRadius t)
  field_simp [hrs, hrt]
  nlinarith

/-- The scaled cusp normal form expressed entirely through the explicit
height coefficients of this module. -/
theorem latitudeKernel_eq_heightScale_mul_reducedCusp
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    latitudeKernel α s t =
      latitudeAngularScale s t ^ (α / 2) *
        reducedLatitudeCusp α (normalizedLatitudeGap s t) := by
  rw [latitudeKernel_eq_scale_mul_reducedCusp hs ht,
    normalizedLatitudeGap_eq hs ht]

noncomputable def normalizedLatitudeGapDs (s t : ℝ) : ℝ :=
  (s - t) / (heightRadius s ^ 3 * heightRadius t)

noncomputable def normalizedLatitudeGapDss (s t : ℝ) : ℝ :=
  (heightRadius s ^ 2 + 3 * s * (s - t)) /
    (heightRadius s ^ 5 * heightRadius t)

noncomputable def normalizedLatitudeGapDsst (s t : ℝ) : ℝ :=
  t / (heightRadius s ^ 3 * heightRadius t ^ 3) -
    3 * s * (1 - s * t) /
      (heightRadius s ^ 5 * heightRadius t ^ 3)

noncomputable def normalizedLatitudeGapDsstt (s t : ℝ) : ℝ :=
  (heightRadius t ^ 2 + 3 * t ^ 2) /
      (heightRadius s ^ 3 * heightRadius t ^ 5) +
    3 * s ^ 2 /
      (heightRadius s ^ 5 * heightRadius t ^ 3) -
    9 * s * t * (1 - s * t) /
      (heightRadius s ^ 5 * heightRadius t ^ 5)

/-- First height derivative of the normalized radial gap. -/
theorem hasDerivAt_normalizedLatitudeGap_left
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ normalizedLatitudeGap y t)
      (normalizedLatitudeGapDs s t) s := by
  have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have hrs : heightRadius s ≠ 0 := (heightRadius_pos hs).ne'
  have hrt : heightRadius t ≠ 0 := (heightRadius_pos ht).ne'
  have hrsq := heightRadius_sq hs'
  unfold normalizedLatitudeGap normalizedLatitudeGapDs
  convert
    (((hasDerivAt_const s 1).sub
        ((hasDerivAt_id s).mul_const t)).div
      ((hasDerivAt_heightRadius hs).mul_const (heightRadius t))
      (mul_ne_zero hrs hrt)).sub_const 1 using 1
  have hmul := congrArg
    (fun z : ℝ ↦ z * heightRadius s ^ 3 * t * heightRadius t ^ 2) hrsq
  unfold heightRadiusD1
  field_simp [hrs, hrt]
  ring_nf at hmul ⊢
  nlinarith

/-- Second derivative in the first height variable. -/
theorem hasDerivAt_normalizedLatitudeGapDs_left
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ normalizedLatitudeGapDs y t)
      (normalizedLatitudeGapDss s t) s := by
  have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have hrs : heightRadius s ≠ 0 := (heightRadius_pos hs).ne'
  have hrt : heightRadius t ≠ 0 := (heightRadius_pos ht).ne'
  have hrsq := heightRadius_sq hs'
  have hden :
      HasDerivAt (fun y ↦ heightRadius y ^ 3 * heightRadius t)
        (3 * heightRadius s ^ 2 * heightRadiusD1 s *
          heightRadius t) s := by
    convert
      ((hasDerivAt_heightRadius hs).pow 3).mul_const
        (heightRadius t) using 1 <;> ring
  unfold normalizedLatitudeGapDs normalizedLatitudeGapDss
  convert
    (((hasDerivAt_id s).sub_const t).div hden
      (mul_ne_zero (pow_ne_zero 3 hrs) hrt)) using 1
  unfold heightRadiusD1
  field_simp [hrs, hrt]
  ring_nf at hrsq ⊢

/-- The first derivative in the second height variable after differentiating
twice in the first variable. -/
theorem hasDerivAt_normalizedLatitudeGapDss_right
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ normalizedLatitudeGapDss s y)
      (normalizedLatitudeGapDsst s t) t := by
  have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hrs : heightRadius s ≠ 0 := (heightRadius_pos hs).ne'
  have hrt : heightRadius t ≠ 0 := (heightRadius_pos ht).ne'
  have hrsq := heightRadius_sq hs'
  have hrtsq := heightRadius_sq ht'
  have hnum :
      HasDerivAt
        (fun y ↦ heightRadius s ^ 2 + 3 * s * (s - y))
        (-3 * s) t := by
    convert
      (hasDerivAt_const t (heightRadius s ^ 2)).add
        ((hasDerivAt_const t (3 * s)).mul
          ((hasDerivAt_const t s).sub (hasDerivAt_id t))) using 1 <;>
      ring
  have hden :
      HasDerivAt (fun y ↦ heightRadius s ^ 5 * heightRadius y)
        (heightRadius s ^ 5 * heightRadiusD1 t) t := by
    convert
      (hasDerivAt_const t (heightRadius s ^ 5)).mul
        (hasDerivAt_heightRadius ht) using 1 <;> ring
  unfold normalizedLatitudeGapDss normalizedLatitudeGapDsst
  convert hnum.div hden (mul_ne_zero (pow_ne_zero 5 hrs) hrt) using 1
  have hmul := congrArg
    (fun z : ℝ ↦ z * heightRadius s ^ 13 * s *
      heightRadius t ^ 6 * 3) hrtsq
  unfold heightRadiusD1
  field_simp [hrs, hrt]
  ring_nf at hrsq hmul ⊢
  nlinarith

/-- The mixed `(2,2)` height derivative of the normalized radial gap. -/
theorem hasDerivAt_normalizedLatitudeGapDsst_right
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ normalizedLatitudeGapDsst s y)
      (normalizedLatitudeGapDsstt s t) t := by
  have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hrs : heightRadius s ≠ 0 := (heightRadius_pos hs).ne'
  have hrt : heightRadius t ≠ 0 := (heightRadius_pos ht).ne'
  have hrtsq := heightRadius_sq ht'
  have hpow :
      HasDerivAt (fun y ↦ heightRadius y ^ 3)
        (3 * heightRadius t ^ 2 * heightRadiusD1 t) t := by
    convert (hasDerivAt_heightRadius ht).pow 3 using 1 <;> ring
  have hden3 :
      HasDerivAt (fun y ↦ heightRadius s ^ 3 * heightRadius y ^ 3)
        (heightRadius s ^ 3 *
          (3 * heightRadius t ^ 2 * heightRadiusD1 t)) t := by
    convert (hasDerivAt_const t (heightRadius s ^ 3)).mul hpow using 1 <;>
      ring
  have hden5 :
      HasDerivAt (fun y ↦ heightRadius s ^ 5 * heightRadius y ^ 3)
        (heightRadius s ^ 5 *
          (3 * heightRadius t ^ 2 * heightRadiusD1 t)) t := by
    convert (hasDerivAt_const t (heightRadius s ^ 5)).mul hpow using 1 <;>
      ring
  have hfirst :
      HasDerivAt
        (fun y ↦ y / (heightRadius s ^ 3 * heightRadius y ^ 3))
        ((heightRadius s ^ 3 * heightRadius t ^ 3 -
            t * (heightRadius s ^ 3 *
              (3 * heightRadius t ^ 2 * heightRadiusD1 t))) /
          (heightRadius s ^ 3 * heightRadius t ^ 3) ^ 2) t := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id t).div hden3
        (mul_ne_zero (pow_ne_zero 3 hrs) (pow_ne_zero 3 hrt))
  have hnum :
      HasDerivAt (fun y ↦ 1 - s * y) (-s) t := by
    convert (hasDerivAt_const t 1).sub
      ((hasDerivAt_const t s).mul (hasDerivAt_id t)) using 1 <;> ring
  have hquot :
      HasDerivAt
        (fun y ↦ (1 - s * y) /
          (heightRadius s ^ 5 * heightRadius y ^ 3))
        (((-s) * (heightRadius s ^ 5 * heightRadius t ^ 3) -
            (1 - s * t) * (heightRadius s ^ 5 *
              (3 * heightRadius t ^ 2 * heightRadiusD1 t))) /
          (heightRadius s ^ 5 * heightRadius t ^ 3) ^ 2) t := by
    convert hnum.div hden5
      (mul_ne_zero (pow_ne_zero 5 hrs) (pow_ne_zero 3 hrt)) using 1
  have hsecond :
      HasDerivAt
        (fun y ↦ 3 * s * ((1 - s * y) /
          (heightRadius s ^ 5 * heightRadius y ^ 3)))
        (3 * s *
          (((-s) * (heightRadius s ^ 5 * heightRadius t ^ 3) -
              (1 - s * t) * (heightRadius s ^ 5 *
                (3 * heightRadius t ^ 2 * heightRadiusD1 t))) /
            (heightRadius s ^ 5 * heightRadius t ^ 3) ^ 2)) t := by
    convert (hasDerivAt_const t (3 * s)).mul hquot using 1 <;> ring
  unfold normalizedLatitudeGapDsst normalizedLatitudeGapDsstt
  convert hfirst.sub hsecond using 1
  · funext y
    ring
  · unfold heightRadiusD1
    field_simp [hrs, hrt]
    ring_nf at hrtsq ⊢

/-- A reusable denominator estimate for products of powers under a common
positive lower bound. -/
theorem abs_div_pow_mul_pow_le
    {z C x y R : ℝ} {m n : ℕ}
    (hC : 0 ≤ C) (hz : |z| ≤ C) (hR : 0 < R)
    (hx : R ≤ x) (hy : R ≤ y) :
    |z / (x ^ m * y ^ n)| ≤ C * R⁻¹ ^ (m + n) := by
  have hx0 : 0 < x := hR.trans_le hx
  have hy0 : 0 < y := hR.trans_le hy
  have hden0 : 0 < x ^ m * y ^ n := mul_pos (pow_pos hx0 _) (pow_pos hy0 _)
  have hRpow0 : 0 < R ^ (m + n) := pow_pos hR _
  have hdenLower : R ^ (m + n) ≤ x ^ m * y ^ n := by
    rw [pow_add]
    exact mul_le_mul
      (pow_le_pow_left₀ hR.le hx m)
      (pow_le_pow_left₀ hR.le hy n)
      (pow_nonneg hR.le _) (pow_nonneg hx0.le _)
  rw [abs_div, abs_of_pos hden0, div_eq_mul_inv]
  calc
    |z| * (x ^ m * y ^ n)⁻¹ ≤
        C * (x ^ m * y ^ n)⁻¹ := by
      gcongr
    _ ≤ C * (R ^ (m + n))⁻¹ := by
      gcongr
    _ = C * R⁻¹ ^ (m + n) := by
      rw [inv_pow]

/-- Quantitative first derivative bound for the normalized gap. -/
theorem abs_normalizedLatitudeGapDs_le
    {s t R : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) (hR : 0 < R)
    (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t) :
    |normalizedLatitudeGapDs s t| ≤ 2 * R⁻¹ ^ 4 := by
  have hz : |s - t| ≤ 2 := by
    exact (abs_sub s t).trans (by
      have hs' : |s| ≤ 1 := abs_le.mpr hs
      have ht' : |t| ≤ 1 := abs_le.mpr ht
      linarith)
  unfold normalizedLatitudeGapDs
  simpa using
    (abs_div_pow_mul_pow_le (m := 3) (n := 1)
      (by norm_num) hz hR hsfloor htfloor)

/-- Quantitative second derivative bound for the normalized gap. -/
theorem abs_normalizedLatitudeGapDss_le
    {s t R : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) (hR : 0 < R)
    (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t) :
    |normalizedLatitudeGapDss s t| ≤ 7 * R⁻¹ ^ 6 := by
  have hsabs : |s| ≤ 1 := abs_le.mpr hs
  have hst : |s - t| ≤ 2 := by
    exact (abs_sub s t).trans (by
      have ht' : |t| ≤ 1 := abs_le.mpr ht
      linarith)
  have hrsq := heightRadius_sq hs
  have hrsqle : |heightRadius s ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _), hrsq]
    nlinarith [sq_nonneg s]
  have hprod : |3 * s * (s - t)| ≤ 6 := by
    rw [abs_mul, abs_mul]
    norm_num
    calc
      3 * |s| * |s - t| ≤ 3 * 1 * 2 := by gcongr
      _ = 6 := by norm_num
  have hz : |heightRadius s ^ 2 + 3 * s * (s - t)| ≤ 7 :=
    (abs_add _ _).trans (by linarith)
  unfold normalizedLatitudeGapDss
  simpa using
    (abs_div_pow_mul_pow_le (m := 5) (n := 1)
      (by norm_num) hz hR hsfloor htfloor)

/-- Quantitative mixed `(2,1)` derivative bound for the normalized gap. -/
theorem abs_normalizedLatitudeGapDsst_le
    {s t R : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) (hR : 0 < R)
    (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t) :
    |normalizedLatitudeGapDsst s t| ≤
      R⁻¹ ^ 6 + 6 * R⁻¹ ^ 8 := by
  have hsabs : |s| ≤ 1 := abs_le.mpr hs
  have htabs : |t| ≤ 1 := abs_le.mpr ht
  have hst : |s * t| ≤ 1 := by
    rw [abs_mul]
    calc
      |s| * |t| ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hone : |1 - s * t| ≤ 2 :=
    (abs_sub _ _).trans (by norm_num at hst ⊢; linarith)
  have hnum : |3 * s * (1 - s * t)| ≤ 6 := by
    rw [abs_mul, abs_mul]
    norm_num
    calc
      3 * |s| * |1 - s * t| ≤ 3 * 1 * 2 := by gcongr
      _ = 6 := by norm_num
  have h1 := abs_div_pow_mul_pow_le (m := 3) (n := 3)
    (z := t) (C := 1) (x := heightRadius s) (y := heightRadius t)
    (R := R) (by norm_num) htabs hR hsfloor htfloor
  have h2 := abs_div_pow_mul_pow_le (m := 5) (n := 3)
    (z := 3 * s * (1 - s * t)) (C := 6)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (by norm_num) hnum hR hsfloor htfloor
  unfold normalizedLatitudeGapDsst
  exact (abs_sub _ _).trans (by linarith)

/-- Explicit off-pole bound for the mixed `(2,2)` normalized-gap
coefficient.  The three displayed terms retain their separate denominator
orders, which is useful before choosing a particular radius scale. -/
theorem abs_normalizedLatitudeGapDsstt_le
    {s t R : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) (hR : 0 < R)
    (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t) :
    |normalizedLatitudeGapDsstt s t| ≤
      4 * R⁻¹ ^ 8 + 3 * R⁻¹ ^ 8 + 18 * R⁻¹ ^ 10 := by
  have hsabs : |s| ≤ 1 := abs_le.mpr hs
  have htabs : |t| ≤ 1 := abs_le.mpr ht
  have htRadiusSq := heightRadius_sq ht
  have hnum1 : |heightRadius t ^ 2 + 3 * t ^ 2| ≤ 4 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg t]
  have hnum2 : |3 * s ^ 2| ≤ 3 := by
    rw [abs_mul, abs_of_nonneg (by norm_num), abs_pow]
    calc
      3 * |s| ^ 2 ≤ 3 * 1 ^ 2 := by
        gcongr
      _ = 3 := by norm_num
  have hst : |s * t| ≤ 1 := by
    rw [abs_mul]
    calc
      |s| * |t| ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hone : |1 - s * t| ≤ 2 := by
    calc
      |1 - s * t| ≤ |(1 : ℝ)| + |s * t| := abs_sub _ _
      _ ≤ 2 := by norm_num at hst ⊢; linarith
  have hnum3 : |9 * s * t * (1 - s * t)| ≤ 18 := by
    rw [abs_mul, abs_mul, abs_mul]
    norm_num
    calc
      9 * |s| * |t| * |1 - s * t| ≤ 9 * 1 * 1 * 2 := by
        gcongr
      _ = 18 := by norm_num
  have h1 := abs_div_pow_mul_pow_le (m := 3) (n := 5)
    (z := heightRadius t ^ 2 + 3 * t ^ 2) (C := 4)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (by norm_num) hnum1 hR hsfloor htfloor
  have h2 := abs_div_pow_mul_pow_le (m := 5) (n := 3)
    (z := 3 * s ^ 2) (C := 3)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (by norm_num) hnum2 hR hsfloor htfloor
  have h3 := abs_div_pow_mul_pow_le (m := 5) (n := 5)
    (z := 9 * s * t * (1 - s * t)) (C := 18)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (by norm_num) hnum3 hR hsfloor htfloor
  unfold normalizedLatitudeGapDsstt
  calc
    |(heightRadius t ^ 2 + 3 * t ^ 2) /
          (heightRadius s ^ 3 * heightRadius t ^ 5) +
        3 * s ^ 2 / (heightRadius s ^ 5 * heightRadius t ^ 3) -
        9 * s * t * (1 - s * t) /
          (heightRadius s ^ 5 * heightRadius t ^ 5)| ≤
        |(heightRadius t ^ 2 + 3 * t ^ 2) /
          (heightRadius s ^ 3 * heightRadius t ^ 5)| +
        |3 * s ^ 2 / (heightRadius s ^ 5 * heightRadius t ^ 3)| +
        |9 * s * t * (1 - s * t) /
          (heightRadius s ^ 5 * heightRadius t ^ 5)| := by
      exact (abs_sub _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤ 4 * R⁻¹ ^ 8 + 3 * R⁻¹ ^ 8 + 18 * R⁻¹ ^ 10 := by
      norm_num at h1 h2 h3 ⊢
      linarith

end BEMOC
