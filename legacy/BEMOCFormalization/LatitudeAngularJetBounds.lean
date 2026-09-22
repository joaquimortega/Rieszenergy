import BEMOCFormalization.LatitudeVariableMixedDerivative

/-!
# Quantitative bounds for the angular-scale jet

On a nonpolar latitude rectangle both radii have a common positive lower
bound `R`.  This file records a uniform bound for every derivative of

`p(s,t) = 2 * sqrt (1-s²) * sqrt (1-t²)`

which occurs in the mixed `(2,2)` derivative of `p^(α/2) h(q)`.
The powers are deliberately not optimized; what matters is that a height
derivative in one variable has the correct `R⁻¹`/`R⁻³` cost.
-/

open Set

namespace BEMOC

theorem abs_latitudeAngularScale_le_two
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    |latitudeAngularScale s t| ≤ 2 := by
  have hrs0 : 0 ≤ heightRadius s := by
    unfold heightRadius
    positivity
  have hrt0 : 0 ≤ heightRadius t := by
    unfold heightRadius
    positivity
  have hrs1 := heightRadius_le_one hs
  have hrt1 := heightRadius_le_one ht
  rw [latitudeAngularScale_eq_heightRadius, abs_mul, abs_mul,
    abs_of_nonneg hrs0, abs_of_nonneg hrt0]
  norm_num
  nlinarith

theorem two_mul_radiusFloor_sq_le_latitudeAngularScale
    {s t R : ℝ} (hR : 0 ≤ R)
    (hsfloor : R ≤ heightRadius s) (htfloor : R ≤ heightRadius t) :
    2 * R ^ 2 ≤ latitudeAngularScale s t := by
  rw [latitudeAngularScale_eq_heightRadius]
  nlinarith [mul_le_mul hsfloor htfloor hR
    (hR.trans hsfloor)]

theorem abs_latitudeAngularScaleDs_le
    {s t R : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) (hR : 0 < R)
    (hsfloor : R ≤ heightRadius s) :
    |latitudeAngularScaleDs s t| ≤ 2 * R⁻¹ := by
  have hds := abs_heightRadiusD1_le hs hR hsfloor
  have hrt0 : 0 ≤ heightRadius t := by
    unfold heightRadius
    positivity
  have hrt1 := heightRadius_le_one ht
  unfold latitudeAngularScaleDs
  rw [abs_mul, abs_mul, abs_of_nonneg hrt0]
  norm_num
  nlinarith [inv_nonneg.mpr hR.le]

theorem abs_latitudeAngularScaleDt_le
    {s t R : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) (hR : 0 < R)
    (htfloor : R ≤ heightRadius t) :
    |latitudeAngularScaleDt s t| ≤ 2 * R⁻¹ := by
  unfold latitudeAngularScaleDt
  simpa [latitudeAngularScaleDs, mul_comm] using
    (abs_latitudeAngularScaleDs_le ht hs hR htfloor)

theorem abs_latitudeAngularScaleDtt_le
    {s t R : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (hR : 0 < R) (htfloor : R ≤ heightRadius t) :
    |latitudeAngularScaleDtt s t| ≤ 2 * R⁻¹ ^ 3 := by
  unfold latitudeAngularScaleDtt
  simpa [latitudeAngularScaleDss, mul_comm] using
    (abs_latitudeAngularScaleDss_le hs hR htfloor)

theorem abs_latitudeAngularScaleDst_le
    {s t R : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) (hR : 0 < R)
    (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t) :
    |latitudeAngularScaleDst s t| ≤ 2 * R⁻¹ ^ 2 := by
  have hds := abs_heightRadiusD1_le hs hR hsfloor
  have hdt := abs_heightRadiusD1_le ht hR htfloor
  unfold latitudeAngularScaleDst
  rw [abs_mul, abs_mul]
  norm_num
  calc
    2 * |heightRadiusD1 s| * |heightRadiusD1 t| ≤
        2 * R⁻¹ * R⁻¹ := by gcongr
    _ = 2 * (R ^ 2)⁻¹ := by
      rw [← inv_pow]
      ring

theorem abs_latitudeAngularScaleDstt_le
    {s t R : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (hR : 0 < R) (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t) :
    |latitudeAngularScaleDstt s t| ≤ 2 * R⁻¹ ^ 4 := by
  unfold latitudeAngularScaleDstt
  simpa [latitudeAngularScaleDsst, mul_comm] using
    (abs_latitudeAngularScaleDsst_le hs hR htfloor hsfloor)

/-- On a comparable-radius rectangle the unused radius factor restores the
sharp scale: a first derivative of `p` is bounded independently of `R`. -/
theorem abs_latitudeAngularScaleDs_le_of_radius_ceiling
    {s t R K : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (hR : 0 < R) (_hK : 0 ≤ K)
    (hsfloor : R ≤ heightRadius s)
    (htceiling : heightRadius t ≤ K * R) :
    |latitudeAngularScaleDs s t| ≤ 2 * K := by
  have hds := abs_heightRadiusD1_le hs hR hsfloor
  have hrt0 : 0 ≤ heightRadius t := by
    unfold heightRadius
    positivity
  unfold latitudeAngularScaleDs
  rw [abs_mul, abs_mul, abs_of_nonneg hrt0]
  norm_num
  calc
    2 * |heightRadiusD1 s| * heightRadius t ≤
        2 * R⁻¹ * (K * R) := by gcongr
    _ = 2 * K := by
      field_simp [hR.ne']
      ring

/-- Sharp comparable-radius scale for a pure second derivative of `p`. -/
theorem abs_latitudeAngularScaleDss_le_of_radius_ceiling
    {s t R K : ℝ} (hR : 0 < R) (_hK : 0 ≤ K)
    (hsfloor : R ≤ heightRadius s)
    (htceiling : heightRadius t ≤ K * R) :
    |latitudeAngularScaleDss s t| ≤ 2 * K * (R ^ 2)⁻¹ := by
  have hdss := abs_heightRadiusD2_le hR hsfloor
  have hrt0 : 0 ≤ heightRadius t := by
    unfold heightRadius
    positivity
  unfold latitudeAngularScaleDss
  rw [abs_mul, abs_mul, abs_of_nonneg hrt0]
  norm_num
  calc
    2 * |heightRadiusD2 s| * heightRadius t ≤
        2 * (R ^ 3)⁻¹ * (K * R) := by
      simpa using mul_le_mul
        (mul_le_mul_of_nonneg_left hdss (by norm_num))
        htceiling hrt0 (by positivity)
    _ = 2 * K * (R ^ 2)⁻¹ := by
      field_simp [hR.ne']
      ring

theorem abs_latitudeAngularScaleDt_le_of_radius_ceiling
    {s t R K : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (hR : 0 < R) (hK : 0 ≤ K)
    (htfloor : R ≤ heightRadius t)
    (hsceiling : heightRadius s ≤ K * R) :
    |latitudeAngularScaleDt s t| ≤ 2 * K := by
  unfold latitudeAngularScaleDt
  simpa [latitudeAngularScaleDs, mul_comm] using
    (abs_latitudeAngularScaleDs_le_of_radius_ceiling
      ht hR hK htfloor hsceiling)

theorem abs_latitudeAngularScaleDtt_le_of_radius_ceiling
    {s t R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    (htfloor : R ≤ heightRadius t)
    (hsceiling : heightRadius s ≤ K * R) :
    |latitudeAngularScaleDtt s t| ≤ 2 * K * (R ^ 2)⁻¹ := by
  unfold latitudeAngularScaleDtt
  simpa [latitudeAngularScaleDss, mul_comm] using
    (abs_latitudeAngularScaleDss_le_of_radius_ceiling
      hR hK htfloor hsceiling)

end BEMOC
