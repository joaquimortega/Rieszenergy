import BEMOCFormalization.LatitudeNeighboringRegularClosure

/-! Diagonal-smooth normal form of the analytic neighboring component. -/

open Set

namespace BEMOC

noncomputable def neighboringAffineSmoothKernel
    (α H L s t : ℝ) : ℝ :=
  (H - L) * latitudePower α s t +
    2 * L * (1 - s * t) * latitudePower (α - 2) s t

noncomputable def neighboringAffineSmoothKernelDsstt
    (α H L s t : ℝ) : ℝ :=
  (H - L) * latitudePowerDsstt α s t +
    2 * L *
      ((1 - s * t) * latitudePowerDsstt (α - 2) s t -
        2 * s * latitudePowerDsst (α - 2) s t -
        4 * latitudePowerDst (α - 2) s t -
        2 * t * latitudePowerDstt (α - 2) s t)

/-- A uniform algebraic bound for the diagonal-valid mixed derivative.
The formula is just Leibniz' rule applied to the manifestly smooth normal
form above. -/
theorem abs_neighboringAffineSmoothKernelDsstt_le
    {α H L s t P Q : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hP : LatitudePowerJetBound α s t P)
    (hQ : LatitudePowerJetBound (α - 2) s t Q) :
    |neighboringAffineSmoothKernelDsstt α H L s t| ≤
      |H - L| * P + 20 * |L| * Q := by
  rcases hP with ⟨hP0, _, _, _, _, _, _, _, _, hPsstt⟩
  rcases hQ with
    ⟨hQ0, _, _, _, _, hQst, hQstt, _, hQsst, hQsstt⟩
  have hsabs : |s| ≤ 1 := abs_le.mpr hs
  have htabs : |t| ≤ 1 := abs_le.mpr ht
  have hg : |1 - s * t| ≤ 2 := by
    have hst : |s * t| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg s, abs_nonneg t]
    have hsum : 1 + |s * t| ≤ 2 := by linarith
    exact (abs_sub (1 : ℝ) (s * t)).trans (by simpa only [abs_one] using hsum)
  unfold neighboringAffineSmoothKernelDsstt
  calc
    |_ + _| ≤
        |(H - L) * latitudePowerDsstt α s t| +
          |2 * L *
            ((1 - s * t) * latitudePowerDsstt (α - 2) s t -
              2 * s * latitudePowerDsst (α - 2) s t -
              4 * latitudePowerDst (α - 2) s t -
              2 * t * latitudePowerDstt (α - 2) s t)| := abs_add _ _
    _ ≤ |H - L| * P + 20 * |L| * Q := by
      rw [abs_mul, abs_mul, abs_mul]
      have hinner :
          |(1 - s * t) * latitudePowerDsstt (α - 2) s t -
              2 * s * latitudePowerDsst (α - 2) s t -
              4 * latitudePowerDst (α - 2) s t -
              2 * t * latitudePowerDstt (α - 2) s t| ≤
            10 * Q := by
        calc
          |_ - _ - _ - _| ≤
              |(1 - s * t) * latitudePowerDsstt (α - 2) s t| +
                |2 * s * latitudePowerDsst (α - 2) s t| +
                |4 * latitudePowerDst (α - 2) s t| +
                |2 * t * latitudePowerDstt (α - 2) s t| := by
            have h1 := abs_sub
              ((1 - s * t) * latitudePowerDsstt (α - 2) s t -
                2 * s * latitudePowerDsst (α - 2) s t -
                4 * latitudePowerDst (α - 2) s t)
              (2 * t * latitudePowerDstt (α - 2) s t)
            have h2 := abs_sub
              ((1 - s * t) * latitudePowerDsstt (α - 2) s t -
                2 * s * latitudePowerDsst (α - 2) s t)
              (4 * latitudePowerDst (α - 2) s t)
            have h3 := abs_sub
              ((1 - s * t) * latitudePowerDsstt (α - 2) s t)
              (2 * s * latitudePowerDsst (α - 2) s t)
            linarith
          _ ≤ 2 * Q + 2 * Q + 4 * Q + 2 * Q := by
            simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
            have h1 :
                |1 - s * t| * |latitudePowerDsstt (α - 2) s t| ≤ 2 * Q :=
              mul_le_mul hg hQsstt (abs_nonneg _) (by norm_num)
            have h2 :
                2 * |s| * |latitudePowerDsst (α - 2) s t| ≤ 2 * Q := by
              nlinarith [mul_le_mul hsabs hQsst (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
            have h3 :
                4 * |latitudePowerDst (α - 2) s t| ≤ 4 * Q := by
              nlinarith
            have h4 :
                2 * |t| * |latitudePowerDstt (α - 2) s t| ≤ 2 * Q := by
              nlinarith [mul_le_mul htabs hQstt (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
            linarith
          _ = 10 * Q := by ring
      exact add_le_add
        (mul_le_mul_of_nonneg_left hPsstt (abs_nonneg _))
        (by
          calc
            |2| * |L| *
                  |(1 - s * t) * latitudePowerDsstt (α - 2) s t -
                      2 * s * latitudePowerDsst (α - 2) s t -
                      4 * latitudePowerDst (α - 2) s t -
                      2 * t * latitudePowerDstt (α - 2) s t| =
                (2 * |L|) *
                  |(1 - s * t) * latitudePowerDsstt (α - 2) s t -
                      2 * s * latitudePowerDsst (α - 2) s t -
                      4 * latitudePowerDst (α - 2) s t -
                      2 * t * latitudePowerDstt (α - 2) s t| := by norm_num
            _ ≤ (2 * |L|) * (10 * Q) :=
              mul_le_mul_of_nonneg_left hinner
                (mul_nonneg (by norm_num) (abs_nonneg L))
            _ = 20 * |L| * Q := by ring)

/-- Removing the normalized quotient exposes a manifestly smooth kernel:
the apparent `q` denominator is absorbed by one power of the positive
angular scale. -/
theorem angularScale_mul_affine_normalizedGap_eq_smooth
    {α H L s t : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1) :
    latitudeAngularScale s t ^ (α / 2) *
        (H + L * normalizedLatitudeGap s t) =
      neighboringAffineSmoothKernel α H L s t := by
  let p := latitudeAngularScale s t
  have hp : 0 < p := by
    dsimp [p, latitudeAngularScale]
    exact mul_pos (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hrs : heightRadius s ≠ 0 := (heightRadius_pos hs).ne'
  have hrt : heightRadius t ≠ 0 := (heightRadius_pos ht).ne'
  have hpow :
      p ^ (α / 2) = p ^ (α / 2 - 1) * p := by
    calc
      p ^ (α / 2) =
          p ^ ((α / 2 - 1) + 1) := by congr 1 ; ring
      _ = p ^ (α / 2 - 1) * p ^ (1 : ℝ) :=
        Real.rpow_add hp _ _
      _ = _ := by rw [Real.rpow_one]
  have hexp : (α - 2) / 2 = α / 2 - 1 := by ring
  let r := heightRadius s * heightRadius t
  have hr : r ≠ 0 := mul_ne_zero hrs hrt
  have hpr : p = 2 * r := by
    dsimp [p, r, latitudeAngularScale, heightRadius]
    ring
  unfold neighboringAffineSmoothKernel latitudePower normalizedLatitudeGap
  rw [hexp]
  change p ^ (α / 2) *
      (H + L * ((1 - s * t) / r - 1)) =
    (H - L) * p ^ (α / 2) +
      2 * L * (1 - s * t) * p ^ (α / 2 - 1)
  rw [hpow, hpr]
  field_simp [hr]
  ring

theorem neighboringUpperAnalyticKernel_eq_smooth
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    neighboringUpperAnalyticKernel α s t =
      neighboringAffineSmoothKernel α
        (reducedCuspUpperConstantCoefficient α)
        (reducedCuspUpperLinearCoefficient α) s t := by
  unfold neighboringUpperAnalyticKernel
  exact angularScale_mul_affine_normalizedGap_eq_smooth hs ht

theorem neighboringLowerAnalyticKernel_eq_power
    (α s t : ℝ) :
    neighboringLowerAnalyticKernel α s t =
      reducedCuspLowerConstantCoefficient α * latitudePower α s t := by
  unfold neighboringLowerAnalyticKernel latitudePower
  ring

/-- The constant and linear pieces of the resonant model have the same
manifestly smooth form; only the constant-coefficient `q log q` branch
remains to be handled by the diagonal cusp rule. -/
theorem neighboringResonantModelKernel_eq_smooth_add_log
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    neighboringResonantModelKernel s t =
      neighboringAffineSmoothKernel 1
        reducedCuspResonantConstantCoefficient
        reducedCuspResonantLinearCoefficient s t +
      latitudeAngularScale s t ^ (1 / 2 : ℝ) *
        (reducedCuspResonantPrincipalCoefficient *
          normalizedLatitudeGap s t *
            Real.log (normalizedLatitudeGap s t)) := by
  unfold neighboringResonantModelKernel
  have haff := angularScale_mul_affine_normalizedGap_eq_smooth
    (α := 1) (H := reducedCuspResonantConstantCoefficient)
    (L := reducedCuspResonantLinearCoefficient) hs ht
  calc
    _ = latitudeAngularScale s t ^ (1 / 2 : ℝ) *
          (reducedCuspResonantConstantCoefficient +
            reducedCuspResonantLinearCoefficient *
              normalizedLatitudeGap s t) +
        latitudeAngularScale s t ^ (1 / 2 : ℝ) *
          (reducedCuspResonantPrincipalCoefficient *
            normalizedLatitudeGap s t *
              Real.log (normalizedLatitudeGap s t)) := by ring
    _ = _ := by rw [haff]

end BEMOC
