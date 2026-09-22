import BEMOCFormalization.Core

/-!
# The common cross-ring angular kernel

This file fixes the normalization used by both the angular-aliasing and
latitude-quadrature arguments.  The scalar kernel is the squared chordal
distance from `parallelPoint s θ` to `parallelPoint t 0`, raised to `α / 2`.
-/

open scoped BigOperators
open MeasureTheory Set

namespace BEMOC

/-- Chord-power kernel for two latitudes and one angular difference. -/
noncomputable def angularPairKernel (α s t θ : ℝ) : ℝ :=
  (2 - 2 * s * t -
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) *
        Real.cos θ) ^ (α / 2)

/-- Angularly averaged interaction of two unit-mass parallels. -/
noncomputable def latitudeKernel (α s t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ θ in (0 : ℝ)..2 * Real.pi, angularPairKernel α s t θ

/-- The two coefficients in the standard form `A - B cos θ`. -/
def angularKernelA (s t : ℝ) : ℝ := 2 - 2 * s * t

noncomputable def angularKernelB (s t : ℝ) : ℝ :=
  2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)

theorem angularPairKernel_eq_A_sub_B_cos (α s t θ : ℝ) :
    angularPairKernel α s t θ =
      (angularKernelA s t - angularKernelB s t * Real.cos θ) ^ (α / 2) := by
  rfl

theorem angularKernelB_eq_two_mul_radius
    (P Q : OccupiedRing) :
    angularKernelB P.height Q.height = 2 * P.radius * Q.radius := by
  rfl

theorem angularPairKernel_eq_dist_rpow
    {α s t θ : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    angularPairKernel α s t θ =
      dist (parallelPoint s θ hs) (parallelPoint t 0 ht) ^ α := by
  rw [angularPairKernel, ← distance_sq_rpow_half_alpha,
    parallelPoint_dist_sq hs ht]
  simp

theorem angularPairKernel_eq_dist_rpow_sub
    {α s t θ φ : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    angularPairKernel α s t (θ - φ) =
      dist (parallelPoint s θ hs) (parallelPoint t φ ht) ^ α := by
  rw [angularPairKernel, ← distance_sq_rpow_half_alpha,
    parallelPoint_dist_sq hs ht]

theorem angularPairKernel_periodic (α s t : ℝ) :
    Function.Periodic (angularPairKernel α s t) (2 * Real.pi) := by
  intro θ
  unfold angularPairKernel
  rw [show θ + 2 * Real.pi = θ + 2 * Real.pi by rfl,
    Real.cos_add_two_pi]

theorem angularKernelB_nonneg (s t : ℝ) :
    0 ≤ angularKernelB s t := by
  unfold angularKernelB
  positivity

theorem angularKernelA_nonneg
    {s t : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ angularKernelA s t := by
  unfold angularKernelA
  have hst : s * t ≤ 1 := by
    calc
      s * t ≤ |s * t| := le_abs_self _
      _ = |s| * |t| := abs_mul s t
      _ ≤ 1 * 1 := mul_le_mul (abs_le.mpr hs) (abs_le.mpr ht)
        (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  linarith

theorem angularKernelB_le_A
    {s t : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    angularKernelB s t ≤ angularKernelA s t := by
  have hrs : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hrt : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hA := angularKernelA_nonneg hs ht
  have hB := angularKernelB_nonneg s t
  have hsqrt_s := Real.sq_sqrt hrs
  have hsqrt_t := Real.sq_sqrt hrt
  have hsq :
      angularKernelB s t ^ 2 ≤ angularKernelA s t ^ 2 := by
    unfold angularKernelA angularKernelB
    nlinarith [sq_nonneg (s - t)]
  nlinarith

theorem angularKernel_coefficients
    {s t : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ angularKernelB s t ∧ angularKernelB s t ≤ angularKernelA s t :=
  ⟨angularKernelB_nonneg s t, angularKernelB_le_A hs ht⟩

theorem angularPairKernel_nonneg
    {α s t θ : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ angularPairKernel α s t θ := by
  rw [angularPairKernel_eq_A_sub_B_cos]
  apply Real.rpow_nonneg
  have hcoeff := angularKernel_coefficients hs ht
  have hcos := Real.cos_le_one θ
  nlinarith [mul_le_mul_of_nonneg_left hcos hcoeff.1]

theorem continuous_angularPairKernel
    {α : ℝ} (hα : 0 < α) :
    Continuous (fun p : ℝ × ℝ × ℝ ↦
      angularPairKernel α p.1 p.2.1 p.2.2) := by
  unfold angularPairKernel
  have hbase : Continuous (fun p : ℝ × ℝ × ℝ ↦
      2 - 2 * p.1 * p.2.1 -
        2 * Real.sqrt (1 - p.1 ^ 2) * Real.sqrt (1 - p.2.1 ^ 2) *
          Real.cos p.2.2) := by
    fun_prop
  exact hbase.rpow continuous_const (fun _ ↦ Or.inr (by linarith))

theorem angularPairKernel_neg
    (α s t θ : ℝ) :
    angularPairKernel α s t (-θ) =
      angularPairKernel α s t θ := by
  unfold angularPairKernel
  rw [Real.cos_neg]

set_option maxHeartbeats 800000 in
theorem integral_uniform_angularPairKernel
    (P Q : OccupiedRing) {α : ℝ} (_hα : 0 < α) (θ : ℝ) :
    (∫ φ : ℝ,
        dist
          (parallelPoint P.height θ P.height_mem)
          (parallelPoint Q.height φ Q.height_mem) ^ α
        ∂uniformAngleMeasure) =
      latitudeKernel α P.height Q.height := by
  let g : ℝ → ℝ :=
    angularPairKernel α P.height Q.height
  have hg : Function.Periodic g (2 * Real.pi) :=
    angularPairKernel_periodic α P.height Q.height
  have hshift :
      (∫ t : ℝ in -θ..2 * Real.pi - θ, g t) =
        ∫ t : ℝ in (0 : ℝ)..2 * Real.pi, g t := by
    convert hg.intervalIntegral_add_eq (-θ) 0 using 1 <;> ring_nf
  calc
    (∫ φ : ℝ,
        dist
          (parallelPoint P.height θ P.height_mem)
          (parallelPoint Q.height φ Q.height_mem) ^ α
        ∂uniformAngleMeasure) =
        (1 / (2 * Real.pi)) *
          ∫ φ : ℝ in (0 : ℝ)..2 * Real.pi,
            dist
              (parallelPoint P.height θ P.height_mem)
              (parallelPoint Q.height φ Q.height_mem) ^ α :=
      integral_uniformAngleMeasure_eq_interval _
    _ = (1 / (2 * Real.pi)) *
          ∫ φ : ℝ in (0 : ℝ)..2 * Real.pi, g (φ - θ) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro φ hφ
      dsimp [g]
      rw [← angularPairKernel_neg α P.height Q.height (φ - θ)]
      rw [show -(φ - θ) = θ - φ by ring]
      exact (angularPairKernel_eq_dist_rpow_sub
        (α := α) (θ := θ) (φ := φ)
        P.height_mem Q.height_mem).symm
    _ = (1 / (2 * Real.pi)) *
          ∫ t : ℝ in -θ..2 * Real.pi - θ, g t := by
      rw [intervalIntegral.integral_comp_sub_right]
      simp only [zero_sub]
    _ = (1 / (2 * Real.pi)) *
          ∫ t : ℝ in (0 : ℝ)..2 * Real.pi, g t := by
      rw [hshift]
    _ = latitudeKernel α P.height Q.height := by
      rfl

theorem integral_distancePower_angularRingMeasure_eq_latitudeKernel
    (P Q : OccupiedRing) {α : ℝ} (hα : 0 < α) (θ : ℝ) :
    (∫ y : Sphere,
        dist (parallelPoint P.height θ P.height_mem) y ^ α
          ∂angularRingMeasure Q) =
      latitudeKernel α P.height Q.height := by
  have hf : Continuous (fun y : Sphere ↦
      dist (parallelPoint P.height θ P.height_mem) y ^ α) :=
    (continuous_const.dist continuous_id).rpow continuous_const
      (fun _ ↦ Or.inr hα)
  rw [integral_angularRingMeasure_eq_uniform Q _ hf]
  exact integral_uniform_angularPairKernel P Q hα θ

theorem measurePairEnergy_angularRingMeasure_eq_latitudeKernel
    (P Q : OccupiedRing) {α : ℝ} (hα : 0 < α) :
    measurePairEnergy (angularRingMeasure P) (angularRingMeasure Q) α =
      latitudeKernel α P.height Q.height := by
  unfold measurePairEnergy kernelPairEnergy
  rw [integral_angularRingMeasure_eq_uniform P _
    (continuous_inner_distancePower_angular hα Q)]
  simp_rw [integral_distancePower_angularRingMeasure_eq_latitudeKernel
    P Q hα]
  rw [integral_const]
  simp only [smul_eq_mul, measureReal_def,
    uniformAngleMeasure_apply_univ, ENNReal.toReal_one, one_mul]

/-- Population-weighted bridge from the common scalar kernel to the existing
continuous ring-pair energy. -/
theorem continuousRingPairEnergy_eq_latitudeKernel
    (P Q : OccupiedRing) {α : ℝ} (hα : 0 < α) :
    continuousRingPairEnergy P Q α =
      (P.population : ℝ) * (Q.population : ℝ) *
        latitudeKernel α P.height Q.height := by
  rw [continuousRingPairEnergy,
    measurePairEnergy_angularRingMeasure_eq_latitudeKernel P Q hα]

end BEMOC
