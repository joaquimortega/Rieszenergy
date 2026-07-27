import BEMOCFormalization.LatitudeBands
import BEMOCFormalization.LatitudeKernelLocal

/-!
# Uniform latitude-kernel block estimates

This file records the elementary global estimate used for the bounded pieces
of the latitude decomposition.  It is deliberately independent of a choice
of BEMOC band: after the angular average every pair of heights in `[-1,1]`
has a uniform chord-power bound.  Combining this with the two-band bounded
kernel lemma gives a genuine (though coarse) separated/polar block bound.
-/

open scoped BigOperators
open MeasureTheory Set

namespace BEMOC

/-- The angular kernel is symmetric in the two height variables. -/
theorem angularPairKernel_swap (α s t θ : ℝ) :
    angularPairKernel α s t θ = angularPairKernel α t s θ := by
  unfold angularPairKernel
  congr 1
  ring

/-- Consequently the averaged latitude kernel is symmetric. -/
theorem latitudeKernel_swap (α s t : ℝ) :
    latitudeKernel α s t = latitudeKernel α t s := by
  unfold latitudeKernel
  congr 2
  funext θ
  exact angularPairKernel_swap α s t θ

/-- At the north pole the angular average has no angular dependence. -/
theorem angularPairKernel_north (α t θ : ℝ) :
    angularPairKernel α 1 t θ = (2 * (1 - t)) ^ (α / 2) := by
  unfold angularPairKernel
  norm_num
  ring_nf

/-- Exact polar reduction of the latitude kernel. -/
theorem latitudeKernel_north (α t : ℝ) :
    latitudeKernel α 1 t = (2 * (1 - t)) ^ (α / 2) := by
  unfold latitudeKernel
  simp_rw [angularPairKernel_north]
  rw [intervalIntegral.integral_const]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

/-- Exact antipodal-pole reduction of the latitude kernel. -/
theorem angularPairKernel_south (α t θ : ℝ) :
    angularPairKernel α (-1) t θ = (2 * (1 + t)) ^ (α / 2) := by
  unfold angularPairKernel
  norm_num
  ring_nf

theorem latitudeKernel_south (α t : ℝ) :
    latitudeKernel α (-1) t = (2 * (1 + t)) ^ (α / 2) := by
  unfold latitudeKernel
  simp_rw [angularPairKernel_south]
  rw [intervalIntegral.integral_const]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

/-- Two points on the unit sphere are at distance at most two. -/
theorem parallelPoint_dist_le_two
    {s t θ φ : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    dist (parallelPoint s θ hs) (parallelPoint t φ ht) ≤ 2 := by
  have hsq := sphere_dist_sq_nonneg_le_four
    (parallelPoint s θ hs) (parallelPoint t φ ht)
  have hnonneg : 0 ≤ dist (parallelPoint s θ hs) (parallelPoint t φ ht) :=
    dist_nonneg
  nlinarith

/-- Pointwise global chord-power bound for the angular kernel. -/
theorem angularPairKernel_le_global
    {α s t θ : ℝ} (hα : 0 ≤ α)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    angularPairKernel α s t θ ≤ (2 : ℝ) ^ α := by
  rw [angularPairKernel_eq_dist_rpow hs ht]
  exact Real.rpow_le_rpow dist_nonneg
    (parallelPoint_dist_le_two hs ht) hα

/-- The squared chord is at least the squared height separation.  This is
the elementary separation estimate behind all off-diagonal latitude blocks. -/
theorem angularPairKernel_base_ge_height_sq
    {s t θ : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    (s - t) ^ 2 ≤
      2 - 2 * s * t -
        2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * Real.cos θ := by
  have hrs : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hrt : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hrad : 0 ≤ Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcos : 0 ≤ 1 - Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
  have hsqr : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hrs
  have htqr : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hrt
  have hdecomp :
      2 - 2 * s * t -
          2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * Real.cos θ =
        (s - t) ^ 2 +
          (Real.sqrt (1 - s ^ 2) - Real.sqrt (1 - t ^ 2)) ^ 2 +
          2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) *
            (1 - Real.cos θ) := by
    ring_nf
    rw [hsqr, htqr]
    ring
  rw [hdecomp]
  nlinarith [sq_nonneg (Real.sqrt (1 - s ^ 2) - Real.sqrt (1 - t ^ 2))]

/-- Raising the preceding separation inequality to a nonnegative chord
power gives a pointwise off-diagonal lower bound. -/
theorem angularPairKernel_ge_height_sq_rpow
    {α s t θ : ℝ} (hα : 0 ≤ α)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    ((s - t) ^ 2) ^ (α / 2) ≤ angularPairKernel α s t θ := by
  unfold angularPairKernel
  apply Real.rpow_le_rpow
  · positivity
  · exact angularPairKernel_base_ge_height_sq hs ht
  · positivity

/-- Averaging preserves the pointwise lower bound supplied by height
separation.  In particular, a nonzero vertical gap removes the angular
singularity altogether. -/
theorem latitudeKernel_ge_height_sq_rpow
    {α s t : ℝ} (hα : 0 < α)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    ((s - t) ^ 2) ^ (α / 2) ≤ latitudeKernel α s t := by
  let C : ℝ := ((s - t) ^ 2) ^ (α / 2)
  have hcont : Continuous (fun θ : ℝ ↦ angularPairKernel α s t θ) :=
    continuous_angularPairKernel hα |>.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
    (f := fun _ : ℝ ↦ C) (g := fun θ ↦ angularPairKernel α s t θ)
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    (continuous_const.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    (fun θ _ ↦ angularPairKernel_ge_height_sq_rpow hα.le hs ht)
  have hD : 0 < 2 * Real.pi := by positivity
  have hCI : C * (2 * Real.pi) ≤
      ∫ θ in (0 : ℝ)..2 * Real.pi, angularPairKernel α s t θ := by
    convert hmono using 1
    simp [C, intervalIntegral.integral_const, smul_eq_mul]
    ring
  unfold latitudeKernel
  calc
    C = (C * (2 * Real.pi)) / (2 * Real.pi) := by
      field_simp
    _ ≤ (∫ θ in (0 : ℝ)..2 * Real.pi,
        angularPairKernel α s t θ) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right hCI hD.le
    _ = (1 / (2 * Real.pi)) *
        ∫ θ in (0 : ℝ)..2 * Real.pi, angularPairKernel α s t θ := by ring

/-- The angular average is uniformly bounded by the diameter power. -/
theorem abs_latitudeKernel_le_global
    {α s t : ℝ} (hα : 0 ≤ α)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    |latitudeKernel α s t| ≤ (2 : ℝ) ^ α := by
  have hC : 0 ≤ (2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  have hang (θ : ℝ) : |angularPairKernel α s t θ| ≤ (2 : ℝ) ^ α := by
    rw [abs_of_nonneg (angularPairKernel_nonneg hs ht)]
    exact angularPairKernel_le_global hα hs ht
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (C := (2 : ℝ) ^ α)
    (f := angularPairKernel α s t)
    (fun θ _ ↦ by simpa [Real.norm_eq_abs] using hang θ)
  have hlen : |2 * Real.pi - 0| = 2 * Real.pi := by
    rw [sub_zero]
    exact abs_of_pos (by positivity)
  have hint' : |∫ θ in (0 : ℝ)..2 * Real.pi,
      angularPairKernel α s t θ| ≤ (2 : ℝ) ^ α * (2 * Real.pi) := by
    calc
      |∫ θ in (0 : ℝ)..2 * Real.pi, angularPairKernel α s t θ| =
          ‖∫ θ in (0 : ℝ)..2 * Real.pi, angularPairKernel α s t θ‖ := by
            simp [Real.norm_eq_abs]
      _ ≤ (2 : ℝ) ^ α * |2 * Real.pi - 0| := hint
      _ = (2 : ℝ) ^ α * (2 * Real.pi) := by rw [hlen]
  unfold latitudeKernel
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) * |∫ θ in (0 : ℝ)..2 * Real.pi,
        angularPairKernel α s t θ| ≤
        (1 / (2 * Real.pi)) * ((2 : ℝ) ^ α * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hint' (by positivity)
    _ = (2 : ℝ) ^ α := by
      have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp

end BEMOC
