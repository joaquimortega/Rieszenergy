import BEMOCFormalization.CrossRingKernel

/-!
# Local identities for the latitude kernel

These exact identities isolate the diagonal angular cusp.  They are the
starting point for the comparable-scale block analysis: all non-smoothness
comes from the factor `1 - cos θ` after the radial factor has been separated.
-/

open scoped BigOperators
open MeasureTheory Set

namespace BEMOC

theorem latitudeKernel_nonneg {α s t : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    0 ≤ latitudeKernel α s t := by
  unfold latitudeKernel
  apply mul_nonneg
  · positivity
  · apply intervalIntegral.integral_nonneg
    · positivity
    · intro θ hθ
      exact angularPairKernel_nonneg hs ht

/-- On a fixed parallel the angular kernel is a scaled copy of the standard
chord cusp. -/
theorem angularPairKernel_self_eq_scaled_cusp
    {α s θ : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    angularPairKernel α s s θ =
      (2 * (1 - s ^ 2) * (1 - Real.cos θ)) ^ (α / 2) := by
  unfold angularPairKernel
  have hsq : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 := by
    apply Real.sq_sqrt
    nlinarith [hs.1, hs.2]
  congr 1
  calc
    2 - 2 * s * s - 2 * Real.sqrt (1 - s ^ 2) *
        Real.sqrt (1 - s ^ 2) * Real.cos θ =
        2 - 2 * s ^ 2 - 2 * (Real.sqrt (1 - s ^ 2)) ^ 2 * Real.cos θ := by ring
    _ = 2 * (1 - s ^ 2) * (1 - Real.cos θ) := by rw [hsq]; ring

/-- The diagonal latitude kernel is the angular average of that scaled
cusp, with no additional geometric normalization. -/
theorem latitudeKernel_self_eq_scaled_cusp
    {α s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    latitudeKernel α s s =
      (1 / (2 * Real.pi)) *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          (2 * (1 - s ^ 2) * (1 - Real.cos θ)) ^ (α / 2) := by
  unfold latitudeKernel
  congr 2
  funext θ
  exact angularPairKernel_self_eq_scaled_cusp hs

/-- At a common height the `A - B cos θ` coefficients agree. -/
theorem angularKernelA_self_eq_B
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    angularKernelA s s = angularKernelB s s := by
  unfold angularKernelA angularKernelB
  have hsq : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 := by
    apply Real.sq_sqrt
    nlinarith [hs.1, hs.2]
  nlinarith

end BEMOC
