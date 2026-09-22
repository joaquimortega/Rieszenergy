import BEMOCFormalization.CrossRingKernel
import BEMOCFormalization.LatitudeBands

/-!
# Latitude-energy decomposition

The latitude analysis works with the scalar angular average
`latitudeKernel`.  This file makes its relation to the existing continuous
ring energy explicit, while `LatitudeBands` supplies the one-dimensional
band rule used in each variable.
-/

open scoped BigOperators

namespace BEMOC

/-- The continuous energy of a finite family of parallels is exactly the
ordered height-pair quadrature for the common latitude kernel. -/
theorem continuousRingEnergy_eq_sum_latitudeKernel
    {κ : Type*} [Fintype κ] (R : κ → OccupiedRing)
    {α : ℝ} (hα : 0 < α) :
    continuousRingEnergy R α =
      ∑ p, ∑ q,
        (R p).population * (R q).population *
          latitudeKernel α (R p).height (R q).height := by
  unfold continuousRingEnergy
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact continuousRingPairEnergy_eq_latitudeKernel (R p) (R q) hα

/-- Concrete BEMOC specialization of the scalar latitude-kernel energy. -/
theorem bemocContinuousRingEnergy_eq_sum_latitudeKernel
    {N : ℕ} {α : ℝ} (hα : 0 < α) :
    continuousRingEnergy (bemocRingFamily N) α =
      ∑ p, ∑ q,
        (bemocRingFamily N p).population * (bemocRingFamily N q).population *
          latitudeKernel α (bemocRingFamily N p).height
            (bemocRingFamily N q).height := by
  exact continuousRingEnergy_eq_sum_latitudeKernel (bemocRingFamily N) hα

/-- The latitude contribution is exactly the difference between the uniform
spherical value and the atomic height-pair quadrature for `latitudeKernel`.
This is the scalar-energy half of the band-error decomposition. -/
theorem bemocLatitudeDeficit_eq_continuous_minus_latitudeKernelSum
    {N : ℕ} {α : ℝ} (hα : 0 < α) :
    bemocLatitudeDeficit α N =
      continuousEnergy α * (N : ℝ) ^ 2 -
        ∑ p, ∑ q,
          (bemocRingFamily N p).population * (bemocRingFamily N q).population *
            latitudeKernel α (bemocRingFamily N p).height
              (bemocRingFamily N q).height := by
  unfold bemocLatitudeDeficit
  rw [bemocContinuousRingEnergy_eq_sum_latitudeKernel hα]

end BEMOC
