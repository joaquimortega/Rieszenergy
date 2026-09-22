import BEMOCFormalization.LatitudeDecomposition

/-!
# Height pushforwards for BEMOC latitude quadrature

The continuous angular measure on a parallel has constant height.  This is
the measure-theoretic bridge used to convert the ring energy into a scalar
height quadrature.
-/

open MeasureTheory Set

namespace BEMOC

@[simp] theorem sphereHeight_parallelPoint (z θ : ℝ)
    (hz : z ∈ Icc (-1 : ℝ) 1) : sphereHeight (parallelPoint z θ hz) = z := by
  exact parallelPoint_height z θ hz

/-- The height pushforward of a unit angular ring is the unit atom at its
certified latitude. -/
theorem map_sphereHeight_angularRingMeasure (R : OccupiedRing) :
    Measure.map sphereHeight (angularRingMeasure R) = Measure.dirac R.height := by
  rw [angularRingMeasure,
    Measure.map_map continuous_sphereHeight.measurable
      (measurable_parallelPoint R.height R.height_mem)]
  have hconst : sphereHeight ∘ (fun θ ↦ parallelPoint R.height θ R.height_mem) =
      fun _ : ℝ ↦ R.height := by
    funext θ
    exact sphereHeight_parallelPoint R.height θ R.height_mem
  rw [hconst, Measure.map_const]
  simp

/-- The height pushforward of a finite continuous ring family is its
population-weighted atomic latitude measure. -/
theorem map_sphereHeight_continuousRingMeasure
    {κ : Type*} [Fintype κ] (R : κ → OccupiedRing) :
    Measure.map sphereHeight (continuousRingMeasure R) =
      ∑ k, (R k).population • Measure.dirac (R k).height := by
  classical
  unfold continuousRingMeasure
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp
  | insert k s hks ih =>
      rw [Finset.sum_insert hks, Finset.sum_insert hks,
        Measure.map_add _ _ continuous_sphereHeight.measurable, ih]
      rw [Measure.map_smul, map_sphereHeight_angularRingMeasure]

theorem map_sphereHeight_bemocContinuousRingMeasure (N : ℕ) :
    Measure.map sphereHeight (continuousRingMeasure (bemocRingFamily N)) =
      ∑ p, (bemocRingFamily N p).population •
        Measure.dirac (bemocRingFamily N p).height := by
  exact map_sphereHeight_continuousRingMeasure (bemocRingFamily N)

/-- The height pushforward of the mass-`N` spherical reference measure is
the uniform height measure with the same mass. -/
theorem map_sphereHeight_sphereReferenceMeasure (N : ℕ) :
    Measure.map sphereHeight (sphereReferenceMeasure N) =
      N • uniformHeightMeasure := by
  rw [sphereReferenceMeasure, Measure.map_smul, hasUniformHeightMarginal]

/-- The uncombined three-atom latitude measure of one BEMOC band.  Its
shared endpoint atoms are deliberately kept separate here; summing adjacent
bands combines them into the actual boundary rings. -/
noncomputable def bandAtomicMeasure (N : ℕ)
    (j : Fin (bandTailCount N + 1)) : Measure ℝ :=
  (midpointRingPopulation N j) • Measure.dirac (bandMidpointHeight N j) +
    (boundarySixth N j) • Measure.dirac (bandBoundaryHeight N j) +
      (boundarySixth N j) • Measure.dirac (bandBoundaryHeight N (j + 1))

/-- The uniform-height portion of one BEMOC band. -/
noncomputable def bandContinuousMeasure (N : ℕ)
    (j : Fin (bandTailCount N + 1)) : Measure ℝ :=
  ENNReal.ofReal (N / 2 : ℝ) •
    volume.restrict (Ioc (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j))

theorem integral_bandContinuousMeasure {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) :
    ∫ t, f t ∂bandContinuousMeasure N j = bandContinuousValue N j f := by
  unfold bandContinuousMeasure bandContinuousValue
  rw [integral_smul_measure]
  have hle : bandBoundaryHeight N (j + 1) ≤ bandBoundaryHeight N j := by
    rw [← sub_nonneg, bandBoundaryHeight_sub_succ]
    positivity
  rw [intervalIntegral.integral_of_le hle]
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (N / 2 : ℝ)), smul_eq_mul]

/-- Integration against the one-band atomic measure is exactly the scalar
atomic rule already used by `bandError`. -/
theorem integral_bandAtomicMeasure (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) :
    ∫ t, f t ∂bandAtomicMeasure N j = bandAtomicValue N j f := by
  unfold bandAtomicMeasure bandAtomicValue
  simp_rw [← Nat.cast_smul_eq_nsmul ENNReal]
  have hmid : Integrable f ((midpointRingPopulation N j : ENNReal) •
      Measure.dirac (bandMidpointHeight N j)) :=
    integrable_dirac.smul_measure ENNReal.coe_ne_top
  have hleft : Integrable f ((boundarySixth N j : ENNReal) •
      Measure.dirac (bandBoundaryHeight N j)) :=
    integrable_dirac.smul_measure ENNReal.coe_ne_top
  have hright : Integrable f ((boundarySixth N j : ENNReal) •
      Measure.dirac (bandBoundaryHeight N (j + 1))) :=
    integrable_dirac.smul_measure ENNReal.coe_ne_top
  rw [MeasureTheory.integral_add_measure (hmid.add_measure hleft) hright,
    MeasureTheory.integral_add_measure hmid hleft,
    integral_smul_measure, integral_smul_measure, integral_smul_measure]
  simp

/-- The uncombined band atoms integrate exactly as the combined BEMOC
height atoms.  This is the integration form of their measure equality. -/
theorem sum_integral_bandAtomicMeasure_eq_bemocHeightAtoms
    {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ) :
    (∑ j : Fin (bandTailCount N + 1),
      ∫ t, f t ∂bandAtomicMeasure N j) =
      ∑ p : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
        (bemocRingFamily N p).population * f (bemocRingFamily N p).height := by
  simp_rw [integral_bandAtomicMeasure]
  exact sum_bandAtomicValue_eq_bemocRingFamily hN f

/-- The continuous band measures concatenate to the mass-`N` uniform height
integral. -/
theorem sum_integral_bandContinuousMeasure_eq_uniformHeight
    {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ) (hf : Continuous f) :
    (∑ j : Fin (bandTailCount N + 1),
      ∫ t, f t ∂bandContinuousMeasure N j) =
      (N / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, f t := by
  simp_rw [integral_bandContinuousMeasure hN]
  exact sum_bandContinuousValue_eq_heightIntegral hN f hf

end BEMOC
