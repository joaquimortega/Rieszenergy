import Mathlib

/-! Basic geometric objects. Targets in later modules are propositions, not proofs. -/
open scoped BigOperators
open MeasureTheory
namespace BEMOC
namespace Definitive

/-- Euclidean ambient space; chordal distance is inherited from this space. -/
abbrev Ambient := EuclideanSpace ℝ (Fin 3)
/-- The unit sphere. -/
abbrev Sphere := Metric.sphere (0 : Ambient) 1

/-- Latitude parametrization, before enforcing the height domain. -/
noncomputable def parallelVector (z θ : ℝ) : Ambient :=
  !₂[Real.sqrt (1 - z ^ 2) * Real.cos θ,
     Real.sqrt (1 - z ^ 2) * Real.sin θ, z]

/-- Reused geometric argument from the previous Core, independent of its construction. -/
theorem parallelVector_mem_sphere {z θ : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    parallelVector z θ ∈ Metric.sphere (0 : Ambient) 1 := by
  rw [EuclideanSpace.sphere_zero_eq 1 (by positivity)]
  have hrad : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  simp [parallelVector, Fin.sum_univ_succ, Real.sq_sqrt hrad]
  ring_nf
  rw [Real.sq_sqrt hrad]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The exact point on a parallel, with its height condition explicit. -/
noncomputable def parallelPoint (z θ : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) : Sphere :=
  ⟨parallelVector z θ, parallelVector_mem_sphere hz⟩

/-- Normalized geometric surface measure, using mathlib's polar measure. -/
noncomputable def sigma : Measure Sphere :=
  (volume.toSphere (E := Ambient) Set.univ)⁻¹ • volume.toSphere

/-- The manuscript's continuous energy constant. -/
noncomputable def continuousEnergy (α : ℝ) : ℝ := 2 ^ (α + 1) / (α + 2)

/-- Ordered-pair energy including the diagonal, which vanishes for `0 < α`. -/
noncomputable def energy {ι : Type*} [Fintype ι] (X : ι → Sphere) (α : ℝ) : ℝ :=
  ∑ i, ∑ j, dist (X i) (X j) ^ α

/-- The target second-order scale. -/
noncomputable def scale (α : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (1 - α / 2)

/-- Average kernel for two uniform parallels; meaningful on `[-1,1]²`. -/
noncomputable def latitudeKernel (α s t : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
    (2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ) ^ (α / 2)

/-- Algebraic specialization used by the discrepancy corollary. -/
theorem continuousEnergy_one : continuousEnergy 1 = 4 / 3 := by
  norm_num [continuousEnergy]

end Definitive
end BEMOC
