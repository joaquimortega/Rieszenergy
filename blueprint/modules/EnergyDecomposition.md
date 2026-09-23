# EnergyDecomposition proof guide

Source anchors: `definitive.tex` `eq:energianu`, `eq:Falpha`, and `eq:decomp` (around lines 386–421). The module defines the continuous ring energy, latitude and longitude errors, and their exact algebraic decomposition. It now also proves that the actual finite configuration deficit is nonnegative for `0 < α < 2`.

For an arbitrary finite label type `ι`, define its counting measure `μ = Σᵢ δ_{Xᵢ}`. Integration against `μ` is summation over labels, so its self pair energy is exactly the ordered sum `energy X α`, including the diagonal. The reference measure `ν = (card ι) • sigma` has the same total mass. `constantPotential_of_pos` evaluates the two reference and mixed pair energies as `continuousEnergy α * (card ι)^2`; symmetry of the distance-power kernel supplies the reversed mixed orientation. Applying `measureNegativeType_of_pos_of_lt_two` and rearranging proves `energy_nonnegative_finite`.

The specialization `energy_nonnegative` inhabits the existing `EnergyNonnegative α` contract for `Fin n`. The specialization `diamond_nonnegative` inhabits `DiamondNonnegative α`, using `card_pointIndex N hN` and `diamondEnergy = energy (point N φ) α`. Injectivity of the point map is unnecessary for this numerical inequality. Both theorems retain the exact assumptions `0 < α` and `α < 2`.

The two-term algebraic decomposition remains independent of analytic estimates. The geometric identification of `ringEnergy` with the energy of a continuous ring measure, the latitude block identity, and the bounds on latitude/longitude errors are proved in separate downstream modules.

Status: all statements in this module elaborate. `lake build BEMOCFormalization.EnergyDecomposition` passes. The proof-shortcut audit finds no `sorry`, `admit`, `axiom`, or `opaque`.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Construction
import BEMOCFormalization.ContinuousEnergy
import BEMOCFormalization.SurfaceMeasure

open scoped BigOperators
open MeasureTheory
namespace BEMOC.Definitive

/-- Energy of the weighted union of uniform parallels. -/
noncomputable def ringEnergy (α : ℝ) (N : ℕ) : ℝ :=
  ∑ j : RingIndex N, ∑ k : RingIndex N,
    (population N (j.val + 1) : ℝ) * population N (k.val + 1) *
      latitudeKernel α (height N (j.val + 1)) (height N (k.val + 1))
/-- Latitude error A. -/
noncomputable def latitudeError (α : ℝ) (N : ℕ) : ℝ :=
  continuousEnergy α * (N : ℝ) ^ 2 - ringEnergy α N
/-- Angular discretization error B; phases are retained. -/
noncomputable def longitudeError (α : ℝ) (N : ℕ) (φ : Phases N) : ℝ :=
  ringEnergy α N - diamondEnergy α N φ
/-- The actual energy deficit appearing in Theorem 1. -/
noncomputable def deficit (α : ℝ) (N : ℕ) (φ : Phases N) : ℝ :=
  continuousEnergy α * (N : ℝ) ^ 2 - diamondEnergy α N φ

/-- The two-term decomposition is algebraic and already proved. -/
theorem deficit_eq_latitude_add_longitude (α : ℝ) (N : ℕ) (φ : Phases N) :
    deficit α N φ = latitudeError α N + longitudeError α N φ := by
  unfold deficit latitudeError longitudeError
  ring

/-- Required geometric identification, including the finite-label cardinality. -/
def DiamondNonnegative (α : ℝ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N, 0 ≤ deficit α N φ

/-- The counting measure of a finitely labelled configuration. -/
noncomputable def finitePointMeasure {ι : Type*} [Fintype ι]
    (X : ι → Sphere) : Measure Sphere :=
  ∑ i, Measure.dirac (X i)

@[simp] theorem finitePointMeasure_apply_univ {ι : Type*} [Fintype ι]
    (X : ι → Sphere) : finitePointMeasure X Set.univ = Fintype.card ι := by
  simp [finitePointMeasure, Measure.sum_apply]

/-- Integration against counting measure is summation over labels. -/
theorem integral_finitePointMeasure {ι : Type*} [Fintype ι]
    (X : ι → Sphere) (f : Sphere → ℝ) :
    ∫ x, f x ∂finitePointMeasure X = ∑ i, f (X i) := by
  unfold finitePointMeasure
  rw [integral_finset_sum_measure (s := Finset.univ)
    (fun _ _ ↦ integrable_dirac)]
  simp

/-- Pair energy of a labelled configuration is the ordered double sum. -/
theorem pairEnergy_finitePointMeasure {ι : Type*} [Fintype ι]
    (X : ι → Sphere) (α : ℝ) :
    kernelPairEnergy (fun x y ↦ dist x y ^ α)
      (finitePointMeasure X) (finitePointMeasure X) = energy X α := by
  unfold kernelPairEnergy energy
  simp_rw [integral_finitePointMeasure]

/-- The mass-scaled normalized area measure used for comparison. -/
noncomputable def referenceMeasure (n : ℕ) : Measure Sphere :=
  (n : ENNReal) • sigma

@[simp] theorem referenceMeasure_apply_univ (n : ℕ) :
    referenceMeasure n Set.univ = n := by
  simp [referenceMeasure]

theorem pairEnergy_reference_right (n : ℕ) {α : ℝ}
    (hpot : ConstantPotential α) (μ : Measure Sphere)
    (hmass : μ Set.univ = n) :
    kernelPairEnergy (fun x y ↦ dist x y ^ α) μ (referenceMeasure n) =
      continuousEnergy α * (n : ℝ) ^ 2 := by
  unfold kernelPairEnergy referenceMeasure
  simp_rw [integral_smul_measure]
  simp only [smul_eq_mul]
  simp_rw [show ∀ x : Sphere, (∫ y, dist x y ^ α ∂sigma) = continuousEnergy α from hpot]
  rw [integral_const]
  simp [Measure.real_def, hmass]
  ring

theorem pairEnergy_reference_left (n : ℕ) {α : ℝ} (hα : 0 < α)
    (hpot : ConstantPotential α) (μ : Measure Sphere)
    [IsFiniteMeasure μ] (hmass : μ Set.univ = n) :
    kernelPairEnergy (fun x y ↦ dist x y ^ α) (referenceMeasure n) μ =
      continuousEnergy α * (n : ℝ) ^ 2 := by
  letI : IsFiniteMeasure (referenceMeasure n) :=
    IsFiniteMeasure.mk (by simp)
  rw [kernelPairEnergy_distancePower_comm hα]
  exact pairEnergy_reference_right n hpot μ hmass

theorem pairEnergy_reference_self (n : ℕ) {α : ℝ}
    (hpot : ConstantPotential α) :
    kernelPairEnergy (fun x y ↦ dist x y ^ α)
      (referenceMeasure n) (referenceMeasure n) =
      continuousEnergy α * (n : ℝ) ^ 2 := by
  exact pairEnergy_reference_right n hpot (referenceMeasure n)
    (referenceMeasure_apply_univ n)

/-- Every finite spherical configuration satisfies the Riesz deficit bound. -/
theorem energy_nonnegative_finite {ι : Type*} [Fintype ι]
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (X : ι → Sphere) :
    0 ≤ continuousEnergy α * (Fintype.card ι : ℝ) ^ 2 - energy X α := by
  let μ := finitePointMeasure X
  let ν := referenceMeasure (Fintype.card ι)
  have hμfinite : IsFiniteMeasure μ := IsFiniteMeasure.mk (by simp [μ])
  have hνfinite : IsFiniteMeasure ν := IsFiniteMeasure.mk (by simp [ν])
  have h := measureNegativeType_of_pos_of_lt_two hα0 hα2
    μ ν hμfinite hνfinite (by simp [μ, ν])
  change kernelPairEnergy (fun x y ↦ dist x y ^ α) μ μ +
      kernelPairEnergy (fun x y ↦ dist x y ^ α) ν ν -
        2 * kernelPairEnergy (fun x y ↦ dist x y ^ α) μ ν ≤ 0 at h
  rw [show μ = finitePointMeasure X from rfl,
    pairEnergy_finitePointMeasure, show ν = referenceMeasure (Fintype.card ι) from rfl,
    pairEnergy_reference_self _ (constantPotential_of_pos hα0),
    pairEnergy_reference_right _ (constantPotential_of_pos hα0)
      (finitePointMeasure X) (finitePointMeasure_apply_univ X)] at h
  linarith

theorem energy_nonnegative {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    EnergyNonnegative α := by
  intro n X
  simpa using energy_nonnegative_finite hα0 hα2 X

/-- The Diamond configuration inherits the finite energy inequality. -/
theorem diamond_nonnegative {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    DiamondNonnegative α := by
  intro N hN φ
  simpa [deficit, diamondEnergy, card_pointIndex N hN] using
    energy_nonnegative_finite hα0 hα2 (point N φ)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
