import BEMOCFormalization.EnergyDecomposition

open scoped BigOperators
open MeasureTheory
namespace BEMOC.Definitive

/-- Closed spherical cap, using the manuscript's chordal inner-product convention. -/
def cap (u : Sphere) (t : ℝ) : Set Sphere :=
  {x | t ≤ @Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)}
/-- Empirical cap proportion minus normalized surface area. -/
noncomputable def capError {ι : Type} [Fintype ι] (X : ι → Sphere)
    (u : Sphere) (t : ℝ) : ℝ := by
  classical
  exact (∑ i, if X i ∈ cap u t then (1 : ℝ) else 0) / Fintype.card ι -
    (sigma (cap u t)).toReal
/-- Actual integrated squared cap error; the height measure is dt, of total mass two. -/
noncomputable def capDiscrepancySq {ι : Type} [Fintype ι] (X : ι → Sphere) : ℝ :=
  ∫ t in Set.Icc (-1 : ℝ) 1, ∫ u, capError X u t ^ 2 ∂sigma
/-- Actual L² spherical cap discrepancy, defined independently of energy. -/
noncomputable def capDiscrepancy {ι : Type} [Fintype ι] (X : ι → Sphere) : ℝ :=
  Real.sqrt (capDiscrepancySq X)

/-- Stolarsky with ordinary dt; replacing dt by dt/2 would change the factor to eight. -/
def StolarskyIdentity : Prop :=
  ∀ n : ℕ, 0 < n → ∀ X : Fin n → Sphere,
    4 * capDiscrepancySq X = continuousEnergy 1 - energy X 1 / (n : ℝ) ^ 2

/-- Geometric nonnegativity before invoking the invariance principle. -/
theorem capDiscrepancySq_nonneg {ι : Type} [Fintype ι] (X : ι → Sphere) :
    0 ≤ capDiscrepancySq X := by
  unfold capDiscrepancySq
  exact integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))

/-- Relabeling/cardinality bridge for the concrete point-index type. -/
def DiamondStolarsky : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N,
    4 * (N : ℝ) ^ 2 * capDiscrepancySq (point N φ) = deficit 1 N φ

/-- Beck's external lower estimate for actual sets, with injectivity explicit. -/
def BeckLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ X : Fin n → Sphere,
    Function.Injective X → c * (n : ℝ) ^ (-(3 : ℝ) / 4) ≤ capDiscrepancy X

/-- Corollary main, stronger by its uniformity in arbitrary ring phases. -/
def CapDiscrepancyCorollary : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N,
    c * (N : ℝ) ^ (-(3 : ℝ) / 4) ≤ capDiscrepancy (point N φ) ∧
    capDiscrepancy (point N φ) ≤ C * (N : ℝ) ^ (-(3 : ℝ) / 4)

end BEMOC.Definitive
