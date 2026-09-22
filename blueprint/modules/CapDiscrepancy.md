# `BEMOCFormalization.CapDiscrepancy` proof guide

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
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
```

<!-- END_LEAN_STATEMENTS -->

**Status and source.** The module defines the cap observable, proves the elementary nonnegativity of its squared integral, and states four unproved `Prop` contracts: `StolarskyIdentity`, `DiamondStolarsky`, `BeckLowerBound`, and `CapDiscrepancyCorollary`. The source is `definitive.tex:64–84` for definition, identity, and lower bound, and `:139–147` for the corollary. Its direct code dependency is `EnergyDecomposition`, which imports `Construction`, `ContinuousEnergy`, and ultimately `Core`. Analytic sphere integration should reuse `ContinuousEnergy.SurfaceIntegration` once that proposition is proved; the cap theorem must not be reduced to an energy-defined discrepancy.

**Definition and normalization.** `cap u t` is the closed set of points with `t≤⟪u,x⟫`; this agrees with the manuscript's `u·x≥t`. `capError X u t` is an empirical *proportion* minus `sigma (cap u t)`, whose real measure is obtained through `.toReal`. To identify this with the manuscript's formula, establish `IsProbabilityMeasure sigma`, `sigma (cap u t)≠⊤`, and the cap's measurability. For `n>0`, prove `(Finset.univ.sum fun i => if X i∈cap u t then 1 else 0)/n` equals `# {i | ...}/n`. The squared discrepancy integrates first over center `u` against normalized surface measure, then over `t` against ordinary volume restricted to `Icc (-1) 1`. This is `dt` of mass 2. The reference integral has the opposite nesting, but Tonelli/Fubini for a bounded nonnegative measurable square gives equality. Bound `|capError|≤1` (or ≤2) for finite integrability. The boundary at `t=±1` is measure zero, so `Icc` versus open or half-open endpoints does not change the value.

**Proof of the universal identity.** For a clean Lean proof, first establish the scalar interval lemma

`∫ t in Icc (-1) 1, (if t≤a then 1 else 0)*(if t≤b then 1 else 0) = 1 + min a b`

when `a,b∈[-1,1]`. This follows because the product is the indicator of `Icc (-1) (min a b)`. Next use `min a b = (a+b-|a-b|)/2`. Expand the square in the integrated cap error. A finite signed-measure viewpoint is attractive: let `ν=(1/n)∑ᵢδ_{Xᵢ}-sigma`. It has total mass zero, and `capError` is its cap mass. After interchanging integrals, constant and linear terms in `a` and `b` vanish because `ν(Sphere)=0`; the remaining kernel is `-1/2 ∫_{Sphere}|⟪u,x-y⟫| dσ(u)`. Rotational invariance gives `∫|⟪u,v⟫|dσ(u)=‖v‖/2`. Consequently `D²=-1/4 ∬dist(x,y)dν(x)dν(y)`. Expand `ν`; use the constant distance potential `continuousEnergy 1=4/3`, yielding `4D²=4/3-energy X 1/n²`. A proof with direct finite sums and integrals is also possible and avoids signed measures, at the cost of more expansion lemmas. Verify `n=1` as a normalization check: `D²=1/3`.

`Core.energy` includes all ordered pairs. At exponent 1, `dist(x,x)^1=0`, so it equals the manuscript's off-diagonal convention. The factor is **4** with ordinary `dt`; if one accidentally inserts the probability measure `dt/2`, it becomes **8**. Keep this test close to the theorem. The universal `StolarskyIdentity` should be proved independently of `DiamondStolarsky`, thereby also supplying a useful theorem for arbitrary configurations.

**Concrete index bridge.** `point N φ` is indexed by `PointIndex N`, not `Fin N`. From `ConstructionFacts` derive `Fintype.card (PointIndex N)=N` using the population sum. Construct `e : PointIndex N ≃ Fin N` with `Fintype.equivFinOfCardEq`. Prove `capError (point N φ)` equals `capError (point N φ ∘ e.symm)` pointwise, using finite-sum reindexing and cardinality equality; hence the discrepancies are equal. Likewise prove `energy (point N φ) 1 = energy (point N φ ∘ e.symm) 1`. Apply `StolarskyIdentity` to the relabeled map and multiply by `N²`; unfold `deficit` and `diamondEnergy` to obtain `DiamondStolarsky`. This bridge should be an actual theorem rather than an additional assumption in the final exported result.

**Lower bound.** `BeckLowerBound` is the exact-kind external theorem needed for the manuscript's `cN^-3/4` lower estimate; its premise `Function.Injective X` makes explicit that Beck discusses `n`-element sets. A formal proof is a substantial harmonic/discrepancy argument, not an algebraic consequence of Stolarsky. One may instead prove a universal Wagner-type deficit lower bound `b n^(1/2)≤(4/3)n²-energy X 1` and use Stolarsky to derive Beck's numerical rate, checking whether the source bound permits repeated labels. In either route, prove `Function.Injective (point N φ)` from `ConstructionFacts` and transfer it under the index equivalence. Do not instantiate a distinct-set theorem with a possibly repeated labeling.

**Asymptotic assembly and checks.** `MainTheorem 1` gives `deficit 1 N φ≤C N^(1/2)` for every `N≥4` in the new scaffold. `DiamondStolarsky` gives `D²≤(C/4)N^(-3/2)`. From `capDiscrepancySq_nonneg` obtain `D=√D²≥0`; use positive `N`, `Real.sqrt_le_iff`, and `Real.rpow_mul` to derive `D≤(√C/2)N^-3/4`. Apply Beck for the other inequality. The constant must be independent of both `N` and `φ`, as `CapDiscrepancyCorollary` quantifies over arbitrary phases. The cap result depends on the main energy theorem, geometric cardinality/injectivity, Stolarsky, and Beck; none is supplied merely by importing this module. Build the module after each identity and audit for forbidden proof shortcuts.
