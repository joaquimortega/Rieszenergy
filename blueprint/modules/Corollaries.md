# `BEMOCFormalization.Corollaries` proof guide

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.MainTheorem
import BEMOCFormalization.CapDiscrepancy
import BEMOCFormalization.Sobolev

namespace BEMOC.Definitive

/-- The Riesz exponent for the Sobolev corollary lies in the main theorem's open range. -/
theorem sobolev_exponent_range {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    0 < 2 * s - 2 ∧ 2 * s - 2 < 2 := by constructor <;> linarith

/-- Dividing the energy scale by N² gives the squared Sobolev error exponent. -/
theorem sobolev_normalized_exponent (s : ℝ) :
    (1 - (2 * s - 2) / 2) - 2 = -s := by ring

/-- Dividing by N² and then taking a square root gives the cap discrepancy exponent. -/
theorem cap_normalized_exponent : ((1 : ℝ) - 1 / 2 - 2) / 2 = -3 / 4 := by norm_num

/-- Explicit corollary assembly obligation, including distinctness and the geometric bridge. -/
def CapAssembly : Prop :=
  ConstructionFacts → MainTheorem 1 → DiamondStolarsky → BeckLowerBound →
    CapDiscrepancyCorollary

/-- Explicit Sobolev assembly obligation; supremum boundedness is not implicit. -/
def SobolevAssembly : Prop :=
  ∀ Y : HarmonicBasis, ∀ s : ℝ, 1 < s → s < 2 → ConstructionFacts →
    MainTheorem (2 * s - 2) → SobolevEmbedding Y s →
    SobolevEnergyComparison Y s → SobolevCorollary Y s

/-- Full requested scaffold destination, including existence of the harmonic model. -/
def DefinitiveTargets : Prop :=
  MainTheoremTarget ∧ CapDiscrepancyCorollary ∧ Nonempty HarmonicBasis ∧
    ∀ Y : HarmonicBasis, ∀ s : ℝ, 1 < s → s < 2 →
      SobolevCorollary Y s ∧ SobolevOptimality Y s

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->

**Status and purpose.** `Corollaries.lean` currently proves only three elementary exponent/range lemmas. `CapAssembly`, `SobolevAssembly`, and `DefinitiveTargets` are definitions of propositions; none has an inhabiting theorem. The module imports `MainTheorem`, `CapDiscrepancy`, and `Sobolev`. It corresponds to `definitive.tex:118–192`, with the main energy theorem at `:118–127`, the cap corollary at `:139–147`, and the Sobolev corollary at `:178–192`. Keep assembly theorems small and auditable: all the analysis belongs to the source modules, while this module only transfers rates and combines hypotheses. The chosen output is stronger than the manuscript in quantifying uniformly over every family of ring phases.

**Inputs and their exact meanings.** `MainTheorem α` supplies one `C_α>0` that bounds `deficit α N φ` simultaneously for every `N≥4` and every `φ:Phases N`, plus nonnegativity. It is still a target unless `MainTheoremTarget` is actually proved from the latitude, longitude, small-size, and geometric nonnegative estimates. `ConstructionFacts` supplies population/cardinality and injectivity; its use cannot be dropped because `BeckLowerBound` and `SobolevOptimality` are set statements. `DiamondStolarsky` is the concrete bridge between the actual cap integral and `deficit 1`. `SobolevEnergyComparison Y s` compares the actual spectral WCE to the normalized distance deficit; it is not a definition of WCE. `SobolevEmbedding Y s` establishes that the unit-ball error set underlying `sSup` is bounded. Each named predicate should be inhabited by a theorem before constructing the unconditional destination.

**Cap assembly.** Destruct `MainTheorem 1` as `⟨C₁,hC₁,hmain⟩`. For `N≥4`, derive `(N:ℝ)>0` and use `DiamondStolarsky N hN φ` to rewrite `4*N²*capDiscrepancySq (point N φ)` as `deficit 1 N φ`. The main upper bound is `deficit≤C₁*scale 1 N=C₁*N^(1/2)`. Divide by `4*N²>0`; with `Real.rpow_sub`, `Real.rpow_natCast`, and `scale`, show `N^(1/2)/N²=N^(-3/2)`. Thus `capDiscrepancySq≤(C₁/4)*N^(-3/2)`. Since `capDiscrepancySq≥0`, `capDiscrepancy=Real.sqrt capDiscrepancySq`, and `N>0`, square-root monotonicity gives `capDiscrepancy≤(√C₁/2)*N^(-3/4)`. If positivity of the displayed constant is awkward, choose a larger constant such as `√C₁+1`; its independence from `N` and phases is the relevant point. For the lower bound, prove an equivalence `PointIndex N≃Fin N`, preserve cap discrepancy under reindexing, and transfer injectivity from `ConstructionFacts`; then apply `BeckLowerBound`. An alternative is to derive a universal energy-deficit lower estimate and feed it through Stolarsky. Both halves produce the witnesses for `CapDiscrepancyCorollary`. The displayed `cap_normalized_exponent` checks the exponent arithmetic but does not itself prove the power equality; the latter needs positivity of `N` and real-power laws.

**Sobolev assembly.** Fix `Y` and `s` with `1<s<2`. Set `α=2*s-2`; `sobolev_exponent_range` provides `0<α<2`, which is needed to apply `MainTheoremTarget`. Destruct `MainTheorem α` and `SobolevEnergyComparison Y s` to obtain constants `C_α,A_s>0`. From `SobolevEmbedding Y s`, the zero function in the unit ball, and probability of `sigma`, prove the `sSup` defining WCE is finite and nonnegative. For `N≥4`, use `ConstructionFacts` to show `Fintype.card (PointIndex N)=N`; unfold `diamondEnergy` and `deficit` to rewrite

`continuousEnergy α - energy (point N φ) α / N² = deficit α N φ / N²`.

The comparison gives `WCE²≤A_s*deficit/N²≤A_s*C_α*N^((1-α/2)-2)`. `sobolev_normalized_exponent` turns the exponent into `-s`, so `WCE²≤A_s C_α N^{-s}`. Use `WCE≥0`, `A_s C_α>0`, `N>0`, and square-root/power identities to conclude `WCE≤√(A_s C_α) N^{-s/2}`. As with cap discrepancy, a slightly larger positive constant is acceptable if it simplifies Lean positivity. The quantifier order matters: choose `C_s` after `s` and `Y`, but before `N` and `φ`. The paper fixes a canonical spectral norm; once basis-independence is proved, the witness may be chosen independently of `Y` as well, though the present `SobolevCorollary Y s` does not require that uniformity.

**Optimality and final target.** `SobolevAssembly` concludes only the upper `SobolevCorollary`. The full `DefinitiveTargets` additionally requires `Nonempty HarmonicBasis` and `SobolevOptimality Y s` for **every** harmonic basis, while the cap conjunct requires both Beck lower and upper. Prove harmonic-basis existence in `Sobolev`, universal Sobolev lower there or in a dedicated module, and the cap lower theorem in `CapDiscrepancy`; then combine their resulting theorems with `MainTheoremTarget` and `ConstructionFacts`. The final theorem should have type `DefinitiveTargets` with no arguments. Avoid replacing it by a theorem that assumes the target itself or by a tautological proposition. A conditional theorem `CapAssembly`/`SobolevAssembly` is useful as an intermediate proof but is not the requested completed formalization.

**Small sizes and audit.** The new `MainTheorem` asserts all `N≥4`, whereas the manuscript conducts estimates for `N≥1024` and absorbs smaller sizes. Ensure `SmallSizeBound` is genuinely uniform over all phases before using it. For `N=4` the cap and WCE denominators are safe; in general-purpose lemmas require `0<n`. Verify at the end with `lake build`, a project-owned source scan for `sorry`, `admit`, custom `axiom`, and `opaque`, and a declaration check that the final theorem is inhabited rather than merely named as a `Prop`.
