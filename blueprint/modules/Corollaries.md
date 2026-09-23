# `BEMOCFormalization.Corollaries` proof guide

Checked result: `cap_corollary`, `sobolev_energy_comparison`, and `sobolev_corollary` are unconditional in the stated exponent ranges, and `definitive_targets : DefinitiveTargets` packages the main theorem and both corollaries with harmonic-basis existence and Sobolev optimality. The earlier `cap_assembly` and `sobolev_assembly` remain useful conditional assembly lemmas. Every statement uses the actual discrepancy and spectral WCE definitions.

The strongest cap assembly is now `cap_corollary_of_main`. Its only input
is `MainTheorem 1`: construction and exact cardinality come from
`constructionFacts`, the ordinary-dt geometric identity from
`diamondStolarsky`, and the universal lower bound from `beckLowerBound` in
`CapLowerBound`. The lower constant supplied there is 1/16. Normalizing the
energy bound by N² and taking a square root yields exponent −3/4; the proof
retains a positive upper constant uniform in all ring phases. The unconditional `cap_corollary` supplies this input with `main_theorem` at α=1.

With both unequal regimes now proved, `cap_corollary_of_comparable`
reduces the cap corollary to `ComparableBlockBound 1`. The unconditional `comparable_block_bound` now discharges this input; `cap_corollary_of_comparable` remains a useful intermediate form.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.MainTheorem
import BEMOCFormalization.CapDiscrepancy
import BEMOCFormalization.CapLowerBound
import BEMOCFormalization.Sobolev
import BEMOCFormalization.HarmonicBasisExistence
import BEMOCFormalization.DistanceScalarBridge
import BEMOCFormalization.HarmonicAdditionLegendre
import BEMOCFormalization.SobolevMomentSpectral

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

/-- The main theorem and both corollaries, including existence of the harmonic model. -/
def DefinitiveTargets : Prop :=
  MainTheoremTarget ∧ CapDiscrepancyCorollary ∧ Nonempty HarmonicBasis ∧
    ∀ Y : HarmonicBasis, ∀ s : ℝ, 1 < s → s < 2 →
      SobolevCorollary Y s ∧ SobolevOptimality Y s


/-- Normalizing an energy estimate divides its real power by the square of the population. -/
theorem rpow_div_sq {x : ℝ} (hx : 0 < x) (a : ℝ) :
    x ^ a / x ^ 2 = x ^ (a - 2) := by
  rw [Real.rpow_sub hx]
  norm_num

/-- Squaring a positive-base real power doubles its exponent. -/
theorem sq_rpow {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

/-- Turn a squared power bound into a square-root bound with explicit positive constant. -/
theorem nonneg_le_sqrt_mul_rpow {e c x a : ℝ} (hc : 0 < c) (hx : 0 < x)
    (h : e ^ 2 ≤ c * x ^ (2 * a)) :
    e ≤ Real.sqrt c * x ^ a := by
  have hsq : (Real.sqrt c * x ^ a) ^ 2 = c * x ^ (2 * a) := by
    rw [mul_pow, Real.sq_sqrt hc.le, sq_rpow hx.le]
  have hp : 0 ≤ Real.sqrt c * x ^ a := by positivity
  nlinarith


/-- The actual cap corollary follows from its geometric identity and the universal lower bound. -/
theorem cap_assembly : CapAssembly := by
  intro hcon hmain hstol hbeck
  obtain ⟨c, hc, hlower⟩ := diamond_beck_lower_of hcon hbeck
  obtain ⟨C, hC, hupper⟩ := hmain
  refine ⟨c, Real.sqrt C, hc, Real.sqrt_pos.2 hC, ?_⟩
  intro N hN φ
  refine ⟨hlower N hN φ, ?_⟩
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hn2 : 0 < (N : ℝ) ^ 2 := by positivity
  have hd : 0 ≤ capDiscrepancySq (point N φ) := capDiscrepancySq_nonneg _
  have he := (hupper N hN φ).2
  have hs := hstol N hN φ
  have hp : (N : ℝ) ^ 2 * (N : ℝ) ^ (2 * (-(3 : ℝ) / 4)) = scale 1 N := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn]
    norm_num [scale]
  have he' : (N : ℝ) ^ 2 * capDiscrepancySq (point N φ) ≤ C * scale 1 N := by
    nlinarith [mul_nonneg (le_of_lt hn2) hd]
  have hsq : capDiscrepancy (point N φ) ^ 2 ≤
      C * (N : ℝ) ^ (2 * (-(3 : ℝ) / 4)) := by
    rw [capDiscrepancy, Real.sq_sqrt hd]
    apply (mul_le_mul_left hn2).mp
    calc
      (N : ℝ) ^ 2 * capDiscrepancySq (point N φ) ≤ C * scale 1 N := he'
      _ = (N : ℝ) ^ 2 * (C * (N : ℝ) ^ (2 * (-(3 : ℝ) / 4))) := by rw [← hp]; ring
  exact nonneg_le_sqrt_mul_rpow hC hn hsq

/-- The cap corollary now requires only the energy theorem and universal lower bound. -/
theorem cap_corollary_of_main_and_beck (hmain : MainTheorem 1)
    (hbeck : BeckLowerBound) : CapDiscrepancyCorollary :=
  cap_assembly constructionFacts hmain diamondStolarsky hbeck

/-- Both geometric cap inputs are proved; only the energy theorem remains. -/
theorem cap_corollary_of_main (hmain : MainTheorem 1) : CapDiscrepancyCorollary :=
  cap_corollary_of_main_and_beck hmain beckLowerBound

/-- The cap corollary is reduced to the comparable-band estimate at exponent one. -/
theorem cap_corollary_of_comparable (hc : ComparableBlockBound 1) :
    CapDiscrepancyCorollary :=
  cap_corollary_of_main (main_theorem_of_comparable (by norm_num) (by norm_num) hc)

/-- Conditional transfer from the actual spectral WCE comparison to the paper's decay rate. -/
theorem sobolev_assembly : SobolevAssembly := by
  intro Y s _hs1 _hs2 hcon hmain _hemb hcomp
  obtain ⟨A, hA, hcomp⟩ := hcomp
  obtain ⟨C, hC, hmain⟩ := hmain
  refine ⟨Real.sqrt (A * C), Real.sqrt_pos.2 (mul_pos hA hC), ?_⟩
  intro N hN φ
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hn2 : 0 < (N : ℝ) ^ 2 := by positivity
  let e : PointIndex N ≃ Fin N :=
    Fintype.equivFinOfCardEq (pointIndex_card_of_constructionFacts hcon N hN)
  have hcomparison := hcomp N (by omega) (point N φ ∘ e.symm)
  rw [sobolevWCE_comp_equiv, energy_comp_equiv] at hcomparison
  have hid : continuousEnergy (2 * s - 2) - energy (point N φ) (2 * s - 2) / (N : ℝ)^2 =
      deficit (2 * s - 2) N φ / (N : ℝ)^2 := by
    unfold deficit diamondEnergy
    field_simp
  rw [hid] at hcomparison
  have hpower : scale (2 * s - 2) N / (N : ℝ)^2 = (N : ℝ)^(-s) := by
    unfold scale
    rw [rpow_div_sq hn, sobolev_normalized_exponent]
  have hnormalized : deficit (2 * s - 2) N φ / (N : ℝ)^2 ≤ C * (N : ℝ)^(-s) := by
    calc
      deficit (2 * s - 2) N φ / (N : ℝ)^2 ≤ C * scale (2 * s - 2) N / (N : ℝ)^2 :=
        div_le_div_of_nonneg_right (hmain N hN φ).2 hn2.le
      _ = C * (N : ℝ)^(-s) := by rw [mul_div_assoc, hpower]
  have hsq : sobolevWCE Y s (point N φ)^2 ≤ (A * C) * (N : ℝ)^(2 * (-s / 2)) := by
    have hh := hcomparison.trans (mul_le_mul_of_nonneg_left hnormalized hA.le)
    convert hh using 1 <;> ring
  exact nonneg_le_sqrt_mul_rpow (mul_pos hA hC) hn hsq

/-- Optimal spherical cap discrepancy for every Diamond configuration and all ring phases. -/
theorem cap_corollary : CapDiscrepancyCorollary :=
  cap_corollary_of_main (main_theorem (by norm_num) (by norm_num))

/-- The actual spectral Sobolev worst-case error is controlled by the Riesz deficit. -/
theorem sobolev_energy_comparison (Y : HarmonicBasis) {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) : SobolevEnergyComparison Y s :=
  sobolevEnergyComparison_of_addition Y hs1 hs2 (harmonic_addition_legendre Y)

/-- Optimal-order Sobolev cubature for every Diamond configuration in the range 1 < s < 2. -/
theorem sobolev_corollary (Y : HarmonicBasis) {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) : SobolevCorollary Y s :=
  sobolev_assembly Y s hs1 hs2 constructionFacts
    (main_theorem (sobolev_exponent_range hs1 hs2).1 (sobolev_exponent_range hs1 hs2).2)
    (sobolevEmbedding_of_harmonicAddition Y hs1) (sobolev_energy_comparison Y hs1 hs2)

/-- The complete, unconditional formalization of the main theorem and both corollaries. -/
theorem definitive_targets : DefinitiveTargets := by
  refine ⟨main_theorem_target, cap_corollary, harmonicBasis_nonempty, ?_⟩
  intro Y s hs1 hs2
  exact ⟨sobolev_corollary Y hs1 hs2, sobolevOptimality Y hs1 hs2⟩

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->

**Status and purpose.** `Corollaries.lean` proves the exponent/range lemmas and both conditional assembly contracts. `definitive_targets` proves the full `DefinitiveTargets` proposition. The module imports `MainTheorem`, `CapDiscrepancy`, and `Sobolev`. It corresponds to `definitive.tex:118–192`, with the main energy theorem at `:118–127`, the cap corollary at `:139–147`, and the Sobolev corollary at `:178–192`. Keep assembly theorems small and auditable: all the analysis belongs to the source modules, while this module only transfers rates and combines hypotheses. The chosen output is stronger than the manuscript in quantifying uniformly over every family of ring phases.

**Inputs and their exact meanings.** `MainTheorem α` supplies one `C_α>0` that bounds `deficit α N φ` simultaneously for every `N≥4` and every `φ:Phases N`, plus nonnegativity. `main_theorem_target` proves this contract from the latitude, longitude, small-size, and geometric nonnegative estimates. `ConstructionFacts` supplies population/cardinality and injectivity; its use cannot be dropped because `BeckLowerBound` and `SobolevOptimality` are set statements. `DiamondStolarsky` is the concrete bridge between the actual cap integral and `deficit 1`. `SobolevEnergyComparison Y s` compares the actual spectral WCE to the normalized distance deficit; it is not a definition of WCE. `SobolevEmbedding Y s` establishes that the unit-ball error set underlying `sSup` is bounded. Each named predicate is inhabited by a theorem used in the unconditional destination.

**Cap assembly.** Destruct `MainTheorem 1` as `⟨C₁,hC₁,hmain⟩`. For `N≥4`, derive `(N:ℝ)>0` and use `DiamondStolarsky N hN φ` to rewrite `4*N²*capDiscrepancySq (point N φ)` as `deficit 1 N φ`. The main upper bound is `deficit≤C₁*scale 1 N=C₁*N^(1/2)`. Divide by `4*N²>0`; with `Real.rpow_sub`, `Real.rpow_natCast`, and `scale`, show `N^(1/2)/N²=N^(-3/2)`. Thus `capDiscrepancySq≤(C₁/4)*N^(-3/2)`. Since `capDiscrepancySq≥0`, `capDiscrepancy=Real.sqrt capDiscrepancySq`, and `N>0`, square-root monotonicity gives `capDiscrepancy≤(√C₁/2)*N^(-3/4)`. If positivity of the displayed constant is awkward, choose a larger constant such as `√C₁+1`; its independence from `N` and phases is the relevant point. For the lower bound, prove an equivalence `PointIndex N≃Fin N`, preserve cap discrepancy under reindexing, and transfer injectivity from `ConstructionFacts`; then apply `BeckLowerBound`. An alternative is to derive a universal energy-deficit lower estimate and feed it through Stolarsky. Both halves produce the witnesses for `CapDiscrepancyCorollary`. The displayed `cap_normalized_exponent` checks the exponent arithmetic but does not itself prove the power equality; the latter needs positivity of `N` and real-power laws.

**Sobolev assembly.** Fix `Y` and `s` with `1<s<2`. Set `α=2*s-2`; `sobolev_exponent_range` provides `0<α<2`, which is needed to apply `MainTheoremTarget`. Destruct `MainTheorem α` and `SobolevEnergyComparison Y s` to obtain constants `C_α,A_s>0`. From `SobolevEmbedding Y s`, the zero function in the unit ball, and probability of `sigma`, prove the `sSup` defining WCE is finite and nonnegative. For `N≥4`, use `ConstructionFacts` to show `Fintype.card (PointIndex N)=N`; unfold `diamondEnergy` and `deficit` to rewrite

`continuousEnergy α - energy (point N φ) α / N² = deficit α N φ / N²`.

The comparison gives `WCE²≤A_s*deficit/N²≤A_s*C_α*N^((1-α/2)-2)`. `sobolev_normalized_exponent` turns the exponent into `-s`, so `WCE²≤A_s C_α N^{-s}`. Use `WCE≥0`, `A_s C_α>0`, `N>0`, and square-root/power identities to conclude `WCE≤√(A_s C_α) N^{-s/2}`. As with cap discrepancy, a slightly larger positive constant is acceptable if it simplifies Lean positivity. The quantifier order matters: choose `C_s` after `s` and `Y`, but before `N` and `φ`. The paper fixes a canonical spectral norm; once basis-independence is proved, the witness may be chosen independently of `Y` as well, though the present `SobolevCorollary Y s` does not require that uniformity.

**Optimality and final target.** `SobolevAssembly` concludes only the upper `SobolevCorollary`. The full `DefinitiveTargets` additionally requires `Nonempty HarmonicBasis` and `SobolevOptimality Y s` for **every** harmonic basis, while the cap conjunct requires both Beck lower and upper. `HarmonicBasisExistence`, `SobolevMomentSpectral`, and `CapLowerBound` supply those three inputs; `definitive_targets` combines them with `main_theorem_target` and the unconditional cap and Sobolev corollaries. Its type is `DefinitiveTargets` with no arguments. Avoid replacing it by a theorem that assumes the target itself or by a tautological proposition. A conditional theorem `CapAssembly`/`SobolevAssembly` is useful as an intermediate proof but is not the requested completed formalization.

**Small sizes and audit.** The new `MainTheorem` asserts all `N≥4`, whereas the manuscript conducts estimates for `N≥1024` and absorbs smaller sizes. Ensure `SmallSizeBound` is genuinely uniform over all phases before using it. For `N=4` the cap and WCE denominators are safe; in general-purpose lemmas require `0<n`. The final audit checks `lake build`, scans for `sorry`, `admit`, custom `axiom`, and `opaque`, and checks that `definitive_targets` inhabits the proposition rather than merely naming it.

The universal and Diamond Stolarsky identities are now proved independently
of energy bounds. Accordingly, `cap_corollary_of_main_and_beck` needs only
`MainTheorem 1` and `BeckLowerBound`; the construction and invariance principle
are supplied by checked witnesses.
