# Taylor: two-moment cancellation on a closed rectangle

`Taylor.lean` isolates Appendix 2's `eq:one-variable-taylor` and `eq:two-variable-taylor`. The analytic input is elementary but its hypotheses matter: a function `G` must be `C⁴` on an open neighborhood `W` of the entire closed product `B_j×B_k`, and its fourth mixed height derivative must be bounded there on the rectangle. The `MixedTaylorBound` contract states exactly the estimate later consumed by the separated and truncated-kernel cases. Do not apply it to the full latitude kernel on equal or adjacent bands, where the angular cusp invalidates the needed regularity. At a polar boundary, differentiating the raw square-root formula also fails; a smooth extension supplied by the separated-series argument is required.

Start with a one-variable lemma for a linear functional `L` that annihilates `1` and `id`. For any basepoint `x₀` in an interval of length `a`, Taylor's integral remainder gives `f(x)=f(x₀)+f'(x₀)(x−x₀)+R(x)` and `|R(x)|≤(a²/2) sup_I|f''|`. Applying `bandError` kills the affine part and leaves an absolute bound `≤(r_j a²) sup|f''|`, because its underlying signed measure has total variation at most `2r_j`. An equivalent direct calculation avoids signed measures: bound the continuous integral of `R` by `r_j sup|R|` and the atomic term by `r_j sup|R|`. Choose a basepoint inside the interval; `h_j` is convenient and reduces some interval-width constants, though the manuscript uses any point.

The exact band width is `a_j=2r_j/N`. From `4M²≤N`, `a_j≤r_j/(2M²)≤r_j/M²`. Applying the one-variable lemma first in `t` and then in `s` yields a coefficient at most `(r_j³r_k³)/(M⁸)`; the manuscript uses the somewhat loose factor at each stage. Keep an explicit denominator positivity proof for `M≥1`. For `j,k : RingIndex N`, `4≤N` implies `M≥1`; `ConstructionFacts` already contains this. Because `bandBlock` applies `k` inside `j`, a clean proof fixes `s`, estimates the `t` error, then differentiates the resulting function twice in `s`. The derivative and finite-interval integral commute under `ContDiffOn ℝ 4 G W`; prove the resulting mixed derivative equals `mixedFourth G`, or switch the application order to match `mixedFourth`'s exact nesting. The `C⁴` assumption gives equality of the mixed partial orders. Check the Lean `iteratedDeriv 2` convention at both levels and use `ContinuousLinearMap` or standard one-dimensional differentiation-under-integral lemmas rather than rewriting derivatives formally.

The contract uses `W` and `Set.prod` explicitly. The band rectangles are compact; all desired derivatives are continuous and bounded there. A reusable bridge should take a locally `C⁴` family of extensions whose values agree with the physical kernel and produce one rectangle-level witness, so that callers do not repeat gluing. If this proves awkward, state and prove a version of the Taylor lemma for `ContDiffOn` on an open set containing just the rectangle and define a canonical separated-series extension on that set. In either approach, prevent a pointwise `∃G` from being mistaken for a global `G`.

Legacy candidate: `legacy/BEMOCFormalization/MixedTaylorRemainder.lean`, especially `TwoMomentFunctional.abs_pairEval_le_of_mixedDerivative` and `abs_bandPairError_le_of_mixedDerivative`. It may offer an efficient abstract proof, but the old functional types and band normalization differ. `LatitudeBands.lean` supplies the moment cancellation used by those lemmas. This module's immediate dependency is `BandErrors`; downstream analytic blocks should cite this theorem rather than re-prove Taylor estimates.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.BandErrors

namespace BEMOC.Definitive

/-- Two derivatives in each height variable, in a fixed order. -/
noncomputable def mixedFourth (G : ℝ × ℝ → ℝ) (s t : ℝ) : ℝ :=
  iteratedDeriv 2 (fun u => iteratedDeriv 2 (fun v => G (u, v)) t) s

/-- The two-moment estimate for a C⁴ extension around a closed rectangle. -/
def MixedTaylorBound : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ j k : RingIndex N,
    ∀ G : ℝ × ℝ → ℝ, ∀ W : Set (ℝ × ℝ), IsOpen W →
      (band N (j.val + 1) ×ˢ band N (k.val + 1)) ⊆ W →
      ContDiffOn ℝ 4 G W → ∀ L : ℝ, 0 ≤ L →
      (∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
        |mixedFourth G p.1 p.2| ≤ L) →
      |bandBlock N (j.val + 1) (k.val + 1) G| ≤
        (population N (j.val + 1) : ℝ) ^ 3 *
          (population N (k.val + 1) : ℝ) ^ 3 / (bandParameter N : ℝ) ^ 8 * L

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
