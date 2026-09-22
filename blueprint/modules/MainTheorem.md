# MainTheorem proof guide

Checked progress: `main_theorem_of_latitude_longitude` now derives the main bound from only `LatitudeBound` and `LongitudeBound` in the open exponent range. `diamond_nonnegative` and the phase-uniform `small_size_bound` discharge the other inputs. The two upper estimates remain open. The detailed plan below explains their remaining dependencies.

Source anchors: `definitive.tex` Theorem `thm:main` and inequality `theo:ineq` (around lines 118–126); construction threshold and proof cutoff (line 274); longitude bound `lem:BalphaN` (around 438–540); latitude block lemma and summed estimate `lem:blocks`/`lem:latitude` (around 620–730). The public goal is a constant depending only on `α` for **every** `N≥4` and **every** choice of phases. The manuscript names one zero-phase convention but explicitly says the estimates survive arbitrary rotations; the phase-uniform Lean target is therefore a faithful strengthening.

`MainTheorem α` states `∃C>0, ∀N≥4, ∀φ, 0≤deficit α N φ≤C*scale α N`. `MainTheoremTarget` supplies `0<α` and `α<2` before that conclusion. The existing `main_theorem_of_estimates` is a sound assembly theorem: it accepts absolute latitude and longitude bounds, a small-size upper bound, and geometric deficit nonnegativity. It takes the sum of their positive constants. On `N≥1024`, use the exact algebraic decomposition and `x≤|x|` twice; on `4≤N<1024`, use `SmallSizeBound`. Since `scale≥0`, increasing either constant preserves the bound. The finite cutoff needs no dependence on phase, despite phases ranging over continuum many choices.

To inhabit `LatitudeBound α`, first prove `BandMoments`, `LatitudeIdentity`, and `BlockSymmetry` from `BandErrors`. The block lemma divides ordered pairs into comparable populations `r_j/8≤r_k≤8r_j`, or, after possibly swapping `j,k`, into the orientation `r_k>8r_j`. The oriented unequal pairs split into `SameSide` (both ordinary rings north or both south) and its negation (opposite hemispheres or a central ring). Prove this classifier in Lean, including the reverse inequality case and symmetry of `kernelBlock`, before summing. Comparable blocks contribute `C M^{-α} Σ_j r_j Σ_k(1+|j−k|)^(α−3)`. Since `α<2`, exponent `3−α>1` gives a uniform offset-series bound; `Σr_j=N≍M²`, hence `O(M^(2−α))`. Same-side unequal blocks give `O(1)` after summing smaller populations cubed and the larger scale power; the manuscript enlarges a sparse `4j` population sum to all integer scales, but a direct finite index sum may be easier in Lean. Opposite or central unequal blocks are bounded by `M^{-8}(Σr_j³)²=O(1)` using `r_j≤15M` and `O(M)` bands. Because `M≥16` and `2−α>0`, both `O(1)` terms are absorbed into `O(M^(2−α))`. Convert `M^(2−α)` to `N^(1−α/2)` with square bounds.

The three block estimates are the major mathematical burden. Comparable diagonal and adjacent blocks see the angular cusp at coincident latitudes; the appendix splits small angles around `1/r` and uses Taylor only on the smooth remainder. Separated blocks use polar separation and derivative bounds. Same-side unequal blocks have a delicate height/radius imbalance; opposite or central blocks use a smoother derivative regime. `M≥16` is used in the appendix, so these estimates should carry `1024≤N` as the current contracts do. A plain two-moment Taylor estimate with a global fourth mixed derivative supremum would be invalid on the diagonal. Preserve the exact exponent and the `r_j` orientation in each estimate before any summation.

To inhabit `LongitudeBound α`, apply the phase-uniform trapezoid lemma to `G(θ)=(A−B cos θ)^(α/2)` with `A≥B≥0`. For rings `j,k`, the multiset of differences between the `r_j` and `r_k` polygon angles consists of `L=lcm(r_j,r_k)` equally spaced angles, each with multiplicity `d=gcd(r_j,r_k)`. Thus the ordered cross-ring error is bounded by `C_α M^{-α} d^(1+α)/(r_jr_k)^(α/2)`, using `r_j≍Mρ_j`. Population multiplicity at most three and `r_j≤15M` reduce the total to `gcdSum α (15M)`. Write `u=da`, `v=db`; the resulting sum is `O_α(M²)` because `α>0` makes the relevant double p-series convergent. This proves `O(M^(2−α))`, uniformly in all phase differences. It includes within-ring diagonal pairs without a special exclusion.

For `SmallSizeBound α`, handle each of the finitely many integers `4≤N<1024` with a *phase-independent* estimate. Under `α>0`, every pair distance on the unit sphere is at most `2`, so `0≤diamondEnergy≤2^α N²`, and `deficit≤I_αN²`. The scale is strictly positive for these `N`; choose one explicit constant from the endpoint bound, or take a finite maximum over integer `N`. This avoids invoking compactness of the phase space. `DiamondNonnegative α` comes from the measure-level negative-type result and exact cardinality, as detailed in ContinuousEnergy and EnergyDecomposition.

Finally prove `MainTheoremTarget` by fixing `α`, obtaining the four inputs with their `0<α<2` hypotheses, and applying `main_theorem_of_estimates`. Add a named corollary for `zeroPhases` and the associated `N`-element finite set to mirror the manuscript's `\mathcal P_N`. The project should describe its status honestly until that final theorem is inhabited: `def MainTheoremTarget : Prop` is a statement, and the proved assembly has analytic hypotheses. No `sorry`, `admit`, custom axiom, or opaque shortcut is needed or appropriate.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Latitude
import BEMOCFormalization.Longitude

namespace BEMOC.Definitive

/-- Main theorem target, with constants uniform over every N and every choice of phases. -/
def MainTheorem (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N,
    0 ≤ deficit α N φ ∧ deficit α N φ ≤ C * scale α N

/-- Proved assembly; analytic estimates and geometric nonnegativity remain explicit inputs. -/
theorem main_theorem_of_estimates {α : ℝ}
    (hlat : LatitudeBound α) (hlong : LongitudeBound α)
    (hsmall : SmallSizeBound α) (hnonneg : DiamondNonnegative α) : MainTheorem α := by
  obtain ⟨A, hA, hlat⟩ := hlat
  obtain ⟨B, hB, hlong⟩ := hlong
  obtain ⟨S, hS, hsmall⟩ := hsmall
  refine ⟨A + B + S, by positivity, ?_⟩
  intro N hN φ
  refine ⟨hnonneg N hN φ, ?_⟩
  have hscale : 0 ≤ scale α N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  by_cases hlarge : 1024 ≤ N
  · have ha := (le_abs_self (latitudeError α N)).trans (hlat N hlarge)
    have hb := (le_abs_self (longitudeError α N φ)).trans (hlong N hN φ)
    rw [deficit_eq_latitude_add_longitude]
    nlinarith [mul_nonneg (le_of_lt hS) hscale]
  · have hs := hsmall N hN (by omega) φ
    nlinarith [mul_nonneg (le_of_lt hA) hscale, mul_nonneg (le_of_lt hB) hscale]

/-- Complete unconditional statement to be proved; no proof of this target is asserted. -/
def MainTheoremTarget : Prop := ∀ α : ℝ, 0 < α → α < 2 → MainTheorem α

/-- The remaining analytic burden is exactly the latitude and longitude upper estimates. -/
theorem main_theorem_of_latitude_longitude {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hlat : LatitudeBound α) (hlong : LongitudeBound α) : MainTheorem α :=
  main_theorem_of_estimates hlat hlong (small_size_bound hα2) (diamond_nonnegative hα0 hα2)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
