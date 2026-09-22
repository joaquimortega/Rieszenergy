# UnequalBlocks: same-side decay and opposite/central smoothness

`UnequalBlocks.lean` states the manuscript's `eq:farblock` and `eq:oppositeblock`. Both predicates orient the ordered pair with `r_k>8r_j`, leaving the reverse orientation for `BlockSymmetry` in `Latitude.lean`. `SameSide N j k` means both one-based indices are strictly below `M` or strictly above `M`; its negation deliberately includes the central index `M`. A case split on the one-based index, not merely height signs, is needed because the central band spans both sides of the equator. All block statements assume `N≥1024` and have constants independent of `N`, `j`, and `k`.

For `SameSideBlockBound`, reflect the south hemisphere to the north. The northern population formula gives `r_j=4j`, `r_k=4k`; `r_k>8r_j` implies `k>8j`, so `j≤M/2` and the small band is close to the pole relative to the large one. On the full closed rectangle `s∈B_j`, `t∈B_k`, show `s>t≥0`, `U=2(1−st)>0`, and `U≥c(r_k/M)²`. An efficient exact proof of the separation ratio uses `x=1−k²/N` and boundary formulas:

`8(x−H_{k-1})−(1−xH_k) = (19k²−36k)/N + 4k³(k+1)/N² > 0`.

Since `H_j≥x` when `k>8j`, and `u↦8(u−H_{k-1})−(1−uH_k)` is increasing on the relevant interval, obtain `8(s−t)≥1−st`. The identity `(1−st)²−(1−s²)(1−t²)=(s−t)²` then gives `V/U≤√63/8`. This is a fixed gap below one. On the rectangle, the separated-series kernel admits a common smooth extension and `|mixedFourth|≤C_α U^(α/2−4)≤C_α(r_k/M)^(α−8)`; note `α/2−4<0`, so lower bounding `U` gives an upper derivative bound. `MixedTaylorBound` produces `r_j³r_k³/M⁸ · (r_k/M)^(α−8)=r_j³/(M^α r_k^(5−α))`. Do not replace the strict factor 8 with a merely “far apart” assertion without proving a uniform `ε`.

For `OppositeBlockBound`, after orienting and reflecting, place the small band in the north. It cannot be central: `r_M≥4M` and no occupied band has population more than `12M+3`, so `r_k>8r_M` is impossible. If `M/2<j<M`, then `r_j>2M` and `r_M≤12M+3≤8r_j` for `M≥16`; a southern large band at the same or reflected scale is also at most `4(M−1)≤8r_j`. Hence noncomparability forces `j≤M/2`. The boundary formula yields `s≥H_j≥23/32>2/3`. If `k>M`, its entire band lies in the southern half so `t≤0`; if `k=M`, its upper endpoint satisfies `t≤r_M/N≤195/1024<1/5`. Therefore `t≤1/5`, `U=2−2st≥8/5`, and by monotonicity `(s−t)/(1−st)≥7/13`. The same algebraic identity gives `V/U≤√120/13<15/16`. The separated mixed derivative is now bounded by an `α`-dependent constant because `U` is bounded below by a positive absolute constant. Apply the mixed Taylor estimate to obtain `C_α r_j³r_k³/M⁸`.

The reflection map must preserve the kernel, band populations, band endpoints, midpoint heights, and `bandError` signs. Reflection of both variables changes the sign of each first-moment coordinate but leaves the two-moment cancellation and the energy kernel unchanged. For central pairs, `k=M` is the larger scale and the central interval crosses height zero, yet `t≤1/5` remains enough; no “opposite hemisphere” argument alone covers this case. The proof should expose a finite arithmetic lemma that from `r_k>8r_j` and `¬SameSide` derives the reduced northern configuration. This avoids hidden exhaustive case reasoning in the final analytic estimate.

Legacy candidates include `legacy/BEMOCFormalization/LatitudePairClassification.lean` for side and central cases, `LatitudeComparableGeometry.lean` for reflected rectangles, `LatitudeSmoothOppositeBlocks.lean` and `LatitudeUnequalSeries.lean` for smooth separated estimates. Check every candidate against the new population formula and the contract's strict factor 8. Dependencies are `KernelDerivatives`, `Taylor`, `Geometry`, and `BlockSymmetry`; the latter is needed only when the final sum reverses orientation.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.KernelDerivatives

namespace BEMOC.Definitive

/-- Strictly on the same side; the central index is excluded. -/
def SameSide (N j k : ℕ) : Prop :=
  (j < bandParameter N ∧ k < bandParameter N) ∨
    (bandParameter N < j ∧ bandParameter N < k)

/-- Unequal scales in one hemisphere, oriented with k the larger population. -/
def SameSideBlockBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
    8 * population N (j.val + 1) < population N (k.val + 1) →
    SameSide N (j.val + 1) (k.val + 1) →
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
      C * (population N (j.val + 1) : ℝ) ^ 3 /
        ((bandParameter N : ℝ) ^ α * (population N (k.val + 1) : ℝ) ^ (5 - α))

/-- Unequal opposite/central blocks; the central band belongs in this regime. -/
def OppositeBlockBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
    8 * population N (j.val + 1) < population N (k.val + 1) →
    ¬SameSide N (j.val + 1) (k.val + 1) →
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
      C * (population N (j.val + 1) : ℝ) ^ 3 *
        (population N (k.val + 1) : ℝ) ^ 3 / (bandParameter N : ℝ) ^ 8

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
