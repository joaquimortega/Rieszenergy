# Latitude: finite block summation and the uniform size bridge

`Latitude.lean` is the assembly of `definitive.tex` `lem:latitude`, lines 669–735. Its `LatitudeBound α` is a slightly stronger formulation than the printed upper bound: `|latitudeError α N|≤C·scale α N` for all `N≥1024`. This follows because each block contribution is estimated in absolute value. The module also states `SmallSizeBound α` to bridge the manuscript's global large-`N` convention to a theorem for all `N≥4`; that predicate is about the full phase-dependent deficit, not merely the latitude part. Prove the latitude theorem under `0<α<2` and the input contracts `LatitudeIdentity`, `BlockSymmetry`, `ComparableBlockBound`, `SameSideBlockBound`, and `OppositeBlockBound`.

The pair partition must be exhaustive and disjoint enough for finite sums. For any ordered `j,k`, either `r_j/8≤r_k≤8r_j` (comparable), `r_k>8r_j`, or `r_j>8r_k`. The third case is moved to the second using `BlockSymmetry`; the appropriate bound is then selected by `SameSide` versus its negation. The strict comparisons use natural populations, but `Comparable` uses real casts; prove simple equivalence lemmas with `norm_num` or `exact_mod_cast`. The central index `M` is classified in the negated `SameSide` regime. Avoid a partition relying on geographic height signs, because `B_M` straddles the equator. Preserve the ordered pair multiplicity: reverse-oriented unequal pairs contribute a factor at most two, and the two hemispheres contribute another fixed factor. The diagonal is comparable and remains included.

For comparable pairs, use the bound `C_α r_j M^(−α)(1+|j−k|)^(α−3)`. At fixed `j`, dominate the finite `k` sum by the bilateral series `1+2∑_{n≥1}(1+n)^(α−3)`, finite because `3−α>1`. The source says at most `2ζ(3−α)`; formalization can use a p-series theorem or a dyadic geometric majorant. Sum `r_j` exactly to `N`; `N≤C M²` gives `C_α M^(2−α)`. Note that `α−3` is negative, so monotonicity of real powers reverses inequality when comparing distances. This is a frequent Lean coercion pitfall.

For same-side unequal pairs, at a fixed larger population `r`, there is at most one northern and one southern band of that scale; `GeometryBounds` says at most three globally and is enough for a loose constant. The smaller scales satisfy `m<r/8`. Bound `∑_{m<r/8}m³≤C r⁴` and therefore

`M^(−α) ∑_{r≤C M} r^(α−5)∑_{m<r/8}m³ ≤ C_α M^(−α)∑_{r≤C M}r^(α−1)≤C_α`.

When indexing actual populations, north/south values are multiples of four and the central value lies between `4M` and `12M+3`; using a general `r≤15M` bound avoids a needless exact enumeration. For `0<α<2`, the exponent `α−1` is greater than `−1`, so the last sum grows at most `C_α M^α`. A dyadic proof avoids integral rounding details and is valid at `α=1` without special treatment.

For opposite/central unequal pairs, sum the product bound without using the regime condition: `M^(−8)(∑_j r_j³)²`. The bound `r_j≤15M` and `∑_j r_j=N≤C M²` gives `∑r_j³≤(15M)²∑r_j≤C M⁴`, so this entire contribution is `O(1)`. Alternatively sum `j³` on each hemisphere and the central `r_M³`; either route is elementary. Since `M≥16` and `2−α>0`, `O(1)≤C_α M^(2−α)`. Finally `M≈√N` gives `M^(2−α)≤C_α N^(1−α/2)` for `0<α<2`. Combine with `LatitudeIdentity` and triangle inequality for the finite double sum.

`SmallSizeBound α` needs special care. There are finitely many integers `4≤N<1024`, but each `Phases N` is an infinite real-valued function space. Use a uniform diameter estimate: every pair distance on the unit sphere is at most 2, so `diamondEnergy α N φ≤2^α N²` for `α>0` regardless of phases; the deficit is at most `continuousEnergy α N²` if nonnegativity of `diamondEnergy` is used, and `scale α N>0`. Pick the maximum of finitely many ratios, or a coarse bound involving `1024²` and a positive lower bound of `scale` over `4≤N<1024`. This proves phase uniformity rather than appealing to “finitely many configurations.” The full main theorem still needs `DiamondNonnegative α` and `LongitudeBound α`; the latitude absolute estimate alone does not prove either.

Legacy candidates: `legacy/BEMOCFormalization/LatitudePairClassification.lean` for pair cases; `LatitudeFiniteFallback.lean` for finite-range methods; `LatitudeDecomposition.lean` and old row-sum modules for summation patterns. Transfer the mathematical technique, not old target declarations, because the new construction uses a different exact `N` family and explicit phases.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.ComparableBlocks
import BEMOCFormalization.UnequalBlocks

namespace BEMOC.Definitive

/-- Latitude bound after summing the three block regimes. -/
def LatitudeBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N →
    |latitudeError α N| ≤ C * scale α N

/-- Uniform finite-size bound, also uniform over the continuously varying phases. -/
def SmallSizeBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → N < 1024 →
    ∀ φ : Phases N, deficit α N φ ≤ C * scale α N

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
