# ComparableBlocks: all equal-scale latitude interactions

`ComparableBlocks.lean` states `ComparableBlockBound α`, the manuscript's `eq:comparableblock` in Lemma `blocks`. The predicate `Comparable N j k` is exactly `r_j/8≤r_k≤8r_j`, with real casts to avoid truncated natural division. The source proof assumes `N≥1024`, hence `M≥16`; this assumption already appears globally in `definitive.tex` around line 274 and explicitly in the Lean contract. Let `ℓ=|j−k|` and `r=r_j≈r_k`. The zero-based difference in the Lean RHS is equal to the one-based source difference. State separate helper lemmas for polar endpoints, regular close bands (`ℓ≤2`), regular intermediate separation (`3≤ℓ≤2r`), and regular far separation (`ℓ>2r`), then combine them by exhaustive finite arithmetic.

First, handle a polar endpoint. After swapping indices and reflecting north/south, take `j=1`, so `r_j=4` and comparability forces `r_k≤32`. Since the equatorial population is at least `4M≥64`, either `k≤8` or `2M−k≤8`. In the first branch, `φ+ψ≤C/M` throughout both polar bands; `D≤C/M` uniformly in angle. Use `|bandError f|≤2r sup|f|` twice to bound the block by `C_α M^(−α)`. Here `ℓ≤7`, so this implies `C_α r M^(−α)(1+ℓ)^(α−3)` after absorbing fixed constants. In the opposite-pole branch, `s≥127/128`, `t≤0`, `2≤U≤4`, `V/U≤1/2`. Obtain a rectangle-level smooth extension from `SeparatedDerivativeBound` and invoke `MixedTaylorBound` to get `C_α M^(−8)` because both populations are bounded by 32. As `ℓ≈M`, the desired bound is of order `M^(−3)` for every `α`; `M^(−8)` is stronger. The reflection identity for `F_α(−s,−t)=F_α(s,t)` proves the south case.

For nonpolar bands use `AngularGeometry`: `sinφ,sinψ≈r/M` on the full angle intervals, even when one band is central (its population is `≈M`). If `3≤ℓ≤2r`, angular separation yields `D²≥c[(ℓ/M)²+(rθ/M)²]`. Apply the four-term height derivative bound from `KernelDerivatives`, integrate in `θ`, and split at `θ=ℓ/r`. The needed integrals of `D^(α−4)` and `D^(α−3)` scale respectively as `M^(4−α)ℓ^(α−3)/r` and `M^(3−α)ℓ^(α−2)/r`. For `D^(α−2)`, split **three ways**: `α<1` gives `M^(2−α)ℓ^(α−1)/r`; `α=1` gives `(M/r)log(2+r/ℓ)`; `α>1` gives `(r/M)^(α−2)`. Relative to the leading term, the subsidiary terms are bounded by `ℓ/r`, `(ℓ/r)²`, `(ℓ/r)²log(2+r/ℓ)`, or `(ℓ/r)^(3−α)`, all bounded on `0<ℓ/r≤2`. Therefore `sup|∂²_s∂²_tF_α|≤C_α M^(8−α)ℓ^(α−3)/r⁵`, and `MixedTaylorBound` gives the target.

If `ℓ≤2`, the untruncated kernel can have a diagonal cusp; no `C⁴` statement for it should be used. Split the angular average at `θ₀=1/r`. The low-angle part has `D≤C/M` because `|φ−ψ|≤C/M` and `rθ/M≤1/M`; its angular length is `1/r`, so `|F_lo|≤C_α/(rM^α)`. Two TV bounds contribute `r²`, giving `C_α r/M^α`. For the high-angle part, `D≥c/M` uniformly, including on a touching or identical rectangle. Differentiate under its integral and repeat the four-term estimate with lower cutoff `1/r` to obtain `C_α M^(8−α)/r⁵`; Taylor gives the same target. This branch also handles the exact diagonal `j=k`.

If `ℓ>2r`, `U−V=2(1−cos(φ−ψ))≈(ℓ/M)²`, `V≤C(r/M)²`, and `U≈(ℓ/M)²`; hence `V≤(1−ε)U` with an absolute `ε>0`. The separated derivative and Taylor bounds give `C_α r⁶M^(−8)(ℓ/M)^(α−8)`. Divide by the desired expression: the ratio is `(r/ℓ)^5≤2^(−5)`. This case can include bands across the equator with comparable populations. Legacy candidates are `LatitudePolarBlocks.lean`, `LatitudeComparableGeometry.lean`, and `LatitudeDiagonalCuspBlocks.lean`, but the old work may use a more complex cusp decomposition; the manuscript's angle cutoff offers a direct route.

The final case split should be stated with exact natural inequalities to avoid an unhandled boundary at `ℓ=2` or `ℓ=2r`: use `ℓ≤2`, `3≤ℓ∧ℓ≤2r`, and `2r<ℓ`. Since `r` is a positive integer population, `1/r` lies in `(0,π)`, so both angular pieces are legitimate. The constants in each local estimate may differ; take their maximum, then enlarge it once to absorb the finitely many endpoint and reflection factors. This produces one existential `C` for the whole `ComparableBlockBound` contract, as required by the Lean statement.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.KernelDerivatives

namespace BEMOC.Definitive

/-- Symmetric scale-comparability predicate, using real rather than truncated division. -/
def Comparable (N j k : ℕ) : Prop :=
  (population N j : ℝ) / 8 ≤ population N k ∧
    (population N k : ℝ) ≤ 8 * population N j

/-- The full comparable estimate, including equal, adjacent, polar, and opposite bands. -/
def ComparableBlockBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
    Comparable N (j.val + 1) (k.val + 1) →
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
      C * population N (j.val + 1) / (bandParameter N : ℝ) ^ α *
        (1 + |(j.val : ℝ) - k.val|) ^ (α - 3)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
