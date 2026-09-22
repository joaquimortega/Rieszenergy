# Geometry proof guide

Source anchors: `definitive.tex` `eq:geometry` near lines 359–367; polar geometry and chordal-distance comparisons in the latitude appendix, especially around lines 1286–1352 and the separated-band arguments around 1587–1731. The module converts exact Construction formulas into bounds with constants independent of `N`, ring index, and phase. `GeometryBounds` applies already for `N≥4`; `AngularGeometry` is deliberately restricted to `M≥16` and is for the analytic block lemmas.

Start from `0<h_j<1` on northern noncentral rings, `h_M=0`, and reflection. For `1≤j<M`, put `x=4j²/N`; then `h_j=1−x` and `ρ_j²=1−h_j²=x(2−x)`. The square bounds imply `j/M` and `sqrt x` are comparable by absolute constants; `x<1` for these rings. Therefore `ρ_j` is comparable to `j/M`, while `r_j=4j` is comparable to `Mρ_j`. The southern case follows by symmetry of the radius; the central case is `ρ_M=1` and `4M≤r_M≤12M+3`. Combine these to prove the two inequalities in `GeometryBounds` using one global pair of positive constants. Do not assume the central population is exactly `4M`; its residual `N−4M(M−1)` varies across the full permitted interval.

The `population≤15M` clause follows from `4j≤4M` on ordinary rings and `r_M≤12M+3≤15M` for `M≥1`. For each integer population `n`, an ordinary northern value `4j` appears at most once and has at most one reflected southern counterpart. The central ring can add one more occurrence, so the multiplicity is at most three. This fact is used in the longitude gcd double sum. Establish also `Σ_jρ_j≍M`: sum the inequalities `cMρ_j≤r_j≤CMρ_j` and use `Σr_j=N≍M²`. It is a consequence of the contract rather than a separate requested conjunct, but an exported theorem will prevent later duplication.

For `AngularGeometry`, write polar coordinate `φ=arccos z`. The band `polarBand N j` is `[arccos H_{j−1}, arccos H_j]` because `arccos` reverses height order. Its width is `arccos H_j−arccos H_{j−1}`. Express it as an integral of `1/sqrt(1−z²)` over a height interval of length `2r_j/N`. On ordinary bands, the radius throughout the band is comparable to `r_j/M`; for the two cap bands, evaluate endpoint behavior directly rather than invoking a positive lower radius at the pole. The result is a width between `c/M` and `C/M`, including the polar bands. Near a pole the height width is of order `M^{-2}`, yet the polar angular width remains order `M^{-1}`. This is why direct global Lipschitz estimates for `arccos` fail.

The second conjunct bounds `sin θ` on noncap bands by `r_j/M`. Check its current one-based exclusion: `j.val≠0` excludes the first ring, and `j.val+1≠2M−1` excludes the last. The central band is included and has `sin θ` bounded away from zero when `M≥16`. Derive the estimate from the endpoint heights, monotonicity on each hemisphere, and the population comparisons. At the equator, use central band symmetry rather than a formula that presumes a hemisphere. Explicitly prove `θ∈[0,π]` for valid bands.

The third conjunct handles ring offsets at least two. Ordered disjoint polar intervals imply their pointwise angular gap is at least the sum of intervening widths, hence at least a constant times `|j−k|/M`. The upper bound follows by summing the widths of all bands between the selected points, with at most two partial endpoint bands. Both directions are symmetric in `j,k`; avoid a proof that tacitly assumes `j<k`. Use `Int` absolute values for the discrete separation and real absolute values for the angle bound; cast lemmas should be kept separate from analytic estimates.

These bounds feed the appendix's angular-distance model `D²≍(φ−ψ)²+sinφ sinψ θ²`, comparable-block gap estimates, and smooth unequal-block estimates. They do not themselves establish the kernel's derivative bounds. In particular, they must be combined with special treatment when heights coincide and the angular kernel has a cusp, and with polar endpoint expansions where `sqrt(1−z²)` has singular derivatives.

Status: `GeometryBounds`, `AngularGeometry`, and `polarBand` are declared, not proved. Prove the all-size elementary geometry before the `M≥16` polar estimates. Any reused legacy bound should be checked against the new exact height `1−4j²/N` and central residual population.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Construction

open scoped BigOperators
namespace BEMOC.Definitive

/-- Uniform geometric estimates; constants never depend on N or phases. -/
def GeometryBounds : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
    (∀ j : RingIndex N,
      c * bandParameter N * radius N (j.val + 1) ≤ population N (j.val + 1) ∧
      (population N (j.val + 1) : ℝ) ≤
        C * bandParameter N * radius N (j.val + 1)) ∧
    (∀ j : RingIndex N, population N (j.val + 1) ≤ 15 * bandParameter N) ∧
    (∀ n : ℕ, (Finset.univ.filter
      (fun j : RingIndex N => population N (j.val + 1) = n)).card ≤ 3)

/-- Polar interval in increasing angular coordinates. -/
def polarBand (N j : ℕ) : Set ℝ :=
  Set.Icc (Real.arccos (boundary N (j - 1))) (Real.arccos (boundary N j))

/-- Polar geometry used for block estimates, after the explicit large-N cutoff. -/
def AngularGeometry : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 16 ≤ bandParameter N →
    (∀ j : RingIndex N,
      c / bandParameter N ≤ Real.arccos (boundary N (j.val + 1)) -
        Real.arccos (boundary N j.val) ∧
      Real.arccos (boundary N (j.val + 1)) - Real.arccos (boundary N j.val)
        ≤ C / bandParameter N) ∧
    (∀ j : RingIndex N, j.val ≠ 0 → j.val + 1 ≠ 2 * bandParameter N - 1 →
      ∀ θ ∈ polarBand N (j.val + 1),
        c * population N (j.val + 1) / bandParameter N ≤ Real.sin θ ∧
        Real.sin θ ≤ C * population N (j.val + 1) / bandParameter N) ∧
    (∀ j k : RingIndex N, 2 ≤ |(j.val : ℤ) - k.val| →
      ∀ θ ∈ polarBand N (j.val + 1), ∀ ψ ∈ polarBand N (k.val + 1),
        c * |(j.val : ℝ) - k.val| / bandParameter N ≤ |θ - ψ| ∧
        |θ - ψ| ≤ C * |(j.val : ℝ) - k.val| / bandParameter N)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
