# Construction proof guide

Source anchors: `definitive.tex` §2, especially `eq:rj` and lines 274–325. The construction is defined for every `N≥4`; the appendix's `N≥1024` assumption has no place in its basic lemmas. The occupied bands are numbered `1,...,2M−1` in the manuscript, while Lean uses `Fin (2*M−1)` and translates a label `j` to `j.val+1`. Every subtraction in a one-based formula should be accompanied by the range proof that prevents natural-number truncation from changing its meaning.

First prove arithmetic for `bandParameter N = Nat.sqrt (N/4)`. Natural division followed by integer square root still gives the intended floor: `M²≤N/4` is equivalent to `4M²≤N`, and the square-root upper bound gives `N<4(M+1)²`. For `N≥4`, obtain `M≥1`; for `N≥1024`, obtain `M≥16`. Convert these inequalities to `N≍M²` with explicit constants. The elementary edge case `4≤N≤15` has `M=1`, one occupied equatorial ring; it is part of the definition even though the analytic appendix excludes it.

Next unfold `population`. For `1≤j<M`, show `r_j=4j`; at `j=M`, show `r_M=N−4M(M−1)` using `Σ_{j=1}^{M−1}4j=2M(M−1)`. The subtraction is exact because `N≥4M²`. From the square bounds deduce `4M≤r_M≤12M+3≤15M`. For `M<j<2M`, the last branch gives `r_j=4(2M−j)=r_{2M−j}`. All occupied populations are strictly positive. Reindex the southern sum by reflection to prove `Σ_{j=1}^{2M−1}r_j=N`. The dependent `PointIndex` then has exactly `N` labels, using the standard cardinality-of-sigma identity. This cardinality is independent of phases.

`boundary N j` is `1−(2/N)Σ_{k=1}^j r_k` on the occupied range. Prove `H₀=1`, `H_{2M−1}=−1`, and `H_{j−1}−H_j=2r_j/N>0`. The northern closed formula in `BoundaryFormulas`, `H_j=1−4j(j+1)/N` for `j<M`, follows from the arithmetic sum. The central midpoint is zero because populations on the two sides agree and the equatorial band straddles zero. Reflection yields `H_{2M−1−j}=−H_j` with carefully chosen index range. Derive `h_j=(H_{j−1}+H_j)/2`, `h_j=1−4j²/N` for `1≤j<M`, and `h_{2M−j}=−h_j`. These are exact height midpoints, not Simpson nodes. Strict boundary descent gives `H_j<h_j<H_{j−1}`; thus all heights lie in `(-1,1)` and distinct rings have distinct heights. Also derive band height length `2r_j/N` and normalized spherical area `r_j/N` once the surface integration lemma is available.

The `point` definition accepts an arbitrary phase per ring and a vertex number modulo `r_j`. Its pole fallback exists only to make the function total for malformed inputs. Under `N≥4`, midpoint interior makes the fallback unreachable; prove a simplification lemma before geometric work. Then `point` lies on the sphere by construction and has third coordinate `h_j`. If two points are equal, their third coordinates force the same ring. On one ring the positive radius allows division by `ρ_j`, and equality of sine and cosine forces the angular difference to be an integer multiple of `2π`; the two vertex labels in `[0,r_j)` must agree. This proves `Function.Injective (point N φ)` uniformly in phases. A finite set `Finset.univ.image (point N φ)` now has cardinality `N` and its ordered pair sum reindexes to `diamondEnergy`.

The manuscript's named deterministic Diamond set fixes one vertex on the positive first-coordinate meridian in each occupied parallel. Define `zeroPhases N := fun _ => 0`, identify its `k=0` vertex with `(ρ_j,0,h_j)`, and name the corresponding finite set. Retain `Phases` in stronger intermediate results because the energy estimate is phase uniform. Avoid carrying over `legacy/` construction formulas: there the northern population was `4j−1` and point placement used a Simpson-style arrangement. Generic finite-group polygon facts may transfer, but their hypotheses need checking.

Status: the definitions and `ConstructionFacts`/`BoundaryFormulas` propositions are present; their proofs, the finite-set bridge, and the canonical phase corollary are outstanding. The total definitions have arbitrary behavior outside occupied indices, so state every manuscript correspondence with `4≤N` and a valid `RingIndex`.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Core

open scoped BigOperators
namespace BEMOC.Definitive

/-- Integer version of `floor(sqrt(N/4))`; division here is natural-number division. -/
def bandParameter (N : ℕ) : ℕ := Nat.sqrt (N / 4)
/-- Population of a one-based band. Only indices `1,...,2M-1` are occupied. -/
def population (N j : ℕ) : ℕ :=
  let M := bandParameter N
  if j < M then 4 * j
  else if j = M then N - 4 * M * (M - 1)
  else 4 * (2 * M - j)
/-- Boundary heights, defined from cumulative populations, including `H₀=1`. -/
noncomputable def boundary (N j : ℕ) : ℝ :=
  1 - 2 / (N : ℝ) * ∑ k ∈ Finset.Icc 1 j, (population N k : ℝ)
/-- Midpoint height, defined from the boundaries. -/
noncomputable def height (N j : ℕ) : ℝ := (boundary N (j - 1) + boundary N j) / 2
/-- Radius of an occupied parallel. -/
noncomputable def radius (N j : ℕ) : ℝ := Real.sqrt (1 - height N j ^ 2)
/-- Closed height band; endpoints have zero Lebesgue mass. -/
def band (N j : ℕ) : Set ℝ := Set.Icc (boundary N j) (boundary N (j - 1))
/-- Zero-based finite band labels; add one to recover the manuscript index. -/
abbrev RingIndex (N : ℕ) := Fin (2 * bandParameter N - 1)
/-- Every polygon vertex has its own label. -/
abbrev PointIndex (N : ℕ) := Σ j : RingIndex N, Fin (population N (j.val + 1))
/-- Independent azimuthal phases on the occupied parallels. -/
abbrev Phases (N : ℕ) := RingIndex N → ℝ

/-- Total definition. The north-pole fallback is unreachable after proving `ConstructionFacts`. -/
noncomputable def point (N : ℕ) (φ : Phases N) (i : PointIndex N) : Sphere :=
  let j := i.1.val + 1
  if h : height N j ∈ Set.Icc (-1 : ℝ) 1 then
    parallelPoint (height N j)
      (φ i.1 + 2 * Real.pi * (i.2.val : ℝ) / (population N j : ℝ)) h
  else parallelPoint 1 0 (by norm_num)

/-- The exact finite energy of the new Diamond points. -/
noncomputable def diamondEnergy (α : ℝ) (N : ℕ) (φ : Phases N) : ℝ :=
  energy (point N φ) α

/-- Construction obligations, including distinctness needed to speak about an N-element set. -/
def ConstructionFacts : Prop :=
  ∀ N : ℕ, 4 ≤ N →
    1 ≤ bandParameter N ∧
    4 * bandParameter N ^ 2 ≤ N ∧
    N < 4 * (bandParameter N + 1) ^ 2 ∧
    (∑ j : RingIndex N, population N (j.val + 1)) = N ∧
    (∀ j : RingIndex N, 0 < population N (j.val + 1) ∧
      height N (j.val + 1) ∈ Set.Ioo (-1 : ℝ) 1) ∧
    (∀ φ : Phases N, Function.Injective (point N φ))

/-- Closed formulas to prove from cumulative populations. -/
def BoundaryFormulas : Prop :=
  ∀ N : ℕ, 4 ≤ N →
    (∀ j : ℕ, j < bandParameter N →
      boundary N j = 1 - 4 * (j : ℝ) * (j + 1) / N) ∧
    (∀ j : ℕ, 1 ≤ j → j < bandParameter N →
      height N j = 1 - 4 * (j : ℝ) ^ 2 / N) ∧
    height N (bandParameter N) = 0 ∧
    (∀ j : ℕ, 1 ≤ j → j < 2 * bandParameter N →
      height N (2 * bandParameter N - j) = -height N j)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
