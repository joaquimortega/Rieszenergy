# `BEMOCFormalization.Longitude` proof guide

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Trapezoid
import BEMOCFormalization.Geometry
import BEMOCFormalization.EnergyDecomposition

open scoped BigOperators
namespace BEMOC.Definitive

/-- The arithmetic double sum after reducing angular quadrature to gcd/lcm. -/
noncomputable def gcdSum (α : ℝ) (T : ℕ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 T, ∑ v ∈ Finset.Icc 1 T,
    (Nat.gcd u v : ℝ) ^ (1 + α) / ((u : ℝ) * v) ^ (α / 2)

/-- The two zeta sums are finite because α>0. -/
def GcdSumBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, gcdSum α T ≤ C * (T : ℝ) ^ 2

/-- Phase-uniform longitude estimate for the actual Diamond energy. -/
def LongitudeBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N,
    |longitudeError α N φ| ≤ C * scale α N

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->

**Status, source, and dependencies.** `Longitude.lean` currently compiles `gcdSum`, `GcdSumBound`, and `LongitudeBound` as definitions of targets. It proves none of them. Its source is `definitive.tex`, Lemma `BalphaN` and its proof at lines 433–548, together with `eq:geometry` and `eq:decomp`. It imports `Trapezoid`, `Geometry`, and `EnergyDecomposition`; those in turn make the construction, point energy, latitude kernel, and analytic contract statements available. An import is only a source dependency. The desired mathematical implication is `TrapezoidBound α`, `GridMultiplicity`, `GeometryBounds`, `ConstructionFacts`, `GcdSumBound α` and `0<α<2` imply `LongitudeBound α`. Until each input is proved, any theorem taking it as a hypothesis is conditional. The current `LongitudeBound α` proposition itself has no range assumption; proof theorems must explicitly take `0<α` and `α<2`.

**Connect the actual energy to angular sums.** Work with `N≥4`, `M=bandParameter N`, and `RingIndex N=Fin (2M-1)`. From `ConstructionFacts`, derive `M≥1`, all occupied populations positive, and every midpoint height strictly inside `(-1,1)`. Therefore `point` always selects its intended `parallelPoint` branch, never the north-pole fallback. Expand `diamondEnergy` as an ordered double sum over `PointIndex N`; use `Sigma`/`Fin` sum rearrangement to obtain a sum over ring pairs and then vertex pairs. The diagonal `j=k` is present, including `i=i'`; with `α>0`, the same-point distance power is zero. Do not silently switch to unordered energy or delete the diagonal before applying the finite grid identity. Expand `ringEnergy` from `EnergyDecomposition`: its ring-pair term is `r_j r_k latitudeKernel α h_j h_k`. This yields exactly the manuscript's `B_{α,N}` as `longitudeError α N φ`.

**Distance and pair kernel.** Set `ρ_j=radius N (j+1)`, `A=2-2 h_j h_k`, and `B=2ρ_jρ_k`. Prove `0≤B≤A` by identifying `A-B` as the squared distance between points on the two parallels at a common longitude, or by Cauchy–Schwarz for `(h_j,ρ_j)` and `(h_k,ρ_k)`. Prove the squared Euclidean distance of the two actual vertices is `A-B cos(θ_j-θ_k)`, with `θ_j=φ j+2π i/r_j` and `θ_k=φ k+2π i'/r_k`. This requires the sphere point definitions, trigonometric difference formula, and `dist_eq_norm`. Then use `Real.sqrt_sq_eq_abs`/positive-base real-power identities to relate `dist ^ α` to `(A-B cos(...))^(α/2)`. The same kernel appears definitionally in `latitudeKernel` after unfolding. Establish periodicity of `angularKernel` in its angular argument; with `φ=φ j-φ k`, `GridMultiplicity` converts the vertex double sum into `d * ∑_{u<L} angularKernel α A B (φ+2πu/L)`, where `d=gcd(r_j,r_k)` and `L=lcm(r_j,r_k)`.

**Pair error and critical exponents.** Since `r_j*r_k=d*L`, the ring-pair discrepancy is `d*L` times the difference between the angular integral and `angularAverage L φ`. Apply `TrapezoidBound α`, including its `L=1` and `A=B` cases, to get `C B^(α/2) d L^(-α)`. Use `Nat.gcd_mul_lcm`, positivity of `d,L,r_j,r_k`, and real-power laws to rewrite this as `C B^(α/2) d^(1+α)/(r_j*r_k)^α`. The power `1+α` on the gcd is essential. The manuscript's `eq:geometry` gives `r_j≥c Mρ_j`, or `ρ_j≤r_j/(cM)`; the lower comparison field in `GeometryBounds` has precisely this direction. Because `B=2ρ_jρ_k`, absorb `2^(α/2)c^(-α)` into the constant and obtain the usable weight
`|pairError(j,k)| ≤ C' M^(-α) gcd(r_j,r_k)^(1+α)/(r_j*r_k)^(α/2)`.
All factors raised to negative exponents are positive, including `M`, populations, gcd, and lcm. The constant cannot depend on `N`, rings, or phases. Use the triangle inequality for a finite ordered double sum to pass to `|longitudeError|`.

**Population reduction.** The `GeometryBounds` contract supplies `r_j≤15M` and, for every natural `n`, a fiber cardinality at most three. For any nonnegative weight `W(u,v)`, regroup by the two population values. Each ordered fiber product has at most nine members, giving `∑_{j,k}W(r_j,r_k)≤9∑_{1≤u,v≤15M}W(u,v)`. The actual new construction permits multiplicity two, but proving the contract's weaker three is sufficient. Do not apply the factor only once. The `gcdSum α (15M)` definition is exactly the remaining double sum. The `GcdSumBound α` witness yields `≤C_g(15M)²`, hence the longitude error is `≤C''M^(2-α)`.

**Arithmetic proof of `GcdSumBound`.** For `T=0`, the `Icc 1 0` sums are empty and the inequality follows from positivity of `C`; handle it before using positive integer denominators. For `T≥1`, take `u,v∈Icc 1 T`, let `d=gcd u v`, `a=u/d`, `b=v/d`. Prove `d,a,b≥1`, `u=d a`, `v=d b`, and `gcd a b=1`. Real-power algebra gives `d^(1+α)/(uv)^(α/2)=d/(ab)^(α/2)`. Regroup by coprime `a,b` and `d≤T/max(a,b)`, then discard coprimality for an upper bound. The elementary finite sum `∑_{d≤x}d≤x²` and `max(a,b)²≥ab` bound the expression by `T²(∑_{n≥1}n^(-1-α/2))²`. The series is finite for `α>0`, via `Real.summable_nat_rpow` or an elementary integral comparison. The manuscript writes the same constant as `ζ(1+α/2)²`; no explicit zeta identification is required for `GcdSumBound`.

An alternative reusable route is legacy `BEMOCFormalization/CrossRingEstimate.lean`, whose `gcd_arithmetic_double_sum_le` proves the same growth for a related weight using divisor majorization, plus legacy `CrossRingPair.lean` for `gcd_mul_lcm_rpow_identity`. These files are outside the current import graph. Their configuration/population definitions differ from the new manuscript construction, so port only the number-theoretic lemmas after checking casts and algebraic equivalence of `gcdArithmeticWeight` with `gcdSum`'s summand. The factorization approach above is closer to lines 506–533 and may be simpler to audit.

**Final scale and checks.** `ConstructionFacts` gives `4M²≤N<4(M+1)²`; for `M≥1`, `4(M+1)²≤16M²`. Since `2-α>0`, derive `M^(2-α)≤C N^(1-α/2)` with a universal numerical multiplier (indeed the lower bound already gives a direct comparison). Combine all constants into one positive witness for `LongitudeBound α`. Check edge cases `N=4`, `M=1`, identical rings, identical vertices, opposite or arbitrary phases, coincident heights, `B=0` in the abstract trapezoid lemma, and `T=0` in `GcdSumBound`. A successful Lean build after proving only the conditional implication still does not verify `LongitudeBound`; that requires concrete proofs of every named input contract.
