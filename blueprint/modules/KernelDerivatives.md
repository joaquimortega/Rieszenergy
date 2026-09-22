# KernelDerivatives: polar derivatives and the separated analytic branch

`KernelDerivatives.lean` corresponds to Appendix 2's `eq:F-polar-average`, `eq:distance-comparison`, Lemma `derivative-bounds`, and Lemma `separated-derivative`. It is the analytic hinge for all smooth block cases. `polarKernel α θ φ ψ` is `(D²)^(α/2)` with `D²=2−2(cosφ cosψ+sinφ sinψ cosθ)`. The source writes `D^α`; prove equality using `D≥0` and `D²` as a Euclidean squared distance before translating estimates. The current definition is total on real inputs, but real powers at nonpositive bases are not a substitute for Euclidean geometry. Derivatives are asserted only when `D²>0`, which provides an open neighborhood on which ordinary smooth real-power calculus applies.

For `PolarDerivativeBound α`, define sphere points `x(φ,θ)=(sinφ cosθ,sinφ sinθ,cosφ)` and `y(ψ)=(sinψ,0,cosψ)`. Their difference `z` has norm at most two and all polar partial derivatives of orders up to four uniformly bounded. On `z≠0`, the `q`th derivative of `|z|^α` has norm at most `C_{α,q}|z|^(α−q)`. Apply the multivariate chain rule, observe that each term has `1≤q≤m+n`, and use `D≤2` to absorb the gap from `q` to `m+n`. Include the `m=n=0` case directly. In Lean, a vector-norm derivative formulation may be easier than repeated scalar expansion; package the finite list of orders `m+n≤4` with one maximum constant. Verify the order of the nested `iteratedDeriv` in the contract: it differentiates in `ψ` inside and `φ` outside. Smoothness away from zero gives commutation if needed.

For the height derivative estimate, substitute `s=cosφ`, `t=cosψ` only when `−1<s,t<1`. The chain rule gives `∂_s=−(sinφ)⁻¹∂_φ` and `∂²_s=(sinφ)⁻²∂²_φ−cosφ(sinφ)⁻³∂_φ`, likewise for `t`. Expansion yields four terms with denominators `(sinφ sinψ)^2`, `sin²φ sin³ψ`, `sin³φ sin²ψ`, and `(sinφ sinψ)^3`, multiplied by `D^(α−4)`, `D^(α−3)`, `D^(α−3)`, and `D^(α−2)`. Do not invoke this formula at either pole; that is precisely why the separated branch exists. The distance comparison `D²≈(φ−ψ)²+sinφ sinψ θ²` is valid for polar angles `φ,ψ∈[0,π]` and `θ∈[0,π]` by the cosine identity; use it in `ComparableBlocks`.

`SeparatedDerivativeBound α` formalizes the binomial-series proof at `U=2−2st>0`, `V=2√(1−s²)√(1−t²)`, with `V≤(1−ε)U`. Put `A=1−s²`, `B=1−t²`. On the physical square, `A,B≥0`, `A,B≤U≤4`, and `V²=4AB`. The angular average equals `U^(α/2)∑_{m≥0}a_m(4AB/U²)^m`, where odd cosine powers vanish. Prove local uniform convergence for four derivatives when `|4AB/U²|<(1−ε')²<1`; after differentiation, the `m≥2` terms are bounded by `C_α(1+m)^4(1−ε')^(2m−4)U^(α/2−4)`. Treat `m=0,1` separately so that no negative powers of `A` or `B` appear at a pole. This series in the polynomial variables `A,B,U` defines a smooth extension outside `[-1,1]²`, unlike the original square-root expression. It provides the pointwise witness `G,W` and the derivative bound in the contract.

**Gluing obligation:** The current contract returns a potentially different `G,W` at each `(s,t)`. `MixedTaylorBound` needs one `G` on each closed separated band rectangle. Prove local extensions agree where their neighborhoods meet the physical square, hence their derivatives agree on interior overlaps; use continuity for boundary points. Compactness and a finite subcover then give a uniform rectangle-level `C⁴` extension, or replace the local witness with the same canonical binomial-series formula on a common open set around the rectangle. This is a real proof obligation, not a definitional rewrite.

Legacy candidates: `legacy/BEMOCFormalization/LatitudeUnequalSeries.lean` for the normalized series and polynomial-geometric summability; `LatitudeCoefficientDerivatives.lean`, `LatitudePowerJetBounds.lean`, and `LatitudeAngularJetBounds.lean` for derivative patterns. Translate exponents and normalization carefully: the present theorem is for `0<α<2`, with `β=α/2`, and `latitudeKernel` integrates over `[0,2π]` before the `[0,π]` symmetry reduction.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Taylor

namespace BEMOC.Definitive

/-- Distance power in polar coordinates, used only away from zero distance for differentiation. -/
noncomputable def polarKernel (α θ φ ψ : ℝ) : ℝ :=
  (2 - 2 * (Real.cos φ * Real.cos ψ +
    Real.sin φ * Real.sin ψ * Real.cos θ)) ^ (α / 2)

/-- The angular derivative estimate from Lemma derivative-bounds. -/
def PolarDerivativeBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, m + n ≤ 4 → ∀ θ φ ψ : ℝ,
    0 < 2 - 2 * (Real.cos φ * Real.cos ψ +
      Real.sin φ * Real.sin ψ * Real.cos θ) →
    |iteratedDeriv m (fun u => iteratedDeriv n (fun v => polarKernel α θ u v) ψ) φ| ≤
      C * (2 - 2 * (Real.cos φ * Real.cos ψ +
        Real.sin φ * Real.sin ψ * Real.cos θ)) ^ ((α - m - n) / 2)

/-- Smooth extension of the separated averaged kernel, including polar boundaries. -/
def SeparatedDerivativeBound (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧
    ∀ s ∈ Set.Icc (-1 : ℝ) 1, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      0 < 2 - 2 * s * t →
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
        (1 - ε) * (2 - 2 * s * t) →
      ∃ G : ℝ × ℝ → ℝ, ∃ W : Set (ℝ × ℝ), IsOpen W ∧ (s, t) ∈ W ∧
        ContDiffOn ℝ 4 G W ∧
        (∀ p ∈ W, p.1 ∈ Set.Icc (-1 : ℝ) 1 → p.2 ∈ Set.Icc (-1 : ℝ) 1 →
          G p = latitudeKernel α p.1 p.2) ∧
        |mixedFourth G s t| ≤ C * (2 - 2 * s * t) ^ (α / 2 - 4)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
