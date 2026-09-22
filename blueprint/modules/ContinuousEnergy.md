# ContinuousEnergy proof guide

Source anchors: `definitive.tex` `eq:integralaintervalo` (the height-angle integration formula), `eq:Falpha`, Theorem `thm:main` for the value of `I_α`, and the conditional negative definiteness paragraph immediately after `eq:decomp` (around lines 414–421). The latitude section uses rotational invariance again to cancel the mixed term (around lines 606–612). These are separate steps. Conditional negative type alone cannot identify the coefficient of `N²` in the deficit.

Prove `SurfaceIntegration` by relating the chosen `sigma` in Core to normalized geometric area. First establish `IsProbabilityMeasure sigma`. Then derive the parametrization formula for every continuous `f : Ambient → ℝ` on the sphere: integrate height `t` uniformly over `[-1,1]` with density `1/2`, and angle over `[0,2π]` with density `1/(2π)`. The current contract quantifies over ambient continuous functions; this is enough for the distance-power potential because `y↦dist x y ^ α` extends continuously to `Ambient` when `α>0`. It may be convenient to prove a stronger bounded Borel formulation first, then specialize. At the poles the angular parametrization is redundant but the poles have zero area. Ensure the normalization of `volume.toSphere` is checked against mathlib's conventions; do not replace the probability proof by a simplification that presumes the total sphere area.

For `ConstantPotential α`, assume at least `0<α` and usually carry `α<2` to match the theorem, though the integral calculation holds in a broader range. Rotations preserve `sigma` and act transitively on the sphere. Thus the integral `∫ dist x y ^ α dσ(y)` is independent of `x`. Evaluate it at the north pole. A point of height `t` is at chordal distance squared `2−2t` from the north pole, so its power distance is `(2−2t)^(α/2)`. The angular integral is constant and equals itself. Integrate `1/2∫_{−1}^{1}(2−2t)^(α/2)dt`: after substitution, the result is `2^(α+1)/(α+2)`. Verify all real-power domain conditions, the positive denominator, endpoint integrability, and conversion between `(sqrt u)^α` and `u^(α/2)`. This proves the formula rather than merely using the scalar definition from Core. Integrating the constant potential once more gives the double continuous energy. A second consequence is the exact mixed energy `E(ν,Nσ)=N² I_α` whenever the positive measure `ν` has mass `N`.

`MeasureNegativeType α` is stated for two finite positive measures of equal total mass. Its left side is the quadratic energy of their signed difference, written without introducing a signed-measure API. To prove it, invoke an appropriate conditional negative definiteness theorem for the Euclidean distance power, valid for `0<α<2`, and extend from finite sums to finite measures. A viable route uses a positive integral representation of `r^α` in terms of Gaussian kernels or Fourier transforms, then each zero-mass signed measure has nonpositive energy. If a mathlib theorem handles finite signed measures or negative-type kernels directly, use it; verify the direction of the inequality and exact exponent range. Since the sphere is compact and `dist≤2`, all distance-power kernels are bounded for `α>0`, so Tonelli/Fubini and finite-energy statements are straightforward after establishing measurability. Keep the distinction between `μ` and `ν` order in the mixed integral; symmetry of the kernel makes the two orientations equal.

For `EnergyNonnegative α`, take an arbitrary labelled finite configuration `X : Fin n → Sphere` and its atomic measure `ξ=Σ_iδ_{X_i}`. Its mass is `n`, even if some labels coincide. Apply `MeasureNegativeType` to `ξ` and `n • sigma`. Expand: `E[ξ] + n²E[σ]−2nE[ξ,σ]≤0`. The constant-potential identity gives `E[ξ,σ]=n I_α`; hence `E[ξ]≤n²I_α`. Reindex the atomic double integral to `energy X α`. This produces `EnergyNonnegative` without requiring injectivity. If the public claim is phrased as an `N`-element set, Construction supplies injectivity and card `N` separately. The diagonal terms vanish for `α>0`; their inclusion in `energy` is nevertheless the exact manuscript normalization.

An alternate proof could apply a finite negative-type inequality directly to the points plus a weak approximation of `σ`, but the measure-level route is also needed for `A=I_αN²−E[ν]≥0`, so prove the general version first. For `ν=Σ_jr_j U_{h_j}`, show mass `N`; then the same expansion with `Nσ` yields `A=−E[ν−Nσ]≥0`. This latter bridge belongs in EnergyDecomposition or BandErrors but depends on the facts proved here.

Status: the file currently declares four `Prop` contracts and proves none of them. The contracts are correctly separated: surface integration, potential, finite nonnegativity, and measure negative type. In a final theorem proof, `0<α<2` must enter before the negative-type step; merely having `ConstantPotential α` does not establish nonnegativity at arbitrary exponents.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Core

open MeasureTheory
namespace BEMOC.Definitive

/-- Geometric normalized surface area has the height-angle integration formula. -/
def SurfaceIntegration : Prop :=
  IsProbabilityMeasure sigma ∧
  ∀ f : Ambient → ℝ, Continuous f →
    (∫ x : Sphere, f x ∂sigma) =
      (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1,
        (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f (parallelVector t θ)

/-- Rotational invariance and the beta integral give a constant potential. -/
def ConstantPotential (α : ℝ) : Prop :=
  ∀ x : Sphere, (∫ y : Sphere, dist x y ^ α ∂sigma) = continuousEnergy α

/-- Finite-configuration nonnegativity, for the actual geometric surface constant. -/
def EnergyNonnegative (α : ℝ) : Prop :=
  ∀ n : ℕ, ∀ X : Fin n → Sphere,
    0 ≤ continuousEnergy α * (n : ℝ) ^ 2 - energy X α

/-- Measure-level negative type, stated using differences of positive finite measures. -/
def MeasureNegativeType (α : ℝ) : Prop :=
  ∀ μ ν : Measure Sphere, IsFiniteMeasure μ → IsFiniteMeasure ν →
    μ Set.univ = ν Set.univ →
    (∫ x, ∫ y, dist x y ^ α ∂μ ∂μ) +
      (∫ x, ∫ y, dist x y ^ α ∂ν ∂ν) -
        2 * (∫ x, ∫ y, dist x y ^ α ∂ν ∂μ) ≤ 0

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
