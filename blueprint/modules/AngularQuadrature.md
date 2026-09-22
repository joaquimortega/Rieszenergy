# `BEMOCFormalization.AngularQuadrature`

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Trapezoid
import BEMOCFormalization.Angular.CuspTrapezoid

/-! Transfer of the proved generic cusp trapezoid estimate to the
`BEMOC.Definitive` proposition contract. -/

namespace BEMOC.Definitive

/-- Appendix 1 quadrature bound, uniformly in the phase and both kernel
coefficients, including the unsmoothed cusp `A = B`. -/
theorem trapezoid_bound {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    TrapezoidBound α := by
  obtain ⟨C, hC, hbound⟩ :=
    Angular.CuspTrapezoid.exists_uniform_cusp_trapezoid_all hα0 hα2
  refine ⟨C, hC, ?_⟩
  intro A B hB hAB L hL φ
  have h := hbound hB hAB L hL φ
  simpa only [angularAverage, angularKernel, Finset.sum_range,
    one_div] using h

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->

**Checked status.** `AngularQuadrature.lean` builds and proves `BEMOC.Definitive.trapezoid_bound {α} (hα0:0<α) (hα2:α<2) : TrapezoidBound α`. This discharges the exact proposition contract in `Trapezoid.lean` without modifying that scaffold file. It imports the current `Trapezoid` definitions and the independent proved analytic chain ending in `Angular.CuspTrapezoid`. This is a theorem, not a field assumed in a structure and not a restatement under a new name. The mathematical source is Lemma `trap` and Appendix 1 in `definitive.tex`.

**Interface transfer.** The analytic theorem `Angular.CuspTrapezoid.exists_uniform_cusp_trapezoid_all` produces a positive constant `C` and quantifies over `A,B,L,φ` in the same order as `TrapezoidBound`. Both have the same kernel `(A-B cos θ)^(α/2)`, normalized angular integral `(2π)⁻¹∫₀^{2π}`, and rate `B^(α/2)L^(-1-α)`. The only syntactic difference is the grid: the analytic theorem sums over `Finset.range L`, while `angularAverage` sums over `Fin L`. Mathlib's `Finset.sum_range` converts these exactly. `one_div` identifies `1/L` with `L⁻¹`. Unfolding `angularAverage` and `angularKernel` therefore closes the proof with no additional estimate or altered constant.

**Parameters and endpoints.** The theorem requires `0<α<2`, so `a=α/2` lies in `(0,1)`. It retains `0≤B≤A`, including `B=0` and `A=B`. The analytic input already handles `B=0` as a constant-function branch and `A=B` as the unsmoothed cusp `δ=0`. The proof transfers `L=1` directly because the input quantifies `1≤L`. It also preserves an arbitrary real phase; no phase is fixed by choosing a meridian. The witness `C` is obtained before `A,B,L,φ` and therefore depends only on `α`. In particular, this theorem can be applied to every ring pair with the same constant once the geometric coefficients have been identified.

**Relationship to other contracts.** This proof does not inhabit `FourierDecayBound`, `FourierDomination`, or `CuspCoefficientFormula` as they are currently formulated in `FourierDecay.lean`; the imported generic chain proves the needed circle coefficient decay with a different normalization and takes a Schoenberg-mixture route instead of Appendix 1's exact Gamma coefficient evaluation. The distinction matters for status reporting. The trapezoid estimate itself is fully proved. It also does not prove `GridMultiplicity`: that finite gcd/lcm identity is logically separate and needed to apply a single-grid quadrature bound to two regular polygons. `Longitude.lean` can use `trapezoid_bound hα0 hα2` as a checked input to its ring-pair bound, together with a future proof of `GridMultiplicity`, geometry, and energy identification.

**Validation and maintenance.** `lake build BEMOCFormalization.AngularQuadrature` checks the complete analytic import chain. The helper files contain no `sorry`, `admit`, custom `axiom`, or `opaque` declarations. The ported proofs are substantial, especially Fourier inversion and the smoothing integral interchange; changing the normalization or replacing `Finset.range` with `Fin L` upstream should be followed by a rebuild of this endpoint theorem. The file is intentionally small so the relation between the new scaffold statement and the proved legacy analytic theorem remains auditable.
