# `BEMOCFormalization.Trapezoid` proof guide

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.FourierDecay

open scoped BigOperators
namespace BEMOC.Definitive

/-- Phase-shifted equally spaced quadrature on a full angular period. -/
noncomputable def angularAverage (L : ℕ) (φ : ℝ) (f : ℝ → ℝ) : ℝ :=
  (L : ℝ)⁻¹ * ∑ k : Fin L, f (φ + 2 * Real.pi * (k.val : ℝ) / L)
/-- The angular distance-power model. -/
noncomputable def angularKernel (α A B θ : ℝ) : ℝ := (A - B * Real.cos θ) ^ (α / 2)

/-- Lemma trap, with B=0, A=B, L=1 and arbitrary phase all retained. -/
def TrapezoidBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ A B : ℝ, 0 ≤ B → B ≤ A →
    ∀ L : ℕ, 1 ≤ L → ∀ φ : ℝ,
      |angularAverage L φ (angularKernel α A B) -
        (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, angularKernel α A B θ| ≤
        C * B ^ (α / 2) * (L : ℝ) ^ (-1 - α)

/-- Finite group counting identity underlying the angular aliasing. -/
def GridMultiplicity : Prop :=
  ∀ q r : ℕ, 0 < q → 0 < r → ∀ f : ℝ → ℝ,
    Function.Periodic f (2 * Real.pi) → ∀ φ : ℝ,
      (∑ i : Fin q, ∑ j : Fin r,
        f (φ + 2 * Real.pi * ((i.val : ℝ) / q - (j.val : ℝ) / r))) =
      (Nat.gcd q r : ℝ) * ∑ k : Fin (Nat.lcm q r),
        f (φ + 2 * Real.pi * (k.val : ℝ) / Nat.lcm q r)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->

**Status and scope.** `Trapezoid.lean` imports `FourierDecay.lean` and defines `angularAverage`, `angularKernel`, `TrapezoidBound`, and `GridMultiplicity`. It currently supplies no proofs of the two proposition contracts. The analytic source is Lemma `trap` at `definitive.tex` lines 445–458 and Appendix 1 lines 1103–1285. The finite aliasing source is the proof of Lemma `BalphaN` around lines 465–485. The import of `FourierDecay.lean` makes its definitions available; it does not imply `TrapezoidBound`. The intended theorem is conditional on `FourierDecayBound (α/2)` and on `0<α<2`. The standalone `GridMultiplicity` is arithmetic and does not need any restriction on `α`.

**Check the exact analytic statement.** `angularKernel α A B θ=(A-B cos θ)^(α/2)` and `angularAverage` is a normalized sum over `Fin L` at points `φ+2πk/L`. The integral is normalized by `(2π)⁻¹`, matching the manuscript. The quantified assumptions are `0≤B≤A`, `1≤L`, with arbitrary real phase. This includes `B=0` (constant profile), `A=B` (unsmoothed cusp), and `L=1` (one sample). The positive constant `C` occurs outside all `A,B,L,φ`, so the uniformity is correctly captured. In all proof theorems write `hα0:0<α` and `hα2:α<2`, set `a=α/2`, and derive `0<a<1`. The definition itself quantifies no range because it is a proposition-valued target for each `α`; do not treat mere elaboration as evidence that it holds for all `α`.

**Scale reduction.** Split on `B=0`. Then `angularKernel` is constant `A^a`; the quadrature error is exactly zero, even if `A=0`. For `B>0`, define `δ=(A-B)/B≥0`. Prove `A-B cos θ=B(1+δ-cos θ)`, nonnegativity of both factors, and `angularKernel α A B θ=B^a * fourierProfile a δ θ` using `Real.mul_rpow`. Move `B^a` through finite sums and interval integrals. This reduction must retain `δ=0` when `A=B`. Be careful with real division and natural coercions: `L>0`, `B>0`, and `Real.pi>0` are necessary for `field_simp`, real-power laws, and normalizing the average.

**Fourier inversion and root-grid filtering.** From `FourierDecayBound a`, derive a bound on positive integer cosine coefficients by `C n^(-1-2a)`. Evenness of `fourierProfile` identifies negative complex Fourier coefficients with positive ones, while the zero mode is separately finite. Thus the full coefficient sequence on `ℤ` is absolutely summable because `2a=α>0` and `∑_{n≥1}n^(-1-α)<∞`. Use mathlib's continuous functions on `AddCircle` or a custom periodic-continuous wrapper to invoke the pointwise Fourier series theorem. Uniform summability alone is not an equality with the original function until Fourier uniqueness/inversion is applied. Averaging the series at `φ+2πk/L` kills all frequencies not divisible by `L`; the zero mode is the normalized integral. The error is the sum over nonzero multiples `mL` with phases of modulus one. The resulting bound is
`B^a C ∑_{m∈ℤ\{0}}|mL|^(-1-α) = B^a (2C∑_{m≥1}m^(-1-α)) L^(-1-α)`.
Choose this finite expression, or a larger positive number, as the `TrapezoidBound α` constant. Its value depends only on `α` and the `FourierDecayBound` witness. An arbitrary phase never changes the norm of a Fourier character.

Legacy `BEMOCFormalization/CuspTrapezoid.lean` contains `hasSum_fourierCoeff_filtered_by_shiftedRootGrid`, `hasSum_fourierCoeff_multiples_shiftedRootGridAverage`, and `exists_uniform_cusp_trapezoid_all`. Its `AddCircle 1` convention and complex-valued continuous profiles differ from the new real `2π` convention. Reuse the proof architecture, not the statement verbatim. The legacy `CircleFourier` module also has root-character orthogonality. These files are under `Rieszenergy/legacy/`, outside the current imported source graph; adapting them creates new proof work. The alternative of proving a real cosine-series version directly is acceptable if it handles arbitrary phase, which introduces sine factors after translation.

**Finite grid multiplicity.** `GridMultiplicity` says that an ordered pair of regular polygon grids with sizes `q,r>0` produces every residue on the `lcm(q,r)` grid exactly `gcd(q,r)` times. A robust proof works in finite additive groups. Let `L=lcm(q,r)` and map `ZMod q × ZMod r` to `ZMod L` by `(i,j)↦(L/q)i-(L/r)j`. Prove it is surjective because `gcd(L/q,L/r)=1`; its domain has `q*r` elements and its codomain `L`, so every fiber has `q*r/L=gcd(q,r)` elements. The real angle identity holds modulo `2π`; apply `Function.Periodic f (2π)` to replace any representative by `k/L`. `Fin` sums can be converted to `ZMod` sums. The legacy `Core.lean` contains `GridMultiplicity.sum_generalGridDifference_eq_gcd_mul_sum`, and legacy `CrossRingPair.lean` converts such finite-group sums to angular sums; they are concrete candidates to port. A direct combinatorial proof via `Finset.sum_bij` is another option. The contract is valid for arbitrary periodic `f`, even discontinuous, because it is only a finite identity. Its cases `q=r`, `q=1`, `r=1`, and coprime `q,r` should be checked explicitly while developing the proof.

**Output toward longitude.** Prove a named implication `FourierDecayBound (α/2) → TrapezoidBound α`, with the range hypotheses. Separately prove `GridMultiplicity`, or accept it as an explicit hypothesis in a conditional pair bound. Do not conflate the two: the trapezoid estimate controls one regular grid, whereas multiplicity identifies the two-grid pair sum with that grid. `Longitude.lean` needs both. A completed build of this module after adding theorems would establish the analytic quadrature step only if the Fourier decay hypothesis has also been discharged; a theorem taking that hypothesis remains conditional.
