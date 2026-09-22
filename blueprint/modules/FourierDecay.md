# `BEMOCFormalization.FourierDecay` proof guide

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Core

namespace BEMOC.Definitive

/-- The even real profile used in Appendix 1, including the cusp at δ=0. -/
noncomputable def fourierProfile (a δ θ : ℝ) : ℝ := (1 + δ - Real.cos θ) ^ a
/-- Real cosine coefficient; the sine coefficient vanishes by evenness. -/
noncomputable def cosineCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f θ * Real.cos (n * θ)

/-- Appendix 1 monotonicity, including δ=0 and all positive frequencies. -/
def FourierDomination (a : ℝ) : Prop :=
  ∀ δ : ℝ, 0 ≤ δ → ∀ n : ℕ, 1 ≤ n →
    cosineCoefficient (fourierProfile a 0) n ≤ cosineCoefficient (fourierProfile a δ) n ∧
    cosineCoefficient (fourierProfile a δ) n ≤ 0

/-- Gamma formula for the cusp profile; positive n avoids the zero mode. -/
def CuspCoefficientFormula (a : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    cosineCoefficient (fourierProfile a 0) n =
      -(2 : ℝ) ^ (-a) * Real.Gamma (2 * a + 1) * Real.sin (Real.pi * a) /
        Real.pi * (Real.Gamma (n - a) / Real.Gamma (n + a + 1))

/-- Uniform Fourier decay; the constant is outside all geometric parameters. -/
def FourierDecayBound (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 ≤ δ → ∀ n : ℕ, 1 ≤ n →
    |cosineCoefficient (fourierProfile a δ) n| ≤ C * (n : ℝ) ^ (-1 - 2 * a)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->

**Status.** This module currently compiles definitions of three propositions, `FourierDomination`, `CuspCoefficientFormula`, and `FourierDecayBound`. It does not prove any of them, and importing `Core` adds no Fourier theorem. All intended proofs require `0<a<1`, equivalently `0<α<2` when `a=α/2`. Those restrictions are intentionally not built into the proposition definitions, so every subsequent theorem must list them as hypotheses. The source is Appendix 1 of `definitive.tex`, particularly equations `monotone-fourier`, `fourier-domination`, and `f0-explicit` and the lines following them. This module is the analytic input for `Trapezoid.lean`; that dependency is an intended future proof implication, not a theorem supplied by the import graph.

**Normalization and preliminary lemmas.** `cosineCoefficient f n` is `(2π)⁻¹∫₀^{2π}f(θ)cos(nθ)dθ`. Appendix 1 uses `(2π)⁻¹∫ f(θ)e^{-inθ}dθ`. Before porting any complex Fourier result, prove that for the real even periodic function `fourierProfile a δ`, the imaginary sine integral is zero and its complex Fourier coefficient equals the real coercion of `cosineCoefficient`. The profile is continuous for `δ≥0` and `a>0`; at `δ=0` its base vanishes at integer multiples of `2π` but real power is still continuous. Prove `1+δ-cos θ≥δ≥0`. Show periodicity from cosine periodicity. These facts establish interval integrability and justify later change of variables. Keep the zero frequency outside every decay claim; its coefficient is generally positive and does not satisfy the stated sign inequality.

**Domination route.** For `δ>0`, set `g_δ(θ)=(1+δ-cos θ)^(a-1)`. The manuscript expands it as `(1+δ)^(a-1)∑_{k≥0}((1-a)_k/k!)(cos θ/(1+δ))^k`. The ratio is strictly below one uniformly in θ, and each coefficient is nonnegative when `0<a<1`. The coefficient of `cos^k θ` at nonnegative frequency `n` is `2^(-k) binomial(k,(k-n)/2)` when parity and size permit, zero otherwise. For `k=n` it is positive. Formalization needs a uniform convergence theorem to exchange the power series and integral, a finite exponential or trigonometric expansion of `cos^k`, and a positivity lemma for the resulting coefficient. Then differentiate `δ↦cosineCoefficient (fourierProfile a δ) n` locally at each `δ>0`. The derivative is `a` times the coefficient of `g_δ`; local domination uses a positive lower bound on `δ`, because exponent `a-1` is negative. This gives strict increase in `δ` for `n≥1`.

The endpoint step is separate. For `δ≥0`, prove `|(x+δ)^a-x^a|≤δ^a` for `x≥0`, `0<a<1`; apply it at `x=1-cos θ` to get uniform convergence to `f₀` as `δ↓0`. At infinity, subtract the constant `(1+δ)^a`, whose positive-frequency cosine coefficient is zero, and use the mean-value inequality `|(1+δ-cos θ)^a-(1+δ)^a|≤a δ^(a-1)` for `δ≥1`. The right side tends to zero. Strict increase, endpoint continuity, and this zero limit give precisely `f̂₀(n)≤f̂_δ(n)≤0`. The assertion at `δ=0` follows by equality. In Lean, do not apply a derivative theorem at `δ=0`; the cusp makes that step false as a general smoothness argument.

**Cusp coefficient.** The exact formula in `CuspCoefficientFormula` agrees with Appendix 1. Transform `1-cos θ=2 sin²(θ/2)` and use symmetry/substitution to reduce to `(2^a/π)∫₀^π sin(u)^(2a)cos(2nu)du`. The beta integral quoted from Gradshteyn–Ryzhik, together with Gamma reflection, gives the expression. A more reusable Lean route is the recurrence already established in legacy `BEMOCFormalization/CuspFourier.lean`: `sinePowerCosMoment_succ`, then the base coefficient, then Gamma recurrence. This avoids directly formalizing a table integral, although the base integral and normalization still need proof. The legacy `CircleFourier.chordFourierCoeffGamma_succ` and `exists_unitChordCosCoeff_power_bound` are candidate techniques. They belong to `Rieszenergy/legacy/`, use another namespace and chord normalization, and cannot be cited as an active import without adapting them. Check the `2^(-a)` factor carefully after changing from the unit-period chord `(2 sin πx)^α` to `(1-cos θ)^a`.

**Decay from formula and domination.** The explicit coefficient is negative because `Γ(2a+1)`, `sin(πa)`, `Γ(n-a)`, and `Γ(n+a+1)` are positive for `0<a<1`, `n≥1`. Prove a separate Gamma ratio bound `Γ(n-a)/Γ(n+a+1)≤C_a n^(-1-2a)` with `C_a>0`. This can use Stirling/asymptotic lemmas or the recurrence and a convergent product bound. The ratio estimate is essential; the formula alone does not give uniform decay. Domination then turns the negative interval `[f̂₀(n),0]` into `|f̂_δ(n)|≤|f̂₀(n)|` for all `δ≥0`. Absorb the positive Gamma prefactor into `C_a`. State the result as `FourierDecayBound a`, with `C` chosen before quantifying `δ` and `n`.

**Alternative direct route.** One may prove `FourierDecayBound` without `CuspCoefficientFormula` or `FourierDomination` by a uniform localized Fourier estimate. Subtract `f_δ(0)`; near the cusp use `|f_δ(θ)-f_δ(0)|≤C|θ|^(2a)`. Away from the cusp, integrate by parts three times with derivative estimates `|∂^k f_δ(θ)|≤C_k|θ|^(2a-k)` for `k=1,2,3`, uniformly in `δ≥0`. A cutoff at scale `1/n` gives `n^(-1-2a)`. Periodic endpoint cancellation is indispensable. This alternative proves the decay target but would leave the manuscript's separate Gamma and domination contracts unproved; document the distinction.

**Edge cases and verification.** Retain `δ=0`, `n=1`, arbitrary large `δ`, and `a` close to either endpoint of `(0,1)`. The constant may depend on `a`, but on no smoothing or frequency parameter. Inspect the sign of the negative coefficient and the exact factor of two. Build the module after each analytic lemma; run the repository shortcut audit after proofs. The module remains a contract until a Lean theorem inhabits each desired proposition.
