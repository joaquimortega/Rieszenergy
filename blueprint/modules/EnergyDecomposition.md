# EnergyDecomposition proof guide

Source anchors: `definitive.tex` `eq:energianu`, `eq:Falpha`, and `eq:decomp` (around lines 386–411), the conditional negative definiteness paragraph (around 414–421), the longitude expansion (around 466–515), and the latitude height-measure decomposition (around 560–620). This module defines the three energies and their algebraic difference. It should be the meeting point of construction, normalized surface energy, angular quadrature, and latitude band errors, while leaving the hard analytic estimates in their own modules.

For valid `N`, let `U_h` be the pushforward of normalized angular Lebesgue measure under `θ↦parallelPoint h θ`. Show `U_h` is a probability measure on the latitude circle and that its height pushforward is `δ_h`. The weighted ring measure is `ν=Σ_{j∈RingIndex N}r_j U_{h_j}`. From Construction, `Σr_j=N`, so `ν` has mass `N`. Then expand its energy by bilinearity of the finite sum and apply the Core kernel-average identity: `E_α[ν]=Σ_{j,k}r_jr_kF_α(h_j,h_k)=ringEnergy α N`. The source's `F_α` uses a single angular difference; proving that two independent uniform angles reduce to this average requires angular translation invariance. Check that self-ring terms `j=k` are included. The uniform ring measure has a nonzero self-interaction integral, whereas the finite polygon includes zero diagonal pair terms; their difference belongs to longitude error.

Let `ξ=Σ_{i∈PointIndex N}δ_{point N φ i}`. Its energy is the finite ordered double sum `diamondEnergy α N φ`. The phase enters only through `ξ`, not through `ν` or `ringEnergy`. Once Construction proves injectivity, `ξ` is also the atomic measure of an `N`-element finite set. The exact deficit is `I_αN²−E[ξ]`, `latitudeError=I_αN²−E[ν]`, and `longitudeError=E[ν]−E[ξ]`. The implemented `deficit_eq_latitude_add_longitude` follows by ring algebra; it has no analytic assumptions and is already proved. Record explicitly that `longitudeError` can have either sign. The manuscript estimates its absolute value; no nonnegativity lemma for this term is needed.

`DiamondNonnegative α` should be derived from `EnergyNonnegative α` after identifying the label count with `N`. Its proof can reindex `PointIndex N` to `Fin N`, or use a generalized finite-index version of the nonnegativity theorem to avoid an explicit equivalence. If the former is chosen, show `Fintype.card (PointIndex N)=N` and use the energy invariance under label equivalence. Injectivity is unnecessary for the numerical inequality but necessary for calling the image an `N`-set. Keep `0<α<2` in the theorem that inhabits `DiamondNonnegative`; the bare proposition's definition does not carry those hypotheses.

The latitude identity is the next bridge. Define the continuous height measure `λ=(N/2)1_[−1,1]dt`, the atomic height measure `ν_z=Σ_jr_jδ_{h_j}`, and for each band `B_j=[H_j,H_{j−1}]` its pieces `λ_j`, `ν_j`, and signed error `μ_j=λ_j−ν_j`. The implemented `bandError N j f` in `BandErrors.lean` is exactly `∫f dμ_j` expressed as an ordinary integral minus midpoint evaluation. Prove `λ=Σ_jλ_j` despite closed bands: adjacent endpoints overlap, but Lebesgue measure of each endpoint is zero. Prove `ν_z=Σ_jν_j` trivially. Use `SurfaceIntegration` and the ring height pushforward to obtain `E[Nσ]=∬F dλ dλ` and `E[ν]=∬F dν_z dν_z`. By constant potential, `∫F(s,t)dλ(t)=NI_α` for every `s∈[-1,1]`; since `λ` and `ν_z` both have mass `N`, the two mixed terms equal `N²I_α`. Expand the signed difference `μ=λ−ν_z`: `E[μ]=E[λ]+E[ν_z]−2E[λ,ν_z]=E[ν]−I_αN²=−latitudeError`. Finally distribute the finite band sum to obtain `latitudeError=−Σ_{j,k}kernelBlock α N j k`.

The manuscript's displayed `eq:latitude-decomposition` accidentally writes `dμ_k(s)dμ_j(t)` while the outer variable `s` belongs to `B_j` and inner variable `t` belongs to `B_k`. The Lean `bandBlock` correctly applies band `j` to `s` and band `k` to `t`; preserve that binding throughout integration and derivative lemmas. For each band, exact mass `λ_j(B_j)=r_j` and first moment `∫t dλ_j=r_jh_j` give `bandError 1=bandError id=0`. These two cancellations power the Taylor block estimates, but the singular diagonal and polar blocks need more analysis than a global fourth-derivative estimate.

Status: the four numeric definitions and algebraic decomposition are implemented. The geometric interpretations of `ringEnergy` and `diamondEnergy`, `DiamondNonnegative`, and the latitude identity remain proof obligations. `BandErrors.lean` holds the last identity's target rather than this file, so later imports must close that dependency before claiming the full deficit theorem.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Construction
import BEMOCFormalization.ContinuousEnergy

open scoped BigOperators
namespace BEMOC.Definitive

/-- Energy of the weighted union of uniform parallels. -/
noncomputable def ringEnergy (α : ℝ) (N : ℕ) : ℝ :=
  ∑ j : RingIndex N, ∑ k : RingIndex N,
    (population N (j.val + 1) : ℝ) * population N (k.val + 1) *
      latitudeKernel α (height N (j.val + 1)) (height N (k.val + 1))
/-- Latitude error A. -/
noncomputable def latitudeError (α : ℝ) (N : ℕ) : ℝ :=
  continuousEnergy α * (N : ℝ) ^ 2 - ringEnergy α N
/-- Angular discretization error B; phases are retained. -/
noncomputable def longitudeError (α : ℝ) (N : ℕ) (φ : Phases N) : ℝ :=
  ringEnergy α N - diamondEnergy α N φ
/-- The actual energy deficit appearing in Theorem 1. -/
noncomputable def deficit (α : ℝ) (N : ℕ) (φ : Phases N) : ℝ :=
  continuousEnergy α * (N : ℝ) ^ 2 - diamondEnergy α N φ

/-- The two-term decomposition is algebraic and already proved. -/
theorem deficit_eq_latitude_add_longitude (α : ℝ) (N : ℕ) (φ : Phases N) :
    deficit α N φ = latitudeError α N + longitudeError α N φ := by
  unfold deficit latitudeError longitudeError
  ring

/-- Required geometric identification, including the finite-label cardinality. -/
def DiamondNonnegative (α : ℝ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N, 0 ≤ deficit α N φ

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
