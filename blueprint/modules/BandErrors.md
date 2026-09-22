# BandErrors: signed latitude quadrature and exact decomposition

`BandErrors.lean` is the translation of `definitive.tex` lines 549–620 and Appendix 2's two displayed moment equations preceding `eq:one-variable-taylor`. The module defines `bandError N j f` as a difference of ordinary real integrals instead of constructing a signed measure `μ_j`. On the manuscript's one-based band `j`, this is exactly integration against `λ_j−ν_j`, where `λ_j=(N/2)1_{B_j}dt`, `ν_j=r_jδ_{h_j}`, and `B_j=[H_j,H_{j-1}]`. The nested `bandBlock` is ordered: the outer `bandError` acts on the first kernel variable `s`; the inner acts on `t`. Preserve that order when rewriting double integrals, and use `BlockSymmetry` rather than silently swapping variables. The underlying angular kernel is symmetric, but the nested integral equality must still be proved.

The first proof target is `BandMoments`. For each `j : RingIndex N`, put `q=j.val+1`; prove `1≤q<2M`, positive population, `H_{q-1}−H_q=2r_q/N`, and `h_q=(H_{q-1}+H_q)/2` from `ConstructionFacts` and boundary definitions. Then `bandError N q (fun _=>1)= (N/2)(H_{q-1}−H_q)−r_q=0`. For the identity function, use `∫_{H_q}^{H_{q-1}}t dt=(H_{q-1}²−H_q²)/2` and factor the difference of squares to obtain `(N/2)∫t=r_q h_q`. This uses the actual order of endpoints; a reversed interval introduces a sign error. Prove linearity of `bandError` and a lemma annihilating affine functions. An auxiliary TV-style bound should say `|bandError N q f|≤2r_q sup_{B_q}|f|` for bounded `f`, preferably with a pointwise bound form to avoid requiring an attained supremum. It follows by triangle inequality and `λ_j(B_j)=r_j`.

The second target is `LatitudeIdentity α`, corresponding to `eq:latitude-decomposition`. Begin from `latitudeError α N=I_αN²−ringEnergy α N`, where `ringEnergy` is the finite ordered sum of `r_jr_kF_α(h_j,h_k)`. Show the height disintegration of normalized surface measure, then `I_α N² = ∑_{j,k}(N/2)²∫_{B_j}∫_{B_k}F_α(s,t)dt ds`. Boundaries are shared, but they have zero Lebesgue measure; either use half-open bands for partition theorems or prove the closed-band overlap integrals vanish. Use the constant-potential identity `(N/2)∫_{-1}^1F_α(s,t)dt=N I_α` for every `s∈[-1,1]`, a consequence of rotational invariance and normalized sphere measure. Expand `bandBlock` into continuous-continuous, two mixed, and discrete-discrete terms. The mixed terms collapse by `∑_j bandError N q 1=0` and the constant potential; this yields the **negative** sign in `A=-∑ kernelBlock`. Check the sign algebra explicitly on a formal bilinear expression before introducing analytic details. The sums include `j=k`, and the global energy counts ordered pairs.

`BlockSymmetry α` follows from `latitudeKernel α s t=latitudeKernel α t s`, finite linearity, and Fubini for compact bounded kernels. One can also derive symmetry at the `bandBlock` level using elementary integrals and commutation, avoiding abstract signed measure machinery. The original proof's `0<α<2` is the intended range; the current `Prop` definitions accept arbitrary real `α`, so a proving theorem should take `0<α` explicitly, or the contracts may be narrowed later. At negative exponents the totalized real power at zero can obscure analytic integrability.

Legacy candidates: `legacy/BEMOCFormalization/LatitudeBands.lean` has `bandError_one`, `bandError_id`, `bandError_affine`; `LatitudeDecomposition.lean` has finite energy identities. Reuse their arithmetic and cancellation arguments only after checking new one-based labels, exact `N` normalization, and `r_M=N−4M(M−1)`.

An efficient intermediate statement is a bilinear identity for an arbitrary symmetric bounded kernel `K`: if a continuous height functional `L` has the same total mass as the atomic functional `R` and `L(K(s,·))` is constant in `s`, then `E(L)−E(R)=−E(L−R)`. Proving this once with finite band sums makes the sign and two mixed terms transparent. Specializing to `latitudeKernel` then leaves only the sphere disintegration and rotational invariance. It also makes the analytic integrability assumption visible at the specialization boundary, where `0<α` is available.

Dependencies: `Geometry`, `EnergyDecomposition`, `ConstructionFacts`, `BoundaryFormulas`, continuous-energy disintegration. Downstream users: `Taylor`, `ComparableBlocks`, `UnequalBlocks`, `Latitude`.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Geometry
import BEMOCFormalization.EnergyDecomposition

open scoped BigOperators
namespace BEMOC.Definitive

/-- Integration against λ_j−ν_j, implemented as a difference of ordinary integrals. -/
noncomputable def bandError (N j : ℕ) (f : ℝ → ℝ) : ℝ :=
  (N : ℝ) / 2 * (∫ t in boundary N j..boundary N (j - 1), f t) -
    (population N j : ℝ) * f (height N j)

/-- Ordered tensor of the two band error functionals: j acts on s, k on t. -/
noncomputable def bandBlock (N j k : ℕ) (G : ℝ × ℝ → ℝ) : ℝ :=
  bandError N j (fun s => bandError N k (fun t => G (s, t)))
/-- The actual latitude kernel block. -/
noncomputable def kernelBlock (α : ℝ) (N j k : ℕ) : ℝ :=
  bandBlock N j k (fun p => latitudeKernel α p.1 p.2)

/-- Exact two-moment cancellation, derived from the midpoint and mass formulas. -/
def BandMoments : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ j : RingIndex N,
    bandError N (j.val + 1) (fun _ => 1) = 0 ∧
    bandError N (j.val + 1) id = 0

/-- Corrected variable binding for eq:latitude-decomposition. -/
def LatitudeIdentity (α : ℝ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → latitudeError α N =
    -∑ j : RingIndex N, ∑ k : RingIndex N, kernelBlock α N (j.val + 1) (k.val + 1)

/-- Exchange symmetry used when orienting unequal-scale ordered pairs. -/
def BlockSymmetry (α : ℝ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ j k : RingIndex N,
    kernelBlock α N (j.val + 1) (k.val + 1) =
      kernelBlock α N (k.val + 1) (j.val + 1)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
