# BandErrors: signed latitude quadrature and exact decomposition

`BandErrors.lean` is the translation of `definitive.tex` lines 549–620 and Appendix 2's two displayed moment equations preceding `eq:one-variable-taylor`. The module defines `bandError N j f` as a difference of ordinary real integrals instead of constructing a signed measure `μ_j`. On the manuscript's one-based band `j`, this is exactly integration against `λ_j−ν_j`, where `λ_j=(N/2)1_{B_j}dt`, `ν_j=r_jδ_{h_j}`, and `B_j=[H_j,H_{j-1}]`. The nested `bandBlock` is ordered: the outer `bandError` acts on the first kernel variable `s`; the inner acts on `t`. Preserve that order when rewriting double integrals, and use `BlockSymmetry` rather than silently swapping variables. The underlying angular kernel is symmetric, but the nested integral equality must still be proved.

The first proof target is `BandMoments`, proved by `bandMoments`. For each `j : RingIndex N`, put `q=j.val+1`; prove `1≤q<2M`, positive population, `H_{q-1}−H_q=2r_q/N`, and `h_q=(H_{q-1}+H_q)/2` from `ConstructionFacts` and boundary definitions. Then `bandError N q (fun _=>1)= (N/2)(H_{q-1}−H_q)−r_q=0`. For the identity function, use `∫_{H_q}^{H_{q-1}}t dt=(H_{q-1}²−H_q²)/2` and factor the difference of squares to obtain `(N/2)∫t=r_q h_q`. This uses the actual order of endpoints; a reversed interval introduces a sign error. Prove linearity of `bandError` and a lemma annihilating affine functions. An auxiliary TV-style bound should say `|bandError N q f|≤2r_q sup_{B_q}|f|` for bounded `f`, preferably with a pointwise bound form to avoid requiring an attained supremum. It follows by triangle inequality and `λ_j(B_j)=r_j`.

The second target is `LatitudeIdentity α`, corresponding to `eq:latitude-decomposition`. Begin from `latitudeError α N=I_αN²−ringEnergy α N`, where `ringEnergy` is the finite ordered sum of `r_jr_kF_α(h_j,h_k)`. Show the height disintegration of normalized surface measure, then `I_α N² = ∑_{j,k}(N/2)²∫_{B_j}∫_{B_k}F_α(s,t)dt ds`. Boundaries are shared, but they have zero Lebesgue measure; either use half-open bands for partition theorems or prove the closed-band overlap integrals vanish. Use the constant-potential identity `(N/2)∫_{-1}^1F_α(s,t)dt=N I_α` for every `s∈[-1,1]`, a consequence of rotational invariance and normalized sphere measure. Expand `bandBlock` into continuous-continuous, two mixed, and discrete-discrete terms. The mixed terms collapse by `∑_j bandError N q 1=0` and the constant potential; this yields the **negative** sign in `A=-∑ kernelBlock`. Check the sign algebra explicitly on a formal bilinear expression before introducing analytic details. The sums include `j=k`, and the global energy counts ordered pairs.

`BlockSymmetry α` is proved for `0<α` by `blockSymmetry_of_pos`. The proof uses `latitudeKernel α s t=latitudeKernel α t s`, finite linearity, and Fubini for compact bounded kernels. One can also derive symmetry at the `bandBlock` level using elementary integrals and commutation, avoiding abstract signed measure machinery. The original proof's `0<α<2` is the intended range; the current `Prop` definitions accept arbitrary real `α`, so a proving theorem should take `0<α` explicitly, or the contracts may be narrowed later. At negative exponents the totalized real power at zero can obscure analytic integrability.

Legacy candidates: `legacy/BEMOCFormalization/LatitudeBands.lean` has `bandError_one`, `bandError_id`, `bandError_affine`; `LatitudeDecomposition.lean` has finite energy identities. Reuse their arithmetic and cancellation arguments only after checking new one-based labels, exact `N` normalization, and `r_M=N−4M(M−1)`.

An efficient intermediate statement is a bilinear identity for an arbitrary symmetric bounded kernel `K`: if a continuous height functional `L` has the same total mass as the atomic functional `R` and `L(K(s,·))` is constant in `s`, then `E(L)−E(R)=−E(L−R)`. Proving this once with finite band sums makes the sign and two mixed terms transparent. Specializing to `latitudeKernel` then leaves only the sphere disintegration and rotational invariance. It also makes the analytic integrability assumption visible at the specialization boundary, where `0<α` is available.

Dependencies: `Geometry`, `EnergyDecomposition`, `ConstructionFacts`, `BoundaryFormulas`, continuous-energy disintegration. Downstream users: `Taylor`, `ComparableBlocks`, `UnequalBlocks`, `Latitude`.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Geometry
import BEMOCFormalization.EnergyDecomposition

open scoped BigOperators
open MeasureTheory Set
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

/-- The signed band functional has zero mass and first moment on every occupied band. -/
theorem bandMoments : BandMoments := by
  intro N hN j
  let q := j.val + 1
  have hq : 1 ≤ q := by omega
  have hw := boundary_width hN hq
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmid : height N q =
      (boundary N (q - 1) + boundary N q) / 2 := rfl
  constructor
  · unfold bandError
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one]
    change (N : ℝ) / 2 * (boundary N (q - 1) - boundary N q) -
      (population N q : ℝ) = 0
    rw [hw]
    field_simp
    ring
  · unfold bandError
    change (N : ℝ) / 2 *
      (∫ t in boundary N q..boundary N (q - 1), t) -
      (population N q : ℝ) * height N q = 0
    rw [integral_id, hmid]
    have hmass : (population N q : ℝ) =
        (N : ℝ) / 2 * (boundary N (q - 1) - boundary N q) := by
      rw [hw]
      field_simp
      ring
    rw [hmass]
    ring

/-- Corrected variable binding for eq:latitude-decomposition. -/
def LatitudeIdentity (α : ℝ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → latitudeError α N =
    -∑ j : RingIndex N, ∑ k : RingIndex N, kernelBlock α N (j.val + 1) (k.val + 1)

/-- Exchange symmetry used when orienting unequal-scale ordered pairs. -/
def BlockSymmetry (α : ℝ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ j k : RingIndex N,
    kernelBlock α N (j.val + 1) (k.val + 1) =
      kernelBlock α N (k.val + 1) (j.val + 1)

/-- The angular average is continuous when its exponent is positive. -/
theorem continuous_latitudeKernel_bandErrors {α : ℝ} (hα : 0 < α) :
    Continuous (fun p : ℝ × ℝ => latitudeKernel α p.1 p.2) := by
  unfold latitudeKernel
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hp : 0 ≤ α / 2 := by linarith
  have hbase : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      2 - 2 * p.1.1 * p.1.2 -
        2 * Real.sqrt (1 - p.1.1 ^ 2) *
          Real.sqrt (1 - p.1.2 ^ 2) * Real.cos p.2) := by
    fun_prop
  exact (Real.continuous_rpow_const hp).comp hbase

/-- Swapping the two heights preserves the angular kernel. -/
theorem latitudeKernel_swap (α s t : ℝ) :
    latitudeKernel α s t = latitudeKernel α t s := by
  unfold latitudeKernel
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  ring

/-- Fubini for two oriented interval integrals on a compact rectangle. -/
theorem intervalIntegral_swap_of_continuous
    {K : ℝ → ℝ → ℝ} (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ s in a..b, ∫ t in c..d, K s t) =
      ∫ t in c..d, ∫ s in a..b, K s t := by
  have hrect : IntegrableOn (fun p : ℝ × ℝ => K p.1 p.2)
      (Icc a b ×ˢ Icc c d) :=
    hK.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hioc : IntegrableOn (fun p : ℝ × ℝ => K p.1 p.2)
      (Ioc a b ×ˢ Ioc c d) :=
    hrect.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hint : Integrable (Function.uncurry K)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact hioc
  simp_rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hcd]
  exact MeasureTheory.integral_integral_swap hint

/-- Integrating a jointly continuous kernel over a fixed interval preserves continuity. -/
theorem continuous_intervalIntegral_right
    {K : ℝ → ℝ → ℝ} (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (c d : ℝ) : Continuous (fun s => ∫ t in c..d, K s t) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hK

/-- The four terms obtained by expanding both signed band rules. -/
theorem bandBlock_eq_four_terms (N j k : ℕ) (K : ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2)) :
    bandBlock N j k (fun p => K p.1 p.2) =
      ((N : ℝ) / 2) ^ 2 *
          (∫ s in boundary N j..boundary N (j - 1),
            ∫ t in boundary N k..boundary N (k - 1), K s t) -
        (N : ℝ) / 2 * (population N k : ℝ) *
          (∫ s in boundary N j..boundary N (j - 1), K s (height N k)) -
        (population N j : ℝ) * (N : ℝ) / 2 *
          (∫ t in boundary N k..boundary N (k - 1), K (height N j) t) +
        (population N j : ℝ) * (population N k : ℝ) *
          K (height N j) (height N k) := by
  have hinner : IntervalIntegrable
      (fun s => ∫ t in boundary N k..boundary N (k - 1), K s t)
      volume (boundary N j) (boundary N (j - 1)) :=
    (continuous_intervalIntegral_right hK _ _).intervalIntegrable _ _
  have hatom : IntervalIntegrable
      (fun s => K s (height N k)) volume
      (boundary N j) (boundary N (j - 1)) :=
    (hK.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  unfold bandBlock bandError
  rw [intervalIntegral.integral_sub
    (hinner.const_mul ((N : ℝ) / 2))
    (hatom.const_mul (population N k : ℝ))]
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- Symmetry of two signed band rules on a continuous symmetric kernel. -/
theorem bandBlock_swap_of_continuous_of_symmetric
    (N j k : ℕ) (K : ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hsym : ∀ s t, K s t = K t s)
    (hj : boundary N j ≤ boundary N (j - 1))
    (hk : boundary N k ≤ boundary N (k - 1)) :
    bandBlock N j k (fun p => K p.1 p.2) =
      bandBlock N k j (fun p => K p.1 p.2) := by
  have hdouble :
      (∫ s in boundary N j..boundary N (j - 1),
        ∫ t in boundary N k..boundary N (k - 1), K s t) =
      (∫ s in boundary N k..boundary N (k - 1),
        ∫ t in boundary N j..boundary N (j - 1), K s t) := by
    calc
      _ = ∫ t in boundary N k..boundary N (k - 1),
            ∫ s in boundary N j..boundary N (j - 1), K s t :=
          intervalIntegral_swap_of_continuous hK hj hk
      _ = ∫ t in boundary N k..boundary N (k - 1),
            ∫ s in boundary N j..boundary N (j - 1), K t s := by
          simp_rw [hsym]
      _ = _ := rfl
  rw [bandBlock_eq_four_terms N j k K hK,
    bandBlock_eq_four_terms N k j K hK, hdouble]
  have hcrossj :
      (∫ s in boundary N j..boundary N (j - 1), K s (height N k)) =
      (∫ s in boundary N j..boundary N (j - 1), K (height N k) s) := by
    simp_rw [hsym]
  have hcrossk :
      (∫ s in boundary N k..boundary N (k - 1), K s (height N j)) =
      (∫ s in boundary N k..boundary N (k - 1), K (height N j) s) := by
    simp_rw [hsym]
  rw [hcrossj, hcrossk, hsym (height N j) (height N k)]
  ring

/-- The physical latitude-kernel blocks are symmetric for positive exponent. -/
theorem blockSymmetry_of_pos {α : ℝ} (hα : 0 < α) : BlockSymmetry α := by
  intro N hN j k
  have horder (i : RingIndex N) :
      boundary N (i.val + 1) ≤ boundary N (i.val + 1 - 1) := by
    have hpos : 0 < population N (i.val + 1) :=
      population_pos hN (by omega) (by have := i.isLt; omega)
    have hw := boundary_width hN (j := i.val + 1) (by omega)
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hpr : (0 : ℝ) ≤ population N (i.val + 1) := by exact_mod_cast hpos.le
    have hnonneg : 0 ≤ 2 * (population N (i.val + 1) : ℝ) / N :=
      div_nonneg (by positivity) hNr.le
    linarith
  exact bandBlock_swap_of_continuous_of_symmetric N (j.val + 1) (k.val + 1)
    (latitudeKernel α) (continuous_latitudeKernel_bandErrors hα)
    (latitudeKernel_swap α) (horder j) (horder k)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
