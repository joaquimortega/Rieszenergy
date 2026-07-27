# Blueprint for the BEMOC upper bound

## Objective

Prove unconditionally in Lean, for every fixed `0 < α < 2`, the upper
estimate for the concrete BEMOC configuration:

```text
0 ≤ continuousEnergy α * N² - bemocFiniteEnergy α N
  ≤ Cα N^(1 - α/2).
```

The exact construction, energy normalization, three-term decomposition,
conditional-negative-definiteness argument, within-ring estimate, and
cross-ring angular-aliasing estimate are complete. L1--L3, the complete
latitude summation infrastructure, and the unequal-scale same-hemisphere
block estimate are also checked. The remaining analytic input is the
comparable/exceptional latitude block closure, followed by the short
component assembly.

Wagner's lower bound and the paper's matching lower asymptotic are explicitly
outside the scope of this project.

The optional Fourier proof of the circle Euler--Maclaurin theorem is not on
the critical path: the direct endpoint proof is already unconditional.

## Current endpoint

The final proof should instantiate the existing upper-bound structures and
theorems:

- `BemocComponentBounds α` in `BEMOCFormalization/Core.lean`;
- `bemoc_upper_bound_of_component_bounds`.

The within-ring and cross-ring fields are already supplied by:

```lean
exists_bemocWithinRingDeficit_concrete_bound
exists_bemocCrossRingDeficit_concrete_bound
```

The remaining component target is:

```lean
theorem exists_bemocLatitudeDeficit_concrete_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |bemocLatitudeDeficit α N| ≤
        C * (N : ℝ) ^ (1 - α / 2)
```

## Current dependency order

```text
Completed within-ring bound ───────────────────────────────┐
Completed cross-ring bound ────────────────────────────────┼─ Component bounds
Latitude analytic closure ── Latitude concrete bound ──────┘
                                                             │
                                                             └─ Upper theorem
```

Only the latitude analytic closure is on the critical path.

---

## Track C: cross-ring angular aliasing — complete

This track is retained below as a record of the proved architecture.
`exists_bemocCrossRingDeficit_concrete_bound` is compiled and imported by the
canonical root.

### C1. Common angular kernel

Create `BEMOCFormalization/CrossRingKernel.lean`.

Define the paper's scalar kernel before specializing it to occupied rings:

```lean
noncomputable def angularPairKernel
    (α s t θ : ℝ) : ℝ :=
  (2 - 2 * s * t
    - 2 * Real.sqrt (1 - s^2) * Real.sqrt (1 - t^2) *
      Real.cos θ) ^ (α / 2)

noncomputable def latitudeKernel
    (α s t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ θ in 0..2 * Real.pi, angularPairKernel α s t θ
```

Required bridge lemmas:

- agreement with `dist (parallelPoint ...) (...) ^ α`;
- periodicity in `θ`;
- agreement of `latitudeKernel` with `continuousRingPairEnergy` after
  multiplying by populations;
- representation as `(A - B cos θ)^(α/2)`;
- `A ≥ B ≥ 0` on `s,t ∈ [-1,1]`;
- `B = 2ρ_sρ_t`.

Acceptance gate: all later cross-ring and latitude files use this one kernel,
so no duplicate normalization can arise.

### C2. Exact cusp Fourier coefficients

Create `BEMOCFormalization/CuspFourier.lean`.

Prove the exact positive-frequency coefficient for

```text
f₀(θ) = (1 - cos θ)^(α/2)
      = 2^(-α/2) (2 |sin(θ/2)|)^α.
```

Reuse the existing infrastructure in `CircleFourier.lean`:

- intrinsic chord profile;
- interval representation of Fourier coefficients;
- beta-integral substitution;
- Gamma products and quotient asymptotics;
- root-grid character orthogonality.

First discharge the existing interface:

```lean
theorem hasExactPositiveChordCoefficients
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    CircleFourier.HasExactPositiveChordCoefficients α hα0
```

Then expose a real-valued form matching equation (4.3):

```lean
theorem abs_fourierCoeff_cusp_eq
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (n : ℕ) (hn : 1 ≤ n) :
    |cuspFourierCoeff α n| =
      cuspConstant α *
        Real.Gamma (n - α / 2) /
          Real.Gamma (n + α / 2 + 1)
```

Also prove a uniform power bound:

```lean
|cuspFourierCoeff α n| ≤ Cα * (n : ℝ)^(-1-α).
```

Important cases:

- positivity of every Gamma argument;
- integer/real coercions in `n ± α/2`;
- symmetry of positive and negative frequencies;
- the normalization difference between period `1` and period `2π`.

### C3. Smoothing domination

Create `BEMOCFormalization/CuspSmoothing.lean`.

For

```text
fδ(θ) = (δ + 1 - cos θ)^(α/2),  δ ≥ 0,
```

formalize equation (4.2):

```lean
|fourierCoeff (fδ) n| ≤ |fourierCoeff (f₀) n|,  n ≠ 0.
```

Recommended implementation:

1. formalize the Bernstein representation of `x^a`, `0 < a < 1`;
2. define only the modified-Bessel coefficient needed here, using its
   nonnegative integral representation;
3. justify Fubini/Tonelli using a nonnegative majorant;
4. obtain domination from `exp (-(1+δ)t) ≤ exp (-t)`.

Do not build a general Bessel library unless mathlib forces it. A local
coefficient integral with positivity, measurability, and the Fourier identity
is sufficient.

Fallback route: prove coefficient domination directly from the positive
Laplace mixture of the functions `exp (t cos θ)`.

### C4. Uniform cusp trapezoidal estimate

Create `BEMOCFormalization/CuspTrapezoid.lean`.

Target equation (4.1):

```lean
theorem uniform_cusp_trapezoid
    {α A B : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hB : 0 ≤ B) (hAB : B ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ), 1 ≤ L → ∀ φ : ℝ,
      |(1 / L) * ∑ k ∈ Finset.range L,
          (A - B * Real.cos (φ + 2 * Real.pi * k / L)) ^ (α / 2)
        - (1 / (2 * Real.pi)) *
          ∫ θ in 0..2 * Real.pi,
            (A - B * Real.cos θ) ^ (α / 2)|
      ≤ C * B ^ (α / 2) * (L : ℝ) ^ (-1 - α)
```

Proof stages:

- separate `B = 0`;
- scale by `B^(α/2)` and set `δ = (A-B)/B`;
- use C3 and the C2 coefficient bound;
- establish absolute summability of the Fourier series;
- instantiate the existing root-grid alias theorem;
- handle an arbitrary phase by multiplying coefficients by unit complex
  phases;
- sum `∑_{m≠0}|mL|^(-1-α)`.

Acceptance gate: the constant may depend on `α`, but not on `A`, `B`, `L`,
or `φ`.

### C5. Pairwise ring error

Create `BEMOCFormalization/CrossRingPair.lean`.

Prove that two positive populations `q,r`, with `d = gcd q r` and
`L = lcm q r`, have cross-error

```text
≤ Cα (ρqρr)^(α/2) d^(1+α)/(qr)^α.
```

Reuse:

- `sum_generalGridDifference_eq_gcd_mul_sum`;
- `Nat.gcd_mul_lcm`;
- exact polygon phase and distance formulas;
- C4 with the phase difference of the two polygons.

Keep ordered-pair normalization explicit. The total cross term sums both
`(p,q)` and `(q,p)`.

### C6. BEMOC arithmetic summation

Create `BEMOCFormalization/CrossRingEstimate.lean`.

Required supporting lemmas:

- partition noncentral BEMOC populations into finitely many affine families;
- each population value occurs with uniformly bounded multiplicity;
- `w_p ≍ Mρ_p` in both directions, with explicit constants;
- all ordinary populations are `≤ C M`;
- only `O(1)` exceptional central/equatorial populations occur;
- divisor/Jordan identity
  `n^(1+α) = ∑_{a∣n} J_{1+α}(a)`;
- estimates for
  `∑_{u≤X} u^(-α/2)` and `∑_{a≤X} a^(α-1)`;
- the exceptional-population estimate using `gcd(q*,r) ≤ r`.

Public endpoint:

```lean
theorem exists_bemocCrossRingDeficit_concrete_bound ...
```

Do not optimize constants.

---

## Track L: latitude quadrature — active

### Current latitude checkpoint

Verified Git checkpoint: `7c21167` (`Formalize unequal latitude derivative
series bounds`).

Completed and imported:

- L1 exact band algebra and affine exactness;
- L2 exact identity
  `bemocLatitudeDeficit = -∑ j, ∑ k, bandPairError`;
- L3 mixed Taylor/Peano transfer;
- literal comparable, unequal, central, polar, reflected, and antipodal
  rectangle geometry;
- exact pair classification and all pointwise-to-row and L7 summation
  arithmetic;
- actual even-power identity (5.6);
- the complete finite `(2,2)` derivative chain for each even mode;
- the explicit left-small mode estimate
  `4194304 (m+1)^4 A^(α/2-4) (15/16)^(m-2)` for `m ≥ 2`;
- normal summability of the coefficient-weighted fourth-derivative series;
- nonresonant local reduced-cusp decompositions for both `0 < α < 1` and
  `1 < α < 2`.

Remaining, in dependency order:

1. identify the normally convergent differentiated series with
   `variableReducedLatitudeKernelDsstt`;
2. export the resulting unconditional unequal-block bound;
3. complete the resonant `α = 1` local cusp decomposition;
4. retain the graded gap powers in the sharp comparable-block estimate;
5. instantiate the central and antipodal cases and export the unconditional
   latitude endpoint.

### Design choice: use error functionals

The manuscript writes signed measures `μ_j = ν_j - λ_j`. In Lean, a direct
signed-measure implementation would add substantial infrastructure unrelated
to the estimates. Prefer an explicit band error functional:

```lean
noncomputable def bandError
    (N j : ℕ) (f : ℝ → ℝ) : ℝ :=
  atomicBandValue N j f -
    (N / 2 : ℝ) * ∫ t in bandLower N j..bandUpper N j, f t

noncomputable def bandPairError
    (N j k : ℕ) (K : ℝ → ℝ → ℝ) : ℝ :=
  bandError N j (fun s => bandError N k (fun t => K s t))
```

This represents `μ_j(f)` and `(μ_j ⊗ μ_k)(K)` while keeping all operations
finite sums and interval integrals.

### L1. Exact band algebra — complete

Create `BEMOCFormalization/LatitudeBands.lean`.

Formalize:

- band endpoints `H_{j-1}, H_j`, midpoint `h_j`, and width `2r_j/N`;
- atomic Simpson-like weights including remainders;
- shared endpoint atoms combining to the existing boundary populations;
- decomposition of the full height quadrature error as a sum of `bandError`;
- exactness on constants and linear functions:

```lean
bandError N j (fun _ => 1) = 0
bandError N j (fun t => t) = 0
```

- a variation bound of the form
  `|bandError N j f| ≤ C d_j sup_{B_j}|f|`;
- scale bounds
  `bandWidth ≍ d_j/M²` and `bandRadius ≍ d_j/M`;
- polar, central, northern, and reflected index classifications.

Use explicit constants and enlarge them freely to absorb the finitely many
exceptional bands.

### L2. Latitude-energy decomposition — complete

Create `BEMOCFormalization/LatitudeDecomposition.lean`.

Prove the exact analogue of equation (5.1):

```lean
bemocLatitudeDeficit α N =
  -∑ j, ∑ k, bandPairError N j k (latitudeKernel α)
```

Required bridges:

- height pushforward of `Nσ` is `(N/2) 1_[−1,1] dt`;
- height pushforward of the continuous BEMOC ring measure is the atomic
  latitude rule;
- constant spherical potential kills the two linear terms;
- finite band integrals concatenate to `[-1,1]`.

### L3. Generic two-moment Peano lemmas — complete

Create `BEMOCFormalization/TwoMomentPeano.lean`.

Prove reusable one- and two-variable estimates. Suggested interface:

```lean
theorem bandError_le_of_secondDerivative ...

theorem bandPairError_le_of_mixedFourthDerivative ...
```

The hypotheses should expose:

- exactness on `1` and `t`;
- support intervals and their widths;
- total-variation-style coefficient bounds;
- a bound for `∂s²∂t² K`.

Also add a rescaled fixed-rectangle version for kernels such as
`|u-v|^(1+α)` and `(u-v)^2 log |u-v|`, where a pointwise fourth derivative
is not integrable on the diagonal.

This module should not mention BEMOC.

### L4. Local kernel expansion — nonresonant cases complete

Create `BEMOCFormalization/LatitudeKernelLocal.lean`.

Formalize the comparable-scale analysis:

1. exact half-angle representation with
   `p = sin α₀ sin β₀` and
   `q = sin²((α₀-β₀)/2)`;
2. the angular average `p^(α/2) hα(q/p)`;
3. decomposition near zero into an analytic part and a branch part:

```text
Hα(x) + x^((1+α)/2) Bα(x),        α ≠ 1,
H₁(x) + x log(1/x) B₁(x),         α = 1;
```

4. bounded derivatives of the analytic factors through order four;
5. the off-diagonal estimate

```text
|∂s²∂t² Fα(s,t)|
  ≤ Cα R^(-2-α) |s-t|^(α-3).
```

Current split:

- the nonresonant ranges `0 < α < 1` and `1 < α < 2` are proved;
- formalize `α = 1` in a separate namespace/file section;
- combine only at the exported theorem.

The remaining risk is the logarithmic resonant normalization, not the
nonresonant branch decomposition.

### L5. Comparable and polar blocks — analytic closure pending

Create `BEMOCFormalization/LatitudeComparableBlocks.lean`.

Targets:

```lean
|bandPairError N j k (latitudeKernel α)|
  ≤ Cα * d_j / M^α * (1 + |j-k|)^(α-3)
```

for comparable scales.

Handle separately:

- neighboring/overlapping blocks by rescaling to a fixed square;
- separated comparable blocks using L3 and L4;
- finitely many north-polar blocks;
- reflected south-polar blocks;
- near-equatorial opposite-hemisphere blocks.

### L6. Unequal-scale and antipodal blocks — unequal same-hemisphere case complete

Create `BEMOCFormalization/LatitudeSeparatedBlocks.lean`.

Formalize the even-power expansion in equation (5.6):

- `A ≍ R_k²`;
- `B/A ≤ 1-δ`;
- angular integration removes odd cosine powers;
- rewrite `B^(2m)` polynomially as
  `4^m(1-s²)^m(1-t²)^m`;
- prove normal convergence after up to two derivatives in each variable;
- identify the sum of the fourth derivatives with the fourth derivative of
  the actual kernel;
- obtain `|∂s²∂t²F| ≤ C R_k^(α-8)`.

The normal-summability statement, four termwise derivative passes, closed
rectangle identification with the actual mixed derivative, explicit
pointwise constant, conversion to
`Cα M^(8-α) d_k^(α-8)`, and the mixed-Peano block transfer are complete.

Export:

```lean
|bandPairError N j k (latitudeKernel α)|
  ≤ Cα * d_j^3 / (M^α * d_k^(5-α))
```

for unequal scales in one hemisphere is now exported unconditionally as
`leftSmallSame_block_bound_series`. The remaining exceptional cases are:

- smooth opposite-hemisphere bound `C d_j³d_k³/M⁸`;
- central-band versus small-scale bound;
- symmetry lemmas exchanging `j` and `k`.

### L7. Summation — infrastructure complete

Create `BEMOCFormalization/LatitudeEstimate.lean`.

Partition all ordered band pairs into the cases exported by L5 and L6. Prove:

- summability of `(1+|ℓ|)^(α-3)` because `α-3 < -1`;
- `∑_{d≤M} d = O(M²)`;
- `∑_{d≤M} d^(α-1) = O(M^α)`;
- the opposite-hemisphere smooth sum is `O(1)`;
- finite exceptional cases are absorbed.

The row partition, convolution estimates, unequal-orientation sums, finite
fallback, and implication from uniform large-row bounds are compiled. The
public endpoint becomes unconditional as soon as L5--L6 supply the remaining
pointwise bounds:

```lean
theorem exists_bemocLatitudeDeficit_concrete_bound ...
```

---

## Track A: final assembly

Create `BEMOCFormalization/MainTheorem.lean`.

### A1. Construct component bounds

Combine the three independently obtained constants using a maximum or sum:

```lean
theorem bemocComponentBounds
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    BemocComponentBounds α
```

Fields:

- `latitude`: L7;
- `withinRing`: `exists_bemocWithinRingDeficit_concrete_bound`;
- `crossRing`: C6.

Choose `N₀` as the maximum of the three thresholds and one constant larger
than all three constants.

### A2. Concrete upper theorem

Export:

```lean
theorem bemocEnergyDeficit_upper
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      0 ≤ bemocEnergyDeficit α N ∧
      bemocEnergyDeficit α N ≤
        C * (N : ℝ) ^ (1 - α / 2)
```

This should be a short application of
`bemoc_upper_bound_of_component_bounds`.

Finally expose a theorem stated directly with `bemocFiniteEnergy` and import
it from `BEMOCFormalization.lean`.

---

## Optional track F: complete the alternative circle Fourier proof

This track is not required for the paper because the endpoint
Euler--Maclaurin theorem is already proved directly.

After C2, most of it should become inexpensive:

- instantiate `HasExactPositiveChordCoefficients`;
- prove summability of all chord Fourier coefficients;
- reindex divisible modes;
- construct `HasNormalizedCircleAlias`;
- invoke `circleEulerMaclaurin_of_fourier_alias`;
- verify that the result agrees with the existing direct theorem.

Keep this out of the critical path unless C2 naturally discharges it.

---

## Recommended execution schedule

Use one proof track at a time to minimize duplicated exploration and quota
cost. Each phase ends with a direct module build, canonical build, placeholder
audit, Git commit, and push.

| Phase | Remaining work | Gate |
|---|---|---|
| 1 | Unequal-series termwise `(2,2)` differentiation | Complete |
| 2 | Unequal pointwise-to-block closure | Complete |
| 3 | Resonant `α = 1` cusp decomposition | All exponent ranges covered |
| 4 | Sharp comparable estimate | Unconditional comparable-block estimate |
| 5 | Central/antipodal instantiation and L7 endpoint | `exists_bemocLatitudeDeficit_concrete_bound` |
| 6 | Component assembly and final audit | Unconditional BEMOC upper theorem |

## Rough effort and risk

These are token estimates for the remaining upper-bound work, not guarantees.

| Package | Estimated tokens | Main risk |
|---|---:|---|
| Unequal-series differentiation and block closure | 30k--55k | termwise multivariable differentiation interface |
| Resonant `α = 1` cusp decomposition | 20k--35k | logarithmic normalization |
| Sharp comparable-block estimate | 45k--80k | preserving graded gap powers |
| Central/antipodal closure | 15k--30k | matching existing geometric interfaces |
| Final assembly, repairs, audit, and documentation | 20k--30k | interface alignment |

Estimated total: `130k--230k` tokens, with approximately `175k` the current
best estimate. The comparable-block proof is the largest uncertainty.

## Invariants to preserve

- Ordered-pair energy normalization throughout.
- Constants may depend on `α`, never on `N`, phases, ring indices, or band
  indices.
- All phase estimates must be uniform.
- Keep `0 < α < 2` explicit; split `α = 1` only where the logarithmic
  resonance requires it.
- Treat polar, central, equatorial, and antipodal exceptions explicitly.
- Do not replace the actual BEMOC ring family by an asymptotic surrogate.
- Do not introduce `sorry`, `admit`, or custom axioms.
- Deep unfinished results remain named propositions or structures until
  proved.
- Preserve the existing corrected within-ring coefficient with distinct
  population factors `8/3` and `4/3`.

## Verification checklist for every work package

1. Compile the new module directly.
2. Import it only through its immediate downstream module.
3. Add focused exact-value or specialization checks when available.
4. Run:

   ```bash
   lake build
   ```

5. Audit project sources:

   ```bash
   rg -n '\b(sorry|admit|axiom|opaque)\b' \
     BEMOCFormalization.lean BEMOCFormalization --glob '*.lean'
   ```

6. Update `LEAN_FORMALIZATION.md` after each material compiled checkpoint,
   keeping all remaining hypotheses explicit.
7. Commit and push each clean checkpoint to the private GitHub repository.

## Definition of completion

The upper-bound project is complete when all of the following hold:

- `bemocComponentBounds hα0 hα2` is unconditional;
- the concrete upper theorem has no analytic hypotheses;
- its conclusion is stated for the literal `bemocFiniteEnergy`;
- `BEMOCFormalization.lean` imports the final theorem;
- `lake build` succeeds;
- the project-owned Lean sources contain no `sorry`, `admit`, or custom
  axioms;
- `LEAN_FORMALIZATION.md` has no remaining upper-bound obligations, apart
  from explicitly optional alternative proofs.
