# Completed architecture of the BEMOC upper bound

## Status

The Lean formalization of the BEMOC upper energy bound is complete for the
full range

```text
0 < α < 2.
```

This includes the logarithmically resonant exponent `α = 1`.  The public
endpoint has no analytic premise left to the caller:

```lean
theorem BEMOC.bemoc_deficit_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      0 ≤ continuousEnergy α * (N : ℝ) ^ 2 -
          bemocFiniteEnergy α N ∧
        continuousEnergy α * (N : ℝ) ^ 2 -
          bemocFiniteEnergy α N ≤
            C * (N : ℝ) ^ (1 - α / 2)
```

The proof-completion checkpoint is Git commit `1287c26`, dated
28 July 2026.

Wagner's configuration-uniform lower bound and the matching lower asymptotic
in the paper are outside this formalization's scope.  Interfaces for deriving
the full asymptotic from such a lower bound remain in the development, but
they are not assumptions of `bemoc_deficit_bound`.

## Public theorem ladder

The final proof is exposed in four unconditional layers:

```lean
hasVeryLargeComparableLatitudeBlockBound
exists_bemocLatitudeDeficit_concrete_bound
exists_bemocComponentBounds
bemoc_deficit_bound
```

Their roles are:

1. `hasVeryLargeComparableLatitudeBlockBound` packages every large-scale
   comparable latitude case.
2. `exists_bemocLatitudeDeficit_concrete_bound` combines comparable,
   unequal-scale, and finite-depth estimates with the row arithmetic.
3. `exists_bemocComponentBounds` combines latitude, within-ring, and
   cross-ring estimates at the common threshold `N ≥ 36`.
4. `bemoc_deficit_bound` adds conditional negative definiteness to obtain
   nonnegativity and unfolds the literal finite BEMOC energy.

The main dependency flow is:

```text
Concrete BEMOC geometry
          │
          ├── Within-ring endpoint ────────────────────────┐
          ├── Cross-ring endpoint ─────────────────────────┤
          └── Latitude band identity                       │
                    │                                      │
                    ├── Unequal-scale bounds               │
                    ├── Comparable bounds                  │
                    │      ├── polar                       │
                    │      ├── neighboring                 │
                    │      ├── central                     │
                    │      ├── opposite                    │
                    │      └── resonant α = 1              │
                    └── Row and scale summation ────────────┤
                                                           │
                                   BemocComponentBounds α ──┘
                                             │
                              Conditional negative definiteness
                                             │
                                  BEMOC.bemoc_deficit_bound
```

## Canonical modules

| Layer | Principal modules | Checked export |
|---|---|---|
| Root | `BEMOCFormalization.lean` | Public project entry point |
| Final assembly | `MainTheorem.lean` | `bemoc_deficit_bound` |
| Unconditional latitude assembly | `LatitudeUnconditionalComparableClosure.lean` | `exists_bemocLatitudeDeficit_concrete_bound` |
| Latitude pointwise assembly | `LatitudeFinalAssembly.lean`, `LatitudeComparablePointwiseAssembly.lean` | Complete comparable and unequal interfaces |
| Resonant closure | `LatitudeResonantEndpointClosure.lean`, `LatitudeResonantOscillationClosure.lean`, `LatitudeCentralResonantPointwiseClosure.lean` | Neighboring and central `α = 1` bounds |
| Nonresonant comparable closure | `LatitudeGenericSharpComparableClosure.lean`, `LatitudeCentralComparableClosure.lean` | Sharp neighboring and central bounds for `α ≠ 1` |
| Opposite/exceptional closure | `LatitudeOppositeComparableClosure.lean`, `LatitudeExceptionalComparablePointwiseClosure.lean` | Smooth-opposite and exceptional separated bounds |
| Unequal-scale closure | `LatitudeUnequalSeriesClosure.lean`, `LatitudeUnequalPointwiseClosure.lean` | Both oriented unequal-scale bounds |
| Latitude arithmetic | `LatitudeEstimate.lean`, `LatitudeRowArithmetic.lean` | Population-weighted rows and the `N^(1-α/2)` conversion |
| Exact latitude identity | `LatitudeAxialBridge.lean`, `LatitudeL2.lean` | `bemocLatitudeDeficit = -∑ E_jk` |
| Within-ring | `ConcreteWithinRing.lean` | `exists_bemocWithinRingDeficit_concrete_bound` |
| Cross-ring | `CrossRingEstimate.lean` | `exists_bemocCrossRingDeficit_concrete_bound` |
| Energy and CND core | `Core.lean` and its imported analytic modules | Decomposition and nonnegativity |

`LEAN_FORMALIZATION.md` contains the exhaustive theorem-level inventory.

## Track W: within-ring contribution

The within-ring contribution is unconditional.

The proof contains:

- the exact one-ring discrete and continuous identities;
- the endpoint Euler--Maclaurin theorem for every `0 < α < 2`;
- identification of the finite-part constant with `ζ(-α)`;
- a uniform scalar self-deficit estimate;
- concrete BEMOC population/radius comparisons;
- the summation
  `Σ ρ_p^α w_p^(1-α) = O(N^(1-α/2))`;
- the corrected sharp square-subsequence limit with distinct midpoint and
  shared-boundary population factors `8/3` and `4/3`.

The public bound is:

```lean
exists_bemocWithinRingDeficit_concrete_bound
```

The alternative circle-Fourier derivation is optional.  The direct endpoint
proof already supplies the required theorem.

## Track C: cross-ring contribution

The cross-ring contribution is unconditional.

The proof proceeds through:

- one normalized angular kernel for discrete and continuous ring pairs;
- exact gcd/lcm reindexing of two polygon grids;
- uniform Fourier decay for the angular cusp;
- smoothing domination and a phase-uniform trapezoid estimate;
- the pairwise error
  `Cα(ρ_pρ_q)^(α/2) gcd(w_p,w_q)^(1+α)/(w_pw_q)^α`;
- concrete BEMOC population multiplicity and divisor arithmetic;
- conversion of the resulting `M^(2-α)` bound to
  `N^(1-α/2)`.

The public bound is:

```lean
exists_bemocCrossRingDeficit_concrete_bound
```

## Track L: latitude contribution

The latitude contribution was the final analytic track and is now
unconditional.

### Exact band identity

The atomic BEMOC latitude rule and its continuous counterpart have equal
constant and linear moments on every band.  Angular disintegration and the
constant-potential formula give the exact identity

```text
bemocLatitudeDeficit α N
  = -∑ j, ∑ k, bandPairError N j k (latitudeKernel α).
```

`LatitudeAxialBridge.lean` proves the concrete geometric/Fubini proposition
used by `LatitudeL2.lean`; it is not an assumption at the public endpoint.

### Pointwise case partition

Every ordered band pair is assigned to a checked case:

| Geometric case | Closure |
|---|---|
| Polar comparable | Fixed-square polar estimate |
| Same-hemisphere unequal scale | Normally convergent even-power series |
| Polar/central/opposite unequal scale | Unified oriented unequal interface |
| Separated regular comparable | Sharp four-term mixed-derivative estimate |
| Exceptional separated comparable | Classifier-free radius chart |
| Neighboring nonresonant | Upper/lower local cusp decomposition |
| Neighboring resonant `α = 1` | Quadratic-log principal extraction and oscillation control |
| Central nonresonant | Central neighboring plus generic separated closure |
| Central resonant `α = 1` | Fixed-radius resonant pointwise closure |
| Opposite hemisphere | Smooth-opposite mixed Peano estimate |
| Bounded band count | Coarse finite fallback |

The final parameter split in
`veryLargeRemainingComparableLatitudeBounds` is exhaustive:

```lean
by_cases hα1 : α = 1
```

The `α = 1` branch uses the resonant constants; the `α ≠ 1` branch uses the
nonresonant upper/lower neighboring and central estimates.

### Resonant endpoint

For the reduced latitude cusp, the manuscript decomposition is interpreted
on the literal diagonal:

```text
hα(x) = Hα(x) + x^ν Bα(x)                    if α ≠ 1,
h1(x) = H1(x) + c1 x log x + x^(3/2) B1(x)  if α = 1.
```

The constants satisfy `Hα(0) = hα(0)`.  Both `x^ν Bα(x)` and `x log x` are
interpreted as zero at `x = 0`.  This convention is formalized because the
product quadrature contains literal diagonal atoms.

At `α = 1`, the proof:

- extracts the exact quadratic-log principal term;
- proves cancellation of its frozen quadratic part by the two band moments;
- controls coefficient and logarithmic-amplitude oscillation;
- bounds the higher `x^(3/2)` branch;
- assembles neighboring, central, and separated resonant cases.

Thus the resonant exponent requires no exclusion, limit argument, or
additional premise.

### Row summation and concrete scale

The pointwise estimates feed a symmetric ordered-pair partition.
`LatitudeRowArithmetic.lean` proves:

- the summable comparable-distance convolution;
- multiplicity-two latitude-depth coding;
- both orientations of the unequal-scale sum;
- scale-weighted and population-weighted row bounds;
- absolute control of the double band-error sum.

`LatitudeEstimate.lean` then converts the band-count scale to
`N^(1-α/2)`.  The unconditional public result is:

```lean
theorem exists_bemocLatitudeDeficit_concrete_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      |bemocLatitudeDeficit α N| ≤
        C * (N : ℝ) ^ (1 - α / 2)
```

## Track A: final assembly

All three components use the threshold `N ≥ 36`.  Their positive constants
are combined by addition in `exists_bemocComponentBounds_of_latitude`.

The exact deficit decomposition supplies the upper estimate.  The
Schoenberg/conditional-negative-definiteness development supplies
nonnegativity for every `0 < α < 2`.  `MainTheorem.lean` combines these facts
and unfolds `bemocEnergyDeficit` to the literal expression involving
`bemocFiniteEnergy`.

The root module imports this final theorem, so a canonical `lake build`
checks the complete dependency graph.

## Verification record

The completion checkpoint satisfies all project gates:

- `lake build` completes all 6,767 targets;
- a forced `latexmk` build produces the 10-page paper without TeX errors,
  undefined references, or bad boxes;
- every newly added module is transitively reachable from
  `BEMOCFormalization.lean`;
- project-owned Lean sources contain no `sorry`, `admit`, custom `axiom`, or
  `opaque` declaration;
- `#print axioms BEMOC.bemoc_deficit_bound` reports only `propext`,
  `Classical.choice`, and `Quot.sound`;
- `git diff --check` is clean.

The source audit command is:

```bash
rg -n '^\s*(axiom|opaque)\b|\b(sorry|admit)\b' \
  BEMOCFormalization.lean BEMOCFormalization --glob '*.lean'
```

## Maintenance invariants

- Preserve ordered-pair energy normalization.
- Constants may depend on `α`, but not on `N`, phases, ring indices, or band
  indices.
- Keep `0 < α < 2` explicit and isolate `α = 1` only where the logarithmic
  local model requires it.
- Treat polar, central, equatorial, antipodal, and literal diagonal cases
  explicitly.
- Do not replace the concrete BEMOC ring family with an asymptotic surrogate.
- Do not introduce `sorry`, `admit`, custom axioms, or opaque proof
  shortcuts.
- Keep conditional helper interfaces clearly distinguished from the
  unconditional public theorem.
- Preserve the corrected within-ring coefficient with distinct `8/3` and
  `4/3` population factors.
- Run the full Lean build and source audit after material proof changes.
- Rebuild `BEMOCRieszEnergies.tex` after manuscript changes.
- Update `README.md`, `CLAUDE.md`, `LEAN_FORMALIZATION.md`, and this document
  together whenever the verified project scope changes.

## Optional and out-of-scope work

The following items are not completion gates for the upper-bound project:

- Wagner's configuration-uniform lower bound;
- the matching lower asymptotic for the BEMOC sequence;
- a closed Gamma-form normalization for every positive-frequency cusp
  coefficient;
- the alternative circle-Fourier proof of the already established endpoint
  Euler--Maclaurin theorem;
- optimization of any proof constant.
