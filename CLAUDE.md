# Repository guidance

## Scope

The formalized target is the upper-bound half of the main theorem in
`BEMOCRieszEnergies.tex`, for negative Riesz energies of the concrete BEMOC
point set and every `0 < α < 2`:

```text
0 ≤ 2^(α+1)/(α+2) * N^2
      - Σ_{x ≠ y in P_N} |x-y|^α
  ≤ C_α N^(1-α/2).
```

Wagner's configuration-uniform lower bound and the matching lower asymptotic
are explicitly outside the formalization scope.

The Lean root is `BEMOCFormalization.lean`, with analytic helper modules in
`BEMOCFormalization/`. Other TeX papers in the directory are out of scope
unless the user explicitly says otherwise.

## Completed endpoint

The upper-bound project is complete.  The unconditional public theorem is
`BEMOC.bemoc_deficit_bound` in `BEMOCFormalization/MainTheorem.lean`.
It is assembled from:

- `exists_bemocLatitudeDeficit_concrete_bound`;
- `exists_bemocWithinRingDeficit_concrete_bound`;
- `exists_bemocCrossRingDeficit_concrete_bound`;
- `exists_bemocComponentBounds`.

All neighboring, central, opposite, unequal-scale, polar, finite-depth, and
resonant latitude cases are discharged.  In particular, `α = 1` is not an
assumption or an open endpoint.  No upper-bound analytic hypothesis remains
for callers.

## Builds

```bash
lake build
latexmk -pdf -interaction=nonstopmode -halt-on-error BEMOCRieszEnergies.tex
```

Lean and mathlib are pinned by `lean-toolchain` and `lake-manifest.json`.
`LEAN_FORMALIZATION.md` records the checked results.

## Formalization discipline

- Keep all project-owned Lean modules free of `sorry`, `admit`, and custom
  axioms or opaque proof shortcuts.
- Preserve the unconditional status of `BEMOC.bemoc_deficit_bound`; helper
  assembly theorems may remain conditional, but the public endpoint may not
  acquire analytic premises.
- Distinguish an unconditional theorem from an assembly theorem whose
  analytic estimates are arguments.
- Preserve ordered-pair energy normalization throughout.
- The endpoint Euler--Maclaurin theorem is unconditional for `0 < α < 2`:
  endpoint residual regularity and the complex analytic-continuation proof
  identifying the finite-part power constant with `ζ(-α)` are complete.
- Within-ring circle aggregation and the concrete BEMOC estimate
  `Σ ρ_p^α w_p^(1-α) = O(N^(1-α/2))` are unconditional.  The corrected sharp
  square-subsequence Riemann-sum limit is also unconditional, including the
  low-population transfer and the distinct `8/3` and `4/3` population factors.
- The corrected general-`α` within-ring coefficient in the TeX retains the
  distinct asymptotic populations `8mx/3` and `4mx/3`; the former simpler
  radius-sum coefficient is valid only at `α = 1`.
- The within-ring, cross-ring, and complete latitude estimates are
  unconditional.  This includes the neighboring/central/opposite comparable
  closure and the resonant `α = 1` branch.
- The TeX decomposition is endpoint-safe on the literal diagonal atoms:
  `Hα(0) = hα(0)`, with `x^ν Bα(x)` and `x log x` interpreted as zero at
  `x = 0`.
- After Lean edits, run the full `lake build`, the placeholder/custom-axiom
  audit documented in `LEAN_FORMALIZATION.md`, and `git diff --check`.
- Update all repository status documents together when the verified scope
  changes.
