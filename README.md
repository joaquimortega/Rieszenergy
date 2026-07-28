# BEMOC negative Riesz energies

Lean 4 formalization and supporting manuscript/code for the BEMOC negative
Riesz-energy project.

## Status

The upper-bound formalization is complete for every `0 < α < 2`, including
the resonant exponent `α = 1`.  The public theorem
`BEMOC.bemoc_deficit_bound` proves that the concrete BEMOC energy deficit is
nonnegative and satisfies

```text
continuousEnergy α * N² - bemocFiniteEnergy α N
  ≤ Cα N^(1 - α/2)
```

for all sufficiently large `N`.  It has no caller-supplied analytic
hypotheses.  Wagner's configuration-uniform lower bound and the matching
lower asymptotic are outside the formalization scope.

## Build

The canonical Lean entry point is `BEMOCFormalization.lean`:

```bash
lake build
latexmk -pdf BEMOCRieszEnergies.tex
```

The proof-completion checkpoint is Git commit `1287c26`.  At that checkpoint
the full Lean build passes, the paper builds to a 10-page PDF, and the
project-owned Lean sources contain no `sorry`, `admit`, custom `axiom`, or
`opaque` declarations.

See `LEAN_FORMALIZATION.md` for the detailed verified inventory and
`FORMALIZATION_BLUEPRINT.md` for the completed proof architecture.
