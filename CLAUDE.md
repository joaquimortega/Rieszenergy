# Repository guidance

## Scope

The sole formalization target is `BEMOCRieszEnergies.tex`, whose main theorem
concerns negative Riesz energies of the BEMOC point set for `0 < α < 2`:

```text
Σ_{x ≠ y in P_N} |x-y|^α
  = 2^(α+1)/(α+2) * N^2 - Θ_α(N^(1-α/2)).
```

The Lean root is `BEMOCFormalization.lean`, with analytic helper modules in
`BEMOCFormalization/`. Other TeX papers in the directory are out of scope
unless the user explicitly says otherwise.

## Builds

```bash
lake build                         # formalization; required after Lean edits
latexmk -pdf BEMOCRieszEnergies.tex
```

Lean and mathlib are pinned by `lean-toolchain` and `lake-manifest.json`.
`LEAN_FORMALIZATION.md` records the checked results and remaining obligations.

## Formalization discipline

- Keep all project-owned Lean modules free of `sorry`, `admit`, and custom
  axioms.
- Deep unfinished estimates must remain explicit named propositions or
  structures; never hide them behind an axiom.
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
- Other active missing analytic components are uniform Fourier/Bessel
  aliasing, gcd/Jordan summation, latitude block estimates, and Wagner's
  universal lower bound.
- Rebuild with `lake build` and update `LEAN_FORMALIZATION.md` after material
  progress.
