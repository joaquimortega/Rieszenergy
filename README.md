# Deterministic Diamond points

Lean formalization of the main theorem and both corollaries of
[`definitive.tex`](definitive.tex), *A set of points with optimal L² spherical
cap discrepancy*, by Carlos Beltrán, Jordi Marzo and Joaquim Ortega-Cerdà.

The theorem `BEMOC.Definitive.manuscript_targets` proves the energy bound,
cap discrepancy, genuine L² Sobolev cubature bound and its matching universal
lower bound, including existence of the harmonic basis. All 104 modules
build, and `manuscript_sobolev_model` proves the required continuous-representative
and intrinsic weak-Laplacian identifications. Final standalone comparator
verification is in progress; see [verification status](LEAN_FORMALIZATION.md).

For every `0 < α < 2`, the energy theorem proves

```text
0 ≤ (2^(α+1)/(α+2)) N² − Σ(x,y) |x−y|^α ≤ Cα N^(1−α/2),
```

for every `N ≥ 4`, with a constant uniform over independent ring rotations.
The sum is over ordered pairs. The corollaries give cap discrepancy comparable
to `N^(-3/4)` and spectral `H^s` worst-case error at most `Cs N^(-s/2)` for
`1 < s < 2`, together with the matching universal lower bound. Cap discrepancy
and Sobolev worst-case error are defined from their geometric and spectral
observables, independently of energy.

- [Detailed modular blueprint and all 104 proof guides](blueprint/README.md)
- [Theorem inventory and verification status](LEAN_FORMALIZATION.md)
- [Source corrections and formalization notebook](NOTEBOOK.md)
- [Independent Sol reviews](reviews/README.md)
- [Standalone source and comparator evidence](comparator/README.md)
- [Previous formalization and reuse boundaries](legacy/README.md)
- [Formalization metadata](formalization.yaml)

Build with Lean 4.19.0 and the pinned mathlib revision:

```bash
lake exe cache get
lake build
python scripts/check_scaffold.py
python scripts/sync_blueprint.py --check
```

`BEMOCFormalization.lean` imports every active module. The midpoint-only
configuration uses `r_j = 4j`. The previous Simpson configuration is archived
under `legacy/`; only generic arguments from it are reused. Its configuration
estimates are not used to prove the new theorem. The repository history and
reusable source material are preserved.
