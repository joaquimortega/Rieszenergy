# Deterministic Diamond points

Lean formalization in progress for the main theorem and both corollaries of
[`definitive.tex`](definitive.tex), *A set of points with optimal L² spherical
cap discrepancy*, by Carlos Beltrán, Jordi Marzo and Joaquim Ortega-Cerdà.

The current development defines the new midpoint-only Diamond configuration
and its energy, actual cap discrepancy, and spectral Sobolev worst-case error.
It contains a modular, executable blueprint and checked analytic foundations,
including negative type, constant surface potential, the full longitude bound,
latitude block summation, the actual Stolarsky invariance principle, and
Beck's universal cap discrepancy lower bound with constant 1/16.
**The unconditional main theorem and the two corollaries are not yet proved.**
Named proposition definitions are open obligations, not accepted axioms or
completed theorems.

For every `0 < α < 2`, the main target is

```text
0 ≤ (2^(α+1)/(α+2)) N² − Σ(x,y) |x−y|^α ≤ Cα N^(1−α/2),
```

for all `N ≥ 4`, with a constant uniform over independent ring rotations.
The corollary targets are cap discrepancy comparable to `N^(-3/4)` and spectral
`H^s` worst-case error at most `Cs N^(-s/2)` for `1 < s < 2`.

- [Detailed modular blueprint](blueprint/README.md)
- [Checked results and open proof obligations](LEAN_FORMALIZATION.md)
- [Source corrections and formalization notebook](NOTEBOOK.md)
- [Independent Sol reviews](reviews/README.md)
- [Previous formalization and reuse boundaries](legacy/README.md)
- [Formalization metadata](formalization.yaml)

Build with Lean 4.19.0 and the pinned mathlib revision:

```bash
lake exe cache get
lake build
python scripts/check_scaffold.py
python scripts/sync_blueprint.py --check
```

`BEMOCFormalization.lean` imports every active module. The old Simpson
configuration is archived under `legacy/`; its main theorem is not a proof for
the new point set. The current project replaces the old default build while
preserving the repository's history and reusable source material.
