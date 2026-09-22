# Standalone Lean export and comparator check

`scripts/export_self_contained.py` follows the imports from
`BEMOCFormalization.lean`, orders the 19 current project modules by dependency,
and writes `comparator/SelfContained.lean`. That generated file imports only
`Mathlib`. It is a source export, not an automatic proof completion. Regenerate
and elaborate after changing the Lean sources:

```sh
python3 scripts/export_self_contained.py
lake env lean comparator/SelfContained.lean
rg -n '^\s*(axiom|opaque)\b|\b(sorry|admit)\b' \
  BEMOCFormalization.lean BEMOCFormalization comparator/SelfContained.lean \
  --glob '*.lean'
```

The expected `rg` result is no matches (exit code 1). The standalone file
currently contains definitions, formal proof obligations, and the conditional
`BEMOC.Definitive.main_theorem_of_estimates`. Its successful elaboration does
**not** prove `BEMOC.Definitive.MainTheoremTarget` or the cap/Sobolev targets.

Comparator compares the statement of a solution theorem with a trusted
challenge theorem and checks its proof against permitted axioms. It does not
prove missing mathematical estimates or transform an imported development
into standalone source. The trusted challenge can be an existing project
module, such as `BEMOCFormalization.MainTheorem` for the current conditional
assembly theorem. A complete proof would first need named, proved theorems
for the unconditional main target and corollaries in the authoritative project
modules. The trusted challenge must expose those exact statements, and the
standalone solution must elaborate with `import Mathlib` alone.

The project uses Lean 4.19.0. Upstream comparator's first published revision
uses 4.20.0-rc5, and its current head uses 4.35.0-rc2. No comparator/exporter
pair compatible with this project's Lean version was established here. Do not
represent elaboration or the script below as a successful comparator check.
When a compatible pair is available, set executable paths for `COMPARATOR_BIN`,
`COMPARATOR_LEAN4EXPORT`, and `COMPARATOR_LANDRUN`, then run, for example:

```sh
python3 scripts/run_comparator.py \
  --challenge-module BEMOCFormalization.MainTheorem \
  --theorem BEMOC.Definitive.main_theorem_of_estimates
```

`run_comparator.py` writes a temporary JSON config with only Lean's standard
`propext`, `Quot.sound`, and `Classical.choice` axioms permitted, then invokes
`lake env` on comparator. It requires the real `landrun`; upstream's fake
landrun is only a development shim and provides no sandbox assurance. Follow
upstream's `systemd-run` containment advice when checking untrusted solutions.
Never use a custom axiom, `sorry`, `admit`, or `opaque` proof shortcut to fill a
challenge or solution theorem.

Upstream documentation: https://github.com/leanprover/comparator
