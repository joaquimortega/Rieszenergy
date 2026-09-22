# Standalone Lean export and comparator check

`scripts/export_self_contained.py` follows the imports from
`BEMOCFormalization.lean`, orders the current project modules by dependency,
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
currently contains definitions, formal proof obligations, and conditional
assembly results including `BEMOC.Definitive.main_theorem_of_estimates` and
`BEMOC.Definitive.main_theorem_of_latitude`. Its successful elaboration does
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

The project uses Lean 4.19.0. `scripts/build_comparator_419.sh` builds a pinned,
experimental backport: comparator `437574b` with the patch in this directory,
format-2 lean4export `aca5d12` with its toolchain set to 4.19.0, and real
landrun `811cfff`. The comparator patch adapts a Lean API type, preserves the
exporter's `--` argument through current landrun, retains the caller's Lean
environment, and compiles the standalone module directly without changing the
project lakefile. Set `COMPARATOR_BIN`, `COMPARATOR_LEAN4EXPORT`, and
`COMPARATOR_LANDRUN` to the paths printed by that build script, then run:

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

The actual cross-module check on clean commit `d621018` did **not** pass.
Comparator built and exported both modules, then reported
`Const does not match between challenge and target 'BEMOC.Definitive.point'`.
The types matched; the first difference in the values was an automatically
generated proof constant for `Nat.AtLeastTwo (0 + 2)`:
`BEMOC.Definitive.boundary._proof_1` in the modular challenge versus
`BEMOC.Definitive.parallelVector._proof_1` in the inlined solution. Both are
internal proof terms created while elaborating numerals. Isolating each
inlined module in a `section` and replacing the point fallback's `by norm_num`
with an explicit proof did not remove this difference. The exporter merges
the modules' elaboration contexts, so its generated private proof names differ
from those of separately compiled modules. Comparator deliberately requires
the transitive definitions to match exactly. A separate self-comparison also
failed during old comparator kernel replay on duplicate normalized private
Mathlib declaration names. No comparator certification is claimed.

Upstream documentation: https://github.com/leanprover/comparator
