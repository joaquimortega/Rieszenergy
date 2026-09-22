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
environment, fixes the upstream comparison/axiom traversal's tail recursion,
and compiles the standalone module directly without changing the project
lakefile. `KernelReplay.lean` adapts Lean 4.19's kernel replay to call the
kernel environment directly, avoiding frontend private-name registration
collisions while still checking every declaration. The runner raises the
process stack limit to 64 MiB for deep Mathlib expressions. Set
`COMPARATOR_BIN`, `COMPARATOR_LEAN4EXPORT`, and
`COMPARATOR_LANDRUN` to the paths printed by that build script, then run:

```sh
python3 scripts/run_comparator.py \
  --challenge-module BEMOCFormalization.MainTheorem \
  --theorem BEMOC.Definitive.main_theorem_of_estimates
```

`run_comparator.py` writes a temporary JSON config with only Lean's standard
`propext`, `Quot.sound`, and `Classical.choice` axioms permitted, then invokes
`lake env` on comparator. Repeat `--theorem` to check multiple declarations
in one challenge module. It requires the real `landrun`; upstream's fake
landrun is only a development shim and provides no sandbox assurance. Follow
upstream's `systemd-run` containment advice when checking untrusted solutions.
Never use a custom axiom, `sorry`, `admit`, or `opaque` proof shortcut to fill a
challenge or solution theorem.

The full comparator check **passed** on the current 40-module proof
checkpoint for these exact declarations:

- `BEMOC.Definitive.main_theorem_of_block_estimates`
- `BEMOC.Definitive.beckLowerBound`
- `BEMOC.Definitive.cap_corollary_of_main`
- `BEMOC.Definitive.longitude_bound`
- `BEMOC.Definitive.mixedTaylorBound`

It built and exported both the modular challenge and the Mathlib-only
standalone solution under real landrun, matched the selected statements and
their transitive definitions, checked the permitted axioms, and replayed the
solution in the kernel: `Solution valid. Your solution is okay!`
See the [verification record](checkpoint-verification.md) and
[actual run log](verification-40-modules.txt). The standalone source has
15,307 lines. Its source hash is recorded with the command.

The main theorem in this check assumes the three latitude block bounds, and
the cap corollary assumes the main energy theorem at α=1. Comparator confirms
those exact conditional statements; it does not prove their remaining
hypotheses. The universal Beck, longitude, and mixed Taylor results have
checked proofs under only their stated parameter/domain assumptions.

An earlier full check passed on the 19-module conditional scaffold at
`d621018`. Negative controls rejected the upstream `simple_axiom_issue`
example with `Illegal axiom detected: 'helper'`, and a pair of valid proofs
of different statements with `Challenge and solution theorem statement do
not match: 'comm'`.

The source exporter resets Lean's module-local `auxLemmasExt` cache at each
inlined module boundary. Without that reset, the first strict comparison
failed at `BEMOC.Definitive.point`: separately compiled modules and the merged
file gave the same numeral proof different generated names. The cache is
explicitly local and absent from `.olean` files in Lean 4.19. The exporter
also isolates file-level `open` state in sections and prefixes file-private
declaration names to avoid collisions when multiple modules become one file.

Upstream documentation: https://github.com/leanprover/comparator

The adapted `KernelReplay.lean` retains Lean's copyright notice and is
covered by [Apache 2.0](LICENSE-LeanReplay). That notice applies to the
adapted tool source; it does not assign a license to the manuscript or the
rest of this repository.
