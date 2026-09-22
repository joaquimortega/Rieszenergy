# Comparator verification: 40-module checkpoint

Date: 2026-09-23 (Europe/Madrid). Result: **PASS, exit code 0**.

The challenge is the checked modular `BEMOCFormalization` root. The solution
is the generated Mathlib-only `comparator.SelfContained`, containing all
40 active project modules plus the root. The standalone SHA-256 is:

`831c5850cf9632995a4eca1e558f2e731a586c129b74d90aea14eb6543845d47`

## Exact command

After building the pinned backport and setting the three tool environment
variables as described in [README](README.md):

```sh
python3 scripts/run_comparator.py \
  --challenge-module BEMOCFormalization \
  --theorem BEMOC.Definitive.main_theorem_of_block_estimates \
  --theorem BEMOC.Definitive.beckLowerBound \
  --theorem BEMOC.Definitive.cap_corollary_of_main \
  --theorem BEMOC.Definitive.longitude_bound \
  --theorem BEMOC.Definitive.mixedTaylorBound
```

The actual [run log](verification-40-modules.txt) records successful builds,
exports of the same five declarations from both modules, and:

```text
Running kernel on solution.
Solution valid.
Your solution is okay!
```

The allowed axioms were exactly `propext`, `Quot.sound`, and
`Classical.choice`. Real landrun was used with abort-on-panic enabled.
The Lean 4.19 backport and kernel replay adaptations are described in the
README and pinned build script; they are not an unmodified upstream binary.

## Scope and accompanying checks

The main result here is conditional on `ComparableBlockBound`,
`SameSideBlockBound`, and `OppositeBlockBound`. The cap result is conditional
on `MainTheorem 1`. This verification does not assert `MainTheoremTarget`
or the final cap/Sobolev targets without those missing proofs.

The frozen source tree also passed `lake build`, the source-shortcut and
import-coverage audit, blueprint/source synchronization, and metadata schema
v0.4 validation. The standalone compiled during the comparator run. Direct
axiom checks of Beck, its explicit lower bound, cap assembly, the scalar
iterated derivative theorem, and the generalized binomial theorem reported
only the same three standard axioms. Independent Sol reviews cover the new
cap and angular/series modules.

The proof source was frozen separately from ongoing module development;
all 41 staged Lean files were byte-for-byte identical to that built tree.
