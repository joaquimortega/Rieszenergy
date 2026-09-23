# Final comparator verification

Date: 2026-09-23. Result: **PASS, exit code 0**.

The challenge is the frozen modular `BEMOCFormalization` root; the solution
is the generated `comparator.SelfContained`. The development has 104 active
modules plus the root. The standalone imports only Mathlib modules and
contains 37,595 lines. Its SHA-256 is:

`d4c38100c8ef19dfb64cbc18acb3f8f3fec30b8a2f5fba4da1d38558da9ffcd2`

[Source hashes](source-sha256.json) identify all 105 modular Lean files and
the standalone source. These files matched the final repository sources
byte for byte when the result was recorded.

## Exact command

Build the pinned tool versions and set the three environment variables as
described in [README](README.md), then run:

```sh
python3 scripts/run_comparator.py \
  --challenge-module BEMOCFormalization \
  --theorem BEMOC.Definitive.manuscript_targets \
  --theorem BEMOC.Definitive.diamond_energy_bound \
  --theorem BEMOC.Definitive.cap_corollary \
  --theorem BEMOC.Definitive.l2_sobolev_corollary \
  --theorem BEMOC.Definitive.l2_sobolev_optimality \
  --theorem BEMOC.Definitive.l2_sobolev_energy_comparison \
  --theorem BEMOC.Definitive.manuscript_sobolev_model \
  --theorem BEMOC.Definitive.spherePolynomialLaplacian_eigen_iff_unconditional
```

The [actual run log](verification-final.txt) records both source builds,
exports of all eight selected declarations, statement and transitive-definition
matching, the permitted-axiom check, and kernel replay:

```text
Running kernel on solution.
Solution valid.
Your solution is okay!
```

Tool pins: comparator `437574bcec4e7d76fa141e98e4a72682ab580859`,
lean4export `aca5d120d25d9ae14436f96c0732497f11f3931e`, and landrun
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`. The checked run used the
Lean 4.19 adaptations committed with this repository.

The permitted axioms were exactly `propext`, `Quot.sound`, and
`Classical.choice`. Real landrun was used, with abort-on-panic enabled.
This uses the documented Lean 4.19 backport and kernel replay adaptation,
not an unmodified upstream comparator binary.

## Mathematical scope

The selected results include the unconditional main theorem and cap
corollary, the actual finite-set formula and cardinality, and the genuine
L² Sobolev upper/lower bounds and energy comparison. Every L² spectral
unit-ball class participates through its proved unique continuous
representative. The model theorem identifies the weak L² eigenspaces of
the intrinsic rotation-field sphere Laplacian with harmonic restrictions;
the final selected theorem gives the strong polynomial-core counterpart.
No analytic estimate remains as an extra hypothesis. Parameter ranges,
N≥4, and the distinct-node hypothesis of the universal lower statement
remain explicit.

The Laplacian is an intrinsic angular operator on polynomial restrictions,
with a weak L² test relation. A separate general-manifold Laplace–Beltrami
implementation, maximal self-adjoint domain, and packaged Sobolev Hilbert
type are outside the claimed scope; the complete defining L² unit ball,
its representatives, eigenbasis identification, and WCE are formalized.

## Accompanying checks

The 97-module base was rebuilt from source in an isolated tree. The final
seven modules, updated root, and the later lower-bound helper rename were
built in the final frozen tree. `lake build`, all-module import coverage,
source shortcut audit, exact guide/source synchronization, metadata schema
v0.4 validation, and whitespace checks passed. Direct axiom checks of the
final aggregates, finite-set theorem, and polynomial eigenspace theorem
reported only the same standard axioms; see [axiom log](axioms-final.txt).
Independent Sol reviews cover the main/cap and complete Sobolev chains.
All nine dependency commits match `lake-manifest.json`, with no Lean-source
or build-configuration content changes. The dependency dirty-worktree
warnings concern executable mode bits and a missing Batteries documentation
README, not theorem sources.

The earlier 97-module standalone attempt detected a duplicate public helper
name in two independent branches. That naming collision was repaired before
this run. The historical [40-module record](checkpoint-verification.md)
remains separate and certifies its explicitly conditional statements only.

The first 104-module comparison detected a generated private helper whose
module-qualified name differed in the merged file. The exporter now preserves
the original module identity at each boundary and restores the standalone
identity at the end; the mathematical proof and comparator equality checks
are unchanged. See notebook N43.

A subsequent comparison detected lexical renaming of an explicit private
helper. Three source-level private helper names were made distinct, enabling removal
of all private-name rewriting from the exporter. The third repair avoids a
private/public visibility collision. See notebook N44–N45.
