# Working on the definitive Diamond formalization

`definitive.tex` is the authoritative source for the current task. The earlier
`BEMOCRieszEnergies.tex` and its Simpson-based formalization live in `legacy/`.
The two constructions differ; never transfer a concrete old theorem without
proving its hypotheses for the new configuration.

The default `lake build` target is `BEMOCFormalization.lean`. All current proof
modules must be imported transitively there. Use namespace `BEMOC.Definitive`,
two-space indentation, descriptive declaration names and public doc comments.
Do not introduce `sorry`, `admit`, custom `axiom`, or `opaque` shortcuts. A named
`def ... : Prop` is an obligation, not a proved theorem. Keep this distinction
explicit in the proof inventory and every public-facing status claim.

Every current module has a detailed `blueprint/modules/<Module>.md` guide with
its mathematical proof, exact Lean source, dependencies and source references.
Run `python scripts/sync_blueprint.py` after source changes, and check the
notebook for source corrections. Record newly found mistakes, clarifications
and simplifications in `NOTEBOOK.md` with evidence and resolution status.

Use `gpt-6-sol` explicitly for independent review or proof subagents, as the
user requested. Record review scope, findings and dispositions in `reviews/`.

Required checks after relevant changes: `lake build`, the proof-shortcut audit
in `scripts/check_scaffold.py`, `python scripts/sync_blueprint.py --check`, and
`git diff --check`. Rebuild an edited TeX source with latexmk. Never commit
`.lake/`, generated TeX files or generated manuscript PDFs. Preserve the source
manuscript unless a change is explicitly requested; corrections belong first
in the notebook.

Full requested scope: prove the main theorem and both corollaries; keep the
accompanying optimality obligations explicit. Produce a self-contained Lean
export and comparator verification, maintain `formalization.yaml`, and push
verified work to the existing GitHub repository. Passing scaffold elaboration
is not completion of the formalization.
