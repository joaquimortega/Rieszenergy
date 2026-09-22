# Formalization status

The current target is `definitive.tex`, Theorem `thm:main`, Corollaries
`cor:main` and `cor:wce`, and the accompanying optimality statements. The
previous Simpson-based proof is archived, not used as a proof of this target.

## Verified checkpoint: reviewed scaffold

`lake build` successfully elaborates the 18 active modules and root entry
point with Lean 4.19.0 and mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. A Mathlib-only standalone export also
elaborates. Every module has a detailed guide and an independent gpt-6-sol
interface review. The source-shortcut and whitespace checks pass.

The initial checkpoint proves:

| Declaration in `BEMOC.Definitive` | Content |
|---|---|
| `parallelVector_mem_sphere` | The valid-height parametrization lies on the unit sphere |
| `continuousEnergy_one` | The named energy constant at α=1 is 4/3 |
| `deficit_eq_latitude_add_longitude` | Exact algebraic decomposition D=A+B |
| `main_theorem_of_estimates` | Conditional assembly from latitude, longitude, small-N and nonnegativity estimates |
| `capDiscrepancySq_nonneg` | The integral of the squared actual cap error is nonnegative |
| `sobolev_exponent_range` | 1<s<2 implies 0<2s−2<2 |
| `sobolev_normalized_exponent` | Normalized energy exponent is −s |
| `cap_normalized_exponent` | Cap square-root exponent is −3/4 |

These results do **not** include a proof of the main energy bound, a proof of
Stolarsky's identity, a Beck lower bound, or a Sobolev kernel comparison.
Absence of proof shortcuts is not evidence that these missing proofs exist.

## Remaining work

- Prove `ConstructionFacts`, `BoundaryFormulas`, `GeometryBounds` and
  `AngularGeometry`, including the genuine N-element-set bridge.
- Prove normalized surface disintegration, `ConstantPotential`,
  `MeasureNegativeType`, and `DiamondNonnegative`.
- Prove Fourier decay and `TrapezoidBound`, grid multiplicity and `GcdSumBound`,
  then `LongitudeBound` for the concrete Diamond polygons.
- Prove band moments, kernel symmetry, the exact latitude identity, the double
  Taylor inequality, separated and polar derivative estimates, the angular
  cusp split, all three block regimes and their sums; discharge `LatitudeBound`.
- Prove uniform `SmallSizeBound` and instantiate the proved main assembly.
- Prove actual Stolarsky and Beck/relabeling ingredients and the cap corollary.
- Construct a complete orthonormal harmonic basis, identify the continuous
  spectral model with the manuscript's H^s space, prove bounded evaluation,
  the distance-kernel spectral comparison and universal Sobolev lower bound,
  then the actual worst-case-error corollary.
- Verify the self-contained export with a working comparator/exporter pair
  and update the metadata with final theorem declarations and evidence.

`MainTheoremTarget`, `CapDiscrepancyCorollary`, `SobolevCorollary`,
`SobolevOptimality` and `DefinitiveTargets` are currently **unproved proposition
definitions**. They are explicit destinations and are not added to Lean's
axiom environment. The source defines the actual observables independently
of energy, so the corollary targets cannot be satisfied by relabeling a deficit.

## Reproducible checks

```bash
lake build
python scripts/check_scaffold.py
python scripts/sync_blueprint.py --check
python scripts/export_self_contained.py
lake env lean comparator/SelfContained.lean
git diff --check
```

See [comparator/README.md](comparator/README.md) for the separate comparator
verification gate and current compatibility status. No comparator certification
is claimed by a successful Lean build. `legacy/` is excluded from this build;
its original import paths are reproducible in a checkout of commit `2348f37`.
