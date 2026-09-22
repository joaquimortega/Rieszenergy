# Formalization status

The current target is `definitive.tex`, Theorem `thm:main`, Corollaries
`cor:main` and `cor:wce`, and the accompanying optimality statements. The
previous Simpson-based proof is archived, not used as a proof of this target.

## Verified proof progress

The reviewed scaffold was pushed as `d621018`, and the first substantial proof
checkpoint as `2300930`. Subsequent proof development
uses the same Lean 4.19.0 and pinned mathlib revision. The following targets
now have checked proofs in the active namespace `BEMOC.Definitive`:

| Result | Checked declaration / module |
|---|---|
| Full construction, cardinality, injectivity, boundary identities, canonical set | `constructionFacts`, `boundaryFormulas`, `diamondPoints_card` in Construction |
| Radius/population comparability and multiplicity at most three | `geometry_bounds` in Geometry |
| Polar band widths, noncap sine comparison, and band separation | `angular_geometry` in AngularGeometry |
| Chord comparison and near/separated band angle estimates | AngularDistance |
| General real binomial theorem and square-root coefficient tail | SeparatedBinomialSeries and BinomialTail |
| Analytic scalar series with exact finite-order derivatives | ScalarPowerSeries |
| Full mixed Taylor estimate on closed band rectangles | `mixedTaylorBound` in Taylor |
| Measure conditional negative definiteness for 0<α<2 | `measureNegativeType_of_pos_of_lt_two` in NegativeType |
| Probability surface measure, uniform height marginal and constant potential | `constantPotential_of_pos` in SurfaceMeasure |
| Nonnegative finite and Diamond energy deficits | `energy_nonnegative`, `diamond_nonnegative` in EnergyDecomposition |
| Two vanishing band moments and positive-exponent block symmetry | `bandMoments`, `blockSymmetry_of_pos` in BandErrors |
| Constant height potential of the actual averaged latitude kernel | `half_intervalIntegral_latitudeKernel` in LatitudePotential |
| Exact summed latitude-error decomposition | `latitudeIdentity_of_pos` in LatitudeIdentity |
| Phase-uniform angular trapezoid estimate for 0<α<2 | `trapezoid_bound` in AngularQuadrature |
| Exact periodic gcd/lcm grid counting | `Grid.grid_multiplicity` in GridMultiplicity |
| Arithmetic gcd sum for all α>0 | `gcd_sum_bound` in Longitude |
| Full phase-uniform longitude bound for 0<α<2 | `longitude_bound` in Longitude |
| Summation of the three latitude block regimes | `latitude_bound_of_blocks` in LatitudeSummation |
| Uniform finite-size closure | `small_size_bound` in Latitude |
| Main theorem reduced to the latitude bound, or its three block regimes | `main_theorem_of_latitude`, `main_theorem_of_block_estimates` in MainTheorem |
| Projection averages and exact cap area | SphereProjection and SphereCapMeasure |
| Universal and Diamond Stolarsky identities with ordinary dt | `stolarskyIdentity`, `diamondStolarsky` in CapDiscrepancy |
| Universal cap discrepancy lower bound with constant 1/16 | `beckLowerBound`, `capDiscrepancy_lower_rpow` in CapLowerBound |
| Cap corollary reduced to the main energy theorem at α=1 | `cap_corollary_of_main` in Corollaries |
| Conditional cap/Sobolev assembly | `cap_assembly`, `sobolev_assembly` in Corollaries |
| Nonempty spectral unit ball; bounded supremum under embedding | SobolevBasic |

Taylor now proves `MixedTaylorCalculusBridge` and the unconditional
`mixedTaylorBound`, including differentiation of parameterized band integrals,
commutation of the required mixed partials, and closed endpoints. The remaining
block estimates still require concrete kernel derivative/cusp bounds.

## Remaining work

The **unconditional main theorem and both final corollaries are not yet
proved**. The current main assembly requires only `LatitudeBound α`, which
has itself been reduced to the three exhaustive block estimates. The remaining
work includes smooth separated-kernel series, polar kernel derivative bounds,
comparable cusp/neighbor blocks, and unequal blocks.

The cap branch has complete Stolarsky and Beck proofs and now needs only
the main energy theorem. Beck's bound permits repeated point labels. The Sobolev branch needs
existence/completeness of the harmonic basis, the spectral-space/continuous-representative bridge,
embedding, the distance-kernel comparison and the universal lower bound.
The conditional assembly proofs do not discharge these hypotheses.

Some blueprint contracts describe optional proof routes: Appendix-1 Gamma
coefficient statements are not yet inhabited, but the required trapezoid
bound is already proved by the extracted generic cusp/smoothing route. The
full `SurfaceIntegration` formula remains separate; its specific constant
latitude-potential consequence has been proved without assuming it.

`MainTheoremTarget` and `DefinitiveTargets` remain proposition definitions,
not completed theorems. The actual cap/Sobolev observables are defined
independently of energy. No custom axioms or proof shortcuts are used. Axiom
audits of the major proved declarations report only `propext`, `Classical.choice`, and
`Quot.sound`.

## Comparator and metadata

The Mathlib-only standalone file is generated from the active import graph
and elaborated separately. A pinned comparator/exporter backport for
Lean 4.19 passed a full comparison of five major results in the current
40-module checkpoint: the main theorem from block estimates, Beck, the cap
corollary from the main theorem, longitude, and mixed Taylor. Statement and
dependency matching, the standard-axiom check, and kernel replay all passed.
The main and cap statements retain their explicit energy/block assumptions. See
[comparator/README.md](comparator/README.md) for setup and evidence as the
integration develops. The root `formalization.yaml` validates against the
reporting standard's v0.4 schema and distinguishes proved conditional results
from the still-open final targets.

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
