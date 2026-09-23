# Formalization status

The current target is `definitive.tex`, Theorem `thm:main`, Corollaries
`cor:main` and `cor:wce`, and the accompanying optimality statements. The
previous Simpson-based proof is archived, not used as a proof of this target.

## Proved results

The final public declaration is `BEMOC.Definitive.manuscript_targets` in
`Manuscript.lean`. Its conclusion `ManuscriptTargets` has no analytic premise
and includes the genuine L² Sobolev unit ball. The theorem
`manuscript_sobolev_model` proves the representative and intrinsic weak
eigenspace identifications. `diamond_energy_bound` states the literal
finite-set energy formula and exact cardinality. The main bound is uniform
for every `0<α<2`, all `N≥4`, and arbitrary ring phases.

The complete 104-module graph builds with Lean 4.19.0 and the pinned mathlib
revision. The original 97-module graph also passed a fresh build in an isolated
source tree. The final snapshot retains those sources apart from a
subsequent lower-bound helper rename detected by standalone elaboration;
the changed module and its dependents were rebuilt.
The seven added model/assembly modules and updated root also passed the
separate frozen build. Final independent main and Sobolev reviews pass.
Standalone comparison is the remaining verification gate.

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
| Global separated kernel extension and fourth derivative, including poles | `separatedDerivativeBound_of_range` in SeparatedComplete |
| Both unequal latitude block regimes | `sameSideBlockBound`, `oppositeBlockBound` in UnequalBlockEstimates |
| Every comparable latitude block, including the diagonal and α=1 | `comparable_block_bound` in ComparableAssembly |
| Unconditional energy theorem for all 0<α<2 | `main_theorem`, `main_theorem_target` in MainTheorem |
| Projection averages and exact cap area | SphereProjection and SphereCapMeasure |
| Universal and Diamond Stolarsky identities with ordinary dt | `stolarskyIdentity`, `diamondStolarsky` in CapDiscrepancy |
| Universal cap discrepancy lower bound with constant 1/16 | `beckLowerBound`, `capDiscrepancy_lower_rpow` in CapLowerBound |
| Unconditional optimal cap discrepancy | `cap_corollary` in Corollaries |
| Genuine complete orthonormal harmonic basis exists | `harmonicBasis_nonempty` in HarmonicBasisExistence |
| Exact harmonic addition formula | `harmonic_addition_legendre` in HarmonicAdditionLegendre |
| Spectral Sobolev embedding for s>1 | `sobolevEmbedding_of_harmonicAddition` in SobolevEmbeddingDirect |
| Actual spectral WCE compared to the distance-power deficit | `sobolev_energy_comparison` in Corollaries |
| Unconditional Sobolev cubature bound for 1<s<2 | `sobolev_corollary` in Corollaries |
| Matching universal Sobolev lower bound | `sobolevOptimality` in SobolevMomentSpectral |
| L² coefficient completeness and injectivity | HarmonicL2 |
| Unique continuous representative of every L² Sobolev unit-ball class | `l2Sobolev_continuousRepresentative` in SobolevL2 |
| Intrinsic angular Laplacian on polynomial restrictions | HarmonicLaplacian |
| Exact weak L² eigenspace identification | `weakSphereLaplacian_eigen_iff` in HarmonicL2Laplacian |
| All-L² WCE equality, upper/lower bounds and energy comparison | SobolevL2Corollary |
| All requested results and explicit model identification | `manuscript_targets`, `manuscript_sobolev_model` in Manuscript |
| Literal finite-set energy bound with cardinality N | `diamond_energy_bound` in Manuscript |

## Proof scope and definitions

The latitude proof uses two vanishing moments, a C⁴ mixed Taylor bound,
and an exhaustive comparable/same-side unequal/opposite unequal partition.
The comparable branch handles endpoints, the truncated angular cusp,
intermediate separation, and far separation. Its order-four domination works
through α=1. The longitude bound is uniform in phase and uses generic cusp
quadrature, exact gcd/lcm multiplicities, and arithmetic summation. Separate
phase-uniform bounds close `4≤N<1024`.

The cap observable integrates squared geometric cap error against sphere
probability and ordinary `dt` on `[-1,1]`. Stolarsky has the corresponding
factor 4. Beck's lower bound is proved with constant 1/16 and permits repeated
point labels. Both halves of the Diamond cap corollary are unconditional.

The Sobolev unit ball consists of continuous functions whose genuine harmonic
coefficients satisfy the spectral norm bound with weights
`(1+ℓ(ℓ+1))^s`; summability is explicit. The basis consists of restrictions
of homogeneous harmonic polynomials. Fischer decomposition, dimension,
orthogonality, and polynomial density establish its existence and completeness.
The addition formula supplies uniform spectral reconstruction and embedding.
Legendre moments identify the distance-kernel coefficients, and coefficient
comparison bounds the actual supremum defining worst-case error. A centered
even-moment polynomial gives the universal lower bound. The genuine L² model is now linked to these continuous representatives:
L² coefficient completeness gives uniqueness, and the weighted spectral
series constructs a continuous representative for every unit-ball class at
s>1. The canonical L² supremum includes every such class and equals the
continuous WCE exactly. The intrinsic sphere Laplacian is defined from the
three tangential rotation fields on polynomial restrictions. Its weak L²
eigenspaces are exactly the degree-ℓ harmonic restrictions. This is the
sphere-specific polynomial-core formulation; a separate general-manifold
Laplacian API and maximal self-adjoint domain are outside the claimed scope.

Conditional helper contracts remain useful interfaces; the final results
supply all their needed premises. Some optional scaffold routes are unused:
the explicit Appendix-1 Gamma coefficient contracts and full
`SurfaceIntegration` formula are not required by the final theorem. Their
presence as proposition definitions asserts no additional result. All active
proofs avoid custom axioms and proof shortcuts; `legacy/` is excluded.

## Comparator and metadata

The generated standalone source imports only Mathlib. The previous full
comparator run passed on five selected results from checkpoint `1eb5d8f`
(40 modules), including conditional main/cap assemblies. That historical
check does not certify the final graph. The final 104-module source export,
comparison of unconditional statements, permitted-axiom check, and kernel
replay are being run separately. See [comparator/README.md](comparator/README.md)
for the pinned Lean 4.19 backport and exact verification evidence.

The metadata in `formalization.yaml` records theorem scope, proof techniques,
source divergences, independent agent review, and comparator status. Independent
Sol reviews are mathematical statement/proof reviews, not human peer review.

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
