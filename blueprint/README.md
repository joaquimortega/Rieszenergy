# Proof blueprint for `definitive.tex`

The canonical Lean entry point is [`BEMOCFormalization.lean`](../BEMOCFormalization.lean). Its transitive import graph now contains all **104 modules**, each with a proof guide and embedded Lean source. The manuscript [`definitive.tex`](../definitive.tex) is the mathematical reference; [`LEAN_FORMALIZATION.md`](../LEAN_FORMALIZATION.md) records the verification boundary.

The final theorem chain is unconditional in the source: `comparable_block_bound`, `sameSideBlockBound`, and `oppositeBlockBound` feed `latitude_bound_of_blocks`; with `longitude_bound`, `small_size_bound`, and `diamond_nonnegative`, these give `main_theorem` for every `N ≥ 4`, every ring-phase choice, and each `0 < α < 2`. `main_theorem_target` packages all such exponents. The separate cap and Sobolev chains then give `cap_corollary`, `sobolev_corollary`, and `definitive_targets`. The 104-module full build and final strict comparator check pass. Those checks are separate from the presence of the theorem proofs.

For cap discrepancy, `stolarsky_identity` converts the α=1 energy deficit to the actual cap observable, and `beckLowerBound` proves its universal lower bound. For Sobolev cubature, `angular_integral_zero` and the Casimir identity prove cross-degree orthogonality; Fischer decomposition and finite-dimensional orthonormalization produce `harmonicBasis_nonempty`. The zonal/addition and distance-coefficient chains prove `harmonic_addition_legendre`, `sobolev_energy_comparison`, the continuous embedding, and `sobolevOptimality`. The original continuous-function `sobolev_corollary` covers `1 < s < 2`. The new `HarmonicL2` and `SobolevL2` modules extend harmonic coefficients to actual `Lp ℝ 2 sigma` classes and construct a unique continuous representative in the Sobolev class. `SobolevL2Corollary` transfers cubature error, the energy comparison, and optimality to the canonical L² worst-case error. `HarmonicLaplacian` and `HarmonicL2Laplacian` define the intrinsic angular Laplacian on polynomial sphere restrictions and its weak L² graph, then identify its eigenspaces exactly with homogeneous harmonic restrictions. `manuscript_sobolev_model` packages that eigenbridge with uniqueness of L² Sobolev representatives. This is a polynomial-core statement; it does not assert an unrelated manifold-level Laplace–Beltrami API.

`SurfaceIntegration` in `ContinuousEnergy` and the `FourierDomination`, `CuspCoefficientFormula` (Gamma), and `FourierDecayBound` propositions in `FourierDecay` are optional interface contracts. They are not premises of `main_theorem`, either corollary, or `definitive_targets`; their definitions should not be mistaken for proved final targets. The operative angular estimates are proved in the `Angular/*`, `AngularQuadrature`, `Trapezoid`, and `Longitude` modules.

## Complete module inventory

Each link opens the module’s proof guide. A module’s role in the chain is summarized beside its group.

### Geometry, measures, and construction (14)

Defines the midpoint-only Diamond configuration, exact band geometry, normalized surface measure, projection and cap measures, constant potential, and nonnegative energy deficit.

| Module guide | Module guide | Module guide |
|---|---|---|
| [Core](modules/Core.md) | [Construction](modules/Construction.md) | [Geometry](modules/Geometry.md) |
| [AngularGeometry](modules/AngularGeometry.md) | [AngularDistance](modules/AngularDistance.md) | [PlaneRotation](modules/PlaneRotation.md) |
| [SurfaceMeasure](modules/SurfaceMeasure.md) | [NegativeType](modules/NegativeType.md) | [ContinuousEnergy](modules/ContinuousEnergy.md) |
| [EnergyDecomposition](modules/EnergyDecomposition.md) | [LatitudePotential](modules/LatitudePotential.md) | [SphereProjection](modules/SphereProjection.md) |
| [SphereCapMeasure](modules/SphereCapMeasure.md) | [GridMultiplicity](modules/GridMultiplicity.md) |  |

### Angular quadrature and longitude (9)

Builds the circle Fourier and shifted trapezoid estimates, finite grid multiplicities, and the phase-uniform `longitude_bound`.

| Module guide | Module guide | Module guide |
|---|---|---|
| [Angular/CircleFourier](modules/Angular/CircleFourier.md) | [Angular/CuspFourier](modules/Angular/CuspFourier.md) | [Angular/CuspSmoothing](modules/Angular/CuspSmoothing.md) |
| [Angular/CuspTrapezoid](modules/Angular/CuspTrapezoid.md) | [Angular/Schoenberg](modules/Angular/Schoenberg.md) | [AngularQuadrature](modules/AngularQuadrature.md) |
| [FourierDecay](modules/FourierDecay.md) | [Trapezoid](modules/Trapezoid.md) | [Longitude](modules/Longitude.md) |

### Latitude and unequal blocks (22)

Establishes the exact signed latitude decomposition, fourth-order quadrature cancellation, separated-kernel derivatives, both unequal regimes, and finite block summation.

| Module guide | Module guide | Module guide |
|---|---|---|
| [BandErrors](modules/BandErrors.md) | [LatitudeIdentity](modules/LatitudeIdentity.md) | [Taylor](modules/Taylor.md) |
| [KernelDerivatives](modules/KernelDerivatives.md) | [PolarDerivatives](modules/PolarDerivatives.md) | [ScalarPowerSeries](modules/ScalarPowerSeries.md) |
| [SeparatedAngularExpansion](modules/SeparatedAngularExpansion.md) | [SeparatedBinomialSeries](modules/SeparatedBinomialSeries.md) | [SeparatedBoundaryTransfer](modules/SeparatedBoundaryTransfer.md) |
| [SeparatedComplete](modules/SeparatedComplete.md) | [SeparatedKernel](modules/SeparatedKernel.md) | [SeparatedLocalRectangle](modules/SeparatedLocalRectangle.md) |
| [SeparatedMixedFourth](modules/SeparatedMixedFourth.md) | [SeparatedSeriesBounds](modules/SeparatedSeriesBounds.md) | [SeparatedSeriesDifferentiation](modules/SeparatedSeriesDifferentiation.md) |
| [SeparatedSeriesSum](modules/SeparatedSeriesSum.md) | [SeparatedSmoothExtension](modules/SeparatedSmoothExtension.md) | [SeparatedSummandDerivatives](modules/SeparatedSummandDerivatives.md) |
| [UnequalBlockEstimates](modules/UnequalBlockEstimates.md) | [UnequalBlocks](modules/UnequalBlocks.md) | [Latitude](modules/Latitude.md) |
| [LatitudeSummation](modules/LatitudeSummation.md) |  |  |

### Comparable blocks (17)

Closes endpoint, near, intermediate, and far comparable rectangles; `comparable_block_bound` combines them for every `0 < α < 2`.

| Module guide | Module guide | Module guide |
|---|---|---|
| [AngularPowerIntegrals](modules/AngularPowerIntegrals.md) | [NearTailIntegralCalculus](modules/NearTailIntegralCalculus.md) | [ComparableAssembly](modules/ComparableAssembly.md) |
| [ComparableBlockEstimates](modules/ComparableBlockEstimates.md) | [ComparableBlocks](modules/ComparableBlocks.md) | [ComparableEndpointAssembly](modules/ComparableEndpointAssembly.md) |
| [ComparableHeightChainBounds](modules/ComparableHeightChainBounds.md) | [ComparableIntermediateBlocks](modules/ComparableIntermediateBlocks.md) | [ComparableIntermediateClosure](modules/ComparableIntermediateClosure.md) |
| [ComparableIntermediateIntegrability](modules/ComparableIntermediateIntegrability.md) | [ComparableIntermediateIntegralBound](modules/ComparableIntermediateIntegralBound.md) | [ComparableIntermediateScaling](modules/ComparableIntermediateScaling.md) |
| [ComparableNearBlocks](modules/ComparableNearBlocks.md) | [ComparableNearTailClosure](modules/ComparableNearTailClosure.md) | [ComparableNearTailScaling](modules/ComparableNearTailScaling.md) |
| [ComparablePowerScaling](modules/ComparablePowerScaling.md) | [ComparableSeparatedBlocks](modules/ComparableSeparatedBlocks.md) |  |

### Cap discrepancy (3)

Formalizes the actual cap observable, Stolarsky identity, and Beck lower bound.

| Module guide | Module guide | Module guide |
|---|---|---|
| [BinomialTail](modules/BinomialTail.md) | [CapDiscrepancy](modules/CapDiscrepancy.md) | [CapLowerBound](modules/CapLowerBound.md) |

### Harmonic basis and addition formula (18)

Proves finite-dimensional harmonic algebra, rotation-based cross-degree orthogonality, full-support L² inner products, basis existence, and the all-degree addition formula.

| Module guide | Module guide | Module guide |
|---|---|---|
| [AngularIntegralZero](modules/AngularIntegralZero.md) | [FischerDecomposition](modules/FischerDecomposition.md) | [HarmonicAddition](modules/HarmonicAddition.md) |
| [HarmonicAdditionLegendre](modules/HarmonicAdditionLegendre.md) | [HarmonicBasis](modules/HarmonicBasis.md) | [HarmonicBasisAssembly](modules/HarmonicBasisAssembly.md) |
| [HarmonicBasisExistence](modules/HarmonicBasisExistence.md) | [HarmonicCasimir](modules/HarmonicCasimir.md) | [HarmonicDimension](modules/HarmonicDimension.md) |
| [HarmonicFiniteSpan](modules/HarmonicFiniteSpan.md) | [HarmonicMonomialCount](modules/HarmonicMonomialCount.md) | [HarmonicOrthogonality](modules/HarmonicOrthogonality.md) |
| [HarmonicOrthonormal](modules/HarmonicOrthonormal.md) | [HarmonicPullback](modules/HarmonicPullback.md) | [HarmonicRadialDifferentiation](modules/HarmonicRadialDifferentiation.md) |
| [HarmonicZonal](modules/HarmonicZonal.md) | [SphereSupport](modules/SphereSupport.md) | [ZonalPolynomials](modules/ZonalPolynomials.md) |

### Distance kernel and Sobolev theory (12)

Identifies the Legendre coefficients of the chordal kernel, proves the spectral energy comparison and embedding, and supplies the universal optimality test.

| Module guide | Module guide | Module guide |
|---|---|---|
| [DistanceKernelExpansion](modules/DistanceKernelExpansion.md) | [DistanceScalarBridge](modules/DistanceScalarBridge.md) | [DistanceScalarUniqueness](modules/DistanceScalarUniqueness.md) |
| [DistanceZonal](modules/DistanceZonal.md) | [DistanceZonalCoefficients](modules/DistanceZonalCoefficients.md) | [Sobolev](modules/Sobolev.md) |
| [SobolevBasic](modules/SobolevBasic.md) | [SobolevEmbeddingDirect](modules/SobolevEmbeddingDirect.md) | [SobolevKernel](modules/SobolevKernel.md) |
| [SobolevLowerBound](modules/SobolevLowerBound.md) | [SobolevMomentAction](modules/SobolevMomentAction.md) | [SobolevMomentSpectral](modules/SobolevMomentSpectral.md) |

### Final statements (2)

Assembles the unconditional phase-uniform energy theorem, both corollaries, and `definitive_targets`.

| Module guide | Module guide | Module guide |
|---|---|---|
| [MainTheorem](modules/MainTheorem.md) | [Corollaries](modules/Corollaries.md) |  |

### L² completion and manuscript endpoint (7)

Extends the harmonic system to actual L² classes, identifies continuous representatives of the Sobolev unit ball, proves the canonical L² worst-case-error and optimality statements, and formalizes the intrinsic polynomial-core angular Laplacian and its exact weak eigenspaces. `Manuscript` contains the aggregate `manuscript_targets`, model bridge `manuscript_sobolev_model`, and raw finite-set `diamond_energy_bound`.

| Module guide | Module guide | Module guide |
|---|---|---|
| [HarmonicL2](modules/HarmonicL2.md) | [SobolevL2](modules/SobolevL2.md) | [SobolevL2Corollary](modules/SobolevL2Corollary.md) |
| [HarmonicLaplacian](modules/HarmonicLaplacian.md) | [HarmonicL2Laplacian](modules/HarmonicL2Laplacian.md) | [Manuscript](modules/Manuscript.md) |
| [HarmonicLaplacianEigenspace](modules/HarmonicLaplacianEigenspace.md) | | |

The final 104-module build and standalone comparator check pass; see the [verification record](../comparator/final-verification.md).

The import graph is acyclic, but imports alone do not prove an analytic contract. The named theorems above are the proof-producing links. Guides contain exact statements and proof bodies; use `python scripts/sync_blueprint.py --check` to detect stale embedded source.
