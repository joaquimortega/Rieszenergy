# Independent Sol reviews

The initial scaffold modules were assigned to reviewers explicitly selected
as **gpt-6-sol**, independently of the main scaffold author. These are
mathematical/interface reviews, not completed Lean proofs or human peer review.

| Review | Modules |
|---|---|
| [Foundations](foundations-review.md) | Core, Construction, Geometry, ContinuousEnergy, EnergyDecomposition, MainTheorem |
| [Longitude](longitude-review.md) | FourierDecay, Trapezoid, Longitude |
| [Latitude blocks](blocks-review.md) | BandErrors, Taylor, KernelDerivatives, ComparableBlocks, UnequalBlocks, Latitude |
| [Corollaries](corollaries-review.md) | CapDiscrepancy, Sobolev, Corollaries |

The proof guides incorporate the review findings. No reviewer was asked to
approve a replacement of the actual cap/Sobolev observable by an energy-based
surrogate. The open contracts, source notation corrections, finite-size
uniformity, pole/cusp issues and classical lower bounds remain explicit.

Resolution log:

- New r_j=4j midpoint construction kept separate from legacy Simpson rings.
- Ordered pairs, arbitrary phases, N≥4 and the analytic cutoff N≥1024 retained.
- Swapped latitude integration variables corrected in the formal definitions.
- Signed functionals implemented with ordinary integrals; integrability remains a proof obligation.
- Pointwise separated extensions require a rectangle-level extension/gluing lemma before mixed Taylor.
- Sobolev series includes a summability guard; existence of the harmonic basis is in the final target.
- Stolarsky uses unnormalized dt and factor 4; spectral norm comparison is not assigned constant 1.
- Compilation and source audits are reported as such, without claiming the open propositions proved.

Reviews describe the scaffold at their initial inspection. Later proof changes
must receive appropriate Lean checks and, where their statements change,
follow-up review recorded here.

A subsequent [proof-checkpoint alignment review](proof-checkpoint-review.md)
independently checked the 32-module proof checkpoint. It found no concrete
normalization mismatch and confirmed the documented boundary between checked
foundations and the unfinished unconditional main theorem and corollaries.

The [cap lower-bound review](cap-lower-bound-review.md) checks the actual
discrepancy definition, ordered-pair convention, endpoint limit and constant
1/16 in Beck's lower bound, together with the reduced corollary assembly.

The [angular and scalar-series review](angular-series-review.md) checks
AngularDistance, SeparatedKernel, and ScalarPowerSeries, including closed
height endpoints and the open convergence interval for scalar derivatives.

The [separated and unequal-block review](separated-unequal-review.md) checks
the global extension, mixed derivative identification, polar boundary passage,
and exact same-side/opposite block contracts, including the central band.


The [final main-theorem review](final-main-theorem-review.md) checks the
construction, ordered-pair normalization, phase uniformity, exhaustive
latitude cases, and small-size closure. Its remaining wrapper integration
was subsequently completed and the later 104-module dependency graph built.

The [final Sobolev review](final-sobolev-review.md) confirms the unconditional
continuous spectral WCE upper/lower estimates and exact normalization. It
initially identified a formal link needed for the manuscript’s L² and
Laplace–Beltrami presentation. The follow-up review confirms that the
representative, canonical all-L² WCE, and intrinsic weak eigenspace theorems
close it. The Laplacian is the sphere-specific angular operator on a
polynomial test core; no separate general-manifold API is claimed.

The [standalone exporter hygiene review](export-hygiene-review.md) checks the
per-module elaboration identity, private-name rewriting, auxiliary cache
reset, scoped command state, and final identity restoration. It is a static
review; the strict eight-theorem comparator result remains a separate check.
