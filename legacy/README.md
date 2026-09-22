# Previous Simpson-based formalization

Recovered verbatim from `joaquimortega/Rieszenergy` at commit
`2348f376b5944bd36343bce8531332bdebf3cd65` (the remote main branch at recovery).
The old construction uses ordinary band populations `4j-1` and a mixture of
midpoint/shared-boundary rings. The new `definitive.tex` uses populations `4j`
and only midpoint rings. Concrete configuration theorems do not transfer.

These sources are **archival reference material** and are not in the current
Lean build. Their original module paths refer to the old source root. To
reproduce that project, use a separate checkout at the above commit rather
than running these files inside the new source root. The old status documents
are historical claims; the current build does not recertify them.

Reuse inventory:

| Material | Old location | Current disposition |
|---|---|---|
| Euclidean parallel parametrization | `BEMOCFormalization/Core.lean`, beginning | Short sphere-membership proof adapted in new `Core.lean` and rechecked |
| Arbitrary ring geometry and finite-energy relabeling | `Core.lean`, first 250 lines | Reuse candidates; independent of Simpson geometry |
| General gcd/lcm fiber counting | `Core.lean`, `GridMultiplicity` namespace | Candidate for new `Trapezoid.GridMultiplicity` |
| Geometric surface measure, height marginal, CND | `Core.lean`, surface probability and negative-type sections | Candidate for `ContinuousEnergy`; requires extraction and rebuild |
| Circle Fourier and endpoint estimates | `CircleFourier.lean`, `CuspFourier.lean`, related modules | Compare normalization and exponent range before reuse |
| Taylor cancellation | `TwoMomentPeano.lean`, `MixedTaylorRemainder.lean` | Generic analytic helpers may transfer after checking hypotheses |
| Concrete populations, latitude blocks, assembled bound | `Core.lean`, `Latitude*.lean`, `MainTheorem.lean` | Configuration-specific; no direct transfer |
| Sharp within-ring asymptotic | `WithinRingLimit.lean` and related files | Outside the new main theorem/corollary proof requirements |

No content from the old main theorem is being asserted for the new points
without a proof bridge. See the current `NOTEBOOK.md` for the reason.
