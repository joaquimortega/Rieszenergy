import BEMOCFormalization.Corollaries
import BEMOCFormalization.Manuscript
import BEMOCFormalization.NegativeType
import BEMOCFormalization.AngularQuadrature
import BEMOCFormalization.AngularGeometry
import BEMOCFormalization.AngularDistance
import BEMOCFormalization.ScalarPowerSeries
import BEMOCFormalization.SphereProjection
import BEMOCFormalization.GridMultiplicity
import BEMOCFormalization.LatitudePotential
import BEMOCFormalization.LatitudeIdentity
import BEMOCFormalization.SobolevBasic
import BEMOCFormalization.SphereCapMeasure

/-!
# Deterministic Diamond points: definitive.tex formalization

Every active module is imported transitively here.
`BEMOC.Definitive.manuscript_targets` proves the main energy bound, spherical
cap discrepancy corollary, and genuine L² Sobolev cubature corollary with
universal optimality. `manuscript_sobolev_model` supplies continuous
representatives and identifies the intrinsic weak Laplacian eigenspaces.
`diamond_energy_bound` exposes the finite-set formula and exact cardinality.
See LEAN_FORMALIZATION.md and blueprint/README.md for verification scope.
-/
