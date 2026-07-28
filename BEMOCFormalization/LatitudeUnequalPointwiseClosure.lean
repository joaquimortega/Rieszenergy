import BEMOCFormalization.LatitudePolarPointwiseClosure
import BEMOCFormalization.LatitudePointwiseAssembly

/-!
# Final unequal-scale latitude pointwise closure

The polar, central, smooth-opposite, and regular same-hemisphere estimates
are already unconditional.  This module enlarges their four numerical
constants to one common constant and packages them in the broad oriented
unequal-scale interface consumed by the row arithmetic.
-/

namespace BEMOC

/-- A single positive constant dominating all four oriented unequal-scale
geometric estimates. -/
noncomputable def latitudeUnequalGeometricConstant (α : ℝ) : ℝ :=
  1 +
    (1024 * unequalLatitudeDssttConstant α +
      54000 * exceptionalLatitudeDssttConstant α) +
    54000 * exceptionalLatitudeDssttConstant α +
    1024 * exceptionalLatitudeDssttConstant α +
    1024 * unequalLatitudeDssttConstant α

theorem latitudeUnequalGeometricConstant_pos (α : ℝ) :
    0 < latitudeUnequalGeometricConstant α := by
  have hU := unequalLatitudeDssttConstant_nonneg α
  have hE := exceptionalLatitudeDssttConstant_nonneg α
  unfold latitudeUnequalGeometricConstant
  positivity

/-- The complete oriented unequal-scale pointwise estimate, with no
remaining analytic hypotheses. -/
theorem hasUnequalLatitudeBlockBound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 15 ≤ bandCount N) :
    HasUnequalLatitudeBlockBound α N
      (latitudeUnequalGeometricConstant α) := by
  let C := latitudeUnequalGeometricConstant α
  have hU := unequalLatitudeDssttConstant_nonneg α
  have hE := exceptionalLatitudeDssttConstant_nonneg α
  have hpC :
      1024 * unequalLatitudeDssttConstant α +
          54000 * exceptionalLatitudeDssttConstant α ≤ C := by
    dsimp [C, latitudeUnequalGeometricConstant]
    linarith
  have hcC :
      54000 * exceptionalLatitudeDssttConstant α ≤ C := by
    dsimp [C, latitudeUnequalGeometricConstant]
    linarith
  have hoC :
      1024 * exceptionalLatitudeDssttConstant α ≤ C := by
    dsimp [C, latitudeUnequalGeometricConstant]
    linarith
  have hsC :
      1024 * unequalLatitudeDssttConstant α ≤ C := by
    dsimp [C, latitudeUnequalGeometricConstant]
    linarith
  apply hasUnequalLatitudeBlockBound_of_geometric_cases
  · intro j k hp hscale
    exact (polar_leftSmall_unequal_bound_series
      hα0 hα2 hM j k hp hscale).trans
        (unequalLatitudeBlockMajorant_mono hpC)
  · intro j k hc hscale
    exact (central_leftSmall_unequal_bound_series
      hα0 hα2 hM j k hc hscale).trans
        (unequalLatitudeBlockMajorant_mono hcC)
  · intro j k ho hscale
    exact (smoothOpposite_leftSmall_unequal_bound_series
      hα0 hα2 (by omega) j k ho hscale).trans
        (unequalLatitudeBlockMajorant_mono hoC)
  · intro j k hs
    exact (leftSmallSame_block_bound_series
      hα0 hα2 (by omega) j k hs).trans
        (unequalLatitudeBlockMajorant_mono hsC)

end BEMOC
