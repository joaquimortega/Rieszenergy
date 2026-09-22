import BEMOCFormalization.LatitudeExceptionalGeometry
import BEMOCFormalization.LatitudeUnequalSeriesClosure

/-!
# Even-series closure for exceptional unequal latitude rectangles

Central/half-depth and smooth opposite-hemisphere unequal rectangles both
have the fixed geometry

`angularKernelA ≥ 1/4`, `unequalAngularRatio ≤ 15/16`.

The generalized four-pass even-series theorem therefore gives a uniform
mixed `(2,2)` derivative bound on both classes, including band endpoints.
The mixed-Peano bridges in `LatitudeExceptionalGeometry` then give the
literal broad unequal-block majorants.
-/

open Set

namespace BEMOC

theorem central_leftSmall_evenPowerSeriesRectangleGeometry
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hc : CentralLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k) :
    LatitudeEvenPowerSeriesRectangleGeometry N j k ((1 : ℝ) / 4) where
  base_pos := by norm_num
  base_le s hs t ht :=
    (centralPair_leftSmall_series_geometry hM hc hscale hs ht).1
  ratio_le s hs t ht :=
    (centralPair_leftSmall_series_geometry hM hc hscale hs ht).2
  interior_offDiagonal s hs t ht :=
    central_leftSmall_rectangle_interior_offDiagonal
      hM hc hscale hs ht

theorem smoothOpposite_leftSmall_evenPowerSeriesRectangleGeometry
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (ho : SmoothOppositeLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k) :
    LatitudeEvenPowerSeriesRectangleGeometry N j k ((1 : ℝ) / 4) where
  base_pos := by norm_num
  base_le s hs t ht :=
    (smoothOppositePair_leftSmall_series_geometry
      hN hM ho hscale hs ht).1
  ratio_le s hs t ht :=
    (smoothOppositePair_leftSmall_series_geometry
      hN hM ho hscale hs ht).2
  interior_offDiagonal s hs t ht :=
    smoothOpposite_leftSmall_rectangle_interior_offDiagonal
      hN hM ho hscale hs ht

/-- Uniform constant furnished by the normally convergent DSSTT series on
every exceptional fixed-gap rectangle. -/
noncomputable def exceptionalLatitudeDssttConstant (α : ℝ) : ℝ :=
  unequalLatitudeDssttSeriesConstant α *
    ((1 : ℝ) / 4) ^ (α / 2 - 4)

theorem exceptionalLatitudeDssttConstant_nonneg (α : ℝ) :
    0 ≤ exceptionalLatitudeDssttConstant α := by
  unfold exceptionalLatitudeDssttConstant
  exact mul_nonneg (unequalLatitudeDssttSeriesConstant_nonneg α)
    (Real.rpow_nonneg (by norm_num) _)

/-- Unconditional uniform mixed derivative estimate on oriented central
unequal rectangles. -/
theorem hasCentralLeftSmallDssttBound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 15 ≤ bandCount N) :
    HasCentralLeftSmallDssttBound α N
      (exceptionalLatitudeDssttConstant α) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  intro j k hc hscale s hs t ht
  exact abs_variableReducedLatitudeKernelDsstt_le_series_scale
    hα0 hα2 hN (by omega)
    (central_leftSmall_evenPowerSeriesRectangleGeometry
      hM hc hscale) hs ht

/-- Unconditional uniform mixed derivative estimate on oriented smooth
opposite-hemisphere unequal rectangles. -/
theorem hasSmoothOppositeLeftSmallDssttBound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    HasSmoothOppositeLeftSmallDssttBound α N
      (exceptionalLatitudeDssttConstant α) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  intro j k ho hscale s hs t ht
  exact abs_variableReducedLatitudeKernelDsstt_le_series_scale
    hα0 hα2 hN hM
    (smoothOpposite_leftSmall_evenPowerSeriesRectangleGeometry
      hN (by omega) ho hscale) hs ht

/-- Final unconditional central unequal-block majorant. -/
theorem central_leftSmall_unequal_bound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 15 ≤ bandCount N) :
    ∀ j k, CentralLatitudePair N j k →
      2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α
          (54000 * exceptionalLatitudeDssttConstant α) N j k := by
  exact central_leftSmall_unequal_bound_of_Dsstt
    hM hα0 (exceptionalLatitudeDssttConstant_nonneg α)
    (hasCentralLeftSmallDssttBound_series hα0 hα2 hM)

/-- Final unconditional smooth-opposite unequal-block majorant. -/
theorem smoothOpposite_leftSmall_unequal_bound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    ∀ j k, SmoothOppositeLatitudePair N j k →
      2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α
          (1024 * exceptionalLatitudeDssttConstant α) N j k := by
  exact smoothOpposite_leftSmall_unequal_bound_of_Dsstt
    (by omega) hα0 hα2 (exceptionalLatitudeDssttConstant_nonneg α)
    (hasSmoothOppositeLeftSmallDssttBound_series hα0 hα2 hM)

end BEMOC
