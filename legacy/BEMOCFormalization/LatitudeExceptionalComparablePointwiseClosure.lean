import BEMOCFormalization.LatitudeGenericSharpComparableClosure

/-!
# Exceptional comparable pointwise closure

The classifier-free sharp four-term estimate is now available on both
exceptional off-diagonal geometries.  This module inserts it into the
central and smooth-opposite block reducers, leaving only the genuinely
diagonal central input to the neighboring analysis.
-/

namespace BEMOC

noncomputable def exceptionalComparableSharpConstant (α : ℝ) : ℝ :=
  comparableDerivativeScaleConversionConstant α *
    latitudeComparableMixedConstant α

theorem exceptionalComparableSharpConstant_nonneg (α : ℝ) :
    0 ≤ exceptionalComparableSharpConstant α := by
  unfold exceptionalComparableSharpConstant
    comparableDerivativeScaleConversionConstant
  exact mul_nonneg (by positivity)
    (latitudeComparableMixedConstant_nonneg α)

/-- The smooth-opposite comparable field is now fully unconditional. -/
theorem hasSmoothOppositeComparableLatitudeBlockBound_generic
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N) :
    HasSmoothOppositeComparableLatitudeBlockBound α N
      (65536 * exceptionalLatitudeDssttConstant α +
        8192 * exceptionalComparableSharpConstant α) := by
  exact
    hasSmoothOppositeComparableLatitudeBlockBound_of_nearEquatorDsstt
      hα0 hα2 hM
      (exceptionalComparableSharpConstant_nonneg α)
      (by
        simpa [exceptionalComparableSharpConstant] using
          hasSmoothOppositeComparableNearEquatorDssttBound_generic
            hα0 hα2 hM)

/-- A central neighboring estimate plus the unconditional generic sharp
off-diagonal estimate gives the complete central comparable field. -/
theorem hasCentralComparableLatitudeBlockBound_of_neighboring
    {α A : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N) (hA : 0 ≤ A)
    (hneighbor :
      ∀ j k, CentralLatitudePair N j k →
        ComparableLatitudeScales N j k →
        Nat.dist (j : ℕ) (k : ℕ) ≤ 1 →
        |bandPairError N j k (latitudeKernel α)| ≤
          comparableLatitudeBlockMajorant α A N j k) :
    HasCentralComparableLatitudeBlockBound α N
      (A + (15 : ℝ) ^ 6 / 2 *
        exceptionalComparableSharpConstant α) := by
  exact centralComparable_block_bound_of_neighboring_and_analytic
    hα0 hA (exceptionalComparableSharpConstant_nonneg α)
    (by omega) hneighbor
    (by
      simpa [exceptionalComparableSharpConstant] using
        hasCentralComparableSeparatedDssttBound_generic
          hα0 hα2 (by omega))

end BEMOC
