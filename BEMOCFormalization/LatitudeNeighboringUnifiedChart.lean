import BEMOCFormalization.LatitudeCentralNeighboringBlocks

/-!
# Unified all-depth neighboring chart split

Combining the regular polar-scale chart with the equatorial central chart
leaves only the already-closed finite-depth regular case.
-/

open Set

namespace BEMOC

/-- Every nonpolar comparable neighboring rectangle is either in the unit
reduced-cusp chart, or is a regular same-hemisphere rectangle below the
fixed finite-depth threshold handled by
`abs_bandPairError_neighboringComparable_smallDepth`. -/
theorem nonpolar_comparable_neighboring_chart_or_smallRegular
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hnpolar : ¬ PolarLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    normalizedLatitudeGap s t ≤ 1 ∨
      (NeighboringComparableLatitudePair N j k ∧
        latitudeBandScale N j < 600) := by
  rcases nonpolar_comparable_neighboring_central_or_regular
    hnpolar hcomp hneigh with hcentral | hregular
  · exact Or.inl
      (centralComparable_neighboring_rectangle_normalizedLatitudeGap_le_one
        hM hcentral hcomp hneigh hs ht)
  · by_cases hdepth : 600 ≤ latitudeBandScale N j
    · exact Or.inl
        (neighboringComparable_rectangle_normalizedLatitudeGap_le_one
          (by omega : 1 ≤ bandCount N) hregular hdepth hs ht)
    · exact Or.inr ⟨hregular, by omega⟩

/-- Consequently, in the only branch not covered by the unit cusp chart,
the actual full-kernel finite-depth estimate is immediately available. -/
theorem nonpolar_comparable_neighboring_chart_or_fullKernelBound
    {α : ℝ} (hα : 0 ≤ α)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hnpolar : ¬ PolarLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    (∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          normalizedLatitudeGap s t ≤ 1) ∨
      |bandPairError N j k (latitudeKernel α)| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (8 * ((1200 : ℝ) * (2 * 1200 + 1) /
              (2 * (bandCount N : ℝ) ^ 2))) ^ (α / 2) := by
  rcases nonpolar_comparable_neighboring_central_or_regular
    hnpolar hcomp hneigh with hcentral | hregular
  · left
    intro s hs t ht
    exact
      centralComparable_neighboring_rectangle_normalizedLatitudeGap_le_one
        hM hcentral hcomp hneigh hs ht
  · by_cases hdepth : 600 ≤ latitudeBandScale N j
    · left
      intro s hs t ht
      exact neighboringComparable_rectangle_normalizedLatitudeGap_le_one
        (by omega : 1 ≤ bandCount N) hregular hdepth hs ht
    · right
      exact abs_bandPairError_neighboringComparable_smallDepth hα
        (by omega : 1 ≤ bandCount N) j k hregular (by omega)

end BEMOC
