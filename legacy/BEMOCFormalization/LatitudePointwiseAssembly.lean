import BEMOCFormalization.LatitudePairClassification
import BEMOCFormalization.LatitudeEstimate

/-!
# Assembly of classified latitude block estimates

The geometric priority partition is finer than the two scale regimes used
by the row arithmetic.  This file records the exact logical conversion.
It ensures that no exceptional polar, central, or opposite-hemisphere case
can be lost when the local L5--L6 estimates are packaged as
`HasComparableLatitudeBlockBound` and `HasUnequalLatitudeBlockBound`.
-/

namespace BEMOC

/-- The pointwise weight used by the comparable-scale row summation. -/
noncomputable def comparableLatitudeBlockMajorant
    (α C : ℝ) (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : ℝ :=
  C * (latitudeBandScale N j : ℝ) *
    (bandCount N : ℝ) ^ (-α) *
    (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3)

/-- The pointwise weight used by the ordered unequal-scale row summation. -/
noncomputable def unequalLatitudeBlockMajorant
    (α C : ℝ) (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : ℝ :=
  C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
    (bandCount N : ℝ) ^ (-α) *
    (latitudeBandScale N k : ℝ) ^ (α - 5)

/-- Increasing the numerical constant increases the comparable pointwise
majorant.  This small bookkeeping lemma lets the final case assembly use one
constant even when the individual analytic arguments produce different
ones. -/
theorem comparableLatitudeBlockMajorant_mono
    {α C D : ℝ} {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (hCD : C ≤ D) :
    comparableLatitudeBlockMajorant α C N j k ≤
      comparableLatitudeBlockMajorant α D N j k := by
  unfold comparableLatitudeBlockMajorant
  have hscale :
      0 ≤ (latitudeBandScale N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) *
          (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
    positivity
  nlinarith

/-- Increasing the numerical constant also increases the ordered
unequal-scale majorant. -/
theorem unequalLatitudeBlockMajorant_mono
    {α C D : ℝ} {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (hCD : C ≤ D) :
    unequalLatitudeBlockMajorant α C N j k ≤
      unequalLatitudeBlockMajorant α D N j k := by
  unfold unequalLatitudeBlockMajorant
  have hscale :
      0 ≤ (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
          (bandCount N : ℝ) ^ (-α) *
          (latitudeBandScale N k : ℝ) ^ (α - 5) := by
    positivity
  nlinarith

/-- Monotonicity of the broad comparable block interface. -/
theorem HasComparableLatitudeBlockBound.mono
    {α C D : ℝ} {N : ℕ}
    (h : HasComparableLatitudeBlockBound α N C)
    (hCD : C ≤ D) :
    HasComparableLatitudeBlockBound α N D := by
  intro j k hjk
  exact (h j k hjk).trans
    (comparableLatitudeBlockMajorant_mono hCD)

/-- Monotonicity of the ordered unequal-scale block interface. -/
theorem HasUnequalLatitudeBlockBound.mono
    {α C D : ℝ} {N : ℕ}
    (h : HasUnequalLatitudeBlockBound α N C)
    (hCD : C ≤ D) :
    HasUnequalLatitudeBlockBound α N D := by
  intro j k hjk
  exact (h j k hjk).trans
    (unequalLatitudeBlockMajorant_mono hCD)

/-- Assemble the broad comparable-scale interface from the four geometric
cases which can actually occur under factor-two comparability. -/
theorem hasComparableLatitudeBlockBound_of_geometric_cases
    {α C : ℝ} {N : ℕ}
    (hpolar : ∀ j k, PolarLatitudePair N j k →
      ComparableLatitudeScales N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α C N j k)
    (hcentral : ∀ j k, CentralLatitudePair N j k →
      ComparableLatitudeScales N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α C N j k)
    (hopposite : ∀ j k, SmoothOppositeLatitudePair N j k →
      ComparableLatitudeScales N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α C N j k)
    (hsame : ∀ j k, ComparableSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α C N j k) :
    HasComparableLatitudeBlockBound α N C := by
  intro j k hcomp
  rcases latitudePair_geometric_partition N j k with
    hp | hc | ho | hs | hleft | hright
  · simpa [comparableLatitudeBlockMajorant] using hpolar j k hp hcomp
  · simpa [comparableLatitudeBlockMajorant] using hcentral j k hc hcomp
  · simpa [comparableLatitudeBlockMajorant] using hopposite j k ho hcomp
  · simpa [comparableLatitudeBlockMajorant] using hsame j k hs
  · unfold LeftSmallSameLatitudePair at hleft
    unfold ComparableLatitudeScales at hcomp
    omega
  · unfold RightSmallSameLatitudePair at hright
    unfold ComparableLatitudeScales at hcomp
    omega

/-- Assemble the ordered unequal-scale interface from its polar, central,
opposite, and left-small same-hemisphere cases.  Comparable and reverse
unequal cases are arithmetically impossible under the orientation
`2 d_j < d_k`. -/
theorem hasUnequalLatitudeBlockBound_of_geometric_cases
    {α C : ℝ} {N : ℕ}
    (hpolar : ∀ j k, PolarLatitudePair N j k →
      2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α C N j k)
    (hcentral : ∀ j k, CentralLatitudePair N j k →
      2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α C N j k)
    (hopposite : ∀ j k, SmoothOppositeLatitudePair N j k →
      2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α C N j k)
    (hsame : ∀ j k, LeftSmallSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α C N j k) :
    HasUnequalLatitudeBlockBound α N C := by
  intro j k hscale
  rcases latitudePair_geometric_partition N j k with
    hp | hc | ho | hcomp | hleft | hright
  · simpa [unequalLatitudeBlockMajorant] using hpolar j k hp hscale
  · simpa [unequalLatitudeBlockMajorant] using hcentral j k hc hscale
  · simpa [unequalLatitudeBlockMajorant] using hopposite j k ho hscale
  · unfold ComparableSameLatitudePair at hcomp
    unfold ComparableLatitudeScales at hcomp
    omega
  · simpa [unequalLatitudeBlockMajorant] using hsame j k hleft
  · have hjpos := latitudeBandScale_pos N j
    have hkpos := latitudeBandScale_pos N k
    unfold RightSmallSameLatitudePair at hright
    omega

end BEMOC
