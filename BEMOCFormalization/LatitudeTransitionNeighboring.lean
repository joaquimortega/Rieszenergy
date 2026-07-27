import BEMOCFormalization.LatitudeNeighboringSmoothTaylor
import BEMOCFormalization.LatitudeCentralGeometry

/-!
# The comparable neighboring transition

This file closes a small but important classification gap: an
opposite-hemisphere pair cannot have neighboring band indices because the
unique central band lies strictly between the northern and southern bands.
Thus a comparable pair at index distance at most one is necessarily polar,
central, or one of the regular same-hemisphere neighboring pairs.
-/

namespace BEMOC

/-- The central index separates every noncentral opposite-hemisphere pair
by at least two index steps. -/
theorem smoothOppositeLatitudePair_two_le_natDist
    {N : ℕ} {j k : Fin (bandTailCount N + 1)}
    (hjk : SmoothOppositeLatitudePair N j k) :
    2 ≤ Nat.dist (j : ℕ) (k : ℕ) := by
  rcases hjk.2.2 with hNS | hSN
  · unfold IsNorthernLatitudeBand IsSouthernLatitudeBand at hNS
    rw [Nat.dist_eq_sub_of_le (by omega : (j : ℕ) ≤ (k : ℕ))]
    omega
  · unfold IsNorthernLatitudeBand IsSouthernLatitudeBand at hSN
    rw [Nat.dist_comm,
      Nat.dist_eq_sub_of_le (by omega : (k : ℕ) ≤ (j : ℕ))]
    omega

theorem not_smoothOppositeLatitudePair_of_neighboring
    {N : ℕ} {j k : Fin (bandTailCount N + 1)}
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    ¬ SmoothOppositeLatitudePair N j k := by
  intro hjk
  have := smoothOppositeLatitudePair_two_le_natDist hjk
  omega

/-- Exact routing theorem for every factor-two comparable pair whose
indices differ by at most one.  In particular, there is no additional
smooth-opposite transition case hidden between the central and regular
same-hemisphere predicates. -/
theorem comparable_neighboring_geometric_partition
    (N : ℕ) (j k : Fin (bandTailCount N + 1))
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    PolarLatitudePair N j k ∨
      CentralLatitudePair N j k ∨
      NeighboringComparableLatitudePair N j k := by
  rcases latitudePair_geometric_partition N j k with
    hp | hc | ho | hs | hleft | hright
  · exact Or.inl hp
  · exact Or.inr (Or.inl hc)
  · exact (not_smoothOppositeLatitudePair_of_neighboring hneigh ho).elim
  · exact Or.inr (Or.inr ⟨hs, hneigh⟩)
  · unfold LeftSmallSameLatitudePair ComparableLatitudeScales at *
    omega
  · unfold RightSmallSameLatitudePair ComparableLatitudeScales at *
    omega

/-- Away from the already-prioritized polar exception, a neighboring
comparable pair is exactly central or regular same-hemisphere. -/
theorem nonpolar_comparable_neighboring_central_or_regular
    {N : ℕ} {j k : Fin (bandTailCount N + 1)}
    (hnpolar : ¬ PolarLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    CentralLatitudePair N j k ∨
      NeighboringComparableLatitudePair N j k := by
  rcases comparable_neighboring_geometric_partition N j k hcomp hneigh with
    hp | hc | hs
  · exact (hnpolar hp).elim
  · exact Or.inl hc
  · exact Or.inr hs

end BEMOC
