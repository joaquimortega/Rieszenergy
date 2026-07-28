import BEMOCFormalization.LatitudeComparableFourTermClosure
import BEMOCFormalization.LatitudeDiagonalBandBridge
import BEMOCFormalization.LatitudePolarPointwiseClosure

/-!
# Comparable latitude pointwise assembly

The polar and separated regular comparable cases are unconditional.  This
module isolates the three genuinely remaining fields—neighboring regular,
central, and smooth opposite—and performs all constant enlargement and
geometric routing around them.
-/

namespace BEMOC

private theorem comparableDerivativeScaleConversionConstant_nonneg
    (α : ℝ) :
    0 ≤ comparableDerivativeScaleConversionConstant α := by
  unfold comparableDerivativeScaleConversionConstant
  positivity

/-- Pointwise neighboring regular comparable estimate at one fixed `N`. -/
def HasNeighboringComparableLatitudeBlockBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k, NeighboringComparableLatitudePair N j k →
    |bandPairError N j k (latitudeKernel α)| ≤
      comparableLatitudeBlockMajorant α C N j k

/-- Pointwise central comparable estimate at one fixed `N`. -/
def HasCentralComparableLatitudeBlockBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k, CentralLatitudePair N j k →
    ComparableLatitudeScales N j k →
    |bandPairError N j k (latitudeKernel α)| ≤
      comparableLatitudeBlockMajorant α C N j k

/-- Pointwise smooth opposite-hemisphere comparable estimate at one fixed
`N`. -/
def HasSmoothOppositeComparableLatitudeBlockBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k, SmoothOppositeLatitudePair N j k →
    ComparableLatitudeScales N j k →
    |bandPairError N j k (latitudeKernel α)| ≤
      comparableLatitudeBlockMajorant α C N j k

/-- The already-closed separated estimate and a neighboring estimate give
the complete regular same-hemisphere comparable field. -/
theorem comparableSame_block_bound_of_neighboring
    {α C : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N) (hC : 0 ≤ C)
    (hneighbor : HasNeighboringComparableLatitudeBlockBound α N C) :
    ∀ j k, ComparableSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α
          (C + 8192 * (comparableDerivativeScaleConversionConstant α *
            latitudeComparableMixedConstant α)) N j k := by
  intro j k hjk
  by_cases hdist : Nat.dist (j : ℕ) (k : ℕ) ≤ 1
  · exact (hneighbor j k ⟨hjk, hdist⟩).trans
      (comparableLatitudeBlockMajorant_mono (by
        have hsepC : 0 ≤
            8192 * (comparableDerivativeScaleConversionConstant α *
              latitudeComparableMixedConstant α) := by
          unfold comparableDerivativeScaleConversionConstant
          exact mul_nonneg (by norm_num)
            (mul_nonneg (by positivity)
              (latitudeComparableMixedConstant_nonneg α))
        linarith))
  · have hsep : SeparatedComparableSameLatitudePair N j k :=
      ⟨hjk, by omega⟩
    exact (separatedComparableSame_block_bound
      hα0 hα2 hM j k hsep).trans
        (comparableLatitudeBlockMajorant_mono (by linarith))

/-- One common constant for the unconditional polar and separated fields
and the three supplied remaining comparable fields. -/
noncomputable def latitudeComparableGeometricConstant
    (α Cneighbor Ccentral Copposite : ℝ) : ℝ :=
  1 +
    (32768 * 144 ^ (α / 2) +
      8388608 * exceptionalLatitudeDssttConstant α) +
    Cneighbor +
    8192 * (comparableDerivativeScaleConversionConstant α *
      latitudeComparableMixedConstant α) +
    Ccentral + Copposite

theorem latitudeComparableGeometricConstant_pos
    {α Cneighbor Ccentral Copposite : ℝ}
    (hn : 0 ≤ Cneighbor) (hc : 0 ≤ Ccentral)
    (ho : 0 ≤ Copposite) :
    0 < latitudeComparableGeometricConstant
      α Cneighbor Ccentral Copposite := by
  have hE := exceptionalLatitudeDssttConstant_nonneg α
  have hmix := latitudeComparableMixedConstant_nonneg α
  unfold latitudeComparableGeometricConstant
    comparableDerivativeScaleConversionConstant
  positivity

/-- Final comparable routing theorem.  Only the neighboring, central, and
smooth-opposite fields remain as arguments. -/
theorem hasComparableLatitudeBlockBound_of_remaining_cases
    {α Cneighbor Ccentral Copposite : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 15 ≤ bandCount N)
    (hn0 : 0 ≤ Cneighbor) (hc0 : 0 ≤ Ccentral)
    (ho0 : 0 ≤ Copposite)
    (hneighbor :
      HasNeighboringComparableLatitudeBlockBound α N Cneighbor)
    (hcentral :
      HasCentralComparableLatitudeBlockBound α N Ccentral)
    (hopposite :
      HasSmoothOppositeComparableLatitudeBlockBound α N Copposite) :
    HasComparableLatitudeBlockBound α N
      (latitudeComparableGeometricConstant
        α Cneighbor Ccentral Copposite) := by
  let C :=
    latitudeComparableGeometricConstant
      α Cneighbor Ccentral Copposite
  have hpC :
      32768 * 144 ^ (α / 2) +
          8388608 * exceptionalLatitudeDssttConstant α ≤ C := by
    dsimp [C, latitudeComparableGeometricConstant]
    have hsep : 0 ≤
        8192 * (comparableDerivativeScaleConversionConstant α *
          latitudeComparableMixedConstant α) := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg
          (comparableDerivativeScaleConversionConstant_nonneg α)
          (latitudeComparableMixedConstant_nonneg α))
    linarith
  have hnC : Cneighbor ≤ C := by
    dsimp [C, latitudeComparableGeometricConstant]
    have hE := exceptionalLatitudeDssttConstant_nonneg α
    have hpow : 0 ≤ (144 : ℝ) ^ (α / 2) := by positivity
    have hsep : 0 ≤
        8192 * (comparableDerivativeScaleConversionConstant α *
          latitudeComparableMixedConstant α) := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg
          (comparableDerivativeScaleConversionConstant_nonneg α)
          (latitudeComparableMixedConstant_nonneg α))
    linarith
  have hcC : Ccentral ≤ C := by
    dsimp [C, latitudeComparableGeometricConstant]
    have hE := exceptionalLatitudeDssttConstant_nonneg α
    have hpow : 0 ≤ (144 : ℝ) ^ (α / 2) := by positivity
    have hsep : 0 ≤
        8192 * (comparableDerivativeScaleConversionConstant α *
          latitudeComparableMixedConstant α) := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg
          (comparableDerivativeScaleConversionConstant_nonneg α)
          (latitudeComparableMixedConstant_nonneg α))
    linarith
  have hoC : Copposite ≤ C := by
    dsimp [C, latitudeComparableGeometricConstant]
    have hE := exceptionalLatitudeDssttConstant_nonneg α
    have hpow : 0 ≤ (144 : ℝ) ^ (α / 2) := by positivity
    have hsep : 0 ≤
        8192 * (comparableDerivativeScaleConversionConstant α *
          latitudeComparableMixedConstant α) := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg
          (comparableDerivativeScaleConversionConstant_nonneg α)
          (latitudeComparableMixedConstant_nonneg α))
    linarith
  have hsame :=
    comparableSame_block_bound_of_neighboring
      hα0 hα2 (by omega) hn0 hneighbor
  apply hasComparableLatitudeBlockBound_of_geometric_cases
  · intro j k hp hcomp
    exact (polar_comparable_bound_series
      hα0 hα2 hM j k hp hcomp).trans
        (comparableLatitudeBlockMajorant_mono hpC)
  · intro j k hc hcomp
    exact (hcentral j k hc hcomp).trans
      (comparableLatitudeBlockMajorant_mono hcC)
  · intro j k ho hcomp
    exact (hopposite j k ho hcomp).trans
      (comparableLatitudeBlockMajorant_mono hoC)
  · intro j k hs
    exact (hsame j k hs).trans
      (comparableLatitudeBlockMajorant_mono (by
        dsimp [C, latitudeComparableGeometricConstant]
        have hE := exceptionalLatitudeDssttConstant_nonneg α
        have hpow : 0 ≤ (144 : ℝ) ^ (α / 2) := by positivity
        linarith))

/-- Uniform versions of the three genuinely remaining comparable fields.
The constants depend on `α` but not on `N` or the band indices. -/
structure VeryLargeRemainingComparableLatitudeBounds (α : ℝ) where
  Cneighbor : ℝ
  Ccentral : ℝ
  Copposite : ℝ
  Cneighbor_nonneg : 0 ≤ Cneighbor
  Ccentral_nonneg : 0 ≤ Ccentral
  Copposite_nonneg : 0 ≤ Copposite
  neighboring :
    ∀ N ≥ 36, 600 ≤ bandCount N →
      HasNeighboringComparableLatitudeBlockBound α N Cneighbor
  central :
    ∀ N ≥ 36, 600 ≤ bandCount N →
      HasCentralComparableLatitudeBlockBound α N Ccentral
  opposite :
    ∀ N ≥ 36, 600 ≤ bandCount N →
      HasSmoothOppositeComparableLatitudeBlockBound α N Copposite

/-- The three remaining uniform fields, together with the unconditional
polar and separated fields, give the complete very-large comparable
interface. -/
theorem VeryLargeRemainingComparableLatitudeBounds.toComparable
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (h : VeryLargeRemainingComparableLatitudeBounds α) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36, 600 ≤ bandCount N →
      HasComparableLatitudeBlockBound α N C := by
  let C := latitudeComparableGeometricConstant
    α h.Cneighbor h.Ccentral h.Copposite
  have hC : 0 < C := by
    exact latitudeComparableGeometricConstant_pos
      h.Cneighbor_nonneg h.Ccentral_nonneg h.Copposite_nonneg
  refine ⟨C, hC, ?_⟩
  intro N hN hM
  exact hasComparableLatitudeBlockBound_of_remaining_cases
    hα0 hα2 (by omega)
    h.Cneighbor_nonneg h.Ccentral_nonneg h.Copposite_nonneg
    (h.neighboring N hN hM)
    (h.central N hN hM)
    (h.opposite N hN hM)

end BEMOC
