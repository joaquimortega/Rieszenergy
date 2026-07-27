import BEMOCFormalization.LatitudeCentralGeometry
import BEMOCFormalization.LatitudeEstimate

/-!
# Uniform fallback for finitely many latitude counts

The sharp local analysis is only needed once the number of latitude bands
is large.  For a bounded range of `N`, the diameter estimate and the exact
total band population give a uniform row bound directly.  This removes all
small-`M` edge cases from the central and opposite-hemisphere arguments.
-/

open scoped BigOperators

namespace BEMOC

/-- Summing the elementary global block bound over one row uses the exact
total population `N`. -/
theorem latitude_block_row_global
    {α : ℝ} (hα : 0 ≤ α) {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) :
    (∑ k : Fin (bandTailCount N + 1),
      |bandPairError N j k (latitudeKernel α)|) ≤
      4 * (finiteBandPopulation N j : ℝ) * (N : ℝ) *
        (2 : ℝ) ^ α := by
  calc
    (∑ k : Fin (bandTailCount N + 1),
        |bandPairError N j k (latitudeKernel α)|) ≤
        ∑ k : Fin (bandTailCount N + 1),
          4 * (finiteBandPopulation N j : ℝ) *
            (finiteBandPopulation N k : ℝ) * (2 : ℝ) ^ α := by
      apply Finset.sum_le_sum
      intro k hk
      exact abs_latitudeKernel_bandPairError_le_global hα hN j k
    _ = (4 * (finiteBandPopulation N j : ℝ) * (2 : ℝ) ^ α) *
        (∑ k : Fin (bandTailCount N + 1),
          (finiteBandPopulation N k : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = 4 * (finiteBandPopulation N j : ℝ) *
        (∑ k : Fin (bandTailCount N + 1),
          (finiteBandPopulation N k : ℝ)) * (2 : ℝ) ^ α := by ring
    _ = 4 * (finiteBandPopulation N j : ℝ) * (N : ℝ) *
        (2 : ℝ) ^ α := by
      rw [sum_finiteBandPopulation_cast]

/-- A single explicit constant handles every `N ≤ 900` with at least one
band.  The value is deliberately loose. -/
theorem hasLatitudeBlockRowBound_of_N_le_nine_hundred
    {α : ℝ} (hα : 0 ≤ α) {N : ℕ}
    (hN : 0 < N) (hN900 : N ≤ 900)
    (hM : 1 ≤ bandCount N) :
    HasLatitudeBlockRowBound α N
      (3600 * (2 : ℝ) ^ α * (15 : ℝ) ^ α) := by
  intro j
  have hglobal := latitude_block_row_global hα hN j
  have hMpos : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hM15Nat : bandCount N ≤ 15 := by
    have hfour := four_mul_bandCount_sq_le N
    have hfourR :
        4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
      exact_mod_cast hfour
    have hNreal : (N : ℝ) ≤ 900 := by exact_mod_cast hN900
    by_contra h
    have hM16 : (16 : ℝ) ≤ bandCount N := by
      exact_mod_cast (show 16 ≤ bandCount N by omega)
    nlinarith
  have hM15 : (bandCount N : ℝ) ≤ 15 := by
    exact_mod_cast hM15Nat
  have hpow :
      (bandCount N : ℝ) ^ α ≤ (15 : ℝ) ^ α :=
    Real.rpow_le_rpow hMpos.le hM15 hα
  have hinv : 0 ≤ (bandCount N : ℝ) ^ (-α) :=
    Real.rpow_nonneg hMpos.le _
  have hone :
      (1 : ℝ) ≤ (15 : ℝ) ^ α *
        (bandCount N : ℝ) ^ (-α) := by
    have hprod :
        (bandCount N : ℝ) ^ α *
            (bandCount N : ℝ) ^ (-α) = 1 := by
      rw [← Real.rpow_add hMpos]
      norm_num
    calc
      (1 : ℝ) =
          (bandCount N : ℝ) ^ α *
            (bandCount N : ℝ) ^ (-α) := hprod.symm
      _ ≤ (15 : ℝ) ^ α *
          (bandCount N : ℝ) ^ (-α) :=
        mul_le_mul_of_nonneg_right hpow hinv
  have hNreal : (N : ℝ) ≤ 900 := by exact_mod_cast hN900
  calc
    (∑ k : Fin (bandTailCount N + 1),
        |bandPairError N j k (latitudeKernel α)|) ≤
        4 * (finiteBandPopulation N j : ℝ) * (N : ℝ) *
          (2 : ℝ) ^ α := hglobal
    _ ≤ 4 * (finiteBandPopulation N j : ℝ) * 900 *
          (2 : ℝ) ^ α := by
      gcongr
    _ ≤ 4 * (finiteBandPopulation N j : ℝ) * 900 *
          (2 : ℝ) ^ α *
          ((15 : ℝ) ^ α * (bandCount N : ℝ) ^ (-α)) := by
      apply le_mul_of_one_le_right
      · positivity
      · exact hone
    _ = (3600 * (2 : ℝ) ^ α * (15 : ℝ) ^ α) *
        (finiteBandPopulation N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) := by ring

/-- A parameterized version of the finite fallback.  It is useful when a
local chart is only available above a larger fixed band-count threshold:
any bounded range of `N` and `M` is absorbed into one explicit constant. -/
theorem hasLatitudeBlockRowBound_of_bounded_N_and_bandCount
    {α : ℝ} (hα : 0 ≤ α) {N B D : ℕ}
    (hN : 0 < N) (hNB : N ≤ B)
    (hM : 1 ≤ bandCount N) (hMD : bandCount N ≤ D) :
    HasLatitudeBlockRowBound α N
      (4 * (B : ℝ) * (2 : ℝ) ^ α * (D : ℝ) ^ α) := by
  intro j
  have hglobal := latitude_block_row_global hα hN j
  have hMpos : (0 : ℝ) < bandCount N := by
    exact_mod_cast hM
  have hMDreal : (bandCount N : ℝ) ≤ D := by
    exact_mod_cast hMD
  have hpow :
      (bandCount N : ℝ) ^ α ≤ (D : ℝ) ^ α :=
    Real.rpow_le_rpow hMpos.le hMDreal hα
  have hinv : 0 ≤ (bandCount N : ℝ) ^ (-α) :=
    Real.rpow_nonneg hMpos.le _
  have hone :
      (1 : ℝ) ≤ (D : ℝ) ^ α *
        (bandCount N : ℝ) ^ (-α) := by
    have hprod :
        (bandCount N : ℝ) ^ α *
            (bandCount N : ℝ) ^ (-α) = 1 := by
      rw [← Real.rpow_add hMpos]
      norm_num
    calc
      (1 : ℝ) =
          (bandCount N : ℝ) ^ α *
            (bandCount N : ℝ) ^ (-α) := hprod.symm
      _ ≤ (D : ℝ) ^ α *
          (bandCount N : ℝ) ^ (-α) :=
        mul_le_mul_of_nonneg_right hpow hinv
  have hNBreal : (N : ℝ) ≤ B := by
    exact_mod_cast hNB
  calc
    (∑ k : Fin (bandTailCount N + 1),
        |bandPairError N j k (latitudeKernel α)|) ≤
        4 * (finiteBandPopulation N j : ℝ) * (N : ℝ) *
          (2 : ℝ) ^ α := hglobal
    _ ≤ 4 * (finiteBandPopulation N j : ℝ) * (B : ℝ) *
          (2 : ℝ) ^ α := by
      gcongr
    _ ≤ 4 * (finiteBandPopulation N j : ℝ) * (B : ℝ) *
          (2 : ℝ) ^ α *
          ((D : ℝ) ^ α * (bandCount N : ℝ) ^ (-α)) := by
      apply le_mul_of_one_le_right
      · positivity
      · exact hone
    _ = (4 * (B : ℝ) * (2 : ℝ) ^ α * (D : ℝ) ^ α) *
        (finiteBandPopulation N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) := by ring

/-- Row bounds are monotone in their numerical constant. -/
theorem HasLatitudeBlockRowBound.mono
    {α C D : ℝ} {N : ℕ}
    (h : HasLatitudeBlockRowBound α N C) (hCD : C ≤ D) :
    HasLatitudeBlockRowBound α N D := by
  intro j
  exact (h j).trans <|
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (by positivity))
      (by positivity)

/-- It is enough to prove the sharp analytic row estimate for `M ≥ 15`;
all remaining values are covered by the finite fallback above. -/
def HasLargeLatitudeBlockRowBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36, 15 ≤ bandCount N →
    HasLatitudeBlockRowBound α N C

/-- Analytic row control only in the range where all fixed neighboring
charts are available.  The bounded range below `600` is handled by the
preceding parameterized fallback. -/
def HasVeryLargeLatitudeBlockRowBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36, 600 ≤ bandCount N →
    HasLatitudeBlockRowBound α N C

/-- A very-large-band analytic estimate supplies the existing large-band
interface.  If `M < 600`, the elementary converse
`N ≤ 16 M²` bounds `N` by `5 760 000`, and the global finite fallback
applies uniformly. -/
theorem hasLargeLatitudeBlockRowBound_of_veryLarge
    {α : ℝ} (hα : 0 < α)
    (hvery : HasVeryLargeLatitudeBlockRowBound α) :
    HasLargeLatitudeBlockRowBound α := by
  obtain ⟨C, hC, hvery⟩ := hvery
  let Cmid : ℝ :=
    4 * (5760000 : ℝ) * (2 : ℝ) ^ α * (600 : ℝ) ^ α
  have hCmid : 0 < Cmid := by
    dsimp [Cmid]
    positivity
  refine ⟨C + Cmid, add_pos hC hCmid, ?_⟩
  intro N hN36 hM15
  by_cases hM600 : 600 ≤ bandCount N
  · exact (hvery N hN36 hM600).mono
      (le_add_of_nonneg_right hCmid.le)
  · have hM2 : 2 ≤ bandCount N := by omega
    have hNbound : N ≤ 5760000 := by
      have hrough := N_le_sixteen_bandCount_sq hM2
      have hMle : bandCount N ≤ 600 := by omega
      nlinarith
    exact
      (hasLatitudeBlockRowBound_of_bounded_N_and_bandCount
        (B := 5760000) (D := 600)
        hα.le (by omega) hNbound (by omega) (by omega)).mono
          (le_add_of_nonneg_left hC.le)

theorem hasUniformLatitudeBlockRowBound_of_large
    {α : ℝ} (hα : 0 < α)
    (hlarge : HasLargeLatitudeBlockRowBound α) :
    HasUniformLatitudeBlockRowBound α := by
  obtain ⟨C, hC, hlarge⟩ := hlarge
  let Csmall : ℝ := 3600 * (2 : ℝ) ^ α * (15 : ℝ) ^ α
  have hCsmall : 0 < Csmall := by
    dsimp [Csmall]
    positivity
  refine ⟨C + Csmall, add_pos hC hCsmall, ?_⟩
  intro N hN36
  have hM3 := three_le_bandCount_of_36_le hN36
  by_cases hMlarge : 15 ≤ bandCount N
  · exact (hlarge N hN36 hMlarge).mono
      (le_add_of_nonneg_right hCsmall.le)
  · have hN900 : N ≤ 900 := by
      by_contra hNbound
      have hquot : 225 ≤ N / 4 := by omega
      have hsqrt : 15 ≤ Nat.sqrt (N / 4) := by
        rw [Nat.le_sqrt]
        omega
      have : 15 ≤ bandCount N := by
        simpa [bandCount] using hsqrt
      exact hMlarge this
    exact
      (hasLatitudeBlockRowBound_of_N_le_nine_hundred
        hα.le (by omega) hN900 (by omega)).mono
          (le_add_of_nonneg_left hC.le)

/-- Public latitude endpoint reduced to the large-`M` analytic package. -/
theorem exists_bemocLatitudeDeficit_concrete_bound_of_largeRows
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hlarge : HasLargeLatitudeBlockRowBound α) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      |bemocLatitudeDeficit α N| ≤
        C * (N : ℝ) ^ (1 - α / 2) :=
  exists_bemocLatitudeDeficit_concrete_bound_of_uniformRows
    hα0 hα2
      (hasUniformLatitudeBlockRowBound_of_large hα0 hlarge)

/-- Therefore the public latitude endpoint may be discharged by proving the
analytic row estimate only for `M ≥ 600`. -/
theorem exists_bemocLatitudeDeficit_concrete_bound_of_veryLargeRows
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hvery : HasVeryLargeLatitudeBlockRowBound α) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      |bemocLatitudeDeficit α N| ≤
        C * (N : ℝ) ^ (1 - α / 2) :=
  exists_bemocLatitudeDeficit_concrete_bound_of_largeRows hα0 hα2
    (hasLargeLatitudeBlockRowBound_of_veryLarge hα0 hvery)

end BEMOC
