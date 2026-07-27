import BEMOCFormalization.LatitudeAxialBridge
import BEMOCFormalization.LatitudeSeparatedBlocks
import BEMOCFormalization.CrossRingEstimate

/-!
# Summation of latitude blocks

This module isolates the exact interface between the analytic block estimates
of L5--L6 and the arithmetic summation of L7.  The natural summable output of
the geometric case split is an absolute row estimate: the total interaction
of one band with all other bands is bounded by its population, times the
global latitude scale `M⁻ᵅ`.

The results below prove that this interface is sufficient, with explicit
constants, for both the `M^(2-α)` and `N^(1-α/2)` latitude bounds.  Thus the
remaining analytic work cannot hide any further arithmetic or normalization
issue.
-/

open scoped BigOperators

namespace BEMOC

/-- The manuscript scale `d_j`: distance of a band index from the nearer
polar end, with values starting at one. -/
def latitudeBandScale (N : ℕ)
    (j : Fin (bandTailCount N + 1)) : ℕ :=
  min ((j : ℕ) + 1) (bandTailCount N + 1 - (j : ℕ))

/-- The literal BEMOC band population dominates the manuscript scale.  This
is the bridge that lets analytic row bounds stated using `d_j` feed the
population-weighted L7 interface below. -/
theorem three_mul_latitudeBandScale_le_population
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (j : Fin (bandTailCount N + 1)) :
    3 * latitudeBandScale N j ≤ finiteBandPopulation N j := by
  by_cases hnorth : (j : ℕ) < bandCount N - 1
  · have hscale : latitudeBandScale N j = (j : ℕ) + 1 := by
      unfold latitudeBandScale
      rw [Nat.min_eq_left]
      simp [bandTailCount]
      omega
    rw [hscale, concrete_finiteBandPopulation_north j hnorth]
    exact (ordinaryPopulation_between_three_and_four_mul ((j : ℕ) + 1)
      (by omega)).1
  by_cases hcentral : (j : ℕ) = bandCount N - 1
  · have hj : j = concreteCentralBandIndex N := by
      apply Fin.ext
      simpa [concreteCentralBandIndex] using hcentral
    have hscale : latitudeBandScale N j = bandCount N := by
      unfold latitudeBandScale
      rw [Nat.min_eq_left]
      · simp [bandTailCount]
        omega
      · simp [bandTailCount]
        omega
    rw [hscale, hj, concrete_finiteBandPopulation_central (by omega)]
    exact (show 3 * bandCount N ≤ centralPopulation N by
      have hc := concrete_centralPopulation_lower (N := N) (by omega)
      omega)
  · let jr := concreteReflectBandIndex N j
    have hjrVal : (jr : ℕ) = bandTailCount N - (j : ℕ) := rfl
    have hjrNorth : (jr : ℕ) < bandCount N - 1 := by
      rw [hjrVal]
      simp [bandTailCount]
      omega
    have hscale : latitudeBandScale N j = (jr : ℕ) + 1 := by
      unfold latitudeBandScale
      rw [Nat.min_eq_right]
      · rw [hjrVal]
        omega
      · simp [bandTailCount]
        omega
    rw [hscale, concrete_finiteBandPopulation_reflect,
      concrete_finiteBandPopulation_north jr hjrNorth]
    exact (ordinaryPopulation_between_three_and_four_mul ((jr : ℕ) + 1)
      (by omega)).1

/-- Comparable latitude scales, in the deliberately inclusive factor-two
sense used by L5. -/
def ComparableLatitudeScales (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : Prop :=
  latitudeBandScale N j ≤ 2 * latitudeBandScale N k ∧
    latitudeBandScale N k ≤ 2 * latitudeBandScale N j

theorem latitudeBandScale_pos (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    0 < latitudeBandScale N j := by
  unfold latitudeBandScale
  rw [Nat.pos_iff_ne_zero]
  omega

theorem comparableLatitudeScales_comm {N : ℕ}
    {j k : Fin (bandTailCount N + 1)} :
    ComparableLatitudeScales N j k ↔ ComparableLatitudeScales N k j := by
  simp only [ComparableLatitudeScales, and_comm]

/-- The factor-two comparable and the two ordered unequal-scale regimes
exhaust every ordered pair of bands. -/
theorem latitudeScale_trichotomy (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) :
    ComparableLatitudeScales N j k ∨
      2 * latitudeBandScale N j < latitudeBandScale N k ∨
      2 * latitudeBandScale N k < latitudeBandScale N j := by
  unfold ComparableLatitudeScales
  omega

/-- Comparable partners of one fixed band. -/
noncomputable def comparableLatitudePartners (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    Finset (Fin (bandTailCount N + 1)) := by
  classical
  exact Finset.univ.filter (fun k ↦ ComparableLatitudeScales N j k)

/-- Noncomparable partners whose scale is more than twice the fixed scale. -/
noncomputable def largerLatitudePartners (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    Finset (Fin (bandTailCount N + 1)) := by
  classical
  exact (Finset.univ.filter
      (fun k ↦ ¬ ComparableLatitudeScales N j k)).filter
        (fun k ↦ 2 * latitudeBandScale N j < latitudeBandScale N k)

/-- The remaining noncomparable partners.  Exhaustiveness implies that their
scale is less than half the fixed scale. -/
noncomputable def smallerLatitudePartners (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    Finset (Fin (bandTailCount N + 1)) := by
  classical
  exact (Finset.univ.filter
      (fun k ↦ ¬ ComparableLatitudeScales N j k)).filter
        (fun k ↦ ¬ 2 * latitudeBandScale N j < latitudeBandScale N k)

theorem mem_smallerLatitudePartners_scale
    {N : ℕ} {j k : Fin (bandTailCount N + 1)}
    (hk : k ∈ smallerLatitudePartners N j) :
    2 * latitudeBandScale N k < latitudeBandScale N j := by
  simp only [smallerLatitudePartners, Finset.mem_filter,
    Finset.mem_univ, true_and] at hk
  rcases latitudeScale_trichotomy N j k with hcomp | hlarge | hsmall
  · exact False.elim (hk.1 hcomp)
  · exact False.elim (hk.2 hlarge)
  · exact hsmall

/-- The three L5--L6 regimes are an exact partition of every row. -/
theorem sum_latitudePartners_partition
    {N : ℕ} (j : Fin (bandTailCount N + 1))
    (f : Fin (bandTailCount N + 1) → ℝ) :
    (∑ k, f k) =
      (∑ k ∈ comparableLatitudePartners N j, f k) +
      (∑ k ∈ largerLatitudePartners N j, f k) +
      (∑ k ∈ smallerLatitudePartners N j, f k) := by
  classical
  rw [show (∑ k, f k) =
      (∑ k ∈ Finset.univ.filter
        (fun k ↦ ComparableLatitudeScales N j k), f k) +
      ∑ k ∈ Finset.univ.filter
        (fun k ↦ ¬ ComparableLatitudeScales N j k), f k by
    simpa using (Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun k ↦ ComparableLatitudeScales N j k) f).symm]
  rw [show (∑ k ∈ Finset.univ.filter
      (fun k ↦ ¬ ComparableLatitudeScales N j k), f k) =
      (∑ k ∈ (Finset.univ.filter
        (fun k ↦ ¬ ComparableLatitudeScales N j k)).filter
          (fun k ↦ 2 * latitudeBandScale N j < latitudeBandScale N k), f k) +
      ∑ k ∈ (Finset.univ.filter
        (fun k ↦ ¬ ComparableLatitudeScales N j k)).filter
          (fun k ↦ ¬ 2 * latitudeBandScale N j < latitudeBandScale N k), f k by
    simpa using (Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter
        (fun k ↦ ¬ ComparableLatitudeScales N j k))
      (fun k ↦ 2 * latitudeBandScale N j < latitudeBandScale N k) f).symm]
  simp only [comparableLatitudePartners, largerLatitudePartners,
    smallerLatitudePartners]
  ring

/-- The pointwise L5 comparable-block conclusion, packaged independently of
the particular local analytic proof used to obtain it. -/
def HasComparableLatitudeBlockBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    ComparableLatitudeScales N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        C * (latitudeBandScale N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) *
          (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3)

/-- The pointwise L6 unequal-scale conclusion.  Hemisphere and central-band
case distinctions remain in the geometric premise used to prove this
estimate; the numerical conclusion is the one that enters L7. -/
def HasUnequalLatitudeBlockBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
          (bandCount N : ℝ) ^ (-α) *
          (latitudeBandScale N k : ℝ) ^ (α - 5)

/-- The smooth opposite-hemisphere L6 conclusion. -/
def HasSmoothLatitudeBlockBound
    (α : ℝ) (N : ℕ) (C : ℝ)
    (SmoothPair :
      Fin (bandTailCount N + 1) →
      Fin (bandTailCount N + 1) → Prop) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1), SmoothPair j k →
    |bandPairError N j k (latitudeKernel α)| ≤
      C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
        (latitudeBandScale N k : ℝ) ^ (3 : ℕ) /
        (bandCount N : ℝ) ^ (8 : ℕ)

/-- The row estimate in the manuscript's `d_j` normalization.  This is the
most convenient direct output of summing the L5 and L6 pointwise estimates. -/
def HasLatitudeScaleRowBound (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j : Fin (bandTailCount N + 1),
    (∑ k : Fin (bandTailCount N + 1),
      |bandPairError N j k (latitudeKernel α)|) ≤
      C * (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α)

/-- The concrete L5--L6 inputs before final assembly: a summable comparable
row, the unequal interaction with larger scales, and the reflected unequal
interaction with smaller scales. -/
structure HasClassifiedLatitudeScaleRows
    (α : ℝ) (N : ℕ) (Ccomp Clarger Csmaller : ℝ) : Prop where
  comparable : ∀ j : Fin (bandTailCount N + 1),
    (∑ k ∈ comparableLatitudePartners N j,
      |bandPairError N j k (latitudeKernel α)|) ≤
      Ccomp * (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α)
  larger : ∀ j : Fin (bandTailCount N + 1),
    (∑ k ∈ largerLatitudePartners N j,
      |bandPairError N j k (latitudeKernel α)|) ≤
      Clarger * (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α)
  smaller : ∀ j : Fin (bandTailCount N + 1),
    (∑ k ∈ smallerLatitudePartners N j,
      |bandPairError N j k (latitudeKernel α)|) ≤
      Csmaller * (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α)

/-- Exhaustive assembly of the three concrete L5--L6 regimes. -/
theorem HasClassifiedLatitudeScaleRows.toScaleRowBound
    {α Ccomp Clarger Csmaller : ℝ} {N : ℕ}
    (h : HasClassifiedLatitudeScaleRows
      α N Ccomp Clarger Csmaller) :
    HasLatitudeScaleRowBound α N (Ccomp + Clarger + Csmaller) := by
  intro j
  rw [sum_latitudePartners_partition j
    (fun k ↦ |bandPairError N j k (latitudeKernel α)|)]
  calc
    (∑ k ∈ comparableLatitudePartners N j,
        |bandPairError N j k (latitudeKernel α)|) +
      (∑ k ∈ largerLatitudePartners N j,
        |bandPairError N j k (latitudeKernel α)|) +
      (∑ k ∈ smallerLatitudePartners N j,
        |bandPairError N j k (latitudeKernel α)|) ≤
      (Ccomp * (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α)) +
      (Clarger * (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α)) +
      (Csmaller * (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α)) :=
      add_le_add (add_le_add (h.comparable j) (h.larger j)) (h.smaller j)
    _ = (Ccomp + Clarger + Csmaller) *
        (latitudeBandScale N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) := by ring

/-- The summable L5--L6 block interface.  Comparable, unequal-scale, polar,
and antipodal estimates are intended to be partitioned and summed to prove
this row bound. -/
def HasLatitudeBlockRowBound (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j : Fin (bandTailCount N + 1),
    (∑ k : Fin (bandTailCount N + 1),
      |bandPairError N j k (latitudeKernel α)|) ≤
      C * (finiteBandPopulation N j : ℝ) *
        (bandCount N : ℝ) ^ (-α)

/-- A scale-row estimate implies the population-row estimate with no loss,
because every concrete BEMOC population dominates `d_j`. -/
theorem HasLatitudeScaleRowBound.toPopulation
    {α C : ℝ} {N : ℕ} (hM : 3 ≤ bandCount N) (hC : 0 ≤ C)
    (h : HasLatitudeScaleRowBound α N C) :
    HasLatitudeBlockRowBound α N C := by
  intro j
  refine (h j).trans ?_
  have hscaleNat := three_mul_latitudeBandScale_le_population hM j
  have hscale :
      (latitudeBandScale N j : ℝ) ≤ finiteBandPopulation N j := by
    exact_mod_cast (show latitudeBandScale N j ≤ finiteBandPopulation N j by
      omega)
  have hpow : 0 ≤ (bandCount N : ℝ) ^ (-α) :=
    Real.rpow_nonneg (by positivity) _
  gcongr

/-- The complete remaining L5--L6 input.  L2 is unconditional in
`LatitudeAxialBridge`, so the only field is the summable analytic row bound. -/
structure HasCompleteLatitudeBlockEstimate
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop where
  rowBound : HasLatitudeBlockRowBound α N C

theorem HasClassifiedLatitudeScaleRows.toComplete
    {α Ccomp Clarger Csmaller : ℝ} {N : ℕ}
    (hM : 3 ≤ bandCount N)
    (hcomp : 0 ≤ Ccomp) (hlarger : 0 ≤ Clarger)
    (hsmaller : 0 ≤ Csmaller)
    (h : HasClassifiedLatitudeScaleRows
      α N Ccomp Clarger Csmaller) :
    HasCompleteLatitudeBlockEstimate α N
      (Ccomp + Clarger + Csmaller) := by
  constructor
  exact h.toScaleRowBound.toPopulation hM
    (add_nonneg (add_nonneg hcomp hlarger) hsmaller)

/-- The sole uniform analytic statement still required for the latitude
endpoint after the unconditional axial/L2 bridge. -/
def HasUniformLatitudeBlockRowBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36, HasLatitudeBlockRowBound α N C

theorem sum_finiteBandPopulation_cast (N : ℕ) :
    (∑ j : Fin (bandTailCount N + 1),
      (finiteBandPopulation N j : ℝ)) = N := by
  exact_mod_cast sum_finiteBandPopulation N

/-- Absolute summation of the row interface. -/
theorem latitude_block_double_sum_abs_le
    {α C : ℝ} {N : ℕ} (hrow : HasLatitudeBlockRowBound α N C) :
    (∑ j : Fin (bandTailCount N + 1),
      ∑ k : Fin (bandTailCount N + 1),
        |bandPairError N j k (latitudeKernel α)|) ≤
      C * (N : ℝ) * (bandCount N : ℝ) ^ (-α) := by
  calc
    (∑ j : Fin (bandTailCount N + 1),
        ∑ k : Fin (bandTailCount N + 1),
          |bandPairError N j k (latitudeKernel α)|) ≤
        ∑ j : Fin (bandTailCount N + 1),
          C * (finiteBandPopulation N j : ℝ) *
            (bandCount N : ℝ) ^ (-α) :=
      Finset.sum_le_sum fun j hj ↦ hrow j
    _ = C * (N : ℝ) * (bandCount N : ℝ) ^ (-α) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum,
        sum_finiteBandPopulation_cast]

/-- The L2 identity turns the absolute block sum into an absolute latitude
deficit bound. -/
theorem abs_bemocLatitudeDeficit_le_of_completeBlockEstimate
    {α C : ℝ} {N : ℕ} (hN : 0 < N) (hα : 0 < α)
    (h : HasCompleteLatitudeBlockEstimate α N C) :
    |bemocLatitudeDeficit α N| ≤
      C * (N : ℝ) * (bandCount N : ℝ) ^ (-α) := by
  rw [bemocLatitudeDeficit_eq_neg_sum_bandPairError hN hα, abs_neg]
  calc
    |∑ j : Fin (bandTailCount N + 1),
        ∑ k : Fin (bandTailCount N + 1),
          bandPairError N j k (latitudeKernel α)| ≤
        ∑ j : Fin (bandTailCount N + 1),
          |∑ k : Fin (bandTailCount N + 1),
            bandPairError N j k (latitudeKernel α)| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun j : Fin (bandTailCount N + 1) ↦
          ∑ k : Fin (bandTailCount N + 1),
            bandPairError N j k (latitudeKernel α)) Finset.univ
    _ ≤ ∑ j : Fin (bandTailCount N + 1),
        ∑ k : Fin (bandTailCount N + 1),
          |bandPairError N j k (latitudeKernel α)| := by
      apply Finset.sum_le_sum
      intro j hj
      simpa using Finset.abs_sum_le_sum_abs
        (fun k : Fin (bandTailCount N + 1) ↦
          bandPairError N j k (latitudeKernel α)) Finset.univ
    _ ≤ C * (N : ℝ) * (bandCount N : ℝ) ^ (-α) :=
      latitude_block_double_sum_abs_le h.rowBound

/-- The purely arithmetic L7 conversion from population-weighted rows to
the manuscript scale `M^(2-α)`. -/
theorem abs_bemocLatitudeDeficit_le_bandCount_of_completeBlockEstimate
    {α C : ℝ} {N : ℕ} (hα : 0 < α) (hC : 0 ≤ C)
    (hM : 1 ≤ bandCount N)
    (h : HasCompleteLatitudeBlockEstimate α N C) :
    |bemocLatitudeDeficit α N| ≤
      (20 * C) * (bandCount N : ℝ) ^ (2 - α) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hfour' : 4 ≤ 4 * bandCount N ^ 2 := by
      nlinarith
    omega
  let M : ℝ := bandCount N
  have hMpos : 0 < M := by
    dsimp [M]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hNupper : (N : ℝ) ≤ 20 * M ^ 2 := by
    simpa [M] using
      (show (N : ℝ) ≤ 20 * (bandCount N : ℝ) ^ 2 by
        exact_mod_cast bemoc_N_le_twenty_bandCount_sq hM)
  have hscale : (N : ℝ) * M ^ (-α) ≤
      20 * M ^ (2 - α) := by
    calc
      (N : ℝ) * M ^ (-α) ≤
          (20 * M ^ 2) * M ^ (-α) :=
        mul_le_mul_of_nonneg_right hNupper (Real.rpow_nonneg hMpos.le _)
      _ = 20 * M ^ (2 - α) := by
        rw [show M ^ (2 : ℕ) = M ^ (2 : ℝ) by
          exact (Real.rpow_natCast M 2).symm]
        rw [mul_assoc, ← Real.rpow_add hMpos]
        congr 2
  calc
    |bemocLatitudeDeficit α N| ≤
        C * (N : ℝ) * M ^ (-α) := by
      simpa [M] using
        abs_bemocLatitudeDeficit_le_of_completeBlockEstimate hN hα h
    _ = C * ((N : ℝ) * M ^ (-α)) := by ring
    _ ≤ C * (20 * M ^ (2 - α)) :=
      mul_le_mul_of_nonneg_left hscale hC
    _ = (20 * C) * (bandCount N : ℝ) ^ (2 - α) := by
      dsimp [M]
      ring

/-- Conditional public endpoint in the `M` normalization.  Its sole
remaining premise is exactly the uniform L5--L6 analytic block package. -/
theorem exists_bemocLatitudeDeficit_bandCount_bound_of_blocks
    {α : ℝ} (hα0 : 0 < α)
    (hblocks : ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      HasCompleteLatitudeBlockEstimate α N C) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      |bemocLatitudeDeficit α N| ≤
        C * (bandCount N : ℝ) ^ (2 - α) := by
  obtain ⟨C, hC, hblocks⟩ := hblocks
  refine ⟨20 * C, mul_pos (by norm_num) hC, ?_⟩
  intro N hN
  apply abs_bemocLatitudeDeficit_le_bandCount_of_completeBlockEstimate
    hα0 hC.le
  · exact (three_le_bandCount_of_36_le hN).trans' (by omega)
  · exact hblocks N hN

/-- Conditional concrete L7 endpoint.  Once the explicit L5--L6 block
package is supplied, no further latitude arithmetic remains. -/
theorem exists_bemocLatitudeDeficit_concrete_bound_of_blocks
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hblocks : ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      HasCompleteLatitudeBlockEstimate α N C) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      |bemocLatitudeDeficit α N| ≤
        C * (N : ℝ) ^ (1 - α / 2) := by
  obtain ⟨C, hC, hband⟩ :=
    exists_bemocLatitudeDeficit_bandCount_bound_of_blocks hα0 hblocks
  refine ⟨C, hC, ?_⟩
  intro N hN
  exact (hband N hN).trans <|
    mul_le_mul_of_nonneg_left
      (bandCount_rpow_two_sub_le (N := N) hα2) hC.le

/-- Endpoint stated from the exact remaining analytic assumption alone.
There is no longer any Fubini, disintegration, or normalization hypothesis
in this interface. -/
theorem exists_bemocLatitudeDeficit_concrete_bound_of_uniformRows
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hrows : HasUniformLatitudeBlockRowBound α) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      |bemocLatitudeDeficit α N| ≤
        C * (N : ℝ) ^ (1 - α / 2) := by
  apply exists_bemocLatitudeDeficit_concrete_bound_of_blocks hα0 hα2
  obtain ⟨C, hC, hrows⟩ := hrows
  exact ⟨C, hC, fun N hN ↦ ⟨hrows N hN⟩⟩

end BEMOC
