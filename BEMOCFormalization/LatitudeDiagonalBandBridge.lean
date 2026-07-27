import BEMOCFormalization.LatitudeDiagonalCuspBlocks
import BEMOCFormalization.LatitudeSmoothOppositeBlocks
import BEMOCFormalization.LatitudeComparableBlocks

/-!
# Concrete neighboring-band bridge

This module connects the fixed-square diagonal cusp estimates to the
literal BEMOC band-pair functional.  For equal or adjacent band indices the
sum of the two literal band widths is a common rescaling length, and the
normalized difference `(s-t)/a` stays in `[-1,1]` on the whole rectangle.

The main power-cusp theorem discards a biaffine part exactly and bounds the
remaining analytic part plus the physical cusp with the literal
populations and widths.  The resonant theorem performs the same reduction
without a `log a` loss: the scaling correction is a quadratic polynomial
and is absorbed into the biaffine nullspace.
-/

open MeasureTheory Set

namespace BEMOC

/-- Comparable same-hemisphere bands whose closed rectangles meet the
diagonal or are immediately adjacent. -/
def NeighboringComparableLatitudePair (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : Prop :=
  ComparableSameLatitudePair N j k ∧
    Nat.dist (j : ℕ) (k : ℕ) ≤ 1

/-- The common fixed-square rescaling length for neighboring bands. -/
noncomputable def neighboringBandLength (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : ℝ :=
  bandWidth N j + bandWidth N k

theorem neighboringBandLength_eq_populations
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1)) :
    neighboringBandLength N j k =
      2 * ((finiteBandPopulation N j : ℝ) +
        (finiteBandPopulation N k : ℝ)) / N := by
  unfold neighboringBandLength
  rw [bandWidth_eq_population, bandWidth_eq_population]
  ring

theorem neighboringBandLength_pos
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1)) :
    0 < neighboringBandLength N j k := by
  have hjpop : 0 < finiteBandPopulation N j := by
    have h := three_mul_latitudeBandScale_le_population hM j
    have hd := latitudeBandScale_pos N j
    omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [neighboringBandLength_eq_populations hN]
  have hjpopR : (0 : ℝ) < finiteBandPopulation N j := by
    exact_mod_cast hjpop
  positivity

/-- Literal neighboring-rectangle geometry: the largest possible physical
height separation is the sum of the two band widths. -/
theorem abs_sub_le_neighboringBandLength
    {N : ℕ} (j k : Fin (bandTailCount N + 1))
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |s - t| ≤ neighboringBandLength N j k := by
  rcases Nat.le_total (j : ℕ) (k : ℕ) with hjk | hkj
  · have hcases : (k : ℕ) = (j : ℕ) ∨ (k : ℕ) = (j : ℕ) + 1 := by
      rw [Nat.dist_eq_sub_of_le hjk] at hneigh
      omega
    rcases hcases with heq | hsucc
    · have hjkeq : j = k := Fin.ext heq.symm
      subst k
      have hwidth : |s - t| ≤ bandWidth N j := by
        rw [abs_le]
        unfold bandWidth
        constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
      unfold neighboringBandLength
      linarith [bandWidth_nonneg (N := N) j]
    · have hkeq : (k : ℕ) = (j : ℕ) + 1 := hsucc
      have horder : t ≤ s := by
        have hboundary :
            bandBoundaryHeight N k =
              bandBoundaryHeight N (j + 1) := by
          congr 1
        linarith [hs.1, ht.2]
      rw [abs_of_nonneg (sub_nonneg.mpr horder)]
      unfold neighboringBandLength bandWidth
      have htBottom :
          bandBoundaryHeight N (j + 2) ≤ t := by
        simpa only [show (k : ℕ) + 1 = (j : ℕ) + 2 by omega] using ht.1
      have hsum :
          (bandBoundaryHeight N j - bandBoundaryHeight N (j + 1)) +
              (bandBoundaryHeight N k - bandBoundaryHeight N (k + 1)) =
            bandBoundaryHeight N j - bandBoundaryHeight N (j + 2) := by
        rw [show (k : ℕ) = (j : ℕ) + 1 by omega]
        norm_num [Nat.add_assoc]
      rw [hsum]
      linarith [hs.2, htBottom]
  · have hcases : (j : ℕ) = (k : ℕ) ∨ (j : ℕ) = (k : ℕ) + 1 := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj] at hneigh
      omega
    rcases hcases with heq | hsucc
    · have hjkeq : j = k := Fin.ext heq
      subst k
      have hwidth : |s - t| ≤ bandWidth N j := by
        rw [abs_le]
        unfold bandWidth
        constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
      unfold neighboringBandLength
      linarith [bandWidth_nonneg (N := N) j]
    · have horder : s ≤ t := by
        have hboundary :
            bandBoundaryHeight N j =
              bandBoundaryHeight N (k + 1) := by
          congr 1
        linarith [hs.2, ht.1]
      rw [abs_of_nonpos (sub_nonpos.mpr horder)]
      unfold neighboringBandLength bandWidth
      have hsBottom :
          bandBoundaryHeight N (k + 2) ≤ s := by
        simpa only [show (j : ℕ) + 1 = (k : ℕ) + 2 by omega] using hs.1
      have hsum :
          (bandBoundaryHeight N j - bandBoundaryHeight N (j + 1)) +
              (bandBoundaryHeight N k - bandBoundaryHeight N (k + 1)) =
            bandBoundaryHeight N k - bandBoundaryHeight N (k + 2) := by
        rw [show (j : ℕ) = (k : ℕ) + 1 by omega]
        norm_num [Nat.add_assoc]
      rw [hsum]
      linarith [hsBottom, ht.2]

/-- The physical height difference normalized by the common neighboring
length lies in the fixed interval `[-1,1]`. -/
theorem abs_normalized_neighboring_sub_le_one
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |(s - t) / neighboringBandLength N j k| ≤ 1 := by
  have ha := neighboringBandLength_pos hN hM j k
  rw [abs_div, abs_of_pos ha, div_le_one ha]
  exact abs_sub_le_neighboringBandLength j k hneigh hs ht

/-- The literal band-pair bound for the diagonal power cusp.  This is the
concrete instantiation of the fixed-square power estimate with `D=1`. -/
theorem abs_bandPairError_latitudePowerBranch_sub_le
    {α : ℝ} (hα : -1 ≤ α)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k (fun s t ↦ latitudePowerBranch α (s - t))| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          neighboringBandLength N j k ^ (1 + α) := by
  let a := neighboringBandLength N j k
  have ha : 0 < a := neighboringBandLength_pos hN hM j k
  apply abs_bandPairError_le_of_band_rectangle_bound hN j k _ _
    (by positivity)
  intro s hs t ht
  have hunit :=
    abs_normalized_neighboring_sub_le_one hN hM j k hneigh hs ht
  have hscale :
      latitudePowerBranch α (s - t) =
        a ^ (1 + α) *
          latitudePowerBranch α ((s - t) / a) := by
    calc
      latitudePowerBranch α (s - t) =
          latitudePowerBranch α (a * ((s - t) / a)) := by
        congr 1
        field_simp [ha.ne']
      _ = _ := latitudePowerBranch_mul ha.le
  rw [hscale, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ha.le _)]
  unfold latitudePowerBranch
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hpow :
      |(s - t) / a| ^ (1 + α) ≤ (1 : ℝ) := by
    simpa using Real.rpow_le_one (abs_nonneg _) hunit (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hpow
    (Real.rpow_nonneg ha.le (1 + α))
  simpa [a] using hmul

/-- Concrete analytic-plus-power-cusp bridge.  The only local analytic
input is a biaffine decomposition whose genuine remainder has the standard
mixed-width bound. -/
theorem neighboring_powerCusp_block_bound_of_biaffine_decomposition
    {α C c : ℝ} (hα : -1 ≤ α) (hC : 0 ≤ C)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : NeighboringComparableLatitudePair N j k)
    (K R : ℝ → ℝ → ℝ)
    (uRight vRight uLeft vLeft : ℝ → ℝ)
    (hR : ∀ s, IntervalIntegrable (R s) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k))
    (hOuter : IntervalIntegrable
      (fun s ↦ bandError N k
        (fun t ↦ R s t + c * latitudePowerBranch α (s - t))) volume
      (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j))
    (huLeft : IntervalIntegrable uLeft volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k))
    (hvLeft : IntervalIntegrable vLeft volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k))
    (hdecomp : ∀ s t, K s t =
      (R s t + c * latitudePowerBranch α (s - t)) +
        (uRight s * t + vRight s) +
          (uLeft t * s + vLeft t))
    (hbound : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
        |R s t| ≤ C * bandWidth N j ^ 2 * bandWidth N k ^ 2) :
    |bandPairError N j k K| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
        (C * bandWidth N j ^ 2 * bandWidth N k ^ 2 +
          |c| * neighboringBandLength N j k ^ (1 + α)) := by
  let T : ℝ → ℝ → ℝ :=
    fun s t ↦ R s t + c * latitudePowerBranch α (s - t)
  have hT : ∀ s, IntervalIntegrable (T s) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k) := by
    intro s
    have hcusp : Continuous
        (fun t ↦ c * latitudePowerBranch α (s - t)) :=
      continuous_const.mul
        ((continuous_latitudePowerBranch hα).comp
          (continuous_const.sub continuous_id))
    exact (hR s).add (hcusp.intervalIntegrable _ _)
  have hTeq :
      bandPairError N j k K = bandPairError N j k T := by
    apply bandPairError_eq_of_biaffine_remainder hN j k K T
      uRight vRight uLeft vLeft hT
      (by simpa [T] using hOuter) huLeft hvLeft
    intro s t
    simpa [T] using hdecomp s t
  rw [hTeq]
  have ha : 0 < neighboringBandLength N j k :=
    neighboringBandLength_pos hN hM j k
  have htotalNonneg :
      0 ≤ C * bandWidth N j ^ 2 * bandWidth N k ^ 2 +
        |c| * neighboringBandLength N j k ^ (1 + α) := by positivity
  apply abs_bandPairError_le_of_band_rectangle_bound hN j k T _ htotalNonneg
  intro s hs t ht
  have hunit := abs_normalized_neighboring_sub_le_one
    hN hM j k hjk.2 hs ht
  have hcusp :
      |latitudePowerBranch α (s - t)| ≤
        neighboringBandLength N j k ^ (1 + α) := by
    have hscale :
        latitudePowerBranch α (s - t) =
          neighboringBandLength N j k ^ (1 + α) *
            latitudePowerBranch α
              ((s - t) / neighboringBandLength N j k) := by
      calc
        latitudePowerBranch α (s - t) =
            latitudePowerBranch α
              (neighboringBandLength N j k *
                ((s - t) / neighboringBandLength N j k)) := by
          congr 1
          field_simp [ha.ne']
        _ = _ := latitudePowerBranch_mul ha.le
    rw [hscale, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg ha.le _)]
    unfold latitudePowerBranch
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hpow := Real.rpow_le_one
      (abs_nonneg ((s - t) / neighboringBandLength N j k))
      hunit (by linarith : 0 ≤ 1 + α)
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hpow
        (Real.rpow_nonneg ha.le (1 + α)))
  dsimp [T]
  calc
    |R s t + c * latitudePowerBranch α (s - t)| ≤
        |R s t| + |c * latitudePowerBranch α (s - t)| :=
      abs_add_le _ _
    _ = |R s t| + |c| * |latitudePowerBranch α (s - t)| := by
      rw [abs_mul]
    _ ≤ C * bandWidth N j ^ 2 * bandWidth N k ^ 2 +
        |c| * neighboringBandLength N j k ^ (1 + α) := by
      exact add_le_add (hbound s hs t ht)
        (mul_le_mul_of_nonneg_left hcusp (abs_nonneg c))

/-- Exact cancellation of the translated quadratic under the literal
two-band BEMOC rule. -/
theorem bandPairError_sub_sq (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1)) :
    bandPairError N j k (fun s t ↦ (s - t) ^ 2) = 0 := by
  let Z : ℝ → ℝ → ℝ := fun _ _ ↦ 0
  have hZ : ∀ s, IntervalIntegrable (Z s) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k) := by
    intro s
    exact continuous_const.intervalIntegrable _ _
  have hOuter : IntervalIntegrable
      (fun s ↦ bandError N k (Z s)) volume
      (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) := by
    simp only [Z, bandError_zero hN]
    exact continuous_const.intervalIntegrable _ _
  have h :=
    bandPairError_eq_of_biaffine_remainder hN j k
      (fun s t ↦ (s - t) ^ 2) Z
      (fun s ↦ -2 * s) (fun s ↦ s ^ 2)
      (fun _ ↦ 0) (fun t ↦ t ^ 2)
      hZ hOuter
      (continuous_const.intervalIntegrable _ _)
      ((continuous_id.pow 2).intervalIntegrable _ _)
      (by intro s t; dsimp [Z]; ring)
  rw [h]
  unfold bandPairError
  simp only [Z, bandError_zero hN]

/-- Literal resonant neighboring-band bound with no scale logarithm.  The
two displayed integrability hypotheses isolate the routine local analytic
fact needed to use interval-integral linearity. -/
theorem exists_abs_bandPairError_resonantLatitudeBranch_sub_le
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    (hInner : ∀ s, IntervalIntegrable
      (fun t ↦ neighboringBandLength N j k ^ 2 *
        resonantLatitudeBranch
          ((s - t) / neighboringBandLength N j k)) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k))
    (hOuter : IntervalIntegrable
      (fun s ↦ bandError N k
        (fun t ↦ neighboringBandLength N j k ^ 2 *
          resonantLatitudeBranch
            ((s - t) / neighboringBandLength N j k))) volume
      (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j)) :
    ∃ B : ℝ, 0 ≤ B ∧
      |bandPairError N j k
        (fun s t ↦ resonantLatitudeBranch (s - t))| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (neighboringBandLength N j k ^ 2 * B) := by
  let a := neighboringBandLength N j k
  have ha : 0 < a := neighboringBandLength_pos hN hM j k
  obtain ⟨B, hB, hbranch⟩ :=
    exists_resonantLatitudeBranch_bound 1 (by norm_num)
  refine ⟨B, hB, ?_⟩
  let R : ℝ → ℝ → ℝ :=
    fun s t ↦ a ^ 2 * resonantLatitudeBranch ((s - t) / a)
  have heq :
      bandPairError N j k
          (fun s t ↦ resonantLatitudeBranch (s - t)) =
        bandPairError N j k R := by
    apply bandPairError_eq_of_biaffine_remainder hN j k _ R
      (fun s ↦ -2 * Real.log a * s)
      (fun s ↦ Real.log a * s ^ 2)
      (fun _ ↦ 0)
      (fun t ↦ Real.log a * t ^ 2)
      (by simpa [R, a] using hInner)
      (by simpa [R, a] using hOuter)
      (continuous_const.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _)
    intro s t
    have hscale := resonantLatitudeBranch_mul
      (a := a) (x := (s - t) / a) ha
    rw [show a * ((s - t) / a) = s - t by field_simp [ha.ne']] at hscale
    have hquad :
        a ^ 2 * ((s - t) / a) ^ 2 = (s - t) ^ 2 := by
      field_simp [ha.ne']
    have hcorr :
        a ^ 2 * Real.log a * ((s - t) / a) ^ 2 =
          Real.log a * (s - t) ^ 2 := by
      calc
        a ^ 2 * Real.log a * ((s - t) / a) ^ 2 =
            Real.log a * (a ^ 2 * ((s - t) / a) ^ 2) := by ring
        _ = _ := by rw [hquad]
    rw [hcorr] at hscale
    dsimp [R]
    rw [hscale]
    ring
  rw [heq]
  apply abs_bandPairError_le_of_band_rectangle_bound hN j k R
    (a ^ 2 * B) (mul_nonneg (sq_nonneg a) hB)
  intro s hs t ht
  have hunit := abs_normalized_neighboring_sub_le_one
    hN hM j k hneigh hs ht
  dsimp [R]
  rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
  exact mul_le_mul_of_nonneg_left (hbranch _ hunit) (sq_nonneg a)

/-- Premise-free resonant neighboring-band bound.  The two integrability
hypotheses in `exists_abs_bandPairError_resonantLatitudeBranch_sub_le` are
automatic because the continuously extended branch
`w ↦ w² log |w|` is continuous, and applying a concrete band error in the
second variable preserves continuity in the first. -/
theorem exists_abs_bandPairError_resonantLatitudeBranch_sub_le_concrete
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    ∃ B : ℝ, 0 ≤ B ∧
      |bandPairError N j k
        (fun s t ↦ resonantLatitudeBranch (s - t))| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (neighboringBandLength N j k ^ 2 * B) := by
  let a := neighboringBandLength N j k
  have hInner : ∀ s, IntervalIntegrable
      (fun t ↦ a ^ 2 * resonantLatitudeBranch ((s - t) / a)) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k) := by
    intro s
    exact
      (continuous_const.mul
        (continuous_resonantLatitudeBranch.comp
          ((continuous_const.sub continuous_id).div_const a))).intervalIntegrable _ _
  have hJoint : Continuous
      (fun p : ℝ × ℝ ↦
        a ^ 2 * resonantLatitudeBranch ((p.1 - p.2) / a)) := by
    exact continuous_const.mul
      (continuous_resonantLatitudeBranch.comp
        ((continuous_fst.sub continuous_snd).div_const a))
  have hOuter : IntervalIntegrable
      (fun s ↦ bandError N k
        (fun t ↦ a ^ 2 * resonantLatitudeBranch ((s - t) / a))) volume
      (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) := by
    exact (continuous_bandError_right k hJoint).intervalIntegrable _ _
  exact exists_abs_bandPairError_resonantLatitudeBranch_sub_le
    hN hM j k hneigh
      (by simpa [a] using hInner)
      (by simpa [a] using hOuter)

end BEMOC
