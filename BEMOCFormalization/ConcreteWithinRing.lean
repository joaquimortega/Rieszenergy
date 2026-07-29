import BEMOCFormalization.Core
import BEMOCFormalization.RiemannSum
import Mathlib.Analysis.MeanInequalities

/-!
# Concrete weighted geometry sum for BEMOC rings

This module controls the literal geometric weight which multiplies the
uniform one-circle Euler--Maclaurin bound.
-/

open scoped BigOperators

namespace BEMOC

abbrev BemocRingIndex (N : ℕ) :=
  Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N)

/-- The literal weighted sum occurring in within-ring aggregation. -/
noncomputable def bemocWeightedRadiusPopulationSum (α : ℝ) (N : ℕ) : ℝ :=
  ∑ p : BemocRingIndex N,
    (bemocRingFamily N p).radius ^ α *
      ((bemocRingFamily N p).population : ℝ) ^ (1 - α)

theorem OccupiedRing.radius_le_one (R : OccupiedRing) : R.radius ≤ 1 := by
  have hrad : 0 ≤ 1 - R.height ^ 2 := by
    nlinarith [R.height_mem.1, R.height_mem.2]
  have hsquare : R.radius ^ 2 = 1 - R.height ^ 2 := by
    rw [OccupiedRing.radius, Real.sq_sqrt hrad]
  nlinarith [R.radius_nonneg, sq_nonneg R.height]

theorem card_bemocRingIndex {N : ℕ} (hM : 1 ≤ bandCount N) :
    Fintype.card (BemocRingIndex N) = 4 * bandCount N - 3 := by
  simp [BemocRingIndex, bandTailCount]
  omega

theorem card_bemocRingIndex_le_four_mul {N : ℕ} (hM : 1 ≤ bandCount N) :
    Fintype.card (BemocRingIndex N) ≤ 4 * bandCount N := by
  rw [card_bemocRingIndex hM]
  omega

theorem sum_bemoc_radius_le_four_mul {N : ℕ} (hM : 1 ≤ bandCount N) :
    ∑ p : BemocRingIndex N, (bemocRingFamily N p).radius ≤
      4 * bandCount N := by
  calc
    ∑ p : BemocRingIndex N, (bemocRingFamily N p).radius ≤
        ∑ _p : BemocRingIndex N, (1 : ℝ) :=
      Finset.sum_le_sum fun p _ ↦ OccupiedRing.radius_le_one _
    _ = Fintype.card (BemocRingIndex N) := by simp
    _ ≤ 4 * bandCount N := by exact_mod_cast card_bemocRingIndex_le_four_mul hM

/-! ## Actual midpoint/shared-boundary populations and exceptions -/

theorem concrete_centralPopulation_lower {N : ℕ} (hM : 1 ≤ bandCount N) :
    6 * bandCount N - 2 ≤ centralPopulation N := by
  have hdoubled := doubledOrdinaryTotal_closed N hM
  have hsq := bandCount_sq_le N
  have hscale : 4 * bandCount N ^ 2 ≤ N := by
    exact (Nat.mul_le_mul_left 4 hsq).trans (by omega)
  have haccount := reflectedPopulationTotal_eq N
  have hpred : bandCount N = (bandCount N - 1) + 1 := by omega
  have hformula :
      doubledOrdinaryTotal N + 6 * bandCount N = 4 * bandCount N ^ 2 + 2 := by
    rw [hdoubled]
    nlinarith
  unfold reflectedPopulationTotal at haccount
  omega

theorem concrete_symmetricBandPopulations_getElem_north {N j : ℕ}
    (hj : j < bandCount N - 1) :
    (symmetricBandPopulations N)[j]'(by
      rw [length_symmetricBandPopulations]
      omega) = ordinaryPopulation (j + 1) := by
  simp [symmetricBandPopulations, northernBandPopulations, hj]

@[simp] theorem concrete_reverse_symmetricBandPopulations (N : ℕ) :
    (symmetricBandPopulations N).reverse = symmetricBandPopulations N := by
  simp [symmetricBandPopulations]

theorem concrete_symmetricBandPopulations_get_reflect (N : ℕ)
    (i : Fin (symmetricBandPopulations N).length) :
    (symmetricBandPopulations N).get i =
      (symmetricBandPopulations N).get
        ⟨(symmetricBandPopulations N).length - 1 - (i : ℕ), by omega⟩ := by
  let ir : Fin (symmetricBandPopulations N).reverse.length :=
    ⟨(i : ℕ), by simpa using i.isLt⟩
  have h := List.get_reverse' (symmetricBandPopulations N) ir (by
    dsimp [ir]
    omega)
  simpa [ir] using h

theorem concrete_finiteBandPopulation_north {N : ℕ}
    (j : Fin (bandTailCount N + 1))
    (hj : (j : ℕ) < bandCount N - 1) :
    finiteBandPopulation N j = ordinaryPopulation ((j : ℕ) + 1) := by
  change (symmetricBandPopulations N)[(j : ℕ)]'_
      = ordinaryPopulation ((j : ℕ) + 1)
  exact concrete_symmetricBandPopulations_getElem_north hj

def concreteReflectBandIndex (N : ℕ) (j : Fin (bandTailCount N + 1)) :
    Fin (bandTailCount N + 1) :=
  ⟨bandTailCount N - (j : ℕ), by omega⟩

theorem concrete_finiteBandPopulation_reflect (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    finiteBandPopulation N j = finiteBandPopulation N (concreteReflectBandIndex N j) := by
  let i : Fin (symmetricBandPopulations N).length :=
    ⟨(j : ℕ), by rw [length_symmetricBandPopulations_eq_tail_succ]; exact j.isLt⟩
  have h := concrete_symmetricBandPopulations_get_reflect N i
  change (symmetricBandPopulations N).get i =
    (symmetricBandPopulations N).get
      ⟨bandTailCount N - (j : ℕ), by
        rw [length_symmetricBandPopulations_eq_tail_succ]
        omega⟩
  simpa [i, concreteReflectBandIndex,
    length_symmetricBandPopulations_eq_tail_succ] using h

def concreteCentralBandIndex (N : ℕ) : Fin (bandTailCount N + 1) :=
  ⟨bandCount N - 1, by simp [bandTailCount]; omega⟩

theorem concrete_finiteBandPopulation_central {N : ℕ}
    (_hM : 1 ≤ bandCount N) :
    finiteBandPopulation N (concreteCentralBandIndex N) = centralPopulation N := by
  change (symmetricBandPopulations N)[bandCount N - 1]'_ = centralPopulation N
  simp [symmetricBandPopulations, northernBandPopulations, concreteCentralBandIndex]

theorem concrete_finiteBandPopulation_interior_seven_le {N : ℕ}
    (hM : 3 ≤ bandCount N) (j : Fin (bandTailCount N + 1))
    (hj0 : 0 < (j : ℕ)) (hjlast : (j : ℕ) < bandTailCount N) :
    7 ≤ finiteBandPopulation N j := by
  by_cases hnorth : (j : ℕ) < bandCount N - 1
  · rw [concrete_finiteBandPopulation_north j hnorth]
    simp [ordinaryPopulation]
    omega
  by_cases hcentral : (j : ℕ) = bandCount N - 1
  · have hj : j = concreteCentralBandIndex N := by
      apply Fin.ext
      simpa [concreteCentralBandIndex] using hcentral
    rw [hj, concrete_finiteBandPopulation_central (by omega)]
    have hc := concrete_centralPopulation_lower (N := N) (by omega)
    omega
  · let jr := concreteReflectBandIndex N j
    have hjrVal : (jr : ℕ) = bandTailCount N - (j : ℕ) := rfl
    have hjrPos : 0 < (jr : ℕ) := by rw [hjrVal]; omega
    have hjrNorth : (jr : ℕ) < bandCount N - 1 := by
      rw [hjrVal]
      simp [bandTailCount]
      omega
    rw [concrete_finiteBandPopulation_reflect,
      concrete_finiteBandPopulation_north jr hjrNorth]
    simp [ordinaryPopulation]
    omega

theorem concrete_finiteBandPopulation_three_le {N : ℕ}
    (hM : 3 ≤ bandCount N) (j : Fin (bandTailCount N + 1)) :
    3 ≤ finiteBandPopulation N j := by
  by_cases hj0 : (j : ℕ) = 0
  · rw [concrete_finiteBandPopulation_north j (by omega)]
    simp [ordinaryPopulation, hj0]
  by_cases hjlast : (j : ℕ) = bandTailCount N
  · have href := concrete_finiteBandPopulation_reflect N j
    have hval : (concreteReflectBandIndex N j : ℕ) = 0 := by
      simp [concreteReflectBandIndex, hjlast]
    rw [href, concrete_finiteBandPopulation_north (concreteReflectBandIndex N j)
      (by rw [hval]; omega), hval]
    norm_num [ordinaryPopulation]
  · exact (by norm_num : 3 ≤ 7).trans
      (concrete_finiteBandPopulation_interior_seven_le hM j (by omega) (by
        have := j.isLt
        omega))

theorem concrete_midpointRingPopulation_two_le {N : ℕ}
    (hM : 3 ≤ bandCount N) (j : Fin (bandTailCount N + 1)) :
    2 ≤ midpointRingPopulation N j := by
  have hthree := concrete_finiteBandPopulation_three_le hM j
  rw [midpointRingPopulation, boundarySixth]
  split_ifs <;> omega

theorem concrete_boundarySixth_interior_one_le {N : ℕ}
    (hM : 3 ≤ bandCount N) (j : Fin (bandTailCount N + 1))
    (hj0 : 0 < (j : ℕ)) (hjlast : (j : ℕ) < bandTailCount N) :
    1 ≤ boundarySixth N j := by
  have hseven := concrete_finiteBandPopulation_interior_seven_le hM j hj0 hjlast
  rw [boundarySixth]
  split_ifs with hend
  · rcases hend with hzero | hlast
    · have hv : (j : ℕ) = 0 := by simpa using congrArg Fin.val hzero
      omega
    · have hv : (j : ℕ) = bandTailCount N := by
        simpa using congrArg Fin.val hlast
      omega
  · omega

theorem concrete_sharedBoundaryPopulation_interior_two_le {N : ℕ}
    (hM : 3 ≤ bandCount N) (j : Fin (bandTailCount N))
    (hj0 : 0 < (j : ℕ)) (hjlast : (j : ℕ) + 1 < bandTailCount N) :
    2 ≤ sharedBoundaryPopulation N j := by
  have hleft : 1 ≤ boundarySixth N j.castSucc := by
    apply concrete_boundarySixth_interior_one_le hM
    · simpa using hj0
    · simp
  have hright : 1 ≤ boundarySixth N j.succ := by
    apply concrete_boundarySixth_interior_one_le hM
    · simp
    · simpa using hjlast
  rw [sharedBoundaryPopulation]
  omega

def concreteNorthPolarBoundaryIndex (N : ℕ) (hM : 2 ≤ bandCount N) :
    Fin (bandTailCount N) := ⟨0, by simp [bandTailCount]; omega⟩

def concreteSouthPolarBoundaryIndex (N : ℕ) (hM : 2 ≤ bandCount N) :
    Fin (bandTailCount N) := ⟨bandTailCount N - 1, by
      simp [bandTailCount]
      omega⟩

theorem concrete_northPolarBoundary_population_eq_one {N : ℕ}
    (hM : 3 ≤ bandCount N) :
    sharedBoundaryPopulation N (concreteNorthPolarBoundaryIndex N (by omega)) = 1 := by
  rw [sharedBoundaryPopulation]
  have hcast : (concreteNorthPolarBoundaryIndex N (by omega)).castSucc = 0 := by
    apply Fin.ext
    simp [concreteNorthPolarBoundaryIndex]
  rw [hcast, boundarySixth_zero]
  have hsucc : (((concreteNorthPolarBoundaryIndex N (by omega)).succ :
      Fin (bandTailCount N + 1)) : ℕ) = 1 := by
    simp [concreteNorthPolarBoundaryIndex]
  rw [boundarySixth]
  split_ifs with hend
  · rcases hend with hzero | hlast
    · have hv := congrArg Fin.val hzero
      simp [hsucc] at hv
    · have hv : (bandTailCount N : ℕ) = 1 := by
        simpa [hsucc] using congrArg Fin.val hlast |>.symm
      simp [bandTailCount] at hv
  · rw [concrete_finiteBandPopulation_north _ (by rw [hsucc]; omega), hsucc]
    norm_num [ordinaryPopulation]

theorem concrete_bemocRingFamily_population_pos {N : ℕ}
    (hM : 3 ≤ bandCount N) (p : BemocRingIndex N) :
    0 < (bemocRingFamily N p).population := by
  rcases p with j | j
  · change 0 < midpointRingPopulation N j
    exact (concrete_midpointRingPopulation_two_le hM j).trans_lt' (by norm_num)
  · change 0 < sharedBoundaryPopulation N j
    by_cases hj0 : (j : ℕ) = 0
    · have hj : j = concreteNorthPolarBoundaryIndex N (by omega) := by
        apply Fin.ext
        simpa [concreteNorthPolarBoundaryIndex] using hj0
      rw [hj, concrete_northPolarBoundary_population_eq_one hM]
      norm_num
    by_cases hjlast : (j : ℕ) + 1 = bandTailCount N
    · rw [sharedBoundaryPopulation]
      have hsucc : j.succ = Fin.last (bandTailCount N) := by
        apply Fin.ext
        simpa using hjlast
      rw [hsucc, boundarySixth_last]
      have hcast : 0 < ((j.castSucc : Fin (bandTailCount N + 1)) : ℕ) := by
        simpa using (show 0 < (j : ℕ) by omega)
      have hcastLast : ((j.castSucc : Fin (bandTailCount N + 1)) : ℕ) <
          bandTailCount N := by
        simp
      have hb := concrete_boundarySixth_interior_one_le hM j.castSucc hcast hcastLast
      omega
    · exact (concrete_sharedBoundaryPopulation_interior_two_le hM j
        (by omega) (by have := j.isLt; omega)).trans_lt' (by norm_num)

/-! ## Northern height and radius bounds -/

private theorem concrete_take_map_eq_map_take { γ δ : Type* } (f : γ → δ)
    (l : List γ) (n : ℕ) : (l.map f).take n = (l.take n).map f := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
      cases l with
      | nil => simp
      | cons a l =>
          change f a :: (l.map f).take n = f a :: (l.take n).map f
          rw [ih]

theorem concrete_sum_take_north {N j : ℕ} (hj : j ≤ bandCount N - 1) :
    ((symmetricBandPopulations N).take j).sum = j * (2 * j + 1) := by
  rw [symmetricBandPopulations,
    List.take_append_of_le_length (by simpa using hj)]
  rw [northernBandPopulations, concrete_take_map_eq_map_take, List.take_range,
    min_eq_left hj]
  rw [← List.sum_toFinset (fun k ↦ ordinaryPopulation (k + 1)) List.nodup_range]
  have hrange : (List.range j).toFinset = Finset.range j := by ext k; simp
  rw [hrange]
  exact sum_ordinaryPopulation j

theorem concrete_bandBoundaryHeight_north {N j : ℕ}
    (hj : j ≤ bandCount N - 1) :
    bandBoundaryHeight N j =
      1 - 2 * (j : ℝ) * (2 * (j : ℝ) + 1) / N := by
  rw [bandBoundaryHeight, concrete_sum_take_north hj]
  norm_num
  congr 1
  ring

theorem concrete_bandMidpointHeight_north {N j : ℕ}
    (hj : j < bandCount N - 1) :
    bandMidpointHeight N j =
      1 - (4 * ((j : ℝ) + 1) ^ 2 - 2 * ((j : ℝ) + 1) + 1) / N := by
  rw [bandMidpointHeight, concrete_bandBoundaryHeight_north (Nat.le_of_lt hj),
    concrete_bandBoundaryHeight_north (by omega : j + 1 ≤ bandCount N - 1)]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

theorem OccupiedRing.radius_sq_le_two_height_gap (R : OccupiedRing) :
    R.radius ^ 2 ≤ 2 * (1 - R.height) := by
  have hrad : 0 ≤ 1 - R.height ^ 2 := by
    nlinarith [R.height_mem.1, R.height_mem.2]
  rw [OccupiedRing.radius, Real.sq_sqrt hrad]
  nlinarith [R.height_mem.2]

theorem concrete_midpoint_radius_upper_north {N : ℕ}
    (hM : 3 ≤ bandCount N) (j : Fin (bandTailCount N + 1))
    (hj : (j : ℕ) < bandCount N - 1) :
    (bandCount N : ℝ) * (bemocRingFamily N (Sum.inl j)).radius ≤
      2 * (((j : ℕ) + 1 : ℕ) : ℝ) := by
  let R := bemocRingFamily N (Sum.inl j)
  let M : ℝ := bandCount N
  let d : ℝ := ((j : ℕ) + 1 : ℕ)
  let a : ℝ := 4 * d ^ 2 - 2 * d + 1
  have hN : (0 : ℝ) < N := by
    have hMpos : 0 < bandCount N := by omega
    rw [bandCount] at hMpos
    exact_mod_cast (show 0 < N by
      have := Nat.sqrt_pos.mp hMpos
      omega)
  have hM0 : 0 ≤ M := by positivity
  have hd : 0 ≤ d := by positivity
  have hd1 : 1 ≤ d := by dsimp [d]; norm_num
  have hdm : d ≤ M := by
    dsimp [d, M]
    exact_mod_cast (show (j : ℕ) + 1 ≤ bandCount N by omega)
  have haUpper : a ≤ 4 * d ^ 2 := by dsimp [a]; nlinarith
  have hheight : R.height = 1 - a / N := by
    dsimp [R, a, d]
    rw [bemocRingFamily]
    simp only [dif_pos (by exact_mod_cast hN)]
    rw [concrete_bandMidpointHeight_north hj]
    norm_num [Nat.cast_add, Nat.cast_one]
  have hr := R.radius_sq_le_two_height_gap
  rw [hheight] at hr
  have hrN : (N : ℝ) * R.radius ^ 2 ≤ 2 * a := by
    have hr' : R.radius ^ 2 ≤ 2 * a / N := by
      convert hr using 1 ; ring
    have := (le_div_iff₀ hN).1 hr'
    nlinarith
  have hscaleNat : 4 * bandCount N ^ 2 ≤ N :=
    (Nat.mul_le_mul_left 4 (bandCount_sq_le N)).trans (by omega)
  have hscale : 4 * M ^ 2 ≤ (N : ℝ) := by
    dsimp [M]
    exact_mod_cast hscaleNat
  have hsquare : (M * R.radius) ^ 2 ≤ (2 * d) ^ 2 := by
    have hr0 := R.radius_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hscale (sq_nonneg R.radius)]
  exact (sq_le_sq₀ (mul_nonneg hM0 R.radius_nonneg) (by positivity)).1 hsquare

theorem concrete_boundary_radius_upper_north {N : ℕ}
    (hM : 3 ≤ bandCount N) (j : Fin (bandTailCount N))
    (hj : (j : ℕ) < bandCount N - 1) :
    (bandCount N : ℝ) * (bemocRingFamily N (Sum.inr j)).radius ≤
      2 * (((j : ℕ) + 1 : ℕ) : ℝ) := by
  let R := bemocRingFamily N (Sum.inr j)
  let M : ℝ := bandCount N
  let d : ℝ := ((j : ℕ) + 1 : ℕ)
  let a : ℝ := 2 * d * (2 * d + 1)
  have hN : (0 : ℝ) < N := by
    have hMpos : 0 < bandCount N := by omega
    rw [bandCount] at hMpos
    exact_mod_cast (show 0 < N by
      have := Nat.sqrt_pos.mp hMpos
      omega)
  have hM0 : 0 ≤ M := by positivity
  have hd : 0 ≤ d := by positivity
  have hd1 : 1 ≤ d := by dsimp [d]; norm_num
  have hdm : d ≤ M := by
    dsimp [d, M]
    exact_mod_cast (show (j : ℕ) + 1 ≤ bandCount N by omega)
  have haUpper : a ≤ 6 * d ^ 2 := by dsimp [a]; nlinarith
  have hheight : R.height = 1 - a / N := by
    dsimp [R, a, d]
    rw [bemocRingFamily]
    simp only [dif_pos (by exact_mod_cast hN)]
    rw [concrete_bandBoundaryHeight_north (by omega)]
  have hr := R.radius_sq_le_two_height_gap
  rw [hheight] at hr
  have hrN : (N : ℝ) * R.radius ^ 2 ≤ 2 * a := by
    have hr' : R.radius ^ 2 ≤ 2 * a / N := by
      convert hr using 1 ; ring
    have := (le_div_iff₀ hN).1 hr'
    nlinarith
  have hscaleNat : 4 * bandCount N ^ 2 ≤ N :=
    (Nat.mul_le_mul_left 4 (bandCount_sq_le N)).trans (by omega)
  have hscale : 4 * M ^ 2 ≤ (N : ℝ) := by
    dsimp [M]
    exact_mod_cast hscaleNat
  have hsquare : (M * R.radius) ^ 2 ≤ (2 * d) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hscale (sq_nonneg R.radius)]
  exact (sq_le_sq₀ (mul_nonneg hM0 R.radius_nonneg) (by positivity)).1 hsquare

/-! ## Northern population lower bounds -/

theorem concrete_boundarySixth_north {N : ℕ}
    (j : Fin (bandTailCount N + 1))
    (hj : (j : ℕ) < bandCount N - 1) :
    boundarySixth N j = ordinaryPopulation ((j : ℕ) + 1) / 6 := by
  rw [boundarySixth]
  split_ifs with hend
  · rcases hend with hj0 | hjlast
    · subst j
      norm_num [ordinaryPopulation]
    · have hv := congrArg Fin.val hjlast
      simp [bandTailCount] at hv
      omega
  · rw [concrete_finiteBandPopulation_north j hj]

private theorem concrete_ordinary_midpoint_two_mul_le {d : ℕ} (hd : 1 ≤ d) :
    2 * d ≤ ordinaryPopulation d - 2 * (ordinaryPopulation d / 6) := by
  simp only [ordinaryPopulation]
  by_cases hsmall : d ≤ 3
  · interval_cases d <;> norm_num
  · omega

theorem concrete_midpoint_population_two_mul_index_le {N : ℕ}
    (j : Fin (bandTailCount N + 1))
    (hj : (j : ℕ) < bandCount N - 1) :
    2 * ((j : ℕ) + 1) ≤ midpointRingPopulation N j := by
  rw [midpointRingPopulation, concrete_finiteBandPopulation_north j hj,
    concrete_boundarySixth_north j hj]
  exact concrete_ordinary_midpoint_two_mul_le (by omega)

private theorem concrete_ordinary_shared_index_le {d : ℕ} (hd : 1 ≤ d) :
    d ≤ ordinaryPopulation d / 6 + ordinaryPopulation (d + 1) / 6 := by
  simp only [ordinaryPopulation]
  by_cases hsmall : d ≤ 3
  · interval_cases d <;> norm_num
  · omega

theorem concrete_shared_population_index_le_ordinary {N : ℕ}
    (j : Fin (bandTailCount N))
    (hj : (j : ℕ) < bandCount N - 2) :
    (j : ℕ) + 1 ≤ sharedBoundaryPopulation N j := by
  have hleft : ((j.castSucc : Fin (bandTailCount N + 1)) : ℕ) <
      bandCount N - 1 := by simpa using (show (j : ℕ) < bandCount N - 1 by omega)
  have hright : ((j.succ : Fin (bandTailCount N + 1)) : ℕ) <
      bandCount N - 1 := by
    simpa using (show (j : ℕ) + 1 < bandCount N - 1 by omega)
  rw [sharedBoundaryPopulation, concrete_boundarySixth_north j.castSucc hleft,
    concrete_boundarySixth_north j.succ hright]
  convert concrete_ordinary_shared_index_le
    (d := (j : ℕ) + 1) (by omega) using 1

theorem concrete_boundarySixth_central_lower {N : ℕ}
    (hM : 3 ≤ bandCount N) :
    bandCount N - 1 ≤ boundarySixth N (concreteCentralBandIndex N) := by
  rw [boundarySixth]
  split_ifs with hend
  · rcases hend with hzero | hlast
    · have hv := congrArg Fin.val hzero
      simp [concreteCentralBandIndex] at hv
      omega
    · have hv := congrArg Fin.val hlast
      simp [concreteCentralBandIndex, bandTailCount] at hv
      omega
  · rw [concrete_finiteBandPopulation_central (by omega)]
    have hc := concrete_centralPopulation_lower (N := N) (by omega)
    omega

theorem concrete_shared_population_index_le_centralAdjacent {N : ℕ}
    (hM : 3 ≤ bandCount N) (j : Fin (bandTailCount N))
    (hj : (j : ℕ) = bandCount N - 2) :
    (j : ℕ) + 1 ≤ sharedBoundaryPopulation N j := by
  have hsucc : j.succ = concreteCentralBandIndex N := by
    apply Fin.ext
    simp [concreteCentralBandIndex]
    omega
  rw [sharedBoundaryPopulation, hsucc]
  have hc := concrete_boundarySixth_central_lower (N := N) hM
  omega

theorem concrete_midpoint_lower_comparison_north {N : ℕ}
    (hM : 3 ≤ bandCount N) (j : Fin (bandTailCount N + 1))
    (hj : (j : ℕ) < bandCount N - 1) :
    (bandCount N : ℝ) * (bemocRingFamily N (Sum.inl j)).radius ≤
      (midpointRingPopulation N j : ℝ) := by
  have hr := concrete_midpoint_radius_upper_north hM j hj
  have hp := concrete_midpoint_population_two_mul_index_le j hj
  exact le_trans hr (by exact_mod_cast hp)

theorem concrete_boundary_lower_comparison_north {N : ℕ}
    (hM : 3 ≤ bandCount N) (j : Fin (bandTailCount N))
    (hj : (j : ℕ) < bandCount N - 1) :
    (bandCount N : ℝ) * (bemocRingFamily N (Sum.inr j)).radius ≤
      2 * (sharedBoundaryPopulation N j : ℝ) := by
  have hr := concrete_boundary_radius_upper_north hM j hj
  have hp : (j : ℕ) + 1 ≤ sharedBoundaryPopulation N j := by
    by_cases hord : (j : ℕ) < bandCount N - 2
    · exact concrete_shared_population_index_le_ordinary j hord
    · apply concrete_shared_population_index_le_centralAdjacent hM j
      omega
  exact le_trans hr (by exact_mod_cast Nat.mul_le_mul_left 2 hp)

theorem concrete_midpoint_central_population_ge_bandCount {N : ℕ}
    (hM : 3 ≤ bandCount N) :
    bandCount N ≤ midpointRingPopulation N (concreteCentralBandIndex N) := by
  have hsixth : boundarySixth N (concreteCentralBandIndex N) =
      centralPopulation N / 6 := by
    rw [boundarySixth]
    split_ifs with hend
    · rcases hend with hzero | hlast
      · have hv := congrArg Fin.val hzero
        simp [concreteCentralBandIndex] at hv
        omega
      · have hv := congrArg Fin.val hlast
        simp [concreteCentralBandIndex, bandTailCount] at hv
        omega
    · rw [concrete_finiteBandPopulation_central (by omega)]
  rw [midpointRingPopulation, concrete_finiteBandPopulation_central (by omega), hsixth]
  have hc := concrete_centralPopulation_lower (N := N) (by omega)
  omega

theorem concrete_midpoint_lower_comparison_central {N : ℕ}
    (hM : 3 ≤ bandCount N) :
    (bandCount N : ℝ) *
        (bemocRingFamily N (Sum.inl (concreteCentralBandIndex N))).radius ≤
      (midpointRingPopulation N (concreteCentralBandIndex N) : ℝ) := by
  have hr := OccupiedRing.radius_le_one
    (bemocRingFamily N (Sum.inl (concreteCentralBandIndex N)))
  have hp := concrete_midpoint_central_population_ge_bandCount (N := N) hM
  have hM0 : (0 : ℝ) ≤ bandCount N := by positivity
  calc
    (bandCount N : ℝ) *
        (bemocRingFamily N (Sum.inl (concreteCentralBandIndex N))).radius ≤
        (bandCount N : ℝ) * 1 := mul_le_mul_of_nonneg_left hr hM0
    _ = (bandCount N : ℝ) := by ring
    _ ≤ midpointRingPopulation N (concreteCentralBandIndex N) := by exact_mod_cast hp

/-! ## North--south reflection -/

theorem concrete_sum_take_reflect {N k : ℕ}
    (_hk : k ≤ (symmetricBandPopulations N).length) :
    ((symmetricBandPopulations N).take
        ((symmetricBandPopulations N).length - k)).sum =
      N - ((symmetricBandPopulations N).take k).sum := by
  let l := symmetricBandPopulations N
  have hdrop : (l.drop (l.length - k)).sum = (l.take k).sum := by
    have hlist : l.drop (l.length - k) = (l.reverse.take k).reverse := by
      have hzero : l.length - k = l.length - k := rfl
      rw [List.take_reverse, hzero, List.reverse_reverse]
    rw [hlist, List.sum_reverse]
    simp [l]
  have hsplit := List.sum_take_add_sum_drop l (l.length - k)
  rw [hdrop] at hsplit
  have htotal : l.sum = N := by simp [l]
  have hresult : (l.take (l.length - k)).sum = N - (l.take k).sum := by
    omega
  simpa [l] using hresult

theorem concrete_bandBoundaryHeight_reflect {N k : ℕ} (hN : 0 < N)
    (hk : k ≤ (symmetricBandPopulations N).length) :
    bandBoundaryHeight N ((symmetricBandPopulations N).length - k) =
      -bandBoundaryHeight N k := by
  have hsum := concrete_sum_take_reflect (N := N) hk
  have hpartial := sum_take_symmetricBandPopulations_le N k
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [bandBoundaryHeight, bandBoundaryHeight, hsum, Nat.cast_sub hpartial]
  field_simp [hNreal]
  ring

theorem concrete_boundarySixth_reflect (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    boundarySixth N (concreteReflectBandIndex N j) = boundarySixth N j := by
  by_cases hj0 : j = 0
  · subst j
    have hr : concreteReflectBandIndex N 0 = Fin.last (bandTailCount N) := by
      apply Fin.ext
      simp [concreteReflectBandIndex]
    rw [hr, boundarySixth_last, boundarySixth_zero]
  by_cases hjlast : j = Fin.last (bandTailCount N)
  · subst j
    have hr : concreteReflectBandIndex N (Fin.last (bandTailCount N)) = 0 := by
      apply Fin.ext
      simp [concreteReflectBandIndex]
    rw [hr, boundarySixth_zero, boundarySixth_last]
  have hr0 : concreteReflectBandIndex N j ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    have hjv := j.isLt
    simp [concreteReflectBandIndex] at hv
    have hjlastVal : (j : ℕ) ≠ bandTailCount N := by
      intro heq
      apply hjlast
      apply Fin.ext
      simpa using heq
    omega
  have hrlast : concreteReflectBandIndex N j ≠ Fin.last (bandTailCount N) := by
    intro h
    have hv := congrArg Fin.val h
    simp [concreteReflectBandIndex] at hv
    have hjzeroVal : (j : ℕ) ≠ 0 := by
      intro heq
      apply hj0
      apply Fin.ext
      simpa using heq
    omega
  simp only [boundarySixth, if_neg (not_or_intro hr0 hrlast),
    if_neg (not_or_intro hj0 hjlast)]
  rw [← concrete_finiteBandPopulation_reflect N j]

theorem concrete_midpointRingPopulation_reflect (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    midpointRingPopulation N (concreteReflectBandIndex N j) =
      midpointRingPopulation N j := by
  rw [midpointRingPopulation, midpointRingPopulation,
    concrete_boundarySixth_reflect]
  rw [← concrete_finiteBandPopulation_reflect N j]

def concreteReflectBoundaryIndex (N : ℕ) (j : Fin (bandTailCount N)) :
    Fin (bandTailCount N) := ⟨bandTailCount N - 1 - (j : ℕ), by omega⟩

theorem concrete_sharedBoundaryPopulation_reflect (N : ℕ)
    (j : Fin (bandTailCount N)) :
    sharedBoundaryPopulation N (concreteReflectBoundaryIndex N j) =
      sharedBoundaryPopulation N j := by
  let jr := concreteReflectBoundaryIndex N j
  have hcast : (jr.castSucc : Fin (bandTailCount N + 1)) =
      concreteReflectBandIndex N j.succ := by
    apply Fin.ext
    simp [jr, concreteReflectBoundaryIndex, concreteReflectBandIndex]
    omega
  have hsucc : (jr.succ : Fin (bandTailCount N + 1)) =
      concreteReflectBandIndex N j.castSucc := by
    apply Fin.ext
    simp [jr, concreteReflectBoundaryIndex, concreteReflectBandIndex]
    omega
  rw [sharedBoundaryPopulation, sharedBoundaryPopulation, hcast, hsucc,
    concrete_boundarySixth_reflect, concrete_boundarySixth_reflect]
  omega

theorem concrete_bandMidpointHeight_reflect {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) :
    bandMidpointHeight N (concreteReflectBandIndex N j) =
      -bandMidpointHeight N j := by
  have hj : (j : ℕ) ≤ (symmetricBandPopulations N).length := by
    rw [length_symmetricBandPopulations_eq_tail_succ]
    omega
  have hj1 : (j : ℕ) + 1 ≤ (symmetricBandPopulations N).length := by
    rw [length_symmetricBandPopulations_eq_tail_succ]
    exact j.isLt
  rw [bandMidpointHeight, bandMidpointHeight]
  rw [show ((concreteReflectBandIndex N j : Fin (bandTailCount N + 1)) : ℕ) =
        (symmetricBandPopulations N).length - ((j : ℕ) + 1) by
      simp [concreteReflectBandIndex, bandTailCount]
      ]
  rw [show (symmetricBandPopulations N).length - ((j : ℕ) + 1) + 1 =
        (symmetricBandPopulations N).length - (j : ℕ) by omega]
  rw [concrete_bandBoundaryHeight_reflect hN hj1,
    concrete_bandBoundaryHeight_reflect hN hj]
  ring

theorem concrete_sharedBoundaryHeight_reflect {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N)) :
    bandBoundaryHeight N ((concreteReflectBoundaryIndex N j : ℕ) + 1) =
      -bandBoundaryHeight N ((j : ℕ) + 1) := by
  have hj1 : (j : ℕ) + 1 ≤ (symmetricBandPopulations N).length := by
    rw [length_symmetricBandPopulations_eq_tail_succ]
    omega
  rw [show ((concreteReflectBoundaryIndex N j : Fin (bandTailCount N)) : ℕ) + 1 =
        (symmetricBandPopulations N).length - ((j : ℕ) + 1) by
      rw [length_symmetricBandPopulations_eq_tail_succ]
      change bandTailCount N - 1 - (j : ℕ) + 1 =
        bandTailCount N + 1 - ((j : ℕ) + 1)
      omega]
  exact concrete_bandBoundaryHeight_reflect hN hj1

theorem concrete_midpoint_radius_reflect {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) :
    (bemocRingFamily N (Sum.inl (concreteReflectBandIndex N j))).radius =
      (bemocRingFamily N (Sum.inl j)).radius := by
  simp only [OccupiedRing.radius, bemocRingFamily, dif_pos hN]
  rw [concrete_bandMidpointHeight_reflect hN]
  ring_nf

theorem concrete_shared_radius_reflect {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N)) :
    (bemocRingFamily N (Sum.inr (concreteReflectBoundaryIndex N j))).radius =
      (bemocRingFamily N (Sum.inr j)).radius := by
  simp only [OccupiedRing.radius, bemocRingFamily, dif_pos hN]
  rw [concrete_sharedBoundaryHeight_reflect hN]
  ring_nf

/-- Uniform lower population--radius comparison for every literal BEMOC ring.
This includes both polar singleton rings and all midpoint, shared-boundary,
central, and reflected southern rings. -/
theorem concrete_bemocRingFamily_lower_comparison {N : ℕ}
    (hM : 3 ≤ bandCount N) (p : BemocRingIndex N) :
    (bandCount N : ℝ) * (bemocRingFamily N p).radius ≤
      2 * ((bemocRingFamily N p).population : ℝ) := by
  have hN : 0 < N := by
    by_contra hn
    have hz : N = 0 := Nat.eq_zero_of_not_pos hn
    subst N
    norm_num [bandCount] at hM
  rcases p with j | j
  · change (bandCount N : ℝ) * (bemocRingFamily N (Sum.inl j)).radius ≤
      2 * (midpointRingPopulation N j : ℝ)
    by_cases hnorth : (j : ℕ) < bandCount N - 1
    · have h := concrete_midpoint_lower_comparison_north hM j hnorth
      calc
        (bandCount N : ℝ) * (bemocRingFamily N (Sum.inl j)).radius ≤
            (midpointRingPopulation N j : ℝ) := h
        _ ≤ 2 * (midpointRingPopulation N j : ℝ) := by
          have hw : (0 : ℝ) ≤ midpointRingPopulation N j := by positivity
          linarith
    · by_cases hcentral : (j : ℕ) = bandCount N - 1
      · have hj : j = concreteCentralBandIndex N := by
          apply Fin.ext
          simpa [concreteCentralBandIndex] using hcentral
        rw [hj]
        have h := concrete_midpoint_lower_comparison_central (N := N) hM
        calc
          (bandCount N : ℝ) *
                (bemocRingFamily N
                  (Sum.inl (concreteCentralBandIndex N))).radius ≤
              (midpointRingPopulation N (concreteCentralBandIndex N) : ℝ) := h
          _ ≤ 2 *
              (midpointRingPopulation N (concreteCentralBandIndex N) : ℝ) := by
                have hw : (0 : ℝ) ≤
                    midpointRingPopulation N (concreteCentralBandIndex N) := by
                  positivity
                linarith
      · let jr := concreteReflectBandIndex N j
        have hjr : (jr : ℕ) < bandCount N - 1 := by
          dsimp [jr, concreteReflectBandIndex]
          simp only [bandTailCount]
          omega
        calc
          (bandCount N : ℝ) * (bemocRingFamily N (Sum.inl j)).radius =
              (bandCount N : ℝ) *
                (bemocRingFamily N
                  (Sum.inl (concreteReflectBandIndex N j))).radius := by
                    rw [concrete_midpoint_radius_reflect hN]
          _ ≤ (midpointRingPopulation N (concreteReflectBandIndex N j) : ℝ) :=
            concrete_midpoint_lower_comparison_north hM jr hjr
          _ = (midpointRingPopulation N j : ℝ) := by
            rw [concrete_midpointRingPopulation_reflect]
          _ ≤ 2 * (midpointRingPopulation N j : ℝ) := by
            have hw : (0 : ℝ) ≤ midpointRingPopulation N j := by positivity
            linarith
  · change (bandCount N : ℝ) * (bemocRingFamily N (Sum.inr j)).radius ≤
      2 * (sharedBoundaryPopulation N j : ℝ)
    by_cases hnorth : (j : ℕ) < bandCount N - 1
    · exact concrete_boundary_lower_comparison_north hM j hnorth
    · let jr := concreteReflectBoundaryIndex N j
      have hjr : (jr : ℕ) < bandCount N - 1 := by
        dsimp [jr, concreteReflectBoundaryIndex]
        simp only [bandTailCount]
        omega
      calc
        (bandCount N : ℝ) * (bemocRingFamily N (Sum.inr j)).radius =
            (bandCount N : ℝ) *
              (bemocRingFamily N
                (Sum.inr (concreteReflectBoundaryIndex N j))).radius := by
                  rw [concrete_shared_radius_reflect hN]
        _ ≤ 2 *
            (sharedBoundaryPopulation N (concreteReflectBoundaryIndex N j) : ℝ) :=
          concrete_boundary_lower_comparison_north hM jr hjr
        _ = 2 * (sharedBoundaryPopulation N j : ℝ) := by
          rw [concrete_sharedBoundaryPopulation_reflect]

/-- The one elementary concrete geometry package still needed below.
The constants `2` and `8` simultaneously cover midpoint rings, shared
boundary rings, the two singleton polar rings, and the three central rings. -/
structure BemocPopulationRadiusComparison (N : ℕ) : Prop where
  bandCount_pos : 1 ≤ bandCount N
  population_pos : ∀ p : BemocRingIndex N,
    0 < (bemocRingFamily N p).population
  radius_pos : ∀ p : BemocRingIndex N,
    0 < (bemocRingFamily N p).radius
  lower : ∀ p : BemocRingIndex N,
    (bandCount N : ℝ) * (bemocRingFamily N p).radius ≤
      2 * (bemocRingFamily N p).population
  upper : ∀ p : BemocRingIndex N,
    ((bemocRingFamily N p).population : ℝ) ≤
      8 * ((bandCount N : ℝ) * (bemocRingFamily N p).radius)

private theorem weighted_term_le_of_comparison_nonneg
    {α M ρ w : ℝ} (hα : α ≤ 1) (hM : 0 < M) (hρ : 0 < ρ)
    (hw : 0 < w) (hupper : w ≤ 8 * (M * ρ)) :
    ρ ^ α * w ^ (1 - α) ≤
      8 ^ (1 - α) * M ^ (1 - α) * ρ := by
  have hpow := Real.rpow_le_rpow hw.le hupper (sub_nonneg.mpr hα)
  have hρpow : ρ ^ α * ρ ^ (1 - α) = ρ := by
    rw [← Real.rpow_add hρ α (1 - α)]
    rw [show α + (1 - α) = 1 by ring, Real.rpow_one]
  calc
    ρ ^ α * w ^ (1 - α) ≤
        ρ ^ α * (8 * (M * ρ)) ^ (1 - α) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hρ.le α)
    _ = 8 ^ (1 - α) * M ^ (1 - α) * ρ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8)
        (mul_nonneg hM.le hρ.le), Real.mul_rpow hM.le hρ.le]
      calc
        ρ ^ α * (8 ^ (1 - α) * (M ^ (1 - α) * ρ ^ (1 - α))) =
            8 ^ (1 - α) * M ^ (1 - α) *
              (ρ ^ α * ρ ^ (1 - α)) := by ring
        _ = 8 ^ (1 - α) * M ^ (1 - α) * ρ := by rw [hρpow]

private theorem weighted_term_le_of_comparison_nonpos
    {α M ρ w : ℝ} (hα : 1 ≤ α) (hM : 0 < M) (hρ : 0 < ρ)
    (_hw : 0 < w) (hlower : M * ρ ≤ 2 * w) :
    ρ ^ α * w ^ (1 - α) ≤
      (1 / 2 : ℝ) ^ (1 - α) * M ^ (1 - α) * ρ := by
  have hbase : 0 < M * ρ / 2 := by positivity
  have hbase_le : M * ρ / 2 ≤ w := by linarith
  have hpow := Real.rpow_le_rpow_of_nonpos hbase hbase_le (sub_nonpos.mpr hα)
  have hρpow : ρ ^ α * ρ ^ (1 - α) = ρ := by
    rw [← Real.rpow_add hρ α (1 - α)]
    rw [show α + (1 - α) = 1 by ring, Real.rpow_one]
  calc
    ρ ^ α * w ^ (1 - α) ≤
        ρ ^ α * (M * ρ / 2) ^ (1 - α) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hρ.le α)
    _ = (1 / 2 : ℝ) ^ (1 - α) * M ^ (1 - α) * ρ := by
      rw [show M * ρ / 2 = (1 / 2 : ℝ) * (M * ρ) by ring]
      rw [Real.mul_rpow (by norm_num) (mul_nonneg hM.le hρ.le),
        Real.mul_rpow hM.le hρ.le]
      calc
        ρ ^ α * ((1 / 2 : ℝ) ^ (1 - α) *
            (M ^ (1 - α) * ρ ^ (1 - α))) =
            (1 / 2 : ℝ) ^ (1 - α) * M ^ (1 - α) *
              (ρ ^ α * ρ ^ (1 - α)) := by ring
        _ = (1 / 2 : ℝ) ^ (1 - α) * M ^ (1 - α) * ρ := by rw [hρpow]

theorem bandCount_rpow_two_sub_le {N : ℕ} {α : ℝ} (hα2 : α < 2) :
    (bandCount N : ℝ) ^ (2 - α) ≤ (N : ℝ) ^ (1 - α / 2) := by
  have hMN : (bandCount N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    change (Nat.sqrt (N / 4) : ℝ) ≤ Real.sqrt (N : ℝ)
    calc
      (Nat.sqrt (N / 4) : ℝ) ≤ Real.sqrt ((N / 4 : ℕ) : ℝ) :=
        Real.nat_sqrt_le_real_sqrt
      _ ≤ Real.sqrt (N : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.div_le_self N 4)
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hMN
    (sub_nonneg.mpr hα2.le)
  calc
    (bandCount N : ℝ) ^ (2 - α) ≤
        (Real.sqrt (N : ℝ)) ^ (2 - α) := hpow
    _ = (N : ℝ) ^ (1 - α / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1
      ring

noncomputable def bemocWeightedGeometryConstant (α : ℝ) : ℝ :=
  if α ≤ 1 then 4 * 8 ^ (1 - α)
  else 4 * (1 / 2 : ℝ) ^ (1 - α)

theorem bemocWeightedGeometryConstant_pos (α : ℝ) :
    0 < bemocWeightedGeometryConstant α := by
  rw [bemocWeightedGeometryConstant]
  split_ifs <;> positivity

theorem bemocWeightedRadiusPopulationSum_le_of_comparison
    {N : ℕ} {α : ℝ} (_hα0 : 0 < α) (hα2 : α < 2)
    (hgeom : BemocPopulationRadiusComparison N) :
    bemocWeightedRadiusPopulationSum α N ≤
      bemocWeightedGeometryConstant α * (N : ℝ) ^ (1 - α / 2) := by
  have hM : (0 : ℝ) < bandCount N := by exact_mod_cast hgeom.bandCount_pos
  have hsumRadius := sum_bemoc_radius_le_four_mul hgeom.bandCount_pos
  by_cases hαone : α ≤ 1
  · let K : ℝ := 8 ^ (1 - α)
    have hK : 0 < K := by dsimp [K]; positivity
    rw [bemocWeightedGeometryConstant, if_pos hαone]
    change bemocWeightedRadiusPopulationSum α N ≤
      (4 * K) * (N : ℝ) ^ (1 - α / 2)
    have hterm (p : BemocRingIndex N) :
        (bemocRingFamily N p).radius ^ α *
            ((bemocRingFamily N p).population : ℝ) ^ (1 - α) ≤
          K * (bandCount N : ℝ) ^ (1 - α) *
            (bemocRingFamily N p).radius := by
      apply weighted_term_le_of_comparison_nonneg hαone hM
        (hgeom.radius_pos p)
      · exact_mod_cast hgeom.population_pos p
      · exact hgeom.upper p
    have hsum : bemocWeightedRadiusPopulationSum α N ≤
        K * (bandCount N : ℝ) ^ (1 - α) *
          (4 * bandCount N) := by
      unfold bemocWeightedRadiusPopulationSum
      calc
        ∑ p : BemocRingIndex N, (bemocRingFamily N p).radius ^ α *
              ((bemocRingFamily N p).population : ℝ) ^ (1 - α) ≤
            ∑ p : BemocRingIndex N,
              K * (bandCount N : ℝ) ^ (1 - α) *
                (bemocRingFamily N p).radius :=
          Finset.sum_le_sum fun p _ ↦ hterm p
        _ = K * (bandCount N : ℝ) ^ (1 - α) *
              ∑ p : BemocRingIndex N, (bemocRingFamily N p).radius := by
          rw [Finset.mul_sum]
        _ ≤ K * (bandCount N : ℝ) ^ (1 - α) *
              (4 * bandCount N) := by
          exact mul_le_mul_of_nonneg_left hsumRadius
            (mul_nonneg hK.le (Real.rpow_nonneg hM.le _))
    have hMpow : (bandCount N : ℝ) ^ (1 - α) * bandCount N =
        (bandCount N : ℝ) ^ (2 - α) := by
      calc
        (bandCount N : ℝ) ^ (1 - α) * bandCount N =
            (bandCount N : ℝ) ^ (1 - α) *
              (bandCount N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (bandCount N : ℝ) ^ ((1 - α) + 1) :=
          (Real.rpow_add hM (1 - α) 1).symm
        _ = (bandCount N : ℝ) ^ (2 - α) := by ring_nf
    calc
      bemocWeightedRadiusPopulationSum α N ≤
          K * (bandCount N : ℝ) ^ (1 - α) * (4 * bandCount N) := hsum
      _ = (4 * K) * (bandCount N : ℝ) ^ (2 - α) := by rw [← hMpow]; ring
      _ ≤ (4 * K) * (N : ℝ) ^ (1 - α / 2) :=
        mul_le_mul_of_nonneg_left (bandCount_rpow_two_sub_le hα2) (by positivity)
  · have hαone' : 1 ≤ α := le_of_not_ge hαone
    let K : ℝ := (1 / 2 : ℝ) ^ (1 - α)
    have hK : 0 < K := by dsimp [K]; positivity
    rw [bemocWeightedGeometryConstant, if_neg hαone]
    change bemocWeightedRadiusPopulationSum α N ≤
      (4 * K) * (N : ℝ) ^ (1 - α / 2)
    have hterm (p : BemocRingIndex N) :
        (bemocRingFamily N p).radius ^ α *
            ((bemocRingFamily N p).population : ℝ) ^ (1 - α) ≤
          K * (bandCount N : ℝ) ^ (1 - α) *
            (bemocRingFamily N p).radius := by
      apply weighted_term_le_of_comparison_nonpos hαone' hM
        (hgeom.radius_pos p)
      · exact_mod_cast hgeom.population_pos p
      · exact hgeom.lower p
    have hsum : bemocWeightedRadiusPopulationSum α N ≤
        K * (bandCount N : ℝ) ^ (1 - α) *
          (4 * bandCount N) := by
      unfold bemocWeightedRadiusPopulationSum
      calc
        ∑ p : BemocRingIndex N, (bemocRingFamily N p).radius ^ α *
              ((bemocRingFamily N p).population : ℝ) ^ (1 - α) ≤
            ∑ p : BemocRingIndex N,
              K * (bandCount N : ℝ) ^ (1 - α) *
                (bemocRingFamily N p).radius :=
          Finset.sum_le_sum fun p _ ↦ hterm p
        _ = K * (bandCount N : ℝ) ^ (1 - α) *
              ∑ p : BemocRingIndex N, (bemocRingFamily N p).radius := by
          rw [Finset.mul_sum]
        _ ≤ K * (bandCount N : ℝ) ^ (1 - α) *
              (4 * bandCount N) := by
          exact mul_le_mul_of_nonneg_left hsumRadius
            (mul_nonneg hK.le (Real.rpow_nonneg hM.le _))
    have hMpow : (bandCount N : ℝ) ^ (1 - α) * bandCount N =
        (bandCount N : ℝ) ^ (2 - α) := by
      calc
        (bandCount N : ℝ) ^ (1 - α) * bandCount N =
            (bandCount N : ℝ) ^ (1 - α) *
              (bandCount N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (bandCount N : ℝ) ^ ((1 - α) + 1) :=
          (Real.rpow_add hM (1 - α) 1).symm
        _ = (bandCount N : ℝ) ^ (2 - α) := by ring_nf
    calc
      bemocWeightedRadiusPopulationSum α N ≤
          K * (bandCount N : ℝ) ^ (1 - α) * (4 * bandCount N) := hsum
      _ = (4 * K) * (bandCount N : ℝ) ^ (2 - α) := by rw [← hMpow]; ring
      _ ≤ (4 * K) * (N : ℝ) ^ (1 - α / 2) :=
        mul_le_mul_of_nonneg_left (bandCount_rpow_two_sub_le hα2) (by positivity)

theorem bemocWeightedRadiusPopulationSum_eventual_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N₀ : ℕ} (hgeom : ∀ N ≥ N₀, BemocPopulationRadiusComparison N) :
    ∀ N ≥ N₀, bemocWeightedRadiusPopulationSum α N ≤
      bemocWeightedGeometryConstant α * (N : ℝ) ^ (1 - α / 2) := by
  intro N hN
  exact bemocWeightedRadiusPopulationSum_le_of_comparison hα0 hα2 (hgeom N hN)

/-! ## Unconditional concrete estimate -/

/-- A coarse converse to `4 M² ≤ N`, sufficient for the low-exponent
weighted AM--GM argument. -/
theorem N_le_sixteen_bandCount_sq {N : ℕ} (hM : 2 ≤ bandCount N) :
    N ≤ 16 * bandCount N ^ 2 := by
  have hsqrt : N / 4 < (bandCount N + 1) ^ 2 := by
    simpa [bandCount, pow_two] using Nat.lt_succ_sqrt (N / 4)
  have hrem : N < 4 * (N / 4 + 1) := by omega
  have hupper : N < 4 * (bandCount N + 1) ^ 2 := by omega
  nlinarith

theorem three_le_bandCount_of_36_le {N : ℕ} (hN : 36 ≤ N) :
    3 ≤ bandCount N := by
  rw [bandCount, Nat.le_sqrt]
  omega

private theorem low_alpha_scaled_ring_term {α M : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hM : 0 ≤ M)
    (R : OccupiedRing) :
    M ^ α * (R.radius ^ α * (R.population : ℝ) ^ (1 - α)) ≤
      α * (M * R.radius) + (1 - α) * R.population := by
  have hamgm := Real.geom_mean_le_arith_mean2_weighted
    hα0 (sub_nonneg.mpr hα1)
    (mul_nonneg hM R.radius_nonneg) (by positivity : 0 ≤ (R.population : ℝ))
    (by ring : α + (1 - α) = 1)
  rw [Real.mul_rpow hM R.radius_nonneg] at hamgm
  calc
    M ^ α * (R.radius ^ α * (R.population : ℝ) ^ (1 - α)) =
        (M ^ α * R.radius ^ α) * (R.population : ℝ) ^ (1 - α) := by ring
    _ ≤ _ := hamgm

private theorem low_alpha_scaled_weighted_sum {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (N : ℕ) :
    (bandCount N : ℝ) ^ α * bemocWeightedRadiusPopulationSum α N ≤
      α * (bandCount N : ℝ) *
          (∑ p, (bemocRingFamily N p).radius) +
        (1 - α) * N := by
  unfold bemocWeightedRadiusPopulationSum
  rw [Finset.mul_sum]
  calc
    ∑ p, (bandCount N : ℝ) ^ α *
          ((bemocRingFamily N p).radius ^ α *
            ((bemocRingFamily N p).population : ℝ) ^ (1 - α)) ≤
        ∑ p, (α * ((bandCount N : ℝ) * (bemocRingFamily N p).radius) +
          (1 - α) * (bemocRingFamily N p).population) :=
      Finset.sum_le_sum fun p _ ↦
        low_alpha_scaled_ring_term hα0 hα1 (by positivity) _
    _ = α * (bandCount N : ℝ) *
          (∑ p, (bemocRingFamily N p).radius) +
        (1 - α) * N := by
      rw [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
      rw [show (∑ p, ((bemocRingFamily N p).population : ℝ)) = N by
        exact_mod_cast sum_bemocRingFamily_population N]
      ring

private theorem low_alpha_weighted_sum_le {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) {N : ℕ}
    (hM : 2 ≤ bandCount N) :
    bemocWeightedRadiusPopulationSum α N ≤
      20 * (bandCount N : ℝ) ^ (2 - α) := by
  let M : ℝ := bandCount N
  have hMpos : 0 < M := by
    dsimp [M]
    exact_mod_cast (show 0 < bandCount N by omega)
  have hscaled := low_alpha_scaled_weighted_sum hα0.le hα1 N
  have hradius := sum_bemoc_radius_le_four_mul (N := N) (by omega)
  have hN := N_le_sixteen_bandCount_sq hM
  have hrhs :
      α * M * (∑ p, (bemocRingFamily N p).radius) + (1 - α) * N ≤
        20 * M ^ 2 := by
    have hαnonneg : 0 ≤ α := hα0.le
    have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα1
    have hradius' : (∑ p, (bemocRingFamily N p).radius) ≤ 4 * M := by
      simpa [M] using hradius
    have hN' : (N : ℝ) ≤ 16 * M ^ 2 := by
      dsimp [M]
      exact_mod_cast hN
    have hfirst : α * M * (∑ p, (bemocRingFamily N p).radius) ≤
        α * M * (4 * M) :=
      mul_le_mul_of_nonneg_left hradius' (mul_nonneg hαnonneg hMpos.le)
    have hsecond : (1 - α) * (N : ℝ) ≤ (1 - α) * (16 * M ^ 2) :=
      mul_le_mul_of_nonneg_left hN' h1α
    nlinarith [sq_nonneg M]
  have hscaled' : M ^ α * bemocWeightedRadiusPopulationSum α N ≤ 20 * M ^ 2 :=
    le_trans hscaled hrhs
  have hpow : M ^ α * (20 * M ^ (2 - α)) = 20 * M ^ 2 := by
    calc
      M ^ α * (20 * M ^ (2 - α)) =
          20 * (M ^ α * M ^ (2 - α)) := by ring
      _ = 20 * M ^ (α + (2 - α)) := by rw [← Real.rpow_add hMpos]
      _ = 20 * M ^ (2 : ℝ) := by ring_nf
      _ = 20 * M ^ (2 : ℕ) :=
        congrArg (fun x : ℝ ↦ 20 * x) (Real.rpow_natCast M 2)
  rw [← hpow] at hscaled'
  exact (mul_le_mul_left (Real.rpow_pos_of_pos hMpos α)).mp hscaled'

private theorem low_alpha_weighted_sum_N_bound {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) {N : ℕ}
    (hM : 2 ≤ bandCount N) :
    bemocWeightedRadiusPopulationSum α N ≤
      20 * (N : ℝ) ^ (1 - α / 2) := by
  exact (low_alpha_weighted_sum_le hα0 hα1 hM).trans
    (mul_le_mul_of_nonneg_left
      (bandCount_rpow_two_sub_le (lt_of_le_of_lt hα1 (by norm_num)))
      (by norm_num))

private theorem high_alpha_ring_term {α M ρ w : ℝ}
    (hα : 1 ≤ α) (hM : 0 < M) (hρ : 0 ≤ ρ) (_hw : 0 < w)
    (hcomparison : M * ρ ≤ 2 * w) :
    ρ ^ α * w ^ (1 - α) ≤
      (1 / 2 : ℝ) ^ (1 - α) * M ^ (1 - α) * ρ := by
  by_cases hρ0 : ρ = 0
  · subst ρ
    simp [Real.zero_rpow (lt_of_lt_of_le (by norm_num) hα).ne']
  · have hρpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hρ0)
    have hbase : 0 < M * ρ / 2 := by positivity
    have hbase_le : M * ρ / 2 ≤ w := by linarith
    have hpow := Real.rpow_le_rpow_of_nonpos hbase hbase_le
      (sub_nonpos.mpr hα)
    have hρpow : ρ ^ α * ρ ^ (1 - α) = ρ := by
      rw [← Real.rpow_add hρpos α (1 - α)]
      rw [show α + (1 - α) = 1 by ring, Real.rpow_one]
    calc
      ρ ^ α * w ^ (1 - α) ≤
          ρ ^ α * (M * ρ / 2) ^ (1 - α) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hρ α)
      _ = (1 / 2 : ℝ) ^ (1 - α) * M ^ (1 - α) * ρ := by
        rw [show M * ρ / 2 = (1 / 2 : ℝ) * (M * ρ) by ring]
        rw [Real.mul_rpow (by norm_num) (mul_nonneg hM.le hρ),
          Real.mul_rpow hM.le hρ]
        calc
          ρ ^ α * ((1 / 2 : ℝ) ^ (1 - α) *
              (M ^ (1 - α) * ρ ^ (1 - α))) =
              (1 / 2 : ℝ) ^ (1 - α) * M ^ (1 - α) *
                (ρ ^ α * ρ ^ (1 - α)) := by ring
          _ = _ := by rw [hρpow]

private theorem high_alpha_weighted_sum_N_bound {α : ℝ}
    (hα1 : 1 ≤ α) (hα2 : α < 2) {N : ℕ}
    (hM : 3 ≤ bandCount N) :
    bemocWeightedRadiusPopulationSum α N ≤
      (4 * (1 / 2 : ℝ) ^ (1 - α)) *
        (N : ℝ) ^ (1 - α / 2) := by
  let M : ℝ := bandCount N
  let K : ℝ := (1 / 2 : ℝ) ^ (1 - α)
  have hMpos : 0 < M := by
    dsimp [M]
    exact_mod_cast (show 0 < bandCount N by omega)
  have hK : 0 < K := by dsimp [K]; positivity
  have hterm (p : BemocRingIndex N) :
      (bemocRingFamily N p).radius ^ α *
          ((bemocRingFamily N p).population : ℝ) ^ (1 - α) ≤
        K * M ^ (1 - α) * (bemocRingFamily N p).radius := by
    apply high_alpha_ring_term hα1 hMpos (bemocRingFamily N p).radius_nonneg
    · exact_mod_cast concrete_bemocRingFamily_population_pos hM p
    · simpa [M] using concrete_bemocRingFamily_lower_comparison hM p
  have hsum : bemocWeightedRadiusPopulationSum α N ≤
      K * M ^ (1 - α) * (4 * M) := by
    unfold bemocWeightedRadiusPopulationSum
    calc
      ∑ p, (bemocRingFamily N p).radius ^ α *
          ((bemocRingFamily N p).population : ℝ) ^ (1 - α) ≤
          ∑ p, K * M ^ (1 - α) * (bemocRingFamily N p).radius :=
        Finset.sum_le_sum fun p _ ↦ hterm p
      _ = K * M ^ (1 - α) *
          ∑ p, (bemocRingFamily N p).radius := by rw [Finset.mul_sum]
      _ ≤ K * M ^ (1 - α) * (4 * M) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [M] using sum_bemoc_radius_le_four_mul (N := N) (by omega))
          (mul_nonneg hK.le (Real.rpow_nonneg hMpos.le _))
  have hMpow : M ^ (1 - α) * M = M ^ (2 - α) := by
    calc
      M ^ (1 - α) * M = M ^ (1 - α) * M ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = M ^ ((1 - α) + 1) := (Real.rpow_add hMpos (1 - α) 1).symm
      _ = M ^ (2 - α) := by ring_nf
  calc
    bemocWeightedRadiusPopulationSum α N ≤ K * M ^ (1 - α) * (4 * M) := hsum
    _ = (4 * K) * M ^ (2 - α) := by rw [← hMpow]; ring
    _ ≤ (4 * K) * (N : ℝ) ^ (1 - α / 2) :=
      mul_le_mul_of_nonneg_left
        (by simpa [M] using bandCount_rpow_two_sub_le (N := N) hα2) (by positivity)

/-- An explicit (non-optimized) constant for the concrete weighted ring sum. -/
noncomputable def concreteWithinRingGeometryConstant (α : ℝ) : ℝ :=
  if α ≤ 1 then 20 else 4 * (1 / 2 : ℝ) ^ (1 - α)

theorem concreteWithinRingGeometryConstant_pos (α : ℝ) :
    0 < concreteWithinRingGeometryConstant α := by
  rw [concreteWithinRingGeometryConstant]
  split_ifs <;> positivity

/-- The concrete estimate missing after within-ring aggregation:
`Σ ρ_p^α w_p^(1-α) = O(N^(1-α/2))`, for the literal BEMOC rings. -/
theorem bemocWeightedRadiusPopulationSum_concrete_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 36 ≤ N) :
    bemocWeightedRadiusPopulationSum α N ≤
      concreteWithinRingGeometryConstant α *
        (N : ℝ) ^ (1 - α / 2) := by
  have hM := three_le_bandCount_of_36_le hN
  by_cases hα1 : α ≤ 1
  · rw [concreteWithinRingGeometryConstant, if_pos hα1]
    exact low_alpha_weighted_sum_N_bound hα0 hα1 (by omega)
  · rw [concreteWithinRingGeometryConstant, if_neg hα1]
    exact high_alpha_weighted_sum_N_bound (le_of_not_ge hα1) hα2 hM

/-- Consequently, the literal BEMOC within-ring deficit has the required
`O(N^(1-α/2))` bound. -/
theorem exists_bemocWithinRingDeficit_concrete_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      |bemocWithinRingDeficit α N| ≤
        C * (N : ℝ) ^ (1 - α / 2) := by
  obtain ⟨C, hC, hweighted⟩ :=
    exists_bemocWithinRingDeficit_weighted_bound hα0 hα2
  refine ⟨C * concreteWithinRingGeometryConstant α,
    mul_pos hC (concreteWithinRingGeometryConstant_pos α), ?_⟩
  intro N hN
  calc
    |bemocWithinRingDeficit α N| ≤ C * bemocWeightedRadiusPopulationSum α N :=
      hweighted N
    _ ≤ C * (concreteWithinRingGeometryConstant α *
        (N : ℝ) ^ (1 - α / 2)) :=
      mul_le_mul_of_nonneg_left
        (bemocWeightedRadiusPopulationSum_concrete_bound hα0 hα2 hN) hC.le
    _ = (C * concreteWithinRingGeometryConstant α) *
        (N : ℝ) ^ (1 - α / 2) := by ring

end BEMOC
