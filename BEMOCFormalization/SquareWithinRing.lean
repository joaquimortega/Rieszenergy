import BEMOCFormalization.ConcreteWithinRing

/-!
# Exact square-subsequence data for the BEMOC within-ring term

This module specializes the literal BEMOC construction to `N = 4 * m^2`.
It records exact cardinality, population, height, and radius identities, together
with elementary bounded-error population formulas intended for the sharp
within-ring Riemann-sum argument.
-/

open scoped BigOperators

namespace BEMOC

/-! ## Band count and global cardinalities -/

@[simp] theorem square_bandCount (m : ℕ) :
    bandCount (4 * m ^ 2) = m := by
  unfold bandCount
  have hdiv : 4 * m ^ 2 / 4 = m ^ 2 := by omega
  rw [hdiv]
  exact Nat.sqrt_eq' m

@[simp] theorem square_bandTailCount (m : ℕ) :
    bandTailCount (4 * m ^ 2) = 2 * (m - 1) := by
  simp [bandTailCount]

@[simp] theorem square_length_symmetricBandPopulations (m : ℕ) :
    (symmetricBandPopulations (4 * m ^ 2)).length = 2 * (m - 1) + 1 := by
  simp

@[simp] theorem square_centralPopulation (m : ℕ) :
    centralPopulation (4 * m ^ 2) = 6 * m - 2 := by
  by_cases hm : m = 0
  · subst m
    simp [centralPopulation]
  have hm1 : 1 ≤ bandCount (4 * m ^ 2) := by simp [Nat.one_le_iff_ne_zero, hm]
  have hd := doubledOrdinaryTotal_closed (4 * m ^ 2) hm1
  have ha := reflectedPopulationTotal_eq (4 * m ^ 2)
  simp only [square_bandCount] at hd
  unfold reflectedPopulationTotal at ha
  rw [hd] at ha
  have hpoly :
      4 * m ^ 2 =
        2 * ((m - 1) * (2 * (m - 1) + 1)) + (6 * m - 2) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    simp only [Nat.succ_sub_one]
    have hsix : 6 * k.succ - 2 = 6 * k + 4 := by omega
    rw [hsix]
    simp only [Nat.succ_eq_add_one]
    ring
  omega

@[simp] theorem square_doubledOrdinaryTotal (m : ℕ) :
    doubledOrdinaryTotal (4 * m ^ 2) = 4 * m ^ 2 - (6 * m - 2) := by
  have h := reflectedPopulationTotal_eq (4 * m ^ 2)
  simp [reflectedPopulationTotal] at h
  omega

/-! ## Exact finite-band populations -/

theorem square_finiteBandPopulation_north {m : ℕ}
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    finiteBandPopulation (4 * m ^ 2) j = 4 * ((j : ℕ) + 1) - 1 := by
  rw [concrete_finiteBandPopulation_north j (by simpa using hj)]
  rfl

theorem square_finiteBandPopulation_north_closed {m : ℕ}
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    finiteBandPopulation (4 * m ^ 2) j = 4 * (j : ℕ) + 3 := by
  rw [square_finiteBandPopulation_north j hj]
  omega

def squareCentralBandIndex (m : ℕ) :
    Fin (bandTailCount (4 * m ^ 2) + 1) :=
  concreteCentralBandIndex (4 * m ^ 2)

@[simp] theorem squareCentralBandIndex_val (m : ℕ) :
    (squareCentralBandIndex m : ℕ) = m - 1 := by
  simp [squareCentralBandIndex, concreteCentralBandIndex]

theorem square_finiteBandPopulation_central {m : ℕ} (hm : 1 ≤ m) :
    finiteBandPopulation (4 * m ^ 2) (squareCentralBandIndex m) = 6 * m - 2 := by
  rw [squareCentralBandIndex,
    concrete_finiteBandPopulation_central (by simpa using hm),
    square_centralPopulation]

def squareReflectBandIndex (m : ℕ)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1)) :
    Fin (bandTailCount (4 * m ^ 2) + 1) :=
  concreteReflectBandIndex (4 * m ^ 2) j

@[simp] theorem squareReflectBandIndex_val (m : ℕ)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1)) :
    (squareReflectBandIndex m j : ℕ) = 2 * (m - 1) - (j : ℕ) := by
  simp [squareReflectBandIndex, concreteReflectBandIndex]

theorem square_finiteBandPopulation_reflect (m : ℕ)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1)) :
    finiteBandPopulation (4 * m ^ 2) (squareReflectBandIndex m j) =
      finiteBandPopulation (4 * m ^ 2) j := by
  simpa [squareReflectBandIndex] using
    (concrete_finiteBandPopulation_reflect (4 * m ^ 2) j).symm

/-! ## Exact split populations -/

theorem square_boundarySixth_north {m : ℕ}
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    boundarySixth (4 * m ^ 2) j = (4 * (j : ℕ) + 3) / 6 := by
  rw [concrete_boundarySixth_north j (by simpa using hj), ordinaryPopulation]
  congr 1

theorem square_midpointRingPopulation_north {m : ℕ}
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    midpointRingPopulation (4 * m ^ 2) j =
      (4 * (j : ℕ) + 3) - 2 * ((4 * (j : ℕ) + 3) / 6) := by
  rw [midpointRingPopulation, square_finiteBandPopulation_north_closed j hj,
    square_boundarySixth_north j hj]

theorem square_sharedBoundaryPopulation_north {m : ℕ}
    (j : Fin (bandTailCount (4 * m ^ 2)))
    (hj : (j : ℕ) < m - 2) :
    sharedBoundaryPopulation (4 * m ^ 2) j =
      (4 * (j : ℕ) + 3) / 6 + (4 * (j : ℕ) + 7) / 6 := by
  have hj0 : ((j.castSucc : Fin (bandTailCount (4 * m ^ 2) + 1)) : ℕ) < m - 1 := by
    simpa using (show (j : ℕ) < m - 1 by omega)
  have hj1 : ((j.succ : Fin (bandTailCount (4 * m ^ 2) + 1)) : ℕ) < m - 1 := by
    simpa using (show (j : ℕ) + 1 < m - 1 by omega)
  rw [sharedBoundaryPopulation, square_boundarySixth_north j.castSucc hj0,
    square_boundarySixth_north j.succ hj1]
  congr 1

theorem square_boundarySixth_central {m : ℕ} (hm : 2 ≤ m) :
    boundarySixth (4 * m ^ 2) (squareCentralBandIndex m) = m - 1 := by
  rw [boundarySixth]
  split_ifs with hend
  · rcases hend with hzero | hlast
    · have hv := congrArg Fin.val hzero
      have hv' : m - 1 = 0 := by simpa using hv
      omega
    · have hv := congrArg Fin.val hlast
      have hv' : m - 1 = 2 * (m - 1) := by simpa using hv
      omega
  · rw [square_finiteBandPopulation_central (by omega)]
    omega

theorem square_midpointRingPopulation_central {m : ℕ} (hm : 2 ≤ m) :
    midpointRingPopulation (4 * m ^ 2) (squareCentralBandIndex m) = 4 * m := by
  rw [midpointRingPopulation, square_finiteBandPopulation_central (by omega),
    square_boundarySixth_central hm]
  omega

def squareNorthCentralBoundaryIndex (m : ℕ) (hm : 2 ≤ m) :
    Fin (bandTailCount (4 * m ^ 2)) :=
  ⟨m - 2, by simp [bandTailCount]; omega⟩

@[simp] theorem squareNorthCentralBoundaryIndex_val (m : ℕ) (hm : 2 ≤ m) :
    (squareNorthCentralBoundaryIndex m hm : ℕ) = m - 2 := rfl

theorem square_sharedBoundaryPopulation_centralAdjacent {m : ℕ} (hm : 2 ≤ m) :
    sharedBoundaryPopulation (4 * m ^ 2) (squareNorthCentralBoundaryIndex m hm) =
      (4 * m - 5) / 6 + (m - 1) := by
  let j := squareNorthCentralBoundaryIndex m hm
  have hjcast :
      ((j.castSucc : Fin (bandTailCount (4 * m ^ 2) + 1)) : ℕ) < m - 1 := by
    change m - 2 < m - 1
    omega
  have hjsucc :
      (j.succ : Fin (bandTailCount (4 * m ^ 2) + 1)) = squareCentralBandIndex m := by
    apply Fin.ext
    rw [Fin.val_succ, squareCentralBandIndex_val]
    dsimp [j, squareNorthCentralBoundaryIndex]
    omega
  rw [sharedBoundaryPopulation, square_boundarySixth_north j.castSucc hjcast,
    hjsucc, square_boundarySixth_central hm]
  change (4 * (m - 2) + 3) / 6 + (m - 1) = (4 * m - 5) / 6 + (m - 1)
  omega

/-! ### Bounded-error versions of the asymptotic populations -/

private theorem midpoint_split_error_nat (d : ℕ) (hd : 1 ≤ d) :
    8 * d ≤ 3 * ((4 * d - 1) - 2 * ((4 * d - 1) / 6)) + 2 ∧
      3 * ((4 * d - 1) - 2 * ((4 * d - 1) / 6)) ≤ 8 * d + 3 := by
  omega

theorem square_midpointRingPopulation_north_error {m : ℕ}
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    |(midpointRingPopulation (4 * m ^ 2) j : ℝ) -
        (8 / 3 : ℝ) * (((j : ℕ) + 1 : ℕ) : ℝ)| ≤ 1 := by
  let d : ℕ := (j : ℕ) + 1
  have herr := midpoint_split_error_nat d (by omega)
  have hpop : midpointRingPopulation (4 * m ^ 2) j =
      (4 * d - 1) - 2 * ((4 * d - 1) / 6) := by
    rw [square_midpointRingPopulation_north j hj]
    dsimp [d]
    congr 2
  rw [hpop]
  change |(((4 * d - 1) - 2 * ((4 * d - 1) / 6) : ℕ) : ℝ) -
      (8 / 3 : ℝ) * (d : ℝ)| ≤ 1
  have hleft : (8 * d : ℝ) ≤
      3 * (((4 * d - 1) - 2 * ((4 * d - 1) / 6) : ℕ) : ℝ) + 2 := by
    exact_mod_cast herr.1
  have hright :
      3 * (((4 * d - 1) - 2 * ((4 * d - 1) / 6) : ℕ) : ℝ) ≤
        8 * d + 3 := by
    exact_mod_cast herr.2
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

private theorem shared_split_error_nat (d : ℕ) (hd : 1 ≤ d) :
    4 * d ≤ 3 * ((4 * d - 1) / 6 + (4 * d + 3) / 6) + 4 ∧
      3 * ((4 * d - 1) / 6 + (4 * d + 3) / 6) ≤ 4 * d + 1 := by
  have hmod1 := Nat.mod_lt (4 * d - 1) (by norm_num : 0 < 6)
  have hmod2 := Nat.mod_lt (4 * d + 3) (by norm_num : 0 < 6)
  have heq1 := Nat.div_add_mod (4 * d - 1) 6
  have heq2 := Nat.div_add_mod (4 * d + 3) 6
  omega

theorem square_sharedBoundaryPopulation_north_error {m : ℕ}
    (j : Fin (bandTailCount (4 * m ^ 2)))
    (hj : (j : ℕ) < m - 2) :
    |(sharedBoundaryPopulation (4 * m ^ 2) j : ℝ) -
        (4 / 3 : ℝ) * (((j : ℕ) + 1 : ℕ) : ℝ)| ≤ 2 := by
  let d : ℕ := (j : ℕ) + 1
  have herr := shared_split_error_nat d (by omega)
  have hpop : sharedBoundaryPopulation (4 * m ^ 2) j =
      (4 * d - 1) / 6 + (4 * d + 3) / 6 := by
    rw [square_sharedBoundaryPopulation_north j hj]
    dsimp [d]
    congr 2
  rw [hpop]
  change |((((4 * d - 1) / 6 + (4 * d + 3) / 6 : ℕ)) : ℝ) -
      (4 / 3 : ℝ) * (d : ℝ)| ≤ 2
  have hleft : (4 * d : ℝ) ≤
      3 * ((((4 * d - 1) / 6 + (4 * d + 3) / 6 : ℕ)) : ℝ) + 4 := by
    exact_mod_cast herr.1
  have hright :
      3 * ((((4 * d - 1) / 6 + (4 * d + 3) / 6 : ℕ)) : ℝ) ≤
        4 * d + 1 := by
    exact_mod_cast herr.2
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

theorem square_midpointRingPopulation_north_normalized_error {m : ℕ}
    (hm : 0 < m) (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    |(midpointRingPopulation (4 * m ^ 2) j : ℝ) / m -
        (8 / 3 : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / m)| ≤ 1 / (m : ℝ) := by
  have h := square_midpointRingPopulation_north_error j hj
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    |(midpointRingPopulation (4 * m ^ 2) j : ℝ) / m -
        (8 / 3 : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / m)| =
        |(midpointRingPopulation (4 * m ^ 2) j : ℝ) -
          (8 / 3 : ℝ) * (((j : ℕ) + 1 : ℕ) : ℝ)| / m := by
            have heq :
                (midpointRingPopulation (4 * m ^ 2) j : ℝ) / m -
                    (8 / 3 : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / m) =
                  ((midpointRingPopulation (4 * m ^ 2) j : ℝ) -
                    (8 / 3 : ℝ) * (((j : ℕ) + 1 : ℕ) : ℝ)) / m := by
              field_simp
              ring
            rw [heq, abs_div, abs_of_pos hmR]
    _ ≤ 1 / (m : ℝ) := (div_le_div_iff_of_pos_right hmR).2 h

theorem square_sharedBoundaryPopulation_north_normalized_error {m : ℕ}
    (hm : 0 < m) (j : Fin (bandTailCount (4 * m ^ 2)))
    (hj : (j : ℕ) < m - 2) :
    |(sharedBoundaryPopulation (4 * m ^ 2) j : ℝ) / m -
        (4 / 3 : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / m)| ≤ 2 / (m : ℝ) := by
  have h := square_sharedBoundaryPopulation_north_error j hj
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    |(sharedBoundaryPopulation (4 * m ^ 2) j : ℝ) / m -
        (4 / 3 : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / m)| =
        |(sharedBoundaryPopulation (4 * m ^ 2) j : ℝ) -
          (4 / 3 : ℝ) * (((j : ℕ) + 1 : ℕ) : ℝ)| / m := by
            have heq :
                (sharedBoundaryPopulation (4 * m ^ 2) j : ℝ) / m -
                    (4 / 3 : ℝ) * ((((j : ℕ) + 1 : ℕ) : ℝ) / m) =
                  ((sharedBoundaryPopulation (4 * m ^ 2) j : ℝ) -
                    (4 / 3 : ℝ) * (((j : ℕ) + 1 : ℕ) : ℝ)) / m := by
              field_simp
              ring
            rw [heq, abs_div, abs_of_pos hmR]
    _ ≤ 2 / (m : ℝ) := (div_le_div_iff_of_pos_right hmR).2 h

/-! ## Exact northern heights -/

theorem square_bandBoundaryHeight_north {m j : ℕ} (hm : 0 < m)
    (hj : j ≤ m - 1) :
    bandBoundaryHeight (4 * m ^ 2) j =
      1 - (j : ℝ) * (2 * (j : ℝ) + 1) / (2 * (m : ℝ) ^ 2) := by
  rw [concrete_bandBoundaryHeight_north (by simpa using hj)]
  push_cast
  field_simp
  ring

theorem square_bandBoundaryHeight_north_normalized {m j : ℕ} (hm : 0 < m)
    (hj : j ≤ m - 1) :
    bandBoundaryHeight (4 * m ^ 2) j =
      1 - ((j : ℝ) / m) ^ 2 - (j : ℝ) / (2 * (m : ℝ) ^ 2) := by
  rw [square_bandBoundaryHeight_north hm hj]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

theorem square_bandMidpointHeight_north {m : ℕ} (_hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    bandMidpointHeight (4 * m ^ 2) j =
      1 - (4 * ((((j : ℕ) + 1 : ℕ) : ℝ)) ^ 2 -
        2 * ((((j : ℕ) + 1 : ℕ) : ℝ)) + 1) / (4 * (m : ℝ) ^ 2) := by
  rw [concrete_bandMidpointHeight_north (by simpa using hj)]
  push_cast
  rfl

theorem square_bandMidpointHeight_north_normalized {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    bandMidpointHeight (4 * m ^ 2) j =
      1 - ((((j : ℕ) + 1 : ℕ) : ℝ) / m) ^ 2 +
        ((((j : ℕ) + 1 : ℕ) : ℝ)) / (2 * (m : ℝ) ^ 2) -
        1 / (4 * (m : ℝ) ^ 2) := by
  rw [square_bandMidpointHeight_north hm j hj]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

theorem square_bandBoundaryHeight_profile_error {m j : ℕ} (hm : 0 < m)
    (hj : j ≤ m - 1) :
    |bandBoundaryHeight (4 * m ^ 2) j -
        (1 - ((j : ℝ) / m) ^ 2)| ≤ 1 / (2 * (m : ℝ)) := by
  rw [square_bandBoundaryHeight_north_normalized hm hj]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hjR : (j : ℝ) ≤ m := by
    exact_mod_cast hj.trans (Nat.sub_le m 1)
  have hden : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  have hfrac : (j : ℝ) / (2 * (m : ℝ) ^ 2) ≤
      (m : ℝ) / (2 * (m : ℝ) ^ 2) :=
    (div_le_div_iff_of_pos_right hden).2 hjR
  rw [show 1 - ((j : ℝ) / m) ^ 2 - (j : ℝ) / (2 * (m : ℝ) ^ 2) -
      (1 - ((j : ℝ) / m) ^ 2) =
      -((j : ℝ) / (2 * (m : ℝ) ^ 2)) by ring,
    abs_neg, abs_of_nonneg (by positivity)]
  calc
    (j : ℝ) / (2 * (m : ℝ) ^ 2) ≤
        (m : ℝ) / (2 * (m : ℝ) ^ 2) := hfrac
    _ = 1 / (2 * (m : ℝ)) := by field_simp; ring

theorem square_bandMidpointHeight_profile_error {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    |bandMidpointHeight (4 * m ^ 2) j -
        (1 - (((((j : ℕ) + 1 : ℕ) : ℝ) / m) ^ 2))| ≤
      1 / (2 * (m : ℝ)) := by
  rw [square_bandMidpointHeight_north_normalized hm j hj]
  let d : ℝ := (((j : ℕ) + 1 : ℕ) : ℝ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hd0 : 0 ≤ d := by positivity
  have hdM : d ≤ (m : ℝ) := by
    dsimp [d]
    exact_mod_cast (show (j : ℕ) + 1 ≤ m by omega)
  have hcorr0 : 0 ≤ d / (2 * (m : ℝ) ^ 2) - 1 / (4 * (m : ℝ) ^ 2) := by
    have hd1 : (1 : ℝ) ≤ d := by dsimp [d]; norm_num
    rw [show d / (2 * (m : ℝ) ^ 2) - 1 / (4 * (m : ℝ) ^ 2) =
        (2 * d - 1) / (4 * (m : ℝ) ^ 2) by field_simp; ring]
    exact div_nonneg (by linarith) (by positivity)
  have hden : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  have hdfrac : d / (2 * (m : ℝ) ^ 2) ≤
      (m : ℝ) / (2 * (m : ℝ) ^ 2) :=
    (div_le_div_iff_of_pos_right hden).2 hdM
  change |(1 - (d / m) ^ 2 + d / (2 * (m : ℝ) ^ 2) -
      1 / (4 * (m : ℝ) ^ 2)) - (1 - (d / m) ^ 2)| ≤ _
  rw [show (1 - (d / m) ^ 2 + d / (2 * (m : ℝ) ^ 2) -
      1 / (4 * (m : ℝ) ^ 2)) - (1 - (d / m) ^ 2) =
      d / (2 * (m : ℝ) ^ 2) - 1 / (4 * (m : ℝ) ^ 2) by ring,
    abs_of_nonneg hcorr0]
  calc
    d / (2 * (m : ℝ) ^ 2) - 1 / (4 * (m : ℝ) ^ 2) ≤
        d / (2 * (m : ℝ) ^ 2) := by
          have : 0 ≤ 1 / (4 * (m : ℝ) ^ 2) := by positivity
          linarith
    _ ≤ (m : ℝ) / (2 * (m : ℝ) ^ 2) := hdfrac
    _ = 1 / (2 * (m : ℝ)) := by field_simp; ring

/-! ## Exact radii -/

/-- Correction factor under the square root for a northern midpoint ring,
with `d = j + 1` and `x = d/m`. -/
noncomputable def squareMidpointRadiusRadicand (m d : ℕ) : ℝ :=
  let x := (d : ℝ) / m
  let q := 1 - 1 / (2 * (d : ℝ)) + 1 / (4 * (d : ℝ) ^ 2)
  q * (2 - x ^ 2 * q)

/-- Correction factor under the square root for a northern shared-boundary
ring, with `d = j + 1` and `x = d/m`. -/
noncomputable def squareBoundaryRadiusRadicand (m d : ℕ) : ℝ :=
  let x := (d : ℝ) / m
  let q := 1 + 1 / (2 * (d : ℝ))
  q * (2 - x ^ 2 * q)

/-- The limiting correction factor in the profile
`rho = (d/m) * sqrt (2 - (d/m)^2)`. -/
noncomputable def squareLimitRadiusFactor (m d : ℕ) : ℝ :=
  Real.sqrt (2 - ((d : ℝ) / m) ^ 2)

private theorem square_midpoint_radicand_bounds {m d : ℕ}
    (hm : 0 < m) (hd : 1 ≤ d) (hdm : d ≤ m) :
    (3 / 4 : ℝ) ≤ squareMidpointRadiusRadicand m d ∧
      squareMidpointRadiusRadicand m d ≤ 2 := by
  let x : ℝ := (d : ℝ) / m
  let u : ℝ := 1 / (d : ℝ)
  let q : ℝ := 1 - u / 2 + u ^ 2 / 4
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hdR
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hmR).2 (by exact_mod_cast hdm)
  have hxsq : x ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg x, mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    exact (div_le_one hdpos).2 hdR
  have hq0 : 0 ≤ q := by
    dsimp [q]
    nlinarith [sq_nonneg (u - 1)]
  have hqLower : (3 / 4 : ℝ) ≤ q := by
    dsimp [q]
    nlinarith [sq_nonneg (u - 1)]
  have hqUpper : q ≤ 1 := by
    have huu : u ^ 2 ≤ u := by
      nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
    dsimp [q]
    nlinarith
  have hy0 : 0 ≤ x ^ 2 * q := mul_nonneg (sq_nonneg x) hq0
  have hy1 : x ^ 2 * q ≤ 1 := by
    calc
      x ^ 2 * q ≤ 1 * q := mul_le_mul_of_nonneg_right hxsq hq0
      _ = q := one_mul q
      _ ≤ 1 := hqUpper
  have hresult : (3 / 4 : ℝ) ≤ q * (2 - x ^ 2 * q) ∧
      q * (2 - x ^ 2 * q) ≤ 2 := by
    have hsecond0 : 0 ≤ 2 - x ^ 2 * q := by linarith
    have hsecond1 : 1 ≤ 2 - x ^ 2 * q := by linarith
    have hsecond2 : 2 - x ^ 2 * q ≤ 2 := by linarith
    constructor
    · calc
        (3 / 4 : ℝ) ≤ q := hqLower
        _ = q * 1 := by ring
        _ ≤ q * (2 - x ^ 2 * q) := mul_le_mul_of_nonneg_left hsecond1 hq0
    · calc
        q * (2 - x ^ 2 * q) ≤ 1 * (2 - x ^ 2 * q) :=
          mul_le_mul_of_nonneg_right hqUpper hsecond0
        _ ≤ 1 * 2 := by gcongr
        _ = 2 := by ring
  simpa [squareMidpointRadiusRadicand, x, q, u] using hresult

private theorem square_boundary_radicand_bounds {m d : ℕ}
    (hm : 0 < m) (hd : 1 ≤ d) (hdm : d < m) :
    (1 : ℝ) ≤ squareBoundaryRadiusRadicand m d ∧
      squareBoundaryRadiusRadicand m d ≤ 3 := by
  let x : ℝ := (d : ℝ) / m
  let u : ℝ := 1 / (d : ℝ)
  let q : ℝ := 1 + u / 2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hdR
  have hdmR : (d : ℝ) + 1 ≤ m := by exact_mod_cast hdm
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    exact (div_le_one hdpos).2 hdR
  have hqLower : 1 ≤ q := by dsimp [q]; linarith
  have hqUpper : q ≤ 3 / 2 := by dsimp [q]; linarith
  have hq0 : 0 ≤ q := le_trans (by norm_num) hqLower
  have hyEq : x ^ 2 * q =
      ((d : ℝ) ^ 2 + (d : ℝ) / 2) / (m : ℝ) ^ 2 := by
    dsimp [x, q, u]
    field_simp
    ring
  have hnum : (d : ℝ) ^ 2 + (d : ℝ) / 2 ≤ (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℝ) - d)]
  have hy0 : 0 ≤ x ^ 2 * q := mul_nonneg (sq_nonneg x) hq0
  have hy1 : x ^ 2 * q ≤ 1 := by
    rw [hyEq]
    exact (div_le_one (sq_pos_of_pos hmR)).2 hnum
  have hresult : (1 : ℝ) ≤ q * (2 - x ^ 2 * q) ∧
      q * (2 - x ^ 2 * q) ≤ 3 := by
    have hsecond0 : 0 ≤ 2 - x ^ 2 * q := by linarith
    have hsecond1 : 1 ≤ 2 - x ^ 2 * q := by linarith
    have hsecond2 : 2 - x ^ 2 * q ≤ 2 := by linarith
    constructor
    · calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ q * 1 := mul_le_mul_of_nonneg_right hqLower (by norm_num)
        _ ≤ q * (2 - x ^ 2 * q) := mul_le_mul_of_nonneg_left hsecond1 hq0
    · calc
        q * (2 - x ^ 2 * q) ≤ (3 / 2 : ℝ) * 2 :=
          mul_le_mul hqUpper hsecond2 hsecond0 (by norm_num)
        _ = 3 := by ring
  simpa [squareBoundaryRadiusRadicand, x, q, u] using hresult

theorem occupiedRing_radius_sq (R : OccupiedRing) :
    R.radius ^ 2 = 1 - R.height ^ 2 := by
  rw [OccupiedRing.radius]
  exact Real.sq_sqrt (by nlinarith [R.height_mem.1, R.height_mem.2])

theorem square_midpoint_radius_factorization {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    (bemocRingFamily (4 * m ^ 2) (Sum.inl j)).radius =
      ((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
        Real.sqrt (squareMidpointRadiusRadicand m ((j : ℕ) + 1)) := by
  let R := bemocRingFamily (4 * m ^ 2) (Sum.inl j)
  let d : ℕ := (j : ℕ) + 1
  let x : ℝ := (d : ℝ) / m
  let q : ℝ := 1 - 1 / (2 * (d : ℝ)) + 1 / (4 * (d : ℝ) ^ 2)
  let A : ℝ := q * (2 - x ^ 2 * q)
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdm : d ≤ m := by dsimp [d]; omega
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hA : 0 ≤ A := by
    have h := (square_midpoint_radicand_bounds hm hd hdm).1
    have hident : A = squareMidpointRadiusRadicand m d := by
      simp [A, squareMidpointRadiusRadicand, x, q]
    rw [hident]
    linarith
  have hheight : R.height = 1 - x ^ 2 * q := by
    dsimp [R]
    simp only [bemocRingFamily, dif_pos (by positivity : 0 < 4 * m ^ 2)]
    rw [square_bandMidpointHeight_north_normalized hm j hj]
    dsimp [x, q, d]
    field_simp
    ring
  have hsq : R.radius ^ 2 = (x * Real.sqrt A) ^ 2 := by
    rw [occupiedRing_radius_sq, hheight, mul_pow, Real.sq_sqrt hA]
    dsimp [A]
    ring
  have heq := (sq_eq_sq₀ R.radius_nonneg
    (mul_nonneg hx0 (Real.sqrt_nonneg A))).mp hsq
  simpa [R, d, x, A, q, squareMidpointRadiusRadicand] using heq

theorem square_boundary_radius_factorization {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2)))
    (hj : (j : ℕ) < m - 1) :
    (bemocRingFamily (4 * m ^ 2) (Sum.inr j)).radius =
      ((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
        Real.sqrt (squareBoundaryRadiusRadicand m ((j : ℕ) + 1)) := by
  let R := bemocRingFamily (4 * m ^ 2) (Sum.inr j)
  let d : ℕ := (j : ℕ) + 1
  let x : ℝ := (d : ℝ) / m
  let q : ℝ := 1 + 1 / (2 * (d : ℝ))
  let A : ℝ := q * (2 - x ^ 2 * q)
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdm : d < m := by dsimp [d]; omega
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hA : 0 ≤ A := by
    have h := (square_boundary_radicand_bounds hm hd hdm).1
    have hident : A = squareBoundaryRadiusRadicand m d := by
      simp [A, squareBoundaryRadiusRadicand, x, q]
    rw [hident]
    linarith
  have hheight : R.height = 1 - x ^ 2 * q := by
    dsimp [R]
    simp only [bemocRingFamily, dif_pos (by positivity : 0 < 4 * m ^ 2)]
    rw [square_bandBoundaryHeight_north_normalized hm
      (by omega : (j : ℕ) + 1 ≤ m - 1)]
    dsimp [x, q, d]
    field_simp
    ring
  have hsq : R.radius ^ 2 = (x * Real.sqrt A) ^ 2 := by
    rw [occupiedRing_radius_sq, hheight, mul_pow, Real.sq_sqrt hA]
    dsimp [A]
    ring
  have heq := (sq_eq_sq₀ R.radius_nonneg
    (mul_nonneg hx0 (Real.sqrt_nonneg A))).mp hsq
  simpa [R, d, x, A, q, squareBoundaryRadiusRadicand] using heq

theorem square_midpoint_radius_ratio_bounds {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    (1 / 2 : ℝ) ≤
        (bemocRingFamily (4 * m ^ 2) (Sum.inl j)).radius /
          (((((j : ℕ) + 1 : ℕ) : ℝ) / m)) ∧
      (bemocRingFamily (4 * m ^ 2) (Sum.inl j)).radius /
          (((((j : ℕ) + 1 : ℕ) : ℝ) / m)) ≤ 2 := by
  let d : ℕ := (j : ℕ) + 1
  let A := squareMidpointRadiusRadicand m d
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdm : d ≤ m := by dsimp [d]; omega
  have hxpos : 0 < (d : ℝ) / m := by positivity
  have hA := square_midpoint_radicand_bounds hm hd hdm
  have hl : (1 / 2 : ℝ) ≤ Real.sqrt A := by
    apply Real.le_sqrt_of_sq_le
    dsimp [A]
    nlinarith
  have hu : Real.sqrt A ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  rw [square_midpoint_radius_factorization hm j hj]
  change (1 / 2 : ℝ) ≤ (((d : ℝ) / m) * Real.sqrt A) / ((d : ℝ) / m) ∧
    (((d : ℝ) / m) * Real.sqrt A) / ((d : ℝ) / m) ≤ 2
  rw [mul_div_cancel_left₀ _ hxpos.ne']
  exact ⟨hl, hu⟩

theorem square_boundary_radius_ratio_bounds {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2)))
    (hj : (j : ℕ) < m - 1) :
    (1 : ℝ) ≤
        (bemocRingFamily (4 * m ^ 2) (Sum.inr j)).radius /
          (((((j : ℕ) + 1 : ℕ) : ℝ) / m)) ∧
      (bemocRingFamily (4 * m ^ 2) (Sum.inr j)).radius /
          (((((j : ℕ) + 1 : ℕ) : ℝ) / m)) ≤ 2 := by
  let d : ℕ := (j : ℕ) + 1
  let A := squareBoundaryRadiusRadicand m d
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdm : d < m := by dsimp [d]; omega
  have hxpos : 0 < (d : ℝ) / m := by positivity
  have hA := square_boundary_radicand_bounds hm hd hdm
  have hl : (1 : ℝ) ≤ Real.sqrt A := by
    apply Real.le_sqrt_of_sq_le
    dsimp [A]
    nlinarith
  have hu : Real.sqrt A ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  rw [square_boundary_radius_factorization hm j hj]
  change (1 : ℝ) ≤ (((d : ℝ) / m) * Real.sqrt A) / ((d : ℝ) / m) ∧
    (((d : ℝ) / m) * Real.sqrt A) / ((d : ℝ) / m) ≤ 2
  rw [mul_div_cancel_left₀ _ hxpos.ne']
  exact ⟨hl, hu⟩

private theorem abs_sqrt_sub_sqrt_le_abs_sub {A B : ℝ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) :
    |Real.sqrt A - Real.sqrt B| ≤ |A - B| := by
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hsB : (1 : ℝ) ≤ Real.sqrt B := by
    exact Real.le_sqrt_of_sq_le (by norm_num [hB])
  have hsum1 : (1 : ℝ) ≤ Real.sqrt A + Real.sqrt B := by
    linarith [Real.sqrt_nonneg A]
  have hsum0 : 0 ≤ Real.sqrt A + Real.sqrt B := by linarith
  calc
    |Real.sqrt A - Real.sqrt B| ≤
        |Real.sqrt A - Real.sqrt B| * (Real.sqrt A + Real.sqrt B) :=
      le_mul_of_one_le_right (abs_nonneg _) hsum1
    _ = |(Real.sqrt A - Real.sqrt B) *
        (Real.sqrt A + Real.sqrt B)| := by
      rw [abs_mul, abs_of_nonneg hsum0]
    _ = |A - B| := by
      congr 1
      calc
        (Real.sqrt A - Real.sqrt B) * (Real.sqrt A + Real.sqrt B) =
            Real.sqrt A ^ 2 - Real.sqrt B ^ 2 := by ring
        _ = A - B := by rw [Real.sq_sqrt hA, Real.sq_sqrt hB0]

private theorem square_midpoint_radicand_error {m d : ℕ}
    (hm : 0 < m) (hd : 1 ≤ d) (hdm : d ≤ m) :
    |squareMidpointRadiusRadicand m d -
        (2 - ((d : ℝ) / m) ^ 2)| ≤ 1 / (d : ℝ) := by
  let x : ℝ := (d : ℝ) / m
  let u : ℝ := 1 / (d : ℝ)
  let q : ℝ := 1 - u / 2 + u ^ 2 / 4
  let F : ℝ := 2 - x ^ 2 * (q + 1)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hdR
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hmR).2 (by exact_mod_cast hdm)
  have hxsq0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hxsq1 : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    exact (div_le_one hdpos).2 hdR
  have hq0 : 0 ≤ q := by dsimp [q]; nlinarith [sq_nonneg (u - 1)]
  have hq1 : q ≤ 1 := by
    have huu : u ^ 2 ≤ u := by
      nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
    dsimp [q]
    nlinarith
  have hdelta0 : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hdelta : 1 - q ≤ u / 2 := by dsimp [q]; nlinarith [sq_nonneg u]
  have hqsum0 : 0 ≤ q + 1 := by linarith
  have hqsum2 : q + 1 ≤ 2 := by linarith
  have hxq : x ^ 2 * (q + 1) ≤ 2 := by
    calc
      x ^ 2 * (q + 1) ≤ 1 * (q + 1) :=
        mul_le_mul_of_nonneg_right hxsq1 hqsum0
      _ ≤ 1 * 2 := by gcongr
      _ = 2 := by ring
  have hF0 : 0 ≤ F := by dsimp [F]; linarith
  have hF2 : F ≤ 2 := by
    dsimp [F]
    nlinarith [mul_nonneg hxsq0 hqsum0]
  have hprod0 : 0 ≤ (1 - q) * F := mul_nonneg hdelta0 hF0
  have hprod : (1 - q) * F ≤ u := by
    calc
      (1 - q) * F ≤ (u / 2) * F := mul_le_mul_of_nonneg_right hdelta hF0
      _ ≤ (u / 2) * 2 := mul_le_mul_of_nonneg_left hF2 (by positivity)
      _ = u := by ring
  have hid : q * (2 - x ^ 2 * q) - (2 - x ^ 2) = -(1 - q) * F := by
    dsimp [F]
    ring
  have hresult : |q * (2 - x ^ 2 * q) - (2 - x ^ 2)| ≤ u := by
    rw [hid, show -(1 - q) * F = -((1 - q) * F) by ring,
      abs_neg, abs_of_nonneg hprod0]
    exact hprod
  simpa [squareMidpointRadiusRadicand, x, q, u] using hresult

private theorem square_boundary_radicand_error {m d : ℕ}
    (hm : 0 < m) (hd : 1 ≤ d) (hdm : d < m) :
    |squareBoundaryRadiusRadicand m d -
        (2 - ((d : ℝ) / m) ^ 2)| ≤ 1 / (d : ℝ) := by
  let x : ℝ := (d : ℝ) / m
  let u : ℝ := 1 / (d : ℝ)
  let q : ℝ := 1 + u / 2
  let F : ℝ := 2 - x ^ 2 * (q + 1)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hdR
  have hdmR : (d : ℝ) + 1 ≤ m := by exact_mod_cast hdm
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hmR).2 (by exact_mod_cast Nat.le_of_lt hdm)
  have hxsq0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hxsq1 : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    exact (div_le_one hdpos).2 hdR
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hyEq : x ^ 2 * q =
      ((d : ℝ) ^ 2 + (d : ℝ) / 2) / (m : ℝ) ^ 2 := by
    dsimp [x, q, u]
    field_simp
    ring
  have hnum : (d : ℝ) ^ 2 + (d : ℝ) / 2 ≤ (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℝ) - d)]
  have hy1 : x ^ 2 * q ≤ 1 := by
    rw [hyEq]
    exact (div_le_one (sq_pos_of_pos hmR)).2 hnum
  have hqsum0 : 0 ≤ q + 1 := by linarith
  have hxq : x ^ 2 * (q + 1) ≤ 2 := by
    rw [mul_add]
    nlinarith
  have hF0 : 0 ≤ F := by dsimp [F]; linarith
  have hF2 : F ≤ 2 := by
    dsimp [F]
    nlinarith [mul_nonneg hxsq0 hqsum0]
  have hdelta0 : 0 ≤ q - 1 := by dsimp [q]; linarith
  have hdelta : q - 1 = u / 2 := by dsimp [q]; ring
  have hprod0 : 0 ≤ (q - 1) * F := mul_nonneg hdelta0 hF0
  have hprod : (q - 1) * F ≤ u := by
    rw [hdelta]
    calc
      (u / 2) * F ≤ (u / 2) * 2 := mul_le_mul_of_nonneg_left hF2 (by positivity)
      _ = u := by ring
  have hid : q * (2 - x ^ 2 * q) - (2 - x ^ 2) = (q - 1) * F := by
    dsimp [F]
    ring
  have hresult : |q * (2 - x ^ 2 * q) - (2 - x ^ 2)| ≤ u := by
    rw [hid, abs_of_nonneg hprod0]
    exact hprod
  simpa [squareBoundaryRadiusRadicand, x, q, u] using hresult

theorem square_midpoint_radius_factor_error {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    abs ((bemocRingFamily (4 * m ^ 2) (Sum.inl j)).radius /
          (((((j : ℕ) + 1 : ℕ) : ℝ) / m)) -
        squareLimitRadiusFactor m ((j : ℕ) + 1)) ≤
      1 / ((((j : ℕ) + 1 : ℕ) : ℝ)) := by
  let d : ℕ := (j : ℕ) + 1
  let A := squareMidpointRadiusRadicand m d
  let B : ℝ := 2 - ((d : ℝ) / m) ^ 2
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdm : d ≤ m := by dsimp [d]; omega
  have hxpos : 0 < (d : ℝ) / m := by positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith [(square_midpoint_radicand_bounds hm hd hdm).1]
  have hB : 1 ≤ B := by
    dsimp [B]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hdmR : (d : ℝ) ≤ m := by exact_mod_cast hdm
    have hx : (d : ℝ) / m ≤ 1 := (div_le_one hmR).2 hdmR
    have hx0 : 0 ≤ (d : ℝ) / m := by positivity
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hsqrt := abs_sqrt_sub_sqrt_le_abs_sub hA hB
  have hrad := square_midpoint_radicand_error hm hd hdm
  rw [square_midpoint_radius_factorization hm j hj]
  change |(((d : ℝ) / m) * Real.sqrt A) / ((d : ℝ) / m) -
      Real.sqrt B| ≤ 1 / (d : ℝ)
  rw [mul_div_cancel_left₀ _ hxpos.ne']
  exact hsqrt.trans hrad

theorem square_boundary_radius_factor_error {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2)))
    (hj : (j : ℕ) < m - 1) :
    abs ((bemocRingFamily (4 * m ^ 2) (Sum.inr j)).radius /
          (((((j : ℕ) + 1 : ℕ) : ℝ) / m)) -
        squareLimitRadiusFactor m ((j : ℕ) + 1)) ≤
      1 / ((((j : ℕ) + 1 : ℕ) : ℝ)) := by
  let d : ℕ := (j : ℕ) + 1
  let A := squareBoundaryRadiusRadicand m d
  let B : ℝ := 2 - ((d : ℝ) / m) ^ 2
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdm : d < m := by dsimp [d]; omega
  have hxpos : 0 < (d : ℝ) / m := by positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith [(square_boundary_radicand_bounds hm hd hdm).1]
  have hB : 1 ≤ B := by
    dsimp [B]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hdmR : (d : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt hdm
    have hx : (d : ℝ) / m ≤ 1 := (div_le_one hmR).2 hdmR
    have hx0 : 0 ≤ (d : ℝ) / m := by positivity
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hsqrt := abs_sqrt_sub_sqrt_le_abs_sub hA hB
  have hrad := square_boundary_radicand_error hm hd hdm
  rw [square_boundary_radius_factorization hm j hj]
  change |(((d : ℝ) / m) * Real.sqrt A) / ((d : ℝ) / m) -
      Real.sqrt B| ≤ 1 / (d : ℝ)
  rw [mul_div_cancel_left₀ _ hxpos.ne']
  exact hsqrt.trans hrad

theorem square_midpoint_radius_factor_error_coarse {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    abs ((bemocRingFamily (4 * m ^ 2) (Sum.inl j)).radius /
          (((((j : ℕ) + 1 : ℕ) : ℝ) / m)) -
        squareLimitRadiusFactor m ((j : ℕ) + 1)) ≤
      1 / ((((j : ℕ) + 1 : ℕ) : ℝ)) + 1 / (m : ℝ) :=
  (square_midpoint_radius_factor_error hm j hj).trans
    (le_add_of_nonneg_right (by positivity))

theorem square_boundary_radius_factor_error_coarse {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2)))
    (hj : (j : ℕ) < m - 1) :
    abs ((bemocRingFamily (4 * m ^ 2) (Sum.inr j)).radius /
          (((((j : ℕ) + 1 : ℕ) : ℝ) / m)) -
        squareLimitRadiusFactor m ((j : ℕ) + 1)) ≤
      1 / ((((j : ℕ) + 1 : ℕ) : ℝ)) + 1 / (m : ℝ) :=
  (square_boundary_radius_factor_error hm j hj).trans
    (le_add_of_nonneg_right (by positivity))

theorem square_midpointRing_radius_north {m : ℕ} (_hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    (bemocRingFamily (4 * m ^ 2) (Sum.inl j)).radius =
      Real.sqrt (1 - (1 - (4 * ((((j : ℕ) + 1 : ℕ) : ℝ)) ^ 2 -
        2 * ((((j : ℕ) + 1 : ℕ) : ℝ)) + 1) / (4 * (m : ℝ) ^ 2)) ^ 2) := by
  rw [OccupiedRing.radius]
  simp only [bemocRingFamily, dif_pos (by positivity : 0 < 4 * m ^ 2)]
  rw [square_bandMidpointHeight_north _hm j hj]

theorem square_sharedBoundary_radius_north {m : ℕ} (_hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2)))
    (hj : (j : ℕ) < m - 1) :
    (bemocRingFamily (4 * m ^ 2) (Sum.inr j)).radius =
      Real.sqrt (1 - (1 - ((((j : ℕ) + 1 : ℕ) : ℝ) *
        (2 * ((((j : ℕ) + 1 : ℕ) : ℝ)) + 1)) /
          (2 * (m : ℝ) ^ 2)) ^ 2) := by
  rw [OccupiedRing.radius]
  simp only [bemocRingFamily, dif_pos (by positivity : 0 < 4 * m ^ 2)]
  rw [square_bandBoundaryHeight_north _hm (by omega : (j : ℕ) + 1 ≤ m - 1)]

theorem square_midpointRing_radius_sq_north {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1))
    (hj : (j : ℕ) < m - 1) :
    (bemocRingFamily (4 * m ^ 2) (Sum.inl j)).radius ^ 2 =
      1 - (1 - (4 * ((((j : ℕ) + 1 : ℕ) : ℝ)) ^ 2 -
        2 * ((((j : ℕ) + 1 : ℕ) : ℝ)) + 1) / (4 * (m : ℝ) ^ 2)) ^ 2 := by
  have hN : 0 < 4 * m ^ 2 := by positivity
  rw [occupiedRing_radius_sq]
  simp only [bemocRingFamily, dif_pos hN]
  rw [square_bandMidpointHeight_north hm j hj]

theorem square_sharedBoundary_radius_sq_north {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2)))
    (hj : (j : ℕ) < m - 1) :
    (bemocRingFamily (4 * m ^ 2) (Sum.inr j)).radius ^ 2 =
      1 - (1 - ((((j : ℕ) + 1 : ℕ) : ℝ) *
        (2 * ((((j : ℕ) + 1 : ℕ) : ℝ)) + 1)) /
          (2 * (m : ℝ) ^ 2)) ^ 2 := by
  have hN : 0 < 4 * m ^ 2 := by positivity
  rw [occupiedRing_radius_sq]
  simp only [bemocRingFamily, dif_pos hN]
  rw [square_bandBoundaryHeight_north hm (by omega : (j : ℕ) + 1 ≤ m - 1)]

/-! ## Square-specific north--south reflection wrappers -/

def squareReflectBoundaryIndex (m : ℕ)
    (j : Fin (bandTailCount (4 * m ^ 2))) :
    Fin (bandTailCount (4 * m ^ 2)) :=
  concreteReflectBoundaryIndex (4 * m ^ 2) j

@[simp] theorem squareReflectBoundaryIndex_val (m : ℕ)
    (j : Fin (bandTailCount (4 * m ^ 2))) :
    (squareReflectBoundaryIndex m j : ℕ) =
      2 * (m - 1) - 1 - (j : ℕ) := by
  simp [squareReflectBoundaryIndex, concreteReflectBoundaryIndex]

theorem square_midpointRingPopulation_reflect (m : ℕ)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1)) :
    midpointRingPopulation (4 * m ^ 2) (squareReflectBandIndex m j) =
      midpointRingPopulation (4 * m ^ 2) j := by
  simpa [squareReflectBandIndex] using
    concrete_midpointRingPopulation_reflect (4 * m ^ 2) j

theorem square_sharedBoundaryPopulation_reflect (m : ℕ)
    (j : Fin (bandTailCount (4 * m ^ 2))) :
    sharedBoundaryPopulation (4 * m ^ 2) (squareReflectBoundaryIndex m j) =
      sharedBoundaryPopulation (4 * m ^ 2) j := by
  simpa [squareReflectBoundaryIndex] using
    concrete_sharedBoundaryPopulation_reflect (4 * m ^ 2) j

theorem square_bandMidpointHeight_reflect {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1)) :
    bandMidpointHeight (4 * m ^ 2) (squareReflectBandIndex m j) =
      -bandMidpointHeight (4 * m ^ 2) j := by
  simpa [squareReflectBandIndex] using
    concrete_bandMidpointHeight_reflect
      (N := 4 * m ^ 2) (by positivity) j

theorem square_sharedBoundaryHeight_reflect {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2))) :
    bandBoundaryHeight (4 * m ^ 2)
        ((squareReflectBoundaryIndex m j : ℕ) + 1) =
      -bandBoundaryHeight (4 * m ^ 2) ((j : ℕ) + 1) := by
  simpa [squareReflectBoundaryIndex] using
    concrete_sharedBoundaryHeight_reflect
      (N := 4 * m ^ 2) (by positivity) j

theorem square_midpoint_radius_reflect {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1)) :
    (bemocRingFamily (4 * m ^ 2) (Sum.inl (squareReflectBandIndex m j))).radius =
      (bemocRingFamily (4 * m ^ 2) (Sum.inl j)).radius := by
  simpa [squareReflectBandIndex] using
    concrete_midpoint_radius_reflect
      (N := 4 * m ^ 2) (by positivity) j

theorem square_shared_radius_reflect {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2))) :
    (bemocRingFamily (4 * m ^ 2)
        (Sum.inr (squareReflectBoundaryIndex m j))).radius =
      (bemocRingFamily (4 * m ^ 2) (Sum.inr j)).radius := by
  simpa [squareReflectBoundaryIndex] using
    concrete_shared_radius_reflect
      (N := 4 * m ^ 2) (by positivity) j

/-! ## Per-ring normalization for the sharp Riemann sum -/

noncomputable def squareNormalizedRingWeight (α : ℝ) (m : ℕ)
    (p : BemocRingIndex (4 * m ^ 2)) : ℝ :=
  (bemocRingFamily (4 * m ^ 2) p).radius ^ α *
    (((bemocRingFamily (4 * m ^ 2) p).population : ℝ) / m) ^ (1 - α)

theorem square_ring_weight_div_scale {α : ℝ} {m : ℕ} (hm : 0 < m)
    (p : BemocRingIndex (4 * m ^ 2)) :
    ((bemocRingFamily (4 * m ^ 2) p).radius ^ α *
        ((bemocRingFamily (4 * m ^ 2) p).population : ℝ) ^ (1 - α)) /
          (m : ℝ) ^ (1 - α) =
      squareNormalizedRingWeight α m p := by
  rw [squareNormalizedRingWeight,
    Real.div_rpow (by positivity) (by positivity) (1 - α)]
  ring

end BEMOC
