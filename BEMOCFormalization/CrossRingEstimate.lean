import BEMOCFormalization.CrossRingPair
import BEMOCFormalization.ConcreteWithinRing
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Cross-ring arithmetic summation

This file sums the phase-uniform pair estimate over the literal BEMOC ring
populations.  The finite-energy normalization is kept as an ordered sum:
both orientations of every pair of distinct rings occur.
-/

open scoped BigOperators Real
open Set

namespace BEMOC

/-! ## The discrete cross energy is the ordered ring-pair sum -/

theorem crossRingEnergy_eq_sum_discreteRingPairEnergy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : κ → OccupiedRing) (α : ℝ) :
    crossRingEnergy R α =
      ∑ p, ∑ q,
        if p ≠ q then discreteRingPairEnergy α (R p) (R q) else 0 := by
  classical
  unfold crossRingEnergy
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  calc
    (∑ i,
        ∑ y ∈ Finset.univ.erase
          (⟨p, i⟩ : RingPointIndex R),
          if p ≠ y.1 then
            dist (ringConfiguration R ⟨p, i⟩)
              (ringConfiguration R y) ^ α
          else 0) =
        ∑ i, ∑ y : RingPointIndex R,
          if p ≠ y.1 then
            dist (ringConfiguration R ⟨p, i⟩)
              (ringConfiguration R y) ^ α
          else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_erase_add _ _
        (Finset.mem_univ (⟨p, i⟩ : RingPointIndex R))]
      simp
    _ = ∑ i, ∑ q, ∑ j,
          if p ≠ q then dist ((R p).point i) ((R q).point j) ^ α
          else 0 := by
      simp_rw [Fintype.sum_sigma]
      rfl
    _ = ∑ q, if p ≠ q then
          discreteRingPairEnergy α (R p) (R q) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hpq : p ≠ q
      · simp_rw [if_pos hpq]
        unfold discreteRingPairEnergy
        change
          (∑ x, ∑ j, dist ((R p).point x) ((R q).point j) ^ α) =
            ∑ i, ∑ j, dist ((R p).point i) ((R q).point j) ^ α
        rfl
      · simp [hpq]

theorem crossRingDeficit_eq_sum_pairDeficits
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : κ → OccupiedRing) (α : ℝ) :
    continuousCrossRingEnergy R α - crossRingEnergy R α =
      ∑ p, ∑ q,
        if p ≠ q then
          (continuousRingPairEnergy (R p) (R q) α -
            discreteRingPairEnergy α (R p) (R q))
        else 0 := by
  rw [crossRingEnergy_eq_sum_discreteRingPairEnergy]
  unfold continuousCrossRingEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hpq : p ≠ q <;> simp [hpq]

/-! ## Elementary population bounds and multiplicity -/

theorem centralPopulation_le_fifteen_mul_bandCount
    {N : ℕ} (hM : 1 ≤ bandCount N) :
    centralPopulation N ≤ 15 * bandCount N := by
  have hsqrt : N / 4 < (bandCount N + 1) ^ 2 := by
    simpa [bandCount, pow_two] using Nat.lt_succ_sqrt (N / 4)
  have hrem : N < 4 * (N / 4 + 1) := by omega
  have hN : N < 4 * (bandCount N + 1) ^ 2 := by omega
  have hdoubled := doubledOrdinaryTotal_closed N hM
  have haccount := centralPopulation_accounting N (doubledOrdinaryTotal_le N)
  have hcentral :
      centralPopulation N +
          2 * ((bandCount N - 1) *
            (2 * (bandCount N - 1) + 1)) = N := by
    calc
      centralPopulation N +
          2 * ((bandCount N - 1) *
            (2 * (bandCount N - 1) + 1)) =
          centralPopulation N + doubledOrdinaryTotal N := by rw [hdoubled]
      _ = N := by
        unfold doubledOrdinaryTotal
        exact haccount
  have hpred := Nat.sub_add_cancel hM
  have hcentralR :
      (centralPopulation N : ℝ) +
          2 * (((bandCount N - 1 : ℕ) : ℝ) *
            (2 * ((bandCount N - 1 : ℕ) : ℝ) + 1)) = N := by
    exact_mod_cast hcentral
  have hpredR :
      ((bandCount N - 1 : ℕ) : ℝ) = (bandCount N : ℝ) - 1 := by
    have hpredR' :
        ((bandCount N - 1 : ℕ) : ℝ) + 1 = (bandCount N : ℝ) := by
      exact_mod_cast hpred
    linarith
  have hNR :
      (N : ℝ) < 4 * ((bandCount N : ℝ) + 1) ^ 2 := by
    exact_mod_cast hN
  have hboundR :
      (centralPopulation N : ℝ) ≤ 15 * (bandCount N : ℝ) := by
    rw [hpredR] at hcentralR
    by_cases hM1 : bandCount N = 1
    · have hNsmall : N < 16 := by
        rw [hM1] at hN
        norm_num at hN ⊢
        exact hN
      have hcentral_le : centralPopulation N ≤ N := by omega
      exact_mod_cast (show centralPopulation N ≤ 15 * bandCount N by omega)
    · have hM2 : (2 : ℝ) ≤ bandCount N := by
        exact_mod_cast (show 2 ≤ bandCount N by omega)
      nlinarith
  exact_mod_cast hboundR

theorem finiteBandPopulation_le_fifteen_mul_bandCount
    {N : ℕ} (hM : 1 ≤ bandCount N)
    (j : Fin (bandTailCount N + 1)) :
    finiteBandPopulation N j ≤ 15 * bandCount N := by
  by_cases hnorth : (j : ℕ) < bandCount N - 1
  · rw [concrete_finiteBandPopulation_north j hnorth]
    simp [ordinaryPopulation]
    omega
  by_cases hcentral : (j : ℕ) = bandCount N - 1
  · have hj : j = concreteCentralBandIndex N := by
      apply Fin.ext
      simpa [concreteCentralBandIndex] using hcentral
    rw [hj, concrete_finiteBandPopulation_central hM]
    exact centralPopulation_le_fifteen_mul_bandCount hM
  · rw [concrete_finiteBandPopulation_reflect]
    let jr := concreteReflectBandIndex N j
    have hjlt := j.isLt
    simp only [bandTailCount] at hjlt
    have hjr : (jr : ℕ) < bandCount N - 1 := by
      dsimp [jr, concreteReflectBandIndex]
      simp only [bandTailCount]
      omega
    rw [concrete_finiteBandPopulation_north jr hjr]
    simp [ordinaryPopulation]
    omega

theorem bemocRingFamily_population_le_thirty_mul_bandCount
    {N : ℕ} (hM : 1 ≤ bandCount N) (p : BemocRingIndex N) :
    (bemocRingFamily N p).population ≤ 30 * bandCount N := by
  rcases p with j | j
  · change midpointRingPopulation N j ≤ 30 * bandCount N
    unfold midpointRingPopulation
    exact (Nat.sub_le _ _).trans
      ((finiteBandPopulation_le_fifteen_mul_bandCount hM j).trans (by omega))
  · change sharedBoundaryPopulation N j ≤ 30 * bandCount N
    unfold sharedBoundaryPopulation
    have hleft := twice_boundarySixth_le N j.castSucc
    have hright := twice_boundarySixth_le N j.succ
    have hleft' :=
      finiteBandPopulation_le_fifteen_mul_bandCount hM j.castSucc
    have hright' :=
      finiteBandPopulation_le_fifteen_mul_bandCount hM j.succ
    omega

private theorem midpointPopulation_injective_north
    {N : ℕ} {j k : Fin (bandTailCount N + 1)}
    (hj : (j : ℕ) < bandCount N - 1)
    (hk : (k : ℕ) < bandCount N - 1)
    (hpop : midpointRingPopulation N j = midpointRingPopulation N k) :
    j = k := by
  rw [midpointRingPopulation, midpointRingPopulation,
    concrete_finiteBandPopulation_north j hj,
    concrete_finiteBandPopulation_north k hk,
    concrete_boundarySixth_north j hj,
    concrete_boundarySixth_north k hk] at hpop
  apply Fin.ext
  simp only [ordinaryPopulation] at hpop
  omega

private theorem ordinaryPopulation_sixth_pair
    {d : ℕ} (hd : 1 ≤ d) :
    ordinaryPopulation d / 6 + ordinaryPopulation (d + 1) / 6 =
      ordinaryPopulation d / 3 := by
  simp only [ordinaryPopulation]
  have hmod := Nat.mod_lt d (by norm_num : 0 < 6)
  have hdecomp := Nat.mod_add_div d 6
  interval_cases h : d % 6 <;> omega

private theorem sharedPopulation_injective_regular_north
    {N : ℕ} {j k : Fin (bandTailCount N)}
    (hj : (j : ℕ) < bandCount N - 2)
    (hk : (k : ℕ) < bandCount N - 2)
    (hpop : sharedBoundaryPopulation N j =
      sharedBoundaryPopulation N k) :
    j = k := by
  have hj0 : ((j.castSucc : Fin (bandTailCount N + 1)) : ℕ) <
      bandCount N - 1 := by simpa using (show (j : ℕ) < bandCount N - 1 by omega)
  have hj1 : ((j.succ : Fin (bandTailCount N + 1)) : ℕ) <
      bandCount N - 1 := by simpa using
        (show (j : ℕ) + 1 < bandCount N - 1 by omega)
  have hk0 : ((k.castSucc : Fin (bandTailCount N + 1)) : ℕ) <
      bandCount N - 1 := by simpa using (show (k : ℕ) < bandCount N - 1 by omega)
  have hk1 : ((k.succ : Fin (bandTailCount N + 1)) : ℕ) <
      bandCount N - 1 := by simpa using
        (show (k : ℕ) + 1 < bandCount N - 1 by omega)
  rw [sharedBoundaryPopulation, sharedBoundaryPopulation,
    concrete_boundarySixth_north j.castSucc hj0,
    concrete_boundarySixth_north j.succ hj1,
    concrete_boundarySixth_north k.castSucc hk0,
    concrete_boundarySixth_north k.succ hk1] at hpop
  apply Fin.ext
  simp only [Fin.coe_castSucc, Fin.val_succ] at hpop
  change
    ordinaryPopulation ((j : ℕ) + 1) / 6 +
          ordinaryPopulation (((j : ℕ) + 1) + 1) / 6 =
      ordinaryPopulation ((k : ℕ) + 1) / 6 +
          ordinaryPopulation (((k : ℕ) + 1) + 1) / 6 at hpop
  rw [ordinaryPopulation_sixth_pair (by omega),
    ordinaryPopulation_sixth_pair (by omega)] at hpop
  simp only [ordinaryPopulation] at hpop
  omega

private def bemocPopulationFiberCode {N : ℕ} (p : BemocRingIndex N) : Fin 7 :=
  match p with
  | Sum.inl j =>
      if (j : ℕ) < bandCount N - 1 then 0
      else if (j : ℕ) = bandCount N - 1 then 1 else 2
  | Sum.inr j =>
      if (j : ℕ) < bandCount N - 2 then 3
      else if (j : ℕ) = bandCount N - 2 then 4
      else if (j : ℕ) = bandCount N - 1 then 5 else 6

private theorem bemocPopulationFiberCode_injective_on_fiber
    {N q : ℕ} (hM : 3 ≤ bandCount N) :
    Set.InjOn bemocPopulationFiberCode
      {p : BemocRingIndex N | (bemocRingFamily N p).population = q} := by
  intro p hp k hk hcode
  rcases p with j | j <;> rcases k with k | k
  · simp only [Set.mem_setOf_eq, bemocRingFamily] at hp hk
    simp only [bemocPopulationFiberCode] at hcode
    by_cases hjn : (j : ℕ) < bandCount N - 1
    · simp only [if_pos hjn] at hcode
      have hkn : (k : ℕ) < bandCount N - 1 := by
        by_contra hn
        simp only [if_neg hn] at hcode
        split_ifs at hcode <;> omega
      exact congrArg Sum.inl
        (midpointPopulation_injective_north hjn hkn (hp.trans hk.symm))
    · simp only [if_neg hjn] at hcode
      by_cases hjc : (j : ℕ) = bandCount N - 1
      · simp only [if_pos hjc] at hcode
        have hkc : (k : ℕ) = bandCount N - 1 := by
          by_contra hn
          by_cases hkn : (k : ℕ) < bandCount N - 1
          · simp [hkn] at hcode
          · simp [hkn, hn] at hcode
        congr 1
        apply Fin.ext
        omega
      · simp only [if_neg hjc] at hcode
        have hks : ¬(k : ℕ) < bandCount N - 1 ∧
            (k : ℕ) ≠ bandCount N - 1 := by
          constructor
          · intro hkn
            simp [hkn] at hcode
          · intro hkc
            simp [show ¬(k : ℕ) < bandCount N - 1 by omega, hkc] at hcode
        have hjr : (concreteReflectBandIndex N j : ℕ) <
            bandCount N - 1 := by
          simp [concreteReflectBandIndex, bandTailCount]
          omega
        have hkr : (concreteReflectBandIndex N k : ℕ) <
            bandCount N - 1 := by
          simp [concreteReflectBandIndex, bandTailCount]
          omega
        have hrefpop :
            midpointRingPopulation N (concreteReflectBandIndex N j) =
              midpointRingPopulation N (concreteReflectBandIndex N k) := by
          rw [concrete_midpointRingPopulation_reflect,
            concrete_midpointRingPopulation_reflect]
          exact hp.trans hk.symm
        have href := midpointPopulation_injective_north hjr hkr hrefpop
        congr 1
        apply Fin.ext
        have hv := congrArg Fin.val href
        have hjlt := j.isLt
        have hklt := k.isLt
        simp [concreteReflectBandIndex, bandTailCount] at hv
        simp only [bandTailCount] at hjlt hklt
        omega
  · simp only [bemocPopulationFiberCode] at hcode
    split_ifs at hcode <;> omega
  · simp only [bemocPopulationFiberCode] at hcode
    split_ifs at hcode <;> omega
  · simp only [Set.mem_setOf_eq, bemocRingFamily] at hp hk
    simp only [bemocPopulationFiberCode] at hcode
    by_cases hjn : (j : ℕ) < bandCount N - 2
    · simp only [if_pos hjn] at hcode
      have hkn : (k : ℕ) < bandCount N - 2 := by
        by_contra! hkn
        simp only [if_neg (not_lt.mpr hkn)] at hcode
        split_ifs at hcode <;> omega
      exact congrArg Sum.inr
        (sharedPopulation_injective_regular_north hjn hkn (hp.trans hk.symm))
    · simp only [if_neg hjn] at hcode
      by_cases hjc₀ : (j : ℕ) = bandCount N - 2
      · simp only [if_pos hjc₀] at hcode
        have hkc : (k : ℕ) = bandCount N - 2 := by
          by_contra hn
          split_ifs at hcode <;> omega
        congr 1
        apply Fin.ext
        omega
      · simp only [if_neg hjc₀] at hcode
        by_cases hjc₁ : (j : ℕ) = bandCount N - 1
        · simp only [if_pos hjc₁] at hcode
          have hkc : (k : ℕ) = bandCount N - 1 := by
            by_contra hn
            split_ifs at hcode <;> omega
          congr 1
          apply Fin.ext
          omega
        · simp only [if_neg hjc₁] at hcode
          have hks : ¬(k : ℕ) < bandCount N - 2 ∧
              (k : ℕ) ≠ bandCount N - 2 ∧
              (k : ℕ) ≠ bandCount N - 1 := by
            constructor
            · intro hkn
              simp [hkn] at hcode
            constructor
            · intro hkc
              split_ifs at hcode <;> omega
            · intro hkc
              split_ifs at hcode <;> omega
          have hjr : (concreteReflectBoundaryIndex N j : ℕ) <
              bandCount N - 2 := by
            simp [concreteReflectBoundaryIndex, bandTailCount]
            omega
          have hkr : (concreteReflectBoundaryIndex N k : ℕ) <
              bandCount N - 2 := by
            simp [concreteReflectBoundaryIndex, bandTailCount]
            omega
          have hrefpop :
              sharedBoundaryPopulation N (concreteReflectBoundaryIndex N j) =
                sharedBoundaryPopulation N
                  (concreteReflectBoundaryIndex N k) := by
            rw [concrete_sharedBoundaryPopulation_reflect,
              concrete_sharedBoundaryPopulation_reflect]
            exact hp.trans hk.symm
          have href :=
            sharedPopulation_injective_regular_north hjr hkr hrefpop
          congr 1
          apply Fin.ext
          have hv := congrArg Fin.val href
          have hjlt := j.isLt
          have hklt := k.isLt
          simp [concreteReflectBoundaryIndex, bandTailCount] at hv
          simp only [bandTailCount] at hjlt hklt
          omega

theorem bemoc_population_fiber_card_le_seven
    {N q : ℕ} (hM : 3 ≤ bandCount N) :
    ((Finset.univ : Finset (BemocRingIndex N)).filter
      (fun p ↦ (bemocRingFamily N p).population = q)).card ≤ 7 := by
  classical
  let s := (Finset.univ : Finset (BemocRingIndex N)).filter
    (fun p ↦ (bemocRingFamily N p).population = q)
  calc
    s.card ≤ (Finset.univ : Finset (Fin 7)).card := by
      apply Finset.card_le_card_of_injOn bemocPopulationFiberCode
      · intro p hp
        simp
      · intro p hp k hk hcode
        apply bemocPopulationFiberCode_injective_on_fiber hM
        · simpa [s] using hp
        · simpa [s] using hk
        · exact hcode
    _ = 7 := by simp

/-! ## Power sums -/

noncomputable def negativePowerSumConstant (a : ℝ) : ℝ :=
  1 + 1 / (1 - a)

theorem negativePowerSumConstant_pos {a : ℝ} (ha1 : a < 1) :
    0 < negativePowerSumConstant a := by
  unfold negativePowerSumConstant
  have hden : 0 < 1 - a := by linarith
  have hinv : 0 < 1 / (1 - a) := one_div_pos.mpr hden
  linarith

theorem sum_range_one_add_rpow_neg_le
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {X : ℕ} (hX : 1 ≤ X) :
    (∑ u ∈ Finset.range X, ((u + 1 : ℕ) : ℝ) ^ (-a)) ≤
      negativePowerSumConstant a * (X : ℝ) ^ (1 - a) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-a)
  have hanti : AntitoneOn f (Set.Icc (1 : ℝ) X) := by
    intro x hx y hy hxy
    dsimp [f]
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx.1) hxy
      (by linarith)
  have hXdecomp : X = (X - 1) + 1 := by omega
  have hend :
      (1 : ℝ) + ((X - 1 : ℕ) : ℝ) = (X : ℝ) := by
    have hNat : 1 + (X - 1) = X := by omega
    exact_mod_cast hNat
  have hanti' : AntitoneOn f
      (Set.Icc (1 : ℝ) ((1 : ℝ) + ((X - 1 : ℕ) : ℝ))) := by
    simpa [hend] using hanti
  have hsumInt := hanti'.sum_le_integral
    (x₀ := (1 : ℝ)) (a := X - 1)
  have hsumSplit :
      (∑ u ∈ Finset.range X, ((u + 1 : ℕ) : ℝ) ^ (-a)) =
        (∑ u ∈ Finset.range (X - 1),
          (((1 : ℝ) + (u + 1 : ℕ)) : ℝ) ^ (-a)) + 1 := by
    rw [hXdecomp, Finset.sum_range_succ']
    norm_num [Nat.cast_add]
    ring_nf
  have hInt :
      (∫ x : ℝ in (1 : ℝ)..X, x ^ (-a)) =
        ((X : ℝ) ^ (1 - a) - 1) / (1 - a) := by
    rw [integral_rpow (a := (1 : ℝ)) (b := (X : ℝ))
      (r := -a) (Or.inl (by linarith))]
    norm_num [Real.one_rpow]
    ring_nf
  have hXpow : 1 ≤ (X : ℝ) ^ (1 - a) := by
    have h1X : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hexp : 0 ≤ 1 - a := by linarith
    have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) h1X hexp
    simpa only [Real.one_rpow] using hpow
  rw [hsumSplit]
  calc
    (∑ u ∈ Finset.range (X - 1),
          (((1 : ℝ) + (u + 1 : ℕ)) : ℝ) ^ (-a)) + 1 ≤
        (∫ x : ℝ in (1 : ℝ)..X, x ^ (-a)) + 1 := by
      exact add_le_add_right (by simpa [f, hend] using hsumInt) 1
    _ = ((X : ℝ) ^ (1 - a) - 1) / (1 - a) + 1 := by rw [hInt]
    _ ≤ negativePowerSumConstant a * (X : ℝ) ^ (1 - a) := by
      unfold negativePowerSumConstant
      have hden : 0 < 1 - a := by linarith
      have hpow0 : 0 ≤ (X : ℝ) ^ (1 - a) := by positivity
      have hinv : 0 < (1 - a)⁻¹ := inv_pos.mpr hden
      rw [div_eq_mul_inv, one_div]
      calc
        ((X : ℝ) ^ (1 - a) - 1) * (1 - a)⁻¹ + 1 =
            (X : ℝ) ^ (1 - a) * (1 - a)⁻¹ +
              1 - (1 - a)⁻¹ := by ring
        _ ≤ (X : ℝ) ^ (1 - a) * (1 - a)⁻¹ +
              (X : ℝ) ^ (1 - a) := by nlinarith
        _ = (1 + (1 - a)⁻¹) * (X : ℝ) ^ (1 - a) := by ring

theorem sum_Icc_rpow_neg_le
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {X : ℕ} (hX : 1 ≤ X) :
    (∑ u ∈ Finset.Icc 1 X, (u : ℝ) ^ (-a)) ≤
      negativePowerSumConstant a * (X : ℝ) ^ (1 - a) := by
  have hEq :
      (∑ u ∈ Finset.Icc 1 X, (u : ℝ) ^ (-a)) =
        ∑ u ∈ Finset.range X, ((u + 1 : ℕ) : ℝ) ^ (-a) := by
    have hsets : Finset.Icc 1 X = Finset.Ico 1 (X + 1) := by
      ext u
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    calc
      (∑ u ∈ Finset.Icc 1 X, (u : ℝ) ^ (-a)) =
          ∑ u ∈ Finset.Ico 1 (X + 1), (u : ℝ) ^ (-a) := by
        rw [hsets]
      _ = ∑ u ∈ Finset.range ((X + 1) - 1),
          ((1 + u : ℕ) : ℝ) ^ (-a) :=
        Finset.sum_Ico_eq_sum_range (fun u : ℕ ↦ (u : ℝ) ^ (-a)) 1 (X + 1)
      _ = ∑ u ∈ Finset.range X, ((u + 1 : ℕ) : ℝ) ^ (-a) := by
        have hsub : X + 1 - 1 = X := by omega
        rw [hsub]
        simp only [add_comm]
  rw [hEq]
  exact sum_range_one_add_rpow_neg_le ha0 ha1 hX

noncomputable def powerSumConstant (α : ℝ) : ℝ :=
  if α < 1 then negativePowerSumConstant (1 - α) else 1

theorem powerSumConstant_pos {α : ℝ} (hα0 : 0 < α) :
    0 < powerSumConstant α := by
  unfold powerSumConstant
  split_ifs with hα1
  · exact negativePowerSumConstant_pos (by linarith)
  · norm_num

theorem sum_Icc_rpow_alpha_sub_one_le
    {α : ℝ} (hα0 : 0 < α) {X : ℕ} (hX : 1 ≤ X) :
    (∑ u ∈ Finset.Icc 1 X, (u : ℝ) ^ (α - 1)) ≤
      powerSumConstant α * (X : ℝ) ^ α := by
  by_cases hα1 : α < 1
  · rw [powerSumConstant, if_pos hα1]
    rw [show α - 1 = -(1 - α) by ring]
    have hsum := sum_Icc_rpow_neg_le (a := 1 - α)
      (by linarith) (by linarith) hX
    convert hsum using 1 ; ring_nf
  · rw [powerSumConstant, if_neg hα1, one_mul]
    have hexp : 0 ≤ α - 1 := by linarith
    calc
      (∑ u ∈ Finset.Icc 1 X, (u : ℝ) ^ (α - 1)) ≤
          ∑ _u ∈ Finset.Icc 1 X, (X : ℝ) ^ (α - 1) := by
        apply Finset.sum_le_sum
        intro u hu
        exact Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast (Finset.mem_Icc.mp hu).2) hexp
      _ = (Finset.Icc 1 X).card * (X : ℝ) ^ (α - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (X : ℝ) * (X : ℝ) ^ (α - 1) := by
        gcongr
        have hcard : (Finset.Icc 1 X).card ≤ X := by
          simp
        exact_mod_cast hcard
      _ = (X : ℝ) ^ α := by
        have hXpos : (0 : ℝ) < X := by
          exact_mod_cast (show 0 < X by omega)
        calc
          (X : ℝ) * (X : ℝ) ^ (α - 1) =
              (X : ℝ) ^ (1 : ℝ) * (X : ℝ) ^ (α - 1) := by
            rw [Real.rpow_one]
          _ = (X : ℝ) ^ ((1 : ℝ) + (α - 1)) :=
            (Real.rpow_add hXpos 1 (α - 1)).symm
          _ = (X : ℝ) ^ α := by ring_nf

/-! ## Divisor majorization of the gcd sum -/

noncomputable def gcdArithmeticWeight (α : ℝ) (q r : ℕ) : ℝ :=
  (Nat.gcd q r : ℝ) ^ (1 + α) *
    (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)

theorem gcdArithmeticWeight_nonneg (α : ℝ) (q r : ℕ) :
    0 ≤ gcdArithmeticWeight α q r := by
  unfold gcdArithmeticWeight
  positivity

private theorem sum_divisible_rpow_neg_eq
    {a : ℝ} {k X : ℕ} (hk : 1 ≤ k) :
    (∑ q ∈ Finset.Icc 1 X with k ∣ q, (q : ℝ) ^ (-a)) =
      (k : ℝ) ^ (-a) *
        ∑ u ∈ Finset.Icc 1 (X / k), (u : ℝ) ^ (-a) := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij
    (s := (Finset.Icc 1 X).filter (fun q ↦ k ∣ q))
    (t := Finset.Icc 1 (X / k))
    (f := fun q : ℕ ↦ (q : ℝ) ^ (-a))
    (g := fun u : ℕ ↦ (k : ℝ) ^ (-a) * (u : ℝ) ^ (-a))
    (fun q hq ↦ q / k) ?_ ?_ ?_ ?_
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hkdvd⟩
    rcases Finset.mem_Icc.mp hqIcc with ⟨hq1, hqX⟩
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_div_iff hk |>.2 (Nat.le_of_dvd hq1 hkdvd)
    · exact (Nat.div_le_div_right hqX)
  · intro q hq r hr hdiv
    have hqk := (Finset.mem_filter.mp hq).2
    have hrk := (Finset.mem_filter.mp hr).2
    have hdiv' : q / k = r / k := by simpa using hdiv
    calc
      q = k * (q / k) := (Nat.mul_div_cancel' hqk).symm
      _ = k * (r / k) := by rw [hdiv']
      _ = r := Nat.mul_div_cancel' hrk
  · intro u hu
    rcases Finset.mem_Icc.mp hu with ⟨hu1, huX⟩
    refine ⟨k * u, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by
      exact Nat.mul_pos (by omega) (by omega), ?_⟩, dvd_mul_right k u⟩, ?_⟩
    · rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hk).mp huX
    · exact Nat.mul_div_cancel_left u hk
  · intro q hq
    have hkdvd := (Finset.mem_filter.mp hq).2
    have hqpos := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
    have hkpos : 0 < k := by omega
    have hkq : k ≤ q := Nat.le_of_dvd hqpos hkdvd
    have hudiv : 0 < q / k := Nat.div_pos hkq hkpos
    have hqeq : q = k * (q / k) := (Nat.mul_div_cancel' hkdvd).symm
    calc
      (q : ℝ) ^ (-a) =
          ((k * (q / k) : ℕ) : ℝ) ^ (-a) := by rw [← hqeq]
      _ = ((k : ℝ) * ((q / k : ℕ) : ℝ)) ^ (-a) := by push_cast; rfl
      _ = (k : ℝ) ^ (-a) * ((q / k : ℕ) : ℝ) ^ (-a) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]

private theorem sum_divisible_rpow_neg_le
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {k X : ℕ} (hk : 1 ≤ k) (hkX : k ≤ X) :
    (∑ q ∈ Finset.Icc 1 X with k ∣ q, (q : ℝ) ^ (-a)) ≤
      negativePowerSumConstant a * (X : ℝ) ^ (1 - a) *
        (k : ℝ) ^ (-(1 : ℝ)) := by
  rw [sum_divisible_rpow_neg_eq hk]
  have hXdiv : 1 ≤ X / k := Nat.one_le_div_iff hk |>.2 hkX
  have hsum := sum_Icc_rpow_neg_le ha0 ha1 hXdiv
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcastDiv : ((X / k : ℕ) : ℝ) ≤ (X : ℝ) / (k : ℝ) := by
    exact Nat.cast_div_le
  have hpowDiv :
      ((X / k : ℕ) : ℝ) ^ (1 - a) ≤
        ((X : ℝ) / (k : ℝ)) ^ (1 - a) :=
    Real.rpow_le_rpow (by positivity) hcastDiv (by linarith)
  calc
    (k : ℝ) ^ (-a) *
          ∑ u ∈ Finset.Icc 1 (X / k), (u : ℝ) ^ (-a) ≤
        (k : ℝ) ^ (-a) *
          (negativePowerSumConstant a *
            ((X / k : ℕ) : ℝ) ^ (1 - a)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (k : ℝ) ^ (-a) *
          (negativePowerSumConstant a *
            ((X : ℝ) / (k : ℝ)) ^ (1 - a)) := by
      have hK0 : 0 ≤ negativePowerSumConstant a :=
        (negativePowerSumConstant_pos ha1).le
      gcongr
    _ = negativePowerSumConstant a * (X : ℝ) ^ (1 - a) *
          (k : ℝ) ^ (-(1 : ℝ)) := by
      rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ X) hkpos.le]
      rw [div_eq_mul_inv, ← Real.rpow_neg hkpos.le]
      calc
        (k : ℝ) ^ (-a) *
            (negativePowerSumConstant a *
              ((X : ℝ) ^ (1 - a) * (k : ℝ) ^ (-(1 - a)))) =
            negativePowerSumConstant a * (X : ℝ) ^ (1 - a) *
              ((k : ℝ) ^ (-a) * (k : ℝ) ^ (-(1 - a))) := by ring
        _ = negativePowerSumConstant a * (X : ℝ) ^ (1 - a) *
              (k : ℝ) ^ (-(1 : ℝ)) := by
          rw [← Real.rpow_add hkpos]
          congr 2
          ring

private theorem gcdArithmeticWeight_le_divisor_sum
    {α : ℝ} {q r X : ℕ}
    (hq : 1 ≤ q) (hqX : q ≤ X) (hr : 1 ≤ r) (_hrX : r ≤ X) :
    gcdArithmeticWeight α q r ≤
      ∑ k ∈ Finset.Icc 1 X,
        if k ∣ q ∧ k ∣ r then
          (k : ℝ) ^ (1 + α) *
            (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
        else 0 := by
  let d := Nat.gcd q r
  have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr <| by
    exact Nat.gcd_ne_zero_left (by omega)
  have hdX : d ≤ X :=
    (Nat.gcd_le_left r hq).trans hqX
  have hdmem : d ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr ⟨hdpos, hdX⟩
  have hdvd : d ∣ q ∧ d ∣ r :=
    ⟨Nat.gcd_dvd_left q r, Nat.gcd_dvd_right q r⟩
  unfold gcdArithmeticWeight
  change
    (d : ℝ) ^ (1 + α) * (q : ℝ) ^ (-α / 2) *
        (r : ℝ) ^ (-α / 2) ≤ _
  have hsingle := Finset.single_le_sum
    (s := Finset.Icc 1 X)
    (f := fun k : ℕ ↦
      if k ∣ q ∧ k ∣ r then
        (k : ℝ) ^ (1 + α) *
          (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
      else 0)
    (fun k hk ↦ by
      dsimp
      split_ifs <;> positivity) hdmem
  simpa [hdvd] using hsingle

private theorem divisor_triple_sum_factorization
    (α : ℝ) (X : ℕ) :
    (∑ q ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
      ∑ k ∈ Finset.Icc 1 X,
        if k ∣ q ∧ k ∣ r then
          (k : ℝ) ^ (1 + α) *
            (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
        else 0) =
      ∑ k ∈ Finset.Icc 1 X,
        (k : ℝ) ^ (1 + α) *
          (∑ q ∈ Finset.Icc 1 X with k ∣ q,
            (q : ℝ) ^ (-α / 2)) *
          (∑ r ∈ Finset.Icc 1 X with k ∣ r,
            (r : ℝ) ^ (-α / 2)) := by
  have hswap (q : ℕ) :
      (∑ r ∈ Finset.Icc 1 X, ∑ k ∈ Finset.Icc 1 X,
        if k ∣ q ∧ k ∣ r then
          (k : ℝ) ^ (1 + α) *
            (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
        else 0) =
      ∑ k ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
        if k ∣ q ∧ k ∣ r then
          (k : ℝ) ^ (1 + α) *
            (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
        else 0 :=
    Finset.sum_comm
  simp_rw [hswap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  let D : ℝ := ∑ q ∈ Finset.Icc 1 X with k ∣ q,
    (q : ℝ) ^ (-α / 2)
  have hinner (q : ℕ) :
      (∑ r ∈ Finset.Icc 1 X,
          if k ∣ q ∧ k ∣ r then
            (k : ℝ) ^ (1 + α) *
              (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
          else 0) =
        if k ∣ q then
          (k : ℝ) ^ (1 + α) * (q : ℝ) ^ (-α / 2) * D
        else 0 := by
    by_cases hkq : k ∣ q
    · simp only [hkq, true_and, if_true]
      dsimp [D]
      rw [Finset.mul_sum]
      rw [Finset.sum_filter]
    · simp [hkq]
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  change
    (∑ q ∈ (Finset.Icc 1 X).filter (fun q ↦ k ∣ q),
      (k : ℝ) ^ (1 + α) * (q : ℝ) ^ (-α / 2) * D) =
      (k : ℝ) ^ (1 + α) * D * D
  have hC :
      (∑ q ∈ (Finset.Icc 1 X).filter (fun q ↦ k ∣ q),
        (k : ℝ) ^ (1 + α) * (q : ℝ) ^ (-α / 2)) =
        (k : ℝ) ^ (1 + α) * D := by
    dsimp [D]
    exact (Finset.mul_sum _ _ _).symm
  calc
    (∑ q ∈ (Finset.Icc 1 X).filter (fun q ↦ k ∣ q),
        (k : ℝ) ^ (1 + α) * (q : ℝ) ^ (-α / 2) * D) =
        (∑ q ∈ (Finset.Icc 1 X).filter (fun q ↦ k ∣ q),
          (k : ℝ) ^ (1 + α) * (q : ℝ) ^ (-α / 2)) * D := by
      exact (Finset.sum_mul _ _ D).symm
    _ = (k : ℝ) ^ (1 + α) * D * D := by rw [hC]

noncomputable def gcdArithmeticConstant (α : ℝ) : ℝ :=
  negativePowerSumConstant (α / 2) ^ 2 * powerSumConstant α

theorem gcdArithmeticConstant_pos
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    0 < gcdArithmeticConstant α := by
  unfold gcdArithmeticConstant
  exact mul_pos (sq_pos_of_pos (negativePowerSumConstant_pos (by linarith)))
    (powerSumConstant_pos hα0)

set_option maxHeartbeats 800000 in
theorem gcd_arithmetic_double_sum_le
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {X : ℕ} (hX : 1 ≤ X) :
    (∑ q ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
      gcdArithmeticWeight α q r) ≤
        gcdArithmeticConstant α * (X : ℝ) ^ 2 := by
  let a : ℝ := α / 2
  let K₀ : ℝ := negativePowerSumConstant a
  let K₁ : ℝ := powerSumConstant α
  have ha0 : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hK₀ : 0 < K₀ := negativePowerSumConstant_pos ha1
  have hK₁ : 0 < K₁ := powerSumConstant_pos hα0
  have hmajor :
      (∑ q ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
        gcdArithmeticWeight α q r) ≤
      ∑ q ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
        ∑ k ∈ Finset.Icc 1 X,
          if k ∣ q ∧ k ∣ r then
            (k : ℝ) ^ (1 + α) *
              (q : ℝ) ^ (-α / 2) * (r : ℝ) ^ (-α / 2)
          else 0 := by
    apply Finset.sum_le_sum
    intro q hq
    apply Finset.sum_le_sum
    intro r hr
    exact gcdArithmeticWeight_le_divisor_sum
      (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
      (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2
  rw [divisor_triple_sum_factorization] at hmajor
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 X) :
      (k : ℝ) ^ (1 + α) *
          (∑ q ∈ Finset.Icc 1 X with k ∣ q,
            (q : ℝ) ^ (-α / 2)) *
          (∑ r ∈ Finset.Icc 1 X with k ∣ r,
            (r : ℝ) ^ (-α / 2)) ≤
        K₀ ^ 2 * (X : ℝ) ^ (2 - α) *
          (k : ℝ) ^ (α - 1) := by
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hkX⟩
    let D : ℝ := ∑ q ∈ Finset.Icc 1 X with k ∣ q,
      (q : ℝ) ^ (-α / 2)
    let B : ℝ := K₀ * (X : ℝ) ^ (1 - a) *
      (k : ℝ) ^ (-(1 : ℝ))
    have hD :
        D ≤ B := by
      have hraw := sum_divisible_rpow_neg_le ha0 ha1 hk1 hkX
      convert hraw using 1 ; dsimp [D, B, a, K₀] ; ring_nf
    have hD0 : 0 ≤ D := by
      dsimp [D]
      positivity
    have hB0 : 0 ≤ B := by
      dsimp [B]
      positivity
    have hsq : D * D ≤ B * B := by
      exact mul_le_mul hD hD hD0 hB0
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    change (k : ℝ) ^ (1 + α) * D * D ≤ _
    calc
      (k : ℝ) ^ (1 + α) * D * D =
          (k : ℝ) ^ (1 + α) * (D * D) := by ring
      _ ≤ (k : ℝ) ^ (1 + α) * (B * B) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = K₀ ^ 2 * (X : ℝ) ^ (2 - α) *
          (k : ℝ) ^ (α - 1) := by
        dsimp [B]
        calc
          (k : ℝ) ^ (1 + α) *
              (K₀ * (X : ℝ) ^ (1 - a) * (k : ℝ) ^ (-(1 : ℝ)) *
                (K₀ * (X : ℝ) ^ (1 - a) *
                  (k : ℝ) ^ (-(1 : ℝ)))) =
              K₀ ^ 2 *
                ((X : ℝ) ^ (1 - a) * (X : ℝ) ^ (1 - a)) *
                (((k : ℝ) ^ (1 + α) * (k : ℝ) ^ (-(1 : ℝ))) *
                  (k : ℝ) ^ (-(1 : ℝ))) := by ring
          _ = K₀ ^ 2 * (X : ℝ) ^ ((1 - a) + (1 - a)) *
                (k : ℝ) ^ (((1 + α) + (-(1 : ℝ))) + (-(1 : ℝ))) := by
            have hXcombine :
                (X : ℝ) ^ (1 - a) * (X : ℝ) ^ (1 - a) =
                  (X : ℝ) ^ ((1 - a) + (1 - a)) :=
              (Real.rpow_add hXpos (1 - a) (1 - a)).symm
            have hkcombine :
                ((k : ℝ) ^ (1 + α) * (k : ℝ) ^ (-(1 : ℝ))) *
                    (k : ℝ) ^ (-(1 : ℝ)) =
                  (k : ℝ) ^
                    (((1 + α) + (-(1 : ℝ))) + (-(1 : ℝ))) := by
              rw [← Real.rpow_add hkpos, ← Real.rpow_add hkpos]
            rw [hXcombine, hkcombine]
          _ = K₀ ^ 2 * (X : ℝ) ^ (2 - α) *
                (k : ℝ) ^ (α - 1) := by
            dsimp [a]
            ring_nf
  calc
    (∑ q ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
        gcdArithmeticWeight α q r) ≤
        ∑ k ∈ Finset.Icc 1 X,
          (k : ℝ) ^ (1 + α) *
            (∑ q ∈ Finset.Icc 1 X with k ∣ q,
              (q : ℝ) ^ (-α / 2)) *
            (∑ r ∈ Finset.Icc 1 X with k ∣ r,
              (r : ℝ) ^ (-α / 2)) := hmajor
    _ ≤ ∑ k ∈ Finset.Icc 1 X,
          K₀ ^ 2 * (X : ℝ) ^ (2 - α) *
            (k : ℝ) ^ (α - 1) :=
      Finset.sum_le_sum hterm
    _ = K₀ ^ 2 * (X : ℝ) ^ (2 - α) *
          (∑ k ∈ Finset.Icc 1 X, (k : ℝ) ^ (α - 1)) := by
      rw [Finset.mul_sum]
    _ ≤ K₀ ^ 2 * (X : ℝ) ^ (2 - α) *
          (K₁ * (X : ℝ) ^ α) := by
      apply mul_le_mul_of_nonneg_left
        (sum_Icc_rpow_alpha_sub_one_le hα0 hX)
      positivity
    _ = gcdArithmeticConstant α * (X : ℝ) ^ 2 := by
      have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
      calc
        K₀ ^ 2 * (X : ℝ) ^ (2 - α) * (K₁ * (X : ℝ) ^ α) =
            (K₀ ^ 2 * K₁) *
              ((X : ℝ) ^ (2 - α) * (X : ℝ) ^ α) := by ring
        _ = (K₀ ^ 2 * K₁) * (X : ℝ) ^ ((2 - α) + α) := by
          rw [Real.rpow_add hXpos]
        _ = gcdArithmeticConstant α * (X : ℝ) ^ 2 := by
          dsimp [gcdArithmeticConstant, K₀, K₁, a]
          ring_nf
          have hrpow :
              (X : ℝ) ^ (2 : ℝ) = (X : ℝ) ^ (2 : ℕ) :=
            Real.rpow_natCast (X : ℝ) 2
          rw [hrpow]

/-! ## Reindexing the literal BEMOC populations -/

private theorem bemoc_population_sum_le_seven
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (g : ℕ → ℝ) (hg : ∀ q, 0 ≤ g q) :
    (∑ p : BemocRingIndex N, g (bemocRingFamily N p).population) ≤
      7 * ∑ q ∈ Finset.Icc 1 (30 * bandCount N), g q := by
  classical
  let w : BemocRingIndex N → ℕ :=
    fun p ↦ (bemocRingFamily N p).population
  let T := Finset.Icc 1 (30 * bandCount N)
  have hmaps : ∀ p ∈ (Finset.univ : Finset (BemocRingIndex N)),
      w p ∈ T := by
    intro p hp
    exact Finset.mem_Icc.mpr
      ⟨concrete_bemocRingFamily_population_pos hM p,
        bemocRingFamily_population_le_thirty_mul_bandCount (by omega) p⟩
  have hfiber :
      (∑ q ∈ T, ∑ p ∈ (Finset.univ : Finset (BemocRingIndex N))
          with w p = q, g q) =
        ∑ p : BemocRingIndex N, g (w p) :=
    Finset.sum_fiberwise_of_maps_to' hmaps g
  rw [← hfiber]
  calc
    (∑ q ∈ T, ∑ p ∈ (Finset.univ : Finset (BemocRingIndex N))
        with w p = q, g q) ≤
        ∑ q ∈ T, 7 * g q := by
      apply Finset.sum_le_sum
      intro q hq
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by
          exact_mod_cast bemoc_population_fiber_card_le_seven
            (N := N) (q := q) hM)
        (hg q)
    _ = 7 * ∑ q ∈ T, g q := by rw [Finset.mul_sum]

theorem bemoc_population_double_gcd_sum_le
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    (∑ p : BemocRingIndex N, ∑ q : BemocRingIndex N,
      gcdArithmeticWeight α
        (bemocRingFamily N p).population
        (bemocRingFamily N q).population) ≤
      (49 * 900 * gcdArithmeticConstant α) *
        (bandCount N : ℝ) ^ 2 := by
  let X := 30 * bandCount N
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hinner (p : BemocRingIndex N) :
      (∑ q : BemocRingIndex N,
        gcdArithmeticWeight α
          (bemocRingFamily N p).population
          (bemocRingFamily N q).population) ≤
        7 * ∑ r ∈ Finset.Icc 1 X,
          gcdArithmeticWeight α
            (bemocRingFamily N p).population r := by
    exact bemoc_population_sum_le_seven hM
      (fun r ↦ gcdArithmeticWeight α
        (bemocRingFamily N p).population r)
      (fun r ↦ gcdArithmeticWeight_nonneg α _ r)
  calc
    (∑ p : BemocRingIndex N, ∑ q : BemocRingIndex N,
        gcdArithmeticWeight α
          (bemocRingFamily N p).population
          (bemocRingFamily N q).population) ≤
        ∑ p : BemocRingIndex N,
          7 * ∑ r ∈ Finset.Icc 1 X,
            gcdArithmeticWeight α
              (bemocRingFamily N p).population r :=
      Finset.sum_le_sum fun p hp ↦ hinner p
    _ = 7 * ∑ r ∈ Finset.Icc 1 X,
          ∑ p : BemocRingIndex N,
            gcdArithmeticWeight α
              (bemocRingFamily N p).population r := by
      rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ 7 * ∑ r ∈ Finset.Icc 1 X,
          (7 * ∑ q ∈ Finset.Icc 1 X,
            gcdArithmeticWeight α q r) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro r hr
        exact bemoc_population_sum_le_seven hM
          (fun q ↦ gcdArithmeticWeight α q r)
          (fun q ↦ gcdArithmeticWeight_nonneg α q r)
      · norm_num
    _ = 49 * (∑ q ∈ Finset.Icc 1 X, ∑ r ∈ Finset.Icc 1 X,
          gcdArithmeticWeight α q r) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      ring_nf
    _ ≤ 49 * (gcdArithmeticConstant α * (X : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
        (gcd_arithmetic_double_sum_le hα0 hα2 hX)
      norm_num
    _ = (49 * 900 * gcdArithmeticConstant α) *
        (bandCount N : ℝ) ^ 2 := by
      dsimp [X]
      push_cast
      norm_num [mul_pow]
      ring

/-! ## Restoring the geometric radius factor -/

noncomputable def crossRingPairWeight
    (α : ℝ) (P Q : OccupiedRing) : ℝ :=
  (P.radius * Q.radius) ^ (α / 2) *
    (Nat.gcd P.population Q.population : ℝ) ^ (1 + α) /
      (((P.population : ℝ) * (Q.population : ℝ)) ^ α)

theorem crossRingPairWeight_nonneg (α : ℝ) (P Q : OccupiedRing) :
    0 ≤ crossRingPairWeight α P Q := by
  unfold crossRingPairWeight
  exact div_nonneg
    (mul_nonneg
      (Real.rpow_nonneg
        (mul_nonneg P.radius_nonneg Q.radius_nonneg) (α / 2))
      (Real.rpow_nonneg (by positivity) (1 + α)))
    (Real.rpow_nonneg (by positivity) α)

private theorem crossRingPairWeight_le_scaled_gcdArithmetic
    {α M : ℝ} (hα0 : 0 < α) (hM : 0 < M)
    (P Q : OccupiedRing)
    (hP : 0 < P.population) (hQ : 0 < Q.population)
    (hlowerP : M * P.radius ≤ 2 * (P.population : ℝ))
    (hlowerQ : M * Q.radius ≤ 2 * (Q.population : ℝ)) :
    crossRingPairWeight α P Q ≤
      (2 : ℝ) ^ α * M ^ (-α) *
        gcdArithmeticWeight α P.population Q.population := by
  let a : ℝ := α / 2
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have hq : (0 : ℝ) < P.population := by exact_mod_cast hP
  have hr : (0 : ℝ) < Q.population := by exact_mod_cast hQ
  have hbaseP :
      P.radius ≤ 2 * (P.population : ℝ) / M := by
    apply (le_div_iff₀ hM).2
    nlinarith [hlowerP]
  have hbaseQ :
      Q.radius ≤ 2 * (Q.population : ℝ) / M := by
    apply (le_div_iff₀ hM).2
    nlinarith [hlowerQ]
  have hpowP :
      P.radius ^ a ≤ (2 * (P.population : ℝ) / M) ^ a :=
    Real.rpow_le_rpow P.radius_nonneg hbaseP ha0
  have hpowQ :
      Q.radius ^ a ≤ (2 * (Q.population : ℝ) / M) ^ a :=
    Real.rpow_le_rpow Q.radius_nonneg hbaseQ ha0
  have hprodPow :
      (P.radius * Q.radius) ^ a ≤
        (2 * (P.population : ℝ) / M) ^ a *
          (2 * (Q.population : ℝ) / M) ^ a := by
    rw [Real.mul_rpow P.radius_nonneg Q.radius_nonneg]
    exact mul_le_mul hpowP hpowQ
      (Real.rpow_nonneg Q.radius_nonneg a)
      (Real.rpow_nonneg (by positivity) a)
  let F : ℝ :=
    (Nat.gcd P.population Q.population : ℝ) ^ (1 + α) /
      (((P.population : ℝ) * (Q.population : ℝ)) ^ α)
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  unfold crossRingPairWeight
  change
    (P.radius * Q.radius) ^ a *
        (Nat.gcd P.population Q.population : ℝ) ^ (1 + α) /
          (((P.population : ℝ) * (Q.population : ℝ)) ^ α) ≤ _
  calc
    (P.radius * Q.radius) ^ a *
        (Nat.gcd P.population Q.population : ℝ) ^ (1 + α) /
          (((P.population : ℝ) * (Q.population : ℝ)) ^ α) =
        (P.radius * Q.radius) ^ a * F := by
      dsimp [F]
      ring
    _ ≤ ((2 * (P.population : ℝ) / M) ^ a *
          (2 * (Q.population : ℝ) / M) ^ a) * F :=
      mul_le_mul_of_nonneg_right hprodPow hF
    _ = (2 : ℝ) ^ α * M ^ (-α) *
          gcdArithmeticWeight α P.population Q.population := by
      have htwo : (0 : ℝ) < 2 := by norm_num
      have htwoPow :
          (2 : ℝ) ^ a * (2 : ℝ) ^ a = (2 : ℝ) ^ α := by
        rw [← Real.rpow_add htwo]
        dsimp [a]
        congr 1
        ring
      have hMpow :
          ((M ^ a)⁻¹ * (M ^ a)⁻¹) = M ^ (-α) := by
        calc
          (M ^ a)⁻¹ * (M ^ a)⁻¹ =
              M ^ (-a) * M ^ (-a) := by
            rw [Real.rpow_neg hM.le]
          _ = M ^ ((-a) + (-a)) :=
            (Real.rpow_add hM (-a) (-a)).symm
          _ = M ^ (-α) := by
            dsimp [a]
            congr 1
            ring
      have hqpow :
          (P.population : ℝ) ^ a *
              ((P.population : ℝ) ^ α)⁻¹ =
            (P.population : ℝ) ^ (-a) := by
        rw [← Real.rpow_neg hq.le, ← Real.rpow_add hq]
        congr 1
        ring
      have hrpow :
          (Q.population : ℝ) ^ a *
              ((Q.population : ℝ) ^ α)⁻¹ =
            (Q.population : ℝ) ^ (-a) := by
        rw [← Real.rpow_neg hr.le, ← Real.rpow_add hr]
        congr 1
        ring
      dsimp [F]
      rw [Real.div_rpow (mul_nonneg (by norm_num) hq.le) hM.le,
        Real.div_rpow (mul_nonneg (by norm_num) hr.le) hM.le,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hq.le,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le,
        Real.mul_rpow hq.le hr.le]
      simp only [div_eq_mul_inv, mul_inv_rev]
      unfold gcdArithmeticWeight
      calc
        (2 ^ a * (P.population : ℝ) ^ a * (M ^ a)⁻¹ *
              (2 ^ a * (Q.population : ℝ) ^ a * (M ^ a)⁻¹) *
              ((Nat.gcd P.population Q.population : ℝ) ^ (1 + α) *
                (((Q.population : ℝ) ^ α)⁻¹ *
                  ((P.population : ℝ) ^ α)⁻¹))) =
            ((2 : ℝ) ^ a * (2 : ℝ) ^ a) *
              ((M ^ a)⁻¹ * (M ^ a)⁻¹) *
              (Nat.gcd P.population Q.population : ℝ) ^ (1 + α) *
              ((P.population : ℝ) ^ a *
                ((P.population : ℝ) ^ α)⁻¹) *
              ((Q.population : ℝ) ^ a *
                ((Q.population : ℝ) ^ α)⁻¹) := by ring
        _ = (2 : ℝ) ^ α * M ^ (-α) *
              ((Nat.gcd P.population Q.population : ℝ) ^ (1 + α) *
                (P.population : ℝ) ^ (-a) *
                (Q.population : ℝ) ^ (-a)) := by
          rw [htwoPow, hMpow, hqpow, hrpow]
          ring
        _ = (2 : ℝ) ^ α * M ^ (-α) *
              ((Nat.gcd P.population Q.population : ℝ) ^ (1 + α) *
                (P.population : ℝ) ^ (-α / 2) *
                (Q.population : ℝ) ^ (-α / 2)) := by
          dsimp [a]
          have hexp : -(α / 2) = -α / 2 := by ring
          rw [hexp]
        _ = _ := by ring

theorem bemoc_crossRingPairWeight_sum_le
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    (∑ p : BemocRingIndex N, ∑ q : BemocRingIndex N,
      crossRingPairWeight α
        (bemocRingFamily N p) (bemocRingFamily N q)) ≤
      ((2 : ℝ) ^ α * (49 * 900 * gcdArithmeticConstant α)) *
        (bandCount N : ℝ) ^ (2 - α) := by
  let M : ℝ := bandCount N
  have hMpos : 0 < M := by
    dsimp [M]
    exact_mod_cast (show 0 < bandCount N by omega)
  have hterm (p q : BemocRingIndex N) :
      crossRingPairWeight α (bemocRingFamily N p) (bemocRingFamily N q) ≤
        (2 : ℝ) ^ α * M ^ (-α) *
          gcdArithmeticWeight α
            (bemocRingFamily N p).population
            (bemocRingFamily N q).population := by
    apply crossRingPairWeight_le_scaled_gcdArithmetic hα0 hMpos
    · exact concrete_bemocRingFamily_population_pos hM p
    · exact concrete_bemocRingFamily_population_pos hM q
    · simpa [M] using concrete_bemocRingFamily_lower_comparison hM p
    · simpa [M] using concrete_bemocRingFamily_lower_comparison hM q
  calc
    (∑ p : BemocRingIndex N, ∑ q : BemocRingIndex N,
        crossRingPairWeight α
          (bemocRingFamily N p) (bemocRingFamily N q)) ≤
        ∑ p : BemocRingIndex N, ∑ q : BemocRingIndex N,
          ((2 : ℝ) ^ α * M ^ (-α) *
            gcdArithmeticWeight α
              (bemocRingFamily N p).population
              (bemocRingFamily N q).population) :=
      Finset.sum_le_sum fun p hp ↦ Finset.sum_le_sum fun q hq ↦ hterm p q
    _ = ((2 : ℝ) ^ α * M ^ (-α)) *
          (∑ p : BemocRingIndex N, ∑ q : BemocRingIndex N,
            gcdArithmeticWeight α
              (bemocRingFamily N p).population
              (bemocRingFamily N q).population) := by
      simp_rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ α * M ^ (-α)) *
          ((49 * 900 * gcdArithmeticConstant α) * M ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [M] using bemoc_population_double_gcd_sum_le
          hα0 hα2 hM
      · positivity
    _ = ((2 : ℝ) ^ α * (49 * 900 * gcdArithmeticConstant α)) *
          M ^ (2 - α) := by
      have hMpow :
          M ^ (-α) * M ^ (2 : ℝ) = M ^ (2 - α) := by
        rw [← Real.rpow_add hMpos]
        congr 1
        ring
      rw [show M ^ (2 : ℕ) = M ^ (2 : ℝ) by
        exact (Real.rpow_natCast M 2).symm, ← hMpow]
      ring
    _ = ((2 : ℝ) ^ α * (49 * 900 * gcdArithmeticConstant α)) *
          (bandCount N : ℝ) ^ (2 - α) := by rfl

/-! ## The concrete cross-ring endpoint -/

theorem exists_bemocCrossRingDeficit_bandCount_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      |bemocCrossRingDeficit α N| ≤
        C * (bandCount N : ℝ) ^ (2 - α) := by
  obtain ⟨C₀, hC₀, hpair⟩ :=
    exists_discreteRingPairDeficit_bound hα0 hα2
  let K : ℝ :=
    (2 : ℝ) ^ α * (49 * 900 * gcdArithmeticConstant α)
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (by positivity)
      (mul_pos (by norm_num) (gcdArithmeticConstant_pos hα0 hα2))
  refine ⟨C₀ * K, mul_pos hC₀ hK, ?_⟩
  intro N hN
  have hM : 3 ≤ bandCount N := three_le_bandCount_of_36_le hN
  let E : BemocRingIndex N → BemocRingIndex N → ℝ :=
    fun p q ↦
      if p ≠ q then
        continuousRingPairEnergy
            (bemocRingFamily N p) (bemocRingFamily N q) α -
          discreteRingPairEnergy α
            (bemocRingFamily N p) (bemocRingFamily N q)
      else 0
  have hdecomp :
      bemocCrossRingDeficit α N = ∑ p, ∑ q, E p q := by
    unfold bemocCrossRingDeficit
    rw [crossRingDeficit_eq_sum_pairDeficits]
  have htriangle :
      |bemocCrossRingDeficit α N| ≤
        ∑ p : BemocRingIndex N, ∑ q : BemocRingIndex N, |E p q| := by
    rw [hdecomp]
    calc
      |∑ p : BemocRingIndex N, ∑ q : BemocRingIndex N, E p q| ≤
          ∑ p : BemocRingIndex N, |∑ q : BemocRingIndex N, E p q| := by
        simpa using Finset.abs_sum_le_sum_abs
          (fun p : BemocRingIndex N ↦ ∑ q : BemocRingIndex N, E p q)
          Finset.univ
      _ ≤ ∑ p : BemocRingIndex N,
          ∑ q : BemocRingIndex N, |E p q| := by
        apply Finset.sum_le_sum
        intro p hp
        simpa using Finset.abs_sum_le_sum_abs
          (fun q : BemocRingIndex N ↦ E p q) Finset.univ
  have hsumPair :
      (∑ p : BemocRingIndex N, ∑ q : BemocRingIndex N, |E p q|) ≤
        C₀ * ∑ p : BemocRingIndex N, ∑ q : BemocRingIndex N,
          crossRingPairWeight α
            (bemocRingFamily N p) (bemocRingFamily N q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    by_cases hpq : p ≠ q
    · dsimp [E]
      rw [if_pos hpq]
      have hp := hpair (bemocRingFamily N p) (bemocRingFamily N q)
          (concrete_bemocRingFamily_population_pos hM p)
          (concrete_bemocRingFamily_population_pos hM q)
      unfold crossRingPairWeight
      convert hp using 1 ; ring
    · dsimp [E]
      rw [if_neg hpq, abs_zero]
      exact mul_nonneg hC₀.le
        (crossRingPairWeight_nonneg α
          (bemocRingFamily N p) (bemocRingFamily N q))
  calc
    |bemocCrossRingDeficit α N| ≤
        ∑ p : BemocRingIndex N, ∑ q : BemocRingIndex N, |E p q| :=
      htriangle
    _ ≤ C₀ * ∑ p : BemocRingIndex N, ∑ q : BemocRingIndex N,
          crossRingPairWeight α
            (bemocRingFamily N p) (bemocRingFamily N q) := hsumPair
    _ ≤ C₀ * (K * (bandCount N : ℝ) ^ (2 - α)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [K] using bemoc_crossRingPairWeight_sum_le hα0 hα2 hM
      · exact hC₀.le
    _ = (C₀ * K) * (bandCount N : ℝ) ^ (2 - α) := by ring

/-- Cross-ring angular aliasing for the literal BEMOC construction, at the
same `N^(1-α/2)` scale as the latitude and within-ring estimates. -/
theorem exists_bemocCrossRingDeficit_concrete_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N ≥ 36,
      |bemocCrossRingDeficit α N| ≤
        C * (N : ℝ) ^ (1 - α / 2) := by
  obtain ⟨C, hC, hband⟩ :=
    exists_bemocCrossRingDeficit_bandCount_bound hα0 hα2
  refine ⟨C, hC, ?_⟩
  intro N hN
  exact (hband N hN).trans <|
    mul_le_mul_of_nonneg_left
      (bandCount_rpow_two_sub_le (N := N) hα2) hC.le

end BEMOC
