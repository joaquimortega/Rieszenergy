import BEMOCFormalization.ConcreteWithinRing

/-!
# A triangular-array transfer lemma for within-ring errors

This module is deliberately independent of the detailed BEMOC geometry.
The index type may vary with the row of the triangular array.
-/

open scoped BigOperators Topology
open Filter

namespace BEMOC

/-- A finite weighted average transfers a pointwise limit through a triangular
array when its total normalized mass converges and every fixed low-population
part has asymptotically zero normalized mass. -/
theorem tendsto_triangularArray_weighted_error
    {ι : ℕ → Type*} [∀ m, Fintype (ι m)]
    (a : ∀ m, ι m → ℝ) (population : ∀ m, ι m → ℕ)
    (e scale : ℕ → ℝ) (L K B : ℝ)
    (ha : ∀ m p, 0 ≤ a m p)
    (hscale : ∀ m, 0 < scale m)
    (he : Tendsto e atTop (𝓝 L))
    (heBound : ∀ w, |e w| ≤ B)
    (htotal : Tendsto
      (fun m => (∑ p : ι m, a m p) / scale m) atTop (𝓝 K))
    (hsmall : ∀ W : ℕ, Tendsto
      (fun m => (∑ p : ι m with population m p < W, a m p) / scale m)
      atTop (𝓝 0)) :
    Tendsto
      (fun m => (∑ p : ι m, a m p * e (population m p)) / scale m)
      atTop (𝓝 (K * L)) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let C : ℝ := B + |L|
  have hB : 0 ≤ B := (abs_nonneg (e 0)).trans (heBound 0)
  have hC : 0 ≤ C := add_nonneg hB (abs_nonneg L)
  let δ : ℝ := ε / (4 * (|K| + 2))
  have hδ : 0 < δ := by positivity
  have heEventually : ∀ᶠ w : ℕ in atTop, |e w - L| < δ := by
    simpa only [Real.dist_eq] using he.eventually (Metric.ball_mem_nhds L hδ)
  rw [eventually_atTop] at heEventually
  obtain ⟨W, hW⟩ := heEventually
  have htotalOne : ∀ᶠ m : ℕ in atTop,
      |(∑ p : ι m, a m p) / scale m - K| < 1 := by
    simpa only [Real.dist_eq] using
      htotal.eventually (Metric.ball_mem_nhds K zero_lt_one)
  have htotalEps : ∀ᶠ m : ℕ in atTop,
      |(∑ p : ι m, a m p) / scale m - K| <
        ε / (2 * (|L| + 1)) := by
    have hpos : 0 < ε / (2 * (|L| + 1)) := by positivity
    simpa only [Real.dist_eq] using
      htotal.eventually (Metric.ball_mem_nhds K hpos)
  have hsmallEps : ∀ᶠ m : ℕ in atTop,
      |(∑ p : ι m with population m p < W, a m p) / scale m| <
        ε / (4 * (C + 1)) := by
    have hpos : 0 < ε / (4 * (C + 1)) := by positivity
    simpa only [Real.dist_eq, sub_zero] using
      (hsmall W).eventually (Metric.ball_mem_nhds 0 hpos)
  rw [← eventually_atTop]
  filter_upwards [htotalOne, htotalEps, hsmallEps] with m hmOne hmEps hmSmall
  have hs : 0 < scale m := hscale m
  have htotalNonneg : 0 ≤ (∑ p : ι m, a m p) / scale m :=
    div_nonneg (Finset.sum_nonneg fun p _ => ha m p) hs.le
  have htotalUpper : (∑ p : ι m, a m p) / scale m < |K| + 2 := by
    have hK : K ≤ |K| := le_abs_self K
    rw [abs_lt] at hmOne
    linarith
  have hsmallNonneg :
      0 ≤ (∑ p : ι m with population m p < W, a m p) / scale m :=
    div_nonneg (Finset.sum_nonneg fun p _ => ha m p) hs.le
  have hsmallUpper :
      (∑ p : ι m with population m p < W, a m p) / scale m <
        ε / (4 * (C + 1)) := by
    rw [abs_of_nonneg hsmallNonneg] at hmSmall
    exact hmSmall
  have hpoint (p : ι m) :
      a m p * |e (population m p) - L| ≤
        C * (if population m p < W then a m p else 0) + δ * a m p := by
    split_ifs with hp
    · have herr : |e (population m p) - L| ≤ C := by
        calc
          |e (population m p) - L| ≤ |e (population m p)| + |L| :=
            abs_sub _ _
          _ ≤ B + |L| := add_le_add_right (heBound _) _
          _ = C := rfl
      nlinarith [ha m p, hδ.le]
    · have hpW : W ≤ population m p := by omega
      have herr : |e (population m p) - L| < δ := hW _ hpW
      nlinarith [ha m p]
  have herrorSum :
      ∑ p : ι m, a m p * |e (population m p) - L| ≤
        C * (∑ p : ι m with population m p < W, a m p) +
          δ * (∑ p : ι m, a m p) := by
    calc
      ∑ p : ι m, a m p * |e (population m p) - L| ≤
          ∑ p : ι m,
            (C * (if population m p < W then a m p else 0) + δ * a m p) :=
        Finset.sum_le_sum fun p _ => hpoint p
      _ = C * (∑ p : ι m with population m p < W, a m p) +
          δ * (∑ p : ι m, a m p) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        congr 2
        rw [← Finset.sum_filter]
  have hnormalizedError :
      |(∑ p : ι m, a m p * e (population m p)) / scale m -
          L * ((∑ p : ι m, a m p) / scale m)| < ε / 2 := by
    have habs :
        |(∑ p : ι m, a m p * e (population m p)) -
            L * (∑ p : ι m, a m p)| ≤
          ∑ p : ι m, a m p * |e (population m p) - L| := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      calc
        |∑ p : ι m, (a m p * e (population m p) - L * a m p)| ≤
            ∑ p : ι m, |a m p * e (population m p) - L * a m p| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ p : ι m, a m p * |e (population m p) - L| := by
          apply Finset.sum_congr rfl
          intro p hp
          calc
            |a m p * e (population m p) - L * a m p| =
                |a m p * (e (population m p) - L)| := by congr 1 ; ring
            _ = a m p * |e (population m p) - L| := by
              rw [abs_mul, abs_of_nonneg (ha m p)]
    have hdiv :
        |(∑ p : ι m, a m p * e (population m p)) / scale m -
            L * ((∑ p : ι m, a m p) / scale m)| ≤
          C * ((∑ p : ι m with population m p < W, a m p) / scale m) +
            δ * ((∑ p : ι m, a m p) / scale m) := by
      have halg :
          (∑ p : ι m, a m p * e (population m p)) / scale m -
              L * ((∑ p : ι m, a m p) / scale m) =
            ((∑ p : ι m, a m p * e (population m p)) -
              L * (∑ p : ι m, a m p)) / scale m := by ring
      rw [halg, abs_div, abs_of_pos hs]
      calc
        |(∑ p : ι m, a m p * e (population m p)) -
            L * ∑ p : ι m, a m p| / scale m ≤
            (∑ p : ι m, a m p * |e (population m p) - L|) / scale m :=
          div_le_div_of_nonneg_right habs hs.le
        _ ≤ (C * (∑ p : ι m with population m p < W, a m p) +
              δ * (∑ p : ι m, a m p)) / scale m :=
          div_le_div_of_nonneg_right herrorSum hs.le
        _ = C * ((∑ p : ι m with population m p < W, a m p) / scale m) +
              δ * ((∑ p : ι m, a m p) / scale m) := by ring
    have hlow :
        C * ((∑ p : ι m with population m p < W, a m p) / scale m) < ε / 4 := by
      by_cases hCzero : C = 0
      · simp [hCzero]
        linarith
      · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
        calc
          C * ((∑ p : ι m with population m p < W, a m p) / scale m) <
              C * (ε / (4 * (C + 1))) :=
            mul_lt_mul_of_pos_left hsmallUpper hCpos
          _ < ε / 4 := by
            have hden : 0 < C + 1 := by positivity
            have hratio : C / (C + 1) < 1 := by
              apply (div_lt_one hden).2
              linarith
            have heq : C * (ε / (4 * (C + 1))) =
                (ε / 4) * (C / (C + 1)) := by
              field_simp [hden.ne']
              ; ring
            rw [heq]
            nlinarith
    have hhigh : δ * ((∑ p : ι m, a m p) / scale m) < ε / 4 := by
      have hfac : 0 ≤ (∑ p : ι m, a m p) / scale m := htotalNonneg
      calc
        δ * ((∑ p : ι m, a m p) / scale m) < δ * (|K| + 2) :=
          mul_lt_mul_of_pos_left htotalUpper hδ
        _ = ε / 4 := by
          dsimp [δ]
          have hden : 4 * (|K| + 2) ≠ 0 := by positivity
          field_simp [hden]
          ; ring
    linarith
  rw [Real.dist_eq]
  calc
    |(∑ p : ι m, a m p * e (population m p)) / scale m - K * L| =
        |((∑ p : ι m, a m p * e (population m p)) / scale m -
            L * ((∑ p : ι m, a m p) / scale m)) +
          L * ((∑ p : ι m, a m p) / scale m - K)| := by
      congr 1
      ring
    _ ≤ |(∑ p : ι m, a m p * e (population m p)) / scale m -
            L * ((∑ p : ι m, a m p) / scale m)| +
          |L| * |(∑ p : ι m, a m p) / scale m - K| := by
      calc
        _ ≤ |(∑ p : ι m, a m p * e (population m p)) / scale m -
              L * ((∑ p : ι m, a m p) / scale m)| +
            |L * ((∑ p : ι m, a m p) / scale m - K)| := abs_add _ _
        _ = _ := by rw [abs_mul]
    _ < ε := by
      have hsecond :
          |L| * |(∑ p : ι m, a m p) / scale m - K| < ε / 2 := by
        by_cases hL : L = 0
        · simp [hL]
          linarith
        · calc
            |L| * |(∑ p : ι m, a m p) / scale m - K| <
                |L| * (ε / (2 * (|L| + 1))) :=
              mul_lt_mul_of_pos_left hmEps (abs_pos.mpr hL)
            _ < ε / 2 := by
              have hden : 0 < |L| + 1 := by positivity
              have hratio : |L| / (|L| + 1) < 1 := by
                exact (div_lt_one hden).2 (by linarith [abs_nonneg L])
              have heq : |L| * (ε / (2 * (|L| + 1))) =
                  (ε / 2) * (|L| / (|L| + 1)) := by
                field_simp [hden.ne']
                ; ring
              rw [heq]
              nlinarith
      linarith

/-! ## Direct BEMOC specialization

The normalized circle error is multiplied by the natural geometric weight
`radius^α * population^(1-α)`.  The product is the within-ring summand after
the elementary cancellation of population powers (for positive populations).
-/

/-- The generic transfer theorem specialized to the square BEMOC subsequence
and the normalized regular-polygon self-deficit.  Its only remaining inputs are
the two geometric mass limits. -/
theorem tendsto_bemoc_weighted_normalizedCircleSelfDeficit_four_mul_sq
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (scale : ℕ → ℝ) (K : ℝ)
    (hscale : ∀ m, 0 < scale m)
    (htotal : Tendsto
      (fun m => bemocWeightedRadiusPopulationSum α (4 * m ^ 2) / scale m)
      atTop (𝓝 K))
    (hsmall : ∀ W : ℕ, Tendsto
      (fun m =>
        (∑ p : BemocRingIndex (4 * m ^ 2) with
            (bemocRingFamily (4 * m ^ 2) p).population < W,
          (bemocRingFamily (4 * m ^ 2) p).radius ^ α *
            ((bemocRingFamily (4 * m ^ 2) p).population : ℝ) ^ (1 - α)) /
          scale m)
      atTop (𝓝 0)) :
    Tendsto
      (fun m =>
        (∑ p : BemocRingIndex (4 * m ^ 2),
          ((bemocRingFamily (4 * m ^ 2) p).radius ^ α *
              ((bemocRingFamily (4 * m ^ 2) p).population : ℝ) ^ (1 - α)) *
            (((bemocRingFamily (4 * m ^ 2) p).population : ℝ) ^ (α - 1) *
              circleSelfDeficit α
                (bemocRingFamily (4 * m ^ 2) p).population)) /
          scale m)
      atTop
      (𝓝 (K * (-2 * (2 * Real.pi) ^ α * realRiemannZeta (-α)))) := by
  let e : ℕ → ℝ := fun w =>
    (w : ℝ) ^ (α - 1) * circleSelfDeficit α w
  let L : ℝ := -2 * (2 * Real.pi) ^ α * realRiemannZeta (-α)
  have he : Tendsto e atTop (𝓝 L) := by
    simpa only [e, L] using
      tendsto_normalizedCircleSelfDeficit
        (hasCircleEulerMaclaurin hα0 hα2)
  have heBounded : Bornology.IsBounded (Set.range e) :=
    Metric.isBounded_range_of_tendsto _ he
  obtain ⟨B, hBpos, hB⟩ := heBounded.exists_pos_norm_le
  have hBabs : ∀ w, |e w| ≤ B := by
    intro w
    simpa only [Real.norm_eq_abs] using hB (e w) ⟨w, rfl⟩
  let weight : ∀ m, BemocRingIndex (4 * m ^ 2) → ℝ := fun m p =>
    (bemocRingFamily (4 * m ^ 2) p).radius ^ α *
      ((bemocRingFamily (4 * m ^ 2) p).population : ℝ) ^ (1 - α)
  have hweight : ∀ m p, 0 ≤ weight m p := by
    intro m p
    exact mul_nonneg
      (Real.rpow_nonneg (bemocRingFamily (4 * m ^ 2) p).radius_nonneg α)
      (Real.rpow_nonneg (Nat.cast_nonneg _) (1 - α))
  have htransfer := tendsto_triangularArray_weighted_error
    (ι := fun m => BemocRingIndex (4 * m ^ 2))
    weight
    (fun m p => (bemocRingFamily (4 * m ^ 2) p).population)
    e scale L K B hweight hscale he hBabs
    (by
      simpa only [weight, bemocWeightedRadiusPopulationSum] using htotal)
    (by
      intro W
      simpa only [weight] using hsmall W)
  simpa only [weight, e, L] using htransfer

/-! ## Vanishing mass of bounded populations on the square subsequence -/

@[simp] theorem scratch_bandCount_four_mul_sq (m : ℕ) :
    bandCount (4 * m ^ 2) = m := by
  simpa [bandCount] using Nat.sqrt_eq' m

/-- A normalization equal to `m^(2-α)` for positive `m`, but positive also
in the irrelevant row `m = 0`. -/
noncomputable def scratchWithinRingScale (α : ℝ) (m : ℕ) : ℝ :=
  ((max 1 m : ℕ) : ℝ) ^ (2 - α)

theorem scratchWithinRingScale_pos (α : ℝ) (m : ℕ) :
    0 < scratchWithinRingScale α m := by
  unfold scratchWithinRingScale
  positivity

theorem scratchWithinRingScale_eq {α : ℝ} {m : ℕ} (hm : 1 ≤ m) :
    scratchWithinRingScale α m = (m : ℝ) ^ (2 - α) := by
  simp [scratchWithinRingScale, max_eq_right hm]

/-- A finite, deliberately nonoptimal bound for the population power on the
set `0 < w < W`. -/
noncomputable def scratchPopulationPowerBound (α : ℝ) (W : ℕ) : ℝ :=
  ∑ w ∈ Finset.range W, (w : ℝ) ^ (1 - α)

theorem scratchPopulationPowerBound_nonneg (α : ℝ) (W : ℕ) :
    0 ≤ scratchPopulationPowerBound α W := by
  unfold scratchPopulationPowerBound
  exact Finset.sum_nonneg fun w _ => Real.rpow_nonneg (Nat.cast_nonneg w) _

theorem scratch_population_rpow_le_bound {α : ℝ} {W w : ℕ}
    (hw : w < W) :
    (w : ℝ) ^ (1 - α) ≤ scratchPopulationPowerBound α W := by
  unfold scratchPopulationPowerBound
  exact Finset.single_le_sum
    (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _) (Finset.mem_range.mpr hw)

noncomputable def scratchBemocLowPopulationMass
    (α : ℝ) (W m : ℕ) : ℝ :=
  ∑ p : BemocRingIndex (4 * m ^ 2) with
      (bemocRingFamily (4 * m ^ 2) p).population < W,
    (bemocRingFamily (4 * m ^ 2) p).radius ^ α *
      ((bemocRingFamily (4 * m ^ 2) p).population : ℝ) ^ (1 - α)

theorem scratch_low_population_ring_weight_le
    {α : ℝ} (hα0 : 0 < α) {W m : ℕ} (hm : 3 ≤ m)
    (p : BemocRingIndex (4 * m ^ 2))
    (hpW : (bemocRingFamily (4 * m ^ 2) p).population < W) :
    (bemocRingFamily (4 * m ^ 2) p).radius ^ α *
        ((bemocRingFamily (4 * m ^ 2) p).population : ℝ) ^ (1 - α) ≤
      (((2 * W : ℕ) : ℝ) / (m : ℝ)) ^ α *
        scratchPopulationPowerBound α W := by
  let R := bemocRingFamily (4 * m ^ 2) p
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hM : 3 ≤ bandCount (4 * m ^ 2) := by simpa using hm
  have hpop : 0 < R.population := by
    exact concrete_bemocRingFamily_population_pos hM p
  have hcomparison : (m : ℝ) * R.radius ≤ 2 * (R.population : ℝ) := by
    simpa [R] using concrete_bemocRingFamily_lower_comparison hM p
  have hpopW : (R.population : ℝ) ≤ W := by
    exact_mod_cast (Nat.le_of_lt hpW)
  have hradius : R.radius ≤ (((2 * W : ℕ) : ℝ) / (m : ℝ)) := by
    apply (le_div_iff₀ hmR).2
    have htwo : 2 * (R.population : ℝ) ≤ (((2 * W : ℕ) : ℝ)) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      linarith
    nlinarith
  have hrpow : R.radius ^ α ≤
      (((2 * W : ℕ) : ℝ) / (m : ℝ)) ^ α :=
    Real.rpow_le_rpow R.radius_nonneg hradius hα0.le
  have hpopulationPower :
      (R.population : ℝ) ^ (1 - α) ≤ scratchPopulationPowerBound α W := by
    exact scratch_population_rpow_le_bound hpW
  exact mul_le_mul hrpow hpopulationPower
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hmR.le) _)

theorem scratch_low_population_mass_eventual_le
    {α : ℝ} (hα0 : 0 < α) (W : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      scratchBemocLowPopulationMass α W m /
          scratchWithinRingScale α m ≤
        (4 * (((2 * W : ℕ) : ℝ) ^ α) *
            scratchPopulationPowerBound α W) / (m : ℝ) := by
  filter_upwards [eventually_ge_atTop 3] with m hm
  let D : ℝ := scratchPopulationPowerBound α W
  let Q : ℝ := ((((2 * W : ℕ) : ℝ) / (m : ℝ)) ^ α) * D
  have hm1 : 1 ≤ m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hQ : 0 ≤ Q := mul_nonneg
    (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hmR.le) _)
    (scratchPopulationPowerBound_nonneg α W)
  have hcard : Fintype.card (BemocRingIndex (4 * m ^ 2)) ≤ 4 * m := by
    calc
      Fintype.card (BemocRingIndex (4 * m ^ 2)) =
          4 * bandCount (4 * m ^ 2) - 3 :=
        card_bemocRingIndex (N := 4 * m ^ 2) (by simpa using hm1)
      _ ≤ 4 * m := by simp
  have hsum : scratchBemocLowPopulationMass α W m ≤ (4 * m : ℕ) * Q := by
    unfold scratchBemocLowPopulationMass
    calc
      (∑ p : BemocRingIndex (4 * m ^ 2) with
          (bemocRingFamily (4 * m ^ 2) p).population < W,
          (bemocRingFamily (4 * m ^ 2) p).radius ^ α *
            ((bemocRingFamily (4 * m ^ 2) p).population : ℝ) ^ (1 - α)) ≤
          ∑ _p : BemocRingIndex (4 * m ^ 2) with
            (bemocRingFamily (4 * m ^ 2) _p).population < W, Q := by
        apply Finset.sum_le_sum
        intro p hp
        exact scratch_low_population_ring_weight_le hα0 hm p
          (Finset.mem_filter.mp hp).2
      _ = ((Finset.univ.filter fun p : BemocRingIndex (4 * m ^ 2) =>
          (bemocRingFamily (4 * m ^ 2) p).population < W).card : ℕ) * Q := by
        simp
      _ ≤ (4 * m : ℕ) * Q := by
        apply mul_le_mul_of_nonneg_right _ hQ
        exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans
          (by simpa using hcard)
  have hscaleEq : scratchWithinRingScale α m = (m : ℝ) ^ (2 - α) :=
    scratchWithinRingScale_eq hm1
  have hpow : (m : ℝ) ^ α * (m : ℝ) ^ (2 - α) = (m : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_add hmR]
    congr 1
    ring
  have hnormalize :
      ((4 * m : ℕ) * Q) / scratchWithinRingScale α m =
        (4 * (((2 * W : ℕ) : ℝ) ^ α) * D) / (m : ℝ) := by
    rw [hscaleEq]
    dsimp [Q]
    rw [Real.div_rpow (Nat.cast_nonneg _) hmR.le]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      (4 * (m : ℝ) *
            ((((2 : ℝ) * W) ^ α / (m : ℝ) ^ α) * D)) /
          (m : ℝ) ^ (2 - α) =
          (4 * (((2 : ℝ) * W) ^ α) * D * (m : ℝ)) /
            ((m : ℝ) ^ α * (m : ℝ) ^ (2 - α)) := by ring
      _ = (4 * (((2 : ℝ) * W) ^ α) * D * (m : ℝ)) /
            (m : ℝ) ^ (2 : ℝ) := by rw [hpow]
      _ = (4 * (((2 : ℝ) * W) ^ α) * D) / (m : ℝ) := by
        rw [Real.rpow_two]
        field_simp [hmR.ne']
        ; ring
  rw [← hnormalize]
  exact div_le_div_of_nonneg_right hsum (scratchWithinRingScale_pos α m).le

theorem tendsto_scratchBemocLowPopulationMass_div_scale
    {α : ℝ} (hα0 : 0 < α) (W : ℕ) :
    Tendsto
      (fun m => scratchBemocLowPopulationMass α W m /
        scratchWithinRingScale α m)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun m =>
      div_nonneg
        (Finset.sum_nonneg fun p _ => mul_nonneg
          (Real.rpow_nonneg (bemocRingFamily (4 * m ^ 2) p).radius_nonneg α)
          (Real.rpow_nonneg (Nat.cast_nonneg _) (1 - α)))
        (scratchWithinRingScale_pos α m).le
  · exact scratch_low_population_mass_eventual_le hα0 W
  · exact tendsto_const_div_atTop_nhds_zero_nat
      (4 * (((2 * W : ℕ) : ℝ) ^ α) * scratchPopulationPowerBound α W)

end BEMOC
