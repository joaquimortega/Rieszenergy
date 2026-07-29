import BEMOCFormalization.GeometricWithinRingLimit
import BEMOCFormalization.WithinRingTransfer

open scoped BigOperators Topology Interval
open Filter
open MeasureTheory

namespace BEMOC

noncomputable def squareWithinRingScale (α : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 1 else (m : ℝ) ^ (2 - α)

theorem squareWithinRingScale_pos {α : ℝ} (_hα2 : α < 2) (m : ℕ) :
    0 < squareWithinRingScale α m := by
  rw [squareWithinRingScale]
  split_ifs with hm
  · norm_num
  · exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) _

theorem eventually_squareWithinRingScale_eq (α : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      squareWithinRingScale α m = (m : ℝ) ^ (2 - α) := by
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [squareWithinRingScale, if_neg (by omega : m ≠ 0)]

theorem squareWithinRingScale_eq_scratch (α : ℝ) (m : ℕ) :
    squareWithinRingScale α m = scratchWithinRingScale α m := by
  by_cases hm : m = 0
  · subst m
    simp [squareWithinRingScale, scratchWithinRingScale]
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    rw [squareWithinRingScale, if_neg hm, scratchWithinRingScale,
      max_eq_right hm1]

theorem tendsto_bemocLowPopulationMass_div_squareScale
    {α : ℝ} (hα0 : 0 < α) (W : ℕ) :
    Tendsto
      (fun m : ℕ =>
        (∑ p : BemocRingIndex (4 * m ^ 2) with
          (bemocRingFamily (4 * m ^ 2) p).population < W,
            (bemocRingFamily (4 * m ^ 2) p).radius ^ α *
              ((bemocRingFamily (4 * m ^ 2) p).population : ℝ) ^ (1 - α)) /
          squareWithinRingScale α m)
      atTop (𝓝 0) := by
  simpa only [scratchBemocLowPopulationMass,
    ← squareWithinRingScale_eq_scratch] using
      tendsto_scratchBemocLowPopulationMass_div_scale hα0 W

noncomputable def normalizedCircleSelfDeficit (α : ℝ) (w : ℕ) : ℝ :=
  (w : ℝ) ^ (α - 1) * circleSelfDeficit α w

theorem tendsto_normalizedCircleSelfDeficit' {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    Tendsto (normalizedCircleSelfDeficit α) atTop
      (𝓝 (-2 * (2 * Real.pi) ^ α * realRiemannZeta (-α))) := by
  exact tendsto_normalizedCircleSelfDeficit
    (hasCircleEulerMaclaurin hα0 hα2)

theorem exists_uniform_normalizedCircleSelfDeficit_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ w : ℕ,
      |normalizedCircleSelfDeficit α w| ≤ B := by
  have ht := tendsto_normalizedCircleSelfDeficit' hα0 hα2
  have hb : Bornology.IsBounded (Set.range (normalizedCircleSelfDeficit α)) :=
    Metric.isBounded_range_of_tendsto _ ht
  obtain ⟨B, hB, hbound⟩ := hb.exists_pos_norm_le
  refine ⟨B, hB, fun w ↦ ?_⟩
  simpa only [Real.norm_eq_abs] using hbound _ ⟨w, rfl⟩

theorem radius_mul_circleSelfDeficit_factorization
    {α ρ : ℝ} {w : ℕ} (hw : 0 < w) :
    ρ ^ α * circleSelfDeficit α w =
      (ρ ^ α * (w : ℝ) ^ (1 - α)) *
        normalizedCircleSelfDeficit α w := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hpow : (w : ℝ) ^ (1 - α) * (w : ℝ) ^ (α - 1) = 1 := by
    rw [← Real.rpow_add hwR]
    norm_num
  rw [normalizedCircleSelfDeficit]
  calc
    ρ ^ α * circleSelfDeficit α w =
        ρ ^ α * (1 * circleSelfDeficit α w) := by ring
    _ = ρ ^ α * (((w : ℝ) ^ (1 - α) * (w : ℝ) ^ (α - 1)) *
          circleSelfDeficit α w) := by rw [hpow]
    _ = (ρ ^ α * (w : ℝ) ^ (1 - α)) *
          ((w : ℝ) ^ (α - 1) * circleSelfDeficit α w) := by
      ring

theorem bemocWithinRingDeficit_eq_weighted_normalizedCircle
    {α : ℝ} (hα : 0 < α) {N : ℕ} (hM : 3 ≤ bandCount N) :
    bemocWithinRingDeficit α N =
      ∑ p : BemocRingIndex N,
        ((bemocRingFamily N p).radius ^ α *
          ((bemocRingFamily N p).population : ℝ) ^ (1 - α)) *
            normalizedCircleSelfDeficit α (bemocRingFamily N p).population := by
  rw [bemocWithinRingDeficit_eq_aggregated hα]
  unfold aggregatedWithinRingDeficit
  apply Finset.sum_congr rfl
  intro p hp
  exact radius_mul_circleSelfDeficit_factorization
    (concrete_bemocRingFamily_population_pos hM p)

noncomputable def withinRingLimitProfile (α x : ℝ) : ℝ :=
  x * (2 - x ^ 2) ^ (α / 2)

theorem continuousOn_withinRingLimitProfile (α : ℝ) :
    ContinuousOn (withinRingLimitProfile α) (Set.Icc 0 1) := by
  apply continuousOn_id.mul
  apply (continuousOn_const.sub (continuousOn_id.pow 2)).rpow_const
  intro x hx
  left
  change 2 - x ^ 2 ≠ 0
  have hs := mul_self_le_mul_self hx.1 hx.2
  nlinarith

theorem integral_withinRingLimitProfile {α : ℝ} (hα : -2 < α) :
    (∫ x in (0 : ℝ)..1, withinRingLimitProfile α x) =
      (2 ^ (1 + α / 2) - 1) / (α + 2) := by
  let F : ℝ → ℝ := fun x => -(2 - x ^ 2) ^ (1 + α / 2) / (α + 2)
  have hden : α + 2 ≠ 0 := by linarith
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F (withinRingLimitProfile α x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hbase : 2 - x ^ 2 ≠ 0 := by
      rcases hx with ⟨hx0, hx1⟩
      nlinarith [sq_nonneg x]
    have hb : HasDerivAt (fun y : ℝ => 2 - y ^ 2) (-2 * x) x := by
      convert (hasDerivAt_const x 2).sub ((hasDerivAt_id x).pow 2) using 1 ;
        simp [id]
    have hp := hb.rpow_const (p := 1 + α / 2) (Or.inl hbase)
    have hF := hp.neg.div_const (α + 2)
    have hcoef :
        -(-2 * x * (1 + α / 2) *
            (2 - x ^ 2) ^ (1 + α / 2 - 1)) / (α + 2) =
          withinRingLimitProfile α x := by
      dsimp [withinRingLimitProfile]
      rw [show 1 + α / 2 - 1 = α / 2 by ring]
      field_simp [hden]
      ring
    simpa only [F, hcoef] using hF
  have hint : IntervalIntegrable (withinRingLimitProfile α) volume 0 1 :=
    (by
      have hc : ContinuousOn (withinRingLimitProfile α) [[(0 : ℝ), 1]] := by
        simpa only [Set.uIcc_of_le zero_le_one] using
          continuousOn_withinRingLimitProfile α
      exact hc.intervalIntegrable)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F]
  norm_num
  field_simp [hden]
  ring

theorem square_rpow_normalization {α : ℝ} {m : ℕ} (hm : 0 < m) :
    (((4 * m ^ 2 : ℕ) : ℝ) ^ (1 - α / 2)) =
      2 ^ (2 - α) * (m : ℝ) ^ (2 - α) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htwo : (0 : ℝ) < 2 := by norm_num
  push_cast
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4) (sq_nonneg (m : ℝ))]
  have h4 : (4 : ℝ) ^ (1 - α / 2) = 2 ^ (2 - α) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast]
    rw [← Real.rpow_mul htwo.le]
    congr 1
    ring
  have hm2 : ((m : ℝ) ^ 2) ^ (1 - α / 2) =
      (m : ℝ) ^ (2 - α) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hmR.le]
    congr 1
    ring
  rw [h4, hm2]

theorem circle_times_geometry_coefficient_eq (α : ℝ) :
    (-2 * (2 * Real.pi) ^ α * realRiemannZeta (-α)) *
          (2 * withinRingAsymptoticWeight α) /
        2 ^ (2 - α) =
      withinRingLimitCoefficient α := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hpow : 2 ^ (2 - α) * 2 ^ α = (4 : ℝ) := by
    rw [← Real.rpow_add htwo]
    norm_num
  have hden : (2 : ℝ) ^ (2 - α) ≠ 0 :=
    (Real.rpow_pos_of_pos htwo _).ne'
  have hfourpi : (4 * Real.pi) ^ α = 2 ^ α * (2 * Real.pi) ^ α := by
    rw [show 4 * Real.pi = 2 * (2 * Real.pi) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
  rw [withinRingLimitCoefficient, hfourpi]
  field_simp [hden]
  calc
    2 * (2 * Real.pi) ^ α * realRiemannZeta (-α) *
          (2 * withinRingAsymptoticWeight α) =
        4 * withinRingAsymptoticWeight α * (2 * Real.pi) ^ α *
          realRiemannZeta (-α) := by ring
    _ = ((2 : ℝ) ^ (2 - α) * 2 ^ α) *
          withinRingAsymptoticWeight α * (2 * Real.pi) ^ α *
            realRiemannZeta (-α) := by rw [hpow]
    _ = withinRingAsymptoticWeight α *
          (2 ^ α * (2 * Real.pi) ^ α) * realRiemannZeta (-α) *
            2 ^ (2 - α) := by ring

theorem tendsto_bemocWithinRingDeficit_four_mul_sq_of_geometry_of_small
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hgeometry : Tendsto
      (fun m : ℕ =>
        bemocWeightedRadiusPopulationSum α (4 * m ^ 2) /
          squareWithinRingScale α m)
      atTop (𝓝 (2 * withinRingAsymptoticWeight α)))
    (hsmall : ∀ W : ℕ, Tendsto
      (fun m : ℕ =>
        (∑ p : BemocRingIndex (4 * m ^ 2) with
          (bemocRingFamily (4 * m ^ 2) p).population < W,
            (bemocRingFamily (4 * m ^ 2) p).radius ^ α *
              ((bemocRingFamily (4 * m ^ 2) p).population : ℝ) ^ (1 - α)) /
          squareWithinRingScale α m)
      atTop (𝓝 0)) :
    Tendsto
      (fun m : ℕ =>
        bemocWithinRingDeficit α (4 * m ^ 2) /
          squareWithinRingScale α m)
      atTop
      (𝓝 ((2 * withinRingAsymptoticWeight α) *
        (-2 * (2 * Real.pi) ^ α * realRiemannZeta (-α)))) := by
  classical
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_normalizedCircleSelfDeficit_bound hα0 hα2
  let weight : ∀ m, BemocRingIndex (4 * m ^ 2) → ℝ := fun m p =>
    (bemocRingFamily (4 * m ^ 2) p).radius ^ α *
      ((bemocRingFamily (4 * m ^ 2) p).population : ℝ) ^ (1 - α)
  let population : ∀ m, BemocRingIndex (4 * m ^ 2) → ℕ := fun m p =>
    (bemocRingFamily (4 * m ^ 2) p).population
  have hweight : ∀ m p, 0 ≤ weight m p := by
    intro m p
    exact mul_nonneg (Real.rpow_nonneg (bemocRingFamily _ p).radius_nonneg α)
      (Real.rpow_nonneg (by positivity) (1 - α))
  have htotal : Tendsto
      (fun m => (∑ p, weight m p) / squareWithinRingScale α m)
      atTop (𝓝 (2 * withinRingAsymptoticWeight α)) := by
    simpa [weight, bemocWeightedRadiusPopulationSum] using hgeometry
  have hsmall' : ∀ W : ℕ, Tendsto
      (fun m => (∑ p with population m p < W, weight m p) /
        squareWithinRingScale α m) atTop (𝓝 0) := by
    simpa [weight, population] using hsmall
  have ht := tendsto_triangularArray_weighted_error
    weight population (normalizedCircleSelfDeficit α)
    (squareWithinRingScale α)
    (-2 * (2 * Real.pi) ^ α * realRiemannZeta (-α))
    (2 * withinRingAsymptoticWeight α) B
    hweight (squareWithinRingScale_pos hα2)
    (tendsto_normalizedCircleSelfDeficit' hα0 hα2) hbound htotal hsmall'
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 3] with m hm
  have hM : 3 ≤ bandCount (4 * m ^ 2) := by simpa using hm
  rw [bemocWithinRingDeficit_eq_weighted_normalizedCircle hα0 hM]

theorem tendsto_bemocWithinRingDeficit_four_mul_sq_of_geometry_of_small'
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hgeometry : Tendsto
      (fun m : ℕ =>
        bemocWeightedRadiusPopulationSum α (4 * m ^ 2) /
          squareWithinRingScale α m)
      atTop (𝓝 (2 * withinRingAsymptoticWeight α)))
    (hsmall : ∀ W : ℕ, Tendsto
      (fun m : ℕ =>
        (∑ p : BemocRingIndex (4 * m ^ 2) with
          (bemocRingFamily (4 * m ^ 2) p).population < W,
            (bemocRingFamily (4 * m ^ 2) p).radius ^ α *
              ((bemocRingFamily (4 * m ^ 2) p).population : ℝ) ^ (1 - α)) /
          squareWithinRingScale α m)
      atTop (𝓝 0)) :
    Tendsto
      (fun m : ℕ =>
        bemocWithinRingDeficit α (4 * m ^ 2) /
          (((4 * m ^ 2 : ℕ) : ℝ) ^ (1 - α / 2)))
      atTop (𝓝 (withinRingLimitCoefficient α)) := by
  have hm := tendsto_bemocWithinRingDeficit_four_mul_sq_of_geometry_of_small
    hα0 hα2 hgeometry hsmall
  have htwo : (2 : ℝ) ^ (2 - α) ≠ 0 := by positivity
  have hdiv := hm.div_const ((2 : ℝ) ^ (2 - α))
  have hlimit :
      ((2 * withinRingAsymptoticWeight α) *
          (-2 * (2 * Real.pi) ^ α * realRiemannZeta (-α))) /
          2 ^ (2 - α) = withinRingLimitCoefficient α := by
    rw [mul_comm]
    exact circle_times_geometry_coefficient_eq α
  rw [hlimit] at hdiv
  apply hdiv.congr'
  filter_upwards [eventually_ge_atTop 1,
    eventually_squareWithinRingScale_eq α] with m hmpos hscale
  rw [hscale, square_rpow_normalization (by omega : 0 < m)]
  ring

/-- The sharp geometric weighted-sum limit, expressed with the safe scale
used by the triangular-array transfer theorem. -/
theorem tendsto_bemocWeightedRadiusPopulationSum_four_mul_sq_squareScale
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Tendsto
      (fun m : ℕ =>
        bemocWeightedRadiusPopulationSum α (4 * m ^ 2) /
          squareWithinRingScale α m)
      atTop (𝓝 (2 * withinRingAsymptoticWeight α)) := by
  apply (tendsto_bemocWeightedRadiusPopulationSum_four_mul_sq hα0 hα2).congr'
  filter_upwards [eventually_squareWithinRingScale_eq α] with m hscale
  rw [hscale]

/-- Sharp corrected within-ring asymptotic along the square subsequence
`N = 4m²`.  The coefficient retains the distinct midpoint and shared-boundary
population factors `8/3` and `4/3`. -/
theorem tendsto_bemocWithinRingDeficit_four_mul_sq
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Tendsto
      (fun m : ℕ =>
        bemocWithinRingDeficit α (4 * m ^ 2) /
          (((4 * m ^ 2 : ℕ) : ℝ) ^ (1 - α / 2)))
      atTop (𝓝 (withinRingLimitCoefficient α)) := by
  apply tendsto_bemocWithinRingDeficit_four_mul_sq_of_geometry_of_small'
    hα0 hα2
  · exact tendsto_bemocWeightedRadiusPopulationSum_four_mul_sq_squareScale
      hα0 hα2
  · intro W
    exact tendsto_bemocLowPopulationMass_div_squareScale hα0 W

end BEMOC
