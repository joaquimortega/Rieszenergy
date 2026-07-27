import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped BigOperators Topology Interval
open Filter Set MeasureTheory

/-- Left-endpoint Riemann sums on the uniform subdivision of `[0,1]`
converge to the interval integral. -/
theorem tendsto_leftEndpointRiemannSum_atTop_integral
    {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto
      (fun n : ℕ ↦
        (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, f ((k : ℝ) / (n : ℝ)))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  have huc : UniformContinuousOn f (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := huc (ε / 2) (half_pos hε)
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ < δ :=
    (hinv.eventually (gt_mem_nhds hδ)).mono (fun _ h ↦ h)
  rw [eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  refine ⟨max N 1, fun n hnlarge ↦ ?_⟩
  have hnmesh : (n : ℝ)⁻¹ < δ := hN n (le_trans (le_max_left _ _) hnlarge)
  have hnpos : 1 ≤ n := le_trans (le_max_right _ _) hnlarge
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnpos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  let a : ℕ → ℝ := fun k ↦ (k : ℝ) / (n : ℝ)
  have hstep (k : ℕ) : a (k + 1) - a k = (n : ℝ)⁻¹ := by
    dsimp [a]
    field_simp
  have hsumInt :
      (∑ k ∈ Finset.range n, ∫ x in a k..a (k + 1), f x) =
        ∫ x in (0 : ℝ)..1, f x := by
    convert intervalIntegral.sum_integral_adjacent_intervals
      (a := a) (f := f) (μ := volume)
      (fun _ _ ↦ hf.intervalIntegrable _ _) using 1
    all_goals simp [a, hn0]
  have herror :
      (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, f (a k) -
          (∫ x in (0 : ℝ)..1, f x) =
        ∑ k ∈ Finset.range n,
          ∫ x in a k..a (k + 1), (f (a k) - f x) := by
    rw [← hsumInt, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_sub
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ f (a k)) volume _ _)
      (hf.intervalIntegrable _ _), intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    rw [hstep]
    simp only [one_div]
  have hcell (k : ℕ) (hk : k ∈ Finset.range n) :
      |∫ x in a k..a (k + 1), (f (a k) - f x)| ≤
        (ε / 2) * (n : ℝ)⁻¹ := by
    have hklt : k < n := Finset.mem_range.mp hk
    have hk1 : k + 1 ≤ n := Nat.succ_le_iff.mpr hklt
    have ha0 : 0 ≤ a k := by
      dsimp [a]
      positivity
    have hb1 : a (k + 1) ≤ 1 := by
      dsimp [a]
      rw [div_le_one hnR]
      exact_mod_cast hk1
    have hab : a k ≤ a (k + 1) := by
      dsimp [a]
      gcongr
      exact Nat.le_succ k
    calc
      |∫ x in a k..a (k + 1), (f (a k) - f x)| ≤
          (ε / 2) * |a (k + 1) - a k| := by
        have hi := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := a k) (b := a (k + 1)) (C := ε / 2)
          (f := fun x : ℝ ↦ f (a k) - f x) (fun x hx ↦ by
            rw [uIoc_of_le hab] at hx
            have hak : a k ∈ Icc (0 : ℝ) 1 :=
              ⟨ha0, hab.trans hb1⟩
            have hx01 : x ∈ Icc (0 : ℝ) 1 :=
              ⟨ha0.trans hx.1.le, hx.2.trans hb1⟩
            have hdist : dist (a k) x < δ := by
              have hax : |a k - x| ≤ (n : ℝ)⁻¹ := by
                rw [abs_of_nonpos (sub_nonpos.mpr hx.1.le)]
                rw [neg_sub, ← hstep]
                linarith [hx.2]
              rw [Real.dist_eq]
              exact hax.trans_lt hnmesh
            simpa [Real.dist_eq] using (hmod (a k) hak x hx01 hdist).le)
        simpa only [Real.norm_eq_abs] using hi
      _ = (ε / 2) * (n : ℝ)⁻¹ := by
        rw [hstep, abs_of_pos (inv_pos.mpr hnR)]
  change dist
    ((1 / (n : ℝ)) * ∑ k ∈ Finset.range n, f (a k))
    (∫ x in (0 : ℝ)..1, f x) < ε
  rw [Real.dist_eq, herror]
  calc
    |∑ k ∈ Finset.range n,
        ∫ x in a k..a (k + 1), (f (a k) - f x)| ≤
        ∑ k ∈ Finset.range n,
          |∫ x in a k..a (k + 1), (f (a k) - f x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, (ε / 2) * (n : ℝ)⁻¹ :=
      Finset.sum_le_sum hcell
    _ = ε / 2 := by
      simp only [Finset.sum_const_zero, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, Nat.cast_ofNat]
      field_simp
      ring
    _ < ε := half_lt_self hε
