import BEMOCFormalization.CuspFourier

/-!
# Smoothing domination for the angular cusp

We first prove the only positivity fact needed from the modified-Bessel
kernel: every Fourier coefficient of `exp (t cos θ)` is nonnegative for
`t ≥ 0`.  The proof uses finite exponential polynomials and orthogonality,
so no general Bessel-function library is introduced.
-/

open scoped BigOperators Topology Real
open Filter Set Complex MeasureTheory

namespace BEMOC

namespace CuspSmoothing

theorem fourierCoeff_fourier
    (m n : ℤ) :
    fourierCoeff (@fourier (1 : ℝ) m) n =
      if m = n then 1 else 0 := by
  unfold fourierCoeff
  simp only [smul_eq_mul]
  simp_rw [← fourier_add]
  by_cases hmn : m = n
  · rw [if_pos hmn, hmn, neg_add_cancel]
    have hone : (fun x : AddCircle (1 : ℝ) ↦ @fourier (1 : ℝ) 0 x) =
        fun _ ↦ (1 : ℂ) := by
      funext x
      exact fourier_zero
    rw [hone, integral_const, measureReal_univ_eq_one]
    simp
  · rw [if_neg hmn]
    have hfreq : -n + m ≠ 0 := by omega
    convert integral_eq_zero_of_add_right_eq_neg
      (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hfreq (by norm_num : (0 : ℝ) < 1))

theorem fourierCoeff_finset_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → C(AddCircle (1 : ℝ), ℂ)) (n : ℤ) :
    fourierCoeff (∑ i ∈ s, f i) n =
      ∑ i ∈ s, fourierCoeff (f i) n := by
  induction s using Finset.induction_on with
  | empty => simp [fourierCoeff]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      unfold fourierCoeff at ih ⊢
      simp only [Pi.add_apply, smul_eq_mul, mul_add]
      simp only [smul_eq_mul] at ih
      rw [integral_add, ih]
      · apply Continuous.integrable_of_hasCompactSupport
          ((fourier (-n)).continuous.mul (f i).continuous)
        exact HasCompactSupport.of_compactSpace _
      · have hc : Continuous (fun t : AddCircle (1 : ℝ) ↦
            ∑ j ∈ s, (f j) t) :=
          continuous_finset_sum s fun j _ ↦ (f j).continuous
        have hint : Integrable (fun t : AddCircle (1 : ℝ) ↦
            fourier (-n) t * ∑ j ∈ s, (f j) t)
            AddCircle.haarAddCircle :=
          Continuous.integrable_of_hasCompactSupport
            ((fourier (-n)).continuous.mul hc)
            (HasCompactSupport.of_compactSpace _)
        simpa only [Finset.sum_apply] using hint

noncomputable def expSeriesCoeff (t : ℝ) (k : ℕ) : ℝ :=
  (t / 2) ^ k / (Nat.factorial k : ℝ)

theorem expSeriesCoeff_nonneg {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    0 ≤ expSeriesCoeff t k := by
  unfold expSeriesCoeff
  positivity

theorem fourier_natCast_eq_pow (k : ℕ) (x : AddCircle (1 : ℝ)) :
    @fourier (1 : ℝ) (k : ℤ) x = fourier 1 x ^ k := by
  induction k with
  | zero => simp only [Nat.cast_zero, fourier_zero, pow_zero]
  | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by omega,
        fourier_add, ih, pow_succ]

theorem fourier_neg_natCast_eq_pow (k : ℕ) (x : AddCircle (1 : ℝ)) :
    @fourier (1 : ℝ) (-(k : ℤ)) x = fourier (-1) x ^ k := by
  induction k with
  | zero => simp only [Nat.cast_zero, neg_zero, fourier_zero, pow_zero]
  | succ k ih =>
      rw [show (-((k + 1 : ℕ) : ℤ)) = -(k : ℤ) + -1 by push_cast; ring,
        fourier_add, ih, pow_succ]

noncomputable def analyticExpPartial (t : ℝ) (N : ℕ) :
    C(AddCircle (1 : ℝ), ℂ) :=
  ∑ k ∈ Finset.range N,
    (expSeriesCoeff t k : ℂ) • @fourier (1 : ℝ) (k : ℤ)

noncomputable def coanalyticExpPartial (t : ℝ) (N : ℕ) :
    C(AddCircle (1 : ℝ), ℂ) :=
  ∑ k ∈ Finset.range N,
    (expSeriesCoeff t k : ℂ) • @fourier (1 : ℝ) (-(k : ℤ))

theorem analyticExpPartial_apply (t : ℝ) (N : ℕ)
    (x : AddCircle (1 : ℝ)) :
    analyticExpPartial t N x =
      ∑ k ∈ Finset.range N,
        (((t / 2 : ℝ) : ℂ) * fourier 1 x) ^ k /
          (Nat.factorial k : ℂ) := by
  unfold analyticExpPartial expSeriesCoeff
  rw [ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  change (expSeriesCoeff t k : ℂ) * fourier (k : ℤ) x = _
  unfold expSeriesCoeff
  rw [fourier_natCast_eq_pow]
  push_cast
  rw [mul_pow]
  ring

theorem coanalyticExpPartial_apply (t : ℝ) (N : ℕ)
    (x : AddCircle (1 : ℝ)) :
    coanalyticExpPartial t N x =
      ∑ k ∈ Finset.range N,
        (((t / 2 : ℝ) : ℂ) * fourier (-1) x) ^ k /
          (Nat.factorial k : ℂ) := by
  unfold coanalyticExpPartial expSeriesCoeff
  rw [ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  change (expSeriesCoeff t k : ℂ) * fourier (-(k : ℤ)) x = _
  unfold expSeriesCoeff
  rw [fourier_neg_natCast_eq_pow]
  push_cast
  rw [mul_pow]
  ring

theorem tendsto_analyticExpPartial (t : ℝ) (x : AddCircle (1 : ℝ)) :
    Tendsto (fun N ↦ analyticExpPartial t N x) atTop
      (𝓝 (Complex.exp (((t / 2 : ℝ) : ℂ) * fourier 1 x))) := by
  simpa only [analyticExpPartial_apply, Complex.exp_eq_exp_ℂ] using
    (NormedSpace.expSeries_div_hasSum_exp ℂ
      (((t / 2 : ℝ) : ℂ) * fourier 1 x)).tendsto_sum_nat

theorem tendsto_coanalyticExpPartial (t : ℝ) (x : AddCircle (1 : ℝ)) :
    Tendsto (fun N ↦ coanalyticExpPartial t N x) atTop
      (𝓝 (Complex.exp (((t / 2 : ℝ) : ℂ) * fourier (-1) x))) := by
  simpa only [coanalyticExpPartial_apply, Complex.exp_eq_exp_ℂ] using
    (NormedSpace.expSeries_div_hasSum_exp ℂ
      (((t / 2 : ℝ) : ℂ) * fourier (-1) x)).tendsto_sum_nat

theorem norm_analyticExpPartial_le {t : ℝ} (ht : 0 ≤ t)
    (N : ℕ) (x : AddCircle (1 : ℝ)) :
    ‖analyticExpPartial t N x‖ ≤ Real.exp (t / 2) := by
  rw [analyticExpPartial_apply]
  calc
    ‖∑ k ∈ Finset.range N,
        ((((t / 2 : ℝ) : ℂ) * fourier 1 x) ^ k /
          (Nat.factorial k : ℂ))‖ ≤
        ∑ k ∈ Finset.range N,
          expSeriesCoeff t k := by
      calc
        _ ≤ ∑ k ∈ Finset.range N,
            ‖((((t / 2 : ℝ) : ℂ) * fourier 1 x) ^ k /
              (Nat.factorial k : ℂ))‖ :=
          norm_sum_le _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [norm_div, norm_pow, norm_mul, norm_real,
            show ‖fourier 1 x‖ = 1 by exact Circle.norm_coe _, norm_natCast]
          unfold expSeriesCoeff
          rw [Real.norm_of_nonneg (by positivity : 0 ≤ t / 2)]
          simp only [mul_one]
    _ ≤ Real.exp (t / 2) := by
      have hs : HasSum (expSeriesCoeff t) (Real.exp (t / 2)) := by
        simpa [expSeriesCoeff, Real.exp_eq_exp_ℝ] using
          (NormedSpace.expSeries_div_hasSum_exp ℝ (t / 2))
      exact sum_le_hasSum (Finset.range N)
        (fun k hk ↦ expSeriesCoeff_nonneg ht k) hs

theorem norm_coanalyticExpPartial_le {t : ℝ} (ht : 0 ≤ t)
    (N : ℕ) (x : AddCircle (1 : ℝ)) :
    ‖coanalyticExpPartial t N x‖ ≤ Real.exp (t / 2) := by
  rw [coanalyticExpPartial_apply]
  calc
    ‖∑ k ∈ Finset.range N,
        ((((t / 2 : ℝ) : ℂ) * fourier (-1) x) ^ k /
          (Nat.factorial k : ℂ))‖ ≤
        ∑ k ∈ Finset.range N,
          expSeriesCoeff t k := by
      calc
        _ ≤ ∑ k ∈ Finset.range N,
            ‖((((t / 2 : ℝ) : ℂ) * fourier (-1) x) ^ k /
              (Nat.factorial k : ℂ))‖ :=
          norm_sum_le _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [norm_div, norm_pow, norm_mul, norm_real,
            show ‖fourier (-1) x‖ = 1 by exact Circle.norm_coe _, norm_natCast]
          unfold expSeriesCoeff
          rw [Real.norm_of_nonneg (by positivity : 0 ≤ t / 2)]
          simp only [mul_one]
    _ ≤ Real.exp (t / 2) := by
      have hs : HasSum (expSeriesCoeff t) (Real.exp (t / 2)) := by
        simpa [expSeriesCoeff, Real.exp_eq_exp_ℝ] using
          (NormedSpace.expSeries_div_hasSum_exp ℝ (t / 2))
      exact sum_le_hasSum (Finset.range N)
        (fun k hk ↦ expSeriesCoeff_nonneg ht k) hs

noncomputable def expCosPartial (t : ℝ) (N : ℕ) :
    C(AddCircle (1 : ℝ), ℂ) :=
  analyticExpPartial t N * coanalyticExpPartial t N

noncomputable def expCosCircle (t : ℝ) :
    C(AddCircle (1 : ℝ), ℂ) where
  toFun x := (Real.exp (t * (fourier 1 x).re) : ℂ)
  continuous_toFun := by
    exact Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp
        (continuous_const.mul
          (Complex.continuous_re.comp (fourier 1).continuous)))

theorem expCosPartial_eq_double_sum (t : ℝ) (N : ℕ) :
    expCosPartial t N =
      ∑ l ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ((expSeriesCoeff t k * expSeriesCoeff t l : ℝ) : ℂ) •
          @fourier (1 : ℝ) ((k : ℤ) - (l : ℤ)) := by
  ext x
  unfold expCosPartial analyticExpPartial coanalyticExpPartial
  simp only [ContinuousMap.mul_apply, ContinuousMap.sum_apply,
    ContinuousMap.coe_smul', smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro k hk
  change (expSeriesCoeff t k : ℂ) * fourier (k : ℤ) x *
      ((expSeriesCoeff t l : ℂ) * fourier (-(l : ℤ)) x) =
    (expSeriesCoeff t k * expSeriesCoeff t l : ℝ) *
      fourier ((k : ℤ) + -(l : ℤ)) x
  rw [fourier_add]
  push_cast
  ring

theorem fourierCoeff_expCosPartial_eq (t : ℝ) (N : ℕ) (n : ℤ) :
    fourierCoeff (expCosPartial t N) n =
      ((∑ l ∈ Finset.range N, ∑ k ∈ Finset.range N,
        if (k : ℤ) - (l : ℤ) = n then
          expSeriesCoeff t k * expSeriesCoeff t l else 0 : ℝ) : ℂ) := by
  rw [expCosPartial_eq_double_sum]
  let F : ℕ → C(AddCircle (1 : ℝ), ℂ) := fun l ↦
    ∑ k ∈ Finset.range N,
      ((expSeriesCoeff t k * expSeriesCoeff t l : ℝ) : ℂ) •
        @fourier (1 : ℝ) ((k : ℤ) - (l : ℤ))
  change fourierCoeff (⇑(∑ l ∈ Finset.range N, F l)) n = _
  rw [ContinuousMap.coe_sum]
  calc
    _ = ∑ l ∈ Finset.range N, fourierCoeff (F l) n :=
      fourierCoeff_finset_sum (Finset.range N) F n
    _ = _ := by
      push_cast
      apply Finset.sum_congr rfl
      intro l hl
      dsimp [F]
      rw [ContinuousMap.coe_sum]
      rw [fourierCoeff_finset_sum]
      apply Finset.sum_congr rfl
      intro k hk
      change fourierCoeff (fun x : AddCircle (1 : ℝ) ↦
        (expSeriesCoeff t k * expSeriesCoeff t l : ℝ) *
          fourier ((k : ℤ) - (l : ℤ)) x) n = _
      rw [fourierCoeff.const_mul, fourierCoeff_fourier]
      split_ifs <;> simp

theorem fourierCoeff_expCosPartial_re_nonneg
    {t : ℝ} (ht : 0 ≤ t) (N : ℕ) (n : ℤ) :
    0 ≤ (fourierCoeff (expCosPartial t N) n).re := by
  rw [fourierCoeff_expCosPartial_eq]
  simp only [ofReal_re]
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro l hl
  split_ifs
  · exact mul_nonneg (expSeriesCoeff_nonneg ht l)
      (expSeriesCoeff_nonneg ht k)
  · exact le_rfl

theorem expCosPartial_tendsto
    (t : ℝ) (x : AddCircle (1 : ℝ)) :
    Tendsto (fun N ↦ expCosPartial t N x) atTop
      (𝓝 (expCosCircle t x)) := by
  have htend := (tendsto_analyticExpPartial t x).mul
    (tendsto_coanalyticExpPartial t x)
  have hlimit :
      expCosCircle t x =
        Complex.exp (((t / 2 : ℝ) : ℂ) * fourier 1 x) *
          Complex.exp (((t / 2 : ℝ) : ℂ) * fourier (-1) x) := by
    change (Real.exp (t * (fourier 1 x).re) : ℂ) = _
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    have hneg : fourier (-1) x = starRingEnd ℂ (fourier 1 x) := by
      simpa using (@fourier_neg (1 : ℝ) 1 x)
    rw [hneg]
    apply Complex.ext <;> simp ; ring
  unfold expCosPartial
  rw [hlimit]
  exact htend

theorem norm_expCosPartial_le
    {t : ℝ} (ht : 0 ≤ t) (N : ℕ) (x : AddCircle (1 : ℝ)) :
    ‖expCosPartial t N x‖ ≤ Real.exp t := by
  unfold expCosPartial
  rw [ContinuousMap.mul_apply, norm_mul]
  calc
    ‖analyticExpPartial t N x‖ * ‖coanalyticExpPartial t N x‖ ≤
        Real.exp (t / 2) * Real.exp (t / 2) :=
      mul_le_mul (norm_analyticExpPartial_le ht N x)
        (norm_coanalyticExpPartial_le ht N x) (norm_nonneg _)
        (Real.exp_pos _).le
    _ = Real.exp t := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem tendsto_fourierCoeff_expCosPartial
    {t : ℝ} (ht : 0 ≤ t) (n : ℤ) :
    Tendsto (fun N ↦ fourierCoeff (expCosPartial t N) n) atTop
      (𝓝 (fourierCoeff (expCosCircle t) n)) := by
  unfold fourierCoeff
  apply MeasureTheory.tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun N ↦
      ((fourier (-n)).continuous.mul
        (expCosPartial t N).continuous).aestronglyMeasurable
  · refine ⟨Real.exp t, Filter.Eventually.of_forall fun N ↦ ?_⟩
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [smul_eq_mul, norm_mul,
        show ‖fourier (-n) x‖ = 1 by exact Circle.norm_coe _, one_mul]
      exact norm_expCosPartial_le ht N x
  · exact Filter.Eventually.of_forall fun x ↦ by
      simpa only [smul_eq_mul] using
        (tendsto_const_nhds.mul (expCosPartial_tendsto t x))

/-- Positivity of every Fourier coefficient of `exp (t cos θ)`. -/
theorem fourierCoeff_expCosCircle_re_nonneg
    {t : ℝ} (ht : 0 ≤ t) (n : ℤ) :
    0 ≤ (fourierCoeff (expCosCircle t) n).re := by
  have htend := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_fourierCoeff_expCosPartial ht n)
  apply ge_of_tendsto htend
  exact Filter.Eventually.of_forall fun N ↦
    fourierCoeff_expCosPartial_re_nonneg ht N n

/-! ## Bernstein mixture and smoothing domination -/

noncomputable def circleCos (n : ℤ) (x : AddCircle (1 : ℝ)) : ℝ :=
  (fourier n x).re

theorem abs_circleCos_le_one (n : ℤ) (x : AddCircle (1 : ℝ)) :
    |circleCos n x| ≤ 1 := by
  unfold circleCos
  exact (Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe _)

noncomputable def smoothedCuspBase
    (δ : ℝ) (x : AddCircle (1 : ℝ)) : ℝ :=
  δ + 1 - circleCos 1 x

theorem smoothedCuspBase_nonneg
    {δ : ℝ} (hδ : 0 ≤ δ) (x : AddCircle (1 : ℝ)) :
    0 ≤ smoothedCuspBase δ x := by
  have hcos := (abs_le.mp (abs_circleCos_le_one 1 x)).2
  unfold smoothedCuspBase
  linarith

theorem smoothedCuspBase_le
    {δ : ℝ} (x : AddCircle (1 : ℝ)) :
    smoothedCuspBase δ x ≤ δ + 2 := by
  have hcos := (abs_le.mp (abs_circleCos_le_one 1 x)).1
  unfold smoothedCuspBase
  linarith

theorem continuous_smoothedCuspBase (δ : ℝ) :
    Continuous (smoothedCuspBase δ) := by
  unfold smoothedCuspBase circleCos
  exact (continuous_const.add continuous_const).sub
    (Complex.continuous_re.comp (fourier 1).continuous)

theorem continuous_circleCos (n : ℤ) :
    Continuous (circleCos n) := by
  unfold circleCos
  exact Complex.continuous_re.comp (fourier n).continuous

noncomputable def smoothedCuspCosCoeff
    (p δ : ℝ) (n : ℤ) : ℝ :=
  ∫ x : AddCircle (1 : ℝ),
    circleCos n x * smoothedCuspBase δ x ^ p
      ∂AddCircle.haarAddCircle

theorem fourierCoeff_ofReal_re
    (f : C(AddCircle (1 : ℝ), ℝ)) (n : ℤ) :
    (fourierCoeff (fun x ↦ (f x : ℂ)) n).re =
      ∫ x : AddCircle (1 : ℝ), circleCos n x * f x
        ∂AddCircle.haarAddCircle := by
  unfold fourierCoeff
  simp only [smul_eq_mul]
  have hint : Integrable
      (fun x : AddCircle (1 : ℝ) ↦ fourier (-n) x * (f x : ℂ))
      AddCircle.haarAddCircle :=
    Continuous.integrable_of_hasCompactSupport
      ((fourier (-n)).continuous.mul
        (Complex.continuous_ofReal.comp f.continuous))
      (HasCompactSupport.of_compactSpace _)
  change Complex.reCLM
      (∫ x : AddCircle (1 : ℝ), fourier (-n) x * (f x : ℂ)
        ∂AddCircle.haarAddCircle) = _
  rw [← Complex.reCLM.integral_comp_comm hint]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change (fourier (-n) x * (f x : ℂ)).re =
      circleCos n x * f x
    rw [show fourier (-n) x = starRingEnd ℂ (fourier n x) by
      simp]
    unfold circleCos
    simp

theorem fourierCoeff_expCosCircle_re_eq_integral (t : ℝ) (n : ℤ) :
    (fourierCoeff (expCosCircle t) n).re =
      ∫ x : AddCircle (1 : ℝ),
        circleCos n x * Real.exp (t * circleCos 1 x)
          ∂AddCircle.haarAddCircle := by
  let f : C(AddCircle (1 : ℝ), ℝ) :=
    { toFun := fun x ↦ Real.exp (t * circleCos 1 x)
      continuous_toFun := Real.continuous_exp.comp
        (continuous_const.mul (continuous_circleCos 1)) }
  have h := fourierCoeff_ofReal_re f n
  simpa [expCosCircle, f, circleCos] using h

theorem integral_circleCos_eq_zero
    {n : ℤ} (hn : n ≠ 0) :
    (∫ x : AddCircle (1 : ℝ), circleCos n x
      ∂AddCircle.haarAddCircle) = 0 := by
  let one : C(AddCircle (1 : ℝ), ℝ) := 1
  have hreal := fourierCoeff_ofReal_re one n
  have hone :
      (fun x : AddCircle (1 : ℝ) ↦ (one x : ℂ)) =
        (fun x ↦ @fourier (1 : ℝ) 0 x) := by
    funext x
    simp [one, fourier_zero]
  rw [hone] at hreal
  have hfourier := fourierCoeff_fourier 0 n
  rw [if_neg (Ne.symm hn)] at hfourier
  have hzero := congrArg Complex.re hfourier
  norm_num at hzero
  simpa [one, circleCos] using hreal.symm.trans hzero

noncomputable def smoothedCuspCircle
    (p δ : ℝ) (hp : 0 < p) (_hδ : 0 ≤ δ) :
    C(AddCircle (1 : ℝ), ℂ) where
  toFun x := (smoothedCuspBase δ x ^ p : ℝ)
  continuous_toFun := by
    exact Complex.continuous_ofReal.comp
      ((continuous_smoothedCuspBase δ).rpow_const
        (fun _ ↦ Or.inr hp.le))

theorem fourierCoeff_smoothedCuspCircle_re
    {p δ : ℝ} (hp : 0 < p) (hδ : 0 ≤ δ) (n : ℤ) :
    (fourierCoeff (smoothedCuspCircle p δ hp hδ) n).re =
      smoothedCuspCosCoeff p δ n := by
  let f : C(AddCircle (1 : ℝ), ℝ) :=
    { toFun := fun x ↦ smoothedCuspBase δ x ^ p
      continuous_toFun :=
        (continuous_smoothedCuspBase δ).rpow_const
          (fun _ ↦ Or.inr hp.le) }
  simpa [smoothedCuspCircle, smoothedCuspCosCoeff, f] using
    (fourierCoeff_ofReal_re f n)

theorem circleCos_neg (n : ℤ) (x : AddCircle (1 : ℝ)) :
    circleCos n (-x) = circleCos n x := by
  unfold circleCos
  rw [show fourier n (-x) = starRingEnd ℂ (fourier n x) by
    calc
      fourier n (-x) = fourier (-n) x := by
        rw [fourier_apply, fourier_apply]
        congr 1
        simp
      _ = starRingEnd ℂ (fourier n x) := fourier_neg]
  simp

theorem smoothedCuspBase_neg (δ : ℝ) (x : AddCircle (1 : ℝ)) :
    smoothedCuspBase δ (-x) = smoothedCuspBase δ x := by
  unfold smoothedCuspBase
  rw [circleCos_neg]

theorem fourierCoeff_smoothedCuspCircle_im_eq_zero
    {p δ : ℝ} (hp : 0 < p) (hδ : 0 ≤ δ) (n : ℤ) :
    (fourierCoeff (smoothedCuspCircle p δ hp hδ) n).im = 0 := by
  let f := smoothedCuspCircle p δ hp hδ
  let g : AddCircle (1 : ℝ) → ℂ := fun x ↦ fourier (-n) x * f x
  have hg : Integrable g AddCircle.haarAddCircle :=
    Continuous.integrable_of_hasCompactSupport
      ((fourier (-n)).continuous.mul f.continuous)
      (HasCompactSupport.of_compactSpace _)
  have him :
      (fourierCoeff f n).im =
        ∫ x : AddCircle (1 : ℝ), (g x).im
          ∂AddCircle.haarAddCircle := by
    unfold fourierCoeff
    change Complex.imCLM
        (∫ x : AddCircle (1 : ℝ), g x
          ∂AddCircle.haarAddCircle) = _
    exact Complex.imCLM.integral_comp_comm hg |>.symm
  have hodd (x : AddCircle (1 : ℝ)) :
      (g (-x)).im = -(g x).im := by
    have hfourier :
        fourier (-n) (-x) = starRingEnd ℂ (fourier (-n) x) := by
      calc
        fourier (-n) (-x) = fourier (-(-n)) x := by
          rw [fourier_apply, fourier_apply]
          congr 1
          simp
        _ = starRingEnd ℂ (fourier (-n) x) := fourier_neg
    have hfreal (y : AddCircle (1 : ℝ)) :
        f y = ((smoothedCuspBase δ y ^ p : ℝ) : ℂ) := rfl
    dsimp only [g]
    rw [hfourier, hfreal, hfreal, smoothedCuspBase_neg]
    simp
  have hinv := integral_neg_eq_self
    (fun x : AddCircle (1 : ℝ) ↦ (g x).im)
    AddCircle.haarAddCircle
  have heq :
      (∫ x : AddCircle (1 : ℝ), (g x).im
          ∂AddCircle.haarAddCircle) =
        -(∫ x : AddCircle (1 : ℝ), (g x).im
          ∂AddCircle.haarAddCircle) := by
    calc
      _ = ∫ x : AddCircle (1 : ℝ), (g (-x)).im
          ∂AddCircle.haarAddCircle := hinv.symm
      _ = ∫ x : AddCircle (1 : ℝ), -(g x).im
          ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hodd
      _ = _ := integral_neg _
  rw [him]
  linarith

theorem fourierCoeff_smoothedCuspCircle_eq_cosCoeff
    {p δ : ℝ} (hp : 0 < p) (hδ : 0 ≤ δ) (n : ℤ) :
    fourierCoeff (smoothedCuspCircle p δ hp hδ) n =
      (smoothedCuspCosCoeff p δ n : ℂ) := by
  apply Complex.ext
  · exact fourierCoeff_smoothedCuspCircle_re hp hδ n
  · simpa using fourierCoeff_smoothedCuspCircle_im_eq_zero hp hδ n

theorem smoothedCuspBase_zero_eq_norm_sq_div_two
    (x : AddCircle (1 : ℝ)) :
    smoothedCuspBase 0 x =
      ‖((AddCircle.toCircle x : Circle) : ℂ) - 1‖ ^ 2 / 2 := by
  let z : ℂ := ((AddCircle.toCircle x : Circle) : ℂ)
  have hznorm : ‖z‖ = 1 := Circle.norm_coe _
  have hzsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    calc
      z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖z‖ ^ 2 := Complex.sq_norm z |>.symm
      _ = 1 := by rw [hznorm]; norm_num
  have hsq : ‖z - 1‖ ^ 2 = 2 * (1 - z.re) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero]
    nlinarith
  unfold smoothedCuspBase circleCos
  rw [fourier_one]
  change 0 + 1 - z.re = ‖z - 1‖ ^ 2 / 2
  rw [hsq]
  ring

theorem smoothedCuspBase_zero_rpow_eq_chord
    {p : ℝ} (_hp : 0 < p) (x : AddCircle (1 : ℝ)) :
    smoothedCuspBase 0 x ^ p =
      (2 : ℝ) ^ (-p) *
        ‖((AddCircle.toCircle x : Circle) : ℂ) - 1‖ ^ (2 * p) := by
  let r : ℝ := ‖((AddCircle.toCircle x : Circle) : ℂ) - 1‖
  rw [smoothedCuspBase_zero_eq_norm_sq_div_two]
  change (r ^ 2 / 2) ^ p = (2 : ℝ) ^ (-p) * r ^ (2 * p)
  rw [Real.div_rpow (sq_nonneg r) (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.rpow_natCast_mul (norm_nonneg _) 2 p]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  dsimp [r]
  rw [div_eq_mul_inv]
  ring

theorem smoothedCuspCircle_zero_eq_chord_smul
    {p : ℝ} (hp : 0 < p) :
    smoothedCuspCircle p 0 hp (le_refl 0) =
      (↑((2 : ℝ) ^ (-p)) : ℂ) •
        CircleFourier.chordProfileCircle (2 * p) (by positivity) := by
  ext x
  change ((smoothedCuspBase 0 x ^ p : ℝ) : ℂ) =
    (↑((2 : ℝ) ^ (-p)) : ℂ) *
      (↑((‖((AddCircle.toCircle x : Circle) : ℂ) - 1‖ : ℝ) ^
        (2 * p)) : ℂ)
  rw [smoothedCuspBase_zero_rpow_eq_chord hp]
  push_cast
  rfl

theorem smoothedCuspCosCoeff_zero_eq_chord
    {p : ℝ} (hp : 0 < p) (n : ℤ) :
    smoothedCuspCosCoeff p 0 n =
      (2 : ℝ) ^ (-p) *
        (fourierCoeff
          (CircleFourier.chordProfileCircle (2 * p) (by positivity)) n).re := by
  have hcoeff := congrArg (fun f : C(AddCircle (1 : ℝ), ℂ) ↦
      fourierCoeff f n) (smoothedCuspCircle_zero_eq_chord_smul hp)
  change fourierCoeff (smoothedCuspCircle p 0 hp (le_refl 0)) n =
    fourierCoeff
      ((↑((2 : ℝ) ^ (-p)) : ℂ) •
        CircleFourier.chordProfileCircle (2 * p) (by positivity)) n at hcoeff
  rw [fourierCoeff_smoothedCuspCircle_eq_cosCoeff hp (le_refl 0)] at hcoeff
  change (smoothedCuspCosCoeff p 0 n : ℂ) =
    fourierCoeff
      (fun x : AddCircle (1 : ℝ) ↦
        (↑((2 : ℝ) ^ (-p)) : ℂ) *
          CircleFourier.chordProfileCircle (2 * p) (by positivity) x) n at hcoeff
  rw [fourierCoeff.const_mul] at hcoeff
  have hre := congrArg Complex.re hcoeff
  simpa using hre

theorem continuousOn_schoenberg_cusp_joint
    (p δ : ℝ) (n : ℤ) :
    ContinuousOn
      (fun z : ℝ × AddCircle (1 : ℝ) ↦
        circleCos n z.2 *
          schoenbergIntegrand p (smoothedCuspBase δ z.2) z.1)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  unfold schoenbergIntegrand
  have hbase : Continuous
      (fun z : ℝ × AddCircle (1 : ℝ) ↦
        smoothedCuspBase δ z.2) :=
    (continuous_smoothedCuspBase δ).comp continuous_snd
  have hcos : Continuous
      (fun z : ℝ × AddCircle (1 : ℝ) ↦ circleCos n z.2) :=
    (continuous_circleCos n).comp continuous_snd
  apply ContinuousOn.mul hcos.continuousOn
  apply ContinuousOn.mul
  · exact continuousOn_const.sub
      (Real.continuous_exp.comp_continuousOn
        ((continuous_fst.neg.mul hbase).continuousOn))
  · exact continuousOn_fst.rpow continuousOn_const
      (fun z hz ↦ Or.inl hz.1.ne')

theorem integrable_schoenberg_cusp_joint
    {p δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hδ : 0 ≤ δ) (n : ℤ) :
    Integrable
      (fun z : ℝ × AddCircle (1 : ℝ) ↦
        circleCos n z.2 *
          schoenbergIntegrand p (smoothedCuspBase δ z.2) z.1)
      ((volume.restrict (Set.Ioi 0)).prod AddCircle.haarAddCircle) := by
  have hupper : 0 ≤ δ + 2 := by linarith
  have hdom : Integrable
      (fun z : ℝ × AddCircle (1 : ℝ) ↦
        schoenbergIntegrand p (δ + 2) z.1 * 1)
      ((volume.restrict (Set.Ioi 0)).prod AddCircle.haarAddCircle) :=
    (integrableOn_schoenbergIntegrand hp0 hp1 hupper).mul_prod
      (integrable_const (1 : ℝ))
  apply Integrable.mono' hdom
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact (continuousOn_schoenberg_cusp_joint p δ n).aestronglyMeasurable
      (measurableSet_Ioi.prod MeasurableSet.univ)
  · have hzmem : ∀ᵐ z
        ∂(volume.restrict (Set.Ioi 0)).prod
          (AddCircle.haarAddCircle :
            Measure (AddCircle (1 : ℝ))),
        z ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem
        (measurableSet_Ioi.prod MeasurableSet.univ)]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Filter.Eventually.of_forall fun x ↦ ⟨ht, Set.mem_univ x⟩
    filter_upwards [hzmem] with z hz
    have ht : 0 < z.1 := hz.1
    have hr0 := smoothedCuspBase_nonneg hδ z.2
    have hr1 := smoothedCuspBase_le (δ := δ) z.2
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (schoenbergIntegrand_nonneg hr0 ht)]
    simp only [mul_one, Real.norm_eq_abs]
    calc
      |circleCos n z.2| *
          schoenbergIntegrand p (smoothedCuspBase δ z.2) z.1 ≤
          1 * schoenbergIntegrand p (δ + 2) z.1 := by
        apply mul_le_mul (abs_circleCos_le_one n z.2) _
          (schoenbergIntegrand_nonneg hr0 ht) (by norm_num)
        unfold schoenbergIntegrand
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
        apply sub_le_sub_left
        exact Real.exp_le_exp.mpr (by nlinarith)
      _ = schoenbergIntegrand p (δ + 2) z.1 := one_mul _

theorem integral_schoenberg_cusp_swap
    {p δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hδ : 0 ≤ δ) (n : ℤ) :
    (∫ t : ℝ in Set.Ioi 0,
        ∫ x : AddCircle (1 : ℝ),
          circleCos n x *
            schoenbergIntegrand p (smoothedCuspBase δ x) t
            ∂AddCircle.haarAddCircle) =
      schoenbergIntegral p 1 * smoothedCuspCosCoeff p δ n := by
  have hswap := MeasureTheory.integral_integral_swap
    (μ := volume.restrict (Set.Ioi 0))
    (ν := AddCircle.haarAddCircle)
    (f := fun t x ↦ circleCos n x *
      schoenbergIntegrand p (smoothedCuspBase δ x) t)
    (integrable_schoenberg_cusp_joint hp0 hp1 hδ n)
  calc
    _ = ∫ x : AddCircle (1 : ℝ),
        (∫ t : ℝ in Set.Ioi 0,
          circleCos n x *
            schoenbergIntegrand p (smoothedCuspBase δ x) t)
          ∂AddCircle.haarAddCircle := hswap
    _ = ∫ x : AddCircle (1 : ℝ),
        circleCos n x *
          (smoothedCuspBase δ x ^ p * schoenbergIntegral p 1)
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change (∫ t : ℝ in Set.Ioi 0,
          circleCos n x *
            schoenbergIntegrand p (smoothedCuspBase δ x) t) =
          circleCos n x *
            (smoothedCuspBase δ x ^ p * schoenbergIntegral p 1)
        rw [MeasureTheory.integral_const_mul]
        change circleCos n x *
            schoenbergIntegral p (smoothedCuspBase δ x) =
          circleCos n x *
            (smoothedCuspBase δ x ^ p * schoenbergIntegral p 1)
        rw [schoenbergIntegral_eq_rpow_mul hp0
          (smoothedCuspBase_nonneg hδ x)]
    _ = schoenbergIntegral p 1 * smoothedCuspCosCoeff p δ n := by
      unfold smoothedCuspCosCoeff
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by ring

theorem integral_circleCos_mul_schoenbergIntegrand
    {p δ : ℝ} (_hδ : 0 ≤ δ) {n : ℤ} (hn : n ≠ 0)
    {t : ℝ} (_ht : 0 < t) :
    (∫ x : AddCircle (1 : ℝ),
        circleCos n x *
          schoenbergIntegrand p (smoothedCuspBase δ x) t
          ∂AddCircle.haarAddCircle) =
      -Real.exp (-t * (δ + 1)) *
          (fourierCoeff (expCosCircle t) n).re *
            t ^ (-p - 1) := by
  have hcosint :
      Integrable (circleCos n) AddCircle.haarAddCircle :=
    (continuous_circleCos n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hexpint : Integrable
      (fun x : AddCircle (1 : ℝ) ↦
        circleCos n x * Real.exp (t * circleCos 1 x))
      AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport
      ((continuous_circleCos n).mul
        (Real.continuous_exp.comp
          (continuous_const.mul (continuous_circleCos 1))))
    exact HasCompactSupport.of_compactSpace _
  unfold schoenbergIntegrand
  have hassoc :
      (fun x : AddCircle (1 : ℝ) ↦
        circleCos n x *
          ((1 - Real.exp (-t * smoothedCuspBase δ x)) *
            t ^ (-p - 1))) =
      (fun x : AddCircle (1 : ℝ) ↦
        (circleCos n x *
          (1 - Real.exp (-t * smoothedCuspBase δ x))) *
            t ^ (-p - 1)) := by
    funext x
    ring
  rw [hassoc]
  rw [integral_mul_const]
  have hpoint (x : AddCircle (1 : ℝ)) :
      Real.exp (-t * smoothedCuspBase δ x) =
        Real.exp (-t * (δ + 1)) *
          Real.exp (t * circleCos 1 x) := by
    rw [← Real.exp_add]
    congr 1
    unfold smoothedCuspBase
    ring
  calc
    (∫ x : AddCircle (1 : ℝ),
        circleCos n x *
          (1 - Real.exp (-t * smoothedCuspBase δ x))
          ∂AddCircle.haarAddCircle) * t ^ (-p - 1) =
        ((∫ x : AddCircle (1 : ℝ), circleCos n x
            ∂AddCircle.haarAddCircle) -
          Real.exp (-t * (δ + 1)) *
            ∫ x : AddCircle (1 : ℝ),
              circleCos n x * Real.exp (t * circleCos 1 x)
              ∂AddCircle.haarAddCircle) * t ^ (-p - 1) := by
      congr 1
      rw [← integral_const_mul]
      rw [← integral_sub hcosint
        (hexpint.const_mul (Real.exp (-t * (δ + 1))))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change circleCos n x *
            (1 - Real.exp (-t * smoothedCuspBase δ x)) =
          circleCos n x -
            Real.exp (-t * (δ + 1)) *
              (circleCos n x * Real.exp (t * circleCos 1 x))
        rw [hpoint]
        ring
    _ = _ := by
      rw [integral_circleCos_eq_zero hn,
        ← fourierCoeff_expCosCircle_re_eq_integral]
      ring

noncomputable def cuspMixtureWeight
    (p δ : ℝ) (n : ℤ) (t : ℝ) : ℝ :=
  Real.exp (-t * (δ + 1)) *
    (fourierCoeff (expCosCircle t) n).re *
      t ^ (-p - 1)

theorem cuspMixtureWeight_nonneg
    {p δ t : ℝ} (_hδ : 0 ≤ δ) {n : ℤ} (ht : 0 < t) :
    0 ≤ cuspMixtureWeight p δ n t := by
  unfold cuspMixtureWeight
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le
      (fourierCoeff_expCosCircle_re_nonneg ht.le n))
    (Real.rpow_nonneg ht.le _)

theorem integrableOn_cuspMixtureWeight
    {p δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hδ : 0 ≤ δ) {n : ℤ} (hn : n ≠ 0) :
    IntegrableOn (cuspMixtureWeight p δ n) (Set.Ioi 0) := by
  let inner : ℝ → ℝ := fun t ↦
    ∫ x : AddCircle (1 : ℝ),
      circleCos n x *
        schoenbergIntegrand p (smoothedCuspBase δ x) t
        ∂AddCircle.haarAddCircle
  have hinner : Integrable inner (volume.restrict (Set.Ioi 0)) := by
    exact (integrable_schoenberg_cusp_joint hp0 hp1 hδ n).integral_prod_left
  have heq :
      inner =ᵐ[volume.restrict (Set.Ioi 0)]
        fun t ↦ -cuspMixtureWeight p δ n t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (∫ x : AddCircle (1 : ℝ),
        circleCos n x *
          schoenbergIntegrand p (smoothedCuspBase δ x) t
          ∂AddCircle.haarAddCircle) =
      -cuspMixtureWeight p δ n t
    rw [integral_circleCos_mul_schoenbergIntegrand hδ hn ht]
    unfold cuspMixtureWeight
    ring
  have hneg : Integrable (fun t ↦ -cuspMixtureWeight p δ n t)
      (volume.restrict (Set.Ioi 0)) :=
    hinner.congr heq
  exact hneg.neg.congr <| Filter.Eventually.of_forall fun t ↦ by
    simp only [Pi.neg_apply, neg_neg]

theorem schoenbergIntegral_mul_smoothedCuspCosCoeff
    {p δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hδ : 0 ≤ δ) {n : ℤ} (hn : n ≠ 0) :
    schoenbergIntegral p 1 * smoothedCuspCosCoeff p δ n =
      -∫ t : ℝ in Set.Ioi 0, cuspMixtureWeight p δ n t := by
  rw [← integral_schoenberg_cusp_swap hp0 hp1 hδ n]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (∫ x : AddCircle (1 : ℝ),
      circleCos n x *
        schoenbergIntegrand p (smoothedCuspBase δ x) t
        ∂AddCircle.haarAddCircle) =
    -cuspMixtureWeight p δ n t
  rw [integral_circleCos_mul_schoenbergIntegrand hδ hn ht]
  unfold cuspMixtureWeight
  ring

theorem cuspMixtureWeight_le_zeroSmoothing
    {p δ t : ℝ} (hδ : 0 ≤ δ) {n : ℤ} (ht : 0 < t) :
    cuspMixtureWeight p δ n t ≤ cuspMixtureWeight p 0 n t := by
  have hexp :
      Real.exp (-t * (δ + 1)) ≤ Real.exp (-t * (0 + 1)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold cuspMixtureWeight
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right hexp
    exact fourierCoeff_expCosCircle_re_nonneg ht.le n
  · exact Real.rpow_nonneg ht.le _

theorem integral_cuspMixtureWeight_le_zeroSmoothing
    {p δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hδ : 0 ≤ δ) {n : ℤ} (hn : n ≠ 0) :
    (∫ t : ℝ in Set.Ioi 0, cuspMixtureWeight p δ n t) ≤
      ∫ t : ℝ in Set.Ioi 0, cuspMixtureWeight p 0 n t := by
  apply integral_mono_ae
    (integrableOn_cuspMixtureWeight hp0 hp1 hδ hn)
    (integrableOn_cuspMixtureWeight hp0 hp1 (le_refl 0) hn)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact cuspMixtureWeight_le_zeroSmoothing hδ ht

/-- Adding a positive constant below the angular cusp cannot enlarge any
nonconstant cosine Fourier coefficient in absolute value. -/
theorem abs_smoothedCuspCosCoeff_le_zero
    {p δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hδ : 0 ≤ δ) {n : ℤ} (hn : n ≠ 0) :
    |smoothedCuspCosCoeff p δ n| ≤
      |smoothedCuspCosCoeff p 0 n| := by
  have hS : 0 < schoenbergIntegral p 1 :=
    schoenbergIntegral_one_pos hp0 hp1
  have hδrep :=
    schoenbergIntegral_mul_smoothedCuspCosCoeff hp0 hp1 hδ hn
  have h0rep :=
    schoenbergIntegral_mul_smoothedCuspCosCoeff hp0 hp1 (le_refl 0) hn
  have hδint : 0 ≤
      ∫ t : ℝ in Set.Ioi 0, cuspMixtureWeight p δ n t :=
    integral_nonneg_of_ae <| by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cuspMixtureWeight_nonneg hδ ht
  have h0int : 0 ≤
      ∫ t : ℝ in Set.Ioi 0, cuspMixtureWeight p 0 n t :=
    integral_nonneg_of_ae <| by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cuspMixtureWeight_nonneg (le_refl 0) ht
  have hmono :=
    integral_cuspMixtureWeight_le_zeroSmoothing hp0 hp1 hδ hn
  have hδnonpos : smoothedCuspCosCoeff p δ n ≤ 0 := by
    nlinarith
  have h0nonpos : smoothedCuspCosCoeff p 0 n ≤ 0 := by
    nlinarith
  have hcoeff :
      smoothedCuspCosCoeff p 0 n ≤
        smoothedCuspCosCoeff p δ n := by
    nlinarith
  rw [abs_of_nonpos hδnonpos, abs_of_nonpos h0nonpos]
  linarith

theorem circleCos_neg_index (n : ℤ) (x : AddCircle (1 : ℝ)) :
    circleCos (-n) x = circleCos n x := by
  unfold circleCos
  rw [fourier_neg]
  simp

theorem smoothedCuspCosCoeff_neg
    (p δ : ℝ) (n : ℤ) :
    smoothedCuspCosCoeff p δ (-n) =
      smoothedCuspCosCoeff p δ n := by
  unfold smoothedCuspCosCoeff
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change circleCos (-n) x * smoothedCuspBase δ x ^ p =
      circleCos n x * smoothedCuspBase δ x ^ p
    rw [circleCos_neg_index]

/-- Uniform positive-frequency decay for every smoothed cusp.  The constant
depends only on the exponent, never on the smoothing parameter. -/
theorem exists_smoothedCuspCosCoeff_power_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {δ : ℝ}, 0 ≤ δ → ∀ n : ℕ, 1 ≤ n →
      |smoothedCuspCosCoeff (α / 2) δ (n : ℤ)| ≤
        C * (n : ℝ) ^ (-1 - α) := by
  obtain ⟨C₀, hC₀, hC₀bound⟩ :=
    exists_unitChordCosCoeff_power_bound hα0 hα2
  let C : ℝ := (2 : ℝ) ^ (-(α / 2)) * C₀
  have hfactor : 0 < (2 : ℝ) ^ (-(α / 2)) := by positivity
  refine ⟨C, mul_pos hfactor hC₀, ?_⟩
  intro δ hδ n hn
  have hprofile :
      CircleFourier.chordProfileCircle (2 * (α / 2)) (by positivity) =
        CircleFourier.chordProfileCircle α hα0 := by
    congr 1
    ring
  have hdom := abs_smoothedCuspCosCoeff_le_zero
    (p := α / 2) (δ := δ) (by linarith) (by linarith)
    hδ (n := (n : ℤ)) (by exact_mod_cast (Nat.zero_lt_of_lt hn).ne')
  calc
    |smoothedCuspCosCoeff (α / 2) δ (n : ℤ)| ≤
        |smoothedCuspCosCoeff (α / 2) 0 (n : ℤ)| := hdom
    _ = (2 : ℝ) ^ (-(α / 2)) *
          |unitChordCosCoeff α n| := by
      rw [smoothedCuspCosCoeff_zero_eq_chord (by linarith)]
      rw [hprofile,
        CircleFourier.fourierCoeff_chordProfile_nat_eq_cosCoeff hα0]
      simp only [Complex.ofReal_re, abs_mul]
      rw [abs_of_pos hfactor]
    _ ≤ (2 : ℝ) ^ (-(α / 2)) *
          (C₀ * (n : ℝ) ^ (-1 - α)) :=
      mul_le_mul_of_nonneg_left (hC₀bound n hn) hfactor.le
    _ = C * (n : ℝ) ^ (-1 - α) := by
      dsimp [C]
      ring

theorem exists_fourierCoeff_smoothedCuspCircle_power_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {δ : ℝ} (hδ : 0 ≤ δ), ∀ n : ℕ, 1 ≤ n →
      ‖fourierCoeff
        (smoothedCuspCircle (α / 2) δ (by linarith) hδ) (n : ℤ)‖ ≤
          C * (n : ℝ) ^ (-1 - α) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_smoothedCuspCosCoeff_power_bound hα0 hα2
  refine ⟨C, hC, ?_⟩
  intro δ hδ n hn
  rw [fourierCoeff_smoothedCuspCircle_eq_cosCoeff (by linarith) hδ,
    Complex.norm_real, Real.norm_eq_abs]
  exact hbound hδ n hn

end CuspSmoothing

end BEMOC
