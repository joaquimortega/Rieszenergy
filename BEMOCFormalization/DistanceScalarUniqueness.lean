import BEMOCFormalization.DistanceKernelExpansion
import Mathlib.Topology.ContinuousMap.Weierstrass

/-! Uniqueness of a continuous scalar function from its Legendre moments. -/

open scoped BigOperators
open MeasureTheory

namespace BEMOC.Definitive

private theorem interval_integrable_mul_polynomial
    {h : ℝ → ℝ} (hh : ContinuousOn h (Set.Icc (-1 : ℝ) 1))
    (p : Polynomial ℝ) :
    IntervalIntegrable (fun t => h t * p.eval t) volume (-1) 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  exact hh.mul p.continuous.continuousOn

/-- Integration against a fixed continuous interval function is a linear
functional on the polynomial ring. -/
noncomputable def intervalPolynomialMomentLinearMap
    (h : ℝ → ℝ) (hh : ContinuousOn h (Set.Icc (-1 : ℝ) 1)) :
    Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ t : ℝ in (-1)..1, h t * p.eval t
  map_add' := by
    intro p q
    simp only [Polynomial.eval_add, mul_add]
    exact intervalIntegral.integral_add
      (interval_integrable_mul_polynomial hh p)
      (interval_integrable_mul_polynomial hh q)
  map_smul' := by
    intro c p
    simp only [Polynomial.eval_smul, smul_eq_mul]
    simp_rw [mul_left_comm]
    rw [intervalIntegral.integral_const_mul]
    rfl

theorem intervalPolynomialMoment_zero_of_legendre
    {h : ℝ → ℝ} (hh : ContinuousOn h (Set.Icc (-1 : ℝ) 1))
    (hmom : ∀ ℓ : ℕ,
      (∫ t : ℝ in (-1)..1, h t * (legendrePolynomial ℓ).eval t) = 0)
    (p : Polynomial ℝ) :
    (∫ t : ℝ in (-1)..1, h t * p.eval t) = 0 := by
  let L := intervalPolynomialMomentLinearMap h hh
  have hspan : Submodule.span ℝ (Set.range legendrePolynomial) ≤
      LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro q ⟨ℓ, rfl⟩
    change L (legendrePolynomial ℓ) = 0
    exact hmom ℓ
  have hp : p ∈ LinearMap.ker L := hspan (by rw [legendrePolynomial_span]; trivial)
  exact hp

/-- Rodrigues orthogonality extends from monomials to every lower-degree
polynomial. -/
theorem legendrePolynomial_orthogonal_lower (ℓ : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree < ℓ) :
    (∫ t : ℝ in (-1)..1,
      (legendrePolynomial ℓ).eval t * p.eval t) = 0 := by
  let h : ℝ → ℝ := fun t => (legendrePolynomial ℓ).eval t
  have hh : ContinuousOn h (Set.Icc (-1 : ℝ) 1) :=
    (legendrePolynomial ℓ).continuous.continuousOn
  let L := intervalPolynomialMomentLinearMap h hh
  have hL (j : ℕ) (hj : j < ℓ) : L (Polynomial.X ^ j) = 0 := by
    change (∫ t : ℝ in (-1)..1,
      (legendrePolynomial ℓ).eval t * (Polynomial.X ^ j).eval t) = 0
    simpa [mul_comm] using legendrePolynomial_orthogonal_monomial ℓ j hj
  have hsum := p.as_sum_support_C_mul_X_pow
  conv_lhs =>
    change L p
  rw [hsum, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [← Polynomial.smul_eq_C_mul, map_smul,
    hL j ((Polynomial.le_natDegree_of_mem_supp j hj).trans_lt hp)]
  simp

theorem legendrePolynomial_orthogonal_of_ne (ℓ m : ℕ) (hℓm : ℓ ≠ m) :
    (∫ t : ℝ in (-1)..1,
      (legendrePolynomial ℓ).eval t * (legendrePolynomial m).eval t) = 0 := by
  rcases lt_or_gt_of_ne hℓm with hlt | hgt
  · have h := legendrePolynomial_orthogonal_lower m (legendrePolynomial ℓ)
      (by rw [legendrePolynomial_natDegree]; exact hlt)
    simpa only [mul_comm] using h
  · exact legendrePolynomial_orthogonal_lower ℓ (legendrePolynomial m)
      (by rw [legendrePolynomial_natDegree]; exact hgt)

/-- A continuous function on the closed interval is determined by its
Legendre moments. -/
theorem continuousOn_eq_zero_of_legendre_moments
    {h : ℝ → ℝ} (hh : ContinuousOn h (Set.Icc (-1 : ℝ) 1))
    (hmom : ∀ ℓ : ℕ,
      (∫ t : ℝ in (-1)..1, h t * (legendrePolynomial ℓ).eval t) = 0) :
    Set.EqOn h 0 (Set.Icc (-1 : ℝ) 1) := by
  let f : C(Set.Icc (-1 : ℝ) 1, ℝ) := ⟨fun x => h x, hh.restrict⟩
  have hpoly (p : Polynomial ℝ) :
      (∫ t : ℝ in (-1)..1, h t * p.eval t) = 0 :=
    intervalPolynomialMoment_zero_of_legendre hh hmom p
  have hsqi : IntervalIntegrable (fun t : ℝ => h t ^ 2) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact hh.pow 2
  let I : ℝ := ∫ t : ℝ in (-1)..1, h t ^ 2
  have hI : I = 0 := by
    by_contra hI0
    let M : ℝ := ‖f‖ + 1
    have hM : 0 < M := by dsimp [M]; positivity
    let ε : ℝ := |I| / (4 * M)
    have hε : 0 < ε := div_pos (abs_pos.mpr hI0) (by positivity)
    obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap (-1) 1 f ε hε
    have hclose (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
        |h t - p.eval t| ≤ ε := by
      have hnorm := (p.toContinuousMapOn (Set.Icc (-1 : ℝ) 1) - f).norm_coe_le_norm
        ⟨t, ht⟩
      have : ‖(p.toContinuousMapOn (Set.Icc (-1 : ℝ) 1) - f) ⟨t, ht⟩‖ < ε :=
        lt_of_le_of_lt hnorm hp
      simpa [f, Real.norm_eq_abs, abs_sub_comm] using this.le
    have hbound (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) : |h t| ≤ M := by
      have hf := f.norm_coe_le_norm ⟨t, ht⟩
      dsimp [f, M] at hf ⊢
      simpa only [Real.norm_eq_abs] using (hf.trans (by linarith))
    have hdiffi : IntervalIntegrable (fun t : ℝ => h t * (h t - p.eval t))
        volume (-1) 1 := by
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      exact hh.mul (hh.sub p.continuous.continuousOn)
    have hIeq : I = ∫ t : ℝ in (-1)..1, h t * (h t - p.eval t) := by
      dsimp [I]
      simp_rw [mul_sub, ← pow_two]
      rw [intervalIntegral.integral_sub hsqi (interval_integrable_mul_polynomial hh p),
        hpoly p, sub_zero]
    have hsmall : |I| ≤ 2 * M * ε := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (-1 : ℝ)) (b := 1) (C := M * ε)
        (f := fun t : ℝ => h t * (h t - p.eval t)) (by
          intro t ht
          have htIoc : t ∈ Set.Ioc (-1 : ℝ) 1 := by
            simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
          have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨htIoc.1.le, htIoc.2⟩
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hbound t ht') (hclose t ht')
            (abs_nonneg _) (by positivity))
      have h' := h
      rw [← hIeq] at h'
      norm_num [Real.norm_eq_abs] at h'
      nlinarith
    dsimp [ε] at hsmall
    have habs : 0 < |I| := abs_pos.mpr hI0
    nlinarith [div_mul_cancel₀ |I| (show 4 * M ≠ 0 by positivity)]
  have hae : (fun t : ℝ => h t ^ 2) =ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)] 0 := by
    exact (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
      (by norm_num : (-1 : ℝ) ≤ 1)
      (Filter.Eventually.of_forall (fun t => sq_nonneg (h t))) hsqi).mp hI
  have hae' : h =ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)] 0 := by
    filter_upwards [hae] with t ht
    exact (sq_eq_zero_iff).mp ht
  have hon : Set.EqOn h 0 (Set.Ioc (-1 : ℝ) 1) :=
    Measure.eqOn_of_ae_eq hae' (hh.mono Set.Ioc_subset_Icc_self)
      continuousOn_const (by
        rw [interior_Ioc, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
        exact Set.Ioc_subset_Icc_self)
  exact hon.of_subset_closure hh continuousOn_const Set.Ioc_subset_Icc_self (by
    rw [closure_Ioc (by norm_num : (-1 : ℝ) ≠ 1)])

theorem continuousOn_eq_of_legendre_moments
    {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hg : ContinuousOn g (Set.Icc (-1 : ℝ) 1))
    (hmom : ∀ ℓ : ℕ,
      (∫ t : ℝ in (-1)..1, f t * (legendrePolynomial ℓ).eval t) =
        (∫ t : ℝ in (-1)..1, g t * (legendrePolynomial ℓ).eval t)) :
    Set.EqOn f g (Set.Icc (-1 : ℝ) 1) := by
  have hzero : Set.EqOn (fun t => f t - g t) 0 (Set.Icc (-1 : ℝ) 1) := by
    apply continuousOn_eq_zero_of_legendre_moments (hf.sub hg)
    intro ℓ
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub
      (interval_integrable_mul_polynomial hf _)
      (interval_integrable_mul_polynomial hg _), hmom ℓ, sub_self]
  intro t ht
  exact sub_eq_zero.mp (hzero ht)

/-- A summable uniform bound permits exchanging the scalar interval integral
and a series of continuous terms. -/
theorem intervalIntegral_tsum_of_summable_uniform_bound
    (F : ℕ → ℝ → ℝ) (u : ℕ → ℝ)
    (hcont : ∀ ℓ, ContinuousOn (F ℓ) (Set.Icc (-1 : ℝ) 1))
    (hu : Summable u)
    (hbound : ∀ ℓ t, t ∈ Set.Icc (-1 : ℝ) 1 → ‖F ℓ t‖ ≤ u ℓ) :
    (∫ t : ℝ in (-1)..1, ∑' ℓ, F ℓ t) =
      ∑' ℓ, (∫ t : ℝ in (-1)..1, F ℓ t) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (-1 : ℝ) 1)
  have hInt (ℓ : ℕ) : Integrable (F ℓ) μ := by
    have hi := (hcont ℓ).intervalIntegrable_of_Icc (μ := volume)
      (by norm_num : (-1 : ℝ) ≤ 1)
    simpa [μ, Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hi.1
  have hNormInt (ℓ : ℕ) : IntervalIntegrable (fun t => ‖F ℓ t‖)
      volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact (hcont ℓ).norm
  have hNormBound (ℓ : ℕ) :
      (∫ t, ‖F ℓ t‖ ∂μ) ≤ 2 * u ℓ := by
    rw [show (∫ t, ‖F ℓ t‖ ∂μ) =
        (∫ t : ℝ in (-1)..1, ‖F ℓ t‖) by
      simp [μ, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]]
    have hmono := intervalIntegral.integral_mono_on
      (by norm_num : (-1 : ℝ) ≤ 1) (hNormInt ℓ)
      (intervalIntegrable_const) (fun t ht => hbound ℓ t ht)
    norm_num at hmono ⊢
    exact hmono
  have hSumNorm : Summable (fun ℓ => ∫ t, ‖F ℓ t‖ ∂μ) := by
    apply Summable.of_nonneg_of_le
    · intro ℓ
      exact integral_nonneg (fun _ => norm_nonneg _)
    · exact hNormBound
    · exact hu.mul_left 2
  have h := integral_tsum_of_summable_integral_norm hInt hSumNorm
  simpa [μ, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using h.symm

end BEMOC.Definitive
