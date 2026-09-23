import BEMOCFormalization.DistanceScalarUniqueness
import BEMOCFormalization.DistanceZonalCoefficients

/-! Affine transfer of the exact shifted Legendre coefficient integral. -/

open scoped BigOperators
open MeasureTheory

namespace BEMOC.Definitive

theorem chordalPower_legendre_affine_integral (s : ℝ) (ℓ : ℕ) :
    (1 / 2 : ℝ) * (∫ t : ℝ in (-1)..1,
      (2 - 2 * t) ^ (s - 1) * (legendrePolynomial ℓ).eval t) =
      2 ^ (2 * s - 2) * (∫ y : ℝ in (0 : ℝ)..1,
        y ^ (s - 1) * (legendrePolynomial ℓ).eval (1 - 2 * y)) := by
  let f : ℝ → ℝ := fun t =>
    (2 - 2 * t) ^ (s - 1) * (legendrePolynomial ℓ).eval t
  have hchange := intervalIntegral.smul_integral_comp_sub_mul
    (a := (0 : ℝ)) (b := 1) f (2 : ℝ) (1 : ℝ)
  have hpoint (y : ℝ) (hy : y ∈ Set.uIcc (0 : ℝ) 1) :
      f (1 - 2 * y) =
        2 ^ (2 * s - 2) *
          (y ^ (s - 1) * (legendrePolynomial ℓ).eval (1 - 2 * y)) := by
    have hy0 : 0 ≤ y := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
      exact hy.1
    dsimp [f]
    have h4 : 2 - 2 * (1 - 2 * y) = 4 * y := by ring
    rw [h4, Real.mul_rpow (by norm_num : 0 ≤ (4 : ℝ)) hy0]
    have hpow : (4 : ℝ) ^ (s - 1) = 2 ^ (2 * s - 2) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      congr 1
      ring
    rw [hpow]
    ring
  have hcongr : (∫ y : ℝ in (0 : ℝ)..1, f (1 - 2 * y)) =
      2 ^ (2 * s - 2) * (∫ y : ℝ in (0 : ℝ)..1,
        y ^ (s - 1) * (legendrePolynomial ℓ).eval (1 - 2 * y)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y hy
    exact hpoint y hy
  rw [hcongr] at hchange
  rw [show (1 : ℝ) - 2 * 1 = -1 by norm_num,
    show (1 : ℝ) - 2 * 0 = 1 by norm_num] at hchange
  dsimp [f] at hchange
  linarith

theorem chordalPower_legendre_coefficient {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) (ℓ : ℕ) :
    (1 / 2 : ℝ) * (∫ t : ℝ in (-1)..1,
      (2 - 2 * t) ^ (s - 1) * (legendrePolynomial (ℓ + 1)).eval t) =
      -distanceHarmonicCoefficient s (ℓ + 1) := by
  rw [chordalPower_legendre_affine_integral]
  exact shiftedLegendreMoment_distanceCoefficient hs1 hs2 ℓ

theorem chordalPower_interval_mean {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) :
    (1 / 2 : ℝ) * (∫ t : ℝ in (-1)..1,
      (2 - 2 * t) ^ (s - 1)) = continuousEnergy (2 * s - 2) := by
  have h := chordalPower_legendre_affine_integral s 0
  have h' : (1 / 2 : ℝ) * (∫ t : ℝ in (-1)..1,
      (2 - 2 * t) ^ (s - 1)) =
      2 ^ (2 * s - 2) * shiftedLegendreMoment s 0 := by
    simpa [shiftedLegendreMoment, legendrePolynomial_zero] using h
  have hshift := shiftedLegendreMoment_product hs1 hs2 0
  simp only [Finset.prod_range_zero, mul_one] at hshift
  rw [hshift] at h'
  rw [continuousEnergy_two_s_sub_two (by linarith : 0 < s)]
  simpa [div_eq_mul_inv] using h'

/-- Uniform absolute convergence permits integration of the scalar Legendre
series against any fixed Legendre polynomial, term by term. -/
theorem distanceScalarSeries_moment_exchange_of_addition
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (haddition : HarmonicAdditionLegendre Y) (m : ℕ) :
    (∫ t : ℝ in (-1)..1,
      (∑' ℓ : ℕ, distanceHarmonicCoefficient s (ℓ + 1) *
        (2 * (ℓ : ℝ) + 3) *
          (legendrePolynomial (ℓ + 1)).eval t) *
        (legendrePolynomial m).eval t) =
      ∑' ℓ : ℕ, (∫ t : ℝ in (-1)..1,
        (distanceHarmonicCoefficient s (ℓ + 1) *
          (2 * (ℓ : ℝ) + 3) *
            (legendrePolynomial (ℓ + 1)).eval t) *
          (legendrePolynomial m).eval t) := by
  let F : ℕ → ℝ → ℝ := fun ℓ t =>
    (distanceHarmonicCoefficient s (ℓ + 1) *
      (2 * (ℓ : ℝ) + 3) *
        (legendrePolynomial (ℓ + 1)).eval t) *
      (legendrePolynomial m).eval t
  have hFcont (ℓ : ℕ) : ContinuousOn (F ℓ) (Set.Icc (-1 : ℝ) 1) := by
    dsimp [F]
    fun_prop
  have hFbound (ℓ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
      ‖F ℓ t‖ ≤ (2 * (ℓ : ℝ) + 3) *
        distanceHarmonicCoefficient s (ℓ + 1) := by
    have h1 := distanceScalarTerm_norm_le_of_addition Y hs1 hs2
      (harmonicAddition_diag Y) haddition ℓ t ht
    have h2 := legendrePolynomial_eval_abs_le_one_of_addition Y
      (harmonicAddition_diag Y) haddition m t ht.1 ht.2
    change ‖(distanceHarmonicCoefficient s (ℓ + 1) *
      (2 * (ℓ : ℝ) + 3) * (legendrePolynomial (ℓ + 1)).eval t) *
      (legendrePolynomial m).eval t‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ ‖distanceHarmonicCoefficient s (ℓ + 1) *
          (2 * (ℓ : ℝ) + 3) * (legendrePolynomial (ℓ + 1)).eval t‖ * 1 :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using h2)
          (norm_nonneg _)
      _ ≤ _ := by simpa using h1
  have hsum := intervalIntegral_tsum_of_summable_uniform_bound F
    (fun ℓ : ℕ => (2 * (ℓ : ℝ) + 3) *
      distanceHarmonicCoefficient s (ℓ + 1)) hFcont
    (distanceCoefficient_weighted_summable hs1 hs2) hFbound
  have hterm (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
      (∑' ℓ, F ℓ t) =
        (∑' ℓ : ℕ, distanceHarmonicCoefficient s (ℓ + 1) *
          (2 * (ℓ : ℝ) + 3) *
            (legendrePolynomial (ℓ + 1)).eval t) *
          (legendrePolynomial m).eval t := by
    exact (distanceScalarSeries_summable_of_addition Y hs1 hs2
      (harmonicAddition_diag Y) haddition t ht.1 ht.2).tsum_mul_right _
  rw [← hsum]
  apply intervalIntegral.integral_congr
  intro t ht
  exact (hterm t (by
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    exact ht)).symm

/-- Normalized spherical height is uniform on `[-1,1]`, for every polynomial
test function. -/
theorem sphereHeight_polynomial_integral (p : Polynomial ℝ) :
    (∫ x : Sphere, p.eval (sphereHeight x) ∂sigma) =
      (1 / 2 : ℝ) * (∫ t : ℝ in (-1)..1, p.eval t) := by
  have hmap := MeasureTheory.integral_map
    (μ := sigma) (continuous_sphereHeight.measurable.aemeasurable)
    p.continuous.aestronglyMeasurable
  rw [← hmap, hasUniformHeightMarginal, uniformHeightMeasure,
    integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2), smul_eq_mul]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

theorem harmonicAdditionKernel_sq_integral (Y : HarmonicBasis)
    (ℓ : ℕ) (y : Sphere) :
    (∫ x : Sphere, harmonicAdditionKernel Y ℓ y x ^ 2 ∂sigma) =
      ∑ k : Fin (2 * ℓ + 1), Y.function ℓ k y ^ 2 := by
  have hpoint (x : Sphere) : harmonicAdditionKernel Y ℓ y x ^ 2 =
      ∑ k : Fin (2 * ℓ + 1), ∑ j : Fin (2 * ℓ + 1),
        (Y.function ℓ k y * Y.function ℓ j y) *
          (Y.function ℓ k x * Y.function ℓ j x) := by
    unfold harmonicAdditionKernel
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hinner (k : Fin (2 * ℓ + 1)) :
      (∫ x : Sphere, ∑ j : Fin (2 * ℓ + 1),
        (Y.function ℓ k y * Y.function ℓ j y) *
          (Y.function ℓ k x * Y.function ℓ j x) ∂sigma) =
      ∑ j : Fin (2 * ℓ + 1),
        (Y.function ℓ k y * Y.function ℓ j y) *
          (∫ x : Sphere, Y.function ℓ k x * Y.function ℓ j x ∂sigma) := by
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul]
    · intro j hj
      exact (continuous_integrable_sigma
        ((Y.function ℓ k) * (Y.function ℓ j))).const_mul _
  simp_rw [hpoint]
  rw [integral_finset_sum]
  · simp_rw [hinner, Y.orthonormal]
    simp only [true_and, mul_ite, mul_one, mul_zero]
    simp only [Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [pow_two]
  · intro k hk
    apply integrable_finset_sum
    intro j hj
    exact (continuous_integrable_sigma
      ((Y.function ℓ k) * (Y.function ℓ j))).const_mul _

theorem sphereInnerKernel_northPole (x : Sphere) :
    sphereInnerKernel northPole x = sphereHeight x := by
  have hdist := northPole_dist_sq x
  have hinner := sphere_dist_sq_coordinates northPole x
  dsimp [sphereInnerKernel, sphereHeight] at hinner ⊢
  linarith

theorem legendrePolynomial_sq_interval_norm_of_addition
    (Y : HarmonicBasis) (haddition : HarmonicAdditionLegendre Y)
    (ℓ : ℕ) :
    (∫ t : ℝ in (-1)..1, (legendrePolynomial ℓ).eval t ^ 2) =
      2 / (2 * (ℓ : ℝ) + 1) := by
  let d : ℝ := 2 * (ℓ : ℝ) + 1
  have hd : d ≠ 0 := by dsimp [d]; positivity
  have hK := harmonicAdditionKernel_sq_integral Y ℓ northPole
  have hdiag := harmonicAddition_diag Y ℓ northPole
  have hpoly := sphereHeight_polynomial_integral ((legendrePolynomial ℓ) ^ 2)
  simp only [Polynomial.eval_pow] at hpoly
  have hpoint (x : Sphere) : harmonicAdditionKernel Y ℓ northPole x =
      d * (legendrePolynomial ℓ).eval (sphereHeight x) := by
    simpa [d, sphereInnerKernel_northPole] using haddition ℓ northPole x
  simp_rw [hpoint, mul_pow] at hK
  rw [integral_const_mul] at hK
  rw [hdiag] at hK
  rw [hpoly] at hK
  dsimp [d] at hd hK ⊢
  field_simp at hK ⊢
  nlinarith

theorem distanceScalarSeries_legendre_moment_of_addition
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (haddition : HarmonicAdditionLegendre Y) (m : ℕ) :
    (∫ t : ℝ in (-1)..1,
      (∑' ℓ : ℕ, distanceHarmonicCoefficient s (ℓ + 1) *
        (2 * (ℓ : ℝ) + 3) *
          (legendrePolynomial (ℓ + 1)).eval t) *
        (legendrePolynomial m).eval t) =
      if m = 0 then 0 else 2 * distanceHarmonicCoefficient s m := by
  rw [distanceScalarSeries_moment_exchange_of_addition Y hs1 hs2 haddition m]
  cases m with
  | zero =>
      have hzero (ℓ : ℕ) :
          (∫ t : ℝ in (-1)..1,
            (distanceHarmonicCoefficient s (ℓ + 1) * (2 * (ℓ : ℝ) + 3) *
              (legendrePolynomial (ℓ + 1)).eval t) *
              (legendrePolynomial 0).eval t) = 0 := by
        simp only [legendrePolynomial_zero, Polynomial.eval_one, mul_one]
        rw [intervalIntegral.integral_const_mul]
        have horth := legendrePolynomial_orthogonal_of_ne (ℓ + 1) 0 (by omega)
        have horth' : (∫ t : ℝ in (-1)..1,
            (legendrePolynomial (ℓ + 1)).eval t) = 0 := by
          simpa [legendrePolynomial_zero] using horth
        rw [horth']
        ring
      simp_rw [hzero]
      simp
  | succ j =>
      rw [tsum_eq_single j]
      · simp only [Nat.succ_ne_zero, ↓reduceIte]
        simp_rw [mul_assoc]
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_const_mul]
        have hnorm := legendrePolynomial_sq_interval_norm_of_addition Y haddition (j + 1)
        simp_rw [← pow_two]
        rw [hnorm]
        push_cast
        field_simp
        ring
      · intro ℓ hℓ
        simp_rw [mul_assoc]
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_const_mul]
        rw [legendrePolynomial_orthogonal_of_ne (ℓ + 1) (j + 1) (by omega)]
        simp

theorem distanceScalarExpansion_of_addition
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (haddition : HarmonicAdditionLegendre Y) :
    DistanceScalarExpansion s := by
  let F : ℝ → ℝ := fun t => ∑' ℓ : ℕ,
    distanceHarmonicCoefficient s (ℓ + 1) * (2 * (ℓ : ℝ) + 3) *
      (legendrePolynomial (ℓ + 1)).eval t
  let G : ℝ → ℝ := fun t =>
    continuousEnergy (2 * s - 2) - (2 - 2 * t) ^ (s - 1)
  have hF : ContinuousOn F (Set.Icc (-1 : ℝ) 1) :=
    distanceScalarSeries_continuousOn_of_addition Y hs1 hs2
      (harmonicAddition_diag Y) haddition
  have hpow : ContinuousOn (fun t : ℝ => (2 - 2 * t) ^ (s - 1))
      (Set.Icc (-1 : ℝ) 1) := by
    have hb : ContinuousOn (fun t : ℝ => 2 - 2 * t)
        (Set.Icc (-1 : ℝ) 1) := by fun_prop
    exact hb.rpow_const (fun t ht => Or.inr (by linarith))
  have hG : ContinuousOn G (Set.Icc (-1 : ℝ) 1) := by
    dsimp [G]
    exact continuousOn_const.sub hpow
  have hmom (m : ℕ) :
      (∫ t : ℝ in (-1)..1, F t * (legendrePolynomial m).eval t) =
      (∫ t : ℝ in (-1)..1, G t * (legendrePolynomial m).eval t) := by
    cases m with
    | zero =>
        have hF0 := distanceScalarSeries_legendre_moment_of_addition
          Y hs1 hs2 haddition 0
        have hmean := chordalPower_interval_mean hs1 hs2
        simp only [F, legendrePolynomial_zero, Polynomial.eval_one, mul_one,
          ↓reduceIte] at hF0 ⊢
        rw [hF0]
        dsimp [G]
        rw [intervalIntegral.integral_sub]
        · rw [intervalIntegral.integral_const]
          simp only [smul_eq_mul] at *
          linarith
        · exact intervalIntegrable_const
        · exact hpow.intervalIntegrable_of_Icc (by norm_num)
    | succ j =>
        have hFj := distanceScalarSeries_legendre_moment_of_addition
          Y hs1 hs2 haddition (j + 1)
        have hcoeff := chordalPower_legendre_coefficient hs1 hs2 j
        have horth := legendrePolynomial_orthogonal_of_ne 0 (j + 1) (by omega)
        have hzero : (∫ t : ℝ in (-1)..1,
            (legendrePolynomial (j + 1)).eval t) = 0 := by
          simpa [legendrePolynomial_zero] using horth
        dsimp [F] at hFj ⊢
        rw [hFj]
        dsimp [G]
        simp_rw [sub_mul]
        rw [intervalIntegral.integral_sub]
        · rw [intervalIntegral.integral_const_mul, hzero]
          linarith
        · apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
          exact continuousOn_const.mul
            (legendrePolynomial (j + 1)).continuous.continuousOn
        · apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
          exact hpow.mul (legendrePolynomial (j + 1)).continuous.continuousOn
  have hEq := continuousOn_eq_of_legendre_moments hF hG hmom
  intro t ht1 ht2
  exact ⟨distanceScalarSeries_summable_of_addition Y hs1 hs2
    (harmonicAddition_diag Y) haddition t ht1 ht2,
    hEq ⟨ht1, ht2⟩⟩

/-- The genuine geometric discrepancy controls the independently defined
Sobolev worst-case error once harmonic addition is identified with Legendre. -/
theorem sobolevEnergyComparison_of_addition
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (haddition : HarmonicAdditionLegendre Y) :
    SobolevEnergyComparison Y s :=
  sobolevEnergyComparison_of_legendre' Y hs1 hs2 haddition
    (distanceScalarExpansion_of_addition Y hs1 hs2 haddition)

end BEMOC.Definitive
