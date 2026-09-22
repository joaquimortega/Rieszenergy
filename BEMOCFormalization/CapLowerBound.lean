import BEMOCFormalization.CapDiscrepancy
import BEMOCFormalization.BinomialTail

open scoped BigOperators
open MeasureTheory
namespace BEMOC.Definitive

/-- The even moments of the normalized height marginal. -/
theorem sphereHeight_even_moment (r : ℕ) :
    (∫ u : Sphere, sphereHeight u ^ (2 * r) ∂sigma) =
      1 / ((2 * r + 1 : ℕ) : ℝ) := by
  have hmap := MeasureTheory.integral_map
    (μ := sigma) continuous_sphereHeight.measurable.aemeasurable
    (continuous_id.pow (2 * r)).aestronglyMeasurable
  change (∫ u : Sphere, (id (sphereHeight u)) ^ (2 * r) ∂sigma) = _
  rw [← hmap, hasUniformHeightMarginal, uniformHeightMeasure,
    integral_smul_measure]
  simp only [id_eq, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2), smul_eq_mul]
  rw [show (∫ z : ℝ, z ^ (2 * r) ∂volume.restrict (Set.Ioc (-1) 1)) =
      ∫ z : ℝ in (-1)..1, z ^ (2 * r) by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]]
  rw [integral_pow]
  simp only [one_pow, pow_add, pow_mul, neg_one_sq, one_pow, mul_neg,
    Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

/-- Odd height moments vanish under the uniform marginal. -/
theorem sphereHeight_odd_moment (r : ℕ) :
    (∫ u : Sphere, sphereHeight u ^ (2 * r + 1) ∂sigma) = 0 := by
  have hmap := MeasureTheory.integral_map
    (μ := sigma) continuous_sphereHeight.measurable.aemeasurable
    (continuous_id.pow (2 * r + 1)).aestronglyMeasurable
  change (∫ u : Sphere, (id (sphereHeight u)) ^ (2 * r + 1) ∂sigma) = _
  rw [← hmap, hasUniformHeightMarginal, uniformHeightMeasure,
    integral_smul_measure]
  simp only [id_eq, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2), smul_eq_mul]
  rw [show (∫ z : ℝ, z ^ (2 * r + 1) ∂volume.restrict (Set.Ioc (-1) 1)) =
      ∫ z : ℝ in (-1)..1, z ^ (2 * r + 1) by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]]
  rw [integral_pow]
  simp [pow_add, pow_mul]

private theorem inner_northPole_eq_height_moment (x : Sphere) :
    @Inner.inner ℝ Ambient _ (x : Ambient) (northPole : Ambient) = sphereHeight x := by
  simp [northPole, parallelPoint, parallelVector, sphereHeight,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]

/-- Reflection invariance transfers any integer projection moment to the height coordinate. -/
theorem sphere_projection_power_eq_height (u : Sphere) (m : ℕ) :
    (∫ x : Sphere,
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ m ∂sigma) =
      (∫ x : Sphere, sphereHeight x ^ m ∂sigma) := by
  let R : Ambient ≃ₗᵢ[ℝ] Ambient :=
    (ℝ ∙ ((u : Ambient) - (northPole : Ambient)))ᗮ.reflection
  have hnorm : ‖(u : Ambient)‖ = ‖(northPole : Ambient)‖ := by
    rw [norm_eq_of_mem_sphere u, norm_eq_of_mem_sphere northPole]
  have hRu : R (u : Ambient) = (northPole : Ambient) :=
    Submodule.reflection_sub hnorm
  let e := sphereLinearIsometryEquiv R
  have hmap := MeasureTheory.integral_map_equiv e
    (μ := sigma) (fun x : Sphere ↦ sphereHeight x ^ m)
  rw [sigma_reflection_invariant ((u : Ambient) - (northPole : Ambient))] at hmap
  have hpoint (x : Sphere) :
      sphereHeight (e x) = @Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient) := by
    rw [← inner_northPole_eq_height_moment (e x)]
    change @Inner.inner ℝ Ambient _ (R (x : Ambient)) (northPole : Ambient) = _
    rw [← hRu, R.inner_map_map]
    exact (real_inner_comm (x : Ambient) (u : Ambient)).symm
  calc
    _ = ∫ x : Sphere, sphereHeight (e x) ^ m ∂sigma := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hpoint]
    _ = ∫ x : Sphere, sphereHeight x ^ m ∂sigma := hmap.symm


/-- Every unit direction has the same even projection moments. -/
theorem sphere_projection_even_moment (u : Sphere) (r : ℕ) :
    (∫ x : Sphere,
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * r) ∂sigma) =
      1 / ((2 * r + 1 : ℕ) : ℝ) := by
  rw [sphere_projection_power_eq_height]
  exact sphereHeight_even_moment r

/-- Every odd projection moment vanishes. -/
theorem sphere_projection_odd_moment (u : Sphere) (r : ℕ) :
    (∫ x : Sphere,
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * r + 1) ∂sigma) =
      0 := by
  rw [sphere_projection_power_eq_height]
  exact sphereHeight_odd_moment r

/-- Diagonal terms alone give the universal even-moment lower bound. -/
theorem finite_even_projection_energy_ge_card {ι : Type} [Fintype ι]
    (X : ι → Sphere) (r : ℕ) :
    (Fintype.card ι : ℝ) ≤
      ∑ i : ι, ∑ j : ι,
        (@Inner.inner ℝ Ambient _ (X i : Ambient) (X j : Ambient)) ^ (2 * r) := by
  have hdiag (i : ι) :
      (@Inner.inner ℝ Ambient _ (X i : Ambient) (X i : Ambient)) ^ (2 * r) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere (X i)]
    norm_num
  calc
    (Fintype.card ι : ℝ) = ∑ i : ι,
        (@Inner.inner ℝ Ambient _ (X i : Ambient) (X i : Ambient)) ^ (2 * r) := by
      simp_rw [hdiag]
      simp
    _ ≤ ∑ i : ι, ∑ j : ι,
        (@Inner.inner ℝ Ambient _ (X i : Ambient) (X j : Ambient)) ^ (2 * r) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j : ι ↦
          (@Inner.inner ℝ Ambient _ (X i : Ambient) (X j : Ambient)) ^ (2 * r))
        (fun j _ ↦ by
          change 0 ≤ (@Inner.inner ℝ Ambient _ (X i : Ambient) (X j : Ambient)) ^ (2 * r)
          rw [show 2 * r = r * 2 by omega, pow_mul]
          exact sq_nonneg _) (Finset.mem_univ i)

/-- Pair energy of an integer power of the inner-product kernel is a
finite sum of tensor-moment products. -/
theorem kernelPairEnergy_innerPow (m : ℕ) (μ ν : Measure Sphere)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m) μ ν =
      ∑ p : Fin m → Fin 3,
        sphereTensorMoment μ m p * sphereTensorMoment ν m p := by
  unfold kernelPairEnergy
  simp_rw [sphereInnerKernel_pow_eq_feature_sum]
  have hfeatureμ (p : Fin m → Fin 3) := integrable_sphereTensorFeature μ m p
  have hfeatureν (p : Fin m → Fin 3) := integrable_sphereTensorFeature ν m p
  have hinner (x : Sphere) :
      (∫ y : Sphere, ∑ p : Fin m → Fin 3,
        sphereTensorFeature m p x * sphereTensorFeature m p y ∂ν) =
      ∑ p : Fin m → Fin 3,
        sphereTensorFeature m p x * sphereTensorMoment ν m p := by
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul]
      rfl
    · intro p hp
      exact (hfeatureν p).const_mul _
  simp_rw [hinner]
  rw [integral_finset_sum]
  · simp_rw [integral_mul_const]
    rfl
  · intro p hp
    exact (hfeatureμ p).mul_const _

/-- Integer powers of the inner-product kernel are positive definite for
finite positive measures. -/
theorem measurePositiveDefinite_innerPow (m : ℕ) :
    MeasurePositiveDefinite (fun x y ↦ sphereInnerKernel x y ^ m) := by
  intro μ ν hμ hν
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  rw [kernelPairEnergy_innerPow, kernelPairEnergy_innerPow,
    kernelPairEnergy_innerPow, kernelPairEnergy_innerPow]
  have hs : 0 ≤ ∑ p : Fin m → Fin 3,
      (sphereTensorMoment μ m p - sphereTensorMoment ν m p) ^ 2 :=
    Finset.sum_nonneg (fun p _ ↦ sq_nonneg _)
  simp_rw [sub_pow_two, pow_two] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  have hid : (∑ p : Fin m → Fin 3,
      2 * sphereTensorMoment μ m p * sphereTensorMoment ν m p) =
      (∑ p : Fin m → Fin 3,
        sphereTensorMoment μ m p * sphereTensorMoment ν m p) +
      (∑ p : Fin m → Fin 3,
        sphereTensorMoment ν m p * sphereTensorMoment μ m p) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hid] at hs
  linarith

/-- Counting measure of a finite spherical configuration. -/
noncomputable def empiricalSphereMeasure {ι : Type} [Fintype ι]
    (X : ι → Sphere) : Measure Sphere :=
  ∑ i : ι, Measure.dirac (X i)

instance empiricalSphereMeasure_isFinite {ι : Type} [Fintype ι]
    (X : ι → Sphere) : IsFiniteMeasure (empiricalSphereMeasure X) := by
  unfold empiricalSphereMeasure
  infer_instance

@[simp] theorem sphereTensorMoment_empiricalSphereMeasure {ι : Type} [Fintype ι]
    (X : ι → Sphere) (m : ℕ) (p : Fin m → Fin 3) :
    sphereTensorMoment (empiricalSphereMeasure X) m p =
      ∑ i : ι, sphereTensorFeature m p (X i) := by
  unfold sphereTensorMoment empiricalSphereMeasure
  rw [integral_finset_sum_measure]
  · simp
  · intro i hi
    exact integrable_sphereTensorFeature (Measure.dirac (X i)) m p

/-- Pair energy against two counting measures is the ordered double sum. -/
theorem kernelPairEnergy_empiricalSphereMeasure {ι κ : Type}
    [Fintype ι] [Fintype κ] (K : Sphere → Sphere → ℝ)
    (X : ι → Sphere) (Y : κ → Sphere) :
    kernelPairEnergy K (empiricalSphereMeasure X) (empiricalSphereMeasure Y) =
      ∑ i : ι, ∑ j : κ, K (X i) (Y j) := by
  unfold kernelPairEnergy empiricalSphereMeasure
  rw [integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_dirac]
    rw [integral_finset_sum_measure]
    · simp
    · intro j hj
      exact integrable_dirac
  · intro i hi
    exact integrable_dirac

theorem sphereInnerKernel_eq_inner (x y : Sphere) :
    sphereInnerKernel x y =
      @Inner.inner ℝ Ambient _ (x : Ambient) (y : Ambient) := by
  simp [sphereInnerKernel, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem kernelPairEnergy_smul_left (K : Sphere → Sphere → ℝ)
    (c : ENNReal) (μ ν : Measure Sphere) :
    kernelPairEnergy K (c • μ) ν = c.toReal * kernelPairEnergy K μ ν := by
  unfold kernelPairEnergy
  rw [integral_smul_measure]
  rfl

theorem kernelPairEnergy_smul_right (K : Sphere → Sphere → ℝ)
    (c : ENNReal) (μ ν : Measure Sphere) :
    kernelPairEnergy K μ (c • ν) = c.toReal * kernelPairEnergy K μ ν := by
  unfold kernelPairEnergy
  simp_rw [integral_smul_measure]
  simp only [smul_eq_mul]
  rw [integral_const_mul]

/-- Uniform height moment of integer degree. -/
noncomputable def sphereHeightMoment (m : ℕ) : ℝ :=
  ∫ x : Sphere, sphereHeight x ^ m ∂sigma

theorem kernelPairEnergy_innerPow_empirical_sigma {ι : Type} [Fintype ι]
    (X : ι → Sphere) (m : ℕ) :
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m)
      (empiricalSphereMeasure X) sigma =
      (Fintype.card ι : ℝ) * sphereHeightMoment m := by
  unfold kernelPairEnergy empiricalSphereMeasure
  rw [integral_finset_sum_measure]
  · simp_rw [integral_dirac]
    have hpoint (i : ι) :
        (∫ y : Sphere, sphereInnerKernel (X i) y ^ m ∂sigma) =
          sphereHeightMoment m := by
      simpa only [sphereInnerKernel_eq_inner, sphereHeightMoment] using
        sphere_projection_power_eq_height (X i) m
    simp_rw [hpoint]
    simp
  · intro i hi
    exact integrable_dirac

theorem kernelPairEnergy_innerPow_sigma_sigma (m : ℕ) :
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m) sigma sigma =
      sphereHeightMoment m := by
  unfold kernelPairEnergy
  have hpoint (x : Sphere) :
      (∫ y : Sphere, sphereInnerKernel x y ^ m ∂sigma) =
        sphereHeightMoment m := by
    simpa only [sphereInnerKernel_eq_inner, sphereHeightMoment] using
      sphere_projection_power_eq_height x m
  simp_rw [hpoint]
  simp

/-- The mixed even-power energy of a configuration with surface area is
its cardinality times the uniform projection moment. -/
theorem kernelPairEnergy_even_empirical_sigma {ι : Type} [Fintype ι]
    (X : ι → Sphere) (r : ℕ) :
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ (2 * r))
      (empiricalSphereMeasure X) sigma =
      (Fintype.card ι : ℝ) / ((2 * r + 1 : ℕ) : ℝ) := by
  unfold kernelPairEnergy empiricalSphereMeasure
  rw [integral_finset_sum_measure]
  · simp_rw [integral_dirac]
    have hpoint (i : ι) :
        (∫ y : Sphere, sphereInnerKernel (X i) y ^ (2 * r) ∂sigma) =
          1 / ((2 * r + 1 : ℕ) : ℝ) := by
      simpa only [sphereInnerKernel_eq_inner] using
        sphere_projection_even_moment (X i) r
    simp_rw [hpoint]
    simp [div_eq_mul_inv]
  · intro i hi
    exact integrable_dirac

/-- The uniform even-power self-energy is its projection moment. -/
theorem kernelPairEnergy_even_sigma_sigma (r : ℕ) :
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ (2 * r)) sigma sigma =
      1 / ((2 * r + 1 : ℕ) : ℝ) := by
  unfold kernelPairEnergy
  have hpoint (x : Sphere) :
      (∫ y : Sphere, sphereInnerKernel x y ^ (2 * r) ∂sigma) =
        1 / ((2 * r + 1 : ℕ) : ℝ) := by
    simpa only [sphereInnerKernel_eq_inner] using
      sphere_projection_even_moment x r
  simp_rw [hpoint]
  simp

/-- Positivity of every integer power-moment pair sum, including odd
powers, follows from the tensor feature representation. -/
theorem finite_projection_power_energy_nonneg {ι : Type} [Fintype ι]
    (X : ι → Sphere) (m : ℕ) :
    0 ≤ ∑ i : ι, ∑ j : ι,
      (@Inner.inner ℝ Ambient _ (X i : Ambient) (X j : Ambient)) ^ m := by
  let μ := empiricalSphereMeasure X
  let K : Sphere → Sphere → ℝ := fun x y ↦ sphereInnerKernel x y ^ m
  have hpd := measurePositiveDefinite_innerPow m μ 0
    (measure_ne_top μ Set.univ) (by simp)
  have hμμ : kernelPairEnergy K μ μ =
      ∑ i : ι, ∑ j : ι,
        (@Inner.inner ℝ Ambient _ (X i : Ambient) (X j : Ambient)) ^ m := by
    change kernelPairEnergy K (empiricalSphereMeasure X) (empiricalSphereMeasure X) = _
    rw [kernelPairEnergy_empiricalSphereMeasure]
    simp [K, sphereInnerKernel_eq_inner]
  have hzero1 : kernelPairEnergy K μ 0 = 0 := by simp [kernelPairEnergy]
  have hzero2 : kernelPairEnergy K 0 μ = 0 := by simp [kernelPairEnergy]
  have hzero3 : kernelPairEnergy K 0 0 = 0 := by simp [kernelPairEnergy]
  rw [hzero1, hzero2, hzero3, hμμ] at hpd
  linarith

/-- Every even power-moment gap is nonnegative. This is the finite
positive-definite-kernel step in Beck's argument. -/
theorem even_projection_moment_gap_nonneg {ι : Type} [Fintype ι]
    (X : ι → Sphere) (r : ℕ) :
    (Fintype.card ι : ℝ) ^ 2 / ((2 * r + 1 : ℕ) : ℝ) ≤
      ∑ i : ι, ∑ j : ι,
        (@Inner.inner ℝ Ambient _ (X i : Ambient) (X j : Ambient)) ^ (2 * r) := by
  let μ := empiricalSphereMeasure X
  let ν : Measure Sphere := (Fintype.card ι : ENNReal) • sigma
  let K : Sphere → Sphere → ℝ := fun x y ↦ sphereInnerKernel x y ^ (2 * r)
  haveI : IsFiniteMeasure ν := IsFiniteMeasure.mk (by
    dsimp [ν]
    rw [sigma_apply_univ]
    simp)
  have hcomm : kernelPairEnergy K sigma μ = kernelPairEnergy K μ sigma := by
    change kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ (2 * r)) sigma μ = _
    rw [kernelPairEnergy_innerPow, kernelPairEnergy_innerPow]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hμν : kernelPairEnergy K μ ν =
      (Fintype.card ι : ℝ) ^ 2 / ((2 * r + 1 : ℕ) : ℝ) := by
    change kernelPairEnergy K μ ((Fintype.card ι : ENNReal) • sigma) = _
    rw [kernelPairEnergy_smul_right, kernelPairEnergy_even_empirical_sigma]
    simp only [ENNReal.toReal_natCast]
    ring
  have hνμ : kernelPairEnergy K ν μ =
      (Fintype.card ι : ℝ) ^ 2 / ((2 * r + 1 : ℕ) : ℝ) := by
    change kernelPairEnergy K ((Fintype.card ι : ENNReal) • sigma) μ = _
    rw [kernelPairEnergy_smul_left, hcomm, kernelPairEnergy_even_empirical_sigma]
    simp only [ENNReal.toReal_natCast]
    ring
  have hνν : kernelPairEnergy K ν ν =
      (Fintype.card ι : ℝ) ^ 2 / ((2 * r + 1 : ℕ) : ℝ) := by
    change kernelPairEnergy K ((Fintype.card ι : ENNReal) • sigma)
      ((Fintype.card ι : ENNReal) • sigma) = _
    rw [kernelPairEnergy_smul_left, kernelPairEnergy_smul_right,
      kernelPairEnergy_even_sigma_sigma]
    simp only [ENNReal.toReal_natCast]
    ring
  have hμμ : kernelPairEnergy K μ μ =
      ∑ i : ι, ∑ j : ι,
        (@Inner.inner ℝ Ambient _ (X i : Ambient) (X j : Ambient)) ^ (2 * r) := by
    change kernelPairEnergy K (empiricalSphereMeasure X) (empiricalSphereMeasure X) = _
    rw [kernelPairEnergy_empiricalSphereMeasure]
    simp [K, sphereInnerKernel_eq_inner]
  have hpd := measurePositiveDefinite_innerPow (2 * r) μ ν
    (measure_ne_top μ Set.univ) (measure_ne_top ν Set.univ)
  rw [hμν, hνμ, hνν, hμμ] at hpd
  linarith

/-- In unnormalized energy units, high even-degree gaps are at least `n/2`. -/
theorem even_power_energy_gap_ge_half_card {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) (r : ℕ) (hr : n ≤ r) :
    (n : ℝ) / 2 ≤
      kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ (2 * r))
        (empiricalSphereMeasure X) (empiricalSphereMeasure X) -
      kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ (2 * r))
        ((n : ENNReal) • sigma) ((n : ENNReal) • sigma) := by
  rw [kernelPairEnergy_empiricalSphereMeasure,
    kernelPairEnergy_smul_left, kernelPairEnergy_smul_right,
    kernelPairEnergy_even_sigma_sigma]
  simp only [ENNReal.toReal_natCast]
  simp_rw [sphereInnerKernel_eq_inner]
  have hsum := finite_even_projection_energy_ge_card X r
  simp only [Fintype.card_fin] at hsum
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hrreal : (n : ℝ) ≤ r := by exact_mod_cast hr
  have hden : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) := by positivity
  have hfrac : (n : ℝ) * ((n : ℝ) * (1 / ((2 * r + 1 : ℕ) : ℝ))) ≤
      (n : ℝ) / 2 := by
    have hden2 : (2 * (n : ℝ)) ≤ ((2 * r + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hbase : (n : ℝ) / ((2 * r + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
      apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).2
      linarith
    have hmul := mul_le_mul_of_nonneg_left hbase hnreal.le
    convert hmul using 1 <;> ring
  linarith

/-- The interior binomial partial kernel for regularized chordal distance. -/
noncomputable def chordPartialKernel (ρ : ℝ) (M : ℕ) (x y : Sphere) : ℝ :=
  Real.sqrt 2 * ∑ m ∈ Finset.range M,
    Ring.choose (1 / 2 : ℝ) m * (-ρ * sphereInnerKernel x y) ^ m

/-- The regularized chordal kernel, whose limit at `ρ=1` is distance. -/
noncomputable def chordRegularizedKernel (ρ : ℝ) (x y : Sphere) : ℝ :=
  Real.sqrt 2 * Real.sqrt (1 - ρ * sphereInnerKernel x y)

theorem chordPartialKernel_tendsto {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (x y : Sphere) :
    Filter.Tendsto (fun M ↦ chordPartialKernel ρ M x y) Filter.atTop
      (_root_.nhds (chordRegularizedKernel ρ x y)) := by
  have hinner := sphereInnerKernel_abs_le_one x y
  have hx : |-(ρ * sphereInnerKernel x y)| < 1 := by
    rw [abs_neg, abs_mul, abs_of_nonneg hρ]
    nlinarith [mul_le_mul_of_nonneg_left hinner hρ]
  have hseries := ((summable_real_choose_mul_pow (1 / 2 : ℝ)
    (-(ρ * sphereInnerKernel x y)) hx).hasSum).tendsto_sum_nat
  have hlim := hseries.const_mul (Real.sqrt 2)
  rw [tsum_real_choose_mul_pow_eq_rpow (1 / 2 : ℝ)
    (-(ρ * sphereInnerKernel x y)) hx] at hlim
  simpa [chordPartialKernel, chordRegularizedKernel,
    Real.sqrt_eq_rpow, mul_assoc] using hlim

/-- A uniform bound on every binomial partial kernel at fixed `ρ<1`. -/
theorem chordPartialKernel_norm_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (M : ℕ) (x y : Sphere) :
    ‖chordPartialKernel ρ M x y‖ ≤
      Real.sqrt 2 * (∑' m : ℕ, |Ring.choose (1 / 2 : ℝ) m * ρ ^ m|) := by
  have hsum : Summable (fun m : ℕ ↦ Ring.choose (1 / 2 : ℝ) m * ρ ^ m) :=
    summable_real_choose_mul_pow (1 / 2 : ℝ) ρ (by rw [abs_of_nonneg hρ]; exact hρ1)
  have hmajor : HasSum (fun m : ℕ ↦ |Ring.choose (1 / 2 : ℝ) m * ρ ^ m|)
      (∑' m : ℕ, |Ring.choose (1 / 2 : ℝ) m * ρ ^ m|) := hsum.norm.hasSum
  have hinner : |sphereInnerKernel x y| ≤ 1 := sphereInnerKernel_abs_le_one x y
  have hterm (m : ℕ) :
      |Ring.choose (1 / 2 : ℝ) m * (-ρ * sphereInnerKernel x y) ^ m| ≤
        |Ring.choose (1 / 2 : ℝ) m * ρ ^ m| := by
    simp only [abs_mul, abs_pow, abs_neg, abs_of_nonneg hρ,
      abs_of_nonneg (pow_nonneg hρ _), mul_pow]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact mul_le_of_le_one_right (pow_nonneg hρ _)
      (pow_le_one₀ (abs_nonneg _) hinner)
  rw [Real.norm_eq_abs, chordPartialKernel, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    |∑ m ∈ Finset.range M,
      Ring.choose (1 / 2 : ℝ) m * (-ρ * sphereInnerKernel x y) ^ m| ≤
      ∑ m ∈ Finset.range M,
        |Ring.choose (1 / 2 : ℝ) m * (-ρ * sphereInnerKernel x y) ^ m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range M,
        |Ring.choose (1 / 2 : ℝ) m * ρ ^ m| :=
      Finset.sum_le_sum (fun m hm ↦ hterm m)
    _ ≤ _ := sum_le_hasSum (Finset.range M) (fun m hm ↦ abs_nonneg _) hmajor

theorem continuous_chordPartialKernel_prod (ρ : ℝ) (M : ℕ) :
    Continuous (fun p : Sphere × Sphere ↦ chordPartialKernel ρ M p.1 p.2) := by
  unfold chordPartialKernel
  apply continuous_const.mul
  apply continuous_finset_sum
  intro m hm
  exact continuous_const.mul ((continuous_const.mul
    continuous_sphereInnerKernel_prod).pow m)

theorem continuous_chordRegularizedKernel_prod (ρ : ℝ) :
    Continuous (fun p : Sphere × Sphere ↦ chordRegularizedKernel ρ p.1 p.2) := by
  unfold chordRegularizedKernel
  exact continuous_const.mul (Real.continuous_sqrt.comp
    (continuous_const.sub (continuous_const.mul continuous_sphereInnerKernel_prod)))

/-- At an interior regularization parameter, pair energies of partial
binomial kernels converge to the regularized chordal pair energy. -/
theorem kernelPairEnergy_chordPartial_tendsto {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Filter.Tendsto (fun M ↦ kernelPairEnergy (chordPartialKernel ρ M) μ ν)
      Filter.atTop (_root_.nhds (kernelPairEnergy (chordRegularizedKernel ρ) μ ν)) := by
  simp_rw [kernelPairEnergy_eq_integral_prod μ ν
    (continuous_chordPartialKernel_prod ρ _),
    kernelPairEnergy_eq_integral_prod μ ν
      (continuous_chordRegularizedKernel_prod ρ)]
  apply MeasureTheory.tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun M ↦
      (continuous_chordPartialKernel_prod ρ M).aestronglyMeasurable
  · refine ⟨Real.sqrt 2 *
      (∑' m : ℕ, |Ring.choose (1 / 2 : ℝ) m * ρ ^ m|),
      Filter.Eventually.of_forall fun M ↦ ?_⟩
    exact Filter.Eventually.of_forall fun p ↦
      chordPartialKernel_norm_le hρ hρ1 M p.1 p.2
  · exact Filter.Eventually.of_forall fun p ↦
      chordPartialKernel_tendsto hρ hρ1 p.1 p.2

/-- Finite binomial kernel pair energies split into integer-power pair energies. -/
theorem kernelPairEnergy_chordPartial (ρ : ℝ) (M : ℕ)
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kernelPairEnergy (chordPartialKernel ρ M) μ ν =
      ∑ m ∈ Finset.range M,
        (Real.sqrt 2 * Ring.choose (1 / 2 : ℝ) m * (-ρ) ^ m) *
          kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m) μ ν := by
  have hrewrite (x y : Sphere) : chordPartialKernel ρ M x y =
      ∑ m ∈ Finset.range M,
        (Real.sqrt 2 * Ring.choose (1 / 2 : ℝ) m * (-ρ) ^ m) *
          sphereInnerKernel x y ^ m := by
    unfold chordPartialKernel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [mul_pow]
    ring
  rw [kernelPairEnergy_eq_integral_prod μ ν (continuous_chordPartialKernel_prod ρ M)]
  simp_rw [hrewrite]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [integral_const_mul,
      kernelPairEnergy_eq_integral_prod μ ν (continuous_sphereInnerKernel_prod.pow m)]
  · intro m hm
    exact (continuous_const.mul (continuous_sphereInnerKernel_prod.pow m)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Mixed and uniform power energies agree after scaling surface area to
the number of sample points. -/
theorem kernelPairEnergy_innerPow_mixed_eq_uniform {ι : Type} [Fintype ι]
    (X : ι → Sphere) (m : ℕ) :
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m)
      (empiricalSphereMeasure X) ((Fintype.card ι : ENNReal) • sigma) =
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m)
      ((Fintype.card ι : ENNReal) • sigma)
      ((Fintype.card ι : ENNReal) • sigma) := by
  rw [kernelPairEnergy_smul_right,
    kernelPairEnergy_innerPow_empirical_sigma,
    kernelPairEnergy_smul_left, kernelPairEnergy_smul_right,
    kernelPairEnergy_innerPow_sigma_sigma]
  simp only [ENNReal.toReal_natCast]

/-- Mixed and uniform partial-binomial energies agree term by term. -/
theorem kernelPairEnergy_chordPartial_mixed_eq_uniform {ι : Type} [Fintype ι]
    (X : ι → Sphere) (ρ : ℝ) (M : ℕ) :
    kernelPairEnergy (chordPartialKernel ρ M)
      (empiricalSphereMeasure X) ((Fintype.card ι : ENNReal) • sigma) =
    kernelPairEnergy (chordPartialKernel ρ M)
      ((Fintype.card ι : ENNReal) • sigma)
      ((Fintype.card ι : ENNReal) • sigma) := by
  haveI : IsFiniteMeasure ((Fintype.card ι : ENNReal) • sigma) :=
    IsFiniteMeasure.mk (by simp [sigma_apply_univ])
  rw [kernelPairEnergy_chordPartial, kernelPairEnergy_chordPartial]
  apply Finset.sum_congr rfl
  intro m hm
  rw [kernelPairEnergy_innerPow_mixed_eq_uniform X m]

/-- Mixed and uniform energies also agree for the regularized chordal kernel. -/
theorem kernelPairEnergy_chordRegularized_mixed_eq_uniform {ι : Type}
    [Fintype ι] (X : ι → Sphere) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    kernelPairEnergy (chordRegularizedKernel ρ)
      (empiricalSphereMeasure X) ((Fintype.card ι : ENNReal) • sigma) =
    kernelPairEnergy (chordRegularizedKernel ρ)
      ((Fintype.card ι : ENNReal) • sigma)
      ((Fintype.card ι : ENNReal) • sigma) := by
  haveI : IsFiniteMeasure ((Fintype.card ι : ENNReal) • sigma) :=
    IsFiniteMeasure.mk (by simp [sigma_apply_univ])
  have h₁ := kernelPairEnergy_chordPartial_tendsto hρ hρ1
    (empiricalSphereMeasure X) ((Fintype.card ι : ENNReal) • sigma)
  have h₂ := kernelPairEnergy_chordPartial_tendsto hρ hρ1
    ((Fintype.card ι : ENNReal) • sigma)
    ((Fintype.card ι : ENNReal) • sigma)
  have hseq : (fun M ↦ kernelPairEnergy (chordPartialKernel ρ M)
      (empiricalSphereMeasure X) ((Fintype.card ι : ENNReal) • sigma)) =
      (fun M ↦ kernelPairEnergy (chordPartialKernel ρ M)
        ((Fintype.card ι : ENNReal) • sigma)
        ((Fintype.card ι : ENNReal) • sigma)) := by
    funext M
    exact kernelPairEnergy_chordPartial_mixed_eq_uniform X ρ M
  rw [hseq] at h₁
  exact tendsto_nhds_unique h₁ h₂

/-- Every integer power moment of a finite configuration dominates the
uniform moment after matching total masses. -/
theorem kernelPairEnergy_innerPow_uniform_le_empirical {ι : Type}
    [Fintype ι] (X : ι → Sphere) (m : ℕ) :
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m)
      ((Fintype.card ι : ENNReal) • sigma)
      ((Fintype.card ι : ENNReal) • sigma) ≤
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m)
      (empiricalSphereMeasure X) (empiricalSphereMeasure X) := by
  let μ := empiricalSphereMeasure X
  let ν : Measure Sphere := (Fintype.card ι : ENNReal) • sigma
  haveI : IsFiniteMeasure ν := IsFiniteMeasure.mk (by simp [ν, sigma_apply_univ])
  have hcomm : kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m) ν μ =
      kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m) μ ν := by
    rw [kernelPairEnergy_innerPow, kernelPairEnergy_innerPow]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hmix := kernelPairEnergy_innerPow_mixed_eq_uniform X m
  change kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m) μ ν =
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m) ν ν at hmix
  have hpd := measurePositiveDefinite_innerPow m μ ν
    (measure_ne_top μ Set.univ) (measure_ne_top ν Set.univ)
  rw [hcomm, hmix] at hpd
  linarith

/-- Finite regularized distance deficit is the positive binomial sum
of power-kernel gaps. -/
theorem chordPartial_deficit_eq_sum {ι : Type} [Fintype ι]
    (X : ι → Sphere) (ρ : ℝ) (M : ℕ) :
    kernelPairEnergy (chordPartialKernel ρ M)
      ((Fintype.card ι : ENNReal) • sigma)
      ((Fintype.card ι : ENNReal) • sigma) -
    kernelPairEnergy (chordPartialKernel ρ M)
      (empiricalSphereMeasure X) (empiricalSphereMeasure X) =
    ∑ m ∈ Finset.range M,
      Real.sqrt 2 * chordBinomialCoeff m * ρ ^ m *
        (kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m)
          (empiricalSphereMeasure X) (empiricalSphereMeasure X) -
        kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m)
          ((Fintype.card ι : ENNReal) • sigma)
          ((Fintype.card ι : ENNReal) • sigma)) := by
  haveI : IsFiniteMeasure ((Fintype.card ι : ENNReal) • sigma) :=
    IsFiniteMeasure.mk (by simp [sigma_apply_univ])
  rw [kernelPairEnergy_chordPartial, kernelPairEnergy_chordPartial,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  unfold chordBinomialCoeff
  rw [neg_pow]
  ring

theorem kernelPairEnergy_innerPow_zero_uniform_eq_empirical {ι : Type}
    [Fintype ι] (X : ι → Sphere) :
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ 0)
      ((Fintype.card ι : ENNReal) • sigma)
      ((Fintype.card ι : ENNReal) • sigma) =
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ 0)
      (empiricalSphereMeasure X) (empiricalSphereMeasure X) := by
  rw [kernelPairEnergy_smul_left, kernelPairEnergy_smul_right,
    kernelPairEnergy_innerPow_sigma_sigma,
    kernelPairEnergy_empiricalSphereMeasure]
  simp [sphereHeightMoment]

/-- A finite block of high even powers survives in every interior
regularized distance deficit. -/
theorem chordPartial_deficit_even_block_lower {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (M : ℕ) (hM : 4 * n ≤ M) :
    Real.sqrt 2 * ((n : ℝ) / 2) *
      (∑ r ∈ Finset.Ico n (2 * n),
        chordBinomialCoeff (2 * r) * ρ ^ (2 * r)) ≤
    kernelPairEnergy (chordPartialKernel ρ M)
      ((n : ENNReal) • sigma) ((n : ENNReal) • sigma) -
    kernelPairEnergy (chordPartialKernel ρ M)
      (empiricalSphereMeasure X) (empiricalSphereMeasure X) := by
  have hformula := chordPartial_deficit_eq_sum X ρ M
  simp only [Fintype.card_fin] at hformula
  rw [hformula]
  let gap : ℕ → ℝ := fun m ↦
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m)
      (empiricalSphereMeasure X) (empiricalSphereMeasure X) -
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ m)
      ((n : ENNReal) • sigma) ((n : ENNReal) • sigma)
  have hgap (m : ℕ) : 0 ≤ gap m := by
    simpa only [Fintype.card_fin] using
      (sub_nonneg.mpr (kernelPairEnergy_innerPow_uniform_le_empirical X m))
  have hterm (m : ℕ) :
      0 ≤ Real.sqrt 2 * chordBinomialCoeff m * ρ ^ m * gap m := by
    by_cases hm : m = 0
    · subst m
      have hz := kernelPairEnergy_innerPow_zero_uniform_eq_empirical X
      simp only [Fintype.card_fin] at hz
      dsimp [gap]
      rw [← hz]
      simp
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (chordBinomialCoeff_pos m hm1).le) (pow_nonneg hρ _)) (hgap m)
  let s := (Finset.Ico n (2 * n)).image (fun r : ℕ ↦ 2 * r)
  have hsubset : s ⊆ Finset.range M := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨r, hr, rfl⟩
    simp only [Finset.mem_Ico] at hr
    simp only [Finset.mem_range]
    omega
  have hsum : (∑ m ∈ s,
      Real.sqrt 2 * chordBinomialCoeff m * ρ ^ m * gap m) ≤
      ∑ m ∈ Finset.range M,
        Real.sqrt 2 * chordBinomialCoeff m * ρ ^ m * gap m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun m hm _ ↦ hterm m)
  have hinj : Set.InjOn (fun r : ℕ ↦ 2 * r) (Finset.Ico n (2 * n)) := by
    intro a ha b hb hab
    change 2 * a = 2 * b at hab
    omega
  rw [Finset.sum_image hinj] at hsum
  have hblock :
      Real.sqrt 2 * ((n : ℝ) / 2) *
        (∑ r ∈ Finset.Ico n (2 * n),
          chordBinomialCoeff (2 * r) * ρ ^ (2 * r)) ≤
      ∑ r ∈ Finset.Ico n (2 * n),
        Real.sqrt 2 * chordBinomialCoeff (2 * r) * ρ ^ (2 * r) * gap (2 * r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hrn : n ≤ r := (Finset.mem_Ico.mp hr).1
    have hlarge := even_power_energy_gap_ge_half_card hn X r hrn
    change (n : ℝ) / 2 ≤ gap (2 * r) at hlarge
    have hcoeff : 0 ≤ Real.sqrt 2 * chordBinomialCoeff (2 * r) * ρ ^ (2 * r) := by
      have hr1 : 1 ≤ 2 * r := by omega
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (chordBinomialCoeff_pos (2 * r) hr1).le) (pow_nonneg hρ _)
    nlinarith [mul_le_mul_of_nonneg_left hlarge hcoeff]
  exact hblock.trans hsum

/-- The regularized chordal deficit retains the same high even block. -/
theorem chordRegularized_deficit_even_block_lower {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Real.sqrt 2 * ((n : ℝ) / 2) *
      (∑ r ∈ Finset.Ico n (2 * n),
        chordBinomialCoeff (2 * r) * ρ ^ (2 * r)) ≤
    kernelPairEnergy (chordRegularizedKernel ρ)
      ((n : ENNReal) • sigma) ((n : ENNReal) • sigma) -
    kernelPairEnergy (chordRegularizedKernel ρ)
      (empiricalSphereMeasure X) (empiricalSphereMeasure X) := by
  haveI : IsFiniteMeasure ((n : ENNReal) • sigma) :=
    IsFiniteMeasure.mk (by simp [sigma_apply_univ])
  have hlim := (kernelPairEnergy_chordPartial_tendsto hρ hρ1
    ((n : ENNReal) • sigma) ((n : ENNReal) • sigma)).sub
    (kernelPairEnergy_chordPartial_tendsto hρ hρ1
      (empiricalSphereMeasure X) (empiricalSphereMeasure X))
  apply ge_of_tendsto hlim
  filter_upwards [Filter.eventually_ge_atTop (4 * n)] with M hM
  exact chordPartial_deficit_even_block_lower hn X hρ M hM

private noncomputable def beckRho (k : ℕ) : ℝ := (k : ℝ) / (k + 1)

private theorem beckRho_nonneg (k : ℕ) : 0 ≤ beckRho k := by
  unfold beckRho
  positivity

private theorem beckRho_lt_one (k : ℕ) : beckRho k < 1 := by
  unfold beckRho
  apply (div_lt_iff₀ (by positivity : 0 < (k : ℝ) + 1)).2
  linarith

private theorem beckRho_tendsto_one :
    Filter.Tendsto beckRho Filter.atTop (_root_.nhds (1 : ℝ)) := by
  have h := RCLike.tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) 0 1 1 (d := 1) one_ne_zero
  simpa [beckRho, add_comm, mul_comm] using h

private theorem chordRegularizedKernel_norm_le_two {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (x y : Sphere) :
    ‖chordRegularizedKernel ρ x y‖ ≤ 2 := by
  have hinner := sphereInnerKernel_abs_le_one x y
  have hρinner : |ρ * sphereInnerKernel x y| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hρ]
    exact (mul_le_mul_of_nonneg_left hinner hρ).trans (by simpa using hρ1)
  have hbase : 0 ≤ 1 - ρ * sphereInnerKernel x y := by
    have := (abs_le.mp hρinner).2
    linarith
  have hbase2 : 1 - ρ * sphereInnerKernel x y ≤ 2 := by
    have := (abs_le.mp hρinner).1
    linarith
  have hsqrt : 0 ≤ Real.sqrt (1 - ρ * sphereInnerKernel x y) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt hbase
  have hsqrt2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold chordRegularizedKernel
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hsqrt)]
  nlinarith [mul_nonneg (Real.sqrt_nonneg 2) hsqrt]

private theorem continuous_chordRegularizedKernel_rho (x y : Sphere) :
    Continuous (fun ρ : ℝ ↦ chordRegularizedKernel ρ x y) := by
  unfold chordRegularizedKernel
  exact continuous_const.mul (Real.continuous_sqrt.comp
    (continuous_const.sub (continuous_id.mul continuous_const)))

/-- Pair energies of regularized kernels converge as `ρ ↑ 1`. -/
theorem kernelPairEnergy_chordRegularized_tendsto_one
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Filter.Tendsto (fun k ↦ kernelPairEnergy (chordRegularizedKernel (beckRho k)) μ ν)
      Filter.atTop (_root_.nhds (kernelPairEnergy (chordRegularizedKernel 1) μ ν)) := by
  simp_rw [kernelPairEnergy_eq_integral_prod μ ν
    (continuous_chordRegularizedKernel_prod _)]
  apply MeasureTheory.tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun k ↦
      (continuous_chordRegularizedKernel_prod (beckRho k)).aestronglyMeasurable
  · refine ⟨2, Filter.Eventually.of_forall fun k ↦ ?_⟩
    exact Filter.Eventually.of_forall fun p ↦
      chordRegularizedKernel_norm_le_two (beckRho_nonneg k)
        (beckRho_lt_one k).le p.1 p.2
  · exact Filter.Eventually.of_forall fun p ↦
      ((continuous_chordRegularizedKernel_rho p.1 p.2).tendsto 1).comp
        beckRho_tendsto_one

/-- At the endpoint the regularized kernel is chordal distance. -/
theorem chordRegularizedKernel_one (x y : Sphere) :
    chordRegularizedKernel 1 x y = dist x y := by
  have hinner := sphereInnerKernel_abs_le_one x y
  have hbase : 0 ≤ 1 - sphereInnerKernel x y := by
    have := (abs_le.mp hinner).2
    linarith
  have hsq := sphere_dist_sq_coordinates x y
  change dist x y ^ 2 = 2 - 2 * sphereInnerKernel x y at hsq
  have hleft : 0 ≤ chordRegularizedKernel 1 x y := by
    unfold chordRegularizedKernel
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hleftsq : chordRegularizedKernel 1 x y ^ 2 =
      2 - 2 * sphereInnerKernel x y := by
    unfold chordRegularizedKernel
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sq_sqrt]
    · ring
    · simpa using hbase
  nlinarith [show 0 ≤ dist x y from dist_nonneg]

/-- Letting the interior regularization tend to one yields a lower
bound for the actual chordal distance deficit. -/
theorem distance_deficit_even_block_lower {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) :
    Real.sqrt 2 * ((n : ℝ) / 2) *
      (∑ r ∈ Finset.Ico n (2 * n), chordBinomialCoeff (2 * r)) ≤
    kernelPairEnergy (fun x y : Sphere ↦ dist x y)
      ((n : ENNReal) • sigma) ((n : ENNReal) • sigma) -
    kernelPairEnergy (fun x y : Sphere ↦ dist x y)
      (empiricalSphereMeasure X) (empiricalSphereMeasure X) := by
  haveI : IsFiniteMeasure ((n : ENNReal) • sigma) :=
    IsFiniteMeasure.mk (by simp [sigma_apply_univ])
  have hcont : Continuous (fun ρ : ℝ ↦
      Real.sqrt 2 * ((n : ℝ) / 2) *
        (∑ r ∈ Finset.Ico n (2 * n),
          chordBinomialCoeff (2 * r) * ρ ^ (2 * r))) := by
    apply continuous_const.mul
    apply continuous_finset_sum
    intro r hr
    exact continuous_const.mul (continuous_id.pow _)
  have hL := (hcont.tendsto 1).comp beckRho_tendsto_one
  have hR := (kernelPairEnergy_chordRegularized_tendsto_one
    ((n : ENNReal) • sigma) ((n : ENNReal) • sigma)).sub
    (kernelPairEnergy_chordRegularized_tendsto_one
      (empiricalSphereMeasure X) (empiricalSphereMeasure X))
  have hbound := le_of_tendsto_of_tendsto' hL hR (fun k ↦
    chordRegularized_deficit_even_block_lower hn X
      (beckRho_nonneg k) (beckRho_lt_one k))
  simp only [one_pow, mul_one] at hbound
  simpa only [kernelPairEnergy, chordRegularizedKernel_one] using hbound

/-- The uniform distance pair energy is the manuscript's constant. -/
theorem kernelPairEnergy_distance_sigma_sigma :
    kernelPairEnergy (fun x y : Sphere ↦ dist x y) sigma sigma =
      continuousEnergy 1 := by
  unfold kernelPairEnergy
  have hpot := hasConstantSpherePotential (α := 1) (by norm_num)
  have hpoint (x : Sphere) :
      (∫ y : Sphere, dist x y ∂sigma) = continuousEnergy 1 := by
    simpa [HasConstantSpherePotential, continuousEnergy, Real.rpow_one] using hpot x
  simp_rw [hpoint]
  simp

/-- The empirical distance pair energy is exactly the ordered-pair energy. -/
theorem kernelPairEnergy_distance_empirical {ι : Type} [Fintype ι]
    (X : ι → Sphere) :
    kernelPairEnergy (fun x y : Sphere ↦ dist x y)
      (empiricalSphereMeasure X) (empiricalSphereMeasure X) = energy X 1 := by
  rw [kernelPairEnergy_empiricalSphereMeasure]
  simp [energy]

/-- The chordal distance deficit has a concrete positive finite-block lower bound. -/
theorem continuousEnergy_distance_deficit_even_block_lower {n : ℕ}
    (hn : 0 < n) (X : Fin n → Sphere) :
    Real.sqrt 2 * ((n : ℝ) / 2) *
      (∑ r ∈ Finset.Ico n (2 * n), chordBinomialCoeff (2 * r)) ≤
    (n : ℝ) ^ 2 * continuousEnergy 1 - energy X 1 := by
  have h := distance_deficit_even_block_lower hn X
  rw [kernelPairEnergy_smul_left, kernelPairEnergy_smul_right,
    kernelPairEnergy_distance_sigma_sigma,
    kernelPairEnergy_distance_empirical] at h
  simp only [ENNReal.toReal_natCast] at h
  convert h using 1; ring

/-- A concrete square-discrepancy lower bound in elementary square-root form. -/
theorem capDiscrepancySq_lower_sqrt {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) :
    1 / (256 * (n : ℝ) * Real.sqrt n) ≤ capDiscrepancySq X := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnreal
  have hsqrt2 : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hblock := chordBinomialCoeff_even_block_lower n hn
  have henergy := continuousEnergy_distance_deficit_even_block_lower hn X
  have hfactor : 0 ≤ Real.sqrt 2 * ((n : ℝ) / 2) := by positivity
  have hcombined := (mul_le_mul_of_nonneg_left hblock hfactor).trans henergy
  have hstol := stolarsky_identity n hn X
  have hn2 : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hnreal.ne'
  have hgap : (n : ℝ) ^ 2 * continuousEnergy 1 - energy X 1 =
      4 * (n : ℝ) ^ 2 * capDiscrepancySq X := by
    field_simp [hn2] at hstol
    nlinarith [hstol]
  rw [hgap] at hcombined
  have hmul : 4 * (n : ℝ) ^ 2 *
      (1 / (256 * (n : ℝ) * Real.sqrt n)) ≤
      Real.sqrt 2 * ((n : ℝ) / 2) *
        (1 / (32 * Real.sqrt n)) := by
    calc
      _ = (n : ℝ) / (64 * Real.sqrt n) := by
        field_simp [hnreal.ne', hsqrt.ne']
        ring
      _ ≤ Real.sqrt 2 * (n : ℝ) / (64 * Real.sqrt n) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt2) hnreal.le]
      _ = _ := by ring
  have hmain := hmul.trans hcombined
  nlinarith [sq_pos_of_pos hnreal]

/-- Beck's exponent follows from the explicit square-discrepancy bound. -/
theorem capDiscrepancy_lower_rpow {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) :
    (1 / 16 : ℝ) * (n : ℝ) ^ (-(3 : ℝ) / 4) ≤ capDiscrepancy X := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : ((n : ℝ) ^ (-(3 : ℝ) / 4)) ^ 2 =
      1 / ((n : ℝ) * Real.sqrt n) := by
    calc
      _ = (n : ℝ) ^ ((-(3 : ℝ) / 4) * 2) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ (-(3 : ℝ) / 4)) 2]
        exact (Real.rpow_mul hnreal.le (-(3 : ℝ) / 4) (2 : ℝ)).symm
      _ = (n : ℝ) ^ (-(1 + (1 : ℝ) / 2)) := by congr 1; ring
      _ = ((n : ℝ) ^ (1 + (1 : ℝ) / 2))⁻¹ := by
        rw [Real.rpow_neg hnreal.le]
      _ = ((n : ℝ) * Real.sqrt n)⁻¹ := by
        rw [Real.rpow_add hnreal]
        simp [Real.sqrt_eq_rpow]
      _ = _ := by ring
  have hsq : ((1 / 16 : ℝ) * (n : ℝ) ^ (-(3 : ℝ) / 4)) ^ 2 =
      1 / (256 * (n : ℝ) * Real.sqrt n) := by
    rw [mul_pow, hpow]
    ring
  have hlow := capDiscrepancySq_lower_sqrt hn X
  rw [← hsq] at hlow
  exact (Real.le_sqrt_of_sq_le hlow)

/-- A concrete Beck constant for the actual unnormalized-`dt` cap discrepancy.
The proof works even when some point labels coincide. -/
theorem beckLowerBound : BeckLowerBound := by
  refine ⟨1 / 16, by norm_num, ?_⟩
  intro n hn X _
  exact capDiscrepancy_lower_rpow (by omega) X

/-- Above degree `n`, the even power-moment gap is at least `1/(2n)`. -/
theorem even_projection_moment_gap_ge {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) (r : ℕ) (hr : n ≤ r) :
    (∑ i : Fin n, ∑ j : Fin n,
      (@Inner.inner ℝ Ambient _ (X i : Ambient) (X j : Ambient)) ^ (2 * r)) /
        (n : ℝ) ^ 2 - 1 / ((2 * r + 1 : ℕ) : ℝ) ≥
      1 / (2 * (n : ℝ)) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hrreal : (n : ℝ) ≤ r := by exact_mod_cast hr
  have hsum := finite_even_projection_energy_ge_card X r
  simp only [Fintype.card_fin] at hsum
  have hden : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) := by positivity
  push_cast at hden ⊢
  have hden' : (0 : ℝ) < (2 * (r : ℝ) + 1) := by linarith
  have hn2 : (n : ℝ) ≠ 0 := ne_of_gt hnreal
  have hr2 : 2 * (r : ℝ) + 1 ≠ 0 := ne_of_gt hden'
  have hSdiv : (n : ℝ) / (n : ℝ) ^ 2 ≤
      (∑ i : Fin n, ∑ j : Fin n,
        (@Inner.inner ℝ Ambient _ (X i : Ambient) (X j : Ambient)) ^ (2 * r)) /
        (n : ℝ) ^ 2 :=
    (div_le_div_iff_of_pos_right (by positivity : 0 < (n : ℝ) ^ 2)).2 hsum
  have hfrac : 1 / (2 * (r : ℝ) + 1) ≤ 1 / (2 * (n : ℝ)) := by
    apply (div_le_div_iff₀ hden' (by positivity : 0 < 2 * (n : ℝ))).2
    nlinarith
  have hnorm : (n : ℝ) / (n : ℝ) ^ 2 = 1 / (n : ℝ) := by
    field_simp
    ring
  rw [hnorm] at hSdiv
  have hhalf : 1 / (n : ℝ) = 2 * (1 / (2 * (n : ℝ))) := by
    field_simp
  linarith

end BEMOC.Definitive
