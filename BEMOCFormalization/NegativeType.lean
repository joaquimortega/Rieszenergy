import BEMOCFormalization.ContinuousEnergy

open scoped BigOperators
open MeasureTheory
namespace BEMOC.Definitive

/-- Pair energy of two positive measures for a real kernel. -/
noncomputable def kernelPairEnergy (K : Sphere → Sphere → ℝ)
    (μ ν : Measure Sphere) : ℝ :=
  ∫ x, ∫ y, K x y ∂ν ∂μ

/-- The exact positive-measure formulation of conditional negative
definiteness.  It is the expansion of the signed-measure inequality for
`η = μ - ν`, avoiding any dependence on a particular signed-measure API. -/
def MeasureConditionallyNegative (K : Sphere → Sphere → ℝ) : Prop :=
  ∀ (μ ν : Measure Sphere), μ Set.univ ≠ ⊤ → ν Set.univ ≠ ⊤ →
    μ Set.univ = ν Set.univ →
    kernelPairEnergy K μ μ + kernelPairEnergy K ν ν ≤
      kernelPairEnergy K μ ν + kernelPairEnergy K ν μ

/-- Conditional negative definiteness of the chordal distance-power kernel,
stated in the measure-theoretic form used in the paper. -/
def DistancePowerMeasureCND (α : ℝ) : Prop :=
  MeasureConditionallyNegative (fun x y ↦ dist x y ^ α)

theorem continuous_sphereCoordinate (i : Fin 3) :
    Continuous (fun x : Sphere ↦ (x : Ambient) i) := by
  exact (continuous_apply i).comp continuous_subtype_val

theorem sphere_dist_sq_coordinates (x y : Sphere) :
    dist x y ^ 2 = 2 - 2 * ∑ i : Fin 3, (x : Ambient) i * (y : Ambient) i := by
  change dist (x : Ambient) (y : Ambient) ^ 2 = _
  rw [EuclideanSpace.dist_eq]
  have hnonneg : 0 ≤ ∑ i : Fin 3,
      dist ((x : Ambient) i) ((y : Ambient) i) ^ 2 := by positivity
  rw [Real.sq_sqrt hnonneg]
  have hx := x.property
  have hy := y.property
  change (x : Ambient) ∈ Metric.sphere (0 : Ambient) 1 at hx
  change (y : Ambient) ∈ Metric.sphere (0 : Ambient) 1 at hy
  rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at hx hy
  change (∑ i, (x : Ambient) i ^ 2) = 1 ^ 2 at hx
  change (∑ i, (y : Ambient) i ^ 2) = 1 ^ 2 at hy
  simp only [Real.dist_eq, sq_abs]
  calc
    ∑ i : Fin 3, ((x : Ambient) i - (y : Ambient) i) ^ 2 =
        ∑ i : Fin 3, ((x : Ambient) i ^ 2 + (y : Ambient) i ^ 2 -
          2 * (x : Ambient) i * (y : Ambient) i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hx, hy]
      ring_nf
      rw [Finset.sum_mul]

/-- Positive definiteness in the same finite-positive-measure formulation as
`MeasureConditionallyNegative`. -/
def MeasurePositiveDefinite (K : Sphere → Sphere → ℝ) : Prop :=
  ∀ (μ ν : Measure Sphere), μ Set.univ ≠ ⊤ → ν Set.univ ≠ ⊤ →
    kernelPairEnergy K μ ν + kernelPairEnergy K ν μ ≤
      kernelPairEnergy K μ μ + kernelPairEnergy K ν ν

def sphereInnerKernel (x y : Sphere) : ℝ :=
  ∑ i : Fin 3, (x : Ambient) i * (y : Ambient) i

def sphereTensorFeature (n : ℕ) (p : Fin n → Fin 3) (x : Sphere) : ℝ :=
  ∏ k : Fin n, (x : Ambient) (p k)

theorem continuous_sphereTensorFeature (n : ℕ) (p : Fin n → Fin 3) :
    Continuous (sphereTensorFeature n p) := by
  unfold sphereTensorFeature
  exact continuous_finset_prod Finset.univ fun k hk ↦ continuous_sphereCoordinate (p k)

theorem integrable_sphereTensorFeature (μ : Measure Sphere) [IsFiniteMeasure μ]
    (n : ℕ) (p : Fin n → Fin 3) : Integrable (sphereTensorFeature n p) μ :=
  (continuous_sphereTensorFeature n p).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def sphereTensorMoment (μ : Measure Sphere)
    (n : ℕ) (p : Fin n → Fin 3) : ℝ :=
  ∫ x : Sphere, sphereTensorFeature n p x ∂μ

theorem sphereInnerKernel_pow_eq_feature_sum (n : ℕ) (x y : Sphere) :
    sphereInnerKernel x y ^ n =
      ∑ p : Fin n → Fin 3, sphereTensorFeature n p x * sphereTensorFeature n p y := by
  unfold sphereInnerKernel sphereTensorFeature
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.prod_mul_distrib]

noncomputable def innerExpCoeff (c : ℝ) (n : ℕ) : ℝ :=
  c ^ n / (Nat.factorial n : ℝ)

noncomputable def innerExpPartialKernel (c : ℝ) (N : ℕ) (x y : Sphere) : ℝ :=
  ∑ n ∈ Finset.range N, innerExpCoeff c n * sphereInnerKernel x y ^ n

theorem innerExpCoeff_nonneg {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ innerExpCoeff c n := by
  unfold innerExpCoeff
  positivity

theorem kernelPairEnergy_innerExpPartialKernel
    (c : ℝ) (N : ℕ) (μ ν : Measure Sphere)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kernelPairEnergy (innerExpPartialKernel c N) μ ν =
      ∑ n ∈ Finset.range N, innerExpCoeff c n *
        ∑ p : Fin n → Fin 3, sphereTensorMoment μ n p * sphereTensorMoment ν n p := by
  unfold kernelPairEnergy innerExpPartialKernel
  simp_rw [sphereInnerKernel_pow_eq_feature_sum]
  have hfeatureμ (n : ℕ) (p : Fin n → Fin 3) := integrable_sphereTensorFeature μ n p
  have hfeatureν (n : ℕ) (p : Fin n → Fin 3) := integrable_sphereTensorFeature ν n p
  have hinner (x : Sphere) :
      (∫ y : Sphere, ∑ n ∈ Finset.range N, innerExpCoeff c n *
        ∑ p : Fin n → Fin 3,
          sphereTensorFeature n p x * sphereTensorFeature n p y ∂ν) =
      ∑ n ∈ Finset.range N, innerExpCoeff c n *
        ∑ p : Fin n → Fin 3, sphereTensorFeature n p x *
          (∫ y : Sphere, sphereTensorFeature n p y ∂ν) := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul, integral_finset_sum]
      · simp_rw [integral_const_mul]
      · intro p hp
        exact (hfeatureν n p).const_mul _
    · intro n hn
      apply Integrable.const_mul
      exact integrable_finset_sum Finset.univ fun p _ ↦ (hfeatureν n p).const_mul _
  simp_rw [hinner]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [integral_const_mul, integral_finset_sum]
    · simp_rw [integral_mul_const]
      simp only [sphereTensorMoment]
    · intro p hp
      exact (hfeatureμ n p).mul_const _
  · intro n hn
    apply Integrable.const_mul
    exact integrable_finset_sum Finset.univ fun p _ ↦ (hfeatureμ n p).mul_const _

theorem measurePositiveDefinite_innerExpPartialKernel {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    MeasurePositiveDefinite (innerExpPartialKernel c N) := by
  intro μ ν hμ hν
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  rw [kernelPairEnergy_innerExpPartialKernel, kernelPairEnergy_innerExpPartialKernel,
    kernelPairEnergy_innerExpPartialKernel, kernelPairEnergy_innerExpPartialKernel]
  have hs : 0 ≤ ∑ n ∈ Finset.range N, innerExpCoeff c n *
      ∑ p : Fin n → Fin 3,
        (sphereTensorMoment μ n p - sphereTensorMoment ν n p) ^ 2 := by
    exact Finset.sum_nonneg fun n _ ↦ mul_nonneg (innerExpCoeff_nonneg hc n)
      (Finset.sum_nonneg fun p _ ↦ sq_nonneg _)
  have hid (n : ℕ) :
      (∑ p : Fin n → Fin 3,
        (sphereTensorMoment μ n p - sphereTensorMoment ν n p) ^ 2) =
        (∑ p : Fin n → Fin 3, sphereTensorMoment μ n p * sphereTensorMoment μ n p) +
        (∑ p : Fin n → Fin 3, sphereTensorMoment ν n p * sphereTensorMoment ν n p) -
        (∑ p : Fin n → Fin 3, sphereTensorMoment μ n p * sphereTensorMoment ν n p) -
        (∑ p : Fin n → Fin 3, sphereTensorMoment ν n p * sphereTensorMoment μ n p) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  simp_rw [hid] at hs
  simp_rw [mul_sub, mul_add] at hs
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib] at hs
  nlinarith

theorem sphereInnerKernel_abs_le_one (x y : Sphere) : |sphereInnerKernel x y| ≤ 1 := by
  have hinner := abs_real_inner_le_norm (x : Ambient) (y : Ambient)
  have hxnorm : ‖(x : Ambient)‖ = 1 := norm_eq_of_mem_sphere x
  have hynorm : ‖(y : Ambient)‖ = 1 := norm_eq_of_mem_sphere y
  rw [hxnorm, hynorm, mul_one] at hinner
  simpa [sphereInnerKernel, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, mul_comm] using hinner

theorem innerExpPartialKernel_norm_le_exp {c : ℝ} (hc : 0 ≤ c)
    (N : ℕ) (x y : Sphere) :
    ‖innerExpPartialKernel c N x y‖ ≤ Real.exp c := by
  have hcoeffSum : HasSum (innerExpCoeff c) (Real.exp c) := by
    simpa [innerExpCoeff, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ℝ c)
  rw [Real.norm_eq_abs, innerExpPartialKernel]
  calc
    |∑ n ∈ Finset.range N, innerExpCoeff c n * sphereInnerKernel x y ^ n| ≤
        ∑ n ∈ Finset.range N,
          |innerExpCoeff c n * sphereInnerKernel x y ^ n| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, innerExpCoeff c n := by
      gcongr with n hn
      rw [abs_mul, abs_of_nonneg (innerExpCoeff_nonneg hc n), abs_pow]
      exact mul_le_of_le_one_right (innerExpCoeff_nonneg hc n)
        (pow_le_one₀ (abs_nonneg _) (sphereInnerKernel_abs_le_one x y))
    _ ≤ Real.exp c := sum_le_hasSum (Finset.range N)
      (fun n hn ↦ innerExpCoeff_nonneg hc n) hcoeffSum

theorem innerExpPartialKernel_tendsto (c : ℝ) (x y : Sphere) :
    Filter.Tendsto (fun N ↦ innerExpPartialKernel c N x y) Filter.atTop
      (_root_.nhds (Real.exp (c * sphereInnerKernel x y))) := by
  have hsum := (NormedSpace.expSeries_div_hasSum_exp ℝ
    (c * sphereInnerKernel x y)).tendsto_sum_nat
  simpa [innerExpPartialKernel, innerExpCoeff, mul_pow, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm, Real.exp_eq_exp_ℝ] using hsum

noncomputable def innerExpKernel (c : ℝ) (x y : Sphere) : ℝ :=
  Real.exp (c * sphereInnerKernel x y)

theorem continuous_sphereInnerKernel_prod :
    Continuous (fun p : Sphere × Sphere ↦ sphereInnerKernel p.1 p.2) := by
  unfold sphereInnerKernel
  apply continuous_finset_sum
  intro i hi
  exact ((continuous_sphereCoordinate i).comp continuous_fst).mul
    ((continuous_sphereCoordinate i).comp continuous_snd)

theorem continuous_innerExpPartialKernel_prod (c : ℝ) (N : ℕ) :
    Continuous (fun p : Sphere × Sphere ↦ innerExpPartialKernel c N p.1 p.2) := by
  unfold innerExpPartialKernel
  apply continuous_finset_sum
  intro n hn
  exact continuous_const.mul (continuous_sphereInnerKernel_prod.pow n)

theorem continuous_innerExpKernel_prod (c : ℝ) :
    Continuous (fun p : Sphere × Sphere ↦ innerExpKernel c p.1 p.2) := by
  unfold innerExpKernel
  exact Real.continuous_exp.comp (continuous_const.mul continuous_sphereInnerKernel_prod)

theorem kernelPairEnergy_eq_integral_prod {K : Sphere → Sphere → ℝ}
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hK : Continuous (fun p : Sphere × Sphere ↦ K p.1 p.2)) :
    kernelPairEnergy K μ ν = ∫ p : Sphere × Sphere, K p.1 p.2 ∂μ.prod ν := by
  symm
  apply MeasureTheory.integral_prod
  exact hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem kernelPairEnergy_innerExpPartialKernel_tendsto {c : ℝ} (hc : 0 ≤ c)
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Filter.Tendsto (fun N ↦ kernelPairEnergy (innerExpPartialKernel c N) μ ν)
      Filter.atTop (_root_.nhds (kernelPairEnergy (innerExpKernel c) μ ν)) := by
  simp_rw [kernelPairEnergy_eq_integral_prod μ ν
    (continuous_innerExpPartialKernel_prod c _),
    kernelPairEnergy_eq_integral_prod μ ν (continuous_innerExpKernel_prod c)]
  apply MeasureTheory.tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun N ↦
      (continuous_innerExpPartialKernel_prod c N).aestronglyMeasurable
  · refine ⟨Real.exp c, Filter.Eventually.of_forall fun N ↦ ?_⟩
    exact Filter.Eventually.of_forall fun p ↦ innerExpPartialKernel_norm_le_exp hc N p.1 p.2
  · exact Filter.Eventually.of_forall fun p ↦ by
      simpa [innerExpKernel] using innerExpPartialKernel_tendsto c p.1 p.2

theorem measurePositiveDefinite_innerExpKernel {c : ℝ} (hc : 0 ≤ c) :
    MeasurePositiveDefinite (innerExpKernel c) := by
  intro μ ν hμ hν
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  have hμν := kernelPairEnergy_innerExpPartialKernel_tendsto hc μ ν
  have hνμ := kernelPairEnergy_innerExpPartialKernel_tendsto hc ν μ
  have hμμ := kernelPairEnergy_innerExpPartialKernel_tendsto hc μ μ
  have hνν := kernelPairEnergy_innerExpPartialKernel_tendsto hc ν ν
  have hlim := hμν.add hνμ
  have hrhs := hμμ.add hνν
  have hd :
      (kernelPairEnergy (innerExpKernel c) μ ν +
          kernelPairEnergy (innerExpKernel c) ν μ) -
        (kernelPairEnergy (innerExpKernel c) μ μ +
          kernelPairEnergy (innerExpKernel c) ν ν) ≤ 0 := by
    apply le_of_tendsto (hlim.sub hrhs)
    exact Filter.Eventually.of_forall fun N ↦ sub_nonpos.mpr
      (measurePositiveDefinite_innerExpPartialKernel hc N μ ν hμ hν)
  linarith

noncomputable def gaussianDistanceKernel (t : ℝ) (x y : Sphere) : ℝ :=
  Real.exp (-t * dist x y ^ 2)

theorem gaussianDistanceKernel_eq_innerExpKernel (t : ℝ) (x y : Sphere) :
    gaussianDistanceKernel t x y =
      Real.exp (-2 * t) * innerExpKernel (2 * t) x y := by
  unfold gaussianDistanceKernel
  rw [sphere_dist_sq_coordinates]
  unfold innerExpKernel sphereInnerKernel
  rw [← Real.exp_add]
  congr 1
  ring

theorem kernelPairEnergy_const_mul (a : ℝ) (K : Sphere → Sphere → ℝ)
    (μ ν : Measure Sphere) :
    kernelPairEnergy (fun x y ↦ a * K x y) μ ν = a * kernelPairEnergy K μ ν := by
  unfold kernelPairEnergy
  simp_rw [integral_const_mul]

theorem measurePositiveDefinite_const_mul {a : ℝ} (ha : 0 ≤ a)
    {K : Sphere → Sphere → ℝ} (hK : MeasurePositiveDefinite K) :
    MeasurePositiveDefinite (fun x y ↦ a * K x y) := by
  intro μ ν hμ hν
  simp_rw [kernelPairEnergy_const_mul]
  nlinarith [hK μ ν hμ hν]

theorem measurePositiveDefinite_congr {K L : Sphere → Sphere → ℝ}
    (h : ∀ x y, K x y = L x y) (hK : MeasurePositiveDefinite K) :
    MeasurePositiveDefinite L := by
  have hfun : L = K := by
    funext x y
    exact (h x y).symm
  simpa [hfun] using hK

theorem measurePositiveDefinite_gaussianDistanceKernel {t : ℝ} (ht : 0 ≤ t) :
    MeasurePositiveDefinite (gaussianDistanceKernel t) := by
  apply measurePositiveDefinite_congr fun x y ↦
    (gaussianDistanceKernel_eq_innerExpKernel t x y).symm
  exact measurePositiveDefinite_const_mul (Real.exp_pos _).le
    (measurePositiveDefinite_innerExpKernel (by positivity : 0 ≤ 2 * t))

theorem continuous_gaussianDistanceKernel_prod (t : ℝ) :
    Continuous (fun p : Sphere × Sphere ↦ gaussianDistanceKernel t p.1 p.2) := by
  unfold gaussianDistanceKernel
  exact Real.continuous_exp.comp
    (continuous_const.mul
      ((continuous_dist.comp (continuous_fst.prodMk continuous_snd)).pow 2))

theorem kernelPairEnergy_one (μ ν : Measure Sphere)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kernelPairEnergy (fun _ _ : Sphere ↦ (1 : ℝ)) μ ν =
      μ.real Set.univ * ν.real Set.univ := by
  unfold kernelPairEnergy
  simp

theorem kernelPairEnergy_sub_continuous {K L : Sphere → Sphere → ℝ}
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hK : Continuous (fun p : Sphere × Sphere ↦ K p.1 p.2))
    (hL : Continuous (fun p : Sphere × Sphere ↦ L p.1 p.2)) :
    kernelPairEnergy (fun x y ↦ K x y - L x y) μ ν =
      kernelPairEnergy K μ ν - kernelPairEnergy L μ ν := by
  rw [kernelPairEnergy_eq_integral_prod μ ν (hK.sub hL),
    kernelPairEnergy_eq_integral_prod μ ν hK,
    kernelPairEnergy_eq_integral_prod μ ν hL]
  exact MeasureTheory.integral_sub
    (hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem measureConditionallyNegative_one_sub_gaussian {t : ℝ} (ht : 0 ≤ t) :
    MeasureConditionallyNegative (fun x y ↦ 1 - gaussianDistanceKernel t x y) := by
  intro μ ν hμ hν hmass
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  have hreal : μ.real Set.univ = ν.real Set.univ := by
    simpa [Measure.real_def] using congrArg ENNReal.toReal hmass
  have hpd := measurePositiveDefinite_gaussianDistanceKernel ht μ ν hμ hν
  have hsub (ρ τ : Measure Sphere) [IsFiniteMeasure ρ] [IsFiniteMeasure τ] :=
    kernelPairEnergy_sub_continuous (K := fun _ _ ↦ (1 : ℝ))
      (L := gaussianDistanceKernel t) ρ τ
      (show Continuous (fun _ : Sphere × Sphere ↦ (1 : ℝ)) from continuous_const)
      (continuous_gaussianDistanceKernel_prod t)
  rw [hsub μ μ, hsub ν ν, hsub μ ν, hsub ν μ,
    kernelPairEnergy_one, kernelPairEnergy_one,
    kernelPairEnergy_one, kernelPairEnergy_one]
  rw [hreal]
  linarith

theorem measureConditionallyNegative_const_mul {a : ℝ} (ha : 0 ≤ a)
    {K : Sphere → Sphere → ℝ} (hK : MeasureConditionallyNegative K) :
    MeasureConditionallyNegative (fun x y ↦ a * K x y) := by
  intro μ ν hμ hν hmass
  simp_rw [kernelPairEnergy_const_mul]
  nlinarith [hK μ ν hμ hν hmass]

noncomputable def schoenbergIntegrand (p r t : ℝ) : ℝ :=
  (1 - Real.exp (-t * r)) * t ^ (-p - 1)

noncomputable def schoenbergIntegral (p r : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0, schoenbergIntegrand p r t

theorem schoenbergIntegrand_nonneg {p r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) :
    0 ≤ schoenbergIntegrand p r t := by
  unfold schoenbergIntegrand
  exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith)))
    (Real.rpow_nonneg ht.le _)

theorem continuousOn_schoenbergIntegrand {p r : ℝ} :
    ContinuousOn (schoenbergIntegrand p r) (Set.Ioi 0) := by
  unfold schoenbergIntegrand
  apply ContinuousOn.mul
  · exact continuousOn_const.sub
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_id.neg.mul continuousOn_const))
  · exact continuousOn_id.rpow continuousOn_const fun t ht ↦ Or.inl ht.ne'

theorem integrableOn_schoenbergIntegrand {p r : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hr : 0 ≤ r) :
    IntegrableOn (schoenbergIntegrand p r) (Set.Ioi 0) := by
  have hmeas (s : Set ℝ) (hs : MeasurableSet s) (hsub : s ⊆ Set.Ioi (0 : ℝ)) :
      AEStronglyMeasurable (schoenbergIntegrand p r) (volume.restrict s) :=
    (continuousOn_schoenbergIntegrand.mono hsub).aestronglyMeasurable hs
  have hzero : IntegrableOn (schoenbergIntegrand p r) (Set.Ioo 0 1) := by
    refine Integrable.mono'
      (((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr
        (by linarith : -1 < -p)).const_mul r)
      (hmeas _ measurableSet_Ioo Set.Ioo_subset_Ioi_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : 0 < t := ht.1
    have hone : 1 - Real.exp (-t * r) ≤ t * r := by
      linarith [Real.add_one_le_exp (-t * r)]
    rw [Real.norm_eq_abs, abs_of_nonneg (schoenbergIntegrand_nonneg hr ht0)]
    unfold schoenbergIntegrand
    calc
      (1 - Real.exp (-t * r)) * t ^ (-p - 1) ≤
          (t * r) * t ^ (-p - 1) :=
        mul_le_mul_of_nonneg_right hone (Real.rpow_nonneg ht0.le _)
      _ = r * (t ^ (1 : ℝ) * t ^ (-p - 1)) := by
        rw [Real.rpow_one]
        ring
      _ = r * t ^ (-p) := by
        rw [← Real.rpow_add ht0]
        congr 2
        ring
  have htop : IntegrableOn (schoenbergIntegrand p r) (Set.Ioi (1 / 2 : ℝ)) := by
    refine Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (by linarith : -p - 1 < -1)
        (by norm_num : (0 : ℝ) < 1 / 2))
      (hmeas _ measurableSet_Ioi (Set.Ioi_subset_Ioi (by norm_num))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) ht
    have hone : 1 - Real.exp (-t * r) ≤ 1 := by
      linarith [Real.exp_nonneg (-t * r)]
    rw [Real.norm_eq_abs, abs_of_nonneg (schoenbergIntegrand_nonneg hr ht0)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) hone
  exact (hzero.union htop).mono_set fun t ht ↦ by
    by_cases h : t < 1
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr (by norm_num at *; linarith)

theorem schoenbergIntegral_zero (p : ℝ) : schoenbergIntegral p 0 = 0 := by
  simp [schoenbergIntegral, schoenbergIntegrand]

theorem schoenbergIntegral_scaling {p r : ℝ} (hr : 0 < r) :
    schoenbergIntegral p r = r ^ p * schoenbergIntegral p 1 := by
  have hchange := integral_comp_mul_left_Ioi (schoenbergIntegrand p 1) 0 hr
  have hpoint : ∀ t ∈ Set.Ioi (0 : ℝ),
      schoenbergIntegrand p 1 (r * t) =
        r ^ (-p - 1) * schoenbergIntegrand p r t := by
    intro t ht
    unfold schoenbergIntegrand
    rw [Real.mul_rpow hr.le ht.le]
    have he : -(r * t) = -(t * r) := by ring
    rw [he]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul,
    mul_zero, smul_eq_mul] at hchange
  unfold schoenbergIntegral
  have hrpow : r ^ (-p - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  apply (mul_left_cancel₀ hrpow)
  rw [hchange, ← mul_assoc, ← Real.rpow_add hr, ← Real.rpow_neg_one]
  congr 2
  ring

theorem schoenbergIntegral_one_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < schoenbergIntegral p 1 := by
  unfold schoenbergIntegral
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae]
  · have hs : Function.support (schoenbergIntegrand p 1) ∩ Set.Ioi 0 = Set.Ioi 0 := by
      rw [Set.inter_eq_right]
      intro t ht
      rw [Function.mem_support]
      apply ne_of_gt
      have ht0 : 0 < t := ht
      unfold schoenbergIntegrand
      exact mul_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by simpa using neg_lt_zero.mpr ht0)))
        (Real.rpow_pos_of_pos ht0 _)
    rw [hs, Real.volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact schoenbergIntegrand_nonneg zero_le_one ht
  · exact integrableOn_schoenbergIntegrand hp0 hp1 zero_le_one

theorem schoenbergIntegral_eq_rpow_mul {p r : ℝ}
    (hp0 : 0 < p) (hr : 0 ≤ r) :
    schoenbergIntegral p r = r ^ p * schoenbergIntegral p 1 := by
  obtain rfl | hr := hr.eq_or_lt
  · simp [schoenbergIntegral_zero, Real.zero_rpow hp0.ne']
  · exact schoenbergIntegral_scaling hr

theorem sphere_dist_sq_nonneg_le_four (x y : Sphere) :
    0 ≤ dist x y ^ 2 ∧ dist x y ^ 2 ≤ 4 := by
  constructor
  · positivity
  · rw [sphere_dist_sq_coordinates]
    have hinner := sphereInnerKernel_abs_le_one x y
    unfold sphereInnerKernel at hinner
    rw [abs_le] at hinner
    linarith

theorem continuousOn_schoenberg_joint {p : ℝ} :
    ContinuousOn
      (fun z : ℝ × (Sphere × Sphere) ↦
        schoenbergIntegrand p (dist z.2.1 z.2.2 ^ 2) z.1)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  unfold schoenbergIntegrand
  have hd : Continuous (fun z : ℝ × (Sphere × Sphere) ↦ dist z.2.1 z.2.2 ^ 2) :=
    (continuous_dist.comp (continuous_snd.fst.prodMk continuous_snd.snd)).pow 2
  apply ContinuousOn.mul
  · exact continuousOn_const.sub (Real.continuous_exp.comp_continuousOn
      ((continuous_fst.neg.mul hd).continuousOn))
  · exact continuousOn_fst.rpow continuousOn_const fun z hz ↦ Or.inl hz.1.ne'

theorem integrable_schoenberg_joint {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : Measure (Sphere × Sphere)) [IsFiniteMeasure ρ] :
    Integrable
      (fun z : ℝ × (Sphere × Sphere) ↦
        schoenbergIntegrand p (dist z.2.1 z.2.2 ^ 2) z.1)
      ((volume.restrict (Set.Ioi 0)).prod ρ) := by
  have hdom : Integrable
      (fun z : ℝ × (Sphere × Sphere) ↦ schoenbergIntegrand p 4 z.1 * 1)
      ((volume.restrict (Set.Ioi 0)).prod ρ) :=
    (integrableOn_schoenbergIntegrand hp0 hp1 (by norm_num : (0 : ℝ) ≤ 4)).mul_prod
      (integrable_const (1 : ℝ))
  apply Integrable.mono' hdom
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact continuousOn_schoenberg_joint.aestronglyMeasurable
      (measurableSet_Ioi.prod MeasurableSet.univ)
  · have hzmem : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)).prod ρ,
        z ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem
        (measurableSet_Ioi.prod MeasurableSet.univ)]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Filter.Eventually.of_forall fun q ↦ ⟨ht, Set.mem_univ q⟩
    filter_upwards [hzmem] with z hz
    have ht : 0 < z.1 := hz.1
    have hr := sphere_dist_sq_nonneg_le_four z.2.1 z.2.2
    rw [Real.norm_eq_abs,
      abs_of_nonneg (schoenbergIntegrand_nonneg hr.1 ht)]
    simp only [mul_one]
    unfold schoenbergIntegrand
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    exact sub_le_sub_left (Real.exp_le_exp.mpr (by nlinarith)) 1

theorem integral_schoenberg_swap {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : Measure (Sphere × Sphere)) [IsFiniteMeasure ρ] :
    (∫ t : ℝ in Set.Ioi 0,
        ∫ q : Sphere × Sphere,
          schoenbergIntegrand p (dist q.1 q.2 ^ 2) t ∂ρ) =
      schoenbergIntegral p 1 *
        ∫ q : Sphere × Sphere, (dist q.1 q.2 ^ 2) ^ p ∂ρ := by
  have hswap := MeasureTheory.integral_integral_swap
    (μ := volume.restrict (Set.Ioi 0)) (ν := ρ)
    (f := fun t q ↦ schoenbergIntegrand p (dist q.1 q.2 ^ 2) t)
    (integrable_schoenberg_joint hp0 hp1 ρ)
  calc
    (∫ t : ℝ in Set.Ioi 0,
        ∫ q : Sphere × Sphere,
          schoenbergIntegrand p (dist q.1 q.2 ^ 2) t ∂ρ) =
        ∫ q : Sphere × Sphere,
          (∫ t : ℝ in Set.Ioi 0,
            schoenbergIntegrand p (dist q.1 q.2 ^ 2) t) ∂ρ := hswap
    _ = ∫ q : Sphere × Sphere,
          (dist q.1 q.2 ^ 2) ^ p * schoenbergIntegral p 1 ∂ρ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q ↦
        schoenbergIntegral_eq_rpow_mul hp0
          (sphere_dist_sq_nonneg_le_four q.1 q.2).1
    _ = _ := by
      rw [integral_mul_const]
      ring

theorem continuous_distance_sq_rpow_prod {p : ℝ} (hp : 0 < p) :
    Continuous (fun q : Sphere × Sphere ↦ (dist q.1 q.2 ^ 2) ^ p) := by
  exact ((continuous_dist.pow 2).rpow continuous_const fun _ ↦ Or.inr hp)

theorem distance_sq_rpow_half_alpha {α : ℝ} (x y : Sphere) :
    (dist x y ^ 2) ^ (α / 2) = dist x y ^ α := by
  rw [← Real.rpow_natCast (dist x y) 2, ← Real.rpow_mul (dist_nonneg : 0 ≤ dist x y)]
  congr 2
  ring

noncomputable def schoenbergKernel (p t : ℝ) (x y : Sphere) : ℝ :=
  schoenbergIntegrand p (dist x y ^ 2) t

theorem continuous_schoenbergKernel_prod (p t : ℝ) :
    Continuous (fun q : Sphere × Sphere ↦ schoenbergKernel p t q.1 q.2) := by
  unfold schoenbergKernel schoenbergIntegrand
  have hd : Continuous (fun q : Sphere × Sphere ↦ dist q.1 q.2 ^ 2) :=
    continuous_dist.pow 2
  exact (continuous_const.sub (Real.continuous_exp.comp
    (continuous_const.mul hd))).mul continuous_const

theorem measureConditionallyNegative_congr {K L : Sphere → Sphere → ℝ}
    (h : ∀ x y, K x y = L x y) (hK : MeasureConditionallyNegative K) :
    MeasureConditionallyNegative L := by
  have hfun : L = K := by
    funext x y
    exact (h x y).symm
  simpa [hfun] using hK

theorem measureConditionallyNegative_schoenbergKernel {p t : ℝ} (ht : 0 < t) :
    MeasureConditionallyNegative (schoenbergKernel p t) := by
  apply measureConditionallyNegative_congr (K := fun x y ↦
    t ^ (-p - 1) * (1 - gaussianDistanceKernel t x y))
  · intro x y
    unfold schoenbergKernel schoenbergIntegrand gaussianDistanceKernel
    ring
  · exact measureConditionallyNegative_const_mul (Real.rpow_nonneg ht.le _)
      (measureConditionallyNegative_one_sub_gaussian ht.le)

theorem measureConditionallyNegative_distance_sq_rpow {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    MeasureConditionallyNegative (fun x y : Sphere ↦ (dist x y ^ 2) ^ p) := by
  intro μ ν hμ hν hmass
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  let A (ρ τ : Measure Sphere) (t : ℝ) :=
    ∫ q : Sphere × Sphere,
      schoenbergIntegrand p (dist q.1 q.2 ^ 2) t ∂ρ.prod τ
  have hAint (ρ τ : Measure Sphere) [IsFiniteMeasure ρ] [IsFiniteMeasure τ] :
      Integrable (A ρ τ) (volume.restrict (Set.Ioi 0)) :=
    (integrable_schoenberg_joint hp0 hp1 (ρ.prod τ)).integral_prod_left
  have hpoint : ∀ᵐ t ∂volume.restrict (Set.Ioi 0),
      A μ μ t + A ν ν t ≤ A μ ν t + A ν μ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hcnd := measureConditionallyNegative_schoenbergKernel (p := p) ht
      μ ν hμ hν hmass
    simpa only [A, kernelPairEnergy_eq_integral_prod μ μ
        (continuous_schoenbergKernel_prod p t),
      kernelPairEnergy_eq_integral_prod ν ν
        (continuous_schoenbergKernel_prod p t),
      kernelPairEnergy_eq_integral_prod μ ν
        (continuous_schoenbergKernel_prod p t),
      kernelPairEnergy_eq_integral_prod ν μ
        (continuous_schoenbergKernel_prod p t),
      schoenbergKernel] using hcnd
  have hint :
      (∫ t in Set.Ioi (0 : ℝ), (A μ μ t + A ν ν t)) ≤
        ∫ t in Set.Ioi (0 : ℝ), (A μ ν t + A ν μ t) :=
    MeasureTheory.integral_mono_ae (hAint μ μ |>.add (hAint ν ν))
      (hAint μ ν |>.add (hAint ν μ)) hpoint
  rw [MeasureTheory.integral_add (hAint μ μ) (hAint ν ν),
    MeasureTheory.integral_add (hAint μ ν) (hAint ν μ),
    integral_schoenberg_swap hp0 hp1 (μ.prod μ),
    integral_schoenberg_swap hp0 hp1 (ν.prod ν),
    integral_schoenberg_swap hp0 hp1 (μ.prod ν),
    integral_schoenberg_swap hp0 hp1 (ν.prod μ)] at hint
  have hbase := schoenbergIntegral_one_pos hp0 hp1
  have hprod :
      (∫ q : Sphere × Sphere, (dist q.1 q.2 ^ 2) ^ p ∂μ.prod μ) +
        (∫ q : Sphere × Sphere, (dist q.1 q.2 ^ 2) ^ p ∂ν.prod ν) ≤
      (∫ q : Sphere × Sphere, (dist q.1 q.2 ^ 2) ^ p ∂μ.prod ν) +
        (∫ q : Sphere × Sphere, (dist q.1 q.2 ^ 2) ^ p ∂ν.prod μ) := by
    apply (mul_le_mul_left hbase).mp
    nlinarith
  simpa only [kernelPairEnergy_eq_integral_prod
      (K := fun x y : Sphere ↦ (dist x y ^ 2) ^ p) μ μ
      (continuous_distance_sq_rpow_prod hp0),
    kernelPairEnergy_eq_integral_prod
      (K := fun x y : Sphere ↦ (dist x y ^ 2) ^ p) ν ν
      (continuous_distance_sq_rpow_prod hp0),
    kernelPairEnergy_eq_integral_prod
      (K := fun x y : Sphere ↦ (dist x y ^ 2) ^ p) μ ν
      (continuous_distance_sq_rpow_prod hp0),
    kernelPairEnergy_eq_integral_prod
      (K := fun x y : Sphere ↦ (dist x y ^ 2) ^ p) ν μ
      (continuous_distance_sq_rpow_prod hp0)] using hprod

theorem distancePowerMeasureCND_of_pos_of_lt_two {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) : DistancePowerMeasureCND α := by
  unfold DistancePowerMeasureCND
  have hp0 : 0 < α / 2 := by linarith
  have hp1 : α / 2 < 1 := by linarith
  simpa only [distance_sq_rpow_half_alpha] using
    measureConditionallyNegative_distance_sq_rpow hp0 hp1

/-- Symmetry of the mixed distance-power energy. -/
theorem kernelPairEnergy_distancePower_comm {α : ℝ} (hα : 0 < α)
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kernelPairEnergy (fun x y ↦ dist x y ^ α) μ ν =
      kernelPairEnergy (fun x y ↦ dist x y ^ α) ν μ := by
  have hcont : Continuous (fun p : Sphere × Sphere ↦ dist p.1 p.2 ^ α) :=
    continuous_dist.rpow continuous_const (fun _ ↦ Or.inr hα)
  have hint : Integrable (fun p : Sphere × Sphere ↦ dist p.1 p.2 ^ α) (μ.prod ν) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold kernelPairEnergy
  rw [integral_integral_swap hint]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with x
  rw [dist_comm]

/-- Chordal distance to a power below two has negative type for finite
positive measures with equal masses. -/
theorem measureNegativeType_of_pos_of_lt_two {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) : MeasureNegativeType α := by
  intro μ ν hμ hν hmass
  letI : IsFiniteMeasure μ := hμ
  letI : IsFiniteMeasure ν := hν
  have h := distancePowerMeasureCND_of_pos_of_lt_two hα0 hα2
    μ ν (ne_of_lt (IsFiniteMeasure.measure_univ_lt_top (μ := μ)))
      (ne_of_lt (IsFiniteMeasure.measure_univ_lt_top (μ := ν))) hmass
  have hcomm := kernelPairEnergy_distancePower_comm hα0 μ ν
  unfold MeasureNegativeType kernelPairEnergy at *
  linarith

end BEMOC.Definitive
