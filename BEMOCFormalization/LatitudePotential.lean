import BEMOCFormalization.SurfaceMeasure
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open scoped BigOperators
open MeasureTheory Set
namespace BEMOC.Definitive


/-- Squared chordal distance between two points on spherical parallels. -/
theorem parallelPoint_dist_sq {s t θ φ : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    dist (parallelPoint s θ hs) (parallelPoint t φ ht) ^ 2 =
      2 - 2 * s * t -
        2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * Real.cos (θ - φ) := by
  have hrs : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hrt : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  change dist (parallelVector s θ) (parallelVector t φ) ^ 2 = _
  rw [EuclideanSpace.dist_eq]
  have hsum : 0 ≤ ∑ i : Fin 3,
      dist (parallelVector s θ i) (parallelVector t φ i) ^ 2 := by positivity
  rw [Real.sq_sqrt hsum]
  simp [parallelPoint, parallelVector, Fin.sum_univ_succ, Real.dist_eq,
    sq_abs, Real.sq_sqrt hrs, Real.sq_sqrt hrt, Real.cos_sub]
  ring_nf
  rw [Real.sq_sqrt hrs, Real.sq_sqrt hrt]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]


theorem exists_parallelPoint_eq (y : Sphere) :
    ∃ θ : ℝ, parallelPoint (sphereHeight y) θ (by
      have hsum := y.property
      change (y : Ambient) ∈ Metric.sphere (0 : Ambient) 1 at hsum
      rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at hsum
      change (∑ i, (y : Ambient) i ^ 2) = 1 ^ 2 at hsum
      norm_num at hsum
      have hterm : (y : Ambient) 2 ^ 2 ≤ ∑ i, (y : Ambient) i ^ 2 :=
        Finset.single_le_sum (fun i _ ↦ sq_nonneg ((y : Ambient) i))
          (Finset.mem_univ 2)
      constructor <;> dsimp [sphereHeight] <;> nlinarith) = y := by
  let z : ℂ := ⟨(y : Ambient) 0, (y : Ambient) 1⟩
  let t : ℝ := sphereHeight y
  have hsum := y.property
  change (y : Ambient) ∈ Metric.sphere (0 : Ambient) 1 at hsum
  rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at hsum
  change (∑ i, (y : Ambient) i ^ 2) = 1 ^ 2 at hsum
  have hsum' :
      (y : Ambient) 0 ^ 2 + ((y : Ambient) 1 ^ 2 + (y : Ambient) 2 ^ 2) = 1 := by
    simpa [Fin.sum_univ_succ] using hsum
  have hnormsq : ‖z‖ ^ 2 = 1 - t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [z, t, sphereHeight]
    nlinarith [hsum']
  have hradius : Real.sqrt (1 - t ^ 2) = ‖z‖ := by
    rw [← hnormsq, Real.sqrt_sq (norm_nonneg z)]
  refine ⟨Complex.arg z, ?_⟩
  apply Subtype.ext
  ext i
  fin_cases i
  · change Real.sqrt (1 - t ^ 2) * Real.cos (Complex.arg z) = (y : Ambient) 0
    rw [hradius]
    simp [z]
  · change Real.sqrt (1 - t ^ 2) * Real.sin (Complex.arg z) = (y : Ambient) 1
    rw [hradius]
    simp [z]
  · rfl


/-- Angular profile of the latitude kernel. -/
noncomputable def latitudeProfile (α s t θ : ℝ) : ℝ :=
  (2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
    Real.sqrt (1 - t ^ 2) * Real.cos θ) ^ (α / 2)

theorem latitudeProfile_periodic (α s t : ℝ) :
    Function.Periodic (latitudeProfile α s t) (2 * Real.pi) := by
  intro θ
  simp [latitudeProfile, Real.cos_add_two_pi]

theorem dist_parallelPoint_rpow_eq_profile {s t θ φ α : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    dist (parallelPoint t θ ht) (parallelPoint s φ hs) ^ α =
      latitudeProfile α s t (φ - θ) := by
  rw [dist_comm]
  have hd := parallelPoint_dist_sq hs ht (θ := φ) (φ := θ)
  unfold latitudeProfile
  rw [← hd]
  rw [show α = (2 : ℝ) * (α / 2) by ring, Real.rpow_mul dist_nonneg]
  norm_num [Real.rpow_natCast]

/-- Normalized uniform angular measure on one complete turn. -/
noncomputable def uniformAngleMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) •
    volume.restrict (Set.Ioc 0 (2 * Real.pi))

@[simp] theorem uniformAngleMeasure_apply_univ :
    uniformAngleMeasure Set.univ = 1 := by
  rw [uniformAngleMeasure, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter, Real.volume_Ioc, sub_zero]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [show 1 / (2 * Real.pi) = (2 * Real.pi)⁻¹ by ring,
    ENNReal.ofReal_inv_of_pos hpi]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_eq_zero.not.mpr (not_le.mpr hpi)) ENNReal.ofReal_ne_top

theorem integral_uniformAngleMeasure_eq_interval (f : ℝ → ℝ) :
    (∫ θ, f θ ∂uniformAngleMeasure) =
      (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..2 * Real.pi, f θ := by
  rw [uniformAngleMeasure, integral_smul_measure]
  have hc : 0 ≤ 1 / (2 * Real.pi) := by positivity
  rw [ENNReal.toReal_ofReal hc]
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rfl

theorem integral_latitudeProfile_shift (α s t θ : ℝ) :
    (∫ φ in (0 : ℝ)..2 * Real.pi, latitudeProfile α s t (φ - θ)) =
      ∫ φ in (0 : ℝ)..2 * Real.pi, latitudeProfile α s t φ := by
  let g := latitudeProfile α s t
  have hg : Function.Periodic g (2 * Real.pi) := latitudeProfile_periodic α s t
  have hshift :
      (∫ u in -θ..2 * Real.pi - θ, g u) =
        ∫ u in (0 : ℝ)..2 * Real.pi, g u := by
    convert hg.intervalIntegral_add_eq (-θ) 0 using 1 <;> ring_nf
  calc
    (∫ φ in (0 : ℝ)..2 * Real.pi, latitudeProfile α s t (φ - θ)) =
        ∫ u in -θ..2 * Real.pi - θ, g u := by
          rw [intervalIntegral.integral_comp_sub_right]
          simp only [zero_sub]
          rfl
    _ = _ := hshift

theorem latitudeKernel_eq_profile_integral (α s t : ℝ) :
    latitudeKernel α s t =
      (1 / (2 * Real.pi)) *
        ∫ θ in (0 : ℝ)..2 * Real.pi, latitudeProfile α s t θ := by
  simp [latitudeKernel, latitudeProfile, one_div]

theorem angular_distancePower_eq_latitudeKernel
    {α s t : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (θ : ℝ) :
    (∫ φ, dist (parallelPoint t θ ht) (parallelPoint s φ hs) ^ α
      ∂uniformAngleMeasure) = latitudeKernel α s t := by
  rw [integral_uniformAngleMeasure_eq_interval]
  simp_rw [dist_parallelPoint_rpow_eq_profile hs ht]
  rw [integral_latitudeProfile_shift]
  exact (latitudeKernel_eq_profile_integral α s t).symm

theorem continuous_parallelPoint (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    Continuous (fun θ ↦ parallelPoint s θ hs) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  fin_cases i <;> simp [parallelPoint, parallelVector] <;> fun_prop

/-- Uniform probability measure on a fixed spherical parallel. -/
noncomputable def parallelMeasure (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    Measure Sphere :=
  Measure.map (fun θ ↦ parallelPoint s θ hs) uniformAngleMeasure

@[simp] theorem parallelMeasure_apply_univ (s : ℝ)
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    parallelMeasure s hs Set.univ = 1 := by
  rw [parallelMeasure,
    Measure.map_apply (continuous_parallelPoint s hs).measurable MeasurableSet.univ]
  simp

instance parallelMeasure_finite (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    IsFiniteMeasure (parallelMeasure s hs) :=
  IsFiniteMeasure.mk (by simp)

theorem integral_parallelMeasure (s : ℝ) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (f : Sphere → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂parallelMeasure s hs) =
      ∫ θ, f (parallelPoint s θ hs) ∂uniformAngleMeasure := by
  unfold parallelMeasure
  rw [integral_map_of_stronglyMeasurable
    (continuous_parallelPoint s hs).measurable hf.stronglyMeasurable]

theorem integral_distancePower_parallelMeasure_eq_latitudeKernel
    {α s : ℝ} (hα : 0 < α) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (y : Sphere) :
    (∫ x, dist y x ^ α ∂parallelMeasure s hs) =
      latitudeKernel α s (sphereHeight y) := by
  have hf : Continuous (fun x : Sphere ↦ dist y x ^ α) :=
    (continuous_const.dist continuous_id).rpow continuous_const
      (fun _ ↦ Or.inr hα)
  rw [integral_parallelMeasure s hs _ hf]
  obtain ⟨θ, hy⟩ := exists_parallelPoint_eq y
  rw [← hy]
  exact angular_distancePower_eq_latitudeKernel hs (sphereHeight_mem_Icc y) θ

theorem continuous_latitudeProfile {α : ℝ} (hα : 0 < α) :
    Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      latitudeProfile α p.1.1 p.1.2 p.2) := by
  unfold latitudeProfile
  have hbase : Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      2 - 2 * p.1.1 * p.1.2 -
        2 * Real.sqrt (1 - p.1.1 ^ 2) * Real.sqrt (1 - p.1.2 ^ 2) *
          Real.cos p.2) := by
    fun_prop
  exact hbase.rpow continuous_const (fun _ ↦ Or.inr (by linarith))

theorem continuous_latitudeKernel {α : ℝ} (hα : 0 < α) :
    Continuous (fun p : ℝ × ℝ ↦ latitudeKernel α p.1 p.2) := by
  rw [show (fun p : ℝ × ℝ ↦ latitudeKernel α p.1 p.2) =
      fun p ↦ (1 / (2 * Real.pi)) *
        ∫ θ in (0 : ℝ)..2 * Real.pi, latitudeProfile α p.1 p.2 θ by
          funext p
          exact latitudeKernel_eq_profile_integral α p.1 p.2]
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact continuous_latitudeProfile hα

theorem integral_latitudeKernel_sigma {α s : ℝ} (hα : 0 < α)
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    (∫ y : Sphere, latitudeKernel α s (sphereHeight y) ∂sigma) =
      continuousEnergy α := by
  have hcont : Continuous (fun p : Sphere × Sphere ↦ dist p.1 p.2 ^ α) :=
    continuous_dist.rpow continuous_const (fun _ ↦ Or.inr hα)
  have hint : Integrable (fun p : Sphere × Sphere ↦ dist p.1 p.2 ^ α)
      (sigma.prod (parallelMeasure s hs)) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hswap := MeasureTheory.integral_integral_swap
    (μ := sigma) (ν := parallelMeasure s hs)
    (f := fun y x ↦ dist y x ^ α) hint
  simp_rw [integral_distancePower_parallelMeasure_eq_latitudeKernel hα hs] at hswap
  have hinner (x : Sphere) :
      (∫ y : Sphere, dist y x ^ α ∂sigma) = continuousEnergy α := by
    simp_rw [dist_comm _ x]
    exact constantPotential_of_pos hα x
  simp_rw [hinner] at hswap
  rw [integral_const] at hswap
  simpa [Measure.real_def] using hswap

theorem integral_latitudeKernel_uniformHeightMeasure {α s : ℝ}
    (hα : 0 < α) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    (∫ t : ℝ, latitudeKernel α s t ∂uniformHeightMeasure) =
      continuousEnergy α := by
  have hf : Continuous (fun t : ℝ ↦ latitudeKernel α s t) :=
    (continuous_latitudeKernel hα).comp (continuous_const.prodMk continuous_id)
  have hmap := MeasureTheory.integral_map
    (μ := sigma) continuous_sphereHeight.measurable.aemeasurable
    hf.aestronglyMeasurable
  rw [← hasUniformHeightMarginal, hmap]
  exact integral_latitudeKernel_sigma hα hs

/-- The angularly averaged kernel has the exact constant height potential. -/
theorem half_intervalIntegral_latitudeKernel {s α : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (hα : 0 < α) :
    (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, latitudeKernel α s t =
      continuousEnergy α := by
  have h := integral_latitudeKernel_uniformHeightMeasure hα hs
  rw [uniformHeightMeasure, integral_smul_measure] at h
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    smul_eq_mul] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  exact h

end BEMOC.Definitive
