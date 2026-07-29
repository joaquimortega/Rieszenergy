import BEMOCFormalization.LatitudeL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Axial disintegration for latitude quadrature

This module proves that averaging the distance-power kernel around an
angular ring makes it a function only of spherical height.  The uniform
height marginal and the constant spherical potential then identify the
full continuous height rule.  This removes the hypothesis from the exact
L2 band-pair quadrature identity.
-/

open scoped BigOperators
open MeasureTheory Set

namespace BEMOC

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

theorem latitudeKernel_swap' (α s t : ℝ) :
    latitudeKernel α s t = latitudeKernel α t s := by
  unfold latitudeKernel angularPairKernel
  congr 2
  funext θ
  congr 1
  ring

theorem integral_distancePower_angularRingMeasure_eq_latitudeKernel_height
    (R : OccupiedRing) {α : ℝ} (hα : 0 < α) (y : Sphere) :
    (∫ x : Sphere, dist y x ^ α ∂angularRingMeasure R) =
      latitudeKernel α R.height (sphereHeight y) := by
  obtain ⟨θ, hy⟩ := exists_parallelPoint_eq y
  let Q : OccupiedRing :=
    { population := 1
      height := sphereHeight y
      height_mem := by
        have hsum := y.property
        change (y : Ambient) ∈ Metric.sphere (0 : Ambient) 1 at hsum
        rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at hsum
        change (∑ i, (y : Ambient) i ^ 2) = 1 ^ 2 at hsum
        norm_num at hsum
        have hterm : (y : Ambient) 2 ^ 2 ≤ ∑ i, (y : Ambient) i ^ 2 :=
          Finset.single_le_sum (fun i _ ↦ sq_nonneg ((y : Ambient) i))
            (Finset.mem_univ 2)
        constructor <;> dsimp [sphereHeight] <;> nlinarith
      phase := 0 }
  rw [← hy]
  change (∫ x : Sphere,
      dist (parallelPoint Q.height θ Q.height_mem) x ^ α
        ∂angularRingMeasure R) =
    latitudeKernel α R.height Q.height
  rw [integral_distancePower_angularRingMeasure_eq_latitudeKernel Q R hα θ]
  exact latitudeKernel_swap' α Q.height R.height

theorem integral_latitudeKernel_sphereAreaProbability
    (R : OccupiedRing) {α : ℝ} (hα : 0 < α) :
    (∫ y : Sphere, latitudeKernel α R.height (sphereHeight y)
        ∂sphereAreaProbability) = continuousEnergy α := by
  calc
    (∫ y : Sphere, latitudeKernel α R.height (sphereHeight y)
        ∂sphereAreaProbability) =
        measurePairEnergy sphereAreaProbability (angularRingMeasure R) α := by
          unfold measurePairEnergy kernelPairEnergy
          apply integral_congr_ae
          filter_upwards with y
          exact (integral_distancePower_angularRingMeasure_eq_latitudeKernel_height
            R hα y).symm
    _ = continuousEnergy α := by
      have h := measurePairEnergy_sphereReference_measure 1 hα
        (hasConstantSpherePotential_continuousEnergy hα)
        (angularRingMeasure R) (angularRingMeasure_apply_univ_ne_top R) (by simp)
      simpa [sphereReferenceMeasure] using h

theorem integral_latitudeKernel_uniformHeightMeasure
    {s α : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) (hα : 0 < α) :
    (∫ t : ℝ, latitudeKernel α s t ∂uniformHeightMeasure) =
      continuousEnergy α := by
  let R : OccupiedRing :=
    { population := 1
      height := s
      height_mem := hs
      phase := 0 }
  have hf : Continuous (fun t : ℝ ↦ latitudeKernel α s t) :=
    (continuous_latitudeKernel hα).comp (continuous_const.prodMk continuous_id)
  have hmap := MeasureTheory.integral_map
    (μ := sphereAreaProbability) continuous_sphereHeight.measurable.aemeasurable
    hf.aestronglyMeasurable
  rw [← hasUniformHeightMarginal, hmap]
  exact integral_latitudeKernel_sphereAreaProbability R hα

theorem half_intervalIntegral_latitudeKernel
    {s α : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) (hα : 0 < α) :
    (1 / 2 : ℝ) * ∫ t : ℝ in (-1)..1, latitudeKernel α s t =
      continuousEnergy α := by
  have h := integral_latitudeKernel_uniformHeightMeasure hs hα
  rw [uniformHeightMeasure, integral_smul_measure] at h
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    smul_eq_mul] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  exact h

set_option maxHeartbeats 500000 in
theorem total_bandContinuousValue_latitudeKernel
    {N : ℕ} (hN : 0 < N) {s α : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) (hα : 0 < α) :
    (∑ k : Fin (bandTailCount N + 1),
      bandContinuousValue N k (fun t ↦ latitudeKernel α s t)) =
      (N : ℝ) * continuousEnergy α := by
  rw [sum_bandContinuousValue_eq_heightIntegral hN
    (fun t ↦ latitudeKernel α s t)
    ((continuous_latitudeKernel hα).comp
      (continuous_const.prodMk continuous_id))]
  have h := half_intervalIntegral_latitudeKernel hs hα
  nlinarith

set_option maxHeartbeats 500000 in
theorem sum_bandError_latitudeKernel_right
    {N : ℕ} (hN : 0 < N) {s α : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) (hα : 0 < α) :
    (∑ k : Fin (bandTailCount N + 1),
      bandError N k (fun t ↦ latitudeKernel α s t)) =
      (∑ q : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
        (bemocRingFamily N q).population *
          latitudeKernel α s (bemocRingFamily N q).height) -
        (N : ℝ) * continuousEnergy α := by
  rw [sum_bandError_eq_bemocHeightQuadrature hN
    (fun t ↦ latitudeKernel α s t)
    ((continuous_latitudeKernel hα).comp
      (continuous_const.prodMk continuous_id))]
  have h := half_intervalIntegral_latitudeKernel hs hα
  nlinarith

set_option maxHeartbeats 800000 in
theorem intervalIntegral_sum_bandError_latitudeKernel_eq_zero
    {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α) :
    (∫ s : ℝ in (-1)..1,
      ∑ k : Fin (bandTailCount N + 1),
        bandError N k (fun t ↦ latitudeKernel α s t)) = 0 := by
  let B : ℝ → ℝ := fun s ↦
    ∑ q : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
      (bemocRingFamily N q).population *
        latitudeKernel α s (bemocRingFamily N q).height
  have hB : Continuous B := by
    dsimp [B]
    apply continuous_finset_sum
    intro q hq
    exact continuous_const.mul ((continuous_latitudeKernel hα).comp
      (continuous_id.prodMk continuous_const))
  have hg : Continuous (fun s : ℝ ↦
      ∑ k : Fin (bandTailCount N + 1),
        bandError N k (fun t ↦ latitudeKernel α s t)) :=
    continuous_finset_sum _ fun k _ ↦
      continuous_bandError_right k (continuous_latitudeKernel hα)
  calc
    (∫ s : ℝ in (-1)..1,
      ∑ k : Fin (bandTailCount N + 1),
        bandError N k (fun t ↦ latitudeKernel α s t)) =
        ∫ s : ℝ in (-1)..1, B s - (N : ℝ) * continuousEnergy α := by
          apply intervalIntegral.integral_congr
          intro s hs
          change (∑ k : Fin (bandTailCount N + 1),
              bandError N k (fun t ↦ latitudeKernel α s t)) =
            B s - (N : ℝ) * continuousEnergy α
          rw [sum_bandError_latitudeKernel_right hN
            (show s ∈ Icc (-1 : ℝ) 1 by simpa using hs) hα]
    _ = (∫ s : ℝ in (-1)..1, B s) -
        ∫ _s : ℝ in (-1)..1, (N : ℝ) * continuousEnergy α := by
          rw [intervalIntegral.integral_sub
            (hB.intervalIntegrable _ _)
            (continuous_const.intervalIntegrable _ _)]
    _ = (∑ q : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
          (bemocRingFamily N q).population *
            ∫ s : ℝ in (-1)..1,
              latitudeKernel α s (bemocRingFamily N q).height) -
        2 * ((N : ℝ) * continuousEnergy α) := by
          dsimp [B]
          rw [intervalIntegral.integral_finset_sum]
          · simp_rw [intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const]
            simp only [smul_eq_mul]
            ring
          · intro q hq
            exact (continuous_const.mul ((continuous_latitudeKernel hα).comp
              (continuous_id.prodMk continuous_const))).intervalIntegrable _ _
    _ = 0 := by
      have hheight (q : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N)) :
          (bemocRingFamily N q).height ∈ Icc (-1 : ℝ) 1 :=
        (bemocRingFamily N q).height_mem
      have hkernel (q : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N)) :
          (∫ s : ℝ in (-1)..1,
            latitudeKernel α s (bemocRingFamily N q).height) =
              2 * continuousEnergy α := by
        rw [show (fun s : ℝ ↦
              latitudeKernel α s (bemocRingFamily N q).height) =
            fun s ↦ latitudeKernel α (bemocRingFamily N q).height s by
              funext s
              exact latitudeKernel_swap' α s (bemocRingFamily N q).height]
        have h := half_intervalIntegral_latitudeKernel (hheight q) hα
        linarith
      simp_rw [hkernel]
      have hpop :
          (∑ q : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
            ((bemocRingFamily N q).population : ℝ)) = N := by
        exact_mod_cast sum_bemocRingFamily_population N
      rw [← Finset.sum_mul, hpop]
      ring

set_option maxHeartbeats 1000000 in
theorem hasExactLatitudePairQuadrature
    {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α) :
    HasExactLatitudePairQuadrature α N := by
  unfold HasExactLatitudePairQuadrature
  rw [sum_bandPairError_eq_total_bandError (continuous_latitudeKernel hα)]
  let g : ℝ → ℝ := fun s ↦
    ∑ k : Fin (bandTailCount N + 1),
      bandError N k (fun t ↦ latitudeKernel α s t)
  have hg : Continuous g := by
    dsimp [g]
    exact continuous_finset_sum _ fun k _ ↦
      continuous_bandError_right k (continuous_latitudeKernel hα)
  change (∑ j : Fin (bandTailCount N + 1), bandError N j g) =
    bandAtomicPairValue N (latitudeKernel α) -
      continuousEnergy α * (N : ℝ) ^ 2
  rw [sum_bandError_eq_bemocHeightQuadrature hN g hg]
  have houter :
      (∫ s : ℝ in (-1)..1, g s) = 0 := by
    exact intervalIntegral_sum_bandError_latitudeKernel_eq_zero hN hα
  rw [houter, mul_zero, sub_zero]
  simp_rw [show ∀ p :
      Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
      g (bemocRingFamily N p).height =
        (∑ q : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
          (bemocRingFamily N q).population *
            latitudeKernel α (bemocRingFamily N p).height
              (bemocRingFamily N q).height) -
          (N : ℝ) * continuousEnergy α by
    intro p
    exact sum_bandError_latitudeKernel_right hN
      (bemocRingFamily N p).height_mem hα]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum]
  have hfirst :
      (∑ p : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
        ∑ q : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
          (bemocRingFamily N p).population *
            ((bemocRingFamily N q).population *
              latitudeKernel α (bemocRingFamily N p).height
                (bemocRingFamily N q).height)) =
        bandAtomicPairValue N (latitudeKernel α) := by
    rw [bandAtomicPairValue_eq_bemoc_sum hN]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hfirst]
  have hpop :
      (∑ p : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
        ((bemocRingFamily N p).population : ℝ)) = N := by
    exact_mod_cast sum_bemocRingFamily_population N
  rw [← Finset.sum_mul, hpop]
  ring

theorem bemocLatitudeDeficit_eq_neg_sum_bandPairError
    {N : ℕ} {α : ℝ} (hN : 0 < N) (hα : 0 < α) :
    bemocLatitudeDeficit α N =
      -∑ j : Fin (bandTailCount N + 1),
        ∑ k : Fin (bandTailCount N + 1),
          bandPairError N j k (latitudeKernel α) :=
  bemocLatitudeDeficit_eq_neg_sum_bandPairError_of_exactLatitudePairQuadrature
    hN hα (hasExactLatitudePairQuadrature hN hα)

end BEMOC
