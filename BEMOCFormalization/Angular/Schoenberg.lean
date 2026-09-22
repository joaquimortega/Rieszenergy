import Mathlib

/-! Fractional-power integral identity used for angular Fourier domination.
Adapted from the legacy Core without importing its unrelated sphere-energy development. -/

open scoped BigOperators Topology Real
open Filter Set Complex MeasureTheory

namespace BEMOC.Definitive.Angular

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


end BEMOC.Definitive.Angular
