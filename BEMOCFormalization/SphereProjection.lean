import BEMOCFormalization.SurfaceMeasure

open MeasureTheory
namespace BEMOC.Definitive

/-- The absolute first moment of the uniform height coordinate. -/
theorem sphereHeight_abs_integral :
    (∫ u : Sphere, |sphereHeight u| ∂sigma) = 1 / 2 := by
  have hmap := MeasureTheory.integral_map
    (μ := sigma) continuous_sphereHeight.measurable.aemeasurable
    continuous_abs.aestronglyMeasurable
  rw [← hmap, hasUniformHeightMarginal, uniformHeightMeasure,
    integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2), smul_eq_mul]
  rw [show (∫ z : ℝ, |z| ∂volume.restrict (Set.Ioc (-1) 1)) =
      ∫ z : ℝ in (-1)..1, |z| by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_abs.intervalIntegrable _ _)
    (continuous_abs.intervalIntegrable _ _)]
  · have hleft : (∫ z : ℝ in (-1)..0, |z|) = (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_congr fun z hz ↦ abs_of_nonpos (by
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hz
        exact hz.2)]
      rw [intervalIntegral.integral_neg, integral_id]
      norm_num
    have hright : (∫ z : ℝ in (0 : ℝ)..1, |z|) = (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_congr fun z hz ↦ abs_of_nonneg (by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hz
        exact hz.1)]
      simp
    rw [hleft, hright]
    ring

private theorem inner_northPole_eq_height (u : Sphere) :
    @Inner.inner ℝ Ambient _ (u : Ambient) (northPole : Ambient) = sphereHeight u := by
  simp [northPole, parallelPoint, parallelVector, sphereHeight,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]

/-- Every unit direction has the same absolute projection moment. -/
theorem sphere_unit_projection_abs_integral (w : Sphere) :
    (∫ u : Sphere, |@Inner.inner ℝ Ambient _ (u : Ambient) (w : Ambient)| ∂sigma) =
      1 / 2 := by
  let R : Ambient ≃ₗᵢ[ℝ] Ambient :=
    (ℝ ∙ ((w : Ambient) - (northPole : Ambient)))ᗮ.reflection
  have hnorm : ‖(w : Ambient)‖ = ‖(northPole : Ambient)‖ := by
    rw [norm_eq_of_mem_sphere w, norm_eq_of_mem_sphere northPole]
  have hRw : R (w : Ambient) = (northPole : Ambient) :=
    Submodule.reflection_sub hnorm
  let e := sphereLinearIsometryEquiv R
  have hmap := MeasureTheory.integral_map_equiv e
    (μ := sigma) (fun u : Sphere ↦ |@Inner.inner ℝ Ambient _ (u : Ambient) (northPole : Ambient)|)
  rw [sigma_reflection_invariant ((w : Ambient) - (northPole : Ambient))] at hmap
  have heq : ∀ u : Sphere,
      |@Inner.inner ℝ Ambient _ (u : Ambient) (w : Ambient)| =
        |@Inner.inner ℝ Ambient _ (e u : Ambient) (northPole : Ambient)| := by
    intro u
    change |@Inner.inner ℝ Ambient _ (u : Ambient) (w : Ambient)| =
      |@Inner.inner ℝ Ambient _ (R (u : Ambient)) (northPole : Ambient)|
    rw [← hRw]
    exact congrArg abs (R.inner_map_map (u : Ambient) (w : Ambient)).symm
  calc
    (∫ u : Sphere, |@Inner.inner ℝ Ambient _ (u : Ambient) (w : Ambient)| ∂sigma) =
        ∫ u : Sphere, |@Inner.inner ℝ Ambient _ (e u : Ambient) (northPole : Ambient)| ∂sigma := by
          apply integral_congr_ae
          filter_upwards with u
          exact heq u
    _ = ∫ u : Sphere, |@Inner.inner ℝ Ambient _ (u : Ambient) (northPole : Ambient)| ∂sigma := hmap.symm
    _ = 1 / 2 := by simpa only [inner_northPole_eq_height] using sphereHeight_abs_integral

/-- The average absolute projection onto an arbitrary ambient vector. -/
theorem sphere_projection_abs_integral (v : Ambient) :
    (∫ u : Sphere, |@Inner.inner ℝ Ambient _ (u : Ambient) v| ∂sigma) =
      ‖v‖ / 2 := by
  by_cases hv : v = 0
  · subst v
    simp
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : Sphere := ⟨‖v‖⁻¹ • v, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hvnorm), inv_mul_cancel₀ hvnorm.ne']⟩
  have hvscale : v = ‖v‖ • (w : Ambient) := by
    simp [w, smul_smul, hvnorm.ne']
  have hpoint (u : Sphere) :
      |@Inner.inner ℝ Ambient _ (u : Ambient) v| =
        ‖v‖ * |@Inner.inner ℝ Ambient _ (u : Ambient) (w : Ambient)| := by
    conv_lhs => rw [hvscale, real_inner_smul_right, abs_mul, abs_of_pos hvnorm]
  simp_rw [hpoint]
  rw [integral_const_mul, sphere_unit_projection_abs_integral w]
  ring

/-- The signed height coordinate has zero mean. -/
theorem sphereHeight_integral : (∫ u : Sphere, sphereHeight u ∂sigma) = 0 := by
  have hmap := MeasureTheory.integral_map
    (μ := sigma) continuous_sphereHeight.measurable.aemeasurable
    continuous_id.aestronglyMeasurable
  change (∫ u : Sphere, id (sphereHeight u) ∂sigma) = 0
  rw [← hmap, hasUniformHeightMarginal, uniformHeightMeasure,
    integral_smul_measure]
  simp only [id_eq, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2), smul_eq_mul]
  rw [show (∫ z : ℝ, z ∂volume.restrict (Set.Ioc (-1) 1)) =
      ∫ z : ℝ in (-1)..1, z by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]]
  rw [integral_id]
  norm_num

/-- The signed projection onto any ambient vector has zero mean. -/
theorem sphere_projection_integral (v : Ambient) :
    (∫ u : Sphere, @Inner.inner ℝ Ambient _ (u : Ambient) v ∂sigma) = 0 := by
  by_cases hv : v = 0
  · subst v
    simp
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : Sphere := ⟨‖v‖⁻¹ • v, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hvnorm), inv_mul_cancel₀ hvnorm.ne']⟩
  have hvscale : v = ‖v‖ • (w : Ambient) := by
    simp [w, smul_smul, hvnorm.ne']
  let R : Ambient ≃ₗᵢ[ℝ] Ambient :=
    (ℝ ∙ ((w : Ambient) - (northPole : Ambient)))ᗮ.reflection
  have hnorm : ‖(w : Ambient)‖ = ‖(northPole : Ambient)‖ := by
    rw [norm_eq_of_mem_sphere w, norm_eq_of_mem_sphere northPole]
  have hRw : R (w : Ambient) = (northPole : Ambient) :=
    Submodule.reflection_sub hnorm
  let e := sphereLinearIsometryEquiv R
  have hmap := MeasureTheory.integral_map_equiv e
    (μ := sigma) (fun u : Sphere ↦ @Inner.inner ℝ Ambient _ (u : Ambient) (northPole : Ambient))
  rw [sigma_reflection_invariant ((w : Ambient) - (northPole : Ambient))] at hmap
  have heq (u : Sphere) :
      @Inner.inner ℝ Ambient _ (u : Ambient) (w : Ambient) =
        @Inner.inner ℝ Ambient _ (e u : Ambient) (northPole : Ambient) := by
    change @Inner.inner ℝ Ambient _ (u : Ambient) (w : Ambient) =
      @Inner.inner ℝ Ambient _ (R (u : Ambient)) (northPole : Ambient)
    rw [← hRw]
    exact (R.inner_map_map (u : Ambient) (w : Ambient)).symm
  have hw : (∫ u : Sphere, @Inner.inner ℝ Ambient _ (u : Ambient) (w : Ambient) ∂sigma) = 0 := by
    calc
      _ = ∫ u : Sphere, @Inner.inner ℝ Ambient _ (e u : Ambient) (northPole : Ambient) ∂sigma := by
        apply integral_congr_ae
        filter_upwards with u
        exact heq u
      _ = ∫ u : Sphere, @Inner.inner ℝ Ambient _ (u : Ambient) (northPole : Ambient) ∂sigma := hmap.symm
      _ = 0 := by simpa only [inner_northPole_eq_height] using sphereHeight_integral
  have hpoint (u : Sphere) :
      @Inner.inner ℝ Ambient _ (u : Ambient) v =
        ‖v‖ * @Inner.inner ℝ Ambient _ (u : Ambient) (w : Ambient) := by
    conv_lhs => rw [hvscale, real_inner_smul_right]
  simp_rw [hpoint]
  rw [integral_const_mul, hw, mul_zero]

end BEMOC.Definitive
