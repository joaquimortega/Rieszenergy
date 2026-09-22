# SphereCapMeasure proof guide

The uniform height marginal gives the upper height cap area. For `-1 ≤ t ≤ 1`, the intersection of the marginal support `(-1,1]` with `[t,∞)` agrees up to the null singleton `{-1}` with `[t,1]`, whose Lebesgue measure is `1-t`. The normalization factor `1/2` therefore gives `(1-t)/2`.

A Householder reflection sends any cap axis `u` to the north pole and preserves `sigma`. Its inner-product identity identifies the preimage of a north-pole cap with the cap centered on `u`. This yields `sphere_cap_measure` in `ENNReal` and `sphere_cap_measure_toReal` in `ℝ`.

Status: complete. `lake build BEMOCFormalization.SphereCapMeasure` elaborates without proof shortcuts.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.SphereProjection

open MeasureTheory
namespace BEMOC.Definitive

/-- The uniform height law assigns a cap of height threshold `t` the expected area. -/
theorem uniformHeightMeasure_Ici {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    uniformHeightMeasure (Set.Ici t) = ENNReal.ofReal ((1 - t) / 2) := by
  rw [uniformHeightMeasure, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Ici]
  have hset : Set.Ici t ∩ Set.Ioc (-1 : ℝ) 1 = Set.Icc t 1 \ {(-1 : ℝ)} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc,
      Set.mem_diff, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · rintro ⟨htz, hzLower, hzUpper⟩
      exact ⟨⟨htz, hzUpper⟩, ne_of_gt hzLower⟩
    · rintro ⟨⟨htz, hzUpper⟩, hne⟩
      exact ⟨htz, lt_of_le_of_ne (ht.1.trans htz) (Ne.symm hne), hzUpper⟩
  rw [hset, measure_diff_null (measure_singleton _), Real.volume_Icc]
  simp only [smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

/-- The north-pole cap has normalized area `(1-t)/2`. -/
theorem sphereHeight_cap_measure {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    sigma {x : Sphere | t ≤ sphereHeight x} = ENNReal.ofReal ((1 - t) / 2) := by
  have hmap := congrArg (fun μ : Measure ℝ ↦ μ (Set.Ici t)) hasUniformHeightMarginal
  dsimp only at hmap
  rw [Measure.map_apply continuous_sphereHeight.measurable measurableSet_Ici] at hmap
  exact hmap.trans (uniformHeightMeasure_Ici ht)

private theorem inner_northPole_eq_height_cap (x : Sphere) :
    @Inner.inner ℝ Ambient _ (x : Ambient) (northPole : Ambient) = sphereHeight x := by
  simp [northPole, parallelPoint, parallelVector, sphereHeight,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]

/-- Every spherical cap of threshold `t` has the same normalized area. -/
theorem sphere_cap_measure (u : Sphere) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    sigma {x : Sphere | t ≤ @Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)} =
      ENNReal.ofReal ((1 - t) / 2) := by
  let R : Ambient ≃ₗᵢ[ℝ] Ambient :=
    (ℝ ∙ ((u : Ambient) - (northPole : Ambient)))ᗮ.reflection
  have hnorm : ‖(u : Ambient)‖ = ‖(northPole : Ambient)‖ := by
    rw [norm_eq_of_mem_sphere u, norm_eq_of_mem_sphere northPole]
  have hRu : R (u : Ambient) = (northPole : Ambient) :=
    Submodule.reflection_sub hnorm
  let e := sphereLinearIsometryEquiv R
  let S : Set Sphere := {x | t ≤ sphereHeight x}
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const continuous_sphereHeight.measurable
  have hinv := sigma_reflection_invariant ((u : Ambient) - (northPole : Ambient))
  have hmap := congrArg (fun μ : Measure Sphere ↦ μ S) hinv
  dsimp only at hmap
  rw [Measure.map_apply e.measurable hS] at hmap
  have hinner (x : Sphere) :
      sphereHeight (e x) = @Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient) := by
    rw [← inner_northPole_eq_height_cap (e x)]
    change @Inner.inner ℝ Ambient _ (R (x : Ambient)) (northPole : Ambient) = _
    rw [← hRu, R.inner_map_map]
    exact (real_inner_comm (x : Ambient) (u : Ambient)).symm
  have hpre : e ⁻¹' S =
      {x : Sphere | t ≤ @Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)} := by
    ext x
    change (t ≤ sphereHeight (e x)) ↔
      (t ≤ @Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient))
    rw [hinner x]
  rw [← hpre, hmap]
  exact sphereHeight_cap_measure ht

/-- The same cap-area formula as a real number. -/
theorem sphere_cap_measure_toReal (u : Sphere) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (sigma {x : Sphere | t ≤ @Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)}).toReal =
      (1 - t) / 2 := by
  rw [sphere_cap_measure u ht, ENNReal.toReal_ofReal]
  linarith [ht.2]

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
