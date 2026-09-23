import BEMOCFormalization.HarmonicDimension

open MeasureTheory Set Metric
namespace BEMOC.Definitive

theorem toSphere_open_pos {U : Set Sphere} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < volume.toSphere U := by
  let r : Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  let W : Set (Sphere × Ioi (0 : ℝ)) := U ×ˢ Iio r
  have hWopen : IsOpen W := hU.prod isOpen_Iio
  have hWne : W.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨(x, ⟨(1/2 : ℝ), by norm_num⟩), ?_⟩
    exact ⟨hx, by norm_num [r]⟩
  let V : Set Ambient := (Subtype.val : ({0}ᶜ : Set Ambient) → Ambient) ''
    ((homeomorphUnitSphereProd Ambient) ⁻¹' W)
  have hVopen : IsOpen V := by
    apply (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set Ambient)).isOpenMap_subtype_val
    exact hWopen.preimage (homeomorphUnitSphereProd Ambient).continuous
  have hVne : V.Nonempty := by
    obtain ⟨z, hz⟩ := hWne
    refine ⟨((homeomorphUnitSphereProd Ambient).symm z).val,
      (homeomorphUnitSphereProd Ambient).symm z, ?_⟩
    simpa [V, W] using hz
  have hVpos : 0 < volume V := hVopen.measure_pos volume hVne
  have hdim : 0 < Module.finrank ℝ Ambient := by norm_num
  rw [Measure.toSphere_apply' volume hU.measurableSet,
    ← Measure.toSphere_apply_aux volume U r]
  exact ENNReal.mul_pos_iff.mpr ⟨by exact_mod_cast hdim, hVpos⟩

theorem sigma_open_pos {U : Set Sphere} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < sigma U := by
  have hUpos := toSphere_open_pos hU hne
  have hfin : volume.toSphere (Set.univ : Set Sphere) ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  change 0 < (volume.toSphere (Set.univ : Set Sphere))⁻¹ * volume.toSphere U
  exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.inv_pos.mpr hfin, hUpos⟩

/-- The normalized surface measure has full topological support. -/
instance : sigma.IsOpenPosMeasure where
  open_pos _ hU hne := ne_of_gt (sigma_open_pos hU hne)

/-- The surface L² pairing is strictly positive on every nonzero continuous
function. -/
theorem sigma_integral_sq_pos {f : C(Sphere, ℝ)} (hf : f ≠ 0) :
    0 < ∫ x, (f x) ^ 2 ∂sigma := by
  have hx : ∃ x : Sphere, f x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf
    ext x
    exact h x
  obtain ⟨x, hx⟩ := hx
  have hcont : Continuous (fun x : Sphere => (f x) ^ 2) := f.continuous.pow 2
  have hint : Integrable (fun x : Sphere => (f x) ^ 2) sigma :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact integral_pos_of_integrable_nonneg_nonzero hcont hint
    (fun _ => sq_nonneg _) (pow_ne_zero 2 hx)

end BEMOC.Definitive
