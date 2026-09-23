# SphereSupport proof guide

This module supplies the measure-theoretic fact needed to turn harmonic polynomials into an honest inner-product space: normalized surface measure `sigma` assigns positive mass to every nonempty open subset of the sphere. `SurfaceMeasure.lean` already proves that `sigma` is a probability measure, but probability mass alone does not make `∫ f² dσ` positive for every nonzero continuous `f`. Full topological support is essential; otherwise a continuous function supported outside the measure's support could have zero L² norm and Gram–Schmidt would not produce a basis of the original function space.

The proof starts with mathlib's `Measure.toSphere_apply'`, which expresses the unnormalized spherical measure of a measurable set `U` as `dim(Ambient)` times the ambient volume of the radial cone over `U` with radii between zero and one. An open nonempty `U` yields an open nonempty cone. Rather than asserting this informally, `toSphere_open_pos` uses `homeomorphUnitSphereProd Ambient`: nonzero ambient vectors are homeomorphic to their direction on the unit sphere and their positive norm. Form the product of `U` with radii below one, use continuity of the homeomorphism and the open embedding of the nonzero-vector subtype into ambient space, and obtain a nonempty open ambient set `V`. Its positive volume follows from the Haar measure `IsOpenPosMeasure` instance. `Measure.toSphere_apply_aux` identifies that volume with the radial-cone volume in `toSphere_apply'`. Since the ambient dimension is three, the unnormalized spherical measure of `U` is positive.

`sigma_open_pos` transfers positivity through the normalization factor. The total unnormalized area is finite by mathlib's `IsFiniteMeasure` instance for `toSphere` and nonzero by the existing `SurfaceMeasure` theorem. Its reciprocal is therefore positive in `ENNReal`, and multiplication preserves positivity. This is packaged as `sigma.IsOpenPosMeasure`, an instance consumed by standard integral lemmas. The proof uses the exact `sigma` from `Core`; no alternative surface measure or unstated equivalence of measures is introduced.

For a nonzero continuous `f : C(Sphere,ℝ)`, choose a point at which `f` is nonzero. The continuous function `x ↦ (f x)^2` is nonnegative and nonzero at that point. Compactness of the sphere gives compact support, and probability/finite measure gives integrability via `Continuous.integrable_of_hasCompactSupport`. Mathlib's `integral_pos_of_integrable_nonneg_nonzero`, together with the open-positive instance, yields `sigma_integral_sq_pos`. This theorem is the positive-definiteness argument used by `HarmonicOrthonormal`: if a harmonic polynomial's restricted L² square integral vanishes, its restriction is zero, and `homogeneous_restrict_injective` then makes the polynomial zero. The same result feeds `HarmonicBasisAssembly`, where orthogonality to the dense harmonic span closes the `HarmonicBasis.complete` field.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
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
```

<!-- END_LEAN_STATEMENTS -->
