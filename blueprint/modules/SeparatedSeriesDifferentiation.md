# SeparatedSeriesDifferentiation: four justified termwise derivatives

This module imports `SeparatedSeriesBounds`. Each shifted-tail theorem applies mathlib's `hasDerivAt_tsum_of_isPreconnected` on the appropriate open side of a `SeparatedSeriesRectangle`. The inputs are a summable rectangle-wide majorant, differentiability of each explicit mode, summability at the evaluation point, and the open/preconnected interval. `norm_separatedEvenPower_tailStages_le_majorant` supplies the uniform bound at each stage.

The order is two derivatives in the left height and then two in the right: series term to `DS`, `DS` to `DSS`, `DSS` to `DSST`, and `DSST` to `DSSTT`. The theorems first treat the shifted tail `m=r+2`, where the common majorant has a uniform formula. The five `...SeriesSum` definitions restore modes `0` and `1` as finite prefixes. The four final `HasDerivAt` theorems add the separately differentiated low modes to the tail results.

These are derivative identities on rectangle interiors, with the other coordinate allowed on the closed side. They justify differentiating the explicit series in the stated order. Identification with `mixedFourth (separatedSmoothExtension α)` is made in `SeparatedMixedFourth`, after the extension is equated with the series on the rectangle.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.SeparatedSeriesBounds

/-! Four uniform termwise differentiations on a separated physical rectangle. -/

open Set Filter
open scoped Topology

namespace BEMOC.Definitive

set_option maxHeartbeats 800000

theorem hasDerivAt_shifted_latitudeEvenPowerSeries_left
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {a b c d L q : ℝ}
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    {s t : ℝ}
    (hs : s ∈ Ioo (a)
      (b))
    (ht : t ∈ Icc (c)
      (d)) :
    HasDerivAt
      (fun y ↦ ∑' r : ℕ,
        separatedEvenPowerSeriesTerm α (r + 2) y t)
      (∑' r : ℕ,
        separatedEvenPowerDSSeriesTerm α (r + 2) s t) s := by
  apply hasDerivAt_tsum_of_isPreconnected
    (u := separatedLatitudeTailMajorant α L q)
    (t := Ioo (a)
      (b))
    (g := fun r y ↦ separatedEvenPowerSeriesTerm α (r + 2) y t)
    (g' := fun r y ↦ separatedEvenPowerDSSeriesTerm α (r + 2) y t)
    (y₀ := s)
  · exact summable_separatedLatitudeTailMajorant α L q hgeo.ratio_nonneg hgeo.ratio_lt_one
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro r y hy
    have hy' : y ∈ Icc (a)
        (b) := ⟨hy.1.le, hy.2.le⟩
    have hA : 0 < angularKernelA y t :=
      hgeo.base_pos.trans_le (hgeo.base_le y hy' t ht)
    simpa [separatedEvenPowerSeriesTerm,
      separatedEvenPowerDSSeriesTerm] using
      (hasDerivAt_separatedEvenPowerSummand_left
        (α := α) (m := r + 2) hA).const_mul
          (Ring.choose (α / 2) (2 * (r + 2)) *
            normalizedCosineMoment (2 * (r + 2)))
  · intro r y hy
    exact
      (norm_separatedEvenPower_tailStages_le_majorant
        hα0 hα2 hgeo ⟨hy.1.le, hy.2.le⟩ ht r).1
  · exact hs
  · exact summable_shifted_separatedEvenPowerSeriesTerm
      (hgeo.left_mem s ⟨hs.1.le, hs.2.le⟩)
      (hgeo.right_mem t ht)
      (hgeo.base_pos.trans_le (hgeo.base_le s ⟨hs.1.le, hs.2.le⟩ t ht))
      hgeo.ratio_nonneg hgeo.ratio_lt_one
      (hgeo.ratio_le s ⟨hs.1.le, hs.2.le⟩ t ht)
  · exact hs

/-- Second left-height pass. -/
theorem hasDerivAt_shifted_latitudeEvenPowerDSSeries_left
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {a b c d L q : ℝ}
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    {s t : ℝ}
    (hs : s ∈ Ioo (a)
      (b))
    (ht : t ∈ Icc (c)
      (d)) :
    HasDerivAt
      (fun y ↦ ∑' r : ℕ,
        separatedEvenPowerDSSeriesTerm α (r + 2) y t)
      (∑' r : ℕ,
        separatedEvenPowerDSSSeriesTerm α (r + 2) s t) s := by
  apply hasDerivAt_tsum_of_isPreconnected
    (u := separatedLatitudeTailMajorant α L q)
    (t := Ioo (a)
      (b))
    (g := fun r y ↦ separatedEvenPowerDSSeriesTerm α (r + 2) y t)
    (g' := fun r y ↦ separatedEvenPowerDSSSeriesTerm α (r + 2) y t)
    (y₀ := s)
  · exact summable_separatedLatitudeTailMajorant α L q hgeo.ratio_nonneg hgeo.ratio_lt_one
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro r y hy
    have hy' : y ∈ Icc (a)
        (b) := ⟨hy.1.le, hy.2.le⟩
    have hA : 0 < angularKernelA y t :=
      hgeo.base_pos.trans_le (hgeo.base_le y hy' t ht)
    simpa [separatedEvenPowerDSSeriesTerm,
      separatedEvenPowerDSSSeriesTerm] using
      (hasDerivAt_separatedEvenPowerSummandDS_left
        (α := α) (m := r + 2) hA).const_mul
          (Ring.choose (α / 2) (2 * (r + 2)) *
            normalizedCosineMoment (2 * (r + 2)))
  · intro r y hy
    exact
      (norm_separatedEvenPower_tailStages_le_majorant
        hα0 hα2 hgeo ⟨hy.1.le, hy.2.le⟩ ht r).2.1
  · exact hs
  · exact
      (summable_shifted_separatedEvenPower_lowerSeriesTerms
        hα0 hα2 (hgeo.left_mem s ⟨hs.1.le, hs.2.le⟩)
        (hgeo.right_mem t ht)
        (hgeo.base_pos.trans_le (hgeo.base_le s ⟨hs.1.le, hs.2.le⟩ t ht))
        hgeo.ratio_nonneg hgeo.ratio_lt_one
        (hgeo.ratio_le s ⟨hs.1.le, hs.2.le⟩ t ht)).1
  · exact hs

/-- First right-height pass after the two left derivatives. -/
theorem hasDerivAt_shifted_latitudeEvenPowerDSSSeries_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {a b c d L q : ℝ}
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    {s t : ℝ}
    (hs : s ∈ Icc (a)
      (b))
    (ht : t ∈ Ioo (c)
      (d)) :
    HasDerivAt
      (fun y ↦ ∑' r : ℕ,
        separatedEvenPowerDSSSeriesTerm α (r + 2) s y)
      (∑' r : ℕ,
        separatedEvenPowerDSSTSeriesTerm α (r + 2) s t) t := by
  apply hasDerivAt_tsum_of_isPreconnected
    (u := separatedLatitudeTailMajorant α L q)
    (t := Ioo (c)
      (d))
    (g := fun r y ↦ separatedEvenPowerDSSSeriesTerm α (r + 2) s y)
    (g' := fun r y ↦ separatedEvenPowerDSSTSeriesTerm α (r + 2) s y)
    (y₀ := t)
  · exact summable_separatedLatitudeTailMajorant α L q hgeo.ratio_nonneg hgeo.ratio_lt_one
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro r y hy
    have hy' : y ∈ Icc (c)
        (d) := ⟨hy.1.le, hy.2.le⟩
    have hA : 0 < angularKernelA s y :=
      hgeo.base_pos.trans_le (hgeo.base_le s hs y hy')
    simpa [separatedEvenPowerDSSSeriesTerm,
      separatedEvenPowerDSSTSeriesTerm] using
      (hasDerivAt_separatedEvenPowerSummandDSS_right
        (α := α) (m := r + 2) hA).const_mul
          (Ring.choose (α / 2) (2 * (r + 2)) *
            normalizedCosineMoment (2 * (r + 2)))
  · intro r y hy
    exact
      (norm_separatedEvenPower_tailStages_le_majorant
        hα0 hα2 hgeo hs ⟨hy.1.le, hy.2.le⟩ r).2.2.1
  · exact ht
  · exact
      (summable_shifted_separatedEvenPower_lowerSeriesTerms
        hα0 hα2 (hgeo.left_mem s hs)
        (hgeo.right_mem t ⟨ht.1.le, ht.2.le⟩)
        (hgeo.base_pos.trans_le (hgeo.base_le s hs t ⟨ht.1.le, ht.2.le⟩))
        hgeo.ratio_nonneg hgeo.ratio_lt_one
        (hgeo.ratio_le s hs t ⟨ht.1.le, ht.2.le⟩)).2.1
  · exact ht

/-- Final right-height pass, producing the shifted `(2,2)` series. -/
theorem hasDerivAt_shifted_latitudeEvenPowerDSSTSeries_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {a b c d L q : ℝ}
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    {s t : ℝ}
    (hs : s ∈ Icc (a)
      (b))
    (ht : t ∈ Ioo (c)
      (d)) :
    HasDerivAt
      (fun y ↦ ∑' r : ℕ,
        separatedEvenPowerDSSTSeriesTerm α (r + 2) s y)
      (∑' r : ℕ,
        separatedEvenPowerDSSTTSeriesTerm α (r + 2) s t) t := by
  apply hasDerivAt_tsum_of_isPreconnected
    (u := separatedLatitudeTailMajorant α L q)
    (t := Ioo (c)
      (d))
    (g := fun r y ↦ separatedEvenPowerDSSTSeriesTerm α (r + 2) s y)
    (g' := fun r y ↦ separatedEvenPowerDSSTTSeriesTerm α (r + 2) s y)
    (y₀ := t)
  · exact summable_separatedLatitudeTailMajorant α L q hgeo.ratio_nonneg hgeo.ratio_lt_one
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro r y hy
    have hy' : y ∈ Icc (c)
        (d) := ⟨hy.1.le, hy.2.le⟩
    have hA : 0 < angularKernelA s y :=
      hgeo.base_pos.trans_le (hgeo.base_le s hs y hy')
    simpa [separatedEvenPowerDSSTSeriesTerm,
      separatedEvenPowerDSSTTSeriesTerm] using
      (hasDerivAt_separatedEvenPowerSummandDSST_right
        (α := α) (m := r + 2) hA).const_mul
          (Ring.choose (α / 2) (2 * (r + 2)) *
            normalizedCosineMoment (2 * (r + 2)))
  · intro r y hy
    exact
      (norm_separatedEvenPower_tailStages_le_majorant
        hα0 hα2 hgeo hs ⟨hy.1.le, hy.2.le⟩ r).2.2.2
  · exact ht
  · exact
      (summable_shifted_separatedEvenPower_lowerSeriesTerms
        hα0 hα2 (hgeo.left_mem s hs)
        (hgeo.right_mem t ⟨ht.1.le, ht.2.le⟩)
        (hgeo.base_pos.trans_le (hgeo.base_le s hs t ⟨ht.1.le, ht.2.le⟩))
        hgeo.ratio_nonneg hgeo.ratio_lt_one
        (hgeo.ratio_le s hs t ⟨ht.1.le, ht.2.le⟩)).2.2
  · exact ht

noncomputable def separatedEvenPowerSeriesSum
    (α s t : ℝ) : ℝ :=
  separatedEvenPowerSeriesTerm α 0 s t +
    separatedEvenPowerSeriesTerm α 1 s t +
    ∑' r : ℕ, separatedEvenPowerSeriesTerm α (r + 2) s t

noncomputable def separatedEvenPowerDSSeriesSum
    (α s t : ℝ) : ℝ :=
  separatedEvenPowerDSSeriesTerm α 0 s t +
    separatedEvenPowerDSSeriesTerm α 1 s t +
    ∑' r : ℕ, separatedEvenPowerDSSeriesTerm α (r + 2) s t

noncomputable def separatedEvenPowerDSSSeriesSum
    (α s t : ℝ) : ℝ :=
  separatedEvenPowerDSSSeriesTerm α 0 s t +
    separatedEvenPowerDSSSeriesTerm α 1 s t +
    ∑' r : ℕ, separatedEvenPowerDSSSeriesTerm α (r + 2) s t

noncomputable def separatedEvenPowerDSSTSeriesSum
    (α s t : ℝ) : ℝ :=
  separatedEvenPowerDSSTSeriesTerm α 0 s t +
    separatedEvenPowerDSSTSeriesTerm α 1 s t +
    ∑' r : ℕ, separatedEvenPowerDSSTSeriesTerm α (r + 2) s t

noncomputable def separatedEvenPowerDSSTTSeriesSum
    (α s t : ℝ) : ℝ :=
  separatedEvenPowerDSSTTSeriesTerm α 0 s t +
    separatedEvenPowerDSSTTSeriesTerm α 1 s t +
    ∑' r : ℕ, separatedEvenPowerDSSTTSeriesTerm α (r + 2) s t

theorem hasDerivAt_separatedEvenPowerSeriesSum_left
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {a b c d L q : ℝ}
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    {s t : ℝ}
    (hs : s ∈ Ioo (a)
      (b))
    (ht : t ∈ Icc (c)
      (d)) :
    HasDerivAt (fun y ↦ separatedEvenPowerSeriesSum α y t)
      (separatedEvenPowerDSSeriesSum α s t) s := by
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le
      (hgeo.base_le s ⟨hs.1.le, hs.2.le⟩ t ht)
  have h0 :=
    (hasDerivAt_separatedEvenPowerSummand_left
      (α := α) (m := 0) hA).const_mul
        (Ring.choose (α / 2) 0 * normalizedCosineMoment 0)
  have h1 :=
    (hasDerivAt_separatedEvenPowerSummand_left
      (α := α) (m := 1) hA).const_mul
        (Ring.choose (α / 2) 2 * normalizedCosineMoment 2)
  have htail :=
    hasDerivAt_shifted_latitudeEvenPowerSeries_left
      hα0 hα2 hgeo hs ht
  simpa [separatedEvenPowerSeriesSum, separatedEvenPowerDSSeriesSum,
    separatedEvenPowerSeriesTerm, separatedEvenPowerDSSeriesTerm] using
      (h0.add h1).add htail

theorem hasDerivAt_separatedEvenPowerDSSeriesSum_left
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {a b c d L q : ℝ}
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    {s t : ℝ}
    (hs : s ∈ Ioo (a)
      (b))
    (ht : t ∈ Icc (c)
      (d)) :
    HasDerivAt (fun y ↦ separatedEvenPowerDSSeriesSum α y t)
      (separatedEvenPowerDSSSeriesSum α s t) s := by
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le
      (hgeo.base_le s ⟨hs.1.le, hs.2.le⟩ t ht)
  have h0 :=
    (hasDerivAt_separatedEvenPowerSummandDS_left
      (α := α) (m := 0) hA).const_mul
        (Ring.choose (α / 2) 0 * normalizedCosineMoment 0)
  have h1 :=
    (hasDerivAt_separatedEvenPowerSummandDS_left
      (α := α) (m := 1) hA).const_mul
        (Ring.choose (α / 2) 2 * normalizedCosineMoment 2)
  have htail :=
    hasDerivAt_shifted_latitudeEvenPowerDSSeries_left
      hα0 hα2 hgeo hs ht
  simpa [separatedEvenPowerDSSeriesSum, separatedEvenPowerDSSSeriesSum,
    separatedEvenPowerDSSeriesTerm, separatedEvenPowerDSSSeriesTerm] using
      (h0.add h1).add htail

theorem hasDerivAt_separatedEvenPowerDSSSeriesSum_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {a b c d L q : ℝ}
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    {s t : ℝ}
    (hs : s ∈ Icc (a)
      (b))
    (ht : t ∈ Ioo (c)
      (d)) :
    HasDerivAt (fun y ↦ separatedEvenPowerDSSSeriesSum α s y)
      (separatedEvenPowerDSSTSeriesSum α s t) t := by
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le
      (hgeo.base_le s hs t ⟨ht.1.le, ht.2.le⟩)
  have h0 :=
    (hasDerivAt_separatedEvenPowerSummandDSS_right
      (α := α) (m := 0) hA).const_mul
        (Ring.choose (α / 2) 0 * normalizedCosineMoment 0)
  have h1 :=
    (hasDerivAt_separatedEvenPowerSummandDSS_right
      (α := α) (m := 1) hA).const_mul
        (Ring.choose (α / 2) 2 * normalizedCosineMoment 2)
  have htail :=
    hasDerivAt_shifted_latitudeEvenPowerDSSSeries_right
      hα0 hα2 hgeo hs ht
  simpa [separatedEvenPowerDSSSeriesSum, separatedEvenPowerDSSTSeriesSum,
    separatedEvenPowerDSSSeriesTerm, separatedEvenPowerDSSTSeriesTerm] using
      (h0.add h1).add htail

theorem hasDerivAt_separatedEvenPowerDSSTSeriesSum_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {a b c d L q : ℝ}
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    {s t : ℝ}
    (hs : s ∈ Icc (a)
      (b))
    (ht : t ∈ Ioo (c)
      (d)) :
    HasDerivAt (fun y ↦ separatedEvenPowerDSSTSeriesSum α s y)
      (separatedEvenPowerDSSTTSeriesSum α s t) t := by
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le
      (hgeo.base_le s hs t ⟨ht.1.le, ht.2.le⟩)
  have h0 :=
    (hasDerivAt_separatedEvenPowerSummandDSST_right
      (α := α) (m := 0) hA).const_mul
        (Ring.choose (α / 2) 0 * normalizedCosineMoment 0)
  have h1 :=
    (hasDerivAt_separatedEvenPowerSummandDSST_right
      (α := α) (m := 1) hA).const_mul
        (Ring.choose (α / 2) 2 * normalizedCosineMoment 2)
  have htail :=
    hasDerivAt_shifted_latitudeEvenPowerDSSTSeries_right
      hα0 hα2 hgeo hs ht
  simpa [separatedEvenPowerDSSTSeriesSum, separatedEvenPowerDSSTTSeriesSum,
    separatedEvenPowerDSSTSeriesTerm, separatedEvenPowerDSSTTSeriesTerm] using
      (h0.add h1).add htail


end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
