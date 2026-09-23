# SeparatedMixedFourth: the rectangle mixed-fourth estimate

This module imports `SeparatedSeriesDifferentiation` and `SeparatedSmoothExtension`. `separatedSmoothExtension_eq_seriesSum_on_rectangle` identifies the single extension with the finite-prefix plus shifted-tail sum on a closed separated rectangle. The proof uses the even-series equality and the summability needed to split the first two modes from the full `tsum`.

The extension and rectangle geometry are symmetric in the two heights. The private `SeparatedSeriesRectangle.swap` transports all rectangle hypotheses under coordinate interchange. `mixedFourth_separatedSmoothExtension_eq_seriesSum_swap` combines local equality of the extension and series, the four `HasDerivAt` results, and this symmetry to identify the actual mathlib `mixedFourth` with the coefficient-weighted `DSSTT` series evaluated at `(t,s)`. The swapped evaluation is required by the order in which `mixedFourth` differentiates its coordinates.

Finally, `abs_mixedFourth_separatedSmoothExtension_le_on_rectangle` applies the `tsum` bound from `SeparatedSeriesSum` after splitting off modes `0` and `1`, then restores the symmetric base. It proves `|mixedFourth| ≤ separatedSeriesFourthConstant α q · angularKernelA(s,t)^(α/2-4)` for points in the **open interior** of a rectangle satisfying `SeparatedSeriesRectangle`, with `0<α<2`. Passing to polar boundary points and constructing suitable rectangles around arbitrary separated physical points are subsequent obligations; this theorem alone is not a global epsilon-separated estimate.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.SeparatedSeriesDifferentiation
import BEMOCFormalization.SeparatedSmoothExtension

/-! Identify the mixed fourth derivative of the analytic separated extension
with the normally convergent series of explicit mixed derivatives. -/

namespace BEMOC.Definitive

open Set Filter
open scoped Topology

/-- The finite-prefix form of the even series is the global extension on a
separated physical rectangle. -/
theorem separatedSmoothExtension_eq_seriesSum_on_rectangle
    {α a b c d L q s t : ℝ}
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc c d) :
    separatedSmoothExtension α (s,t) = separatedEvenPowerSeriesSum α s t := by
  have hU : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le (hgeo.base_le s hs t ht)
  rw [separatedSmoothExtension_eq_evenSeries_of_Upos hU]
  unfold separatedEvenSeries separatedEvenPowerSeriesSum
  have htail := summable_shifted_separatedEvenPowerSeriesTerm
    (α := α) (hgeo.left_mem s hs) (hgeo.right_mem t ht)
    hU hgeo.ratio_nonneg hgeo.ratio_lt_one (hgeo.ratio_le s hs t ht)
  have hfull : Summable (fun m : ℕ ↦ separatedEvenPowerSeriesTerm α m s t) := by
    rw [← summable_nat_add_iff 2]
    simpa [Nat.add_comm] using htail
  have hsplit := hfull.sum_add_tsum_nat_add 2
  simpa [separatedEvenPowerSeriesTerm, Finset.sum_range_succ] using hsplit.symm

private theorem iteratedDeriv_two_separatedSmoothExtension_left
    {α a b c d L q s t : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    (hs : s ∈ Ioo a b) (ht : t ∈ Icc c d) :
    iteratedDeriv 2 (fun y ↦ separatedSmoothExtension α (y,t)) s =
      separatedEvenPowerDSSSeriesSum α s t := by
  have heq :
      (fun y ↦ separatedSmoothExtension α (y,t)) =ᶠ[𝓝 s]
        (fun y ↦ separatedEvenPowerSeriesSum α y t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with y hy
    exact separatedSmoothExtension_eq_seriesSum_on_rectangle
      hgeo ⟨hy.1.le, hy.2.le⟩ ht
  have hDS :
      deriv (fun y ↦ separatedEvenPowerSeriesSum α y t) =ᶠ[𝓝 s]
        (fun y ↦ separatedEvenPowerDSSeriesSum α y t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with y hy
    exact (hasDerivAt_separatedEvenPowerSeriesSum_left
      hα0 hα2 hgeo hy ht).deriv
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ]
  rw [show iteratedDeriv 1
      (fun y ↦ separatedSmoothExtension α (y,t)) =
        deriv (fun y ↦ separatedSmoothExtension α (y,t)) by
      rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_zero]]
  rw [heq.deriv.deriv_eq, hDS.deriv_eq]
  exact (hasDerivAt_separatedEvenPowerDSSeriesSum_left
    hα0 hα2 hgeo hs ht).deriv

private theorem separatedSmoothExtension_symm (α s t : ℝ) :
    separatedSmoothExtension α (s,t) = separatedSmoothExtension α (t,s) := by
  have hU : angularKernelA s t = angularKernelA t s := by
    unfold angularKernelA
    ring
  have hQ : separatedRatio s t = separatedRatio t s := by
    unfold separatedRatio
    ring
  unfold separatedSmoothExtension
  rw [hU, hQ]

private theorem SeparatedSeriesRectangle.swap
    {a b c d L q : ℝ}
    (hgeo : SeparatedSeriesRectangle a b c d L q) :
    SeparatedSeriesRectangle c d a b L q where
  base_pos := hgeo.base_pos
  ratio_nonneg := hgeo.ratio_nonneg
  ratio_lt_one := hgeo.ratio_lt_one
  left_mem := hgeo.right_mem
  right_mem := hgeo.left_mem
  base_le := by
    intro t ht s hs
    have h := hgeo.base_le s hs t ht
    unfold angularKernelA at h ⊢
    nlinarith
  ratio_le := by
    intro t ht s hs
    have h := hgeo.ratio_le s hs t ht
    simpa [separatedRatio, angularKernelA, mul_comm, mul_left_comm, mul_assoc] using h

/-- On the interior of a normally separated rectangle, the actual mixed
fourth derivative is the normally convergent explicit derivative series.
The final equality is evaluated at `(t,s)` because `mixedFourth` takes the
right derivatives first and the even angular kernel is symmetric. -/
theorem mixedFourth_separatedSmoothExtension_eq_seriesSum_swap
    {α a b c d L q s t : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo c d) :
    mixedFourth (separatedSmoothExtension α) s t =
      separatedEvenPowerDSSTTSeriesSum α t s := by
  have hgeo' := hgeo.swap
  have hts : t ∈ Icc c d := ⟨ht.1.le, ht.2.le⟩
  have hss : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
  have hswap :
      (fun u ↦ iteratedDeriv 2
        (fun v ↦ separatedSmoothExtension α (u,v)) t) =
      (fun u ↦ iteratedDeriv 2
        (fun v ↦ separatedSmoothExtension α (v,u)) t) := by
    funext u
    congr 1
    funext v
    exact separatedSmoothExtension_symm α u v
  let J : ℝ → ℝ := fun u ↦ iteratedDeriv 2
    (fun v ↦ separatedSmoothExtension α (v,u)) t
  have hJ : J =ᶠ[𝓝 s]
      (fun u ↦ separatedEvenPowerDSSSeriesSum α t u) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact iteratedDeriv_two_separatedSmoothExtension_left
      hα0 hα2 hgeo' ht ⟨hu.1.le, hu.2.le⟩
  have hDSST :
      deriv (fun u ↦ separatedEvenPowerDSSSeriesSum α t u) =ᶠ[𝓝 s]
        (fun u ↦ separatedEvenPowerDSSTSeriesSum α t u) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact (hasDerivAt_separatedEvenPowerDSSSeriesSum_right
      hα0 hα2 hgeo' hts hu).deriv
  unfold mixedFourth
  rw [hswap]
  change iteratedDeriv 2 J s = _
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ]
  rw [show iteratedDeriv 1 J = deriv J by
      rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_zero]]
  rw [hJ.deriv.deriv_eq, hDSST.deriv_eq]
  exact (hasDerivAt_separatedEvenPowerDSSTSeriesSum_right
    hα0 hα2 hgeo' hts hs).deriv

theorem abs_mixedFourth_separatedSmoothExtension_le_on_rectangle
    {α a b c d L q s t : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hgeo : SeparatedSeriesRectangle a b c d L q)
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo c d) :
    |mixedFourth (separatedSmoothExtension α) s t| ≤
      separatedSeriesFourthConstant α q *
        angularKernelA s t ^ (α / 2 - 4) := by
  have hgeo' := hgeo.swap
  have hts : t ∈ Icc c d := ⟨ht.1.le, ht.2.le⟩
  have hss : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
  have hU : 0 < angularKernelA t s :=
    hgeo'.base_pos.trans_le (hgeo'.base_le t hts s hss)
  have hsum : Summable (fun m : ℕ ↦ separatedEvenPowerDSSTTSeriesTerm α m t s) :=
    summable_separatedEvenPowerDSSTTSeriesTerm hα0 hα2
      (hgeo'.left_mem t hts) (hgeo'.right_mem s hss)
      hU hgeo'.ratio_nonneg hgeo'.ratio_lt_one
      (hgeo'.ratio_le t hts s hss)
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hsumEq : separatedEvenPowerDSSTTSeriesSum α t s =
      ∑' m : ℕ, separatedEvenPowerDSSTTSeriesTerm α m t s := by
    unfold separatedEvenPowerDSSTTSeriesSum
    simpa [Finset.sum_range_succ] using hsplit
  rw [mixedFourth_separatedSmoothExtension_eq_seriesSum_swap
    hα0 hα2 hgeo hs ht, hsumEq]
  have hbound := abs_tsum_separatedEvenPowerDSSTTSeriesTerm_le
    hα0 hα2 (hgeo'.left_mem t hts) (hgeo'.right_mem s hss)
    hU hgeo'.ratio_nonneg hgeo'.ratio_lt_one
    (hgeo'.ratio_le t hts s hss)
  have hUeq : angularKernelA t s = angularKernelA s t := by
    unfold angularKernelA
    ring
  simpa [hUeq] using hbound

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
