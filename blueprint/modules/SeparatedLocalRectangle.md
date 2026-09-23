# SeparatedLocalRectangle: local uniform series geometry

A physical interior latitude pair with positive base and strictly subunit even-series ratio has a closed physical rectangle around it. The proof uses continuity of the base and ratio at the pair, the product-neighborhood basis, and closed interval neighborhoods in each coordinate. It supplies the compact rectangle data required by the interior mixed-fourth derivative bound.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.SeparatedMixedFourth

/-! A strict separated point has a compact physical rectangle on which the
even kernel series has uniform convergence data. -/

open Filter Set
open scoped Topology

namespace BEMOC.Definitive

/-- Local closed rectangle data around a strictly separated interior pair. -/
theorem exists_separatedSeriesRectangle_of_strict_ratio
    {s t q : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hU : 0 < angularKernelA s t)
    (hq0 : 0 ≤ q) (hq : separatedRatio s t < q) (hq1 : q < 1) :
    ∃ a b c d L : ℝ,
      s ∈ Ioo a b ∧ t ∈ Ioo c d ∧
        SeparatedSeriesRectangle a b c d L q := by
  let L : ℝ := angularKernelA s t / 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hLlt : L < angularKernelA s t := by dsimp [L]; linarith
  let O : Set (ℝ × ℝ) := {p |
    p.1 ∈ Ioo (-1 : ℝ) 1 ∧ p.2 ∈ Ioo (-1 : ℝ) 1 ∧
      L < angularKernelA p.1 p.2 ∧ separatedRatio p.1 p.2 < q}
  have hleft : {p : ℝ × ℝ | p.1 ∈ Ioo (-1 : ℝ) 1} ∈ 𝓝 (s, t) :=
    (isOpen_Ioo.preimage continuous_fst).mem_nhds hs
  have hright : {p : ℝ × ℝ | p.2 ∈ Ioo (-1 : ℝ) 1} ∈ 𝓝 (s, t) :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds ht
  have hAcont : ContinuousAt (fun p : ℝ × ℝ => angularKernelA p.1 p.2) (s, t) := by
    unfold angularKernelA
    fun_prop
  have hbase : {p : ℝ × ℝ | L < angularKernelA p.1 p.2} ∈ 𝓝 (s, t) :=
    hAcont.eventually (Ioi_mem_nhds hLlt)
  have hnum : ContinuousAt (fun p : ℝ × ℝ =>
      4 * (1 - p.1 ^ 2) * (1 - p.2 ^ 2)) (s, t) := by fun_prop
  have hden : ContinuousAt (fun p : ℝ × ℝ =>
      (2 - 2 * p.1 * p.2) ^ 2) (s, t) := by fun_prop
  have hratioCont : ContinuousAt
      (fun p : ℝ × ℝ => separatedRatio p.1 p.2) (s, t) := by
    change ContinuousAt (fun p : ℝ × ℝ =>
      4 * (1 - p.1 ^ 2) * (1 - p.2 ^ 2) /
        (2 - 2 * p.1 * p.2) ^ 2) (s, t)
    exact hnum.div hden (pow_ne_zero 2 hU.ne')
  have hratio : {p : ℝ × ℝ | separatedRatio p.1 p.2 < q} ∈ 𝓝 (s, t) :=
    hratioCont.eventually (Iio_mem_nhds hq)
  have hO : O ∈ 𝓝 (s, t) := by
    filter_upwards [hleft, hright, hbase, hratio] with p hp₁ hp₂ hp₃ hp₄
    exact ⟨hp₁, hp₂, hp₃, hp₄⟩
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hO
  obtain ⟨a, b, hsab, hUab, habu⟩ := exists_Icc_mem_subset_of_mem_nhds hu
  obtain ⟨c, d, htcd, hUcd, hcdv⟩ := exists_Icc_mem_subset_of_mem_nhds hv
  have hsab' : s ∈ Ioo a b := Icc_mem_nhds_iff.mp hUab
  have htcd' : t ∈ Ioo c d := Icc_mem_nhds_iff.mp hUcd
  refine ⟨a, b, c, d, L, hsab', htcd', ?_⟩
  refine ⟨hL, hq0, hq1, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxO : (x, t) ∈ O := huv ⟨habu hx, hcdv htcd⟩
    exact ⟨hxO.1.1.le, hxO.1.2.le⟩
  · intro y hy
    have hyO : (s, y) ∈ O := huv ⟨habu hsab, hcdv hy⟩
    exact ⟨hyO.2.1.1.le, hyO.2.1.2.le⟩
  · intro x hx y hy
    have hxyO : (x, y) ∈ O := huv ⟨habu hx, hcdv hy⟩
    exact hxyO.2.2.1.le
  · intro x hx y hy
    have hxyO : (x, y) ∈ O := huv ⟨habu hx, hcdv hy⟩
    exact hxyO.2.2.2.le

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
