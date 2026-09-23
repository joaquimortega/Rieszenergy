# Completion of the separated kernel derivative lemma

`SeparatedComplete.lean` proves the exact `SeparatedDerivativeBound` proposition
from `KernelDerivatives.lean` for `0 < α < 2`. The extension is the single
global function `separatedSmoothExtension α` on the algebraic open set
`separatedOpen`; it agrees with the latitude kernel at every physical point
of that open set, including the polar boundary.

## Dependencies and proof route

The module imports `SeparatedLocalRectangle` and
`SeparatedBoundaryTransfer`. The former gives a compact interior rectangle
around any point with a strict polynomial ratio bound. The checked termwise
derivative estimate on that rectangle is
`abs_mixedFourth_separatedSmoothExtension_le_on_rectangle`. The latter
passes a uniform interior estimate to physical boundary points using radial
contraction and continuity of the fourth derivative of the smooth extension.

For a fixed separation gap `ε`, put `q₀ = (1−ε)²`, then choose successive
midpoints `q₁ = (q₀+1)/2` and `q₂ = (q₁+1)/2`. The assumptions imply
`0 ≤ q₀ < q₁ < q₂ < 1`. At an interior point with ratio at most `q₁`, the
local rectangle theorem applies with strict bound `q₂`. Its derivative
majorant has the common positive constant
`separatedSeriesFourthConstant α q₂`; this constant depends only on `α`
and `ε`, not on the point or rectangle. The boundary transfer applies with
`q₀ < q₁`. This proves `uniform_separatedSmoothExtension_mixedFourth_le`
on the full physical square wherever the original angular gap holds.

Finally, `separatedDerivativeBound_of_range` supplies that common constant,
the smooth extension and its open domain, the kernel equality, and the
fourth derivative bound required by `SeparatedDerivativeBound α`. The same
extension and domain work for all points; the existential witnesses in the
original proposition are therefore stronger than needed.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.SeparatedLocalRectangle
import BEMOCFormalization.SeparatedBoundaryTransfer

/-! The uniform fourth derivative estimate and the manuscript's separated
kernel derivative proposition. -/

namespace BEMOC.Definitive

open Set

/-- A fixed separated angular gap admits one global smooth extension and one
constant valid at every physical point, including polar boundary points. -/
theorem uniform_separatedSmoothExtension_mixedFourth_le
    {α ε : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
        0 < 2 - 2 * s * t →
        2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
          (1 - ε) * (2 - 2 * s * t) →
        |mixedFourth (separatedSmoothExtension α) s t| ≤
          C * (2 - 2 * s * t) ^ (α / 2 - 4) := by
  let q₀ : ℝ := (1 - ε) ^ 2
  let q₁ : ℝ := (q₀ + 1) / 2
  let q₂ : ℝ := (q₁ + 1) / 2
  have hq₀0 : 0 ≤ q₀ := sq_nonneg _
  have hq₀1 : q₀ < 1 := by
    dsimp [q₀]
    nlinarith [mul_pos hε0 (show 0 < 2 - ε by linarith)]
  have hq₀q₁ : q₀ < q₁ := by dsimp [q₁]; linarith
  have hq₁1 : q₁ < 1 := by dsimp [q₁]; linarith
  have hq₁q₂ : q₁ < q₂ := by dsimp [q₂]; linarith
  have hq₂1 : q₂ < 1 := by dsimp [q₂]; linarith
  have hq₂0 : 0 ≤ q₂ := by dsimp [q₂, q₁]; linarith
  refine ⟨separatedSeriesFourthConstant α q₂,
    separatedSeriesFourthConstant_pos α hq₂0, ?_⟩
  intro s hs t ht hU hsep
  have hratio : separatedRatio s t ≤ q₀ :=
    separatedRatio_le_sq_one_sub hs ht hU hε0 hε1 hsep
  have hopen : (s, t) ∈ separatedOpen :=
    mem_separatedOpen_of_physical_ratio_lt_one hs ht hU
      (lt_of_le_of_lt hratio hq₀1)
  apply separatedSmoothExtension_boundary_transfer hα0 hα2 hq₀q₁
    (q := q₀) (q' := q₁) (C := separatedSeriesFourthConstant α q₂)
    ?_ hs ht hopen hratio
  intro u hu v hv huv hratio₁
  have hUu : 0 < angularKernelA u v := huv.1
  obtain ⟨a, b, c, d, L, hua, hvc, hrect⟩ :=
    exists_separatedSeriesRectangle_of_strict_ratio hu hv hUu hq₂0
      (lt_of_le_of_lt hratio₁ hq₁q₂) hq₂1
  simpa only [angularKernelA] using
    (abs_mixedFourth_separatedSmoothExtension_le_on_rectangle
      hα0 hα2 hrect hua hvc)

/-- The separated averaged kernel has the stated fourth derivative bound,
with the same analytic extension across all polar boundary points. -/
theorem separatedDerivativeBound_of_range
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    SeparatedDerivativeBound α := by
  intro ε hε0 hε1
  obtain ⟨C, hC, hbound⟩ :=
    uniform_separatedSmoothExtension_mixedFourth_le hα0 hα2 hε0 hε1
  refine ⟨C, hC, ?_⟩
  intro s hs t ht hU hsep
  have hopen : (s, t) ∈ separatedOpen :=
    mem_separatedOpen_of_physical_ratio_lt_one hs ht hU
      (separatedRatio_lt_one hs ht hU hε0 hε1 hsep)
  refine ⟨separatedSmoothExtension α, separatedOpen,
    isOpen_separatedOpen, hopen,
    separatedSmoothExtension_contDiffOn hα0 hα2, ?_, ?_⟩
  · intro p hp hps hpt
    exact separatedSmoothExtension_eq_latitudeKernel hp hps hpt
  · exact hbound s hs t ht hU hsep

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.SeparatedLocalRectangle
import BEMOCFormalization.SeparatedBoundaryTransfer

/-! The uniform fourth derivative estimate and the manuscript's separated
kernel derivative proposition. -/

namespace BEMOC.Definitive

open Set

/-- A fixed separated angular gap admits one global smooth extension and one
constant valid at every physical point, including polar boundary points. -/
theorem uniform_separatedSmoothExtension_mixedFourth_le
    {α ε : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
        0 < 2 - 2 * s * t →
        2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
          (1 - ε) * (2 - 2 * s * t) →
        |mixedFourth (separatedSmoothExtension α) s t| ≤
          C * (2 - 2 * s * t) ^ (α / 2 - 4) := by
  let q₀ : ℝ := (1 - ε) ^ 2
  let q₁ : ℝ := (q₀ + 1) / 2
  let q₂ : ℝ := (q₁ + 1) / 2
  have hq₀0 : 0 ≤ q₀ := sq_nonneg _
  have hq₀1 : q₀ < 1 := by
    dsimp [q₀]
    nlinarith [mul_pos hε0 (show 0 < 2 - ε by linarith)]
  have hq₀q₁ : q₀ < q₁ := by dsimp [q₁]; linarith
  have hq₁1 : q₁ < 1 := by dsimp [q₁]; linarith
  have hq₁q₂ : q₁ < q₂ := by dsimp [q₂]; linarith
  have hq₂1 : q₂ < 1 := by dsimp [q₂]; linarith
  have hq₂0 : 0 ≤ q₂ := by dsimp [q₂, q₁]; linarith
  refine ⟨separatedSeriesFourthConstant α q₂,
    separatedSeriesFourthConstant_pos α hq₂0, ?_⟩
  intro s hs t ht hU hsep
  have hratio : separatedRatio s t ≤ q₀ :=
    separatedRatio_le_sq_one_sub hs ht hU hε0 hε1 hsep
  have hopen : (s, t) ∈ separatedOpen :=
    mem_separatedOpen_of_physical_ratio_lt_one hs ht hU
      (lt_of_le_of_lt hratio hq₀1)
  apply separatedSmoothExtension_boundary_transfer hα0 hα2 hq₀q₁
    (q := q₀) (q' := q₁) (C := separatedSeriesFourthConstant α q₂)
    ?_ hs ht hopen hratio
  intro u hu v hv huv hratio₁
  have hUu : 0 < angularKernelA u v := huv.1
  obtain ⟨a, b, c, d, L, hua, hvc, hrect⟩ :=
    exists_separatedSeriesRectangle_of_strict_ratio hu hv hUu hq₂0
      (lt_of_le_of_lt hratio₁ hq₁q₂) hq₂1
  simpa only [angularKernelA] using
    (abs_mixedFourth_separatedSmoothExtension_le_on_rectangle
      hα0 hα2 hrect hua hvc)

/-- The separated averaged kernel has the stated fourth derivative bound,
with the same analytic extension across all polar boundary points. -/
theorem separatedDerivativeBound_of_range
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    SeparatedDerivativeBound α := by
  intro ε hε0 hε1
  obtain ⟨C, hC, hbound⟩ :=
    uniform_separatedSmoothExtension_mixedFourth_le hα0 hα2 hε0 hε1
  refine ⟨C, hC, ?_⟩
  intro s hs t ht hU hsep
  have hopen : (s, t) ∈ separatedOpen :=
    mem_separatedOpen_of_physical_ratio_lt_one hs ht hU
      (separatedRatio_lt_one hs ht hU hε0 hε1 hsep)
  refine ⟨separatedSmoothExtension α, separatedOpen,
    isOpen_separatedOpen, hopen,
    separatedSmoothExtension_contDiffOn hα0 hα2, ?_, ?_⟩
  · intro p hp hps hpt
    exact separatedSmoothExtension_eq_latitudeKernel hp hps hpt
  · exact hbound s hs t ht hU hsep

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
