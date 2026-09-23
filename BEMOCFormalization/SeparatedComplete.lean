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
