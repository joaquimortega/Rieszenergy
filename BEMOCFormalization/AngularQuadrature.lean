import BEMOCFormalization.Trapezoid
import BEMOCFormalization.Angular.CuspTrapezoid

/-! Transfer of the proved generic cusp trapezoid estimate to the
`BEMOC.Definitive` proposition contract. -/

namespace BEMOC.Definitive

/-- Appendix 1 quadrature bound, uniformly in the phase and both kernel
coefficients, including the unsmoothed cusp `A = B`. -/
theorem trapezoid_bound {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    TrapezoidBound α := by
  obtain ⟨C, hC, hbound⟩ :=
    Angular.CuspTrapezoid.exists_uniform_cusp_trapezoid_all hα0 hα2
  refine ⟨C, hC, ?_⟩
  intro A B hB hAB L hL φ
  have h := hbound hB hAB L hL φ
  simpa only [angularAverage, angularKernel, Finset.sum_range,
    one_div] using h

end BEMOC.Definitive
