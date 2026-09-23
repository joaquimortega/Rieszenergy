import BEMOCFormalization.SeparatedSeriesSum
import BEMOCFormalization.ScalarPowerSeries

/-! The single analytic extension of the separated latitude kernel. -/

namespace BEMOC.Definitive

open Set

/-- The algebraic open separation domain.  It includes physical polar
boundary points and extends to both sides of those boundaries. -/
def separatedOpen : Set (ℝ × ℝ) :=
  {p | 0 < angularKernelA p.1 p.2 ∧
    |4 * (1 - p.1 ^ 2) * (1 - p.2 ^ 2)| < angularKernelA p.1 p.2 ^ 2}

theorem isOpen_separatedOpen : IsOpen separatedOpen := by
  have hU : Continuous (fun p : ℝ × ℝ ↦ angularKernelA p.1 p.2) := by
    unfold angularKernelA
    fun_prop
  have hN : Continuous (fun p : ℝ × ℝ ↦
      |4 * (1 - p.1 ^ 2) * (1 - p.2 ^ 2)|) := by
    fun_prop
  have hD : Continuous (fun p : ℝ × ℝ ↦ angularKernelA p.1 p.2 ^ 2) :=
    hU.pow 2
  exact (isOpen_lt continuous_const hU).inter (isOpen_lt hN hD)

theorem separatedRatio_mem_unit_of_mem_open {p : ℝ × ℝ}
    (hp : p ∈ separatedOpen) :
    separatedRatio p.1 p.2 ∈ Ioo (-1 : ℝ) 1 := by
  have hU := hp.1
  have hQ := hp.2
  have hU2 : 0 < angularKernelA p.1 p.2 ^ 2 := sq_pos_of_pos hU
  have habs :
      |separatedRatio p.1 p.2| =
        |4 * (1 - p.1 ^ 2) * (1 - p.2 ^ 2)| /
          angularKernelA p.1 p.2 ^ 2 := by
    unfold separatedRatio
    rw [abs_div]
    change |4 * (1 - p.1 ^ 2) * (1 - p.2 ^ 2)| /
        |angularKernelA p.1 p.2 ^ 2| = _
    rw [abs_of_pos hU2]
  have hlt : |separatedRatio p.1 p.2| < 1 := by
    rw [habs]
    exact (div_lt_one hU2).mpr hQ
  exact abs_lt.mp hlt

theorem mem_separatedOpen_of_physical_ratio_lt_one
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hU : 0 < angularKernelA s t)
    (hq : separatedRatio s t < 1) :
    (s,t) ∈ separatedOpen := by
  have hA := radiusSq_nonneg hs
  have hB := radiusSq_nonneg ht
  have hnum : 0 ≤ 4 * (1 - s ^ 2) * (1 - t ^ 2) := by positivity
  have hU2 : 0 < angularKernelA s t ^ 2 := sq_pos_of_pos hU
  constructor
  · exact hU
  · unfold separatedRatio at hq
    change 4 * (1 - s ^ 2) * (1 - t ^ 2) /
      angularKernelA s t ^ 2 < 1 at hq
    rw [div_lt_one hU2] at hq
    rw [abs_of_nonneg hnum]
    exact hq

/-- A single function on the entire plane.  On `separatedOpen` it equals
the polynomial even series, hence the latitude kernel on physical points. -/
noncomputable def separatedSmoothExtension (α : ℝ) (p : ℝ × ℝ) : ℝ :=
  angularKernelA p.1 p.2 ^ (α / 2) *
    scalarPowerSeries (separatedEvenCoefficient α)
      (separatedRatio p.1 p.2)

theorem separatedSmoothExtension_eq_evenSeries
    {α : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ separatedOpen) :
    separatedSmoothExtension α p = separatedEvenSeries α p.1 p.2 := by
  unfold separatedSmoothExtension scalarPowerSeries
  exact (separatedEvenSeries_eq_ratioSeries hp.1).symm

theorem separatedSmoothExtension_eq_evenSeries_of_Upos
    {α : ℝ} {p : ℝ × ℝ}
    (hU : 0 < angularKernelA p.1 p.2) :
    separatedSmoothExtension α p = separatedEvenSeries α p.1 p.2 := by
  unfold separatedSmoothExtension scalarPowerSeries
  exact (separatedEvenSeries_eq_ratioSeries hU).symm

theorem separatedSmoothExtension_eq_latitudeKernel
    {α : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ separatedOpen)
    (hs : p.1 ∈ Icc (-1 : ℝ) 1)
    (ht : p.2 ∈ Icc (-1 : ℝ) 1) :
    separatedSmoothExtension α p = latitudeKernel α p.1 p.2 := by
  rw [separatedSmoothExtension_eq_evenSeries hp]
  apply (latitudeKernel_eq_separatedEvenSeries hs ht hp.1 ?_).symm
  have hB0 : 0 ≤ angularKernelB p.1 p.2 := by
    unfold angularKernelB
    positivity
  have hQ : separatedRatio p.1 p.2 =
      (angularKernelB p.1 p.2 / angularKernelA p.1 p.2) ^ 2 := by
    rw [div_pow, angularKernelB_sq_eq_four_radiusSq hs ht]
    rfl
  have hq := separatedRatio_mem_unit_of_mem_open hp
  have hsq : (angularKernelB p.1 p.2 / angularKernelA p.1 p.2) ^ 2 < 1 := by
    rw [← hQ]
    exact hq.2
  have hsqabs : |angularKernelB p.1 p.2 / angularKernelA p.1 p.2| ^ 2 < 1 := by
    simpa only [sq_abs] using hsq
  nlinarith [abs_nonneg (angularKernelB p.1 p.2 / angularKernelA p.1 p.2)]

theorem separatedSmoothExtension_contDiffOn
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ContDiffOn ℝ 4 (separatedSmoothExtension α) separatedOpen := by
  apply (isOpen_separatedOpen.contDiffOn_iff).2
  intro p hp
  have hU : 0 < angularKernelA p.1 p.2 := hp.1
  have hUcd : ContDiffAt ℝ 4
      (fun x : ℝ × ℝ ↦ angularKernelA x.1 x.2) p := by
    unfold angularKernelA
    fun_prop
  have hNcd : ContDiffAt ℝ 4
      (fun x : ℝ × ℝ ↦
        4 * (1 - x.1 ^ 2) * (1 - x.2 ^ 2)) p := by
    fun_prop
  have hDcd : ContDiffAt ℝ 4
      (fun x : ℝ × ℝ ↦ angularKernelA x.1 x.2 ^ 2) p :=
    hUcd.pow 2
  have hQcd : ContDiffAt ℝ 4
      (fun x : ℝ × ℝ ↦ separatedRatio x.1 x.2) p := by
    unfold separatedRatio
    exact hNcd.div hDcd (pow_ne_zero 2 hU.ne')
  have hPow : ContDiffAt ℝ 4
      (fun x : ℝ × ℝ ↦ angularKernelA x.1 x.2 ^ (α / 2)) p :=
    hUcd.rpow_const_of_ne hU.ne'
  have hH := scalarPowerSeries_contDiffOn_four
    (separatedEvenCoefficient α) (abs_separatedEvenCoefficient_le_one hα0 hα2)
  have hHcd : ContDiffAt ℝ 4
      (scalarPowerSeries (separatedEvenCoefficient α))
      (separatedRatio p.1 p.2) :=
    hH.contDiffAt (isOpen_Ioo.mem_nhds (separatedRatio_mem_unit_of_mem_open hp))
  have hcomp : ContDiffAt ℝ 4
      (fun x : ℝ × ℝ ↦ scalarPowerSeries (separatedEvenCoefficient α)
        (separatedRatio x.1 x.2)) p := by
    exact hHcd.comp (f := fun x : ℝ × ℝ ↦ separatedRatio x.1 x.2) p hQcd
  change ContDiffAt ℝ 4
    (fun x : ℝ × ℝ ↦ angularKernelA x.1 x.2 ^ (α / 2) *
      scalarPowerSeries (separatedEvenCoefficient α)
        (separatedRatio x.1 x.2)) p
  exact hPow.mul hcomp

end BEMOC.Definitive
