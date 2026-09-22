import BEMOCFormalization.LatitudeCentralNeighboringGeometry

/-!
# Reduced-cusp insertion on central neighboring rectangles

The geometry file proves that the central transition lies in the unit cusp
chart.  These wrappers feed that fact into the three actual kernel
decompositions.
-/

open Set

namespace BEMOC

theorem centralComparable_neighboring_rectangle_chart
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧
      normalizedLatitudeGap s t ≤ 1 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have habs :=
    abs_centralComparable_neighboring_rectangle_le hM hcentral hcomp
      hneigh hs ht
  have hsides := abs_le.mp habs.1
  have htides := abs_le.mp habs.2
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    centralComparable_neighboring_rectangle_normalizedLatitudeGap_le_one
      hM hcentral hcomp hneigh hs ht⟩

theorem latitudeKernel_eq_centralNeighboringUpperAnalytic_add_branch
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hst : s ≠ t) :
    latitudeKernel α s t =
      neighboringUpperAnalyticKernel α s t +
        neighboringUpperBranchKernel α s t := by
  have hchart :=
    centralComparable_neighboring_rectangle_chart hM hcentral hcomp
      hneigh hs ht
  exact latitudeKernel_eq_neighboringUpperAnalytic_add_branch
    hα1 hα2 hchart.1 hchart.2.1 hst hchart.2.2

theorem latitudeKernel_eq_centralNeighboringLowerAnalytic_add_branch
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hst : s ≠ t) :
    latitudeKernel α s t =
      neighboringLowerAnalyticKernel α s t +
        neighboringLowerBranchKernel α s t := by
  have hchart :=
    centralComparable_neighboring_rectangle_chart hM hcentral hcomp
      hneigh hs ht
  exact latitudeKernel_eq_neighboringLowerAnalytic_add_branch
    hα0 hα1 hchart.1 hchart.2.1 hst hchart.2.2

theorem latitudeKernel_one_eq_centralNeighboringResonantModel_add_branch
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hst : s ≠ t) :
    latitudeKernel 1 s t =
      neighboringResonantModelKernel s t +
        neighboringResonantHigherBranchKernel s t := by
  have hchart :=
    centralComparable_neighboring_rectangle_chart hM hcentral hcomp
      hneigh hs ht
  exact latitudeKernel_one_eq_neighboringResonantModel_add_branch
    hchart.1 hchart.2.1 hst hchart.2.2

end BEMOC
