import BEMOCFormalization.LatitudePointwiseAssembly
import BEMOCFormalization.LatitudeRowArithmetic

/-!
# Final latitude case-constant assembly

The local analytic arguments naturally produce different constants in the
eight geometric fields used by the comparable and ordered unequal-scale
interfaces.  This file performs the last uniform-constant bookkeeping once
and for all.
-/

namespace BEMOC

/-- One positive constant dominating all four comparable and all four
ordered unequal-scale case constants. -/
noncomputable def latitudeGeometricCaseConstant
    (Cpc Ccc Coc Csc Cpu Ccu Cou Csu : ℝ) : ℝ :=
  1 + Cpc + Ccc + Coc + Csc + Cpu + Ccu + Cou + Csu

theorem latitudeGeometricCaseConstant_pos
    {Cpc Ccc Coc Csc Cpu Ccu Cou Csu : ℝ}
    (hpc : 0 ≤ Cpc) (hcc : 0 ≤ Ccc)
    (hoc : 0 ≤ Coc) (hsc : 0 ≤ Csc)
    (hpu : 0 ≤ Cpu) (hcu : 0 ≤ Ccu)
    (hou : 0 ≤ Cou) (hsu : 0 ≤ Csu) :
    0 < latitudeGeometricCaseConstant
      Cpc Ccc Coc Csc Cpu Ccu Cou Csu := by
  unfold latitudeGeometricCaseConstant
  linarith

/-- Assemble case-specific analytic estimates into the exact complete block
interface consumed by the latitude summation theorem. -/
theorem hasCompleteLatitudeBlockEstimate_of_geometric_case_bounds
    {α Cpc Ccc Coc Csc Cpu Ccu Cou Csu : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (hpc0 : 0 ≤ Cpc) (hcc0 : 0 ≤ Ccc)
    (hoc0 : 0 ≤ Coc) (hsc0 : 0 ≤ Csc)
    (hpu0 : 0 ≤ Cpu) (hcu0 : 0 ≤ Ccu)
    (hou0 : 0 ≤ Cou) (hsu0 : 0 ≤ Csu)
    (hpc : ∀ j k, PolarLatitudePair N j k →
      ComparableLatitudeScales N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α Cpc N j k)
    (hcc : ∀ j k, CentralLatitudePair N j k →
      ComparableLatitudeScales N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α Ccc N j k)
    (hoc : ∀ j k, SmoothOppositeLatitudePair N j k →
      ComparableLatitudeScales N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α Coc N j k)
    (hsc : ∀ j k, ComparableSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α Csc N j k)
    (hpu : ∀ j k, PolarLatitudePair N j k →
      2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α Cpu N j k)
    (hcu : ∀ j k, CentralLatitudePair N j k →
      2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α Ccu N j k)
    (hou : ∀ j k, SmoothOppositeLatitudePair N j k →
      2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α Cou N j k)
    (hsu : ∀ j k, LeftSmallSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α Csu N j k) :
    HasCompleteLatitudeBlockEstimate α N
      (latitudeGeometricCaseConstant
          Cpc Ccc Coc Csc Cpu Ccu Cou Csu *
          latitudeComparableSumConstant α +
        latitudeGeometricCaseConstant
          Cpc Ccc Coc Csc Cpu Ccu Cou Csu *
          latitudeComparableSumConstant α +
        2 * latitudeGeometricCaseConstant
          Cpc Ccc Coc Csc Cpu Ccu Cou Csu) := by
  let C := latitudeGeometricCaseConstant
    Cpc Ccc Coc Csc Cpu Ccu Cou Csu
  have hC : 0 < C :=
    latitudeGeometricCaseConstant_pos hpc0 hcc0 hoc0 hsc0
      hpu0 hcu0 hou0 hsu0
  have hpcC : Cpc ≤ C := by
    dsimp [C, latitudeGeometricCaseConstant]
    linarith
  have hccC : Ccc ≤ C := by
    dsimp [C, latitudeGeometricCaseConstant]
    linarith
  have hocC : Coc ≤ C := by
    dsimp [C, latitudeGeometricCaseConstant]
    linarith
  have hscC : Csc ≤ C := by
    dsimp [C, latitudeGeometricCaseConstant]
    linarith
  have hpuC : Cpu ≤ C := by
    dsimp [C, latitudeGeometricCaseConstant]
    linarith
  have hcuC : Ccu ≤ C := by
    dsimp [C, latitudeGeometricCaseConstant]
    linarith
  have houC : Cou ≤ C := by
    dsimp [C, latitudeGeometricCaseConstant]
    linarith
  have hsuC : Csu ≤ C := by
    dsimp [C, latitudeGeometricCaseConstant]
    linarith
  have hcomp : HasComparableLatitudeBlockBound α N C :=
    hasComparableLatitudeBlockBound_of_geometric_cases
      (fun j k hp hc ↦
        (hpc j k hp hc).trans
          (comparableLatitudeBlockMajorant_mono hpcC))
      (fun j k hp hc ↦
        (hcc j k hp hc).trans
          (comparableLatitudeBlockMajorant_mono hccC))
      (fun j k hp hc ↦
        (hoc j k hp hc).trans
          (comparableLatitudeBlockMajorant_mono hocC))
      (fun j k hp ↦
        (hsc j k hp).trans
          (comparableLatitudeBlockMajorant_mono hscC))
  have hunequal : HasUnequalLatitudeBlockBound α N C :=
    hasUnequalLatitudeBlockBound_of_geometric_cases
      (fun j k hp hs ↦
        (hpu j k hp hs).trans
          (unequalLatitudeBlockMajorant_mono hpuC))
      (fun j k hp hs ↦
        (hcu j k hp hs).trans
          (unequalLatitudeBlockMajorant_mono hcuC))
      (fun j k hp hs ↦
        (hou j k hp hs).trans
          (unequalLatitudeBlockMajorant_mono houC))
      (fun j k hp ↦
        (hsu j k hp).trans
          (unequalLatitudeBlockMajorant_mono hsuC))
  simpa [C] using
    hasCompleteLatitudeBlockEstimate_of_pointwise
      hα0 hα2 hC.le hM hcomp hunequal

end BEMOC
