import BEMOCFormalization.MainTheorem
import BEMOCFormalization.CapDiscrepancy
import BEMOCFormalization.Sobolev

namespace BEMOC.Definitive

/-- The Riesz exponent for the Sobolev corollary lies in the main theorem's open range. -/
theorem sobolev_exponent_range {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    0 < 2 * s - 2 ∧ 2 * s - 2 < 2 := by constructor <;> linarith

/-- Dividing the energy scale by N² gives the squared Sobolev error exponent. -/
theorem sobolev_normalized_exponent (s : ℝ) :
    (1 - (2 * s - 2) / 2) - 2 = -s := by ring

/-- Dividing by N² and then taking a square root gives the cap discrepancy exponent. -/
theorem cap_normalized_exponent : ((1 : ℝ) - 1 / 2 - 2) / 2 = -3 / 4 := by norm_num

/-- Explicit corollary assembly obligation, including distinctness and the geometric bridge. -/
def CapAssembly : Prop :=
  ConstructionFacts → MainTheorem 1 → DiamondStolarsky → BeckLowerBound →
    CapDiscrepancyCorollary

/-- Explicit Sobolev assembly obligation; supremum boundedness is not implicit. -/
def SobolevAssembly : Prop :=
  ∀ Y : HarmonicBasis, ∀ s : ℝ, 1 < s → s < 2 → ConstructionFacts →
    MainTheorem (2 * s - 2) → SobolevEmbedding Y s →
    SobolevEnergyComparison Y s → SobolevCorollary Y s

/-- Full requested scaffold destination, including existence of the harmonic model. -/
def DefinitiveTargets : Prop :=
  MainTheoremTarget ∧ CapDiscrepancyCorollary ∧ Nonempty HarmonicBasis ∧
    ∀ Y : HarmonicBasis, ∀ s : ℝ, 1 < s → s < 2 →
      SobolevCorollary Y s ∧ SobolevOptimality Y s

end BEMOC.Definitive
