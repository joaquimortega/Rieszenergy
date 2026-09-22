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


/-- Normalizing an energy estimate divides its real power by the square of the population. -/
theorem rpow_div_sq {x : ℝ} (hx : 0 < x) (a : ℝ) :
    x ^ a / x ^ 2 = x ^ (a - 2) := by
  rw [Real.rpow_sub hx]
  norm_num

/-- Squaring a positive-base real power doubles its exponent. -/
theorem sq_rpow {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

/-- Turn a squared power bound into a square-root bound with explicit positive constant. -/
theorem nonneg_le_sqrt_mul_rpow {e c x a : ℝ} (hc : 0 < c) (hx : 0 < x)
    (h : e ^ 2 ≤ c * x ^ (2 * a)) :
    e ≤ Real.sqrt c * x ^ a := by
  have hsq : (Real.sqrt c * x ^ a) ^ 2 = c * x ^ (2 * a) := by
    rw [mul_pow, Real.sq_sqrt hc.le, sq_rpow hx.le]
  have hp : 0 ≤ Real.sqrt c * x ^ a := by positivity
  nlinarith


/-- The actual cap corollary follows from its geometric identity and the universal lower bound. -/
theorem cap_assembly : CapAssembly := by
  intro hcon hmain hstol hbeck
  obtain ⟨c, hc, hlower⟩ := diamond_beck_lower_of hcon hbeck
  obtain ⟨C, hC, hupper⟩ := hmain
  refine ⟨c, Real.sqrt C, hc, Real.sqrt_pos.2 hC, ?_⟩
  intro N hN φ
  refine ⟨hlower N hN φ, ?_⟩
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hn2 : 0 < (N : ℝ) ^ 2 := by positivity
  have hd : 0 ≤ capDiscrepancySq (point N φ) := capDiscrepancySq_nonneg _
  have he := (hupper N hN φ).2
  have hs := hstol N hN φ
  have hp : (N : ℝ) ^ 2 * (N : ℝ) ^ (2 * (-(3 : ℝ) / 4)) = scale 1 N := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn]
    norm_num [scale]
  have he' : (N : ℝ) ^ 2 * capDiscrepancySq (point N φ) ≤ C * scale 1 N := by
    nlinarith [mul_nonneg (le_of_lt hn2) hd]
  have hsq : capDiscrepancy (point N φ) ^ 2 ≤
      C * (N : ℝ) ^ (2 * (-(3 : ℝ) / 4)) := by
    rw [capDiscrepancy, Real.sq_sqrt hd]
    apply (mul_le_mul_left hn2).mp
    calc
      (N : ℝ) ^ 2 * capDiscrepancySq (point N φ) ≤ C * scale 1 N := he'
      _ = (N : ℝ) ^ 2 * (C * (N : ℝ) ^ (2 * (-(3 : ℝ) / 4))) := by rw [← hp]; ring
  exact nonneg_le_sqrt_mul_rpow hC hn hsq

/-- The cap corollary now requires only the energy theorem and universal lower bound. -/
theorem cap_corollary_of_main_and_beck (hmain : MainTheorem 1)
    (hbeck : BeckLowerBound) : CapDiscrepancyCorollary :=
  cap_assembly constructionFacts hmain diamondStolarsky hbeck

/-- Conditional transfer from the actual spectral WCE comparison to the paper's decay rate. -/
theorem sobolev_assembly : SobolevAssembly := by
  intro Y s _hs1 _hs2 hcon hmain _hemb hcomp
  obtain ⟨A, hA, hcomp⟩ := hcomp
  obtain ⟨C, hC, hmain⟩ := hmain
  refine ⟨Real.sqrt (A * C), Real.sqrt_pos.2 (mul_pos hA hC), ?_⟩
  intro N hN φ
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hn2 : 0 < (N : ℝ) ^ 2 := by positivity
  let e : PointIndex N ≃ Fin N :=
    Fintype.equivFinOfCardEq (pointIndex_card_of_constructionFacts hcon N hN)
  have hcomparison := hcomp N (by omega) (point N φ ∘ e.symm)
  rw [sobolevWCE_comp_equiv, energy_comp_equiv] at hcomparison
  have hid : continuousEnergy (2 * s - 2) - energy (point N φ) (2 * s - 2) / (N : ℝ)^2 =
      deficit (2 * s - 2) N φ / (N : ℝ)^2 := by
    unfold deficit diamondEnergy
    field_simp
  rw [hid] at hcomparison
  have hpower : scale (2 * s - 2) N / (N : ℝ)^2 = (N : ℝ)^(-s) := by
    unfold scale
    rw [rpow_div_sq hn, sobolev_normalized_exponent]
  have hnormalized : deficit (2 * s - 2) N φ / (N : ℝ)^2 ≤ C * (N : ℝ)^(-s) := by
    calc
      deficit (2 * s - 2) N φ / (N : ℝ)^2 ≤ C * scale (2 * s - 2) N / (N : ℝ)^2 :=
        div_le_div_of_nonneg_right (hmain N hN φ).2 hn2.le
      _ = C * (N : ℝ)^(-s) := by rw [mul_div_assoc, hpower]
  have hsq : sobolevWCE Y s (point N φ)^2 ≤ (A * C) * (N : ℝ)^(2 * (-s / 2)) := by
    have hh := hcomparison.trans (mul_le_mul_of_nonneg_left hnormalized hA.le)
    convert hh using 1 <;> ring
  exact nonneg_le_sqrt_mul_rpow (mul_pos hA hC) hn hsq

end BEMOC.Definitive
