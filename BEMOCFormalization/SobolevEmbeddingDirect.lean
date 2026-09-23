import BEMOCFormalization.SobolevKernel
import BEMOCFormalization.HarmonicAddition
import Mathlib.Analysis.PSeries

/-! Direct Sobolev embedding from the harmonic addition diagonal. -/

open scoped BigOperators

namespace BEMOC.Definitive

/-- In dimension two, the spectral evaluation majorant is summable for
every Sobolev exponent above one. -/
theorem summable_spectral_dimension_weight {s : ℝ} (hs : 1 < s) :
    Summable (fun ℓ : ℕ =>
      (1 + (ℓ : ℝ) * (ℓ + 1)) ^ (-s) * (2 * (ℓ : ℝ) + 1)) := by
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (1 - 2 * s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable (fun ℓ : ℕ =>
      (3 : ℝ) * ((ℓ + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) :=
    (hp.comp_injective (fun _ _ h => Nat.add_right_cancel h)).mul_left 3
  have htail : Summable (fun ℓ : ℕ =>
      (1 + ((ℓ + 1 : ℕ) : ℝ) * ((ℓ + 1 : ℕ) + 1)) ^ (-s) *
        (2 * ((ℓ + 1 : ℕ) : ℝ) + 1)) := by
    apply Summable.of_nonneg_of_le
    · intro ℓ
      positivity
    · intro ℓ
      let n : ℝ := ((ℓ + 1 : ℕ) : ℝ)
      have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le ℓ)
      have hbase : n ^ 2 ≤ 1 + n * (n + 1) := by nlinarith
      have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < n ^ 2)
        hbase (by linarith : -s ≤ 0)
      have hdim : 2 * n + 1 ≤ 3 * n := by linarith
      have hpow0 : 0 ≤ (n ^ 2) ^ (-s) := Real.rpow_nonneg (by positivity) _
      have hbound := mul_le_mul hpow hdim (by positivity) hpow0
      have hident : (n ^ 2) ^ (-s) * (3 * n) =
          3 * n ^ (1 - 2 * s) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ n)]
        norm_num only [Nat.cast_ofNat]
        rw [show (2 : ℝ) * -s = -2 * s by ring]
        rw [show 1 - 2 * s = -2 * s + 1 by ring,
          Real.rpow_add (by positivity : 0 < n)]
        simp only [Real.rpow_one]
        ring
      simpa only [n] using hbound.trans_eq hident
    · exact hshift
  exact (summable_nat_add_iff 1).mp htail

/-- The addition diagonal makes the spectral evaluation norm independent of
the point, so the preceding p-series gives a uniform bound. -/
theorem spectralEvalTerm_uniform_bound_of_addition
    (Y : HarmonicBasis) {s : ℝ} (hs : 1 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : Sphere,
      Summable (spectralEvalTerm Y s x) ∧
        (∑' ℓ, spectralEvalTerm Y s x ℓ) ≤ K := by
  let w : ℕ → ℝ := fun ℓ =>
    (1 + (ℓ : ℝ) * (ℓ + 1)) ^ (-s) * (2 * (ℓ : ℝ) + 1)
  have hw : Summable w := summable_spectral_dimension_weight hs
  have hw0 : ∀ ℓ, 0 ≤ w ℓ := by intro ℓ; dsimp [w]; positivity
  let K : ℝ := 1 + ∑' ℓ, w ℓ
  have hK : 0 < K := by
    dsimp [K]
    have hnonneg : 0 ≤ ∑' ℓ, w ℓ := tsum_nonneg hw0
    linarith
  refine ⟨K, hK, ?_⟩
  intro x
  have heq : spectralEvalTerm Y s x = w := by
    funext ℓ
    unfold spectralEvalTerm w
    rw [harmonicAddition_diag Y ℓ x]
  rw [heq]
  exact ⟨hw, by dsimp [K]; linarith⟩

/-- Actual continuous Sobolev representatives are uniformly bounded directly
from the dimension-weight p-series, with no distance-kernel premise. -/
theorem sobolevEmbedding_of_harmonicAddition
    (Y : HarmonicBasis) {s : ℝ} (hs : 1 < s) :
    SobolevEmbedding Y s := by
  obtain ⟨K, hK, hEval⟩ := spectralEvalTerm_uniform_bound_of_addition Y hs
  refine ⟨Real.sqrt K, Real.sqrt_pos.2 hK, ?_⟩
  intro f hf x
  have hfinite (L : ℕ) : (harmonicPartialSum Y f L x) ^ 2 ≤ K := by
    have hn : (∑ ℓ ∈ Finset.range L, sobolevNormTerm Y s f ℓ) ≤ 1 :=
      (hf.1.sum_le_tsum _ (fun ℓ _ => sobolevNormTerm_nonneg Y s f ℓ)).trans hf.2
    have he : (∑ ℓ ∈ Finset.range L, spectralEvalTerm Y s x ℓ) ≤ K :=
      ((hEval x).1.sum_le_tsum _
        (fun ℓ _ => spectralEvalTerm_nonneg Y s x ℓ)).trans (hEval x).2
    have he0 : 0 ≤ ∑ ℓ ∈ Finset.range L, spectralEvalTerm Y s x ℓ :=
      Finset.sum_nonneg (fun ℓ _ => spectralEvalTerm_nonneg Y s x ℓ)
    rw [harmonicPartialSum_apply]
    exact (finite_spectral_eval_cauchy Y s f x L).trans (by
      nlinarith [mul_le_mul_of_nonneg_right hn he0])
  have hlim : Filter.Tendsto (fun L => harmonicPartialSum Y f L x)
      Filter.atTop (nhds (f x)) :=
    (continuous_eval_const x).tendsto f |>.comp
      (harmonicPartialSum_tendsto_of_evalBound Y s f hf.1 K hK hEval)
  have hsq : (f x) ^ 2 ≤ K :=
    le_of_tendsto (hlim.pow 2) (Filter.Eventually.of_forall hfinite)
  exact (Real.le_sqrt (abs_nonneg _) hK.le).2 (by simpa only [sq_abs] using hsq)

end BEMOC.Definitive
