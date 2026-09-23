import BEMOCFormalization.SobolevEmbeddingDirect
import BEMOCFormalization.HarmonicL2

/-! Spectral synthesis of a Sobolev `L²` class into its continuous representative. -/

open scoped BigOperators
open MeasureTheory

namespace BEMOC.Definitive

/-- Abstract harmonic coefficients, later instantiated with Fourier coefficients
of an `L²` class. -/
abbrev HarmonicCoefficients := (ℓ : ℕ) → Fin (2 * ℓ + 1) → ℝ

/-- The weighted square of one degree of an abstract harmonic sequence. -/
noncomputable def harmonicSequenceNormTerm (s : ℝ)
    (a : HarmonicCoefficients) (ℓ : ℕ) : ℝ :=
  (1 + (ℓ : ℝ) * (ℓ + 1)) ^ s * ∑ k, a ℓ k ^ 2

theorem harmonicSequenceNormTerm_nonneg (s : ℝ)
    (a : HarmonicCoefficients) (ℓ : ℕ) :
    0 ≤ harmonicSequenceNormTerm s a ℓ := by
  unfold harmonicSequenceNormTerm
  positivity

/-- Finite harmonic synthesis of an arbitrary coefficient sequence. -/
noncomputable def harmonicSynthesis (Y : HarmonicBasis)
    (a : HarmonicCoefficients) (L : ℕ) : C(Sphere, ℝ) :=
  ∑ ℓ ∈ Finset.range L,
    ∑ k : Fin (2 * ℓ + 1), a ℓ k • Y.function ℓ k

theorem harmonicSynthesis_apply (Y : HarmonicBasis)
    (a : HarmonicCoefficients) (L : ℕ) (x : Sphere) :
    harmonicSynthesis Y a L x =
      ∑ ℓ ∈ Finset.range L, ∑ k : Fin (2 * ℓ + 1),
        a ℓ k * Y.function ℓ k x := by
  simp [harmonicSynthesis, smul_eq_mul]

theorem harmonicCoefficient_harmonicSynthesis (Y : HarmonicBasis)
    (a : HarmonicCoefficients) (L m : ℕ) (j : Fin (2 * m + 1)) :
    harmonicCoefficient Y (harmonicSynthesis Y a L) m j =
      if m < L then a m j else 0 := by
  classical
  change (harmonicCoefficientLinearMap Y m j)
    (∑ ℓ ∈ Finset.range L,
      ∑ k : Fin (2 * ℓ + 1), a ℓ k • Y.function ℓ k) = _
  simp only [map_sum, map_smul]
  change (∑ ℓ ∈ Finset.range L, ∑ k : Fin (2 * ℓ + 1),
    a ℓ k * harmonicCoefficient Y (Y.function ℓ k) m j) = _
  simp_rw [harmonicCoefficient_basis]
  simp only [mul_ite, mul_one, mul_zero]
  have hsym (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
      (if ℓ = m ∧ (k : ℕ) = j then a ℓ k else 0) =
      (if m = ℓ ∧ (j : ℕ) = k then a ℓ k else 0) := by
    simp only [eq_comm]
  simp_rw [hsym]
  have hcollapse :
      (∑ ℓ ∈ Finset.range L, ∑ k : Fin (2 * ℓ + 1),
        if m = ℓ ∧ (j : ℕ) = k then a ℓ k else 0) =
      ∑ ℓ ∈ Finset.range L, if m = ℓ then a m j else 0 := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    by_cases h : m = ℓ
    · subst ℓ
      simp only [and_self, ite_true]
      simp [Finset.sum_ite_eq', Fin.val_inj]
    · simp [h]
  rw [hcollapse]
  by_cases hm : m < L
  · simp [hm, eq_comm, Fin.val_inj]
  · simp [hm, eq_comm]

/-- The manuscript's spectral norm term for an actual `L²` equivalence class. -/
noncomputable def l2SobolevNormTerm (Y : HarmonicBasis) (s : ℝ)
    (f : Lp ℝ 2 sigma) (ℓ : ℕ) : ℝ :=
  harmonicSequenceNormTerm s (fun ℓ k => l2HarmonicCoefficient Y f ℓ k) ℓ

/-- Unit ball in the `L²`-defined spherical Sobolev space. -/
def L2SobolevUnitBall (Y : HarmonicBasis) (s : ℝ)
    (f : Lp ℝ 2 sigma) : Prop :=
  Summable (l2SobolevNormTerm Y s f) ∧
    (∑' ℓ, l2SobolevNormTerm Y s f ℓ) ≤ 1

theorem l2SobolevNormTerm_nonneg (Y : HarmonicBasis) (s : ℝ)
    (f : Lp ℝ 2 sigma) (ℓ : ℕ) :
    0 ≤ l2SobolevNormTerm Y s f ℓ :=
  harmonicSequenceNormTerm_nonneg s _ ℓ

theorem l2SobolevNormTerm_continuousToLp (Y : HarmonicBasis)
    (s : ℝ) (g : C(Sphere, ℝ)) (ℓ : ℕ) :
    l2SobolevNormTerm Y s (continuousToLp g) ℓ =
      sobolevNormTerm Y s g ℓ := by
  simp [l2SobolevNormTerm, harmonicSequenceNormTerm, sobolevNormTerm,
    l2HarmonicCoefficient_continuousToLp]

theorem continuous_to_L2SobolevUnitBall (Y : HarmonicBasis)
    (s : ℝ) (g : C(Sphere, ℝ))
    (hg : SobolevUnitBall Y s g) :
    L2SobolevUnitBall Y s (continuousToLp g) := by
  have heq : l2SobolevNormTerm Y s (continuousToLp g) =
      sobolevNormTerm Y s g := by
    funext ℓ
    exact l2SobolevNormTerm_continuousToLp Y s g ℓ
  simpa only [L2SobolevUnitBall, SobolevUnitBall, heq] using hg

theorem harmonicSynthesis_difference_sq_le (Y : HarmonicBasis)
    (s : ℝ) (a : HarmonicCoefficients) (x : Sphere)
    {L M : ℕ} (hLM : L ≤ M) :
    (harmonicSynthesis Y a M x - harmonicSynthesis Y a L x) ^ 2 ≤
      (∑ ℓ ∈ Finset.Ico L M, harmonicSequenceNormTerm s a ℓ) *
        (∑ ℓ ∈ Finset.Ico L M, spectralEvalTerm Y s x ℓ) := by
  have h := finite_spectral_eval_cauchy_finset Y s
    (harmonicSynthesis Y a M) x (Finset.Ico L M)
  have hcoeff (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Ico L M)
      (k : Fin (2 * ℓ + 1)) :
      harmonicCoefficient Y (harmonicSynthesis Y a M) ℓ k = a ℓ k := by
    rw [harmonicCoefficient_harmonicSynthesis]
    simp [Finset.mem_Ico.mp hℓ |>.2]
  have hleft :
      (∑ ℓ ∈ Finset.Ico L M, ∑ k : Fin (2 * ℓ + 1),
        harmonicCoefficient Y (harmonicSynthesis Y a M) ℓ k *
          Y.function ℓ k x) =
      harmonicSynthesis Y a M x - harmonicSynthesis Y a L x := by
    rw [harmonicSynthesis_apply, harmonicSynthesis_apply,
      ← Finset.sum_Ico_eq_sub _ hLM]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    apply Finset.sum_congr rfl
    intro k hk
    rw [hcoeff ℓ hℓ k]
  have hright :
      (∑ ℓ ∈ Finset.Ico L M,
        sobolevNormTerm Y s (harmonicSynthesis Y a M) ℓ) =
      ∑ ℓ ∈ Finset.Ico L M, harmonicSequenceNormTerm s a ℓ := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    simp [sobolevNormTerm, harmonicSequenceNormTerm, hcoeff ℓ hℓ]
  rw [hleft, hright] at h
  exact h

/-- The weighted Fourier sequence yields uniformly Cauchy continuous
harmonic sums whenever point evaluation has a uniform spectral bound. -/
theorem harmonicSynthesis_cauchy_of_evalBound (Y : HarmonicBasis) (s : ℝ)
    (a : HarmonicCoefficients)
    (ha : Summable (harmonicSequenceNormTerm s a))
    (K : ℝ) (hK : 0 < K)
    (hEval : ∀ x : Sphere, Summable (spectralEvalTerm Y s x) ∧
      (∑' ℓ, spectralEvalTerm Y s x ℓ) ≤ K) :
    CauchySeq (harmonicSynthesis Y a) := by
  let T : ℝ := ∑' ℓ, harmonicSequenceNormTerm s a ℓ
  have htail : Filter.Tendsto (fun L => T -
      ∑ ℓ ∈ Finset.range L, harmonicSequenceNormTerm s a ℓ)
      Filter.atTop (nhds 0) := by
    have hTconst : Filter.Tendsto (fun _ : ℕ => T) Filter.atTop (nhds T) :=
      tendsto_const_nhds
    simpa [T] using hTconst.sub ha.tendsto_sum_tsum_nat
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hδ : 0 < ε ^ 2 / (2 * K) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (htail.eventually (eventually_lt_nhds hδ))
  refine ⟨N, ?_⟩
  have hordered (L M : ℕ) (hLM : L ≤ M) (hLN : N ≤ L) :
      dist (harmonicSynthesis Y a M) (harmonicSynthesis Y a L) < ε := by
    rw [dist_eq_norm]
    apply ((harmonicSynthesis Y a M - harmonicSynthesis Y a L).norm_lt_iff hε).2
    intro x
    have hNormIco : (∑ ℓ ∈ Finset.Ico L M, harmonicSequenceNormTerm s a ℓ) <
        ε ^ 2 / (2 * K) := by
      rw [Finset.sum_Ico_eq_sub _ hLM]
      have hM := ha.sum_le_tsum (Finset.range M)
        (fun ℓ _ => harmonicSequenceNormTerm_nonneg s a ℓ)
      have hL := hN L hLN
      dsimp [T] at hL
      linarith
    have hNormNonneg : 0 ≤ ∑ ℓ ∈ Finset.Ico L M,
        harmonicSequenceNormTerm s a ℓ :=
      Finset.sum_nonneg (fun ℓ _ => harmonicSequenceNormTerm_nonneg s a ℓ)
    have hEvalIco : (∑ ℓ ∈ Finset.Ico L M, spectralEvalTerm Y s x ℓ) ≤ K :=
      ((hEval x).1.sum_le_tsum _
        (fun ℓ _ => spectralEvalTerm_nonneg Y s x ℓ)).trans (hEval x).2
    have hsq := harmonicSynthesis_difference_sq_le Y s a x hLM
    have hprod :
        (∑ ℓ ∈ Finset.Ico L M, harmonicSequenceNormTerm s a ℓ) *
          (∑ ℓ ∈ Finset.Ico L M, spectralEvalTerm Y s x ℓ) < ε ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hEvalIco hNormNonneg
      have h2 := mul_lt_mul_of_pos_right hNormIco hK
      have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
      nlinarith [div_mul_cancel₀ (ε ^ 2) (show 2 * K ≠ 0 by positivity)]
    have hreal : |harmonicSynthesis Y a M x - harmonicSynthesis Y a L x| < ε := by
      nlinarith [sq_abs (harmonicSynthesis Y a M x - harmonicSynthesis Y a L x),
        abs_nonneg (harmonicSynthesis Y a M x - harmonicSynthesis Y a L x)]
    simpa [Real.norm_eq_abs] using hreal
  intro m hm n hn
  by_cases hnm : n ≤ m
  · exact hordered n m hnm hn
  · rw [dist_comm]
    exact hordered m n (le_of_not_ge hnm) hm

/-- Synthesis has a continuous limit whose Fourier coefficients are precisely
the prescribed abstract sequence. -/
theorem harmonicSynthesis_limit (Y : HarmonicBasis) (s : ℝ)
    (a : HarmonicCoefficients)
    (ha : Summable (harmonicSequenceNormTerm s a))
    (K : ℝ) (hK : 0 < K)
    (hEval : ∀ x : Sphere, Summable (spectralEvalTerm Y s x) ∧
      (∑' ℓ, spectralEvalTerm Y s x ℓ) ≤ K) :
    ∃ g : C(Sphere, ℝ),
      Filter.Tendsto (harmonicSynthesis Y a) Filter.atTop (nhds g) ∧
        ∀ ℓ k, harmonicCoefficient Y g ℓ k = a ℓ k := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete
    (harmonicSynthesis_cauchy_of_evalBound Y s a ha K hK hEval)
  refine ⟨g, hg, ?_⟩
  intro ℓ k
  have hlim : Filter.Tendsto
      (fun L => harmonicCoefficient Y (harmonicSynthesis Y a L) ℓ k)
      Filter.atTop (nhds (harmonicCoefficient Y g ℓ k)) := by
    exact ((harmonicCoefficientLinearMap_continuous Y ℓ k).tendsto g).comp hg
  have hconst : Filter.Tendsto
      (fun L => harmonicCoefficient Y (harmonicSynthesis Y a L) ℓ k)
      Filter.atTop (nhds (a ℓ k)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop (ℓ + 1)] with L hL
    rw [harmonicCoefficient_harmonicSynthesis]
    simp [show ℓ < L by omega]
  exact tendsto_nhds_unique hlim hconst

/-- Every `L²`-defined spectral Sobolev unit vector above the embedding
threshold has a unique continuous representative, with exactly the same
harmonic coefficients and spectral unit-ball condition. -/
theorem l2Sobolev_continuousRepresentative
    (Y : HarmonicBasis) {s : ℝ} (hs : 1 < s)
    (f : Lp ℝ 2 sigma) (hf : L2SobolevUnitBall Y s f) :
    ∃! g : C(Sphere, ℝ),
      (g : Sphere → ℝ) =ᵐ[sigma] (f : Sphere → ℝ) ∧
        SobolevUnitBall Y s g := by
  let a : HarmonicCoefficients := fun ℓ k => l2HarmonicCoefficient Y f ℓ k
  have ha : Summable (harmonicSequenceNormTerm s a) := hf.1
  obtain ⟨K, hK, hEval⟩ := spectralEvalTerm_uniform_bound_of_addition Y hs
  obtain ⟨g, -, hcoeff⟩ := harmonicSynthesis_limit Y s a ha K hK hEval
  have hnorm : sobolevNormTerm Y s g = l2SobolevNormTerm Y s f := by
    funext ℓ
    simp [sobolevNormTerm, l2SobolevNormTerm,
      harmonicSequenceNormTerm, a, hcoeff]
  have hball : SobolevUnitBall Y s g := by
    simpa only [SobolevUnitBall, hnorm] using hf
  have hLp : continuousToLp g = f := by
    apply l2HarmonicCoefficient_injective Y
    intro ℓ k
    rw [l2HarmonicCoefficient_continuousToLp, hcoeff]
  have hae : (g : Sphere → ℝ) =ᵐ[sigma] (f : Sphere → ℝ) := by
    rw [← hLp]
    exact (continuousToLp_ae g).symm
  refine ⟨g, ⟨hae, hball⟩, ?_⟩
  intro g' hg'
  have hLp' : continuousToLp g' = f := by
    apply Lp.ext
    filter_upwards [continuousToLp_ae g', hg'.1] with x hx hy
    exact hx.trans hy
  apply continuousToLp_injective
  rw [hLp', hLp]

/-- An almost-everywhere continuous representative has exactly the same
harmonic Fourier coefficients as its `L²` equivalence class. -/
theorem harmonicCoefficient_eq_l2_of_ae (Y : HarmonicBasis)
    (f : Lp ℝ 2 sigma) (g : C(Sphere, ℝ))
    (hfg : (g : Sphere → ℝ) =ᵐ[sigma] (f : Sphere → ℝ))
    (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    harmonicCoefficient Y g ℓ k = l2HarmonicCoefficient Y f ℓ k := by
  have hLp : continuousToLp g = f := by
    apply Lp.ext
    filter_upwards [continuousToLp_ae g, hfg] with x hx hy
    exact hx.trans hy
  rw [← hLp, l2HarmonicCoefficient_continuousToLp]

/-- The weighted degree contribution is unchanged by choosing the unique
continuous representative. -/
theorem sobolevNormTerm_eq_l2_of_ae (Y : HarmonicBasis)
    (s : ℝ) (f : Lp ℝ 2 sigma) (g : C(Sphere, ℝ))
    (hfg : (g : Sphere → ℝ) =ᵐ[sigma] (f : Sphere → ℝ))
    (ℓ : ℕ) :
    sobolevNormTerm Y s g ℓ = l2SobolevNormTerm Y s f ℓ := by
  simp [sobolevNormTerm, l2SobolevNormTerm, harmonicSequenceNormTerm,
    harmonicCoefficient_eq_l2_of_ae Y f g hfg]

end BEMOC.Definitive
