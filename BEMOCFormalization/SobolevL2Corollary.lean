import BEMOCFormalization.SobolevL2
import BEMOCFormalization.SobolevMomentSpectral
import BEMOCFormalization.Corollaries

/-! Cubature on the manuscript's genuine `L²` spectral Sobolev class. The
unique continuous representative supplies every point value. -/

open scoped BigOperators
open MeasureTheory

namespace BEMOC.Definitive

/-- The unique continuous representative of an `L²` Sobolev unit-ball class. -/
noncomputable def l2SobolevRepresentative (Y : HarmonicBasis) {s : ℝ}
    (hs : 1 < s) (f : Lp ℝ 2 sigma) (hf : L2SobolevUnitBall Y s f) :
    C(Sphere, ℝ) :=
  Classical.choose (l2Sobolev_continuousRepresentative Y hs f hf)

theorem l2SobolevRepresentative_spec (Y : HarmonicBasis) {s : ℝ}
    (hs : 1 < s) (f : Lp ℝ 2 sigma) (hf : L2SobolevUnitBall Y s f) :
    ((l2SobolevRepresentative Y hs f hf : Sphere → ℝ) =ᵐ[sigma]
      (f : Sphere → ℝ)) ∧
      SobolevUnitBall Y s (l2SobolevRepresentative Y hs f hf) :=
  (Classical.choose_spec (l2Sobolev_continuousRepresentative Y hs f hf)).1

theorem l2SobolevRepresentative_unique (Y : HarmonicBasis) {s : ℝ}
    (hs : 1 < s) (f : Lp ℝ 2 sigma) (hf : L2SobolevUnitBall Y s f)
    (g : C(Sphere, ℝ))
    (hg : ((g : Sphere → ℝ) =ᵐ[sigma] (f : Sphere → ℝ)) ∧
      SobolevUnitBall Y s g) :
    l2SobolevRepresentative Y hs f hf = g :=
  (l2Sobolev_continuousRepresentative Y hs f hf).unique
    (l2SobolevRepresentative_spec Y hs f hf) hg

/-- Every genuine `L²` class in the spectral unit ball participates in this
worst-case error; quadrature evaluates its unique continuous representative. -/
noncomputable def l2SobolevWCE {ι : Type} [Fintype ι]
    (Y : HarmonicBasis) {s : ℝ} (hs : 1 < s) (X : ι → Sphere) : ℝ :=
  sSup {e : ℝ | ∃ f : Lp ℝ 2 sigma,
    ∃ hf : L2SobolevUnitBall Y s f,
      e = |quadratureError X (l2SobolevRepresentative Y hs f hf)|}

/-- Diamond cubature bound for the genuine `L²` spectral unit ball. -/
def L2SobolevCorollary (Y : HarmonicBasis) (s : ℝ) (hs : 1 < s) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N,
    l2SobolevWCE Y hs (point N φ) ≤ C * (N : ℝ) ^ (-s / 2)

/-- Universal lower bound on the genuine `L²` spectral unit ball. -/
def L2SobolevOptimality (Y : HarmonicBasis) (s : ℝ) (hs : 1 < s) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ X : Fin N → Sphere,
    Function.Injective X → c * (N : ℝ) ^ (-s / 2) ≤ l2SobolevWCE Y hs X

/-- Riesz-deficit comparison with the genuine `L²` spectral WCE. -/
def L2SobolevEnergyComparison (Y : HarmonicBasis) (s : ℝ) (hs : 1 < s) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 0 < N → ∀ X : Fin N → Sphere,
    l2SobolevWCE Y hs X ^ 2 ≤
      A * (continuousEnergy (2 * s - 2) - energy X (2 * s - 2) / (N : ℝ) ^ 2)

/-- A representative has exactly the `L²` Fourier coefficients of its class. -/
theorem l2HarmonicCoefficient_eq_representative (Y : HarmonicBasis)
    (f : Lp ℝ 2 sigma) (g : C(Sphere, ℝ))
    (hfg : (g : Sphere → ℝ) =ᵐ[sigma] (f : Sphere → ℝ))
    (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    l2HarmonicCoefficient Y f ℓ k = harmonicCoefficient Y g ℓ k := by
  unfold l2HarmonicCoefficient harmonicCoefficient
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

/-- The spectral norm terms agree without any renormalization. -/
theorem l2SobolevNormTerm_eq_representative (Y : HarmonicBasis) (s : ℝ)
    (f : Lp ℝ 2 sigma) (g : C(Sphere, ℝ))
    (hfg : (g : Sphere → ℝ) =ᵐ[sigma] (f : Sphere → ℝ)) (ℓ : ℕ) :
    l2SobolevNormTerm Y s f ℓ = sobolevNormTerm Y s g ℓ := by
  simp [l2SobolevNormTerm, harmonicSequenceNormTerm, sobolevNormTerm,
    l2HarmonicCoefficient_eq_representative Y f g hfg]

theorem l2SobolevNormTerm_representative (Y : HarmonicBasis) {s : ℝ}
    (hs : 1 < s) (f : Lp ℝ 2 sigma) (hf : L2SobolevUnitBall Y s f)
    (ℓ : ℕ) :
    l2SobolevNormTerm Y s f ℓ =
      sobolevNormTerm Y s (l2SobolevRepresentative Y hs f hf) ℓ :=
  l2SobolevNormTerm_eq_representative Y s f _
    (l2SobolevRepresentative_spec Y hs f hf).1 ℓ

/-- The complete squared spectral norms of an `L²` class and its continuous
representative coincide. -/
theorem l2SobolevNormSq_representative (Y : HarmonicBasis) {s : ℝ}
    (hs : 1 < s) (f : Lp ℝ 2 sigma) (hf : L2SobolevUnitBall Y s f) :
    (∑' ℓ, l2SobolevNormTerm Y s f ℓ) =
      sobolevNormSq Y s (l2SobolevRepresentative Y hs f hf) := by
  unfold sobolevNormSq
  congr 1
  funext ℓ
  exact l2SobolevNormTerm_representative Y hs f hf ℓ

/-- The supremum over all `L²` classes equals the continuous spectral WCE. -/
theorem l2SobolevWCE_eq {ι : Type} [Fintype ι]
    (Y : HarmonicBasis) {s : ℝ} (hs : 1 < s) (X : ι → Sphere) :
    l2SobolevWCE Y hs X = sobolevWCE Y s X := by
  unfold l2SobolevWCE sobolevWCE
  congr 1
  ext e
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨l2SobolevRepresentative Y hs f hf,
      (l2SobolevRepresentative_spec Y hs f hf).2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    let f := continuousToLp g
    let hf : L2SobolevUnitBall Y s f := continuous_to_L2SobolevUnitBall Y s g hg
    refine ⟨f, hf, ?_⟩
    rw [l2SobolevRepresentative_unique Y hs f hf g]
    exact ⟨(continuousToLp_ae g).symm, hg⟩

/-- Diamond cubature upper rate for the actual `L²` Sobolev class. -/
theorem l2_sobolev_corollary (Y : HarmonicBasis) {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) : L2SobolevCorollary Y s hs1 := by
  obtain ⟨C, hC, hbound⟩ := sobolev_corollary Y hs1 hs2
  refine ⟨C, hC, ?_⟩
  intro N hN φ
  rw [l2SobolevWCE_eq]
  exact hbound N hN φ

/-- Universal lower rate for the actual `L²` Sobolev class. -/
theorem l2_sobolev_optimality (Y : HarmonicBasis) {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) : L2SobolevOptimality Y s hs1 := by
  obtain ⟨c, hc, hbound⟩ := sobolevOptimality Y hs1 hs2
  refine ⟨c, hc, ?_⟩
  intro N hN X hX
  rw [l2SobolevWCE_eq]
  exact hbound N hN X hX

/-- Riesz-deficit comparison for the actual `L²` Sobolev class. -/
theorem l2_sobolev_energy_comparison (Y : HarmonicBasis) {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) : L2SobolevEnergyComparison Y s hs1 := by
  obtain ⟨A, hA, hbound⟩ := sobolev_energy_comparison Y hs1 hs2
  refine ⟨A, hA, ?_⟩
  intro N hN X
  rw [l2SobolevWCE_eq]
  exact hbound N hN X

/-- All Sobolev assertions in the manuscript's `L²` formulation. -/
def L2SobolevTargets : Prop :=
  ∀ Y : HarmonicBasis, ∀ s : ℝ, ∀ hs1 : 1 < s, s < 2 →
    L2SobolevCorollary Y s hs1 ∧
      L2SobolevOptimality Y s hs1 ∧
        L2SobolevEnergyComparison Y s hs1

theorem l2_sobolev_targets : L2SobolevTargets := by
  intro Y s hs1 hs2
  exact ⟨l2_sobolev_corollary Y hs1 hs2,
    l2_sobolev_optimality Y hs1 hs2,
    l2_sobolev_energy_comparison Y hs1 hs2⟩

end BEMOC.Definitive
