import BEMOCFormalization.EnergyDecomposition

open scoped BigOperators
open MeasureTheory
namespace BEMOC.Definitive

/-- Algebraic Euclidean Laplacian of a polynomial in three variables. -/
noncomputable def polynomialLaplacian (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)
/-- Restriction of a homogeneous harmonic polynomial, defining degree-ℓ spherical harmonics. -/
def IsSphericalHarmonic (ℓ : ℕ) (Y : C(Sphere, ℝ)) : Prop :=
  ∃ p : MvPolynomial (Fin 3) ℝ, p.IsHomogeneous ℓ ∧ polynomialLaplacian p = 0 ∧
    ∀ x : Sphere, Y x = MvPolynomial.eval (fun i => (x : Ambient) i) p

/-- A complete real orthonormal harmonic system. Existence remains an explicit obligation. -/
structure HarmonicBasis where
  function : (ℓ : ℕ) → Fin (2 * ℓ + 1) → C(Sphere, ℝ)
  harmonic : ∀ ℓ k, IsSphericalHarmonic ℓ (function ℓ k)
  orthonormal : ∀ ℓ m k l,
    (∫ x, function ℓ k x * function m l x ∂sigma) =
      if ℓ = m ∧ k.val = l.val then 1 else 0
  complete : ∀ f : C(Sphere, ℝ),
    (∀ ℓ k, (∫ x, f x * function ℓ k x ∂sigma) = 0) → f = 0

/-- The actual Fourier coefficient of a continuous representative. -/
noncomputable def harmonicCoefficient (Y : HarmonicBasis) (f : C(Sphere, ℝ))
    (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) : ℝ :=
  ∫ x, f x * Y.function ℓ k x ∂sigma
/-- Degree-ℓ contribution to the manuscript's specified spectral norm squared. -/
noncomputable def sobolevNormTerm (Y : HarmonicBasis) (s : ℝ)
    (f : C(Sphere, ℝ)) (ℓ : ℕ) : ℝ :=
  (1 + (ℓ : ℝ) * (ℓ + 1)) ^ s * ∑ k, harmonicCoefficient Y f ℓ k ^ 2
/-- Summability is essential: Lean's tsum of a divergent series cannot define this unit ball. -/
def SobolevUnitBall (Y : HarmonicBasis) (s : ℝ) (f : C(Sphere, ℝ)) : Prop :=
  Summable (sobolevNormTerm Y s f) ∧ (∑' ℓ, sobolevNormTerm Y s f ℓ) ≤ 1

/-- Integration error on continuous representatives, independently defined from energy. -/
noncomputable def quadratureError {ι : Type} [Fintype ι]
    (X : ι → Sphere) (f : C(Sphere, ℝ)) : ℝ :=
  (∑ i, f (X i)) / Fintype.card ι - ∫ x, f x ∂sigma
/-- Real worst-case error; boundedness is an explicit analytic obligation below. -/
noncomputable def sobolevWCE {ι : Type} [Fintype ι]
    (Y : HarmonicBasis) (s : ℝ) (X : ι → Sphere) : ℝ :=
  sSup {e : ℝ | ∃ f : C(Sphere, ℝ), SobolevUnitBall Y s f ∧ e = |quadratureError X f|}

/-- Evaluation boundedness needed before taking this supremum. -/
def SobolevEmbedding (Y : HarmonicBasis) (s : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ f : C(Sphere, ℝ), SobolevUnitBall Y s f → ∀ x : Sphere, |f x| ≤ K

/-- Comparison for the specified spectral norm, not a renamed distance-kernel norm. -/
def SobolevEnergyComparison (Y : HarmonicBasis) (s : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 0 < n → ∀ X : Fin n → Sphere,
    sobolevWCE Y s X ^ 2 ≤
      A * (continuousEnergy (2 * s - 2) - energy X (2 * s - 2) / (n : ℝ) ^ 2)

/-- Corollary wce, with an actual spectral unit ball and arbitrary ring phases. -/
def SobolevCorollary (Y : HarmonicBasis) (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N,
    sobolevWCE Y s (point N φ) ≤ C * (N : ℝ) ^ (-s / 2)

/-- Separate lower estimate for the manuscript's accompanying optimality assertion. -/
def SobolevOptimality (Y : HarmonicBasis) (s : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ X : Fin n → Sphere,
    Function.Injective X → c * (n : ℝ) ^ (-s / 2) ≤ sobolevWCE Y s X

/-- Quadrature on a finite family is invariant under relabeling its nodes. -/
theorem quadratureError_comp_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (X : κ → Sphere) (f : C(Sphere, ℝ)) :
    quadratureError (X ∘ e) f = quadratureError X f := by
  have hs : (∑ i : ι, f (X (e i))) = ∑ j : κ, f (X j) := by
    apply Fintype.sum_equiv e
    intro i
    rfl
  simp only [quadratureError, Function.comp_apply, hs, Fintype.card_congr e]

/-- The actual spectral supremum is independent of the finite label type. -/
theorem sobolevWCE_comp_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (Y : HarmonicBasis) (s : ℝ) (X : κ → Sphere) :
    sobolevWCE Y s (X ∘ e) = sobolevWCE Y s X := by
  simp only [sobolevWCE, quadratureError_comp_equiv e X]

end BEMOC.Definitive
