# `BEMOCFormalization.Sobolev` proof guide

This module defines the actual spectral unit ball and worst-case quadrature error; `quadratureError_comp_equiv` and `sobolevWCE_comp_equiv` prove finite relabeling invariance. The downstream `HarmonicBasisExistence`, `SobolevEmbeddingDirect`, `DistanceScalarBridge`, and `SobolevMomentSpectral` modules now prove basis existence, embedding, energy comparison, and the universal lower estimate.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
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
```

<!-- END_LEAN_STATEMENTS -->

**Status and source.** This module defines a concrete spectral model for the manuscript's Sobolev unit ball and the actual equal-weight quadrature error. Those analytic results are proved in the downstream harmonic, embedding, kernel, and spectral-moment modules, while this module fixes their exact definitions. The source is `definitive.tex:150–192`, especially its definition of `\mathbb H^s(\mathbb S^2)` at equation `eq:sobolev` and the last displayed inequality. The dependency path is `Sobolev → EnergyDecomposition → Construction/ContinuousEnergy → Core`; `Corollaries` uses the proved `SobolevEnergyComparison` and `SobolevEmbedding` instances together with `MainTheorem`; the `Prop` definitions here remain the exact contracts.

**Harmonic model.** `polynomialLaplacian` sums the three second formal partial derivatives. `IsSphericalHarmonic ℓ Y` requires a homogeneous degree-ℓ polynomial with zero Euclidean Laplacian whose restriction is exactly Y. `HarmonicBasisExistence` constructs a full basis in each degree using dimension 2ℓ+1, harmonic decomposition, finite-dimensional orthonormalization, and Stone–Weierstrass density. `HarmonicL2` extends coefficient completeness to genuine L² classes by density of continuous test functions. `HarmonicLaplacian` constructs the intrinsic sphere operator from squared tangential rotation fields, proves it independent of a polynomial extension, and identifies its action with the Casimir. `HarmonicL2Laplacian.weakSphereLaplacian_eigen_iff` proves that its weak eigenspace at −ℓ(ℓ+1) consists exactly of genuine degree-ℓ harmonic restrictions. Thus this is an actual geometric harmonic model, not an arbitrary abstract orthonormal system. The formulation uses a polynomial test core and does not introduce a separate general-manifold differential operator.

**Unit ball and representative identification.** `harmonicCoefficient` is the integral of fY against sigma. `sobolevNormTerm` multiplies the degree sum of squared coefficients by `(1+ℓ(ℓ+1))^s`, exactly the manuscript weight. `SobolevUnitBall` requires both summability and total sum at most one, so a divergent totalized `tsum` cannot enter the ball. `SobolevL2` defines the corresponding ball on all genuine `Lp ℝ 2 sigma` classes. For s>1, its weighted evaluation estimate makes the harmonic synthesis uniformly Cauchy, hence continuously convergent. The limit has the original L² coefficients; L² coefficient injectivity identifies its class with the input. Full support of sigma makes the continuous representative unique. The converse continuous-to-L² inclusion and termwise norm equality are proved. `SobolevL2Corollary` uses the unique representative for every class in the unit ball and proves exact equality of worst-case errors. All statements quantify over an arbitrary harmonic basis, and the proof applies directly to that same basis. A separately packaged Hilbert-space type is unnecessary for this complete unit-ball and WCE formulation.

**Supremum foundations.** `sobolevWCE` is `sSup` of the absolute errors over `SobolevUnitBall`. `SobolevBasic` proves this set nonempty using `f=0` and bounded above from the embedding. `SobolevEmbedding Y s` asks for a uniform point-evaluation bound on the unit ball. Given `IsProbabilityMeasure sigma` and a nonempty finite index type, each quadrature average has absolute value at most `K` and the integral at most `K`; hence `|quadratureError|≤2K`, supplying `BddAbove`. The embedding in `SobolevEmbeddingDirect` follows from harmonic coefficient Cauchy–Schwarz, the addition theorem `∑_k Y_{ℓ,k}(x)^2=2ℓ+1`, and convergence of `∑_{ℓ≥0}(2ℓ+1)/(1+ℓ(ℓ+1))^s` exactly for `s>1`. `SobolevEmbeddingDirect` uses the resulting uniformly convergent harmonic expansion to justify point evaluation. A weaker bound on only the quadrature functional could replace embedding in assembly, and the declared `SobolevEmbedding` contract is proved directly downstream.

**Distance-power reproducing kernel.** Set `α=2s-2`; under `1<s<2`, this lies in `(0,2)`. BSSW14 [§5, equations (37)–(42)](https://arxiv.org/pdf/1208.3267) supplies the generalized-distance kernel `K_s(x,y)=2I_α-dist(x,y)^α`, whose centered harmonic coefficients `a_ℓ(s)` are positive for `ℓ≥1` and comparable to `ℓ^{-2s}`. Equation (29) of that paper is the general reproducing-kernel WCE identity; the exact distance formula is equation (42). The manuscript's spectral norm is not defined by `K_s`, so prove a coefficient comparison: with `b_ℓ(s)=(1+ℓ(ℓ+1))^{-s}`, show `b_ℓ(s)≤A_s a_ℓ(s)` for all `ℓ≥1`. The finitely many low modes need positive individual estimates; the tail uses the asymptotic `a_ℓ(s)≈c_sℓ^{-2s}`. In the harmonic WCE expansion, each degree contributes a nonnegative square times its coefficient, so this bound yields `WCE_can²≤A_s WCE_K²`. The kernel identity gives `WCE_K²=continuousEnergy α-energy X α/n²`, including diagonal terms `dist(x,x)^α=0`. Alternatively, prove the norm comparison and boundedness of the quadrature functional, then use its RKHS Riesz representer. Every swap among infinite harmonic sums, finite point sums, and sphere integrals requires a convergence lemma. The comparison constant depends on `s` (and chosen normalization), never on `n` or `X`.

**Optimality.** `SobolevOptimality` is a universal lower bound for injective finite configurations. It is not implied by the upper `SobolevEnergyComparison`. BSSW14 [Theorem 3](https://arxiv.org/pdf/1208.3267), based on Hesse/Hesse–Sloan, gives this `n^{-s/2}` obstruction for any `n`-point rule. A self-contained alternative uses Wagner's lower distance-power deficit plus reverse coefficient comparison `a_ℓ(s)≤B_s b_ℓ(s)`. State the exact lower theorem and transfer between its norm and the specified canonical norm, keeping the inequality direction straight. The qualifier `Function.Injective X` corresponds to a set of `n` distinct points; derive it for the Diamond construction from `ConstructionFacts` before claiming its optimality.

**Verification.** Test the ℓ=0 normalization, where constants integrate exactly and must contribute zero WCE, and check the `s=3/2` distance exponent α=1 against Stolarsky. Confirm that `s>1` is used for evaluation continuity and `s<2` for positive distance-kernel coefficients in this form. Build after each basis, summability, and kernel theorem; keep no abstract placeholder that merely renames the energy deficit as WCE.
