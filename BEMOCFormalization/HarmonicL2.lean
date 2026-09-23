import BEMOCFormalization.HarmonicFiniteSpan
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space

open scoped InnerProductSpace
open MeasureTheory
namespace BEMOC.Definitive

/-- The canonical L² class of a continuous function on the compact sphere. -/
noncomputable def continuousToLp (g : C(Sphere, ℝ)) : Lp ℝ 2 sigma :=
  ContinuousMap.toLp 2 sigma ℝ g

/-- The actual L² Fourier coefficient against a spherical harmonic. -/
noncomputable def l2HarmonicCoefficient (Y : HarmonicBasis)
    (f : Lp ℝ 2 sigma) (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) : ℝ :=
  ∫ x : Sphere, (f : Sphere → ℝ) x * Y.function ℓ k x ∂sigma

theorem continuousToLp_ae (g : C(Sphere, ℝ)) :
  (continuousToLp g : Sphere → ℝ) =ᵐ[sigma] (g : Sphere → ℝ) := by
  exact ContinuousMap.coeFn_toLp (p := 2) sigma g

theorem l2HarmonicCoefficient_continuousToLp (Y : HarmonicBasis)
    (g : C(Sphere, ℝ)) (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    l2HarmonicCoefficient Y (continuousToLp g) ℓ k =
      harmonicCoefficient Y g ℓ k := by
  unfold l2HarmonicCoefficient harmonicCoefficient
  apply integral_congr_ae
  filter_upwards [continuousToLp_ae g] with x hx
  rw [hx]

/-- Pairing an L² class with continuous test functions is bounded for the
uniform norm. -/
noncomputable def l2ContinuousPairing (f : Lp ℝ 2 sigma) :
    C(Sphere, ℝ) →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (Lp ℝ 2 sigma) f).comp
    (ContinuousMap.toLp 2 sigma ℝ)

theorem l2ContinuousPairing_apply (f : Lp ℝ 2 sigma)
    (g : C(Sphere, ℝ)) :
    l2ContinuousPairing f g =
      ∫ x : Sphere, (f : Sphere → ℝ) x * g x ∂sigma := by
  rw [l2ContinuousPairing]
  change (InnerProductSpace.toDual ℝ (Lp ℝ 2 sigma) f)
    (continuousToLp g) = _
  rw [InnerProductSpace.toDual_apply, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousToLp_ae g] with x hx
  simp [hx, mul_comm]

theorem l2ContinuousPairing_harmonic (Y : HarmonicBasis)
    (f : Lp ℝ 2 sigma) (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    l2ContinuousPairing f (Y.function ℓ k) =
      l2HarmonicCoefficient Y f ℓ k :=
  l2ContinuousPairing_apply f (Y.function ℓ k)

/-- If an L² function has no harmonic Fourier coefficients, its bounded
pairing with every continuous function is zero. -/
theorem l2ContinuousPairing_eq_zero_of_coefficients (Y : HarmonicBasis)
    (f : Lp ℝ 2 sigma)
    (hf : ∀ ℓ k, l2HarmonicCoefficient Y f ℓ k = 0) :
    l2ContinuousPairing f = 0 := by
  have hdegree (n : ℕ) (p : harmonicPolynomialSubmodule n) :
      restrictPolynomial p.val ∈ LinearMap.ker (l2ContinuousPairing f).toLinearMap := by
    have hinc : Set.range (Y.function n) ⊆
        LinearMap.ker (l2ContinuousPairing f).toLinearMap := by
      rintro g ⟨k, rfl⟩
      exact (l2ContinuousPairing_harmonic Y f n k).trans (hf n k)
    exact (Submodule.span_le.mpr hinc)
      (harmonic_restriction_mem_basisDegreeSpan Y n p)
  have hspan : harmonicRestrictionSpan ≤
      LinearMap.ker (l2ContinuousPairing f).toLinearMap := by
    apply Submodule.span_le.mpr
    intro g hg
    obtain ⟨n, hn⟩ := hg
    obtain ⟨p, rfl⟩ := (isSphericalHarmonic_iff_range n g).mp hn
    exact hdegree n p
  apply ContinuousLinearMap.ext
  intro g
  have heq : (fun g : C(Sphere, ℝ) => l2ContinuousPairing f g) =
      (fun _ => (0 : ℝ)) :=
    Continuous.ext_on harmonicRestrictionSpan_dense
      (l2ContinuousPairing f).continuous continuous_const
      (by intro g hg; exact hspan hg)
  exact congrFun heq g

/-- Harmonic coefficients distinguish L² equivalence classes. -/
theorem l2HarmonicCoefficient_complete (Y : HarmonicBasis)
    (f : Lp ℝ 2 sigma)
    (hf : ∀ ℓ k, l2HarmonicCoefficient Y f ℓ k = 0) : f = 0 := by
  let F := InnerProductSpace.toDual ℝ (Lp ℝ 2 sigma) f
  have hC := l2ContinuousPairing_eq_zero_of_coefficients Y f hf
  have hdense : DenseRange (ContinuousMap.toLp (E := ℝ) 2 sigma ℝ) :=
    ContinuousMap.toLp_denseRange (p := 2) ℝ sigma ℝ (by norm_num)
  have heq : (fun u : Lp ℝ 2 sigma => F u) = (fun _ => (0 : ℝ)) :=
    Continuous.ext_on hdense F.continuous continuous_const (by
      rintro u ⟨g, rfl⟩
      exact congrArg (fun T : C(Sphere, ℝ) →L[ℝ] ℝ => T g) hC)
  have hself : F f = 0 := congrFun heq f
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp
    (by simpa [F, InnerProductSpace.toDual_apply] using hself)

theorem l2HarmonicCoefficient_eq_inner (Y : HarmonicBasis)
    (f : Lp ℝ 2 sigma) (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    l2HarmonicCoefficient Y f ℓ k =
      ⟪f, continuousToLp (Y.function ℓ k)⟫_ℝ := by
  rw [← l2ContinuousPairing_harmonic]
  rfl

theorem l2HarmonicCoefficient_add (Y : HarmonicBasis)
    (f g : Lp ℝ 2 sigma) (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    l2HarmonicCoefficient Y (f + g) ℓ k =
      l2HarmonicCoefficient Y f ℓ k + l2HarmonicCoefficient Y g ℓ k := by
  simp only [l2HarmonicCoefficient_eq_inner, inner_add_left]

theorem l2HarmonicCoefficient_smul (Y : HarmonicBasis)
    (c : ℝ) (f : Lp ℝ 2 sigma) (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    l2HarmonicCoefficient Y (c • f) ℓ k =
      c * l2HarmonicCoefficient Y f ℓ k := by
  simp only [l2HarmonicCoefficient_eq_inner, real_inner_smul_left]

theorem l2HarmonicCoefficient_sub (Y : HarmonicBasis)
    (f g : Lp ℝ 2 sigma) (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    l2HarmonicCoefficient Y (f - g) ℓ k =
      l2HarmonicCoefficient Y f ℓ k - l2HarmonicCoefficient Y g ℓ k := by
  simp only [l2HarmonicCoefficient_eq_inner, inner_sub_left]

theorem continuousToLp_injective : Function.Injective continuousToLp := by
  exact ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) sigma

theorem l2HarmonicCoefficient_injective (Y : HarmonicBasis)
    {f g : Lp ℝ 2 sigma}
    (hfg : ∀ ℓ k, l2HarmonicCoefficient Y f ℓ k =
      l2HarmonicCoefficient Y g ℓ k) : f = g := by
  apply sub_eq_zero.mp
  apply l2HarmonicCoefficient_complete Y
  intro ℓ k
  simp only [l2HarmonicCoefficient_eq_inner, inner_sub_left]
  exact sub_eq_zero.mpr (by simpa only [l2HarmonicCoefficient_eq_inner] using hfg ℓ k)

end BEMOC.Definitive
