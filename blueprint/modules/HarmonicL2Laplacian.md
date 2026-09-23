# Weak L² spherical Laplacian

`HarmonicL2Laplacian.lean` defines `WeakSphereLaplacian f g` by the test identity

`∫ f · Δφ dσ = ∫ g · φ dσ`

for every `φ : PolynomialSphere`. Here `Δ` is the extension-independent `spherePolynomialLaplacian` from `HarmonicLaplacian.lean`: the sum of squares of three tangent plane-rotation generators. `weakSphereLaplacian_iff_polynomial` proves that this intrinsic test relation is equivalent to testing against every ambient polynomial restriction with its algebraic Casimir. The weak graph is defined by the differential test identity, rather than by harmonic coefficients.

`angularCasimir_integral_selfAdjoint` proves integration by parts on the polynomial core. It applies the checked vanishing of each angular derivative's surface integral to products, obtaining skew-adjointness of each tangent rotation generator, then symmetry of its square and of their three-term Casimir. Thus every homogeneous harmonic polynomial restriction has weak eigenvalue `−ℓ(ℓ+1)`, as shown by `weakSphereLaplacian_harmonic_eigen`.

For the converse, test a weak eigenfunction against each genuine degree-`m` polynomial harmonic underlying an arbitrary `HarmonicBasis Y`. Distinct eigenvalues force every coefficient outside degree `ℓ` to vanish. `harmonicL2DegreeProjection` is the finite sum of its degree-`ℓ` basis components; its coefficients agree in degree `ℓ` and vanish in every other degree. `HarmonicL2.l2HarmonicCoefficient_complete` then identifies the eigenfunction with this projection. The finite projection is explicitly the L² class of a degree-`ℓ` harmonic polynomial restriction, using the finite polynomial basis and linearity of restriction and the continuous-to-L² map.

The public theorem `weakSphereLaplacian_eigen_iff Y ℓ f` therefore says exactly that the weak L² eigenclasses with eigenvalue `−ℓ(ℓ+1)` are the classes of restrictions of genuine homogeneous harmonic polynomials of degree `ℓ`. This identifies the eigenspaces for this weak operator on its polynomial test core. It does not assert a separate maximal self-adjoint realization on a Sobolev operator domain.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.HarmonicL2
import BEMOCFormalization.AngularIntegralZero
import BEMOCFormalization.HarmonicOrthogonality
import BEMOCFormalization.HarmonicLaplacian

open MeasureTheory
open scoped InnerProductSpace
namespace BEMOC.Definitive

private theorem restrictPolynomial_mul_apply (p q : Poly3) (x : Sphere) :
    restrictPolynomial (p * q) x = restrictPolynomial p x * restrictPolynomial q x := by
  simp [restrictPolynomial_apply]

private theorem restrictPolynomial_add_apply (p q : Poly3) (x : Sphere) :
    restrictPolynomial (p + q) x = restrictPolynomial p x + restrictPolynomial q x := by
  simp [restrictPolynomial_apply]

/-- The intrinsic polynomial Casimir is symmetric for the genuine normalized
surface measure. This is integration by parts for the three tangent
rotation generators, without boundary terms. -/
theorem angularCasimir_integral_selfAdjoint (p q : Poly3) :
    (∫ x : Sphere, restrictPolynomial (angularCasimir p) x *
      restrictPolynomial q x ∂sigma) =
    (∫ x : Sphere, restrictPolynomial p x *
      restrictPolynomial (angularCasimir q) x ∂sigma) := by
  have hskew (i j : Fin 3) (a b : Poly3) :
      (∫ x : Sphere, restrictPolynomial (angularDerivation i j a) x *
        restrictPolynomial b x ∂sigma) =
      -(∫ x : Sphere, restrictPolynomial a x *
        restrictPolynomial (angularDerivation i j b) x ∂sigma) := by
    have h := angular_integral_zero i j (a * b)
    rw [angularDerivation_mul] at h
    simp_rw [restrictPolynomial_add_apply, restrictPolynomial_mul_apply] at h
    rw [integral_add] at h
    · linarith
    · exact (restrictPolynomial (angularDerivation i j a) * restrictPolynomial b).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact (restrictPolynomial a * restrictPolynomial (angularDerivation i j b)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hself (i j : Fin 3) (a b : Poly3) :
      (∫ x : Sphere, restrictPolynomial (angularDerivation i j (angularDerivation i j a)) x *
        restrictPolynomial b x ∂sigma) =
      (∫ x : Sphere, restrictPolynomial a x *
        restrictPolynomial (angularDerivation i j (angularDerivation i j b)) x ∂sigma) := by
    calc
      _ = -(∫ x : Sphere, restrictPolynomial (angularDerivation i j a) x *
          restrictPolynomial (angularDerivation i j b) x ∂sigma) :=
        hskew i j (angularDerivation i j a) b
      _ = _ := by rw [hskew i j a (angularDerivation i j b)]; ring
  have hcas :
      (∫ x : Sphere, restrictPolynomial (angularCasimir p) x * restrictPolynomial q x ∂sigma) =
      (∫ x : Sphere, restrictPolynomial p x * restrictPolynomial (angularCasimir q) x ∂sigma) := by
    let A := angularDerivation 0 1 (angularDerivation 0 1 p)
    let B := angularDerivation 0 2 (angularDerivation 0 2 p)
    let C := angularDerivation 1 2 (angularDerivation 1 2 p)
    let D := angularDerivation 0 1 (angularDerivation 0 1 q)
    let E := angularDerivation 0 2 (angularDerivation 0 2 q)
    let F := angularDerivation 1 2 (angularDerivation 1 2 q)
    change (∫ x : Sphere, restrictPolynomial (A + B + C) x * restrictPolynomial q x ∂sigma) =
      ∫ x : Sphere, restrictPolynomial p x * restrictPolynomial (D + E + F) x ∂sigma
    simp_rw [restrictPolynomial_add_apply, add_mul, mul_add]
    have hint (a b : Poly3) :
        Integrable (fun x : Sphere => restrictPolynomial a x * restrictPolynomial b x) sigma :=
      (restrictPolynomial a * restrictPolynomial b).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hleft :
        (∫ x : Sphere, restrictPolynomial A x * restrictPolynomial q x +
          restrictPolynomial B x * restrictPolynomial q x +
          restrictPolynomial C x * restrictPolynomial q x ∂sigma) =
        (∫ x : Sphere, restrictPolynomial A x * restrictPolynomial q x ∂sigma) +
        (∫ x : Sphere, restrictPolynomial B x * restrictPolynomial q x ∂sigma) +
          (∫ x : Sphere, restrictPolynomial C x * restrictPolynomial q x ∂sigma) := by
      calc
        _ = (∫ x : Sphere, restrictPolynomial A x * restrictPolynomial q x +
              restrictPolynomial B x * restrictPolynomial q x ∂sigma) +
              (∫ x : Sphere, restrictPolynomial C x * restrictPolynomial q x ∂sigma) := by
            simpa only [Pi.add_apply] using
              (integral_add ((hint A q).add (hint B q)) (hint C q))
        _ = _ := by rw [integral_add (hint A q) (hint B q)]
    have hright :
        (∫ x : Sphere, restrictPolynomial p x * restrictPolynomial D x +
          restrictPolynomial p x * restrictPolynomial E x +
          restrictPolynomial p x * restrictPolynomial F x ∂sigma) =
        (∫ x : Sphere, restrictPolynomial p x * restrictPolynomial D x ∂sigma) +
        (∫ x : Sphere, restrictPolynomial p x * restrictPolynomial E x ∂sigma) +
          (∫ x : Sphere, restrictPolynomial p x * restrictPolynomial F x ∂sigma) := by
      calc
        _ = (∫ x : Sphere, restrictPolynomial p x * restrictPolynomial D x +
              restrictPolynomial p x * restrictPolynomial E x ∂sigma) +
              (∫ x : Sphere, restrictPolynomial p x * restrictPolynomial F x ∂sigma) := by
            simpa only [Pi.add_apply] using
              (integral_add ((hint p D).add (hint p E)) (hint p F))
        _ = _ := by rw [integral_add (hint p D) (hint p E)]
    rw [hleft, hright]
    rw [hself 0 1 p q, hself 0 2 p q, hself 1 2 p q]
  exact hcas

/-- The weak graph of the intrinsic angular Laplacian, tested against every
polynomial sphere restriction. The differential action is the sum of squares
of the three genuine tangent rotation generators. -/
def WeakSphereLaplacian (f g : Lp ℝ 2 sigma) : Prop :=
  ∀ q : PolynomialSphere,
    (∫ x : Sphere, (f : Sphere → ℝ) x *
      (spherePolynomialLaplacian q : C(Sphere, ℝ)) x ∂sigma) =
    ∫ x : Sphere, (g : Sphere → ℝ) x * (q : C(Sphere, ℝ)) x ∂sigma

/-- Polynomial tests compute the same weak relation as tests in the
extension-independent intrinsic polynomial sphere domain. -/
theorem weakSphereLaplacian_iff_polynomial (f g : Lp ℝ 2 sigma) :
    WeakSphereLaplacian f g ↔
      ∀ q : Poly3,
        (∫ x : Sphere, (f : Sphere → ℝ) x *
          restrictPolynomial (angularCasimir q) x ∂sigma) =
        ∫ x : Sphere, (g : Sphere → ℝ) x * restrictPolynomial q x ∂sigma := by
  constructor
  · intro h q
    simpa only [WeakSphereLaplacian, spherePolynomialLaplacian_restrict,
      polynomialSphereOf_val] using h (polynomialSphereOf q)
  · intro h q
    obtain ⟨p, hp⟩ := q.property
    have hq : q = polynomialSphereOf p := Subtype.ext hp.symm
    rw [hq, spherePolynomialLaplacian_restrict]
    simpa only [polynomialSphereOf_val] using h p

/-- The polynomial harmonic restriction is a weak angular-Laplacian
eigenfunction with the geometric eigenvalue `-ℓ(ℓ+1)`. -/
theorem weakSphereLaplacian_harmonic {ℓ : ℕ}
    (p : harmonicPolynomialSubmodule ℓ) :
    WeakSphereLaplacian (continuousToLp (restrictPolynomial p.val))
      (continuousToLp (restrictPolynomial (angularCasimir p.val))) := by
  apply (weakSphereLaplacian_iff_polynomial _ _).2
  intro q
  have hp := continuousToLp_ae (restrictPolynomial p.val)
  have hcp := continuousToLp_ae (restrictPolynomial (angularCasimir p.val))
  calc
    (∫ x : Sphere, (continuousToLp (restrictPolynomial p.val) : Sphere → ℝ) x *
        restrictPolynomial (angularCasimir q) x ∂sigma) =
      ∫ x : Sphere, restrictPolynomial p.val x *
        restrictPolynomial (angularCasimir q) x ∂sigma := by
          apply integral_congr_ae
          filter_upwards [hp] with x hx
          rw [hx]
    _ = ∫ x : Sphere, restrictPolynomial (angularCasimir p.val) x *
        restrictPolynomial q x ∂sigma :=
          (angularCasimir_integral_selfAdjoint p.val q).symm
    _ = ∫ x : Sphere,
        (continuousToLp (restrictPolynomial (angularCasimir p.val)) : Sphere → ℝ) x *
          restrictPolynomial q x ∂sigma := by
          apply integral_congr_ae
          filter_upwards [hcp] with x hx
          rw [hx]

/-- The weak graph contains the exact spherical-harmonic eigenpair. -/
theorem weakSphereLaplacian_harmonic_eigen {ℓ : ℕ}
    (p : harmonicPolynomialSubmodule ℓ) :
    WeakSphereLaplacian (continuousToLp (restrictPolynomial p.val))
      ((-((ℓ : ℝ) * (ℓ + 1))) • continuousToLp (restrictPolynomial p.val)) := by
  have hcas : angularCasimir p.val = -((ℓ : ℝ) * (ℓ + 1)) • p.val :=
    angularCasimir_harmonic
      (mem_harmonicPolynomialSubmodule.mp p.property).1
      (mem_harmonicPolynomialSubmodule.mp p.property).2
  have heq : continuousToLp (restrictPolynomial (angularCasimir p.val)) =
      (-((ℓ : ℝ) * (ℓ + 1))) • continuousToLp (restrictPolynomial p.val) := by
    apply Lp.ext
    filter_upwards [continuousToLp_ae (restrictPolynomial (angularCasimir p.val)),
      continuousToLp_ae (restrictPolynomial p.val),
      Lp.coeFn_smul (-((ℓ : ℝ) * (ℓ + 1)))
        (continuousToLp (restrictPolynomial p.val))] with x hx hy hz
    rw [hx, hz]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hy, hcas]
    simp [restrictPolynomial_apply, smul_eq_mul]
  rw [← heq]
  exact weakSphereLaplacian_harmonic p

/-- Weak eigenvectors have no Fourier coefficient in any other harmonic
degree. The test functions are the genuine polynomial harmonics. -/
theorem weakSphereLaplacian_eigen_coeff_zero (Y : HarmonicBasis)
    {ℓ : ℕ} {f : Lp ℝ 2 sigma}
    (hf : WeakSphereLaplacian f
      ((-((ℓ : ℝ) * (ℓ + 1))) • f))
    (m : ℕ) (k : Fin (2 * m + 1)) (hm : m ≠ ℓ) :
    l2HarmonicCoefficient Y f m k = 0 := by
  let p := harmonicBasisPolynomial Y m k
  have hhom := (mem_harmonicPolynomialSubmodule.mp p.property).1
  have hlap := (mem_harmonicPolynomialSubmodule.mp p.property).2
  have hcas : angularCasimir p.val = -((m : ℝ) * (m + 1)) • p.val :=
    angularCasimir_harmonic hhom hlap
  have htest := (weakSphereLaplacian_iff_polynomial _ _).1 hf p.val
  have hleft :
      (∫ x : Sphere, (f : Sphere → ℝ) x *
        restrictPolynomial (angularCasimir p.val) x ∂sigma) =
      -((m : ℝ) * (m + 1)) * l2HarmonicCoefficient Y f m k := by
    rw [hcas]
    have hres : restrictPolynomial (-((m : ℝ) * (m + 1)) • p.val) =
        (-((m : ℝ) * (m + 1))) • Y.function m k := by
      rw [← harmonicBasisPolynomial_restrict Y m k]
      exact map_smul restrictPolynomialLinearMap _ _
    simp_rw [show ∀ x : Sphere,
      (f : Sphere → ℝ) x * restrictPolynomial
        (-((m : ℝ) * (m + 1)) • p.val) x =
      -((m : ℝ) * (m + 1)) *
        ((f : Sphere → ℝ) x * Y.function m k x) from fun x => by
          rw [hres]
          simp only [ContinuousMap.smul_apply, smul_eq_mul]
          ring]
    rw [integral_const_mul]
    rfl
  have hright :
      (∫ x : Sphere,
        (((-((ℓ : ℝ) * (ℓ + 1))) • f : Lp ℝ 2 sigma) : Sphere → ℝ) x *
          restrictPolynomial p.val x ∂sigma) =
      -((ℓ : ℝ) * (ℓ + 1)) * l2HarmonicCoefficient Y f m k := by
    apply Eq.trans (integral_congr_ae ?_)
    · rw [integral_const_mul]
      rfl
    filter_upwards [Lp.coeFn_smul (-((ℓ : ℝ) * (ℓ + 1))) f] with x hx
    rw [hx, ← harmonicBasisPolynomial_restrict Y m k]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hleft, hright] at htest
  have heig : (m : ℝ) * (m + 1) ≠ (ℓ : ℝ) * (ℓ + 1) := by
    intro heq
    have : (m : ℝ) = ℓ := by
      nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) ℓ]
    exact hm (Nat.cast_injective this)
  rcases mul_eq_zero.mp (show
      (((m : ℝ) * (m + 1)) - ((ℓ : ℝ) * (ℓ + 1))) *
        l2HarmonicCoefficient Y f m k = 0 by nlinarith [htest]) with h | h
  · exact False.elim (heig (sub_eq_zero.mp h))
  · exact h

/-- The finite L² Fourier projection onto the genuine degree-`ℓ`
polynomial harmonics. -/
noncomputable def harmonicL2DegreeProjection (Y : HarmonicBasis) (ℓ : ℕ)
    (f : Lp ℝ 2 sigma) : Lp ℝ 2 sigma :=
  ∑ k : Fin (2 * ℓ + 1),
    (l2HarmonicCoefficient Y f ℓ k) • continuousToLp (Y.function ℓ k)

theorem harmonicL2DegreeProjection_coefficient_same (Y : HarmonicBasis)
    (ℓ : ℕ) (f : Lp ℝ 2 sigma) (j : Fin (2 * ℓ + 1)) :
    l2HarmonicCoefficient Y (harmonicL2DegreeProjection Y ℓ f) ℓ j =
      l2HarmonicCoefficient Y f ℓ j := by
  simp only [harmonicL2DegreeProjection, l2HarmonicCoefficient_eq_inner,
    sum_inner, real_inner_smul_left]
  have horth (k : Fin (2 * ℓ + 1)) :
      ⟪continuousToLp (Y.function ℓ k),
        continuousToLp (Y.function ℓ j)⟫_ℝ = if k = j then 1 else 0 := by
    simpa [continuousToLp, ContinuousMap.inner_toLp, mul_comm, Fin.val_inj]
      using Y.orthonormal ℓ ℓ k j
  simp_rw [horth]
  simp

theorem harmonicL2DegreeProjection_coefficient_other (Y : HarmonicBasis)
    (ℓ : ℕ) (f : Lp ℝ 2 sigma) (m : ℕ) (j : Fin (2 * m + 1))
    (hm : m ≠ ℓ) :
    l2HarmonicCoefficient Y (harmonicL2DegreeProjection Y ℓ f) m j = 0 := by
  simp only [harmonicL2DegreeProjection, l2HarmonicCoefficient_eq_inner,
    sum_inner, real_inner_smul_left]
  have horth (k : Fin (2 * ℓ + 1)) :
      ⟪continuousToLp (Y.function ℓ k),
        continuousToLp (Y.function m j)⟫_ℝ = 0 := by
    simpa [continuousToLp, ContinuousMap.inner_toLp, mul_comm, Ne.symm hm]
      using Y.orthonormal ℓ m k j
  simp_rw [horth]
  simp

/-- A weak eigenfunction is exactly its finite Fourier projection in the
matching harmonic degree. -/
theorem weakSphereLaplacian_eigen_eq_degreeProjection (Y : HarmonicBasis)
    {ℓ : ℕ} {f : Lp ℝ 2 sigma}
    (hf : WeakSphereLaplacian f
      ((-((ℓ : ℝ) * (ℓ + 1))) • f)) :
    f = harmonicL2DegreeProjection Y ℓ f := by
  apply l2HarmonicCoefficient_injective Y
  intro m k
  by_cases hm : m = ℓ
  · subst m
    exact (harmonicL2DegreeProjection_coefficient_same Y ℓ f k).symm
  · rw [weakSphereLaplacian_eigen_coeff_zero Y hf m k hm,
      harmonicL2DegreeProjection_coefficient_other Y ℓ f m k hm]

/-- The finite projection is the L² class of an actual homogeneous harmonic
polynomial restriction, not merely an abstract spectral vector. -/
theorem harmonicL2DegreeProjection_is_harmonic (Y : HarmonicBasis)
    (ℓ : ℕ) (f : Lp ℝ 2 sigma) :
    ∃ p : harmonicPolynomialSubmodule ℓ,
      harmonicL2DegreeProjection Y ℓ f =
        continuousToLp (restrictPolynomial p.val) := by
  let p : harmonicPolynomialSubmodule ℓ :=
    ∑ k : Fin (2 * ℓ + 1),
      (l2HarmonicCoefficient Y f ℓ k) • harmonicBasisPolynomial Y ℓ k
  refine ⟨p, ?_⟩
  have hres : restrictPolynomial p.val =
      ∑ k : Fin (2 * ℓ + 1),
        (l2HarmonicCoefficient Y f ℓ k) • Y.function ℓ k := by
    change restrictHarmonicLinearMap ℓ p = _
    dsimp only [p]
    rw [map_sum]
    simp only [map_smul, restrictHarmonicLinearMap, LinearMap.comp_apply,
      Submodule.subtype_apply]
    simp [restrictPolynomialLinearMap, harmonicBasisPolynomial_restrict]
  rw [hres]
  simp only [harmonicL2DegreeProjection, continuousToLp]
  rw [map_sum]
  simp only [map_smul]

/-- Exact eigenspace characterization for the weak L² Laplacian on the
polynomial test core. Every eigenclass with eigenvalue `-ℓ(ℓ+1)` is the L²
class of a genuine degree-`ℓ` homogeneous harmonic polynomial restriction,
and every such restriction satisfies the weak differential equation. -/
theorem weakSphereLaplacian_eigen_iff (Y : HarmonicBasis) (ℓ : ℕ)
    (f : Lp ℝ 2 sigma) :
    WeakSphereLaplacian f ((-((ℓ : ℝ) * (ℓ + 1))) • f) ↔
      ∃ p : harmonicPolynomialSubmodule ℓ,
        f = continuousToLp (restrictPolynomial p.val) := by
  constructor
  · intro hf
    obtain ⟨p, hp⟩ := harmonicL2DegreeProjection_is_harmonic Y ℓ f
    exact ⟨p, (weakSphereLaplacian_eigen_eq_degreeProjection Y hf).trans hp⟩
  · rintro ⟨p, rfl⟩
    exact weakSphereLaplacian_harmonic_eigen p

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
