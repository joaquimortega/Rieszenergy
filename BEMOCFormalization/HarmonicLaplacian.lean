import BEMOCFormalization.AngularIntegralZero
import BEMOCFormalization.HarmonicCasimir

/-! The tangential Laplacian on polynomial restrictions of the sphere. -/

open MeasureTheory
namespace BEMOC.Definitive

/-- The finite-dimensional-degree polynomial functions on the sphere,
viewed as a subspace of continuous functions. -/
abbrev PolynomialSphere : Type :=
  LinearMap.range restrictPolynomialLinearMap

/-- A polynomial's continuous restriction, with its range witness. -/
noncomputable def polynomialSphereOf (p : Poly3) : PolynomialSphere :=
  ⟨restrictPolynomial p, ⟨p, rfl⟩⟩

@[simp] theorem polynomialSphereOf_val (p : Poly3) :
    (polynomialSphereOf p : C(Sphere, ℝ)) = restrictPolynomial p := rfl

/-- Differentiation of a polynomial restriction along a genuine plane
rotation is its algebraic angular derivative. -/
theorem angular_orbit_hasDerivAt (i j : Fin 3) (hij : i ≠ j)
    (p : Poly3) :
    HasDerivAt
      (fun θ : ℝ => MvPolynomial.aeval (rotatedSphereCoordinates i j θ) p)
      (restrictPolynomial (angularDerivation i j p)) 0 := by
  have hLeibniz : ∀ q r : Poly3,
      angularDerivation i j (q * r) =
        q * angularDerivation i j r + angularDerivation i j q * r := by
    intro q r
    rw [angularDerivation_mul]
    ring
  have h := polynomial_orbit_hasDerivAt
    (rotatedSphereCoordinates i j) (angularDerivation i j)
    (angularDerivation_C i j) hLeibniz
    (rotatedSphereCoordinates_hasDerivAt i j hij) p
  simpa only [aeval_rotatedSphereCoordinates_zero i j hij] using h

/-- A polynomial vanishing on the sphere has zero tangential derivative
there: the assertion follows by differentiating its identically zero
rotation orbit. -/
theorem restrictPolynomial_angularDerivation_eq_zero
    (i j : Fin 3) (p : Poly3)
    (hp : restrictPolynomial p = 0) :
    restrictPolynomial (angularDerivation i j p) = 0 := by
  by_cases hij : i = j
  · subst j
    ext x
    simp [angularDerivation, restrictPolynomial]
  have horbit (θ : ℝ) :
      MvPolynomial.aeval (rotatedSphereCoordinates i j θ) p = 0 := by
    ext x
    rw [aeval_rotatedSphereCoordinates_apply]
    let T := planeRotation i j hij θ
    have hx := congrArg
      (fun f : C(Sphere, ℝ) => f (sphereLinearIsometryMap T x)) hp
    change MvPolynomial.eval (fun k => (T (x : Ambient)) k) p = 0
    simpa only [restrictPolynomial_apply, ContinuousMap.zero_apply] using hx
  have hder := angular_orbit_hasDerivAt i j hij p
  have hzero : HasDerivAt
      (fun θ : ℝ => MvPolynomial.aeval (rotatedSphereCoordinates i j θ) p)
      (0 : C(Sphere, ℝ)) 0 := by
    have hfun :
        (fun θ : ℝ => MvPolynomial.aeval (rotatedSphereCoordinates i j θ) p) =
          fun _ => (0 : C(Sphere, ℝ)) := funext horbit
    rw [hfun]
    exact hasDerivAt_const (0 : ℝ) (0 : C(Sphere, ℝ))
  exact hder.unique hzero

/-- The genuine rotation generator descends to polynomial functions on the
sphere; its value does not depend on the ambient polynomial extension. -/
noncomputable def sphereAngularDerivation (i j : Fin 3) :
    PolynomialSphere →ₗ[ℝ] PolynomialSphere := by
  let f := restrictPolynomialLinearMap
  let op := angularDerivation i j
  have hker : LinearMap.ker f ≤
      LinearMap.ker ((f.rangeRestrict).comp op) := by
    intro p hp
    have hp' : restrictPolynomial p = 0 := hp
    have hz := restrictPolynomial_angularDerivation_eq_zero i j p hp'
    apply Subtype.ext
    exact hz
  exact (Submodule.liftQ (LinearMap.ker f)
    ((f.rangeRestrict).comp op) hker).comp
      ((f.quotKerEquivRange).symm.toLinearMap)

/-- Evaluating the intrinsic angular derivative on an actual polynomial
restriction recovers the ambient rotation derivation. -/
theorem sphereAngularDerivation_restrict (i j : Fin 3) (p : Poly3) :
    sphereAngularDerivation i j
        ⟨restrictPolynomial p, ⟨p, rfl⟩⟩ =
      ⟨restrictPolynomial (angularDerivation i j p),
        ⟨angularDerivation i j p, rfl⟩⟩ := by
  simp only [sphereAngularDerivation, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  have hs : restrictPolynomialLinearMap.quotKerEquivRange.symm
      ⟨restrictPolynomial p, ⟨p, rfl⟩⟩ =
        (LinearMap.ker restrictPolynomialLinearMap).mkQ p := by
    exact restrictPolynomialLinearMap.quotKerEquivRange_symm_apply_image p ⟨p, rfl⟩
  rw [hs]
  change ((LinearMap.ker restrictPolynomialLinearMap).liftQ
      (restrictPolynomialLinearMap.rangeRestrict.comp (angularDerivation i j))
      (by
        intro q hq
        have hq' : restrictPolynomial q = 0 := hq
        apply Subtype.ext
        exact restrictPolynomial_angularDerivation_eq_zero i j q hq'))
      (Submodule.Quotient.mk p) = _
  rw [Submodule.liftQ_apply]
  rfl

theorem sphereAngularDerivation_polynomialSphereOf (i j : Fin 3)
    (p : Poly3) :
    sphereAngularDerivation i j (polynomialSphereOf p) =
      polynomialSphereOf (angularDerivation i j p) := by
  simpa only [polynomialSphereOf] using sphereAngularDerivation_restrict i j p

/-- Pullback of a continuous sphere function by a genuine Euclidean plane
rotation. -/
noncomputable def sphereRotationPullback (i j : Fin 3) (hij : i ≠ j)
    (θ : ℝ) (f : C(Sphere, ℝ)) : C(Sphere, ℝ) :=
  ⟨fun x => f (sphereLinearIsometryMap (planeRotation i j hij θ) x),
    f.continuous.comp
      (continuous_sphereLinearIsometryMap (planeRotation i j hij θ))⟩

/-- On a polynomial restriction, rotation pullback is evaluation along the
rotated coordinate orbit. -/
theorem sphereRotationPullback_restrict (i j : Fin 3) (hij : i ≠ j)
    (θ : ℝ) (p : Poly3) :
    sphereRotationPullback i j hij θ (restrictPolynomial p) =
      MvPolynomial.aeval (rotatedSphereCoordinates i j θ) p := by
  ext x
  rw [aeval_rotatedSphereCoordinates_apply]
  change MvPolynomial.eval (fun k =>
      (planeRotation i j hij θ (x : Ambient)) k) p = _
  rfl

/-- The descended angular derivation is the derivative at zero of the
actual rotation orbit, so it is a tangential differential operator. -/
theorem sphereAngularDerivation_hasDerivAt
    (i j : Fin 3) (hij : i ≠ j) (f : PolynomialSphere) :
    HasDerivAt
      (fun θ : ℝ => sphereRotationPullback i j hij θ (f : C(Sphere, ℝ)))
      (sphereAngularDerivation i j f : C(Sphere, ℝ)) 0 := by
  obtain ⟨p, hp⟩ := f.property
  have hf : (f : C(Sphere, ℝ)) = restrictPolynomial p := hp.symm
  have hD : (sphereAngularDerivation i j f : C(Sphere, ℝ)) =
      restrictPolynomial (angularDerivation i j p) := by
    have he : f = polynomialSphereOf p := Subtype.ext hf
    rw [he, sphereAngularDerivation_polynomialSphereOf]
    rfl
  simpa only [hf, sphereRotationPullback_restrict, hD] using
    angular_orbit_hasDerivAt i j hij p

/-- The intrinsic polynomial Laplace–Beltrami operator is the sum of
squares of three actual tangential rotation generators. -/
noncomputable def spherePolynomialLaplacian :
    PolynomialSphere →ₗ[ℝ] PolynomialSphere :=
  (sphereAngularDerivation 0 1).comp (sphereAngularDerivation 0 1) +
    (sphereAngularDerivation 0 2).comp (sphereAngularDerivation 0 2) +
      (sphereAngularDerivation 1 2).comp (sphereAngularDerivation 1 2)

/-- The intrinsic sphere operator is exactly the polynomial Casimir when
applied to a polynomial restriction. -/
theorem spherePolynomialLaplacian_restrict (p : Poly3) :
    spherePolynomialLaplacian (polynomialSphereOf p) =
      polynomialSphereOf (angularCasimir p) := by
  apply Subtype.ext
  simp only [spherePolynomialLaplacian, LinearMap.add_apply,
    LinearMap.comp_apply, sphereAngularDerivation_polynomialSphereOf,
    angularCasimir]
  change restrictPolynomial (angularDerivation 0 1 (angularDerivation 0 1 p)) +
      restrictPolynomial (angularDerivation 0 2 (angularDerivation 0 2 p)) +
      restrictPolynomial (angularDerivation 1 2 (angularDerivation 1 2 p)) =
      restrictPolynomial
        (angularDerivation 0 1 (angularDerivation 0 1 p) +
          angularDerivation 0 2 (angularDerivation 0 2 p) +
          angularDerivation 1 2 (angularDerivation 1 2 p))
  change restrictPolynomialLinearMap _ + restrictPolynomialLinearMap _ +
      restrictPolynomialLinearMap _ = restrictPolynomialLinearMap (_ + _ + _)
  rw [map_add, map_add]

/-- Every homogeneous harmonic restriction is an eigenfunction of the
intrinsic polynomial sphere Laplacian with eigenvalue `-ℓ(ℓ+1)`. -/
theorem spherePolynomialLaplacian_harmonic {ℓ : ℕ} {H : Poly3}
    (hH : H ∈ harmonicPolynomialSubmodule ℓ) :
    spherePolynomialLaplacian (polynomialSphereOf H) =
      (-((ℓ : ℝ) * (ℓ + 1))) • polynomialSphereOf H := by
  obtain ⟨hhom, hlap⟩ := mem_harmonicPolynomialSubmodule.mp hH
  rw [spherePolynomialLaplacian_restrict, angularCasimir_harmonic hhom hlap]
  apply Subtype.ext
  exact (restrictPolynomialLinearMap.map_smul _ _)

end BEMOC.Definitive
