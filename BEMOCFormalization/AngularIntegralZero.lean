import BEMOCFormalization.HarmonicOrthogonality
import BEMOCFormalization.HarmonicBasisAssembly
import BEMOCFormalization.PlaneRotation

open MeasureTheory
namespace BEMOC.Definitive

/-! The angular derivative is the infinitesimal action of rotations on sphere
integrals.  The first step packages ordinary spherical integration as a bounded
linear functional on continuous functions. -/

/-- Integration against normalized surface area, acting on continuous functions. -/
noncomputable def sigmaIntegralCLM : C(Sphere, ℝ) →L[ℝ] ℝ :=
  sigmaPairingCLM 1

@[simp] theorem sigmaIntegralCLM_apply (f : C(Sphere, ℝ)) :
    sigmaIntegralCLM f = ∫ x : Sphere, f x ∂sigma := by
  simp [sigmaIntegralCLM, sigmaPairingCLM, sigmaPairingLinearMap]

/-- The integral functional is invariant under every ambient linear isometry. -/
theorem sigmaIntegralCLM_isometry (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    (f : C(Sphere, ℝ)) :
    sigmaIntegralCLM ⟨fun x => f (sphereLinearIsometryMap T x),
      f.continuous.comp (continuous_sphereLinearIsometryMap T)⟩ =
      sigmaIntegralCLM f := by
  simpa only [sigmaIntegralCLM_apply] using
    integral_sigma_comp_linear_isometry T (fun x : Sphere => f x)

/-- A polynomial evaluated along differentiable coordinate curves has the
derivative prescribed by any polynomial derivation agreeing on generators. -/
theorem polynomial_orbit_hasDerivAt
    (a : ℝ → Fin 3 → C(Sphere, ℝ)) (D : Poly3 →ₗ[ℝ] Poly3)
    (hC : ∀ c : ℝ, D (MvPolynomial.C c) = 0)
    (hLeibniz : ∀ p q : Poly3, D (p * q) = p * D q + D p * q)
    (hX : ∀ k : Fin 3,
      HasDerivAt (fun t : ℝ => a t k)
        (MvPolynomial.aeval (a 0) (D (MvPolynomial.X k))) 0)
    (p : Poly3) :
    HasDerivAt (fun t : ℝ => MvPolynomial.aeval (a t) p)
      (MvPolynomial.aeval (a 0) (D p)) 0 := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simpa [hC c] using
        (hasDerivAt_const (0 : ℝ)
          (MvPolynomial.aeval (a 0) (MvPolynomial.C c)))
  | add p q hp hq =>
      simpa only [map_add] using hp.add hq
  | mul_X p k hp =>
      have h := hp.mul (hX k)
      convert h using 1 <;>
        simp only [map_mul, hLeibniz, MvPolynomial.aeval_X,
          map_add, map_mul] <;> ring

/-- Differentiating a polynomial orbit commutes with spherical integration.
No dominated-convergence argument is needed: integration is bounded on the
Banach space of continuous functions on the compact sphere. -/
theorem polynomial_orbit_integral_hasDerivAt
    (a : ℝ → Fin 3 → C(Sphere, ℝ)) (D : Poly3 →ₗ[ℝ] Poly3)
    (hC : ∀ c : ℝ, D (MvPolynomial.C c) = 0)
    (hLeibniz : ∀ p q : Poly3, D (p * q) = p * D q + D p * q)
    (hX : ∀ k : Fin 3,
      HasDerivAt (fun t : ℝ => a t k)
        (MvPolynomial.aeval (a 0) (D (MvPolynomial.X k))) 0)
    (p : Poly3) :
    HasDerivAt
      (fun t : ℝ => sigmaIntegralCLM (MvPolynomial.aeval (a t) p))
      (sigmaIntegralCLM (MvPolynomial.aeval (a 0) (D p))) 0 := by
  exact (sigmaIntegralCLM.hasFDerivAt).comp_hasDerivAt 0
    (polynomial_orbit_hasDerivAt a D hC hLeibniz hX p)

theorem angularDerivation_C (i j : Fin 3) (c : ℝ) :
    angularDerivation i j (MvPolynomial.C c) = 0 := by
  simp [angularDerivation]

theorem angularDerivation_X (i j k : Fin 3) :
    angularDerivation i j (MvPolynomial.X k) =
      (if k = j then MvPolynomial.X i else 0) -
        (if k = i then MvPolynomial.X j else 0) := by
  classical
  by_cases hkj : k = j <;> by_cases hki : k = i <;>
    simp [angularDerivation, MvPolynomial.pderiv_X, Pi.single_apply, hkj, hki]

/-- The infinitesimal generator of an integral-preserving polynomial orbit
has zero spherical integral. -/
theorem integral_derivation_zero_of_constant_orbit
    (a : ℝ → Fin 3 → C(Sphere, ℝ)) (D : Poly3 →ₗ[ℝ] Poly3)
    (hC : ∀ c : ℝ, D (MvPolynomial.C c) = 0)
    (hLeibniz : ∀ p q : Poly3, D (p * q) = p * D q + D p * q)
    (hX : ∀ k : Fin 3,
      HasDerivAt (fun t : ℝ => a t k)
        (MvPolynomial.aeval (a 0) (D (MvPolynomial.X k))) 0)
    (hconstant : ∀ (p : Poly3) (t : ℝ),
      sigmaIntegralCLM (MvPolynomial.aeval (a t) p) =
        sigmaIntegralCLM (MvPolynomial.aeval (a 0) p))
    (p : Poly3) :
    sigmaIntegralCLM (MvPolynomial.aeval (a 0) (D p)) = 0 := by
  have h := polynomial_orbit_integral_hasDerivAt a D hC hLeibniz hX p
  have hc : HasDerivAt
      (fun t : ℝ => sigmaIntegralCLM (MvPolynomial.aeval (a t) p)) 0 0 := by
    convert hasDerivAt_const (0 : ℝ)
      (sigmaIntegralCLM (MvPolynomial.aeval (a 0) p)) using 1 <;>
      ext t <;> exact hconstant p t
  exact h.unique hc

/-- A Cartesian coordinate, viewed as a continuous function on the sphere. -/
noncomputable def sphereCoordinate (k : Fin 3) : C(Sphere, ℝ) :=
  ⟨fun x => (x : Ambient) k,
    (continuous_apply k).comp continuous_subtype_val⟩

@[simp] theorem sphereCoordinate_apply (k : Fin 3) (x : Sphere) :
    sphereCoordinate k x = (x : Ambient) k := rfl

/-- Coordinates of the elementary rotation in the `i,j`-plane. -/
noncomputable def rotatedSphereCoordinates
    (i j : Fin 3) (θ : ℝ) (k : Fin 3) : C(Sphere, ℝ) :=
  if k = i then Real.cos θ • sphereCoordinate i - Real.sin θ • sphereCoordinate j
  else if k = j then Real.sin θ • sphereCoordinate i + Real.cos θ • sphereCoordinate j
  else sphereCoordinate k

theorem rotatedSphereCoordinates_zero (i j : Fin 3) (hij : i ≠ j)
    (k : Fin 3) :
    rotatedSphereCoordinates i j 0 k = sphereCoordinate k := by
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [rotatedSphereCoordinates, hki, hkj, hij, Ne.symm hij]

theorem rotatedSphereCoordinates_hasDerivAt (i j : Fin 3) (hij : i ≠ j)
    (k : Fin 3) :
    HasDerivAt (fun θ : ℝ => rotatedSphereCoordinates i j θ k)
      (MvPolynomial.aeval (rotatedSphereCoordinates i j 0)
        (angularDerivation i j (MvPolynomial.X k))) 0 := by
  classical
  by_cases hki : k = i
  · subst k
    have h := ((Real.hasDerivAt_cos 0).smul_const (sphereCoordinate i)).sub
      ((Real.hasDerivAt_sin 0).smul_const (sphereCoordinate j))
    simpa [rotatedSphereCoordinates, angularDerivation_X, rotatedSphereCoordinates_zero,
      hij, Ne.symm hij] using h
  by_cases hkj : k = j
  · subst k
    have h := ((Real.hasDerivAt_sin 0).smul_const (sphereCoordinate i)).add
      ((Real.hasDerivAt_cos 0).smul_const (sphereCoordinate j))
    simpa [rotatedSphereCoordinates, angularDerivation_X, rotatedSphereCoordinates_zero,
      hki, hij, Ne.symm hij] using h
  simpa [rotatedSphereCoordinates, hki, hkj, angularDerivation_X] using
    (hasDerivAt_const (0 : ℝ) (sphereCoordinate k))

theorem aeval_sphereCoordinate (p : Poly3) :
    MvPolynomial.aeval sphereCoordinate p = restrictPolynomial p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      ext x
      simp [restrictPolynomial_apply]
  | add p q hp hq =>
      ext x
      simpa [restrictPolynomial_apply] using congrArg (fun f : C(Sphere, ℝ) => f x)
        (show MvPolynomial.aeval sphereCoordinate (p + q) =
          restrictPolynomial p + restrictPolynomial q by simp [hp, hq])
  | mul_X p k hp =>
      ext x
      simp [hp, restrictPolynomial_apply, sphereCoordinate_apply]

theorem aeval_rotatedSphereCoordinates_zero (i j : Fin 3) (hij : i ≠ j)
    (p : Poly3) :
    MvPolynomial.aeval (rotatedSphereCoordinates i j 0) p =
      restrictPolynomial p := by
  have heq : rotatedSphereCoordinates i j 0 = sphereCoordinate := by
    funext k
    exact rotatedSphereCoordinates_zero i j hij k
  rw [heq]
  exact aeval_sphereCoordinate p

theorem aeval_continuous_apply (a : Fin 3 → C(Sphere, ℝ))
    (p : Poly3) (x : Sphere) :
    (MvPolynomial.aeval a p) x =
      MvPolynomial.eval (fun k => a k x) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => simp [hp]

theorem aeval_rotatedSphereCoordinates_apply (i j : Fin 3)
    (θ : ℝ) (p : Poly3) (x : Sphere) :
    (MvPolynomial.aeval (rotatedSphereCoordinates i j θ) p) x =
      MvPolynomial.eval (fun k =>
        if k = i then Real.cos θ * (x : Ambient) i - Real.sin θ * (x : Ambient) j
        else if k = j then Real.sin θ * (x : Ambient) i + Real.cos θ * (x : Ambient) j
        else (x : Ambient) k) p := by
  rw [aeval_continuous_apply]
  have hf : (fun k => (rotatedSphereCoordinates i j θ k) x) =
      (fun k =>
        if k = i then Real.cos θ * (x : Ambient) i - Real.sin θ * (x : Ambient) j
        else if k = j then Real.sin θ * (x : Ambient) i + Real.cos θ * (x : Ambient) j
        else (x : Ambient) k) := by
    funext k
    simp only [rotatedSphereCoordinates]
    split_ifs <;> simp [sphereCoordinate_apply, smul_eq_mul]
  rw [hf]

theorem rotatedSphereCoordinates_integral_invariant
    (i j : Fin 3) (hij : i ≠ j) (θ : ℝ) (p : Poly3) :
    sigmaIntegralCLM (MvPolynomial.aeval (rotatedSphereCoordinates i j θ) p) =
      sigmaIntegralCLM (restrictPolynomial p) := by
  let T := planeRotation i j hij θ
  have heq : MvPolynomial.aeval (rotatedSphereCoordinates i j θ) p =
      ⟨fun x : Sphere => restrictPolynomial p (sphereLinearIsometryMap T x),
        (restrictPolynomial p).continuous.comp
          (continuous_sphereLinearIsometryMap T)⟩ := by
    ext x
    rw [aeval_rotatedSphereCoordinates_apply]
    change _ = restrictPolynomial p (sphereLinearIsometryMap T x)
    rw [restrictPolynomial_apply]
    change MvPolynomial.eval _ p = MvPolynomial.eval (fun k => (T (x : Ambient)) k) p
    rfl
  rw [heq]
  exact sigmaIntegralCLM_isometry T (restrictPolynomial p)

/-- The integral of every angular derivative vanishes.  This is the
infinitesimal form of rotational invariance of normalized surface area. -/
theorem angular_integral_zero (i j : Fin 3) (p : Poly3) :
    (∫ x : Sphere, restrictPolynomial (angularDerivation i j p) x ∂sigma) = 0 := by
  by_cases hij : i = j
  · subst j
    have hz : angularDerivation i i p = 0 := by
      simp [angularDerivation]
    have hr : restrictPolynomial (0 : Poly3) = 0 := by
      ext x
      simp [restrictPolynomial_apply]
    simp [hz, hr]
  have hLeibniz (q r : Poly3) :
      angularDerivation i j (q * r) =
        q * angularDerivation i j r + angularDerivation i j q * r := by
    rw [angularDerivation_mul]
    abel
  have hconstant (q : Poly3) (θ : ℝ) :
      sigmaIntegralCLM (MvPolynomial.aeval (rotatedSphereCoordinates i j θ) q) =
        sigmaIntegralCLM (MvPolynomial.aeval (rotatedSphereCoordinates i j 0) q) := by
    rw [rotatedSphereCoordinates_integral_invariant i j hij θ q,
      aeval_rotatedSphereCoordinates_zero i j hij q]
  have hz := integral_derivation_zero_of_constant_orbit
    (rotatedSphereCoordinates i j) (angularDerivation i j)
    (angularDerivation_C i j) hLeibniz
    (rotatedSphereCoordinates_hasDerivAt i j hij) hconstant p
  rw [aeval_rotatedSphereCoordinates_zero i j hij] at hz
  simpa only [sigmaIntegralCLM_apply] using hz

end BEMOC.Definitive
