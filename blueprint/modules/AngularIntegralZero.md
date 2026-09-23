# AngularIntegralZero proof guide

This module closes the analytic bridge between invariance of normalized sphere measure under rigid rotations and orthogonality of spherical harmonics of different degrees. The exact target is `angular_integral_zero`: for every polynomial `p` in the three Cartesian coordinates and every pair `i,j`, the integral over the sphere of the restriction of `angularDerivation i j p` vanishes. Here `angularDerivation i j = X_i ∂_j − X_j ∂_i` is the existing algebraic derivation of `HarmonicCasimir.lean`. The theorem does not assume that `p` is harmonic or homogeneous. That generality is necessary downstream: the skew-adjointness proof applies the identity to products of arbitrary polynomials, then applies it again to derivatives of those polynomials.

The geometric input is `PlaneRotation.lean`. For `i≠j`, its `planeRotation i j hij θ` is a genuine ambient linear isometry, whose `i` coordinate is `cos θ·x_i − sin θ·x_j` and `j` coordinate is `sin θ·x_i + cos θ·x_j`. `HarmonicOrthogonality.integral_sigma_comp_linear_isometry` states that integration against `sigma` is invariant under any such isometry. The sign of this rotation is important: at `θ=0`, the coordinate velocities are `−x_j` and `x_i`, respectively, so its polynomial generator is exactly `X_i ∂_j − X_j ∂_i`. A reversed convention would give the negative derivation but still prove vanishing; the checked proof uses the positive convention consistently.

The derivative is taken in the Banach space `C(Sphere,ℝ)` to avoid a parameterized-integral domination theorem. `sigmaIntegralCLM` is the bounded integral functional, realized through `sigmaPairingCLM 1`; its norm bound comes from the probability measure statement `sigma_apply_univ=1`. `sigmaIntegralCLM_isometry` records invariance of that functional when a continuous function is composed with `sphereLinearIsometryMap`. This is an equality of actual sphere integrals, not an invariance axiom.

`polynomial_orbit_hasDerivAt` is a reusable chain rule for polynomial substitution into `Fin 3 → C(Sphere,ℝ)` curves. It assumes a polynomial linear derivation `D` vanishing on constants and satisfying Leibniz, plus the required derivative on each generator `X_k`. The proof uses `MvPolynomial.induction_on`: constants have derivative zero, addition uses `HasDerivAt.add`, and multiplication by a variable uses the Banach-algebra product rule. Its target derivative is the substituted value of `D p`. Applying `sigmaIntegralCLM.hasFDerivAt` gives `polynomial_orbit_integral_hasDerivAt`. `integral_derivation_zero_of_constant_orbit` then compares this derivative with the zero derivative of a constant scalar function. It is an abstract theorem: all geometric specialization occurs afterward.

`sphereCoordinate k` and `rotatedSphereCoordinates i j θ k` provide the concrete continuous-map curves. The zero-angle lemma identifies their starting coordinates with the ordinary sphere coordinates. `rotatedSphereCoordinates_hasDerivAt` checks the generator condition with `Real.hasDerivAt_sin`, `Real.hasDerivAt_cos`, and the explicit `angularDerivation_X` formula, including the unaffected third coordinate. `aeval_sphereCoordinate` and `aeval_rotatedSphereCoordinates_zero` identify polynomial substitution at zero with the existing `restrictPolynomial`, ensuring the conclusion has precisely the API needed by `HarmonicOrthogonality`.

For arbitrary `θ`, `aeval_rotatedSphereCoordinates_apply` reduces substituted polynomial evaluation to Cartesian evaluation at the rotated coordinates. `rotatedSphereCoordinates_integral_invariant` identifies this continuous function with `restrictPolynomial p` composed with `sphereLinearIsometryMap (planeRotation ...)`, then invokes `sigmaIntegralCLM_isometry`. The integral orbit is therefore constant in `θ`. The abstract constant-orbit theorem gives the desired vanishing. When `i=j`, the derivation is identically zero and the integral vanishes directly. No differential equation, interchange of unbounded limits, auxiliary measure, or unproved regularity statement is used.

`HarmonicBasisExistence.lean` consumes `angular_integral_zero` to remove the final premise of the Casimir-based cross-degree theorem. The module should remain imported after `PlaneRotation.lean` and `HarmonicOrthogonality.lean`. The checked target command is `lake build BEMOCFormalization.AngularIntegralZero`.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
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
```

<!-- END_LEAN_STATEMENTS -->
