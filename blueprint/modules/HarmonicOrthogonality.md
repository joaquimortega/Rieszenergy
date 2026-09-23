# Harmonic orthogonality proof guide

The actual normalized spherical measure `sigma` is invariant under every ambient linear isometry. The proof passes through the cone definition of `volume.toSphere` and Mathlib's `LinearIsometryEquiv.measurePreserving`. Consequently, integration is invariant under all orthogonal changes of coordinates. In particular, antipodal parity proves orthogonality whenever the sum of the two homogeneous degrees is odd.

For all unequal degrees, `harmonic_restrictions_orthogonal_of_angular_integral_zero` is a checked reduction to one analytic premise: the integral of every polynomial angular derivative `Lᵢⱼ p = xᵢ∂ⱼp − xⱼ∂ᵢp` vanishes. The proof uses Leibniz to establish skew-adjointness, then self-adjointness of the sum of squared angular derivatives. `HarmonicCasimir.angularCasimir_harmonic` supplies the eigenvalue `−ℓ(ℓ+1)`, which is injective in nonnegative integer degree. The reduction is a theorem with an explicit premise, not an assertion that the premise has been proved.

The remaining analytic bridge is to derive `∫ Lᵢⱼp dσ = 0` from rotation invariance, for example by differentiating the polynomial integral along a one-parameter coordinate-plane rotation. Until that is formalized, this module does not establish full cross-degree orthogonality or an unconditional harmonic basis.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.HarmonicCasimir

open scoped Pointwise ENNReal NNReal
open MeasureTheory
namespace BEMOC.Definitive

/-- Every orthogonal change of ambient coordinates preserves normalized surface area. -/
theorem sigma_linear_isometry_invariant (T : Ambient ≃ₗᵢ[ℝ] Ambient) :
    Measure.map (sphereLinearIsometryEquiv T) sigma = sigma := by
  ext s hs
  rw [Measure.map_apply (sphereLinearIsometryEquiv T).measurable hs]
  unfold sigma
  rw [Measure.smul_apply, Measure.smul_apply]
  congr 1
  rw [Measure.toSphere_apply' volume
      ((sphereLinearIsometryEquiv T).measurable hs),
    Measure.toSphere_apply' volume hs]
  rw [sphereCone_preimage]
  congr 1
  exact T.measurePreserving.measure_preimage_emb
    T.toHomeomorph.measurableEmbedding _

/-- Spherical integration is unchanged by any ambient orthogonal map. -/
theorem integral_sigma_comp_linear_isometry (T : Ambient ≃ₗᵢ[ℝ] Ambient)
    (f : Sphere → ℝ) :
    (∫ x : Sphere, f (sphereLinearIsometryEquiv T x) ∂sigma) =
      ∫ x : Sphere, f x ∂sigma := by
  rw [← integral_map_equiv (sphereLinearIsometryEquiv T) (μ := sigma) f,
    sigma_linear_isometry_invariant]

/-- Antipodal reflection preserves the normalized spherical measure. -/
theorem sigma_antipodal_invariant :
    Measure.map (sphereLinearIsometryEquiv
      (LinearIsometryEquiv.neg ℝ : Ambient ≃ₗᵢ[ℝ] Ambient)) sigma = sigma := by
  let T : Ambient ≃ₗᵢ[ℝ] Ambient := LinearIsometryEquiv.neg ℝ
  change Measure.map (sphereLinearIsometryEquiv T) sigma = sigma
  ext s hs
  rw [Measure.map_apply (sphereLinearIsometryEquiv T).measurable hs]
  unfold sigma
  rw [Measure.smul_apply, Measure.smul_apply]
  congr 1
  rw [Measure.toSphere_apply' volume
      ((sphereLinearIsometryEquiv T).measurable hs),
    Measure.toSphere_apply' volume hs]
  rw [sphereCone_preimage]
  change _ * volume ((T.toLinearEquiv : Ambient → Ambient) ⁻¹'
      (Set.Ioo (0 : ℝ) 1 • ((fun x : Sphere ↦ (x : Ambient)) '' s))) = _
  rw [Measure.addHaar_preimage_linearEquiv volume T.toLinearEquiv]
  have hdet :
      |LinearMap.det (T.symm.toLinearEquiv : Ambient →ₗ[ℝ] Ambient)| = 1 := by
    have heq : (T.symm.toLinearEquiv : Ambient →ₗ[ℝ] Ambient) =
        (-1 : ℝ) • LinearMap.id := by
      ext x
      simp [T]
    rw [heq, LinearMap.det_smul, LinearMap.det_id, mul_one,
      finrank_euclideanSpace]
    norm_num
  change _ * (ENNReal.ofReal
      |LinearMap.det (T.symm.toLinearEquiv : Ambient →ₗ[ℝ] Ambient)| * _) = _
  rw [hdet]
  norm_num

/-- Each monomial scales by its total degree when all coordinates scale. -/
private theorem monomial_eval_scaled (d : Fin 3 →₀ ℕ) (c : ℝ)
    (x : Fin 3 → ℝ) :
    d.prod (fun i e => (c * x i) ^ e) =
      c ^ d.degree * d.prod (fun i e => x i ^ e) := by
  rw [Finsupp.prod_pow, Finsupp.prod_pow]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact (Finset.sum_subset (Finset.subset_univ d.support) (fun i _ hi => by
    simpa using (Finsupp.not_mem_support_iff.mp hi))).symm

/-- A genuinely homogeneous polynomial scales by its declared degree. -/
theorem homogeneous_eval_scaled {m : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p.IsHomogeneous m) (c : ℝ) (x : Fin 3 → ℝ) :
    MvPolynomial.eval (fun i => c * x i) p =
      c ^ m * MvPolynomial.eval x p := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  conv_rhs => rw [MvPolynomial.as_sum p]
  rw [MvPolynomial.eval_sum, MvPolynomial.eval_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
    monomial_eval_scaled]
  have hdeg : d.degree = m := by
    simpa [Finsupp.degree_eq_weight_one] using
      hp (MvPolynomial.mem_support_iff.mp hd)
  rw [hdeg]
  ring

/-- Antipodal parity of the restriction of a homogeneous polynomial. -/
theorem restrictPolynomial_antipodal {m : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p.IsHomogeneous m)
    (x : Sphere) :
    restrictPolynomial p
      (sphereLinearIsometryEquiv
        (LinearIsometryEquiv.neg ℝ : Ambient ≃ₗᵢ[ℝ] Ambient) x) =
      (-1 : ℝ) ^ m * restrictPolynomial p x := by
  rw [restrictPolynomial_apply, restrictPolynomial_apply]
  change MvPolynomial.eval (fun i => -((x : Ambient) i)) p =
    (-1 : ℝ) ^ m * MvPolynomial.eval (fun i => (x : Ambient) i) p
  simpa only [neg_one_mul] using
    homogeneous_eval_scaled hp (-1) (fun i => (x : Ambient) i)

/-- Homogeneous restrictions of opposite parity are orthogonal. -/
theorem homogeneous_restrictions_orthogonal_of_odd_sum
    {m n : ℕ} {p q : MvPolynomial (Fin 3) ℝ}
    (hp : p.IsHomogeneous m) (hq : q.IsHomogeneous n)
    (hodd : Odd (m + n)) :
    (∫ x : Sphere, restrictPolynomial p x * restrictPolynomial q x ∂sigma) = 0 := by
  let e := sphereLinearIsometryEquiv
    (LinearIsometryEquiv.neg ℝ : Ambient ≃ₗᵢ[ℝ] Ambient)
  have hmap := integral_map_equiv e
    (μ := sigma) (fun x : Sphere => restrictPolynomial p x * restrictPolynomial q x)
  rw [sigma_antipodal_invariant] at hmap
  have hpoint (x : Sphere) :
      restrictPolynomial p (e x) * restrictPolynomial q (e x) =
        (-1 : ℝ) ^ (m + n) *
          (restrictPolynomial p x * restrictPolynomial q x) := by
    rw [restrictPolynomial_antipodal hp,
      restrictPolynomial_antipodal hq, pow_add]
    ring
  simp_rw [hpoint] at hmap
  rw [integral_const_mul, Odd.neg_one_pow hodd] at hmap
  linarith

private theorem restrictPolynomial_mul_apply (p q : Poly3) (x : Sphere) :
    restrictPolynomial (p * q) x = restrictPolynomial p x * restrictPolynomial q x := by
  simp [restrictPolynomial_apply]

private theorem restrictPolynomial_add_apply (p q : Poly3) (x : Sphere) :
    restrictPolynomial (p + q) x = restrictPolynomial p x + restrictPolynomial q x := by
  simp [restrictPolynomial_apply]

private theorem restrictPolynomial_smul_apply (c : ℝ) (p : Poly3) (x : Sphere) :
    restrictPolynomial (c • p) x = c * restrictPolynomial p x := by
  simp [restrictPolynomial_apply, smul_eq_mul]

/-- The sole analytic bridge needed to turn the polynomial Casimir identity into
cross-degree orthogonality is the vanishing of integral angular derivatives. -/
theorem harmonic_restrictions_orthogonal_of_angular_integral_zero
    (hrotation : ∀ (i j : Fin 3) (p : Poly3),
      (∫ x : Sphere, restrictPolynomial (angularDerivation i j p) x ∂sigma) = 0)
    {m n : ℕ} {p q : Poly3}
    (hp : p ∈ harmonicPolynomialSubmodule m)
    (hq : q ∈ harmonicPolynomialSubmodule n)
    (hmn : m ≠ n) :
    (∫ x : Sphere, restrictPolynomial p x * restrictPolynomial q x ∂sigma) = 0 := by
  have hskew (i j : Fin 3) (a b : Poly3) :
      (∫ x : Sphere, restrictPolynomial (angularDerivation i j a) x *
        restrictPolynomial b x ∂sigma) =
      -(∫ x : Sphere, restrictPolynomial a x *
        restrictPolynomial (angularDerivation i j b) x ∂sigma) := by
    have h := hrotation i j (a * b)
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
  obtain ⟨hphom, hplap⟩ := mem_harmonicPolynomialSubmodule.mp hp
  obtain ⟨hqhom, hqlap⟩ := mem_harmonicPolynomialSubmodule.mp hq
  rw [angularCasimir_harmonic hphom hplap,
    angularCasimir_harmonic hqhom hqlap] at hcas
  simp_rw [restrictPolynomial_smul_apply] at hcas
  have hcas' :
      (-(m : ℝ) * (m + 1)) *
          (∫ x : Sphere, restrictPolynomial p x * restrictPolynomial q x ∂sigma) =
        (-(n : ℝ) * (n + 1)) *
          (∫ x : Sphere, restrictPolynomial p x * restrictPolynomial q x ∂sigma) := by
    calc
      _ = ∫ x : Sphere, -(m : ℝ) * (m + 1) *
            (restrictPolynomial p x * restrictPolynomial q x) ∂sigma := by
        rw [integral_const_mul]
      _ = ∫ x : Sphere, restrictPolynomial p x *
            (-(n : ℝ) * (n + 1) * restrictPolynomial q x) ∂sigma := by
        convert hcas using 1 <;> congr 1 <;> funext x <;> ring
      _ = _ := by
        simp_rw [show ∀ x : Sphere,
          restrictPolynomial p x * (-(n : ℝ) * (n + 1) * restrictPolynomial q x) =
          (-(n : ℝ) * (n + 1)) *
            (restrictPolynomial p x * restrictPolynomial q x) from fun x => by ring]
        rw [integral_const_mul]
  have heig : (m : ℝ) * (m + 1) ≠ (n : ℝ) * (n + 1) := by
    intro heq
    have : (m : ℝ) = n := by nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n]
    exact hmn (Nat.cast_injective this)
  exact (mul_eq_zero.mp (by nlinarith [hcas'] :
    (((m : ℝ) * (m + 1)) - ((n : ℝ) * (n + 1))) *
      (∫ x : Sphere, restrictPolynomial p x * restrictPolynomial q x ∂sigma) = 0)).resolve_left
    (sub_ne_zero.mpr heig)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
