# Coordinate-plane rotation proof guide

For distinct indices `i,j : Fin 3`, `planeRotation i j hij θ` is an explicit real-linear isometric equivalence of `Ambient = EuclideanSpace ℝ (Fin 3)`. Its `i` coordinate is `cos θ · xᵢ − sin θ · xⱼ`, its `j` coordinate is `sin θ · xᵢ + cos θ · xⱼ`, and the third coordinate is fixed. The sign convention gives infinitesimal velocity `−xⱼ` in coordinate `i` and `xᵢ` in coordinate `j`, matching `angularDerivation i j = Xᵢ∂ⱼ − Xⱼ∂ᵢ`.

The proof first constructs a coordinatewise linear map, then proves inner-product preservation by six finite index cases and `sin² θ + cos² θ = 1`. The inverse is the same map at `−θ`; its left and right inverse identities use only three coordinate cases. `planeRotation_zero` and `planeRotation_hasDerivAt_coord` expose the two facts needed for differentiating a polynomial orbit. All statements refer to the actual ambient Hilbert space, so the isometry can be passed directly to `sigma_linear_isometry_invariant`.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.HarmonicOrthogonality

namespace BEMOC.Definitive

/-- Cartesian coordinates after a rotation in the `i,j` plane. -/
noncomputable def planeRotationCoords (i j : Fin 3) (θ : ℝ) (x : Ambient) : Ambient :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun k =>
    if k = i then Real.cos θ * x i - Real.sin θ * x j
    else if k = j then Real.sin θ * x i + Real.cos θ * x j
    else x k)

@[simp] theorem planeRotationCoords_apply (i j k : Fin 3) (θ : ℝ) (x : Ambient) :
    planeRotationCoords i j θ x k =
      (if k = i then Real.cos θ * x i - Real.sin θ * x j
       else if k = j then Real.sin θ * x i + Real.cos θ * x j
       else x k) := rfl

/-- The coordinate rotation is real-linear. -/
noncomputable def planeRotationLinear (i j : Fin 3) (θ : ℝ) :
    Ambient →ₗ[ℝ] Ambient where
  toFun := planeRotationCoords i j θ
  map_add' x y := by
    ext k
    simp only [planeRotationCoords_apply, PiLp.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    ext k
    simp only [planeRotationCoords_apply, PiLp.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    split_ifs <;> ring

@[simp] theorem planeRotationLinear_apply (i j k : Fin 3) (θ : ℝ) (x : Ambient) :
    planeRotationLinear i j θ x k =
      (if k = i then Real.cos θ * x i - Real.sin θ * x j
       else if k = j then Real.sin θ * x i + Real.cos θ * x j
       else x k) := rfl

/-- A coordinate-plane rotation preserves the Euclidean inner product. -/
theorem planeRotationLinear_inner (i j : Fin 3) (hij : i ≠ j) (θ : ℝ)
    (x y : Ambient) :
    (@Inner.inner ℝ Ambient _ (planeRotationLinear i j θ x)
      (planeRotationLinear i j θ y)) = (@Inner.inner ℝ Ambient _ x y) := by
  have htrig := Real.sin_sq_add_cos_sq θ
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three,
    WithLp.equiv_pi_apply, planeRotationLinear_apply, RCLike.star_def, star_trivial]
  fin_cases i <;> fin_cases j
  all_goals simp [Fin.reduceEq] at hij ⊢
  all_goals first
    | linear_combination (x 0 * y 0 + x 1 * y 1) * htrig
    | linear_combination (x 0 * y 0 + x 2 * y 2) * htrig
    | linear_combination (x 1 * y 1 + x 2 * y 2) * htrig

/-- The explicit orthogonal coordinate-plane rotation. -/
noncomputable def planeRotation (i j : Fin 3) (hij : i ≠ j) (θ : ℝ) :
    Ambient ≃ₗᵢ[ℝ] Ambient := by
  let f : Ambient →ₗᵢ[ℝ] Ambient :=
    (planeRotationLinear i j θ).isometryOfInner
      (planeRotationLinear_inner i j hij θ)
  apply LinearIsometryEquiv.ofLinearIsometry f (planeRotationLinear i j (-θ))
  · ext x k
    change planeRotationLinear i j θ (planeRotationLinear i j (-θ) x) k = x k
    by_cases hki : k = i
    · subst k
      simp [planeRotationLinear_apply, hij, hij.symm, Real.cos_neg, Real.sin_neg]
      linear_combination (x i) * (Real.sin_sq_add_cos_sq θ)
    by_cases hkj : k = j
    · subst k
      simp [planeRotationLinear_apply, hij, hij.symm, Real.cos_neg, Real.sin_neg]
      linear_combination (x j) * (Real.sin_sq_add_cos_sq θ)
    simp [planeRotationLinear_apply, hki, hkj]
  · ext x k
    change planeRotationLinear i j (-θ) (planeRotationLinear i j θ x) k = x k
    by_cases hki : k = i
    · subst k
      simp [planeRotationLinear_apply, hij, hij.symm, Real.cos_neg, Real.sin_neg]
      linear_combination (x i) * (Real.sin_sq_add_cos_sq θ)
    by_cases hkj : k = j
    · subst k
      simp [planeRotationLinear_apply, hij, hij.symm, Real.cos_neg, Real.sin_neg]
      linear_combination (x j) * (Real.sin_sq_add_cos_sq θ)
    simp [planeRotationLinear_apply, hki, hkj]

@[simp] theorem planeRotation_apply (i j k : Fin 3) (hij : i ≠ j)
    (θ : ℝ) (x : Ambient) :
    planeRotation i j hij θ x k =
      (if k = i then Real.cos θ * x i - Real.sin θ * x j
       else if k = j then Real.sin θ * x i + Real.cos θ * x j
       else x k) := rfl

/-- Zero-angle rotation is the identity. -/
theorem planeRotation_zero (i j : Fin 3) (hij : i ≠ j) :
    planeRotation i j hij 0 = LinearIsometryEquiv.refl ℝ Ambient := by
  ext x k
  change planeRotation i j hij 0 x k = x k
  simp only [planeRotation_apply, Real.cos_zero, Real.sin_zero,
    one_mul, zero_mul, sub_zero, zero_add]
  split_ifs with hki hkj <;> subst_vars <;> rfl

/-- The velocity of each Cartesian coordinate under a plane rotation. -/
theorem planeRotation_hasDerivAt_coord (i j k : Fin 3) (hij : i ≠ j)
    (x : Ambient) :
    HasDerivAt (fun θ : ℝ => planeRotation i j hij θ x k)
      (if k = i then -x j else if k = j then x i else 0) 0 := by
  by_cases hki : k = i
  · subst k
    have h := ((Real.hasDerivAt_cos 0).mul_const (x i)).sub
      ((Real.hasDerivAt_sin 0).mul_const (x j))
    simpa [planeRotation_apply, hij, hij.symm] using h
  by_cases hkj : k = j
  · subst k
    have h := ((Real.hasDerivAt_sin 0).mul_const (x i)).add
      ((Real.hasDerivAt_cos 0).mul_const (x j))
    simpa [planeRotation_apply, hki, hij, hij.symm] using h
  simpa [planeRotation_apply, hki, hkj] using
    (hasDerivAt_const (0 : ℝ) (x k))

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
