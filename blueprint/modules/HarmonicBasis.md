# HarmonicBasis proof guide

This module is the algebraic foundation for the *actual* notion of spherical harmonic in `Sobolev.lean`: a real homogeneous polynomial in three variables annihilated by the stated Euclidean polynomial Laplacian, restricted to the unit sphere. The `harmonicPolynomialSubmodule ℓ` is exactly the intersection of mathlib's homogeneous submodule and the kernel of `polynomialLaplacianLinearMap`. The theorem `isSphericalHarmonic_iff_range` connects this submodule to the original predicate without changing its semantics. Do not replace it with abstract eigenfunctions, an assumed Hilbert basis, or a new shortcut axiom.

The starting source is the manuscript's degree-ℓ harmonic restriction; the Lean dependencies are `Sobolev`, `SurfaceMeasure`, mathlib's homogeneous multivariate polynomials, Euler identity, and Stone–Weierstrass. `polynomialLaplacian_isHomogeneous` proves the two-derivative degree shift. Constants and coordinates give explicit degree-zero and degree-one harmonics; Euler's identity proves every homogeneous linear polynomial is harmonic. `degreeZeroHarmonicEquiv` and `degreeOneHarmonicEquiv` make the low-degree dimensions 1 and 3. `finiteDimensional_homogeneousPolynomial` uses finite exponent vectors and `Finsupp.supportedEquivFinsupp`, and `finrank_homogeneous_eq_degreeMonomials_card` reduces arbitrary homogeneous dimensions to stars-and-bars. The independent `HarmonicMonomialCount` module completes that count.

The restriction map is a real linear map and an algebra homomorphism into `C(Sphere,ℝ)`. Its range subalgebra separates points by coordinate evaluation, so `polynomialRestriction_dense` is a direct Stone–Weierstrass result. The homogeneous scaling law, `homogeneous_eval_scale`, is proved by expanding the polynomial over monomial support and using the common degree of every nonzero coefficient. It yields `homogeneous_restrict_injective`: normalize a nonzero ambient vector to a sphere point, handle the origin separately in degrees zero and positive, then apply mathlib's `IsHomogeneous.eq_zero_of_forall_eval_eq_zero`. Thus restriction does not collapse any fixed-degree harmonic dimension. `restrictHarmonicLinearMap_injective` packages this for later finite-dimensional basis construction.

The Fischer calculation uses `radialSquare=X₀²+X₁²+X₂²`. Its sphere evaluation is exactly one, so radial-square multiplication does not change a restricted function. Product differentiation gives `Δ(r²p)=(4m+6)p+r²Δp` for homogeneous degree m. The checked `radialPower_laplacian` generalizes this to `r^(2(k+1))p`, with coefficient `2(k+1)(2m+2k+3)`. That coefficient is strictly positive for all natural m and k. `radialPower_laplacian_harmonic` removes the residual term when `p` is harmonic, and `harmonic_laplacian_preimage` explicitly lifts each harmonic polynomial two degrees. These exact formulas feed `FischerDecomposition`, whose induction proves every homogeneous polynomial is spanned by radial powers of harmonics.

The remaining construction of a `HarmonicBasis` is outside this foundational file. `FischerDecomposition` proves density of genuine harmonic restrictions, `HarmonicDimension` proves `dim Hℓ=2ℓ+1`, `SphereSupport` makes the surface L² pairing positive definite, and `HarmonicOrthonormal` constructs a finite orthonormal basis in each degree. `HarmonicBasisAssembly` now proves completeness and derives `Nonempty HarmonicBasis` from the precise cross-degree sphere integral identity. `AngularIntegralZero` and `HarmonicOrthogonality` prove that identity, and `HarmonicBasisExistence.harmonicBasis_nonempty` exports the unconditional `Nonempty HarmonicBasis` theorem.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Sobolev
import BEMOCFormalization.SurfaceMeasure
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.Finsupp.Weight
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! Algebraic foundations for the actual homogeneous harmonic polynomials used by `Sobolev`.
No basis existence is asserted here until dimension, orthogonality, and density are proved. -/

open scoped BigOperators
open MeasureTheory
namespace BEMOC.Definitive

/-- The Euclidean polynomial Laplacian as a real linear map. -/
noncomputable def polynomialLaplacianLinearMap :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3,
    ((MvPolynomial.pderiv i).toLinearMap).comp
      ((MvPolynomial.pderiv i).toLinearMap)

theorem polynomialLaplacianLinearMap_apply (p : MvPolynomial (Fin 3) ℝ) :
    polynomialLaplacianLinearMap p = polynomialLaplacian p := by
  rfl

/-- Degree-`ℓ` homogeneous polynomials annihilated by the manuscript's Laplacian. -/
noncomputable def harmonicPolynomialSubmodule (ℓ : ℕ) :
    Submodule ℝ (MvPolynomial (Fin 3) ℝ) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) ℝ ℓ ⊓
    LinearMap.ker polynomialLaplacianLinearMap

theorem mem_harmonicPolynomialSubmodule {ℓ : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} :
    p ∈ harmonicPolynomialSubmodule ℓ ↔
      p.IsHomogeneous ℓ ∧ polynomialLaplacian p = 0 := by
  simp [harmonicPolynomialSubmodule, polynomialLaplacianLinearMap_apply]

/-- Two polynomial derivatives lower homogeneous degree by two. -/
theorem polynomialLaplacian_isHomogeneous {ℓ : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p.IsHomogeneous ℓ) :
    (polynomialLaplacian p).IsHomogeneous (ℓ - 2) := by
  unfold polynomialLaplacian
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  have h := (hp.pderiv (i := i)).pderiv (i := i)
  convert h using 1

/-- Constants are genuine degree-zero harmonic polynomials. -/
theorem constant_mem_harmonicPolynomialSubmodule (c : ℝ) :
    MvPolynomial.C c ∈ harmonicPolynomialSubmodule 0 := by
  rw [mem_harmonicPolynomialSubmodule]
  constructor
  · exact MvPolynomial.isHomogeneous_C (Fin 3) c
  · simp [polynomialLaplacian]

/-- Coordinate polynomials are genuine degree-one harmonics. -/
theorem coordinate_mem_harmonicPolynomialSubmodule (i : Fin 3) :
    MvPolynomial.X i ∈ harmonicPolynomialSubmodule 1 := by
  rw [mem_harmonicPolynomialSubmodule]
  constructor
  · exact MvPolynomial.isHomogeneous_X ℝ i
  · classical
    simp [polynomialLaplacian, MvPolynomial.pderiv_X, Pi.single_apply]
    apply Finset.sum_eq_zero
    intro x _
    split_ifs <;> simp

/-- Restrict a polynomial to the sphere as a continuous real function. -/
noncomputable def restrictPolynomial (p : MvPolynomial (Fin 3) ℝ) : C(Sphere, ℝ) :=
  ⟨fun x => MvPolynomial.eval (fun i => (x : Ambient) i) p,
    (MvPolynomial.continuous_eval p).comp
      ((continuous_pi_iff).2 (fun i => (continuous_apply i).comp continuous_subtype_val))⟩

theorem restrictPolynomial_apply (p : MvPolynomial (Fin 3) ℝ) (x : Sphere) :
    restrictPolynomial p x = MvPolynomial.eval (fun i => (x : Ambient) i) p := rfl

/-- Polynomial restriction is linear in the polynomial. -/
noncomputable def restrictPolynomialLinearMap :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] C(Sphere, ℝ) where
  toFun := restrictPolynomial
  map_add' := by
    intro p q
    ext x
    simp [restrictPolynomial, MvPolynomial.eval_add]
  map_smul' := by
    intro c p
    ext x
    simp [restrictPolynomial, smul_eq_mul]

/-- Every algebraic harmonic polynomial gives exactly the harmonic notion in `Sobolev`. -/
theorem restrictPolynomial_isSphericalHarmonic {ℓ : ℕ}
    {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ harmonicPolynomialSubmodule ℓ) :
    IsSphericalHarmonic ℓ (restrictPolynomial p) := by
  obtain ⟨hhom, hlap⟩ := mem_harmonicPolynomialSubmodule.mp hp
  exact ⟨p, hhom, hlap, fun _ => rfl⟩

/-- The exact `Sobolev` predicate is the range of the algebraic harmonic subspace. -/
theorem isSphericalHarmonic_iff_range (ℓ : ℕ) (Y : C(Sphere, ℝ)) :
    IsSphericalHarmonic ℓ Y ↔
      ∃ p : harmonicPolynomialSubmodule ℓ, Y = restrictPolynomial p.val := by
  constructor
  · rintro ⟨p, hhom, hlap, hY⟩
    refine ⟨⟨p, mem_harmonicPolynomialSubmodule.mpr ⟨hhom, hlap⟩⟩, ?_⟩
    ext x
    exact hY x
  · rintro ⟨p, rfl⟩
    exact restrictPolynomial_isSphericalHarmonic p.property

/-- A concrete nonzero degree-zero spherical harmonic. -/
theorem constant_one_isSphericalHarmonic :
    IsSphericalHarmonic 0 (restrictPolynomial (MvPolynomial.C 1)) :=
  restrictPolynomial_isSphericalHarmonic (constant_mem_harmonicPolynomialSubmodule 1)

/-- Three concrete degree-one spherical harmonics. -/
theorem coordinate_isSphericalHarmonic (i : Fin 3) :
    IsSphericalHarmonic 1 (restrictPolynomial (MvPolynomial.X i)) :=
  restrictPolynomial_isSphericalHarmonic (coordinate_mem_harmonicPolynomialSubmodule i)

/-- Every degree-zero homogeneous polynomial is a constant polynomial. -/
theorem homogeneous_zero_eq_constant {p : MvPolynomial (Fin 3) ℝ}
    (hp : p.IsHomogeneous 0) :
    p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
  open MvPolynomial in
  exact totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp)

/-- Euler's identity shows that degree-one homogeneous polynomials are
linear combinations of the three coordinate polynomials. -/
theorem homogeneous_one_eq_coordinates {p : MvPolynomial (Fin 3) ℝ}
    (hp : p.IsHomogeneous 1) :
    p = ∑ i : Fin 3, MvPolynomial.X i *
      MvPolynomial.C (MvPolynomial.coeff 0 ((MvPolynomial.pderiv i) p)) := by
  have heuler := hp.sum_X_mul_pderiv
  simp only [one_nsmul] at heuler
  calc
    p = ∑ i : Fin 3, MvPolynomial.X i * (MvPolynomial.pderiv i) p := heuler.symm
    _ = ∑ i : Fin 3, MvPolynomial.X i *
          MvPolynomial.C (MvPolynomial.coeff 0 ((MvPolynomial.pderiv i) p)) := by
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs => rw [homogeneous_zero_eq_constant (hp.pderiv (i := i))]

/-- The polynomial Laplacian commutes with real scalar multiplication. -/
theorem polynomialLaplacian_smul (c : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    polynomialLaplacian (c • p) = c • polynomialLaplacian p := by
  rw [← polynomialLaplacianLinearMap_apply,
    map_smul, polynomialLaplacianLinearMap_apply]

/-- The polynomial Laplacian commutes with finite sums. -/
theorem polynomialLaplacian_sum {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin 3) ℝ) :
    polynomialLaplacian (∑ i ∈ s, f i) =
      ∑ i ∈ s, polynomialLaplacian (f i) := by
  rw [← polynomialLaplacianLinearMap_apply, map_sum]
  simp only [polynomialLaplacianLinearMap_apply]

/-- Every homogeneous linear polynomial is harmonic, not merely the coordinate generators. -/
theorem homogeneous_one_laplacian_zero {p : MvPolynomial (Fin 3) ℝ}
    (hp : p.IsHomogeneous 1) : polynomialLaplacian p = 0 := by
  rw [homogeneous_one_eq_coordinates hp, polynomialLaplacian_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_comm, ← MvPolynomial.smul_eq_C_mul,
    polynomialLaplacian_smul]
  have hcoord := (mem_harmonicPolynomialSubmodule.mp
    (coordinate_mem_harmonicPolynomialSubmodule i)).2
  rw [hcoord]
  simp

/-- In degrees zero and one the harmonic subspace is the whole homogeneous subspace. -/
theorem homogeneous_zero_laplacian_zero {p : MvPolynomial (Fin 3) ℝ}
    (hp : p.IsHomogeneous 0) : polynomialLaplacian p = 0 := by
  rw [homogeneous_zero_eq_constant hp]
  exact (mem_harmonicPolynomialSubmodule.mp
    (constant_mem_harmonicPolynomialSubmodule _)).2

/-- The degree-zero harmonic polynomial space is exactly the constants. -/
noncomputable def degreeZeroHarmonicEquiv :
    ℝ ≃ₗ[ℝ] harmonicPolynomialSubmodule 0 where
  toFun c := ⟨MvPolynomial.C c, constant_mem_harmonicPolynomialSubmodule c⟩
  invFun p := MvPolynomial.coeff 0 p.val
  left_inv c := by simp
  right_inv p := by
    apply Subtype.ext
    exact (homogeneous_zero_eq_constant
      (mem_harmonicPolynomialSubmodule.mp p.property).1).symm
  map_add' c d := by
    apply Subtype.ext
    simp
  map_smul' c d := by
    apply Subtype.ext
    simp [MvPolynomial.smul_eq_C_mul]

theorem finrank_harmonicPolynomialSubmodule_zero :
    Module.finrank ℝ (harmonicPolynomialSubmodule 0) = 1 := by
  rw [← degreeZeroHarmonicEquiv.finrank_eq]
  simp

/-- The coefficient of `Xᵢ` in a homogeneous linear polynomial, obtained by
differentiating and reading its constant coefficient. -/
noncomputable def linearCoefficient (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) : ℝ :=
  MvPolynomial.coeff 0 ((MvPolynomial.pderiv i) p)

theorem linearCoefficient_coordinates (v : Fin 3 → ℝ) (i : Fin 3) :
    linearCoefficient (∑ j : Fin 3, v j • MvPolynomial.X j) i = v i := by
  classical
  simp [linearCoefficient, map_sum, map_smul,
    MvPolynomial.pderiv_X, Pi.single_apply]

/-- The degree-one harmonic polynomial space has exactly three coordinates. -/
noncomputable def degreeOneHarmonicEquiv :
    (Fin 3 → ℝ) ≃ₗ[ℝ] harmonicPolynomialSubmodule 1 where
  toFun v := ⟨∑ i : Fin 3, v i • MvPolynomial.X i, by
    apply (harmonicPolynomialSubmodule 1).sum_mem
    intro i _
    exact (harmonicPolynomialSubmodule 1).smul_mem _
      (coordinate_mem_harmonicPolynomialSubmodule i)⟩
  invFun p := linearCoefficient p.val
  left_inv v := by
    funext i
    exact linearCoefficient_coordinates v i
  right_inv p := by
    apply Subtype.ext
    have hp := (mem_harmonicPolynomialSubmodule.mp p.property).1
    simpa only [linearCoefficient, MvPolynomial.smul_eq_C_mul, mul_comm] using
      (homogeneous_one_eq_coordinates hp).symm
  map_add' v w := by
    apply Subtype.ext
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Submodule.coe_add]
  map_smul' c v := by
    apply Subtype.ext
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul,
      Submodule.coe_smul, RingHom.id_apply]
    simp only [smul_eq_mul]

theorem finrank_harmonicPolynomialSubmodule_one :
    Module.finrank ℝ (harmonicPolynomialSubmodule 1) = 3 := by
  rw [← degreeOneHarmonicEquiv.finrank_eq]
  simp

/-- Homogeneous polynomials of any fixed degree form a finite-dimensional
space because there are only finitely many monomials of that degree. -/
theorem finiteDimensional_homogeneousPolynomial (ℓ : ℕ) :
    FiniteDimensional ℝ (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ ℓ) := by
  classical
  let s : Set ((Fin 3) →₀ ℕ) := {d | d.degree = ℓ}
  have hs : s.Finite :=
    (Finsupp.finite_of_degree_le ℓ).subset (by
      intro d hd
      exact le_of_eq hd)
  letI : Finite s := hs.to_subtype
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Finite.equiv (Finsupp.supportedEquivFinsupp (R := ℝ) s).symm

/-- The harmonic kernel is finite-dimensional in every degree. -/
theorem finiteDimensional_harmonicPolynomial (ℓ : ℕ) :
    FiniteDimensional ℝ (harmonicPolynomialSubmodule ℓ) := by
  letI := finiteDimensional_homogeneousPolynomial ℓ
  have hle : harmonicPolynomialSubmodule ℓ ≤
      MvPolynomial.homogeneousSubmodule (Fin 3) ℝ ℓ := inf_le_left
  exact Module.Finite.of_injective
    (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

/-- Exponent vectors of monomials of total degree `ℓ`. -/
def degreeMonomials (ℓ : ℕ) : Set ((Fin 3) →₀ ℕ) :=
  {d | d.degree = ℓ}

theorem degreeMonomials_finite (ℓ : ℕ) : (degreeMonomials ℓ).Finite := by
  exact (Finsupp.finite_of_degree_le ℓ).subset (by
    intro d hd
    exact le_of_eq hd)

noncomputable instance degreeMonomials_fintype (ℓ : ℕ) :
    Fintype (degreeMonomials ℓ) := (degreeMonomials_finite ℓ).fintype

/-- The homogeneous-polynomial dimension reduces exactly to counting monomials. -/
theorem finrank_homogeneous_eq_degreeMonomials_card (ℓ : ℕ) :
    Module.finrank ℝ (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ ℓ) =
      Fintype.card (degreeMonomials ℓ) := by
  classical
  letI : Finite (degreeMonomials ℓ) := (degreeMonomials_finite ℓ).to_subtype
  letI := finiteDimensional_homogeneousPolynomial ℓ
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank ℝ (Finsupp.supported ℝ ℝ (degreeMonomials ℓ)) = _
  rw [(Finsupp.supportedEquivFinsupp (R := ℝ) (degreeMonomials ℓ)).finrank_eq]
  simp

/-- Polynomial evaluation on the sphere, packaged as an algebra homomorphism. -/
noncomputable def polynomialRestrictionAlgHom :
    MvPolynomial (Fin 3) ℝ →ₐ[ℝ] C(Sphere, ℝ) where
  toFun := restrictPolynomial
  map_zero' := by
    ext x
    simp [restrictPolynomial]
  map_one' := by
    ext x
    simp [restrictPolynomial]
  map_add' p q := by
    ext x
    simp [restrictPolynomial]
  map_mul' p q := by
    ext x
    simp [restrictPolynomial]
  commutes' c := by
    ext x
    simp [restrictPolynomial]

/-- Coordinate polynomial restrictions form a separating subalgebra. -/
noncomputable def polynomialRestrictionSubalgebra : Subalgebra ℝ C(Sphere, ℝ) :=
  polynomialRestrictionAlgHom.range

theorem polynomialRestriction_separatesPoints :
    polynomialRestrictionSubalgebra.SeparatesPoints := by
  intro x y hxy
  have hcoord : ∃ i : Fin 3, (x : Ambient) i ≠ (y : Ambient) i := by
    by_contra h
    push_neg at h
    apply hxy
    apply Subtype.ext
    exact funext h
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨restrictPolynomial (MvPolynomial.X i), ?_, ?_⟩
  · refine ⟨restrictPolynomial (MvPolynomial.X i), ?_, rfl⟩
    exact ⟨MvPolynomial.X i, rfl⟩
  · simpa [restrictPolynomial] using hi

/-- Polynomial restrictions are uniformly dense in all continuous real
functions on the sphere. -/
theorem polynomialRestriction_dense :
    polynomialRestrictionSubalgebra.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    polynomialRestrictionSubalgebra polynomialRestriction_separatesPoints

/-! ### The Fischer decomposition calculation -/

/-- The polynomial `x₀²+x₁²+x₂²`, equal to one on the unit sphere. -/
noncomputable def radialSquare : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 + MvPolynomial.X 2 ^ 2

theorem radialSquare_isHomogeneous : radialSquare.IsHomogeneous 2 := by
  unfold radialSquare
  exact ((MvPolynomial.isHomogeneous_X_pow (R := ℝ) (0 : Fin 3) 2).add
    (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (1 : Fin 3) 2)).add
      (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (2 : Fin 3) 2)

/-- The first derivative of the radial square is twice the corresponding coordinate. -/
theorem radialSquare_pderiv (i : Fin 3) :
    (MvPolynomial.pderiv i) radialSquare = 2 * MvPolynomial.X i := by
  classical
  fin_cases i <;>
    simp [radialSquare, map_add, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_X, Pi.single_apply]

/-- The coordinatewise product-rule calculation behind Fischer decomposition. -/
theorem radialSquare_mul_pderiv2 (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    (MvPolynomial.pderiv i) ((MvPolynomial.pderiv i) (radialSquare * p)) =
      2 * p + 4 * MvPolynomial.X i * (MvPolynomial.pderiv i) p +
        radialSquare * (MvPolynomial.pderiv i) ((MvPolynomial.pderiv i) p) := by
  classical
  have htwo : (MvPolynomial.pderiv i) (2 : MvPolynomial (Fin 3) ℝ) = 0 := by
    change (MvPolynomial.pderiv i) (MvPolynomial.C (2 : ℝ)) = 0
    simp
  simp only [MvPolynomial.pderiv_mul, map_add, radialSquare_pderiv]
  simp only [htwo, MvPolynomial.pderiv_X, Pi.single_apply,
    ite_true, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  ring

/-- Laplacian of a radial-square multiple before using homogeneity. -/
theorem polynomialLaplacian_radialSquare_mul (p : MvPolynomial (Fin 3) ℝ) :
    polynomialLaplacian (radialSquare * p) =
      6 * p + 4 * (∑ i : Fin 3, MvPolynomial.X i * (MvPolynomial.pderiv i) p) +
        radialSquare * polynomialLaplacian p := by
  simp only [polynomialLaplacian, Fin.sum_univ_three,
    radialSquare_mul_pderiv2]
  ring

/-- Fischer's basic identity on homogeneous degree `m` polynomials. -/
theorem polynomialLaplacian_radialSquare_mul_homogeneous
    {m : ℕ} {p : MvPolynomial (Fin 3) ℝ} (hp : p.IsHomogeneous m) :
    polynomialLaplacian (radialSquare * p) =
      (4 * (m : ℝ) + 6) • p + radialSquare * polynomialLaplacian p := by
  rw [polynomialLaplacian_radialSquare_mul, hp.sum_X_mul_pderiv]
  simp only [nsmul_eq_mul, MvPolynomial.smul_eq_C_mul,
    map_add, map_mul, map_natCast]
  have h4 : (MvPolynomial.C (4 : ℝ) : MvPolynomial (Fin 3) ℝ) = 4 := by
    simpa using (MvPolynomial.C_eq_coe_nat (σ := Fin 3) (R := ℝ) 4)
  have h6 : (MvPolynomial.C (6 : ℝ) : MvPolynomial (Fin 3) ℝ) = 6 := by
    simpa using (MvPolynomial.C_eq_coe_nat (σ := Fin 3) (R := ℝ) 6)
  rw [h4, h6]
  ring

/-- On the unit sphere the radial square is exactly one. -/
theorem radialSquare_eval_sphere (x : Sphere) :
    MvPolynomial.eval (fun i => (x : Ambient) i) radialSquare = 1 := by
  have hx : ∑ i : Fin 3, ((x : Ambient) i) ^ 2 = 1 := by
    simpa [EuclideanSpace.sphere_zero_eq 1 (by positivity)] using x.property
  simp [radialSquare, Fin.sum_univ_three] at hx ⊢
  exact hx

/-- Multiplication by the radial square does not change a polynomial's
restriction to the unit sphere. -/
theorem restrictPolynomial_radialSquare_mul
    (p : MvPolynomial (Fin 3) ℝ) :
    restrictPolynomial (radialSquare * p) = restrictPolynomial p := by
  ext x
  simp [restrictPolynomial_apply, radialSquare_eval_sphere]

/-- Homogeneity gives the exact scaling law under evaluation. -/
theorem homogeneous_eval_scale {m : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p.IsHomogeneous m) (c : ℝ) (x : Fin 3 → ℝ) :
    MvPolynomial.eval (fun i => c * x i) p =
      c ^ m * MvPolynomial.eval x p := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d.degree = m := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum]
  have hsum : (∑ i : Fin 3, d i) = d.degree := by
    simpa [Finsupp.degree] using
      (Finsupp.sum_fintype (f := d) (g := fun _ n => n) (by simp)).symm
  rw [hsum, hdeg]
  ring

/-- A homogeneous polynomial is determined by its values on the unit sphere. -/
theorem homogeneous_restrict_injective {m : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p.IsHomogeneous m)
    (hzero : restrictPolynomial p = 0) : p = 0 := by
  apply hp.eq_zero_of_forall_eval_eq_zero
  intro a
  let v : Ambient := (EuclideanSpace.equiv (Fin 3) ℝ).symm a
  by_cases hv : v = 0
  · have ha : a = 0 := by
      simpa [v] using congrArg (EuclideanSpace.equiv (Fin 3) ℝ) hv
    subst a
    by_cases hm : m = 0
    · subst m
      have hconst := homogeneous_zero_eq_constant hp
      rw [hconst] at hzero ⊢
      have hx := congrFun (congrArg DFunLike.coe hzero)
        (⟨!₂[0, 0, 1], by
          simp [EuclideanSpace.sphere_zero_eq 1 (by positivity), Fin.sum_univ_three]⟩ : Sphere)
      simpa [restrictPolynomial] using hx
    · have hcoeff := hp.coeff_eq_zero (d := 0) (by simpa using Ne.symm hm)
      simpa [MvPolynomial.eval_zero] using hcoeff
  · have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let y : Sphere := ⟨(‖v‖)⁻¹ • v, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hnorm, inv_mul_cancel₀ (ne_of_gt hnorm)]⟩
    have hv_eq : v = ‖v‖ • (y : Ambient) := by
      simp [y, smul_smul, ne_of_gt hnorm]
    have heval := congrFun (congrArg DFunLike.coe hzero) y
    have hcoord : ∀ i, a i = ‖v‖ * (y : Ambient) i := by
      intro i
      have := congrArg (fun w : Ambient => w i) hv_eq
      simpa [v] using this
    rw [show a = fun i => ‖v‖ * (y : Ambient) i from funext hcoord,
      homogeneous_eval_scale hp]
    simp [restrictPolynomial_apply] at heval
    simp [heval]

/-- Restriction as a linear map on the finite-dimensional harmonic space. -/
noncomputable def restrictHarmonicLinearMap (m : ℕ) :
    harmonicPolynomialSubmodule m →ₗ[ℝ] C(Sphere, ℝ) :=
  restrictPolynomialLinearMap.comp (harmonicPolynomialSubmodule m).subtype

/-- The sphere restriction preserves the dimension of each harmonic space. -/
theorem restrictHarmonicLinearMap_injective (m : ℕ) :
    Function.Injective (restrictHarmonicLinearMap m) := by
  intro p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply homogeneous_restrict_injective
    ((mem_harmonicPolynomialSubmodule.mp p.property).1.sub
      (mem_harmonicPolynomialSubmodule.mp q.property).1)
  change restrictPolynomialLinearMap (p.val - q.val) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hpq

/-- Powers of the radial square remain homogeneous. -/
theorem radialPower_isHomogeneous (k : ℕ) :
    (radialSquare ^ k).IsHomogeneous (2 * k) := by
  simpa using radialSquare_isHomogeneous.pow k

theorem radialPower_mul_isHomogeneous {m : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p.IsHomogeneous m) (k : ℕ) :
    (radialSquare ^ k * p).IsHomogeneous (2 * k + m) :=
  (radialPower_isHomogeneous k).mul hp

/-- Iterated radial multiplication has a triangular Laplacian formula.
This is the coefficient recurrence used for the finite Fischer inverse. -/
theorem radialPower_laplacian {m : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p.IsHomogeneous m) (k : ℕ) :
    polynomialLaplacian (radialSquare ^ (k + 1) * p) =
      (2 * ((k + 1 : ℕ) : ℝ) * (2 * (m : ℝ) + 2 * (k : ℝ) + 3)) •
        (radialSquare ^ k * p) +
      radialSquare ^ (k + 1) * polynomialLaplacian p := by
  induction k with
  | zero =>
      simpa only [pow_one, pow_zero, one_mul, Nat.cast_one, zero_add,
        Nat.cast_zero, mul_one, mul_zero, add_zero,
        show (2 * (2 * (m : ℝ) + 3)) = 4 * (m : ℝ) + 6 by ring] using
        polynomialLaplacian_radialSquare_mul_homogeneous hp
  | succ k ih =>
      have hhom := radialPower_mul_isHomogeneous hp (k + 1)
      calc
        polynomialLaplacian (radialSquare ^ (k + 1 + 1) * p) =
            polynomialLaplacian (radialSquare * (radialSquare ^ (k + 1) * p)) := by
              congr 1 <;> ring
        _ = (4 * ((2 * (k + 1) + m : ℕ) : ℝ) + 6) •
              (radialSquare ^ (k + 1) * p) +
              radialSquare * polynomialLaplacian (radialSquare ^ (k + 1) * p) :=
                polynomialLaplacian_radialSquare_mul_homogeneous hhom
        _ = (2 * (((k + 1 + 1 : ℕ) : ℝ)) *
              (2 * (m : ℝ) + 2 * ((k + 1 : ℕ) : ℝ) + 3)) •
              (radialSquare ^ (k + 1) * p) +
              radialSquare ^ (k + 1 + 1) * polynomialLaplacian p := by
                rw [ih]
                have hc :
                    (4 * ((2 * (k + 1) + m : ℕ) : ℝ) + 6) +
                      2 * (((k + 1 : ℕ) : ℝ)) *
                        (2 * (m : ℝ) + 2 * (k : ℝ) + 3) =
                    2 * (((k + 1 + 1 : ℕ) : ℝ)) *
                      (2 * (m : ℝ) + 2 * ((k + 1 : ℕ) : ℝ) + 3) := by
                  push_cast
                  ring
                conv_lhs => rhs; rw [mul_add, mul_smul_comm]
                have hpow1 : radialSquare * (radialSquare ^ k * p) =
                    radialSquare ^ (k + 1) * p := by ring
                have hpow2 : radialSquare *
                    (radialSquare ^ (k + 1) * polynomialLaplacian p) =
                    radialSquare ^ (k + 1 + 1) * polynomialLaplacian p := by ring
                rw [hpow1, hpow2]
                rw [← hc]
                module

/-- On a harmonic input, each radial power is a Laplacian eigenstep. -/
theorem radialPower_laplacian_harmonic {m : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p ∈ harmonicPolynomialSubmodule m)
    (k : ℕ) :
    polynomialLaplacian (radialSquare ^ (k + 1) * p) =
      (2 * ((k + 1 : ℕ) : ℝ) * (2 * (m : ℝ) + 2 * (k : ℝ) + 3)) •
        (radialSquare ^ k * p) := by
  obtain ⟨hhom, hlap⟩ := mem_harmonicPolynomialSubmodule.mp hp
  simpa [hlap] using radialPower_laplacian hhom k

/-- A homogeneous harmonic polynomial has a homogeneous polynomial Laplacian
preimage in the next even degree. -/
theorem harmonic_laplacian_preimage {m : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p ∈ harmonicPolynomialSubmodule m) :
    ∃ q : MvPolynomial (Fin 3) ℝ,
      q.IsHomogeneous (m + 2) ∧ polynomialLaplacian q = p := by
  let c : ℝ := 4 * (m : ℝ) + 6
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  refine ⟨c⁻¹ • (radialSquare * p), ?_, ?_⟩
  · simpa only [MvPolynomial.smul_eq_C_mul,
      show (2 : ℕ) + m = m + 2 by omega] using
      (radialSquare_isHomogeneous.mul
        (mem_harmonicPolynomialSubmodule.mp hp).1).C_mul c⁻¹
  · rw [polynomialLaplacian_smul]
    have hbase := radialPower_laplacian_harmonic hp 0
    have hb : polynomialLaplacian (radialSquare * p) = c • p := by
      convert hbase using 1 <;> norm_num [c] <;> ring
    rw [hb, smul_smul]
    simp [hc]

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
