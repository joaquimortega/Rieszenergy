# HarmonicFiniteSpan proof guide

This module supplies the finite, degree-controlled version of the harmonic density statement needed in spectral estimates. General density says every continuous function can be approximated by harmonic restrictions, but a moment test that is itself a polynomial of degree at most `m` admits an *exact finite* expansion using harmonics of degrees at most `m`. The latter is essential when the Sobolev estimate needs to truncate the spectral sum at a known degree and compare individual coefficients. This module proves the finite statement for the original `IsSphericalHarmonic` predicate and then for the functions of an arbitrary `Y : HarmonicBasis`.

`harmonicRestrictionSpanUpTo m` is the linear span in `C(Sphere,ℝ)` of all genuine spherical harmonics with degree `n≤m`. `harmonic_restriction_mem_spanUpTo` inserts the restriction of a member of `harmonicPolynomialSubmodule n` into that span by the exact equivalence `isSphericalHarmonic_iff_range`. The substantial algebraic step is `homogeneous_restriction_mem_spanUpTo`. It applies the checked Fischer decomposition theorem `homogeneous_mem_radialHarmonicSpan n p hp`, which expresses a homogeneous degree-`n` polynomial as a linear combination of terms `(radialSquare)^k h` where `h` is harmonic of degree `d` and `n=2k+d`. On the unit sphere `radialSquare=1`, so `restrictPolynomial_radialPower_mul` changes each generator restriction to `restrictPolynomial h`. The arithmetic relation gives `d≤n≤m`; no term can introduce a harmonic degree above the original polynomial degree. The proof is formulated as an inclusion of `radialHarmonicSpan n` into the preimage of `harmonicRestrictionSpanUpTo m` under `restrictPolynomialLinearMap`, making closure under finite linear combinations automatic.

`polynomial_restriction_mem_spanUpTo` removes the homogeneity assumption. Mathlib's `MvPolynomial.sum_homogeneousComponent` decomposes any polynomial into components indexed by `Finset.range (p.totalDegree+1)`. Every component is homogeneous by `homogeneousComponent_isHomogeneous`; if `p.totalDegree≤m`, every index in the range is at most `m`. Mapping the finite sum through `restrictPolynomialLinearMap` and applying the homogeneous result gives an exact membership in the bounded-degree harmonic span. This theorem makes no measure-theoretic assumption and is available before any basis is chosen.

The second half relates these intrinsic harmonic spaces to the particular spectral coordinates of `Y : HarmonicBasis`. `HarmonicAddition.lean` already proves that the functions `Y.function n k` arise from polynomials `harmonicBasisPolynomial Y n k`, and that those polynomials form `harmonicBasisDegree Y n`, an orthonormal basis of the full degree-`n` harmonic polynomial space. We reuse that checked basis rather than constructing another lift. `harmonic_restriction_mem_basisDegreeSpan` applies the ordinary basis spanning theorem, maps the span through `restrictHarmonicLinearMap`, and identifies each image with `Y.function n k`. Consequently every degree-`n` harmonic restriction belongs to the span of the `2n+1` functions of that same degree.

`harmonicBasisSpanUpTo Y m` is the span of `Y.function n k` for `n≤m`. `harmonicRestrictionSpanUpTo_le_basisSpan` combines the degree-wise basis theorem with monotonicity of spans. The final theorem `polynomial_restriction_mem_basisSpanUpTo` applies that inclusion to the degree-controlled Fischer result. It works for an arbitrary basis satisfying the exact `HarmonicBasis` contract and does not depend on choosing the canonical basis constructed by `harmonicBasis_nonempty`.

For the even-moment lower-bound branch, the centered moment test is already represented by `centeredEvenMomentPolynomial` and has proved total degree at most `2r`. Applying `polynomial_restriction_mem_basisSpanUpTo Y` with `m=2r` gives the finite harmonic expansion needed to turn its quadrature gap into a finite sum of harmonic coefficient errors. Membership in a span is not itself an explicit coefficient formula; `SobolevMomentSpectral` subsequently computes the coefficients using the degree basis and orthonormality, then proves the moment spectral domination inequality.

`lake build BEMOCFormalization.HarmonicFiniteSpan` checks the module and its imports in the integrated dependency graph. No project proof shortcuts are used.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.HarmonicBasisExistence
import BEMOCFormalization.HarmonicAddition

namespace BEMOC.Definitive

/-- Finite harmonic restrictions of degree at most `m`. -/
noncomputable def harmonicRestrictionSpanUpTo (m : ℕ) :
    Submodule ℝ C(Sphere, ℝ) :=
  Submodule.span ℝ {f | ∃ n ≤ m, IsSphericalHarmonic n f}

theorem harmonic_restriction_mem_spanUpTo {m n : ℕ}
    {p : Poly3} (hp : p ∈ harmonicPolynomialSubmodule n) (hn : n ≤ m) :
    restrictPolynomial p ∈ harmonicRestrictionSpanUpTo m := by
  apply Submodule.subset_span
  exact ⟨n, hn, restrictPolynomial_isSphericalHarmonic hp⟩

theorem homogeneous_restriction_mem_spanUpTo {m n : ℕ}
    {p : Poly3} (hp : p.IsHomogeneous n) (hn : n ≤ m) :
    restrictPolynomial p ∈ harmonicRestrictionSpanUpTo m := by
  have hspan : radialHarmonicSpan n ≤
      (harmonicRestrictionSpanUpTo m).comap restrictPolynomialLinearMap := by
    apply Submodule.span_le.mpr
    rintro q ⟨k, d, h, hdeg, hh, rfl⟩
    change restrictPolynomial (radialSquare ^ k * h) ∈ harmonicRestrictionSpanUpTo m
    rw [restrictPolynomial_radialPower_mul]
    apply harmonic_restriction_mem_spanUpTo hh
    omega
  exact hspan (homogeneous_mem_radialHarmonicSpan n p hp)

theorem polynomial_restriction_mem_spanUpTo {m : ℕ}
    {p : Poly3} (hp : p.totalDegree ≤ m) :
    restrictPolynomial p ∈ harmonicRestrictionSpanUpTo m := by
  classical
  rw [← MvPolynomial.sum_homogeneousComponent (φ := p)]
  change restrictPolynomialLinearMap
      (∑ i ∈ Finset.range (p.totalDegree + 1),
        MvPolynomial.homogeneousComponent i p) ∈ harmonicRestrictionSpanUpTo m
  rw [map_sum]
  apply (harmonicRestrictionSpanUpTo m).sum_mem
  intro i hi
  apply homogeneous_restriction_mem_spanUpTo
    (MvPolynomial.homogeneousComponent_isHomogeneous i p)
  exact (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hp

/-- Harmonic restrictions of a fixed degree lie in the span of the degree
members of any complete orthonormal `HarmonicBasis`. -/
theorem harmonic_restriction_mem_basisDegreeSpan (Y : HarmonicBasis)
    (n : ℕ) (p : harmonicPolynomialSubmodule n) :
    restrictPolynomial p.val ∈
      Submodule.span ℝ (Set.range (Y.function n)) := by
  let b := (harmonicBasisDegree Y n).toBasis
  have hspan : (Submodule.span ℝ (Set.range (fun k => b k))) = ⊤ := b.span_eq
  have hp : p ∈ Submodule.span ℝ (Set.range (fun k => b k)) := by
    rw [hspan]
    trivial
  have hmap :
      Submodule.span ℝ (Set.range (fun k => b k)) ≤
        (Submodule.span ℝ (Set.range (Y.function n))).comap
          (restrictHarmonicLinearMap n) := by
    apply Submodule.span_le.mpr
    rintro q ⟨k, rfl⟩
    change restrictPolynomial (b k).val ∈
      Submodule.span ℝ (Set.range (Y.function n))
    have hb : b k = harmonicBasisPolynomial Y n k :=
      harmonicBasisDegree_apply Y n k
    rw [hb, harmonicBasisPolynomial_restrict]
    exact Submodule.subset_span ⟨k, rfl⟩
  exact hmap hp

/-- All members of a specified harmonic basis through degree `m`. -/
noncomputable def harmonicBasisSpanUpTo (Y : HarmonicBasis) (m : ℕ) :
    Submodule ℝ C(Sphere, ℝ) :=
  Submodule.span ℝ {f | ∃ n ≤ m, ∃ k : Fin (2 * n + 1), f = Y.function n k}

theorem harmonicRestrictionSpanUpTo_le_basisSpan (Y : HarmonicBasis) (m : ℕ) :
    harmonicRestrictionSpanUpTo m ≤ harmonicBasisSpanUpTo Y m := by
  apply Submodule.span_le.mpr
  intro f hf
  obtain ⟨n, hn, hharm⟩ := hf
  obtain ⟨p, rfl⟩ := (isSphericalHarmonic_iff_range n f).mp hharm
  have hdegree := harmonic_restriction_mem_basisDegreeSpan Y n p
  have hinc : Set.range (Y.function n) ⊆
      {g | ∃ d ≤ m, ∃ k : Fin (2 * d + 1), g = Y.function d k} := by
    rintro g ⟨k, rfl⟩
    exact ⟨n, hn, k, rfl⟩
  exact (Submodule.span_mono hinc) hdegree

/-- A polynomial of total degree at most `m` has a finite expansion in the
members of any specified harmonic basis of degrees at most `m`. -/
theorem polynomial_restriction_mem_basisSpanUpTo
    (Y : HarmonicBasis) {m : ℕ} {p : Poly3} (hp : p.totalDegree ≤ m) :
    restrictPolynomial p ∈ harmonicBasisSpanUpTo Y m :=
  (harmonicRestrictionSpanUpTo_le_basisSpan Y m)
    (polynomial_restriction_mem_spanUpTo hp)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
