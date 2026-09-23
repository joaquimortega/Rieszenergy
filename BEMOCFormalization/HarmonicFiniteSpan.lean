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
