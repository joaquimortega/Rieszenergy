import BEMOCFormalization.HarmonicBasis

namespace BEMOC.Definitive

def radialHarmonicGenerators (m : ℕ) : Set (MvPolynomial (Fin 3) ℝ) :=
  {p | ∃ (k n : ℕ) (h : MvPolynomial (Fin 3) ℝ),
    2 * k + n = m ∧ h ∈ harmonicPolynomialSubmodule n ∧
      p = radialSquare ^ k * h}

noncomputable def radialHarmonicSpan (m : ℕ) :
    Submodule ℝ (MvPolynomial (Fin 3) ℝ) :=
  Submodule.span ℝ (radialHarmonicGenerators m)

theorem radialHarmonicSpan_le_homogeneous (m : ℕ) :
    radialHarmonicSpan m ≤ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ m := by
  apply Submodule.span_le.mpr
  rintro p ⟨k, n, h, rfl, hh, rfl⟩
  exact radialPower_mul_isHomogeneous
    (mem_harmonicPolynomialSubmodule.mp hh).1 k

theorem harmonic_mem_radialHarmonicSpan {m : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p ∈ harmonicPolynomialSubmodule m) :
    p ∈ radialHarmonicSpan m := by
  apply Submodule.subset_span
  exact ⟨0, m, p, by simp, hp, by simp⟩

theorem radialGenerator_laplacian_preimage {m : ℕ}
    {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ radialHarmonicGenerators m) :
    ∃ q : MvPolynomial (Fin 3) ℝ,
      q ∈ radialHarmonicSpan (m + 2) ∧ polynomialLaplacian q = p := by
  obtain ⟨k, n, h, hdeg, hh, rfl⟩ := hp
  let a : ℝ := 2 * ((k + 1 : ℕ) : ℝ) *
    (2 * (n : ℝ) + 2 * (k : ℝ) + 3)
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  refine ⟨a⁻¹ • (radialSquare ^ (k + 1) * h), ?_, ?_⟩
  · apply (radialHarmonicSpan (m + 2)).smul_mem
    apply Submodule.subset_span
    exact ⟨k + 1, n, h, by omega, hh, rfl⟩
  · rw [polynomialLaplacian_smul,
      show polynomialLaplacian (radialSquare ^ (k + 1) * h) =
        a • (radialSquare ^ k * h) from radialPower_laplacian_harmonic hh k,
      smul_smul]
    simp [ha]

noncomputable def radialSpanLaplacianMap (m : ℕ) :
    radialHarmonicSpan (m + 2) →ₗ[ℝ] MvPolynomial (Fin 3) ℝ :=
  polynomialLaplacianLinearMap.comp (radialHarmonicSpan (m + 2)).subtype

theorem radialHarmonicSpan_laplacian_preimage {m : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p ∈ radialHarmonicSpan m) :
    ∃ q : MvPolynomial (Fin 3) ℝ,
      q ∈ radialHarmonicSpan (m + 2) ∧ polynomialLaplacian q = p := by
  have hs : radialHarmonicSpan m ≤ LinearMap.range (radialSpanLaplacianMap m) := by
    apply Submodule.span_le.mpr
    intro t ht
    obtain ⟨q, hq, hΔ⟩ := radialGenerator_laplacian_preimage ht
    exact ⟨⟨q, hq⟩, hΔ⟩
  obtain ⟨q, hq⟩ := hs hp
  exact ⟨q.val, q.property, hq⟩

/-- Every homogeneous polynomial has a finite Fischer expansion into
radial powers of genuine harmonic polynomials. -/
theorem homogeneous_mem_radialHarmonicSpan :
    ∀ (m : ℕ) (p : MvPolynomial (Fin 3) ℝ),
      p.IsHomogeneous m → p ∈ radialHarmonicSpan m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro p hp
    by_cases hm : m < 2
    · have hlap : polynomialLaplacian p = 0 := by
        interval_cases m
        · exact homogeneous_zero_laplacian_zero hp
        · exact homogeneous_one_laplacian_zero hp
      exact harmonic_mem_radialHarmonicSpan
        (mem_harmonicPolynomialSubmodule.mpr ⟨hp, hlap⟩)
    · have hpos : 2 ≤ m := by omega
      have hΔhom : (polynomialLaplacian p).IsHomogeneous (m - 2) :=
        polynomialLaplacian_isHomogeneous hp
      have hΔspan := ih (m - 2) (by omega) (polynomialLaplacian p) hΔhom
      obtain ⟨q, hq', hΔq⟩ := radialHarmonicSpan_laplacian_preimage hΔspan
      have hq : q ∈ radialHarmonicSpan m := by
        simpa [Nat.sub_add_cancel hpos] using hq'
      have hqhom : q.IsHomogeneous m := radialHarmonicSpan_le_homogeneous m hq
      have hrem : p - q ∈ harmonicPolynomialSubmodule m := by
        apply mem_harmonicPolynomialSubmodule.mpr
        constructor
        · exact hp.sub hqhom
        · rw [← polynomialLaplacianLinearMap_apply,
            map_sub, polynomialLaplacianLinearMap_apply,
            polynomialLaplacianLinearMap_apply, hΔq]
          exact sub_self _
      rw [show p = (p - q) + q by abel]
      exact (radialHarmonicSpan m).add_mem
        (harmonic_mem_radialHarmonicSpan hrem) hq

/-- The linear span in continuous functions of all actual spherical harmonics. -/
noncomputable def harmonicRestrictionSpan : Submodule ℝ C(Sphere, ℝ) :=
  Submodule.span ℝ {Y | ∃ m : ℕ, IsSphericalHarmonic m Y}

theorem restrictPolynomial_radialPower_mul
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) :
    restrictPolynomial (radialSquare ^ k * p) = restrictPolynomial p := by
  ext x
  simp [restrictPolynomial_apply, radialSquare_eval_sphere]

theorem harmonic_restriction_mem_span {m : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p ∈ harmonicPolynomialSubmodule m) :
    restrictPolynomial p ∈ harmonicRestrictionSpan := by
  apply Submodule.subset_span
  exact ⟨m, restrictPolynomial_isSphericalHarmonic hp⟩

theorem radialHarmonicSpan_restrict_mem {m : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p ∈ radialHarmonicSpan m) :
    restrictPolynomial p ∈ harmonicRestrictionSpan := by
  have hs : radialHarmonicSpan m ≤
      harmonicRestrictionSpan.comap restrictPolynomialLinearMap := by
    apply Submodule.span_le.mpr
    rintro p ⟨k, n, h, hdeg, hh, rfl⟩
    change restrictPolynomial (radialSquare ^ k * h) ∈ harmonicRestrictionSpan
    rw [restrictPolynomial_radialPower_mul]
    exact harmonic_restriction_mem_span hh
  exact hs hp

/-- Every polynomial restriction is a finite linear combination of genuine
spherical harmonics. -/
theorem restrictPolynomial_mem_harmonicRestrictionSpan
    (p : MvPolynomial (Fin 3) ℝ) :
    restrictPolynomial p ∈ harmonicRestrictionSpan := by
  classical
  rw [← MvPolynomial.sum_homogeneousComponent (φ := p)]
  change restrictPolynomialLinearMap
      (∑ i ∈ Finset.range (p.totalDegree + 1),
        MvPolynomial.homogeneousComponent i p) ∈ harmonicRestrictionSpan
  rw [map_sum]
  apply harmonicRestrictionSpan.sum_mem
  intro i hi
  exact radialHarmonicSpan_restrict_mem
    (homogeneous_mem_radialHarmonicSpan i _
      (MvPolynomial.homogeneousComponent_isHomogeneous i p))

/-- Genuine spherical harmonic polynomials are uniformly dense in continuous
functions on the sphere. -/
theorem harmonicRestrictionSpan_dense :
    Dense (harmonicRestrictionSpan : Set C(Sphere, ℝ)) := by
  apply (dense_iff_closure_eq).2
  have hsub : (polynomialRestrictionSubalgebra : Set C(Sphere, ℝ)) ⊆
      harmonicRestrictionSpan := by
    intro f hf
    obtain ⟨p, rfl⟩ := hf
    exact restrictPolynomial_mem_harmonicRestrictionSpan p
  have hc := closure_mono hsub
  rw [← Subalgebra.topologicalClosure_coe, polynomialRestriction_dense] at hc
  apply Set.eq_univ_iff_forall.mpr
  intro f
  exact hc (Set.mem_univ f)

end BEMOC.Definitive
