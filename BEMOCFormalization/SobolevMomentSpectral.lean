import BEMOCFormalization.SobolevMomentAction
import BEMOCFormalization.HarmonicFiniteSpan
import BEMOCFormalization.SobolevKernel
import BEMOCFormalization.SobolevEmbeddingDirect

/-! Exact finite spectral reconstruction of the centered projection-moment
test. The polynomial degree bound makes all relevant harmonic sums finite. -/

open scoped BigOperators
open MeasureTheory

namespace BEMOC.Definitive

/-- Finite harmonic projection as a real linear map. -/
noncomputable def harmonicPartialSumLinearMap (Y : HarmonicBasis) (L : ℕ) :
    C(Sphere, ℝ) →ₗ[ℝ] C(Sphere, ℝ) where
  toFun f := harmonicPartialSum Y f L
  map_add' f g := by
    unfold harmonicPartialSum harmonicDegreeProjection
    simp only [harmonicCoefficient_add, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    unfold harmonicPartialSum harmonicDegreeProjection
    simp only [harmonicCoefficient_smul, smul_smul, RingHom.id_apply,
      Finset.smul_sum]

theorem harmonicPartialSumLinearMap_apply (Y : HarmonicBasis) (L : ℕ)
    (f : C(Sphere, ℝ)) :
    harmonicPartialSumLinearMap Y L f = harmonicPartialSum Y f L := rfl

theorem harmonicDegreeProjection_basis (Y : HarmonicBasis)
    (n ℓ : ℕ) (k : Fin (2 * n + 1)) :
    harmonicDegreeProjection Y (Y.function n k) ℓ =
      if ℓ = n then Y.function n k else 0 := by
  classical
  by_cases h : ℓ = n
  · subst ℓ
    simp [harmonicDegreeProjection, harmonicCoefficient_basis,
      Finset.sum_ite_eq', Fin.val_inj]
  · simp [harmonicDegreeProjection, harmonicCoefficient_basis, h, Ne.symm h]

theorem harmonicPartialSum_basis (Y : HarmonicBasis)
    (m n : ℕ) (hn : n ≤ m) (k : Fin (2 * n + 1)) :
    harmonicPartialSum Y (Y.function n k) (m + 1) = Y.function n k := by
  classical
  have hn' : n < m + 1 := by omega
  simp [harmonicPartialSum, harmonicDegreeProjection_basis, hn',
    Finset.sum_ite_eq']

/-- Finite harmonic reconstruction on the basis span. -/
theorem harmonicPartialSum_eq_of_mem_basisSpanUpTo (Y : HarmonicBasis)
    (m : ℕ) (f : C(Sphere, ℝ))
    (hf : f ∈ harmonicBasisSpanUpTo Y m) :
    harmonicPartialSum Y f (m + 1) = f := by
  let P := harmonicPartialSumLinearMap Y (m + 1)
  have hle : harmonicBasisSpanUpTo Y m ≤ LinearMap.ker (P - LinearMap.id) := by
    apply Submodule.span_le.mpr
    intro g hg
    obtain ⟨n, hn, k, rfl⟩ := hg
    change harmonicPartialSum Y (Y.function n k) (m + 1) - Y.function n k = 0
    rw [harmonicPartialSum_basis Y m n hn k, sub_self]
  have hmem := hle hf
  rw [LinearMap.mem_ker] at hmem
  simpa only [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
    harmonicPartialSumLinearMap_apply] using hmem

/-- The centered even-moment test has an exact finite harmonic expansion. -/
theorem centeredEvenMomentTest_partialSum (Y : HarmonicBasis)
    {N : ℕ} (X : Fin N → Sphere) (r : ℕ) :
    harmonicPartialSum Y (centeredEvenMomentTest X r) (2 * r + 1) =
      centeredEvenMomentTest X r := by
  apply harmonicPartialSum_eq_of_mem_basisSpanUpTo Y (2 * r)
  rw [← centeredEvenMomentPolynomial_restrict]
  exact polynomial_restriction_mem_basisSpanUpTo Y
    (centeredEvenMomentPolynomial_totalDegree_le X r)

theorem centeredEvenMomentTest_coefficient_even (Y : HarmonicBasis)
    {N : ℕ} (X : Fin N → Sphere) (r k : ℕ)
    (hpos : 0 < k) (j : Fin (2 * (2 * k) + 1)) :
    harmonicCoefficient Y (centeredEvenMomentTest X r) (2 * k) j =
      evenMomentModelCoefficient r k *
        harmonicQuadratureCoefficient Y X (2 * k) j := by
  let H := (harmonicBasisPolynomial Y (2 * k) j).val
  have hH : H ∈ harmonicPolynomialSubmodule (2 * k) :=
    (harmonicBasisPolynomial Y (2 * k) j).property
  have hrepr (x : Sphere) :
      MvPolynomial.eval (fun i => (x : Ambient) i) H = Y.function (2 * k) j x := by
    exact congrFun (congrArg DFunLike.coe
      (harmonicBasisPolynomial_restrict Y (2 * k) j)) x
  have hnode (i : Fin N) :=
    even_projection_harmonic_action hH (X i) r
  simp_rw [hrepr] at hnode
  have hnode' (i : Fin N) :
      (∫ x : Sphere,
        (@Inner.inner ℝ Ambient _ (X i : Ambient) (x : Ambient)) ^ (2 * r) *
          Y.function (2 * k) j x ∂sigma) =
        evenMomentModelCoefficient r k * Y.function (2 * k) j (X i) := by
    convert hnode i using 1
    congr 1
    funext x
    ring
  have hmean : (∫ x : Sphere, Y.function (2 * k) j x ∂sigma) = 0 :=
    harmonicBasis_positive_degree_mean_zero Y (2 * k) (by omega) j
  rw [harmonicQuadratureCoefficient_pos_degree Y X (2 * k) (by omega) j]
  unfold harmonicCoefficient
  simp only [centeredEvenMomentTest, ContinuousMap.sub_apply,
    ContinuousMap.coe_const, Function.const_apply, sub_mul]
  rw [integral_sub]
  · simp only [integral_const_mul, hmean, mul_zero, sub_zero]
    simp only [evenMomentTest, ContinuousMap.coe_mk, div_mul_eq_mul_div]
    rw [integral_div]
    simp_rw [Finset.sum_mul]
    rw [integral_finset_sum]
    simp_rw [hnode']
    simp only [← Finset.mul_sum, Fintype.card_fin]
    ring
    intro i _
    have hc : Continuous (fun x : Sphere =>
        (@Inner.inner ℝ Ambient _ (X i : Ambient) (x : Ambient)) ^ (2 * r) *
          Y.function (2 * k) j x) := by fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact ((evenMomentTest X r).continuous.mul (Y.function (2 * k) j).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_const.mul (Y.function (2 * k) j).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Every odd-degree Fourier coefficient of the centered moment test vanishes. -/
theorem centeredEvenMomentTest_coefficient_odd (Y : HarmonicBasis)
    {N : ℕ} (X : Fin N → Sphere) (r k : ℕ)
    (j : Fin (2 * (2 * k + 1) + 1)) :
    harmonicCoefficient Y (centeredEvenMomentTest X r) (2 * k + 1) j = 0 := by
  let H := (harmonicBasisPolynomial Y (2 * k + 1) j).val
  have hH : H ∈ harmonicPolynomialSubmodule (2 * k + 1) :=
    (harmonicBasisPolynomial Y (2 * k + 1) j).property
  have hrepr (x : Sphere) :
      MvPolynomial.eval (fun i => (x : Ambient) i) H =
        Y.function (2 * k + 1) j x := by
    exact congrFun (congrArg DFunLike.coe
      (harmonicBasisPolynomial_restrict Y (2 * k + 1) j)) x
  have hnode (i : Fin N) := odd_projection_harmonic_action hH (X i) r
  simp_rw [hrepr] at hnode
  have hnode' (i : Fin N) :
      (∫ x : Sphere,
        (@Inner.inner ℝ Ambient _ (X i : Ambient) (x : Ambient)) ^ (2 * r) *
          Y.function (2 * k + 1) j x ∂sigma) = 0 := by
    convert hnode i using 1
    congr 1
    funext x
    ring
  have hmean : (∫ x : Sphere, Y.function (2 * k + 1) j x ∂sigma) = 0 :=
    harmonicBasis_positive_degree_mean_zero Y (2 * k + 1) (by omega) j
  unfold harmonicCoefficient
  simp only [centeredEvenMomentTest, ContinuousMap.sub_apply,
    ContinuousMap.coe_const, Function.const_apply, sub_mul]
  rw [integral_sub]
  · simp only [integral_const_mul, hmean, mul_zero, sub_zero]
    simp only [evenMomentTest, ContinuousMap.coe_mk, div_mul_eq_mul_div]
    rw [integral_div]
    simp_rw [Finset.sum_mul]
    rw [integral_finset_sum]
    simp_rw [hnode']
    simp
    intro i _
    have hc : Continuous (fun x : Sphere =>
        (@Inner.inner ℝ Ambient _ (X i : Ambient) (x : Ambient)) ^ (2 * r) *
          Y.function (2 * k + 1) j x) := by fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact ((evenMomentTest X r).continuous.mul
      (Y.function (2 * k + 1) j).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · exact (continuous_const.mul
      (Y.function (2 * k + 1) j).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Polynomial degree bounds make all higher harmonic coefficients vanish. -/
theorem centeredEvenMomentTest_coefficient_high (Y : HarmonicBasis)
    {N : ℕ} (X : Fin N → Sphere) (r ℓ : ℕ) (hℓ : 2 * r < ℓ)
    (j : Fin (2 * ℓ + 1)) :
    harmonicCoefficient Y (centeredEvenMomentTest X r) ℓ j = 0 := by
  conv_lhs => rw [← centeredEvenMomentTest_partialSum Y X r]
  rw [harmonicCoefficient_partialSum]
  simp [show ¬ℓ < 2 * r + 1 by omega]

theorem centeredEvenMomentTest_normTerm_high (Y : HarmonicBasis) (s : ℝ)
    {N : ℕ} (X : Fin N → Sphere) (r ℓ : ℕ) (hℓ : 2 * r < ℓ) :
    sobolevNormTerm Y s (centeredEvenMomentTest X r) ℓ = 0 := by
  simp [sobolevNormTerm, centeredEvenMomentTest_coefficient_high Y X r ℓ hℓ]

theorem centeredEvenMomentTest_summable (Y : HarmonicBasis) (s : ℝ)
    {N : ℕ} (X : Fin N → Sphere) (r : ℕ) :
    Summable (sobolevNormTerm Y s (centeredEvenMomentTest X r)) := by
  apply summable_of_ne_finset_zero (s := Finset.range (2 * r + 1))
  intro ℓ hℓ
  exact centeredEvenMomentTest_normTerm_high Y s X r ℓ (by
    simpa only [Finset.mem_range, not_lt] using hℓ)

theorem centeredEvenMomentTest_normSq_finite (Y : HarmonicBasis) (s : ℝ)
    {N : ℕ} (X : Fin N → Sphere) (r : ℕ) :
    sobolevNormSq Y s (centeredEvenMomentTest X r) =
      ∑ ℓ ∈ Finset.range (2 * r + 1),
        sobolevNormTerm Y s (centeredEvenMomentTest X r) ℓ := by
  unfold sobolevNormSq
  apply tsum_eq_sum
  intro ℓ hℓ
  exact centeredEvenMomentTest_normTerm_high Y s X r ℓ (by
    simpa only [Finset.mem_range, not_lt] using hℓ)

/-- The explicit even-degree coefficient bound controls its spectral mass. -/
theorem centeredEvenMomentTest_normTerm_even_le (Y : HarmonicBasis)
    {N : ℕ} (hN : 0 < N) (X : Fin N → Sphere)
    {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (k : ℕ) (hk : 0 < k) :
    sobolevNormTerm Y s (centeredEvenMomentTest X N) (2 * k) ≤
      (3136 * (N : ℝ) ^ (s - 1)) *
        ∑ j : Fin (2 * (2 * k) + 1),
          harmonicCoefficient Y (centeredEvenMomentTest X N) (2 * k) j *
            harmonicQuadratureCoefficient Y X (2 * k) j := by
  let b := evenMomentModelCoefficient N k
  let w := (1 + ((2 * k : ℕ) : ℝ) * ((2 * k : ℕ) + 1)) ^ s
  let K := 3136 * (N : ℝ) ^ (s - 1)
  have hbound : w * b ≤ K := by
    simpa [w, b, K, Nat.cast_mul] using
      evenMomentModelCoefficient_weighted hN hs0 hs2 (k := k)
  have hnonneg : 0 ≤ b := evenMomentModelCoefficient_nonneg N k
  have hsum := finite_positive_spectral_bound
    (Finset.univ : Finset (Fin (2 * (2 * k) + 1)))
    (fun _ => w) (fun _ => b)
    (fun j => harmonicQuadratureCoefficient Y X (2 * k) j) K
    (by intro j hj; exact hnonneg)
    (by intro j hj; exact hbound)
  simp only [sobolevNormTerm,
    centeredEvenMomentTest_coefficient_even Y X N k hk]
  convert hsum using 1
  · simp only [w, b, Nat.cast_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · simp only [K, b]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring

/-- The finite spectral inequality holds degree by degree. -/
theorem centeredEvenMomentTest_normTerm_le_gapTerm (Y : HarmonicBasis)
    {N : ℕ} (hN : 0 < N) (X : Fin N → Sphere)
    {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (ℓ : ℕ) :
    sobolevNormTerm Y s (centeredEvenMomentTest X N) ℓ ≤
      (3136 * (N : ℝ) ^ (s - 1)) *
        ∑ j : Fin (2 * ℓ + 1),
          harmonicCoefficient Y (centeredEvenMomentTest X N) ℓ j *
            harmonicQuadratureCoefficient Y X ℓ j := by
  rcases Nat.even_or_odd ℓ with he | ho
  · obtain ⟨k, rfl⟩ := he
    by_cases hk : k = 0
    · subst k
      simp [centeredEvenMomentTest_zero_norm_term Y s hN X N,
        centeredEvenMomentTest_zero_coefficient Y hN X N]
    · rw [show k + k = 2 * k by omega]
      exact centeredEvenMomentTest_normTerm_even_le Y hN X hs0 hs2 k
        (Nat.pos_of_ne_zero hk)
  · obtain ⟨k, rfl⟩ := ho
    simp [sobolevNormTerm, centeredEvenMomentTest_coefficient_odd Y X N k]

/-- The actual centered moment test satisfies the required spectral estimate. -/
theorem evenMomentSpectralBound (Y : HarmonicBasis) {s : ℝ}
    (hs0 : 0 ≤ s) (hs2 : s ≤ 2) : EvenMomentSpectralBound Y s := by
  refine ⟨3136, by norm_num, ?_⟩
  intro N hN X
  let g := centeredEvenMomentTest X N
  have hgap := quadratureError_partialSum Y X g (2 * N + 1)
  rw [centeredEvenMomentTest_partialSum Y X N] at hgap
  constructor
  · exact centeredEvenMomentTest_summable Y s X N
  · rw [centeredEvenMomentTest_normSq_finite]
    calc
      (∑ ℓ ∈ Finset.range (2 * N + 1), sobolevNormTerm Y s g ℓ) ≤
          ∑ ℓ ∈ Finset.range (2 * N + 1),
            (3136 * (N : ℝ) ^ (s - 1)) *
              ∑ j : Fin (2 * ℓ + 1),
                harmonicCoefficient Y g ℓ j * harmonicQuadratureCoefficient Y X ℓ j := by
            apply Finset.sum_le_sum
            intro ℓ hℓ
            exact centeredEvenMomentTest_normTerm_le_gapTerm Y hN X hs0 hs2 ℓ
      _ = (3136 * (N : ℝ) ^ (s - 1)) * quadratureError X g := by
            rw [← Finset.mul_sum, ← hgap]

/-- Universal optimality for the genuine Sobolev norm, once its embedding is
available. The moment estimate itself is unconditional above. -/
theorem sobolevOptimality_of_embedding (Y : HarmonicBasis) {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) (hemb : SobolevEmbedding Y s) :
    SobolevOptimality Y s :=
  sobolev_optimality_of_even_moment_spectral_bound Y hs1 hemb
    (evenMomentSpectralBound Y (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) hs1))
      (le_of_lt hs2))

/-- The universal Sobolev cubature lower bound for every harmonic basis and
every exponent in the manuscript's range. -/
theorem sobolevOptimality (Y : HarmonicBasis) {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) : SobolevOptimality Y s :=
  sobolevOptimality_of_embedding Y hs1 hs2
    (sobolevEmbedding_of_harmonicAddition Y hs1)

end BEMOC.Definitive
