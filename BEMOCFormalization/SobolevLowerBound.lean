import BEMOCFormalization.HarmonicBasis
import BEMOCFormalization.SobolevBasic
import BEMOCFormalization.CapLowerBound

/-!
# Universal Sobolev cubature lower bound

The even projection moment supplies a positive test for every finite node set.
Its quantitative spectral norm estimate is the analytic part of optimality.
-/

open scoped BigOperators
open MeasureTheory

namespace BEMOC.Definitive

/-- The average of the even projection powers centered at the quadrature nodes. -/
noncomputable def evenMomentTest {n : ℕ} (X : Fin n → Sphere) (r : ℕ) :
    C(Sphere, ℝ) :=
  ⟨fun x => (∑ i : Fin n,
      (@Inner.inner ℝ Ambient _ (X i : Ambient) (x : Ambient)) ^ (2 * r)) /
        (n : ℝ), by
    fun_prop⟩

/-- Its integral is the corresponding uniform spherical projection moment. -/
theorem evenMomentTest_integral {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) (r : ℕ) :
    (∫ x : Sphere, evenMomentTest X r x ∂sigma) =
      1 / ((2 * r + 1 : ℕ) : ℝ) := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [evenMomentTest, ContinuousMap.coe_mk]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  rw [integral_finset_sum]
  simp_rw [sphere_projection_even_moment]
  simp only [Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring
  intro i _
  have hc : Continuous (fun a : Sphere =>
      (@Inner.inner ℝ Ambient _ (X i : Ambient) (a : Ambient)) ^ (2 * r)) := by
    fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The error of the test is exactly the nonnegative even-moment gap. -/
theorem quadratureError_evenMomentTest {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) (r : ℕ) :
    quadratureError X (evenMomentTest X r) =
      (∑ i : Fin n, ∑ j : Fin n,
        (@Inner.inner ℝ Ambient _ (X i : Ambient) (X j : Ambient)) ^ (2 * r)) /
          (n : ℝ) ^ 2 - 1 / ((2 * r + 1 : ℕ) : ℝ) := by
  rw [quadratureError, evenMomentTest_integral hn]
  simp only [evenMomentTest, ContinuousMap.coe_mk, Fintype.card_fin]
  rw [Finset.sum_comm]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

/-- At degree `2n`, the concrete moment test has error at least `1/(2n)`. -/
theorem quadratureError_evenMomentTest_ge {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) :
    1 / (2 * (n : ℝ)) ≤ quadratureError X (evenMomentTest X n) := by
  rw [quadratureError_evenMomentTest hn]
  exact even_projection_moment_gap_ge hn X n le_rfl

/-- Remove the degree-zero component of the moment test. -/
noncomputable def centeredEvenMomentTest {n : ℕ} (X : Fin n → Sphere) (r : ℕ) :
    C(Sphere, ℝ) :=
  evenMomentTest X r - ContinuousMap.const Sphere (1 / ((2 * r + 1 : ℕ) : ℝ))

/-- The centered test has zero surface mean. -/
theorem centeredEvenMomentTest_integral {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) (r : ℕ) :
    (∫ x : Sphere, centeredEvenMomentTest X r x ∂sigma) = 0 := by
  have hint : Integrable (fun x : Sphere => evenMomentTest X r x) sigma :=
    (evenMomentTest X r).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [centeredEvenMomentTest, ContinuousMap.sub_apply,
    ContinuousMap.coe_const, Function.const_apply]
  rw [integral_sub hint (integrable_const _), evenMomentTest_integral hn]
  simp

/-- Centering removes every degree-zero Fourier coefficient of the test. -/
theorem centeredEvenMomentTest_zero_coefficient (Y : HarmonicBasis)
    {n : ℕ} (hn : 0 < n) (X : Fin n → Sphere) (r : ℕ)
    (k : Fin 1) :
    harmonicCoefficient Y (centeredEvenMomentTest X r) 0 k = 0 := by
  obtain ⟨p, hp, -, heval⟩ := Y.harmonic 0 k
  let c : ℝ := MvPolynomial.coeff 0 p
  have hc (x : Sphere) : Y.function 0 k x = c := by
    rw [heval x, homogeneous_zero_eq_constant hp]
    simp [c]
  unfold harmonicCoefficient
  simp_rw [hc]
  rw [integral_mul_const, centeredEvenMomentTest_integral hn]
  simp

/-- The centered test contributes no spectral mass in degree zero. -/
theorem centeredEvenMomentTest_zero_norm_term (Y : HarmonicBasis) (s : ℝ)
    {n : ℕ} (hn : 0 < n) (X : Fin n → Sphere) (r : ℕ) :
    sobolevNormTerm Y s (centeredEvenMomentTest X r) 0 = 0 := by
  unfold sobolevNormTerm
  simp [centeredEvenMomentTest_zero_coefficient Y hn X r]

/-- Centering does not change the equal-weight quadrature error. -/
theorem quadratureError_centeredEvenMomentTest {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) (r : ℕ) :
    quadratureError X (centeredEvenMomentTest X r) =
      quadratureError X (evenMomentTest X r) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [quadratureError, centeredEvenMomentTest_integral hn]
  simp only [centeredEvenMomentTest, ContinuousMap.sub_apply,
    ContinuousMap.coe_const, Function.const_apply, Fintype.card_fin]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [quadratureError, evenMomentTest_integral hn]
  simp only [Fintype.card_fin]
  have hden : (((2 * r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hnr, hden]
  left
  ring

/-- The centered moment test retains the universal positive gap. -/
theorem quadratureError_centeredEvenMomentTest_ge {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) :
    1 / (2 * (n : ℝ)) ≤ quadratureError X (centeredEvenMomentTest X n) := by
  rw [quadratureError_centeredEvenMomentTest hn]
  exact quadratureError_evenMomentTest_ge hn X

/-- The centered moment test is the restriction of an explicit polynomial of
degree at most `2r` in the evaluation variable. -/
noncomputable def centeredEvenMomentPolynomial {n : ℕ}
    (X : Fin n → Sphere) (r : ℕ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C ((n : ℝ)⁻¹) *
    (∑ i : Fin n,
      (∑ j : Fin 3, MvPolynomial.C ((X i : Ambient) j) *
        MvPolynomial.X j) ^ (2 * r)) -
    MvPolynomial.C (1 / ((2 * r + 1 : ℕ) : ℝ))

theorem centeredEvenMomentPolynomial_restrict {n : ℕ}
    (X : Fin n → Sphere) (r : ℕ) :
    restrictPolynomial (centeredEvenMomentPolynomial X r) =
      centeredEvenMomentTest X r := by
  ext x
  simp only [restrictPolynomial_apply, centeredEvenMomentPolynomial,
    centeredEvenMomentTest, ContinuousMap.sub_apply,
    ContinuousMap.coe_const, Function.const_apply, evenMomentTest,
    ContinuousMap.coe_mk, map_sub, map_mul, map_sum, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three, div_eq_mul_inv, mul_comm]

theorem centeredEvenMomentPolynomial_totalDegree_le {n : ℕ}
    (X : Fin n → Sphere) (r : ℕ) :
    (centeredEvenMomentPolynomial X r).totalDegree ≤ 2 * r := by
  have hlinear (i : Fin n) :
      (∑ j : Fin 3, MvPolynomial.C ((X i : Ambient) j) *
        MvPolynomial.X j).IsHomogeneous 1 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j hj
    exact (MvPolynomial.isHomogeneous_X ℝ j).C_mul _
  have hpow (i : Fin n) :
      ((∑ j : Fin 3, MvPolynomial.C ((X i : Ambient) j) *
        MvPolynomial.X j) ^ (2 * r)).IsHomogeneous (2 * r) := by
    simpa using (hlinear i).pow (2 * r)
  have hsum :
      (∑ i : Fin n,
        (∑ j : Fin 3, MvPolynomial.C ((X i : Ambient) j) *
          MvPolynomial.X j) ^ (2 * r)).IsHomogeneous (2 * r) := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    exact hpow i
  have hscaled := hsum.C_mul ((n : ℝ)⁻¹)
  unfold centeredEvenMomentPolynomial
  exact (MvPolynomial.totalDegree_sub_C_le _ _).trans hscaled.totalDegree_le

/-- The actual spectral norm squared, defined only for summable inputs. -/
noncomputable def sobolevNormSq (Y : HarmonicBasis) (s : ℝ)
    (f : C(Sphere, ℝ)) : ℝ :=
  ∑' ℓ, sobolevNormTerm Y s f ℓ

/-- Fourier coefficients scale exactly with the continuous test function. -/
theorem harmonicCoefficient_smul_lower (Y : HarmonicBasis) (c : ℝ)
    (f : C(Sphere, ℝ)) (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    harmonicCoefficient Y (c • f) ℓ k = c * harmonicCoefficient Y f ℓ k := by
  unfold harmonicCoefficient
  simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc,
    ← integral_const_mul]

/-- The spectral norm term is quadratic under scalar multiplication. -/
theorem sobolevNormTerm_smul_lower (Y : HarmonicBasis) (s c : ℝ)
    (f : C(Sphere, ℝ)) (ℓ : ℕ) :
    sobolevNormTerm Y s (c • f) ℓ = c ^ (2 : ℕ) * sobolevNormTerm Y s f ℓ := by
  simp only [sobolevNormTerm, harmonicCoefficient_smul_lower]
  simp only [mul_pow]
  rw [← Finset.mul_sum]
  ring

/-- Summability of the spectral norm is preserved by scaling. -/
theorem sobolevNormTerm_smul_summable (Y : HarmonicBasis) (s c : ℝ)
    (f : C(Sphere, ℝ)) (hf : Summable (sobolevNormTerm Y s f)) :
    Summable (sobolevNormTerm Y s (c • f)) := by
  have heq : sobolevNormTerm Y s (c • f) =
      fun ℓ => c ^ (2 : ℕ) * sobolevNormTerm Y s f ℓ := by
    funext ℓ
    exact sobolevNormTerm_smul_lower Y s c f ℓ
  rw [heq]
  exact hf.mul_left _

/-- The whole spectral norm squared is quadratic under scalar multiplication. -/
theorem sobolevNormSq_smul (Y : HarmonicBasis) (s c : ℝ)
    (f : C(Sphere, ℝ)) :
    sobolevNormSq Y s (c • f) = c ^ (2 : ℕ) * sobolevNormSq Y s f := by
  unfold sobolevNormSq
  simp_rw [sobolevNormTerm_smul_lower]
  rw [tsum_mul_left]

/-- The quadrature error scales with the same real scalar. -/
theorem quadratureError_smul_lower {ι : Type} [Fintype ι]
    (X : ι → Sphere) (f : C(Sphere, ℝ)) (c : ℝ) :
    quadratureError X (c • f) = c * quadratureError X f := by
  unfold quadratureError
  simp only [ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum,
    integral_const_mul]
  ring

/-- Interpolate an `L¹` coefficient estimate with a twice-differentiated
estimate. This is the arithmetic step in the moment-kernel spectral bound. -/
theorem moment_coefficient_interpolation
    {n L b K s : ℝ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hK : 1 ≤ K) (hs0 : 0 ≤ s) (hs2 : s ≤ 2)
    (hb : 0 ≤ b) (hcoarse : b ≤ 1 / n)
    (hderiv : b ≤ K * n / L ^ (2 : ℕ)) :
    L ^ s * b ≤ K * n ^ (s - 1) := by
  have hnpos : 0 < n := by linarith
  have hLpos : 0 < L := by linarith
  rcases le_total L n with hsmall | hlarge
  · have hpow : L ^ s ≤ n ^ s :=
      Real.rpow_le_rpow hLpos.le hsmall hs0
    calc
      L ^ s * b ≤ n ^ s * (1 / n) :=
        mul_le_mul hpow hcoarse (by positivity) (by positivity)
      _ = n ^ (s - 1) := by
        rw [Real.rpow_sub hnpos, Real.rpow_one]
        ring
      _ ≤ K * n ^ (s - 1) := by
        exact le_mul_of_one_le_left (by positivity) hK
  · have hpow : L ^ (s - 2) ≤ n ^ (s - 2) :=
      Real.rpow_le_rpow_of_exponent_nonpos hnpos hlarge (by linarith)
    have hbase : L ^ s * (K * n / L ^ (2 : ℕ)) =
        K * n * L ^ (s - 2) := by
      rw [Real.rpow_sub hLpos]
      have htwo : L ^ (2 : ℕ) = L ^ (2 : ℝ) :=
        (Real.rpow_natCast L 2).symm
      rw [htwo]
      ring
    calc
      L ^ s * b ≤ L ^ s * (K * n / L ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hderiv (by positivity)
      _ = K * n * L ^ (s - 2) := hbase
      _ ≤ K * n * n ^ (s - 2) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = K * n ^ (s - 1) := by
        have heq : n * n ^ (s - 2) = n ^ (s - 1) := by
          calc
            _ = n ^ (1 : ℝ) * n ^ (s - 2) := by rw [Real.rpow_one]
            _ = n ^ ((1 : ℝ) + (s - 2)) := (Real.rpow_add hnpos _ _).symm
            _ = _ := by congr 1; ring
        rw [mul_assoc, heq]

/-- Product factor in the even Legendre expansion of `t^(2n)`. -/
private noncomputable def evenMomentRatio (n j : ℕ) : ℝ :=
  (2 * ((n : ℝ) - j)) / (2 * (n : ℝ) + 2 * j + 3)

/-- The explicit candidate coefficient in harmonic degree `2k`; it is zero
above the polynomial degree. -/
noncomputable def evenMomentModelCoefficient (n k : ℕ) : ℝ :=
  if k ≤ n then
    (1 / (2 * (n : ℝ) + 1)) * ∏ j ∈ Finset.range k, evenMomentRatio n j
  else 0

private theorem evenMomentRatio_nonneg {n j : ℕ} (hj : j ≤ n) :
    0 ≤ evenMomentRatio n j := by
  unfold evenMomentRatio
  have h : (j : ℝ) ≤ n := by exact_mod_cast hj
  exact div_nonneg (by linarith) (by positivity)

/-- Each factor is bounded by the exponential of a negative linear term. -/
private theorem evenMomentRatio_le_exp {n j : ℕ}
    (hn : 0 < n) (hj : j ≤ n) :
    evenMomentRatio n j ≤ Real.exp (-(j : ℝ) / n) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hjr : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hd : (0 : ℝ) < 2 * (n : ℝ) + 2 * j + 3 := by positivity
  have hpart : evenMomentRatio n j ≤ 1 - (j : ℝ) / n := by
    unfold evenMomentRatio
    have heq : 1 - (j : ℝ) / n = ((n : ℝ) - j) / n := by
      field_simp
    rw [heq]
    apply (div_le_iff₀ hd).2
    have haux : 0 ≤ ((n : ℝ) - j) * (2 * (j : ℝ) + 3) :=
      mul_nonneg (by linarith) (by positivity)
    have hbase : 2 * ((n : ℝ) - j) ≤
        (((n : ℝ) - j) * (2 * (n : ℝ) + 2 * j + 3)) / n :=
      (le_div_iff₀ hnr).2 (by nlinarith [haux])
    convert hbase using 1 <;> ring
  calc
    evenMomentRatio n j ≤ 1 - (j : ℝ) / n := hpart
    _ ≤ Real.exp (-(j : ℝ) / n) := by
      convert Real.add_one_le_exp (-(j : ℝ) / n) using 1 <;> ring

/-- The candidate coefficients have a Gaussian product upper bound. -/
theorem evenMomentModelCoefficient_le_exp {n k : ℕ}
    (hn : 0 < n) (hk : k ≤ n) :
    evenMomentModelCoefficient n k ≤
      (1 / (2 * (n : ℝ) + 1)) *
        Real.exp (-(k : ℝ) * (k - 1) / (2 * n)) := by
  classical
  have hprod : (∏ j ∈ Finset.range k, evenMomentRatio n j) ≤
      ∏ j ∈ Finset.range k, Real.exp (-(j : ℝ) / n) := by
    apply Finset.prod_le_prod
    · intro j hj
      exact evenMomentRatio_nonneg (by have := Finset.mem_range.mp hj; omega)
    · intro j hj
      exact evenMomentRatio_le_exp hn (by have := Finset.mem_range.mp hj; omega)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum_general : ∀ t : ℕ,
      (∑ j ∈ Finset.range t, -(j : ℝ) / n) =
        -(t : ℝ) * (t - 1) / (2 * n) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  have hsum := hsum_general k
  rw [evenMomentModelCoefficient, if_pos hk]
  have hfactor : 0 ≤ 1 / (2 * (n : ℝ) + 1) := by positivity
  calc
    _ ≤ (1 / (2 * (n : ℝ) + 1)) *
        (∏ j ∈ Finset.range k, Real.exp (-(j : ℝ) / n)) :=
      mul_le_mul_of_nonneg_left hprod hfactor
    _ = _ := by rw [← Real.exp_sum, hsum]

/-- A useful polynomial tail bound for the Gaussian majorant. -/
private theorem exp_neg_le_four_div_sq {u : ℝ} (hu : 0 < u) :
    Real.exp (-u) ≤ 4 / u ^ (2 : ℕ) := by
  have hlin := Real.add_one_le_exp (u / 2)
  have hhalf : 0 ≤ u / 2 := by linarith
  have hdiff : 0 ≤ Real.exp (u / 2) - u / 2 := by linarith
  have hsum : 0 ≤ Real.exp (u / 2) + u / 2 := by positivity
  have hsq : (u / 2) ^ (2 : ℕ) ≤ Real.exp u := by
    have hmul := mul_nonneg hdiff hsum
    have hexp : Real.exp u = (Real.exp (u / 2)) ^ (2 : ℕ) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    nlinarith
  rw [Real.exp_neg]
  have hform : 1 / Real.exp u ≤ 4 / u ^ (2 : ℕ) := by
    apply (div_le_div_iff₀ (Real.exp_pos u) (by positivity : 0 < u ^ (2 : ℕ))).2
    nlinarith [hsq]
  simpa only [one_div] using hform

/-- Above the square-root scale, the explicit even coefficient decays with
four powers of the harmonic degree. -/
theorem evenMomentModelCoefficient_poly_decay {n k : ℕ}
    (hn : 0 < n) (hk2 : 2 ≤ k) (hkn : k ≤ n) :
    evenMomentModelCoefficient n k ≤ 64 * (n : ℝ) / (k : ℝ) ^ (4 : ℕ) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  let u : ℝ := (k : ℝ) * (k - 1) / (2 * n)
  have hu : 0 < u := by
    dsimp [u]
    exact div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  have huLower : (k : ℝ) ^ (2 : ℕ) / (4 * n) ≤ u := by
    dsimp [u]
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * (n : ℝ))
      (by positivity : 0 < 2 * (n : ℝ))).2
    have hterm : 0 ≤ (k : ℝ) * ((k : ℝ) - 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hterm]
  have hb := evenMomentModelCoefficient_le_exp hn hkn
  have hexp := exp_neg_le_four_div_sq hu
  have hmain : evenMomentModelCoefficient n k ≤
      (1 / (2 * (n : ℝ) + 1)) * (4 / u ^ (2 : ℕ)) := by
    have hhexp : Real.exp (-(k : ℝ) * (k - 1) / (2 * n)) ≤
        4 / u ^ (2 : ℕ) := by
      have heq : -(k : ℝ) * (k - 1) / (2 * n) = -u := by
        dsimp [u]
        ring
      rw [heq]
      exact hexp
    exact hb.trans (mul_le_mul_of_nonneg_left hhexp (by positivity))
  have hbound : (1 / (2 * (n : ℝ) + 1)) * (4 / u ^ (2 : ℕ)) ≤
      64 * (n : ℝ) / (k : ℝ) ^ (4 : ℕ) := by
    have hupos : 0 < u ^ (2 : ℕ) := by positivity
    have hk4 : 0 < (k : ℝ) ^ (4 : ℕ) := by positivity
    have hsquare : ((k : ℝ) ^ (2 : ℕ) / (4 * n)) ^ (2 : ℕ) ≤
        u ^ (2 : ℕ) := by
      exact (sq_le_sq₀ (by positivity) hu.le).2 huLower
    have hsquare' : (k : ℝ) ^ (4 : ℕ) ≤
        16 * (n : ℝ) ^ (2 : ℕ) * u ^ (2 : ℕ) := by
      rw [div_pow] at hsquare
      have hn4 : 0 < (4 * (n : ℝ)) ^ (2 : ℕ) := by positivity
      have hh := (div_le_iff₀ hn4).1 hsquare
      nlinarith
    have htail : 4 / u ^ (2 : ℕ) ≤
        64 * (n : ℝ) ^ (2 : ℕ) / (k : ℝ) ^ (4 : ℕ) := by
      exact (div_le_div_iff₀ hupos hk4).2 (by nlinarith [hsquare'])
    have hfirst : 1 / (2 * (n : ℝ) + 1) ≤ 1 / n := by
      exact one_div_le_one_div_of_le hnr (by linarith)
    have hcomb := mul_le_mul hfirst htail (by positivity) (by positivity)
    calc
      _ ≤ (1 / (n : ℝ)) *
          (64 * (n : ℝ) ^ (2 : ℕ) / (k : ℝ) ^ (4 : ℕ)) := hcomb
      _ = _ := by field_simp; ring
  exact hmain.trans hbound

/-- The explicit coefficients are nonnegative in every degree. -/
theorem evenMomentModelCoefficient_nonneg (n k : ℕ) :
    0 ≤ evenMomentModelCoefficient n k := by
  by_cases hk : k ≤ n
  · rw [evenMomentModelCoefficient, if_pos hk]
    apply mul_nonneg (by positivity)
    apply Finset.prod_nonneg
    intro j hj
    exact evenMomentRatio_nonneg (by have := Finset.mem_range.mp hj; omega)
  · simp [evenMomentModelCoefficient, hk]

/-- The zeroth coefficient bounds all even-degree model coefficients. -/
theorem evenMomentModelCoefficient_le_one_div {n k : ℕ}
    (hn : 0 < n) :
    evenMomentModelCoefficient n k ≤ 1 / (n : ℝ) := by
  by_cases hk : k ≤ n
  · have hb := evenMomentModelCoefficient_le_exp hn hk
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hnonneg : 0 ≤ (k : ℝ) * (k - 1) := by
      by_cases hk0 : k = 0
      · subst k
        norm_num
      · have hk1 : (1 : ℝ) ≤ k := by
          exact_mod_cast (by omega : 1 ≤ k)
        exact mul_nonneg (by positivity) (by linarith)
    have hexp : Real.exp (-(k : ℝ) * (k - 1) / (2 * n)) ≤ 1 := by
      have harg : -(k : ℝ) * (k - 1) / (2 * n) ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr harg)
    have hfirst : 0 ≤ 1 / (2 * (n : ℝ) + 1) := by positivity
    have hfrac : 1 / (2 * (n : ℝ) + 1) ≤ 1 / n :=
      one_div_le_one_div_of_le hnr (by linarith)
    exact hb.trans ((mul_le_mul_of_nonneg_left hexp hfirst).trans
      (by simpa using hfrac))
  · simp [evenMomentModelCoefficient, hk]

/-- The explicit coefficient has the decay needed for two spherical
derivatives, with a deliberately generous universal constant. -/
theorem evenMomentModelCoefficient_derivative_bound {n k : ℕ}
    (hn : 0 < n) :
    evenMomentModelCoefficient n k ≤
      3136 * (n : ℝ) /
        (1 + (2 * (k : ℝ)) * (2 * (k : ℝ) + 1)) ^ (2 : ℕ) := by
  let L : ℝ := 1 + (2 * (k : ℝ)) * (2 * (k : ℝ) + 1)
  have hnreal : (1 : ℝ) ≤ n := by
    exact_mod_cast (by omega : 1 ≤ n)
  have hL : 1 ≤ L := by dsimp [L]; nlinarith [sq_nonneg (k : ℝ)]
  have hLpos : 0 < L := by linarith
  by_cases hk2 : 2 ≤ k
  · by_cases hkn : k ≤ n
    · have hb := evenMomentModelCoefficient_poly_decay hn hk2 hkn
      have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have hL7 : L ≤ 7 * (k : ℝ) ^ (2 : ℕ) := by
        dsimp [L]
        nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) - 1 by linarith)
          (show 0 ≤ (k : ℝ) + 1 by linarith)]
      have hLsq : L ^ (2 : ℕ) ≤ 49 * (k : ℝ) ^ (4 : ℕ) := by
        nlinarith [mul_nonneg (show 0 ≤ 7 * (k : ℝ) ^ (2 : ℕ) - L by linarith)
          (show 0 ≤ 7 * (k : ℝ) ^ (2 : ℕ) + L by positivity)]
      have hk4 : 0 < (k : ℝ) ^ (4 : ℕ) := by positivity
      have hLsqpos : 0 < L ^ (2 : ℕ) := by positivity
      have hratio : 64 * (n : ℝ) / (k : ℝ) ^ (4 : ℕ) ≤
          3136 * (n : ℝ) / L ^ (2 : ℕ) := by
        apply (div_le_div_iff₀ hk4 hLsqpos).2
        nlinarith [mul_le_mul_of_nonneg_left hLsq
          (show 0 ≤ 64 * (n : ℝ) by positivity)]
      exact hb.trans (by simpa only [L] using hratio)
    · simp [evenMomentModelCoefficient, hk2, hkn]
      positivity
  · have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with rfl | rfl
    · have hb := evenMomentModelCoefficient_le_one_div (n := n) (k := 0) hn
      have hgoal : 1 / (n : ℝ) ≤ 3136 * (n : ℝ) / (1 : ℝ) := by
        apply (div_le_iff₀ (by positivity : 0 < (n : ℝ))).2
        nlinarith
      simpa [L] using hb.trans hgoal
    · have hb := evenMomentModelCoefficient_le_one_div (n := n) (k := 1) hn
      have hgoal : 1 / (n : ℝ) ≤ 3136 * (n : ℝ) / (7 : ℝ) ^ (2 : ℕ) := by
        apply (div_le_div_iff₀ (by positivity : 0 < (n : ℝ))
          (by norm_num : (0 : ℝ) < (7 : ℝ) ^ (2 : ℕ))).2
        nlinarith
      norm_num [L] at hgoal ⊢
      have hgoal' : 1 / (n : ℝ) ≤ 3136 * (n : ℝ) / 49 := by
        simpa only [one_div] using hgoal
      exact hb.trans hgoal'

/-- Complete weighted scalar estimate for the explicit even-coefficient
model. Harmonic diagonalization is the remaining bridge to the spectral norm. -/
theorem evenMomentModelCoefficient_weighted {n k : ℕ} {s : ℝ}
    (hn : 0 < n) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    (1 + (2 * (k : ℝ)) * (2 * (k : ℝ) + 1)) ^ s *
      evenMomentModelCoefficient n k ≤ 3136 * (n : ℝ) ^ (s - 1) := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  exact moment_coefficient_interpolation hnreal
    (by nlinarith [sq_nonneg (k : ℝ)] :
      (1 : ℝ) ≤ 1 + (2 * (k : ℝ)) * (2 * (k : ℝ) + 1))
    (by norm_num) hs0 hs2 (evenMomentModelCoefficient_nonneg n k)
    (evenMomentModelCoefficient_le_one_div hn)
    (evenMomentModelCoefficient_derivative_bound hn)

/-- Finite positive spectral bookkeeping: a pointwise weighted coefficient
bound turns the squared-coefficient norm into one coefficient times the
positive quadrature gap. -/
theorem finite_positive_spectral_bound {ι : Type*} (S : Finset ι)
    (w b a : ι → ℝ) (K : ℝ)
    (hb : ∀ i ∈ S, 0 ≤ b i)
    (hw : ∀ i ∈ S, w i * b i ≤ K) :
    (∑ i ∈ S, w i * (b i) ^ (2 : ℕ) * (a i) ^ (2 : ℕ)) ≤
      K * ∑ i ∈ S, b i * (a i) ^ (2 : ℕ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hnonneg : 0 ≤ b i * (a i) ^ (2 : ℕ) :=
    mul_nonneg (hb i hi) (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_right (hw i hi) hnonneg
  nlinarith

/-- The first nonconstant zonal moment agrees with the product coefficient.
This is the degree-two case of the Funk–Hecke calculation. -/
theorem even_projection_quadratic_zonal_integral (u : Sphere) (n : ℕ) :
    (∫ x : Sphere,
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) *
        ((@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 : ℕ) -
          (1 / 3 : ℝ)) ∂sigma) =
      (4 * (n : ℝ)) / (3 * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by
  have hcont (m : ℕ) : Continuous (fun x : Sphere =>
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ m) := by
    fun_prop
  have hint (m : ℕ) : Integrable (fun x : Sphere =>
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ m) sigma :=
    (hcont m).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [mul_sub, mul_div_assoc]
  rw [integral_sub]
  · have hpow (x : Sphere) :
        (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) *
          (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 : ℕ) =
        (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * (n + 1)) := by
        rw [← pow_add]
        congr 1
    simp_rw [hpow]
    rw [integral_mul_const, sphere_projection_even_moment,
      sphere_projection_even_moment]
    push_cast
    have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring
  · convert hint (2 * (n + 1)) using 1
    ext x
    rw [← pow_add]
    congr 1
  · exact (hint (2 * n)).mul_const _

/-- The explicit degree-two coefficient is the centered quadratic zonal
integral (the first nonconstant Legendre coefficient). -/
theorem evenMomentModelCoefficient_one {n : ℕ} (hn : 0 < n) :
    evenMomentModelCoefficient n 1 =
      2 * (n : ℝ) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by
  rw [evenMomentModelCoefficient, if_pos (by omega : 1 ≤ n)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  unfold evenMomentRatio
  norm_num
  have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  field_simp

theorem even_projection_legendre_two_integral (u : Sphere) {n : ℕ}
    (hn : 0 < n) :
    (∫ x : Sphere,
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) *
        ((3 * (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 : ℕ) -
          1) / 2) ∂sigma) = evenMomentModelCoefficient n 1 := by
  have hpoint (x : Sphere) :
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) *
        ((3 * (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 : ℕ) -
          1) / 2) =
      (3 / 2 : ℝ) *
        ((@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) *
          ((@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 : ℕ) -
            (1 / 3 : ℝ))) := by ring
  simp_rw [hpoint]
  rw [integral_const_mul, even_projection_quadratic_zonal_integral,
    evenMomentModelCoefficient_one hn]
  have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  field_simp
  ring

/-- Integration of any finite even zonal polynomial reduces to its scalar
monomial moments. This is the finite integration step needed by a general
Legendre coefficient calculation. -/
theorem sphere_even_zonal_polynomial_integral (u : Sphere)
    (S : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x : Sphere, ∑ k ∈ S,
      a k * (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * k)
      ∂sigma) =
      ∑ k ∈ S, a k / ((2 * k + 1 : ℕ) : ℝ) := by
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_const_mul, sphere_projection_even_moment]
    ring
  · intro k hk
    have hc : Continuous (fun x : Sphere =>
        a k * (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * k)) := by
      fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The even projection moment is a homogeneous polynomial identity in an
arbitrary ambient vector, not only a unit direction. -/
theorem ambient_projection_even_moment (u : Ambient) (r : ℕ) :
    (∫ x : Sphere,
      (@Inner.inner ℝ Ambient _ u (x : Ambient)) ^ (2 * r) ∂sigma) =
      ‖u‖ ^ (2 * r) / ((2 * r + 1 : ℕ) : ℝ) := by
  by_cases hu : u = 0
  · subst u
    simp only [inner_zero_left]
    rw [integral_const]
    cases r with
    | zero => norm_num
    | succ r => simp
  · have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let v : Sphere := ⟨‖u‖⁻¹ • u, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
      exact inv_mul_cancel₀ hnorm.ne'⟩
    have huv : u = ‖u‖ • (v : Ambient) := by
      change u = ‖u‖ • (‖u‖⁻¹ • u)
      rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
    have hpoint (x : Sphere) :
        (@Inner.inner ℝ Ambient _ u (x : Ambient)) ^ (2 * r) =
          ‖u‖ ^ (2 * r) *
            (@Inner.inner ℝ Ambient _ (v : Ambient) (x : Ambient)) ^ (2 * r) := by
      have hi : (@Inner.inner ℝ Ambient _ u (x : Ambient)) =
          ‖u‖ * (@Inner.inner ℝ Ambient _ (v : Ambient) (x : Ambient)) := by
        conv_lhs => rw [huv]
        rw [real_inner_smul_left]
      rw [hi, mul_pow]
    simp_rw [hpoint]
    rw [integral_const_mul, sphere_projection_even_moment]
    ring

/-- The same moment identity expressed as a polynomial in the three
coordinates of the ambient vector, ready for polarization. -/
theorem ambient_projection_even_moment_inner (u : Ambient) (r : ℕ) :
    (∫ x : Sphere,
      (@Inner.inner ℝ Ambient _ u (x : Ambient)) ^ (2 * r) ∂sigma) =
      (@Inner.inner ℝ Ambient _ u u) ^ r / ((2 * r + 1 : ℕ) : ℝ) := by
  rw [ambient_projection_even_moment, real_inner_self_eq_norm_sq]
  congr 1
  rw [← pow_mul]

/-- Every odd homogeneous projection moment vanishes for arbitrary ambient
vectors; this is the parity half of the polarization calculation. -/
theorem ambient_projection_odd_moment (u : Ambient) (r : ℕ) :
    (∫ x : Sphere,
      (@Inner.inner ℝ Ambient _ u (x : Ambient)) ^ (2 * r + 1) ∂sigma) = 0 := by
  by_cases hu : u = 0
  · subst u
    simp
  · have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let v : Sphere := ⟨‖u‖⁻¹ • u, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
      exact inv_mul_cancel₀ hnorm.ne'⟩
    have huv : u = ‖u‖ • (v : Ambient) := by
      change u = ‖u‖ • (‖u‖⁻¹ • u)
      rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
    have hpoint (x : Sphere) :
        (@Inner.inner ℝ Ambient _ u (x : Ambient)) ^ (2 * r + 1) =
          ‖u‖ ^ (2 * r + 1) *
            (@Inner.inner ℝ Ambient _ (v : Ambient) (x : Ambient)) ^ (2 * r + 1) := by
      have hi : (@Inner.inner ℝ Ambient _ u (x : Ambient)) =
          ‖u‖ * (@Inner.inner ℝ Ambient _ (v : Ambient) (x : Ambient)) := by
        conv_lhs => rw [huv]
        rw [real_inner_smul_left]
      rw [hi, mul_pow]
    simp_rw [hpoint]
    rw [integral_const_mul, sphere_projection_odd_moment]
    ring

/-- The inner product with a fixed point, represented as a polynomial in an
ambient vector. Its partial derivatives are coordinate constants. -/
noncomputable def projectionPolynomial (x : Ambient) :
    MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, MvPolynomial.C (x i) * MvPolynomial.X i

theorem projectionPolynomial_eval (x u : Ambient) :
    MvPolynomial.eval (fun i => u i) (projectionPolynomial x) =
      @Inner.inner ℝ Ambient _ u x := by
  simp only [projectionPolynomial, map_sum, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

theorem projectionPolynomial_pderiv (x : Ambient) (i : Fin 3) :
    MvPolynomial.pderiv i (projectionPolynomial x) =
      MvPolynomial.C (x i) := by
  classical
  simp only [projectionPolynomial, map_sum]
  simp [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
    Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]

/-- One partial derivative of a projection power supplies its corresponding
coordinate factor, the basic step in harmonic polarization. -/
theorem projectionPolynomial_pderiv_pow (x : Ambient) (i : Fin 3) (m : ℕ) :
    MvPolynomial.pderiv i ((projectionPolynomial x) ^ m) =
      (m : MvPolynomial (Fin 3) ℝ) * MvPolynomial.C (x i) *
        (projectionPolynomial x) ^ (m - 1) := by
  rw [MvPolynomial.pderiv_pow, projectionPolynomial_pderiv]
  ring

/-- Fixed polynomial monomial indexed by a word of coordinate directions. -/
noncomputable def coordinateWordPolynomial (m : ℕ) (p : Fin m → Fin 3) :
    MvPolynomial (Fin 3) ℝ :=
  ∏ j : Fin m, MvPolynomial.X (p j)

/-- Finite tensor expansion of the projection power, with all dependence on
the sphere point isolated in scalar coefficients. -/
theorem projectionPolynomial_pow_eq_word_sum (x : Ambient) (m : ℕ) :
    (projectionPolynomial x) ^ m =
      ∑ p : Fin m → Fin 3,
        MvPolynomial.C (∏ j : Fin m, x (p j)) *
          coordinateWordPolynomial m p := by
  unfold projectionPolynomial
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro p hp
  unfold coordinateWordPolynomial
  rw [Finset.prod_mul_distrib]
  rw [← map_prod]

theorem coordinateWordPolynomial_eval (m : ℕ) (p : Fin m → Fin 3)
    (u : Ambient) :
    MvPolynomial.eval (fun i => u i) (coordinateWordPolynomial m p) =
      ∏ j : Fin m, u (p j) := by
  simp [coordinateWordPolynomial]

/-- The coefficientwise surface integral of a projection power, represented
as a finite polynomial in the ambient variable. -/
noncomputable def integratedProjectionPolynomial (m : ℕ) :
    MvPolynomial (Fin 3) ℝ :=
  ∑ p : Fin m → Fin 3,
    MvPolynomial.C (sphereTensorMoment sigma m p) *
      coordinateWordPolynomial m p

theorem integratedProjectionPolynomial_eval (m : ℕ) (u : Ambient) :
    MvPolynomial.eval (fun i => u i) (integratedProjectionPolynomial m) =
      ∫ x : Sphere, (@Inner.inner ℝ Ambient _ u (x : Ambient)) ^ m ∂sigma := by
  have hpoint (x : Sphere) :
      (@Inner.inner ℝ Ambient _ u (x : Ambient)) ^ m =
        ∑ p : Fin m → Fin 3,
          sphereTensorFeature m p x *
            MvPolynomial.eval (fun i => u i) (coordinateWordPolynomial m p) := by
    rw [← projectionPolynomial_eval (x : Ambient) u,
      ← map_pow, projectionPolynomial_pow_eq_word_sum]
    simp only [map_sum, map_mul, MvPolynomial.eval_C,
      sphereTensorFeature]
  simp only [integratedProjectionPolynomial, map_sum, map_mul,
    MvPolynomial.eval_C]
  simp_rw [hpoint]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [integral_mul_const]
    rfl
  · intro p hp
    exact (integrable_sphereTensorFeature sigma m p).mul_const _

theorem radialSquare_eval_ambient (u : Ambient) :
    MvPolynomial.eval (fun i => u i) radialSquare =
      @Inner.inner ℝ Ambient _ u u := by
  simp [radialSquare, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_three, mul_comm]
  ring

/-- The finite coefficientwise integral is exactly a radial polynomial. -/
theorem integratedProjectionPolynomial_even (r : ℕ) :
    integratedProjectionPolynomial (2 * r) =
      MvPolynomial.C (1 / ((2 * r + 1 : ℕ) : ℝ)) * radialSquare ^ r := by
  apply MvPolynomial.funext
  intro v
  let u : Ambient := (EuclideanSpace.equiv (Fin 3) ℝ).symm v
  have hu (i : Fin 3) : u i = v i := by
    rfl
  have hv : v = fun i => u i := by
    funext i
    exact (hu i).symm
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  rw [integratedProjectionPolynomial_eval,
    ambient_projection_even_moment_inner]
  simp only [map_mul, MvPolynomial.eval_C, map_pow]
  rw [radialSquare_eval_ambient]
  ring

/-- The coefficientwise integral of an odd projection polynomial vanishes. -/
theorem integratedProjectionPolynomial_odd (r : ℕ) :
    integratedProjectionPolynomial (2 * r + 1) = 0 := by
  apply MvPolynomial.funext
  intro v
  let u : Ambient := (EuclideanSpace.equiv (Fin 3) ℝ).symm v
  have hv : v = fun i => u i := by
    funext i
    rfl
  conv_lhs => rw [hv]
  rw [integratedProjectionPolynomial_eval,
    ambient_projection_odd_moment]
  simp

/-- A finite string of coordinate derivatives, applied from right to left. -/
noncomputable def coordinateDerivatives : List (Fin 3) →
    MvPolynomial (Fin 3) ℝ → MvPolynomial (Fin 3) ℝ
  | [], p => p
  | i :: is, p => MvPolynomial.pderiv i (coordinateDerivatives is p)

theorem coordinateDerivatives_add (is : List (Fin 3))
    (p q : MvPolynomial (Fin 3) ℝ) :
    coordinateDerivatives is (p + q) =
      coordinateDerivatives is p + coordinateDerivatives is q := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      simp only [coordinateDerivatives, ih, map_add]

theorem coordinateDerivatives_C_mul (is : List (Fin 3)) (c : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) :
    coordinateDerivatives is (MvPolynomial.C c * p) =
      MvPolynomial.C c * coordinateDerivatives is p := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      simp only [coordinateDerivatives, ih, MvPolynomial.pderiv_C_mul]

theorem coordinateDerivatives_zero (is : List (Fin 3)) :
    coordinateDerivatives is (0 : MvPolynomial (Fin 3) ℝ) = 0 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [coordinateDerivatives, ih]

theorem coordinateDerivatives_sum (is : List (Fin 3))
    {ι : Type*} (S : Finset ι) (f : ι → MvPolynomial (Fin 3) ℝ) :
    coordinateDerivatives is (∑ i ∈ S, f i) =
      ∑ i ∈ S, coordinateDerivatives is (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [coordinateDerivatives_zero]
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        coordinateDerivatives_add, ih]

/-- Iterated derivatives of a projection power are given by the descending
factorial and the corresponding coordinate monomial. -/
theorem coordinateDerivatives_projection_pow (x : Ambient) (is : List (Fin 3))
    (q : ℕ) :
    coordinateDerivatives is ((projectionPolynomial x) ^ (q + is.length)) =
      MvPolynomial.C (((q + is.length).descFactorial is.length : ℕ) : ℝ) *
        MvPolynomial.C ((is.map (fun i => x i)).prod) *
        (projectionPolynomial x) ^ q := by
  induction is generalizing q with
  | nil => simp [coordinateDerivatives]
  | cons i is ih =>
      have he : q + (i :: is).length = (q + 1) + is.length := by simp; omega
      simp only [coordinateDerivatives]
      rw [he, ih (q + 1)]
      rw [mul_assoc, MvPolynomial.pderiv_C_mul,
        MvPolynomial.pderiv_C_mul]
      rw [projectionPolynomial_pderiv_pow]
      simp only [List.map_cons, List.prod_cons, List.length_cons,
        Nat.add_sub_cancel_right]
      rw [Nat.descFactorial_succ]
      have hs : q + 1 + is.length - is.length = q + 1 := by omega
      rw [hs]
      push_cast
      simp only [map_add, map_mul, map_natCast]
      simp
      ring

/-- Canonical coordinate list of a multivariable monomial exponent. -/
noncomputable def monomialCoordinateList (d : Fin 3 →₀ ℕ) : List (Fin 3) :=
  Finsupp.toMultiset d |>.toList

theorem monomialCoordinateList_length (d : Fin 3 →₀ ℕ) :
    (monomialCoordinateList d).length = d.sum fun _ e => e := by
  simp [monomialCoordinateList, Multiset.length_toList,
    Finsupp.card_toMultiset, Function.id_def]

theorem monomialCoordinateList_prod (d : Fin 3 →₀ ℕ) (x : Ambient) :
    ((monomialCoordinateList d).map (fun i => x i)).prod =
      d.prod (fun i e => (x i) ^ e) := by
  have hlist (s : Multiset (Fin 3)) :
      (s.toList.map (fun i => x i)).prod =
        (s.map (fun i => x i)).prod := by
    calc
      _ = ((s.toList.map (fun i => x i) : List ℝ) : Multiset ℝ).prod :=
        (Multiset.prod_coe _).symm
      _ = (Multiset.map (fun i => x i) (↑s.toList)).prod := by
        rw [Multiset.map_coe]
      _ = _ := by rw [Multiset.coe_toList]
  rw [monomialCoordinateList, hlist]
  induction d using Finsupp.induction with
  | zero => simp
  | single_add i e d hi he ih =>
      rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add, ih]
      rw [Finsupp.toMultiset_single, Multiset.map_nsmul,
        Multiset.map_singleton, Multiset.prod_nsmul, Multiset.prod_singleton]
      rw [Finsupp.prod_add_index' (fun i => pow_zero (x i))
        (fun i e₁ e₂ => pow_add (x i) e₁ e₂), Finsupp.prod_single_index]
      simp

/-- Monomial differential action on a projection power, now expressed using
multivariable polynomial evaluation. -/
theorem monomialDerivative_projection_pow (d : Fin 3 →₀ ℕ)
    (x : Ambient) (q : ℕ) :
    coordinateDerivatives (monomialCoordinateList d)
      ((projectionPolynomial x) ^ (q + d.sum fun _ e => e)) =
      MvPolynomial.C ((((q + d.sum fun _ e => e).descFactorial
        (d.sum fun _ e => e) : ℕ) : ℝ)) *
      MvPolynomial.C (MvPolynomial.eval (fun i => x i)
        (MvPolynomial.monomial d (1 : ℝ))) *
      (projectionPolynomial x) ^ q := by
  rw [← monomialCoordinateList_length d,
    coordinateDerivatives_projection_pow]
  rw [monomialCoordinateList_prod, MvPolynomial.eval_monomial]
  simp

/-- Substitute commuting coordinate partial derivatives for the variables of
a polynomial. This finite-support definition is sufficient for homogeneous
harmonic inputs. -/
noncomputable def polynomialDifferentialOperator
    (H p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ d ∈ H.support, MvPolynomial.C (MvPolynomial.coeff d H) *
    coordinateDerivatives (monomialCoordinateList d) p

theorem polynomialDifferentialOperator_C_mul
    (H p : MvPolynomial (Fin 3) ℝ) (c : ℝ) :
    polynomialDifferentialOperator H (MvPolynomial.C c * p) =
      MvPolynomial.C c * polynomialDifferentialOperator H p := by
  unfold polynomialDifferentialOperator
  simp_rw [coordinateDerivatives_C_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem polynomialDifferentialOperator_zero_input
    (H : MvPolynomial (Fin 3) ℝ) :
    polynomialDifferentialOperator H 0 = 0 := by
  unfold polynomialDifferentialOperator
  simp [coordinateDerivatives_zero]

theorem polynomialDifferentialOperator_sum
    (H : MvPolynomial (Fin 3) ℝ) {ι : Type*}
    (S : Finset ι) (f : ι → MvPolynomial (Fin 3) ℝ) :
    polynomialDifferentialOperator H (∑ i ∈ S, f i) =
      ∑ i ∈ S, polynomialDifferentialOperator H (f i) := by
  classical
  unfold polynomialDifferentialOperator
  simp_rw [coordinateDerivatives_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The constant-coefficient polynomial differential operator commutes with
the sphere integral of each projection power. All interchanges here are
finite tensor-word sums. -/
theorem polynomialDifferentialOperator_integratedProjectionPolynomial
    (H : MvPolynomial (Fin 3) ℝ) (m : ℕ) (u : Ambient) :
    MvPolynomial.eval (fun i => u i)
      (polynomialDifferentialOperator H (integratedProjectionPolynomial m)) =
      ∫ x : Sphere,
        MvPolynomial.eval (fun i => u i)
          (polynomialDifferentialOperator H
            ((projectionPolynomial (x : Ambient)) ^ m)) ∂sigma := by
  have hleft :
      MvPolynomial.eval (fun i => u i)
        (polynomialDifferentialOperator H (integratedProjectionPolynomial m)) =
      ∑ p : Fin m → Fin 3,
        sphereTensorMoment sigma m p *
          MvPolynomial.eval (fun i => u i)
            (polynomialDifferentialOperator H (coordinateWordPolynomial m p)) := by
    unfold integratedProjectionPolynomial
    rw [polynomialDifferentialOperator_sum]
    simp_rw [polynomialDifferentialOperator_C_mul]
    simp only [map_sum, map_mul, MvPolynomial.eval_C]
  have hpoint (x : Sphere) :
      MvPolynomial.eval (fun i => u i)
        (polynomialDifferentialOperator H
          ((projectionPolynomial (x : Ambient)) ^ m)) =
      ∑ p : Fin m → Fin 3,
        sphereTensorFeature m p x *
          MvPolynomial.eval (fun i => u i)
            (polynomialDifferentialOperator H (coordinateWordPolynomial m p)) := by
    rw [projectionPolynomial_pow_eq_word_sum,
      polynomialDifferentialOperator_sum]
    simp_rw [polynomialDifferentialOperator_C_mul]
    simp only [map_sum, map_mul, MvPolynomial.eval_C, sphereTensorFeature]
  rw [hleft]
  simp_rw [hpoint]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [integral_mul_const]
    rfl
  · intro p hp
    exact (integrable_sphereTensorFeature sigma m p).mul_const _

/-- A homogeneous polynomial differential operator acts on a projection power
by evaluation of that polynomial at the fixed vector. -/
theorem polynomialDifferentialOperator_projection_pow
    {H : MvPolynomial (Fin 3) ℝ} {ℓ : ℕ}
    (hH : H.IsHomogeneous ℓ) (x : Ambient) (q : ℕ) :
    polynomialDifferentialOperator H
      ((projectionPolynomial x) ^ (q + ℓ)) =
      MvPolynomial.C ((((q + ℓ).descFactorial ℓ : ℕ) : ℝ)) *
      MvPolynomial.C (MvPolynomial.eval (fun i => x i) H) *
      (projectionPolynomial x) ^ q := by
  have hdegree (d : Fin 3 →₀ ℕ) (hd : d ∈ H.support) :
      d.sum (fun _ e => e) = ℓ := by
    have hc : MvPolynomial.coeff d H ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have hw := hH hc
    change Finsupp.weight (fun _ : Fin 3 => (1 : ℕ)) d = ℓ at hw
    rw [← Finsupp.degree_eq_weight_one] at hw
    simpa [Finsupp.degree, Finsupp.sum] using hw
  have heval : MvPolynomial.eval (fun i => x i) H =
      ∑ d ∈ H.support, MvPolynomial.coeff d H *
        MvPolynomial.eval (fun i => x i)
          (MvPolynomial.monomial d (1 : ℝ)) := by
    conv_lhs => rw [H.as_sum]
    simp only [map_sum, MvPolynomial.eval_monomial, one_mul]
  unfold polynomialDifferentialOperator
  calc
    _ = ∑ d ∈ H.support,
        MvPolynomial.C ((((q + ℓ).descFactorial ℓ : ℕ) : ℝ)) *
        MvPolynomial.C (MvPolynomial.coeff d H *
          MvPolynomial.eval (fun i => x i)
            (MvPolynomial.monomial d (1 : ℝ))) *
        (projectionPolynomial x) ^ q := by
          apply Finset.sum_congr rfl
          intro d hd
          have hder := monomialDerivative_projection_pow d x q
          rw [hdegree d hd] at hder
          rw [hder]
          simp only [map_mul]
          ring
    _ = _ := by
      rw [heval, map_sum]
      rw [Finset.mul_sum]
      simp_rw [Finset.sum_mul]

/-- Pointwise form of the homogeneous differential action, suitable for
integration over the sphere. -/
theorem polynomialDifferentialOperator_projection_pow_eval
    {H : MvPolynomial (Fin 3) ℝ} {ℓ : ℕ}
    (hH : H.IsHomogeneous ℓ) (x u : Ambient) (q : ℕ) :
    MvPolynomial.eval (fun i => u i)
      (polynomialDifferentialOperator H
        ((projectionPolynomial x) ^ (q + ℓ))) =
      (((q + ℓ).descFactorial ℓ : ℕ) : ℝ) *
        MvPolynomial.eval (fun i => x i) H *
        (@Inner.inner ℝ Ambient _ u x) ^ q := by
  rw [polynomialDifferentialOperator_projection_pow hH]
  simp only [map_mul, MvPolynomial.eval_C, map_pow,
    projectionPolynomial_eval]

/-- Exact bridge from a harmonic weighted projection moment to the radial
polynomial differential action. The commutation with integration has already
been proved by finite tensor-word expansion. -/
theorem polynomialDifferentialOperator_radial_moment
    {H : MvPolynomial (Fin 3) ℝ} {ℓ : ℕ}
    (hH : H.IsHomogeneous ℓ) (r q : ℕ) (hq : q + ℓ = 2 * r)
    (u : Ambient) :
    (1 / ((2 * r + 1 : ℕ) : ℝ)) *
        MvPolynomial.eval (fun i => u i)
          (polynomialDifferentialOperator H (radialSquare ^ r)) =
      (((2 * r).descFactorial ℓ : ℕ) : ℝ) *
        (∫ x : Sphere,
          MvPolynomial.eval (fun i => (x : Ambient) i) H *
            (@Inner.inner ℝ Ambient _ u (x : Ambient)) ^ q ∂sigma) := by
  have hcomm := polynomialDifferentialOperator_integratedProjectionPolynomial H (2 * r) u
  rw [integratedProjectionPolynomial_even r,
    polynomialDifferentialOperator_C_mul] at hcomm
  simp only [map_mul, MvPolynomial.eval_C] at hcomm
  have hpoint (x : Sphere) :
      MvPolynomial.eval (fun i => u i)
        (polynomialDifferentialOperator H
          ((projectionPolynomial (x : Ambient)) ^ (2 * r))) =
      (((2 * r).descFactorial ℓ : ℕ) : ℝ) *
          MvPolynomial.eval (fun i => (x : Ambient) i) H *
          (@Inner.inner ℝ Ambient _ u (x : Ambient)) ^ q := by
    have h := polynomialDifferentialOperator_projection_pow_eval hH
      (x : Ambient) u q
    rw [hq] at h
    exact h
  simp_rw [hpoint] at hcomm
  simp_rw [mul_assoc] at hcomm
  rw [integral_const_mul] at hcomm
  exact hcomm

/-- Every homogeneous polynomial has zero weighted projection moment when
the total projection degree is odd. This includes all odd harmonic degrees
against the even moment kernel. -/
theorem homogeneous_odd_projection_moment_zero
    {H : MvPolynomial (Fin 3) ℝ} {ℓ : ℕ}
    (hH : H.IsHomogeneous ℓ) (q r : ℕ)
    (hq : q + ℓ = 2 * r + 1) (u : Ambient) :
    (∫ x : Sphere,
      MvPolynomial.eval (fun i => (x : Ambient) i) H *
        (@Inner.inner ℝ Ambient _ u (x : Ambient)) ^ q ∂sigma) = 0 := by
  have hcomm := polynomialDifferentialOperator_integratedProjectionPolynomial
    H (2 * r + 1) u
  rw [integratedProjectionPolynomial_odd r,
    polynomialDifferentialOperator_zero_input] at hcomm
  simp only [map_zero] at hcomm
  have hpoint (x : Sphere) :
      MvPolynomial.eval (fun i => u i)
        (polynomialDifferentialOperator H
          ((projectionPolynomial (x : Ambient)) ^ (2 * r + 1))) =
      (((2 * r + 1).descFactorial ℓ : ℕ) : ℝ) *
        MvPolynomial.eval (fun i => (x : Ambient) i) H *
          (@Inner.inner ℝ Ambient _ u (x : Ambient)) ^ q := by
    have h := polynomialDifferentialOperator_projection_pow_eval hH
      (x : Ambient) u q
    rw [hq] at h
    exact h
  simp_rw [hpoint, mul_assoc] at hcomm
  rw [integral_const_mul] at hcomm
  have hfall : (((2 * r + 1).descFactorial ℓ : ℕ) : ℝ) ≠ 0 := by
    have hn : (2 * r + 1).descFactorial ℓ ≠ 0 := by
      simp only [ne_eq, Nat.descFactorial_eq_zero_iff_lt]
      omega
    exact_mod_cast hn
  exact (mul_eq_zero.mp hcomm.symm).resolve_left hfall

/-- Every even zonal coefficient against `t^(2n)` is a finite rational sum. -/
theorem even_projection_polynomial_integral (u : Sphere) (n : ℕ)
    (S : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x : Sphere,
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) *
        (∑ k ∈ S, a k *
          (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * k))
      ∂sigma) =
      ∑ k ∈ S, a k / ((2 * (n + k) + 1 : ℕ) : ℝ) := by
  have hpoint (x : Sphere) :
      (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) *
        (∑ k ∈ S, a k *
          (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * k)) =
      ∑ k ∈ S, a k *
        (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * (n + k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = a k *
          ((@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * n) *
            (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * k)) := by ring
      _ = _ := by
        rw [← pow_add]
        have he : 2 * n + 2 * k = 2 * (n + k) := by omega
        rw [he]
  simp_rw [hpoint]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_const_mul, sphere_projection_even_moment]
    ring
  · intro k hk
    have hc : Continuous (fun x : Sphere =>
        a k * (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)) ^ (2 * (n + k))) := by
      fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Concrete analytic target for the even-moment test. This bounds the actual
spectral norm by its positive cubature gap, rather than postulating a WCE bound. -/
def EvenMomentSpectralBound (Y : HarmonicBasis) (s : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 0 < n → ∀ X : Fin n → Sphere,
    Summable (sobolevNormTerm Y s (centeredEvenMomentTest X n)) ∧
    sobolevNormSq Y s (centeredEvenMomentTest X n) ≤
      A * (n : ℝ) ^ (s - 1) * quadratureError X (centeredEvenMomentTest X n)

/-- The concrete spectral estimate implies the exact universal optimality
statement for the specified unit ball and quadrature error. -/
theorem sobolev_optimality_of_even_moment_spectral_bound
    (Y : HarmonicBasis) {s : ℝ} (_hs1 : 1 < s)
    (hemb : SobolevEmbedding Y s)
    (hmoment : EvenMomentSpectralBound Y s) : SobolevOptimality Y s := by
  obtain ⟨A, hA, hnorm⟩ := hmoment
  let c : ℝ := 1 / Real.sqrt (2 * A)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro n hn X _hX
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  let g := centeredEvenMomentTest X n
  let E := quadratureError X g
  have hE : 1 / (2 * (n : ℝ)) ≤ E := quadratureError_centeredEvenMomentTest_ge hn X
  have hEpos : 0 < E := lt_of_lt_of_le (by positivity) hE
  let q := A * (n : ℝ) ^ (s - 1) * E
  have hq : 0 < q := by dsimp [q]; positivity
  have hqsqrt : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  let f : C(Sphere, ℝ) := (Real.sqrt q)⁻¹ • g
  have hf : SobolevUnitBall Y s f := by
    have hsum := (hnorm n hn X).1
    have hle := (hnorm n hn X).2
    constructor
    · exact sobolevNormTerm_smul_summable Y s _ g hsum
    · change sobolevNormSq Y s f ≤ 1
      rw [show f = (Real.sqrt q)⁻¹ • g by rfl,
        sobolevNormSq_smul]
      change sobolevNormSq Y s g ≤ q at hle
      have hsq : (Real.sqrt q) ^ (2 : ℕ) = q := Real.sq_sqrt hq.le
      have hinv : ((Real.sqrt q)⁻¹) ^ (2 : ℕ) = q⁻¹ := by
        rw [inv_pow, hsq]
      rw [hinv]
      calc
        q⁻¹ * sobolevNormSq Y s g ≤ q⁻¹ * q :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hq.le)
        _ = 1 := inv_mul_cancel₀ hq.ne'
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have htest : E / Real.sqrt q ≤ sobolevWCE Y s X := by
    have h := quadratureError_abs_le_sobolevWCE Y s X hemb f hf
    rw [show f = (Real.sqrt q)⁻¹ • g by rfl,
      quadratureError_smul_lower, abs_of_pos (mul_pos (inv_pos.mpr hqsqrt) hEpos)] at h
    simpa [E, div_eq_mul_inv, mul_comm] using h
  have hpow : (n : ℝ) ^ (s - 1) * (n : ℝ) ^ (-s) = (n : ℝ)⁻¹ := by
    rw [← Real.rpow_add hnreal]
    have he : s - 1 + -s = (-1 : ℝ) := by ring
    rw [he, Real.rpow_neg_one]
  have htargetSq : (c * (n : ℝ) ^ (-s / 2)) ^ (2 : ℕ) * q ≤ E ^ (2 : ℕ) := by
    have hcSq : c ^ (2 : ℕ) = 1 / (2 * A) := by
      dsimp [c]
      rw [div_pow, one_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * A)]
    have hrpowSq : ((n : ℝ) ^ (-s / 2)) ^ (2 : ℕ) =
        (n : ℝ) ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnreal.le]
      congr 1
      ring
    rw [mul_pow, hcSq, hrpowSq]
    have heq : (1 / (2 * A) * (n : ℝ) ^ (-s)) * q = E / (2 * (n : ℝ)) := by
      dsimp [q]
      calc
        _ = (1 / (2 * A) * A) *
            ((n : ℝ) ^ (s - 1) * (n : ℝ) ^ (-s)) * E := by ring
        _ = E / (2 * (n : ℝ)) := by
          rw [hpow]
          field_simp
          ring
    rw [heq]
    have hh := mul_le_mul_of_nonneg_right hE hEpos.le
    convert hh using 1 <;> ring
  have htarget : c * (n : ℝ) ^ (-s / 2) ≤ E / Real.sqrt q := by
    have hleft : 0 ≤ c * (n : ℝ) ^ (-s / 2) := by positivity
    have hright : 0 ≤ E / Real.sqrt q := by positivity
    have hrewrite : (E / Real.sqrt q) ^ (2 : ℕ) = E ^ (2 : ℕ) / q := by
      rw [div_pow, Real.sq_sqrt hq.le]
    apply (sq_le_sq₀ hleft hright).mp
    rw [hrewrite]
    exact (le_div_iff₀ hq).2 (by nlinarith [htargetSq])
  exact htarget.trans htest

end BEMOC.Definitive
