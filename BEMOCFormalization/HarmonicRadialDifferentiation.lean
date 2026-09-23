import BEMOCFormalization.SobolevLowerBound

/-! Algebraic differentiation of radial powers by harmonic polynomials. -/

open scoped BigOperators

namespace BEMOC.Definitive

/-- Coordinate partial derivatives of multivariable real polynomials commute. -/
theorem polynomial_pderiv_comm (i j : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
      simp only [MvPolynomial.pderiv_mul, map_add]
      simp only [MvPolynomial.pderiv_X]
      rw [hp]
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        simp [Pi.single_apply]

/-- The iterated derivative depends only on the multiset of coordinates. -/
theorem coordinateDerivatives_perm {is js : List (Fin 3)}
    (h : is.Perm js) (p : MvPolynomial (Fin 3) ℝ) :
    coordinateDerivatives is p = coordinateDerivatives js p := by
  induction h with
  | nil => rfl
  | @cons i is js h ih =>
      simpa only [coordinateDerivatives] using
        congrArg (MvPolynomial.pderiv i) ih
  | @swap i j is =>
      simp only [coordinateDerivatives]
      exact (polynomial_pderiv_comm i j (coordinateDerivatives is p)).symm
  | @trans is js ks h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- The Weyl commutator for a coordinate monomial and an iterated derivative. -/
theorem coordinateDerivatives_X_mul (is : List (Fin 3)) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    coordinateDerivatives is (MvPolynomial.X i * p) =
      MvPolynomial.X i * coordinateDerivatives is p +
        (is.count i : MvPolynomial (Fin 3) ℝ) *
          coordinateDerivatives (is.erase i) p := by
  induction is with
  | nil => simp [coordinateDerivatives]
  | cons j js ih =>
      rw [coordinateDerivatives, ih]
      simp only [map_add, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_X, coordinateDerivatives]
      have hc : (MvPolynomial.pderiv j)
          ((js.count i : ℕ) : MvPolynomial (Fin 3) ℝ) = 0 := by
        change (MvPolynomial.pderiv j)
          (MvPolynomial.C ((js.count i : ℕ) : ℝ)) = 0
        simp
      rw [hc]
      simp only [zero_mul, zero_add]
      by_cases hji : j = i
      · subst j
        simp only [List.count_cons_self, List.erase_cons_head,
          Pi.single_eq_same]
        by_cases hi : i ∈ js
        · have hperm : List.Perm (i :: js.erase i) js :=
            (List.perm_cons_erase hi).symm
          have hder := coordinateDerivatives_perm hperm p
          change (MvPolynomial.pderiv i)
            (coordinateDerivatives (js.erase i) p) =
              coordinateDerivatives js p at hder
          rw [hder]
          push_cast
          ring
        · have hcount : js.count i = 0 := List.count_eq_zero.mpr hi
          simp [hcount, add_comm]
      · simp [hji]
        left
        rfl

/-- Coordinate multiplicity in the canonical list equals the monomial exponent. -/
theorem monomialCoordinateList_count (d : Fin 3 →₀ ℕ) (i : Fin 3) :
    (monomialCoordinateList d).count i = d i := by
  rw [← Multiset.coe_count]
  simp only [monomialCoordinateList, Multiset.coe_toList,
    Finsupp.count_toMultiset]

/-- Erasing one present coordinate represents subtraction of one monomial exponent. -/
theorem monomialCoordinateList_erase_perm
    {d : Fin 3 →₀ ℕ} {i : Fin 3} (hi : d i ≠ 0) :
    List.Perm ((monomialCoordinateList d).erase i)
      (monomialCoordinateList (d - Finsupp.single i 1)) := by
  classical
  have hms : Finsupp.toMultiset d =
      {i} + Finsupp.toMultiset (d - Finsupp.single i 1) := by
    calc
      Finsupp.toMultiset d =
          Finsupp.toMultiset
            ((d - Finsupp.single i 1) + Finsupp.single i 1) := by
              rw [Finsupp.sub_add_single_one_cancel hi]
      _ = Finsupp.toMultiset (d - Finsupp.single i 1) +
            Finsupp.toMultiset (Finsupp.single i 1) :=
        Finsupp.toMultiset_add _ _
      _ = {i} + Finsupp.toMultiset (d - Finsupp.single i 1) := by
        rw [Finsupp.toMultiset_single]
        simp [Multiset.add_comm]
  have hperm : List.Perm (monomialCoordinateList d)
      (i :: monomialCoordinateList (d - Finsupp.single i 1)) := by
    apply Multiset.coe_eq_coe.mp
    simpa [monomialCoordinateList, ← Multiset.cons_coe] using hms
  have himem : i ∈ monomialCoordinateList d := by
    have hc := monomialCoordinateList_count d i
    exact List.count_pos_iff.mp (by omega : 0 < (monomialCoordinateList d).count i)
  have hpermerase : List.Perm
      (i :: (monomialCoordinateList d).erase i)
      (i :: monomialCoordinateList (d - Finsupp.single i 1)) :=
    (List.perm_cons_erase himem).symm.trans hperm
  exact List.Perm.cons_inv hpermerase

/-- The polynomial differential action is linear in its operator polynomial. -/
theorem polynomialDifferentialOperator_add (H K p : MvPolynomial (Fin 3) ℝ) :
    polynomialDifferentialOperator (H + K) p =
      polynomialDifferentialOperator H p + polynomialDifferentialOperator K p := by
  classical
  unfold polynomialDifferentialOperator
  change (H + K).sum (fun d a => MvPolynomial.C a *
      coordinateDerivatives (monomialCoordinateList d) p) =
    H.sum (fun d a => MvPolynomial.C a *
      coordinateDerivatives (monomialCoordinateList d) p) +
    K.sum (fun d a => MvPolynomial.C a *
      coordinateDerivatives (monomialCoordinateList d) p)
  exact Finsupp.sum_add_index'
    (by intro d; simp)
    (by intro d a b; simp [map_add, add_mul])

/-- Differential action of one monomial. -/
theorem polynomialDifferentialOperator_monomial
    (d : Fin 3 →₀ ℕ) (a : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    polynomialDifferentialOperator (MvPolynomial.monomial d a) p =
      MvPolynomial.C a * coordinateDerivatives (monomialCoordinateList d) p := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [polynomialDifferentialOperator]
  · simp [polynomialDifferentialOperator, MvPolynomial.support_monomial, ha,
      MvPolynomial.coeff_monomial]

/-- First Weyl commutator for a monomial differential operator. -/
theorem polynomialDifferentialOperator_monomial_X_mul
    (d : Fin 3 →₀ ℕ) (a : ℝ) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    polynomialDifferentialOperator (MvPolynomial.monomial d a)
        (MvPolynomial.X i * p) =
      MvPolynomial.X i *
        polynomialDifferentialOperator (MvPolynomial.monomial d a) p +
      polynomialDifferentialOperator
        (MvPolynomial.pderiv i (MvPolynomial.monomial d a)) p := by
  rw [polynomialDifferentialOperator_monomial,
    polynomialDifferentialOperator_monomial,
    MvPolynomial.pderiv_monomial,
    polynomialDifferentialOperator_monomial,
    coordinateDerivatives_X_mul,
    monomialCoordinateList_count]
  by_cases hi : d i = 0
  · simp [hi]
    ring
  · rw [coordinateDerivatives_perm (monomialCoordinateList_erase_perm hi)]
    simp only [map_mul, map_natCast]
    ring

/-- Constant-coefficient differential operators satisfy the first Weyl
commutator with multiplication by a coordinate. -/
theorem polynomialDifferentialOperator_X_mul
    (H : MvPolynomial (Fin 3) ℝ) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    polynomialDifferentialOperator H (MvPolynomial.X i * p) =
      MvPolynomial.X i * polynomialDifferentialOperator H p +
        polynomialDifferentialOperator (MvPolynomial.pderiv i H) p := by
  induction H using MvPolynomial.induction_on' with
  | monomial d a =>
      exact polynomialDifferentialOperator_monomial_X_mul d a i p
  | add H K hH hK =>
      rw [polynomialDifferentialOperator_add,
        polynomialDifferentialOperator_add, map_add,
        polynomialDifferentialOperator_add, hH, hK]
      ring

/-- Constant-coefficient polynomial differential operators are additive
in the polynomial being differentiated. -/
theorem polynomialDifferentialOperator_add_right
    (H p q : MvPolynomial (Fin 3) ℝ) :
    polynomialDifferentialOperator H (p + q) =
      polynomialDifferentialOperator H p +
        polynomialDifferentialOperator H q := by
  classical
  unfold polynomialDifferentialOperator
  simp_rw [coordinateDerivatives_add, mul_add, Finset.sum_add_distrib]

/-- Commuting a polynomial differential operator through one squared
coordinate produces its first and second operator derivatives. -/
theorem polynomialDifferentialOperator_X_sq_mul
    (H p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    polynomialDifferentialOperator H (MvPolynomial.X i ^ 2 * p) =
      MvPolynomial.X i ^ 2 * polynomialDifferentialOperator H p +
        2 * MvPolynomial.X i *
          polynomialDifferentialOperator (MvPolynomial.pderiv i H) p +
        polynomialDifferentialOperator
          (MvPolynomial.pderiv i (MvPolynomial.pderiv i H)) p := by
  rw [show MvPolynomial.X i ^ 2 * p =
      MvPolynomial.X i * (MvPolynomial.X i * p) by ring,
    polynomialDifferentialOperator_X_mul,
    polynomialDifferentialOperator_X_mul,
    polynomialDifferentialOperator_X_mul]
  ring

/-- The radial Weyl commutator; harmonicity removes its Laplacian term. -/
theorem polynomialDifferentialOperator_radialSquare_mul
    (H p : MvPolynomial (Fin 3) ℝ) :
    polynomialDifferentialOperator H (radialSquare * p) =
      radialSquare * polynomialDifferentialOperator H p +
        2 * (∑ i : Fin 3,
          MvPolynomial.X i *
            polynomialDifferentialOperator (MvPolynomial.pderiv i H) p) +
        polynomialDifferentialOperator (polynomialLaplacian H) p := by
  simp only [radialSquare, polynomialLaplacian, Fin.sum_univ_three,
    add_mul, polynomialDifferentialOperator_add_right,
    polynomialDifferentialOperator_add,
    polynomialDifferentialOperator_X_sq_mul]
  ring

/-- The polynomial Laplacian commutes with each coordinate partial. -/
theorem polynomialLaplacian_pderiv (H : MvPolynomial (Fin 3) ℝ)
    (i : Fin 3) :
    polynomialLaplacian (MvPolynomial.pderiv i H) =
      MvPolynomial.pderiv i (polynomialLaplacian H) := by
  unfold polynomialLaplacian
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (MvPolynomial.pderiv j) ((MvPolynomial.pderiv j)
        ((MvPolynomial.pderiv i) H)) =
      (MvPolynomial.pderiv j) ((MvPolynomial.pderiv i)
        ((MvPolynomial.pderiv j) H)) := by
          rw [polynomial_pderiv_comm j i H]
    _ = (MvPolynomial.pderiv i) ((MvPolynomial.pderiv j)
        ((MvPolynomial.pderiv j) H)) :=
          polynomial_pderiv_comm j i ((MvPolynomial.pderiv j) H)

/-- Every coordinate partial of a homogeneous harmonic polynomial is again
homogeneous and harmonic. -/
theorem harmonic_pderiv {H : MvPolynomial (Fin 3) ℝ} {ℓ : ℕ}
    (hH : H ∈ harmonicPolynomialSubmodule ℓ) (i : Fin 3) :
    MvPolynomial.pderiv i H ∈ harmonicPolynomialSubmodule (ℓ - 1) := by
  obtain ⟨hhom, hlap⟩ := mem_harmonicPolynomialSubmodule.mp hH
  apply mem_harmonicPolynomialSubmodule.mpr
  constructor
  · exact hhom.pderiv
  · rw [polynomialLaplacian_pderiv, hlap]
    simp

/-- A constant polynomial is multiplication by that constant as a
differential operator. -/
theorem polynomialDifferentialOperator_C (c : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) :
    polynomialDifferentialOperator (MvPolynomial.C c) p =
      MvPolynomial.C c * p := by
  rw [MvPolynomial.C_apply,
    polynomialDifferentialOperator_monomial]
  simp [monomialCoordinateList, coordinateDerivatives]

/-- A nonempty string of coordinate derivatives kills the constant one. -/
theorem coordinateDerivatives_one_of_ne_nil
    {is : List (Fin 3)} (his : is ≠ []) :
    coordinateDerivatives is (1 : MvPolynomial (Fin 3) ℝ) = 0 := by
  induction is with
  | nil => exact (his rfl).elim
  | cons i is ih =>
      by_cases he : is = []
      · subst is
        simp [coordinateDerivatives]
      · simp [coordinateDerivatives, ih he]

/-- A positive-degree homogeneous differential operator kills constants. -/
theorem polynomialDifferentialOperator_one_of_homogeneous_pos
    {H : MvPolynomial (Fin 3) ℝ} {ℓ : ℕ}
    (hhom : H.IsHomogeneous ℓ) (hℓ : 0 < ℓ) :
    polynomialDifferentialOperator H 1 = 0 := by
  classical
  unfold polynomialDifferentialOperator
  apply Finset.sum_eq_zero
  intro d hd
  have hc : MvPolynomial.coeff d H ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hw := hhom hc
  change Finsupp.weight (fun _ : Fin 3 => (1 : ℕ)) d = ℓ at hw
  rw [← Finsupp.degree_eq_weight_one] at hw
  have hlen : (monomialCoordinateList d).length = ℓ := by
    rw [monomialCoordinateList_length]
    simpa [Finsupp.degree, Finsupp.sum] using hw
  have hne : monomialCoordinateList d ≠ [] := by
    intro he
    simp [he] at hlen
    omega
  rw [coordinateDerivatives_one_of_ne_nil hne, mul_zero]

/-- Pascal's identity for descending factorials, including the vanishing
regime when the derivative order exceeds the polynomial degree. -/
theorem descFactorial_succ_pascal (a ℓ : ℕ) :
    (a + 1).descFactorial ℓ =
      a.descFactorial ℓ + ℓ * a.descFactorial (ℓ - 1) := by
  cases ℓ with
  | zero => simp
  | succ k =>
      rw [Nat.succ_descFactorial_succ, Nat.descFactorial_succ]
      simp only [Nat.add_sub_cancel]
      by_cases hka : k ≤ a
      · have he : a - k + (k + 1) = a + 1 := by omega
        rw [← add_mul, he]
      · have hzero : a.descFactorial k = 0 :=
          Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        simp [hzero]

/-- The zero polynomial acts by the zero differential operator. -/
theorem polynomialDifferentialOperator_zero
    (p : MvPolynomial (Fin 3) ℝ) :
    polynomialDifferentialOperator 0 p = 0 := by
  simp [polynomialDifferentialOperator]

/-- Hobson's harmonic radial differentiation identity, including the
vanishing regime above the radial polynomial's degree. -/
theorem harmonic_radial_differentiation (a : ℕ) :
    ∀ (ℓ : ℕ) (H : MvPolynomial (Fin 3) ℝ),
      H ∈ harmonicPolynomialSubmodule ℓ →
      polynomialDifferentialOperator H (radialSquare ^ a) =
        MvPolynomial.C (((2 ^ ℓ * a.descFactorial ℓ : ℕ) : ℝ)) *
          radialSquare ^ (a - ℓ) * H := by
  induction a with
  | zero =>
      intro ℓ H hH
      obtain ⟨hhom, hlap⟩ := mem_harmonicPolynomialSubmodule.mp hH
      cases ℓ with
      | zero =>
          rw [homogeneous_zero_eq_constant hhom,
            polynomialDifferentialOperator_C]
          simp
      | succ k =>
          have hzero := polynomialDifferentialOperator_one_of_homogeneous_pos
            hhom (by omega : 0 < k + 1)
          simpa [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : 0 < k + 1)]
            using hzero
  | succ a ih =>
      intro ℓ H hH
      obtain ⟨hhom, hlap⟩ := mem_harmonicPolynomialSubmodule.mp hH
      cases ℓ with
      | zero =>
          rw [homogeneous_zero_eq_constant hhom,
            polynomialDifferentialOperator_C]
          simp
          ring
      | succ k =>
          have hder (i : Fin 3) :
              MvPolynomial.pderiv i H ∈ harmonicPolynomialSubmodule k := by
            simpa using harmonic_pderiv hH i
          have hsum :
              (∑ i : Fin 3,
                MvPolynomial.X i *
                  polynomialDifferentialOperator (MvPolynomial.pderiv i H)
                    (radialSquare ^ a)) =
                MvPolynomial.C (((2 ^ k * a.descFactorial k : ℕ) : ℝ)) *
                  radialSquare ^ (a - k) *
                    (∑ i : Fin 3,
                      MvPolynomial.X i * MvPolynomial.pderiv i H) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [ih k (MvPolynomial.pderiv i H) (hder i)]
            ring
          have hEuler :
              (∑ i : Fin 3,
                MvPolynomial.X i * MvPolynomial.pderiv i H) =
                MvPolynomial.C ((k + 1 : ℕ) : ℝ) * H := by
            have he := hhom.sum_X_mul_pderiv
            simpa [nsmul_eq_mul, MvPolynomial.smul_eq_C_mul] using he
          have hcomm := polynomialDifferentialOperator_radialSquare_mul H
            (radialSquare ^ a)
          rw [hlap, polynomialDifferentialOperator_zero, add_zero,
            hsum, hEuler, ih (k + 1) H hH] at hcomm
          rw [show radialSquare ^ (a + 1) =
              radialSquare * radialSquare ^ a by ring]
          rw [hcomm]
          by_cases hk : k < a
          · have hexp₁ : a - (k + 1) + 1 = a + 1 - (k + 1) := by omega
            have hexp₂ : a - k = a + 1 - (k + 1) := by omega
            have hpow : radialSquare * radialSquare ^ (a - (k + 1)) =
                radialSquare ^ (a + 1 - (k + 1)) := by
              rw [← pow_succ' radialSquare (a - (k + 1)), hexp₁]
            have hcoef : 2 ^ (k + 1) * a.descFactorial (k + 1) +
                2 * 2 ^ k * a.descFactorial k * (k + 1) =
                2 ^ (k + 1) * (a + 1).descFactorial (k + 1) := by
              rw [descFactorial_succ_pascal]
              simp only [Nat.add_sub_cancel]
              ring
            have hmul : radialSquare *
                (MvPolynomial.C (((2 ^ (k + 1) * a.descFactorial (k + 1) : ℕ) : ℝ)) *
                  radialSquare ^ (a - (k + 1)) * H) =
                MvPolynomial.C (((2 ^ (k + 1) * a.descFactorial (k + 1) : ℕ) : ℝ)) *
                  radialSquare ^ (a + 1 - (k + 1)) * H := by
              calc
                _ = MvPolynomial.C (((2 ^ (k + 1) * a.descFactorial (k + 1) : ℕ) : ℝ)) *
                      (radialSquare * radialSquare ^ (a - (k + 1))) * H := by ring
                _ = _ := by rw [hpow]
            calc
              _ = MvPolynomial.C (((2 ^ (k + 1) * a.descFactorial (k + 1) +
                    2 * 2 ^ k * a.descFactorial k * (k + 1) : ℕ) : ℝ)) *
                    radialSquare ^ (a + 1 - (k + 1)) * H := by
                  rw [hmul, hexp₂]
                  simp only [map_add, map_mul, map_natCast]
                  push_cast
                  ring
              _ = _ := by rw [hcoef]
          · by_cases heq : k = a
            · subst k
              have hzero : a.descFactorial (a + 1) = 0 :=
                Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
              have hcoef : 2 * 2 ^ a * a.descFactorial a * (a + 1) =
                  2 ^ (a + 1) * (a + 1).descFactorial (a + 1) := by
                rw [Nat.succ_descFactorial_succ]
                ring
              simp only [hzero, mul_zero, Nat.cast_zero, map_zero, zero_mul,
                zero_add, Nat.sub_self, pow_zero, one_mul]
              rw [← hcoef]
              push_cast
              simp only [map_add, map_mul, map_natCast]
              norm_num
              have htwo : (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 3) ℝ) = 2 := by
                simpa using (MvPolynomial.C_eq_coe_nat (σ := Fin 3) (R := ℝ) 2)
              rw [htwo]
              ring
            · have hak : a < k := by omega
              have hzero₁ : a.descFactorial k = 0 :=
                Nat.descFactorial_eq_zero_iff_lt.mpr hak
              have hzero₂ : a.descFactorial (k + 1) = 0 :=
                Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
              have hzero₃ : (a + 1).descFactorial (k + 1) = 0 :=
                Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
              simp only [hzero₁, hzero₂, hzero₃, mul_zero,
                Nat.cast_zero, map_zero, zero_mul, zero_add, add_zero]

end BEMOC.Definitive
