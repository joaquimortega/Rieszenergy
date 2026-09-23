import BEMOCFormalization.SphereSupport

open MeasureTheory
namespace BEMOC.Definitive

theorem continuous_integrable_sigma (f : C(Sphere, ℝ)) :
    Integrable (fun x => f x) sigma :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

noncomputable def harmonicL2Inner (m : ℕ)
    (p q : harmonicPolynomialSubmodule m) : ℝ :=
  ∫ x, restrictPolynomial p.val x * restrictPolynomial q.val x ∂sigma

theorem harmonicL2Inner_symm (m : ℕ)
    (p q : harmonicPolynomialSubmodule m) :
    harmonicL2Inner m p q = harmonicL2Inner m q p := by
  simp only [harmonicL2Inner, mul_comm]

theorem harmonicL2Inner_add_left (m : ℕ)
    (p q r : harmonicPolynomialSubmodule m) :
    harmonicL2Inner m (p + q) r =
      harmonicL2Inner m p r + harmonicL2Inner m q r := by
  unfold harmonicL2Inner
  have hfun : restrictPolynomial ((p + q).val) =
      restrictPolynomial p.val + restrictPolynomial q.val := by
    exact map_add restrictPolynomialLinearMap p.val q.val
  rw [hfun]
  simp only [ContinuousMap.add_apply, add_mul]
  exact integral_add
    (continuous_integrable_sigma (restrictPolynomial p.val * restrictPolynomial r.val))
    (continuous_integrable_sigma (restrictPolynomial q.val * restrictPolynomial r.val))

theorem harmonicL2Inner_smul_left (m : ℕ)
    (c : ℝ) (p q : harmonicPolynomialSubmodule m) :
    harmonicL2Inner m (c • p) q = c * harmonicL2Inner m p q := by
  unfold harmonicL2Inner
  have hfun : restrictPolynomial ((c • p).val) = c • restrictPolynomial p.val := by
    exact map_smul restrictPolynomialLinearMap c p.val
  rw [hfun]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc,
    integral_const_mul]

theorem harmonicL2Inner_nonneg (m : ℕ)
    (p : harmonicPolynomialSubmodule m) :
    0 ≤ harmonicL2Inner m p p := by
  unfold harmonicL2Inner
  simpa only [← pow_two] using
    integral_nonneg (fun x => sq_nonneg (restrictPolynomial p.val x))

theorem harmonicL2Inner_definite (m : ℕ)
    (p : harmonicPolynomialSubmodule m)
    (hp : harmonicL2Inner m p p = 0) : p = 0 := by
  have hres : restrictPolynomial p.val = 0 := by
    by_contra hne
    have hpos := sigma_integral_sq_pos hne
    apply (ne_of_gt hpos)
    simpa [harmonicL2Inner, pow_two] using hp
  apply Subtype.ext
  exact homogeneous_restrict_injective
    (mem_harmonicPolynomialSubmodule.mp p.property).1 hres

noncomputable def harmonicInnerCore (m : ℕ) :
    InnerProductSpace.Core ℝ (harmonicPolynomialSubmodule m) where
  inner := harmonicL2Inner m
  conj_inner_symm p q := by
    simpa using (harmonicL2Inner_symm m p q).symm
  re_inner_nonneg := harmonicL2Inner_nonneg m
  add_left p q r := harmonicL2Inner_add_left m p q r
  smul_left p q c := by
    simpa using harmonicL2Inner_smul_left m c p q
  definite := harmonicL2Inner_definite m

noncomputable instance harmonicNormedAddCommGroup (m : ℕ) :
    NormedAddCommGroup (harmonicPolynomialSubmodule m) :=
  (harmonicInnerCore m).toNormedAddCommGroup

noncomputable instance harmonicNormedSpace (m : ℕ) :
    NormedSpace ℝ (harmonicPolynomialSubmodule m) :=
  (harmonicInnerCore m).toNormedSpace

noncomputable instance harmonicInnerProductSpace (m : ℕ) :
    InnerProductSpace ℝ (harmonicPolynomialSubmodule m) :=
  InnerProductSpace.ofCore (harmonicInnerCore m)

noncomputable def harmonicOrthonormalBasis (m : ℕ) :
    OrthonormalBasis (Fin (2 * m + 1)) ℝ (harmonicPolynomialSubmodule m) := by
  letI := finiteDimensional_harmonicPolynomial m
  exact (stdOrthonormalBasis ℝ (harmonicPolynomialSubmodule m)).reindex
    (finCongr (finrank_harmonicPolynomialSubmodule m))

end BEMOC.Definitive
