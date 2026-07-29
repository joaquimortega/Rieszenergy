import BEMOCFormalization.CircleEndpoint

/-!
Endpoint regularity infrastructure for the general-`α` circle residual.

This module isolates the removable sinc factor needed to prove that
the third derivative of `circleEndpointResidual` is `L¹` at both endpoints.
-/

open scoped Topology ENat
open Set Filter Function Complex

namespace BEMOC.CircleGeneral.EndpointRegularity

noncomputable def sincPiComplex (z : ℂ) : ℂ :=
  dslope Complex.sin 0 (Complex.ofReal Real.pi * z)

noncomputable def sincPi (x : ℝ) : ℝ :=
  (sincPiComplex x).re

theorem differentiable_sincPiComplex : Differentiable ℂ sincPiComplex := by
  have hds : Differentiable ℂ (dslope Complex.sin 0) := by
    intro z
    apply (Complex.differentiableOn_dslope (f := Complex.sin)
      (s := Set.univ) univ_mem).mpr
      Complex.differentiable_sin.differentiableOn |>.differentiableAt univ_mem
  unfold sincPiComplex
  intro z
  exact (hds _).comp z (by fun_prop)

theorem contDiff_sincPi : ContDiff ℝ (⊤ : WithTop ℕ∞) sincPi := by
  exact differentiable_sincPiComplex.contDiff.real_of_complex

@[simp] theorem sincPi_zero : sincPi 0 = 1 := by
  simp [sincPi, sincPiComplex, dslope_same, Complex.deriv_sin]

theorem sincPi_eq {x : ℝ} (hx : x ≠ 0) :
    sincPi x = Real.sin (Real.pi * x) / (Real.pi * x) := by
  have hp : (Real.pi : ℂ) * (x : ℂ) ≠ 0 := by
    exact mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (ofReal_ne_zero.mpr hx)
  have hcast : (Real.pi : ℂ) * (x : ℂ) = ((Real.pi * x : ℝ) : ℂ) := by norm_num
  have hc : dslope Complex.sin 0 ((Real.pi : ℂ) * (x : ℂ)) =
      ((Real.sin (Real.pi * x) / (Real.pi * x) : ℝ) : ℂ) := by
    rw [dslope_of_ne _ hp, slope_def_field, Complex.sin_zero, sub_zero, sub_zero, hcast,
      ← Complex.ofReal_sin, ← Complex.ofReal_div]
  exact congrArg Complex.re hc

theorem sincPi_neg (x : ℝ) : sincPi (-x) = sincPi x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [sincPi_eq (neg_ne_zero.mpr hx), sincPi_eq hx]
    rw [mul_neg, Real.sin_neg]
    ring

theorem hasDerivAt_sincPi_zero : HasDerivAt sincPi 0 0 := by
  have hd : Differentiable ℝ sincPi := contDiff_sincPi.differentiable (by simp)
  have hneg := ((hd (-(0 : ℝ))).hasDerivAt.comp (0 : ℝ)
    (hasDerivAt_neg (0 : ℝ))).deriv
  simp only [Function.comp_def, neg_zero] at hneg
  rw [show (fun x : ℝ => sincPi (-x)) = sincPi by funext x; exact sincPi_neg x] at hneg
  have hz : deriv sincPi 0 = 0 := by linarith
  simpa [hz] using (hd (0 : ℝ)).hasDerivAt

theorem sincPi_pos_of_abs_lt_one {x : ℝ} (hx : |x| < 1) : 0 < sincPi x := by
  wlog hx0 : 0 ≤ x generalizing x
  · rw [← sincPi_neg x]
    apply this (x := -x)
    · simpa
    · linarith
  rcases hx0.eq_or_lt with rfl | hxpos
  · simp
  have hx1 : x < 1 := by simpa [abs_of_nonneg hx0] using hx
  rw [sincPi_eq hxpos.ne']
  apply div_pos
  · apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  · positivity

noncomputable def sincPiPow (α x : ℝ) : ℝ := sincPi x ^ α

@[simp] theorem sincPiPow_zero (α : ℝ) : sincPiPow α 0 = 1 := by
  simp [sincPiPow]

theorem contDiffAt_sincPiPow {α x : ℝ} (hx : |x| < 1) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) (sincPiPow α) x := by
  unfold sincPiPow
  exact contDiff_sincPi.contDiffAt.rpow contDiff_const.contDiffAt
    (sincPi_pos_of_abs_lt_one hx).ne'

theorem hasDerivAt_sincPiPow_zero (α : ℝ) :
    HasDerivAt (sincPiPow α) 0 0 := by
  unfold sincPiPow
  convert hasDerivAt_sincPi_zero.rpow_const (Or.inl (by simp)) using 1 ; simp

theorem contDiffOn_sincPiPow (α : ℝ) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) (sincPiPow α) (Ioo (-1 : ℝ) 1) := by
  intro x hx
  exact (contDiffAt_sincPiPow (show |x| < 1 by simpa [abs_lt] using hx)).contDiffWithinAt

theorem contDiffOn_deriv_sincPiPow (α : ℝ) :
    ContDiffOn ℝ 3 (deriv (sincPiPow α)) (Ioo (-1 : ℝ) 1) := by
  have h4 : ContDiffOn ℝ (3 + 1) (sincPiPow α) (Ioo (-1 : ℝ) 1) :=
    (contDiffOn_sincPiPow α).of_le (by norm_num)
  exact ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).mp h4).2.2

theorem contDiffOn_deriv2_sincPiPow (α : ℝ) :
    ContDiffOn ℝ 2 (deriv (deriv (sincPiPow α))) (Ioo (-1 : ℝ) 1) := by
  have h3 : ContDiffOn ℝ (2 + 1) (deriv (sincPiPow α)) (Ioo (-1 : ℝ) 1) := by
    simpa using contDiffOn_deriv_sincPiPow α
  exact ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).mp h3).2.2

theorem contDiffOn_deriv3_sincPiPow (α : ℝ) :
    ContDiffOn ℝ 1 (deriv (deriv (deriv (sincPiPow α))))
      (Ioo (-1 : ℝ) 1) := by
  have h2 : ContDiffOn ℝ (1 + 1) (deriv (deriv (sincPiPow α)))
      (Ioo (-1 : ℝ) 1) := by simpa using contDiffOn_deriv2_sincPiPow α
  exact ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).mp h2).2.2

/-- The exact endpoint cancellation: the smooth factor differs from one only
quadratically. This is the key estimate turning the apparent `x^(α-3)` term
in the third derivative into an integrable `x^(α-1)` term. -/
theorem sincPiPow_sub_one_quadratic_bound (α : ℝ) :
    ∃ C : ℝ, ∀ x ∈ Icc (0 : ℝ) (1 / 2 : ℝ),
      |sincPiPow α x - 1| ≤ C * x ^ 2 := by
  have hcont : ContDiffOn ℝ 2 (sincPiPow α) (Icc (0 : ℝ) (1 / 2 : ℝ)) := by
    exact (contDiffOn_sincPiPow α).of_le (by norm_num) |>.mono (by
      intro x hx
      constructor <;> linarith [hx.1, hx.2])
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (n := 1) hcont
  refine ⟨C, ?_⟩
  intro x hx
  have hdu : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) (1 / 2 : ℝ)) 0 :=
    (uniqueDiffOn_Icc (show (0 : ℝ) < 1 / 2 by norm_num)) 0 ⟨le_rfl, by norm_num⟩
  have hdw : derivWithin (sincPiPow α) (Icc (0 : ℝ) (1 / 2 : ℝ)) 0 = 0 :=
    hasDerivAt_sincPiPow_zero α |>.hasDerivWithinAt.derivWithin hdu
  have := hC x hx
  rw [taylorWithinEval_succ, taylor_within_zero_eval,
    iteratedDerivWithin_one, hdw] at this
  simpa using this

end BEMOC.CircleGeneral.EndpointRegularity
