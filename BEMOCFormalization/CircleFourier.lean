import Mathlib
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Fourier route to the singular circle Euler--Maclaurin constant

This module develops the parts of the Fourier proof which are independent
of the still-missing evaluation of the Fourier coefficients of
`x ↦ (2 sin (π x)) ^ α`.
-/

open scoped BigOperators Topology Real
open Filter Set Complex
open MeasureTheory

namespace BEMOC.CircleFourier

/-! ## Negative-axis zeta bridge -/

noncomputable def realZeta (s : ℝ) : ℝ :=
  (riemannZeta (s : ℂ)).re

theorem riemannZeta_one_add_real_eq_ofReal_tsum {α : ℝ} (hα : 0 < α) :
    riemannZeta ((1 + α : ℝ) : ℂ) =
      ((∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + α)) : ℝ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow]
  · rw [Complex.ofReal_tsum]
    congr 1
    funext n
    rw [Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_cpow (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]
    norm_num
  · norm_num
    linarith

theorem riemannZeta_neg_real_functional_equation {α : ℝ} (hα : 0 < α) :
    riemannZeta (-(α : ℂ)) =
      2 * (2 * (Real.pi : ℂ)) ^ (-((1 + α : ℝ) : ℂ)) *
        Complex.Gamma ((1 + α : ℝ) : ℂ) *
        Complex.cos ((Real.pi : ℂ) * ((1 + α : ℝ) : ℂ) / 2) *
        riemannZeta ((1 + α : ℝ) : ℂ) := by
  have hs (n : ℕ) : ((1 + α : ℝ) : ℂ) ≠ -(n : ℂ) := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hs1 : ((1 + α : ℝ) : ℂ) ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  have harg : (1 : ℂ) - ((1 + α : ℝ) : ℂ) = -(α : ℂ) := by
    push_cast
    ring
  rw [← harg]
  exact riemannZeta_one_sub (s := ((1 + α : ℝ) : ℂ)) hs hs1

theorem riemannZeta_neg_real_eq_ofReal {α : ℝ} (hα : 0 < α) :
    riemannZeta (-(α : ℂ)) =
      ((2 * (2 * Real.pi) ^ (-(1 + α)) * Real.Gamma (1 + α) *
          Real.cos (Real.pi * (1 + α) / 2) *
          ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + α)) : ℝ) := by
  rw [riemannZeta_neg_real_functional_equation hα,
    riemannZeta_one_add_real_eq_ofReal_tsum hα]
  have hbase : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    rfl
  have hexp : -((1 + α : ℝ) : ℂ) = ((-(1 + α) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hcosarg :
      (Real.pi : ℂ) * ((1 + α : ℝ) : ℂ) / 2 =
        ((Real.pi * (1 + α) / 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hbase, hexp, hcosarg]
  rw [← Complex.ofReal_cpow (by positivity : 0 ≤ 2 * Real.pi),
    Complex.Gamma_ofReal, ← Complex.ofReal_cos]
  push_cast
  rfl

theorem realZeta_neg_eq_functional_equation {α : ℝ} (hα : 0 < α) :
    realZeta (-α) =
      2 * (2 * Real.pi) ^ (-(1 + α)) * Real.Gamma (1 + α) *
        Real.cos (Real.pi * (1 + α) / 2) *
        ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + α) := by
  have h := congrArg Complex.re (riemannZeta_neg_real_eq_ofReal hα)
  unfold realZeta
  rw [show (((-α : ℝ) : ℂ)) = -(α : ℂ) by push_cast; rfl]
  simpa only [Complex.ofReal_re] using h

/-- The leading constant in the large positive-frequency asymptotic
`f̂(n) ~ fourierCuspConstant α * n ^ (-1-α)` for
`f(x) = (2 sin (πx))^α`. -/
noncomputable def fourierCuspConstant (α : ℝ) : ℝ :=
  -Real.Gamma (1 + α) * Real.sin (Real.pi * α / 2) / Real.pi

/-- The functional equation turns the absolutely convergent positive Fourier
tail into exactly the endpoint constant appearing in Lemma 3.1. -/
theorem two_mul_cusp_mul_zeta_eq_circleCorrection {α : ℝ} (hα : 0 < α) :
    2 * fourierCuspConstant α *
        (∑' m : ℕ, 1 / ((m + 1 : ℕ) : ℝ) ^ (1 + α)) =
      2 * (2 * Real.pi) ^ α * realZeta (-α) := by
  rw [realZeta_neg_eq_functional_equation hα]
  have htrig : Real.cos (Real.pi * (1 + α) / 2) =
      -Real.sin (Real.pi * α / 2) := by
    rw [show Real.pi * (1 + α) / 2 = Real.pi * α / 2 + Real.pi / 2 by ring]
    exact Real.cos_add_pi_div_two _
  rw [htrig]
  unfold fourierCuspConstant
  let P : ℝ := 2 * Real.pi
  have hp : 0 < P := by dsimp [P]; positivity
  have hpow : P ^ α * P ^ (-(1 + α)) = P⁻¹ := by
    rw [show -(1 + α) = -α + -1 by ring, Real.rpow_add hp, ← mul_assoc,
      ← Real.rpow_add hp]
    simp only [add_neg_cancel, Real.rpow_zero, one_mul, Real.rpow_neg_one]
  change
    2 * (-Real.Gamma (1 + α) * Real.sin (Real.pi * α / 2) / Real.pi) *
        (∑' m : ℕ, 1 / ((m + 1 : ℕ) : ℝ) ^ (1 + α)) =
      2 * P ^ α *
        (2 * P ^ (-(1 + α)) * Real.Gamma (1 + α) *
          (-Real.sin (Real.pi * α / 2)) *
          ∑' m : ℕ, 1 / ((m + 1 : ℕ) : ℝ) ^ (1 + α))
  rw [show 2 * P ^ α *
        (2 * P ^ (-(1 + α)) * Real.Gamma (1 + α) *
          (-Real.sin (Real.pi * α / 2)) *
          ∑' m : ℕ, 1 / ((m + 1 : ℕ) : ℝ) ^ (1 + α)) =
      -4 * (P ^ α * P ^ (-(1 + α))) * Real.Gamma (1 + α) *
        Real.sin (Real.pi * α / 2) *
        (∑' m : ℕ, 1 / ((m + 1 : ℕ) : ℝ) ^ (1 + α)) by ring,
    hpow]
  dsimp [P]
  field_simp
  ring

/-! ## Tannery step for the aliased positive Fourier tail -/

/-- The positive-frequency portion selected by a root grid, after multiplying
by the Euler--Maclaurin scale `w^(α+1)`. -/
noncomputable def scaledPositiveAliasTail (α : ℝ) (a : ℕ → ℝ) (w : ℕ) : ℝ :=
  ∑' m : ℕ, (w : ℝ) ^ (1 + α) * a ((m + 1) * w)

/-- Dominated convergence for the positive aliased Fourier tail.  This is the
precise analytic interchange needed after the root-grid filter has selected
the frequencies `(m+1)w`.

The hypotheses are deliberately coefficient-level: the exact Gamma quotient
will supply both `hpoint` and `hbound`. -/
theorem tendsto_scaledPositiveAliasTail
    {α C D : ℝ} {a : ℕ → ℝ} (hα : 0 < α)
    (hpoint : ∀ m : ℕ,
      Tendsto (fun w : ℕ => (w : ℝ) ^ (1 + α) * a ((m + 1) * w)) atTop
        (𝓝 (C / ((m + 1 : ℕ) : ℝ) ^ (1 + α))))
    (hbound : ∀ᶠ w : ℕ in atTop, ∀ m : ℕ,
      ‖(w : ℝ) ^ (1 + α) * a ((m + 1) * w)‖ ≤
        D / ((m + 1 : ℕ) : ℝ) ^ (1 + α)) :
    Tendsto (scaledPositiveAliasTail α a) atTop
      (𝓝 (C * ∑' m : ℕ, 1 / ((m + 1 : ℕ) : ℝ) ^ (1 + α))) := by
  have hs : Summable (fun m : ℕ =>
      D / ((m + 1 : ℕ) : ℝ) ^ (1 + α)) := by
    have hp : Summable (fun m : ℕ =>
        1 / ((m + 1 : ℕ) : ℝ) ^ (1 + α)) := by
      have hraw : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + α))) :=
        Real.summable_nat_rpow.mpr (by linarith : -(1 + α) < -1)
      have hshift := (summable_nat_add_iff 1).2 hraw
      refine hshift.congr (fun m => ?_)
      rw [Real.rpow_neg (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))]
      simp only [one_div]
    exact (hp.mul_left D).congr (fun m => by simp only [div_eq_mul_inv, one_mul])
  have ht := tendsto_tsum_of_dominated_convergence hs hpoint hbound
  unfold scaledPositiveAliasTail
  have htsum : (∑' m : ℕ, C / ((m + 1 : ℕ) : ℝ) ^ (1 + α)) =
      C * ∑' m : ℕ, 1 / ((m + 1 : ℕ) : ℝ) ^ (1 + α) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  rw [← htsum]
  exact ht

/-- Once positive and negative coefficients agree, the two-sided alias tail
has the manuscript's constant. -/
theorem tendsto_two_mul_scaledPositiveAliasTail
    {α D : ℝ} {a : ℕ → ℝ} (hα : 0 < α)
    (hpoint : ∀ m : ℕ,
      Tendsto (fun w : ℕ => (w : ℝ) ^ (1 + α) * a ((m + 1) * w)) atTop
        (𝓝 (fourierCuspConstant α /
          ((m + 1 : ℕ) : ℝ) ^ (1 + α))))
    (hbound : ∀ᶠ w : ℕ in atTop, ∀ m : ℕ,
      ‖(w : ℝ) ^ (1 + α) * a ((m + 1) * w)‖ ≤
        D / ((m + 1 : ℕ) : ℝ) ^ (1 + α)) :
    Tendsto (fun w => 2 * scaledPositiveAliasTail α a w) atTop
      (𝓝 (2 * (2 * Real.pi) ^ α * realZeta (-α))) := by
  have ht := (tendsto_scaledPositiveAliasTail hα hpoint hbound).const_mul 2
  rw [← mul_assoc,
    two_mul_cusp_mul_zeta_eq_circleCorrection hα] at ht
  exact ht

/-! ## Exact Gamma form of the expected coefficients -/

/-- The positive-frequency Gamma quotient predicted by the classical
sine-power integral. -/
noncomputable def chordFourierCoeffGamma (α : ℝ) (n : ℕ) : ℝ :=
  -Real.Gamma (1 + α) * Real.sin (Real.pi * α / 2) / Real.pi *
    (Real.Gamma ((n : ℝ) - α / 2) /
      Real.Gamma ((n : ℝ) + α / 2 + 1))

theorem chordFourierCoeffGamma_eq (α : ℝ) (n : ℕ) :
    chordFourierCoeffGamma α n = fourierCuspConstant α *
      (Real.Gamma ((n : ℝ) - α / 2) /
        Real.Gamma ((n : ℝ) + α / 2 + 1)) := by
  rfl

/-! ### Gamma quotient asymptotics -/

/-- Iterating `Γ(x+1)=xΓ(x)` along a positive real ray. -/
theorem Gamma_add_nat_eq_prod {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Real.Gamma (a + n) =
      (∏ j ∈ Finset.range n, (a + j)) * Real.Gamma a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      rw [show a + ((n : ℝ) + 1) = (a + n) + 1 by ring,
        Real.Gamma_add_one (by positivity : a + (n : ℝ) ≠ 0), ih,
        Finset.prod_range_succ]
      push_cast
      ring

/-- A Gamma quotient rewritten exactly in terms of Euler's convergent
`GammaSeq`.  This identity makes the quotient asymptotic a direct consequence
of `Real.GammaSeq_tendsto_Gamma`. -/
theorem scaled_Gamma_ratio_eq_GammaSeq
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℝ) ^ (b - a) *
        (Real.Gamma (a + (n + 1 : ℕ)) /
          Real.Gamma (b + (n + 1 : ℕ))) =
      ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (b - a)) *
        (Real.GammaSeq b n / Real.GammaSeq a n) *
        (Real.Gamma a / Real.Gamma b) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hn1pos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hGb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hpa : (∏ j ∈ Finset.range (n + 1), (a + j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    positivity
  have hpb : (∏ j ∈ Finset.range (n + 1), (b + j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    positivity
  have hfac : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Gamma_add_nat_eq_prod ha (n + 1), Gamma_add_nat_eq_prod hb (n + 1)]
  unfold Real.GammaSeq
  have hdivpow :
      ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (b - a)) =
        (((n + 1 : ℕ) : ℝ) ^ (b - a)) / (n : ℝ) ^ (b - a) := by
    exact Real.div_rpow hn1pos.le hnpos.le (b - a)
  have hsubpow : (n : ℝ) ^ (b - a) =
      (n : ℝ) ^ b / (n : ℝ) ^ a := Real.rpow_sub hnpos b a
  rw [hdivpow, hsubpow]
  field_simp [hGa, hGb, hpa, hpb, hfac,
    (Real.rpow_pos_of_pos hnpos _).ne']
  ring

/-- Standard Gamma-ratio asymptotic, proved here from Mathlib's Euler-limit
sequence rather than assumed as an external special-function fact. -/
theorem tendsto_scaled_Gamma_ratio
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (b - a) *
        (Real.Gamma (a + (n + 1 : ℕ)) /
          Real.Gamma (b + (n + 1 : ℕ))))
      atTop (𝓝 1) := by
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hGb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hbase : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) / (n : ℝ))) atTop (𝓝 1) := by
    have hz := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
    have ho := (tendsto_const_nhds.add hz :
      Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)))
    convert ho.congr' ?_ using 1 <;> norm_num
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
    push_cast
    field_simp
  have hbasepow : Tendsto
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (b - a)))
      atTop (𝓝 1) := by
    simpa only [Real.one_rpow] using
      (Real.continuousAt_rpow_const 1 (b - a) (Or.inl one_ne_zero)).tendsto.comp
        hbase
  have hseq : Tendsto
      (fun n : ℕ => Real.GammaSeq b n / Real.GammaSeq a n)
      atTop (𝓝 (Real.Gamma b / Real.Gamma a)) :=
    (Real.GammaSeq_tendsto_Gamma b).div (Real.GammaSeq_tendsto_Gamma a) hGa
  have hprod := (hbasepow.mul hseq).mul_const (Real.Gamma a / Real.Gamma b)
  have hone :
      (1 : ℝ) * (Real.Gamma b / Real.Gamma a) *
          (Real.Gamma a / Real.Gamma b) = 1 := by
    field_simp [hGa, hGb]
  rw [hone] at hprod
  apply hprod.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  exact (scaled_Gamma_ratio_eq_GammaSeq ha hb hn).symm

/-- Recurrence variant valid away from the poles, including the parameter
`-α/2 ∈ (-1,0)` needed by the chord coefficient. -/
theorem Gamma_add_nat_eq_prod_of_forall_ne {a : ℝ}
    (ha : ∀ j : ℕ, a + j ≠ 0) (n : ℕ) :
    Real.Gamma (a + n) =
      (∏ j ∈ Finset.range n, (a + j)) * Real.Gamma a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      rw [show a + ((n : ℝ) + 1) = (a + n) + 1 by ring,
        Real.Gamma_add_one (ha n), ih, Finset.prod_range_succ]
      ring

/-- Gamma-ratio asymptotic away from all nonpositive-integer poles. -/
theorem tendsto_scaled_Gamma_ratio_of_forall_ne
    {a b : ℝ} (ha : ∀ j : ℕ, a + j ≠ 0)
    (hb : ∀ j : ℕ, b + j ≠ 0) :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (b - a) *
        (Real.Gamma (a + (n + 1 : ℕ)) /
          Real.Gamma (b + (n + 1 : ℕ))))
      atTop (𝓝 1) := by
  have hGa : Real.Gamma a ≠ 0 := by
    apply Real.Gamma_ne_zero
    intro m ham
    apply ha m
    rw [ham]
    simp
  have hGb : Real.Gamma b ≠ 0 := by
    apply Real.Gamma_ne_zero
    intro m hbm
    apply hb m
    rw [hbm]
    simp
  have hbase : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) / (n : ℝ))) atTop (𝓝 1) := by
    have hz := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
    have ho := (tendsto_const_nhds.add hz :
      Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)))
    convert ho.congr' ?_ using 1 <;> norm_num
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
    field_simp
  have hbasepow : Tendsto
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (b - a)))
      atTop (𝓝 1) := by
    simpa only [Real.one_rpow] using
      (Real.continuousAt_rpow_const 1 (b - a) (Or.inl one_ne_zero)).tendsto.comp
        hbase
  have hseq : Tendsto
      (fun n : ℕ => Real.GammaSeq b n / Real.GammaSeq a n)
      atTop (𝓝 (Real.Gamma b / Real.Gamma a)) :=
    (Real.GammaSeq_tendsto_Gamma b).div (Real.GammaSeq_tendsto_Gamma a) hGa
  have hprod := (hbasepow.mul hseq).mul_const (Real.Gamma a / Real.Gamma b)
  have hone :
      (1 : ℝ) * (Real.Gamma b / Real.Gamma a) *
          (Real.Gamma a / Real.Gamma b) = 1 := by
    field_simp [hGa, hGb]
  rw [hone] at hprod
  apply hprod.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hn1pos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hpa : (∏ j ∈ Finset.range (n + 1), (a + j)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => ha j)
  have hpb : (∏ j ∈ Finset.range (n + 1), (b + j)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hb j)
  have hfac : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Gamma_add_nat_eq_prod_of_forall_ne ha (n + 1),
    Gamma_add_nat_eq_prod_of_forall_ne hb (n + 1)]
  unfold Real.GammaSeq
  have hdivpow :
      ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (b - a)) =
        (((n + 1 : ℕ) : ℝ) ^ (b - a)) / (n : ℝ) ^ (b - a) :=
    Real.div_rpow hn1pos.le hnpos.le (b - a)
  have hsubpow : (n : ℝ) ^ (b - a) =
      (n : ℝ) ^ b / (n : ℝ) ^ a := Real.rpow_sub hnpos b a
  rw [hdivpow, hsubpow]
  field_simp [hGa, hGb, hpa, hpb, hfac,
    (Real.rpow_pos_of_pos hnpos _).ne']
  ring

/-- The exact Gamma quotient occurring in the chord coefficient has the
required cusp normalization for every `0 < α < 2`. -/
theorem tendsto_chord_Gamma_quotient {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 + α) *
        (Real.Gamma (((n + 1 : ℕ) : ℝ) - α / 2) /
          Real.Gamma (((n + 1 : ℕ) : ℝ) + α / 2 + 1)))
      atTop (𝓝 1) := by
  have ha : ∀ j : ℕ, -α / 2 + j ≠ 0 := by
    intro j hj
    rcases j with _ | j
    · norm_num at hj
      linarith
    · have hj1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by norm_num
      have hhalf : α / 2 < 1 := by linarith
      norm_num at hj
      linarith
  have hb : ∀ j : ℕ, (1 + α / 2) + j ≠ 0 := by
    intro j
    positivity
  convert tendsto_scaled_Gamma_ratio_of_forall_ne ha hb using 1
  · funext n
    congr 1
    · congr 1 <;> ring
    · congr 2 <;> push_cast <;> ring

/-- Unshifted form of the chord Gamma-quotient limit. -/
theorem tendsto_chord_Gamma_quotient_full {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    Tendsto
      (fun n : ℕ => (n : ℝ) ^ (1 + α) *
        (Real.Gamma ((n : ℝ) - α / 2) /
          Real.Gamma ((n : ℝ) + α / 2 + 1)))
      atTop (𝓝 1) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  convert tendsto_chord_Gamma_quotient hα0 hα2 using 1

/-- Consequently the proposed exact Fourier coefficients have precisely the
cusp constant required by the zeta functional equation. -/
theorem tendsto_scaled_chordFourierCoeffGamma {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    Tendsto
      (fun n : ℕ => (n : ℝ) ^ (1 + α) * chordFourierCoeffGamma α n)
      atTop (𝓝 (fourierCuspConstant α)) := by
  have h := (tendsto_chord_Gamma_quotient_full hα0 hα2).const_mul
    (fourierCuspConstant α)
  have h' : Tendsto
      (fun n : ℕ => fourierCuspConstant α *
        ((n : ℝ) ^ (1 + α) *
          (Real.Gamma ((n : ℝ) - α / 2) /
            Real.Gamma ((n : ℝ) + α / 2 + 1))))
      atTop (𝓝 (fourierCuspConstant α)) := by
    simpa only [mul_one] using h
  apply h'.congr'
  filter_upwards [] with n
  rw [chordFourierCoeffGamma_eq]
  ring

/-- A global scaled coefficient limit automatically supplies all pointwise
subsequence limits and a single Tannery majorant. -/
theorem subsequence_data_of_scaled_limit
    {p C : ℝ} {a : ℕ → ℝ}
    (h : Tendsto (fun n : ℕ => (n : ℝ) ^ p * a n) atTop (𝓝 C)) :
    (∀ m : ℕ,
      Tendsto (fun w : ℕ => (w : ℝ) ^ p * a ((m + 1) * w)) atTop
        (𝓝 (C / ((m + 1 : ℕ) : ℝ) ^ p))) ∧
      ∃ D : ℝ, ∀ w m : ℕ,
        ‖(w : ℝ) ^ p * a ((m + 1) * w)‖ ≤
          D / ((m + 1 : ℕ) : ℝ) ^ p := by
  have hnorm : Tendsto (fun n : ℕ => ‖(n : ℝ) ^ p * a n‖) atTop (𝓝 ‖C‖) :=
    tendsto_norm.comp h
  rcases hnorm.bddAbove_range with ⟨D, hD⟩
  constructor
  · intro m
    have hm1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
    have hmul : Tendsto (fun w : ℕ => (m + 1) * w) atTop atTop := by
      refine tendsto_atTop.2 (fun N => ?_)
      filter_upwards [eventually_ge_atTop N] with w hw
      exact hw.trans (le_mul_of_one_le_left' hm1)
    have hc := h.comp hmul
    have hmpos : 0 < (((m + 1 : ℕ) : ℝ) ^ p) :=
      Real.rpow_pos_of_pos (by positivity) p
    have hcdiv := hc.div_const (((m + 1 : ℕ) : ℝ) ^ p)
    apply hcdiv.congr'
    filter_upwards [] with w
    change (((((m + 1) * w : ℕ) : ℝ) ^ p * a ((m + 1) * w)) /
      (((m + 1 : ℕ) : ℝ) ^ p)) = _
    rw [show ((((m + 1) * w : ℕ) : ℝ)) =
      ((m + 1 : ℕ) : ℝ) * (w : ℝ) by push_cast; rfl]
    rw [Real.mul_rpow (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))
      (Nat.cast_nonneg w)]
    field_simp [hmpos.ne']
    ring
  · refine ⟨D, fun w m => ?_⟩
    have hmpos : 0 < (((m + 1 : ℕ) : ℝ) ^ p) :=
      Real.rpow_pos_of_pos (by positivity) p
    have hglobal : ‖((((m + 1) * w : ℕ) : ℝ) ^ p) * a ((m + 1) * w)‖ ≤ D :=
      hD (Set.mem_range_self ((m + 1) * w))
    have heq : (w : ℝ) ^ p * a ((m + 1) * w) =
        ((((m + 1) * w : ℕ) : ℝ) ^ p * a ((m + 1) * w)) /
          (((m + 1 : ℕ) : ℝ) ^ p) := by
      rw [show ((((m + 1) * w : ℕ) : ℝ)) =
          ((m + 1 : ℕ) : ℝ) * (w : ℝ) by push_cast; rfl,
        Real.mul_rpow (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ))
          (Nat.cast_nonneg w)]
      field_simp [hmpos.ne']
      ring
    rw [heq, norm_div]
    rw [Real.norm_of_nonneg hmpos.le]
    exact div_le_div_of_nonneg_right hglobal hmpos.le

/-! ## Root-grid character filter -/

/-- Intrinsic continuous chord profile on the unit additive circle. -/
noncomputable def chordProfileCircle (α : ℝ) (hα : 0 < α) :
    C(AddCircle (1 : ℝ), ℂ) where
  toFun x := ((‖((AddCircle.toCircle x : Circle) : ℂ) - 1‖ ^ α : ℝ) : ℂ)
  continuous_toFun := by
    have hc : Continuous
        (fun x : AddCircle (1 : ℝ) => ((AddCircle.toCircle x : Circle) : ℂ)) :=
      continuous_subtype_val.comp AddCircle.continuous_toCircle
    exact Complex.continuous_ofReal.comp
      ((hc.sub continuous_const).norm.rpow_const (fun _ => Or.inr hα.le))

/-- Chord length from `1` to `exp(2πix)` on the fundamental interval. -/
theorem norm_toCircle_sub_one_eq_two_sin {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ‖((AddCircle.toCircle (x : AddCircle (1 : ℝ)) : Circle) : ℂ) - 1‖ =
      2 * Real.sin (Real.pi * x) := by
  have hsin : 0 ≤ Real.sin (Real.pi * x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le hx0)
      (by nlinarith [Real.pi_pos])
  have hsq :
      ‖((AddCircle.toCircle (x : AddCircle (1 : ℝ)) : Circle) : ℂ) - 1‖ ^ 2 =
        (2 * Real.sin (Real.pi * x)) ^ 2 := by
    rw [AddCircle.toCircle, Function.Periodic.lift_coe, Circle.coe_exp]
    simp only [div_one]
    change ‖Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2 = _
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im, sub_zero]
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring,
      Real.cos_two_mul, Real.sin_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
  nlinarith [norm_nonneg
    (((AddCircle.toCircle (x : AddCircle (1 : ℝ)) : Circle) : ℂ) - 1)]

theorem chordProfileCircle_coe {α x : ℝ} (hα : 0 < α)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    chordProfileCircle α hα (x : AddCircle (1 : ℝ)) =
      ((2 * Real.sin (Real.pi * x)) ^ α : ℝ) := by
  change ((‖((AddCircle.toCircle (x : AddCircle (1 : ℝ)) : Circle) : ℂ) - 1‖ ^ α : ℝ) : ℂ) =
    (((2 * Real.sin (Real.pi * x)) ^ α : ℝ) : ℂ)
  rw [norm_toCircle_sub_one_eq_two_sin hx0 hx1]

/-- Unbundled oscillatory integral for the chord Fourier coefficient. -/
noncomputable def chordCoeffIntegral (α : ℝ) (n : ℤ) : ℂ :=
  ∫ x : ℝ in (0)..1,
    Complex.exp (-(2 * Real.pi * Complex.I * n * x)) *
      ((2 * Real.sin (Real.pi * x)) ^ α : ℝ)

/-- The continuous zeroth Fourier coefficient of the chord profile. -/
noncomputable def circleMoment (α : ℝ) : ℝ :=
  ∫ x : ℝ in (0)..1, (2 * Real.sin (Real.pi * x)) ^ α

theorem fourierCoeff_chordProfile_eq_integral {α : ℝ} (hα : 0 < α) (n : ℤ) :
    fourierCoeff (chordProfileCircle α hα) n = chordCoeffIntegral α n := by
  rw [fourierCoeff_eq_intervalIntegral (chordProfileCircle α hα) n 0]
  simp only [zero_add, chordCoeffIntegral]
  norm_num
  apply intervalIntegral.integral_congr
  intro x hx
  norm_num at hx
  simp only [fourier_coe_apply, smul_eq_mul]
  change (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n * x)) *
      chordProfileCircle α hα (x : AddCircle (1 : ℝ)) = _
  rw [chordProfileCircle_coe hα hx.1 hx.2]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

/-- The zero Fourier coefficient is exactly the continuous circle moment;
this part requires no special-function evaluation. -/
theorem fourierCoeff_chordProfile_zero {α : ℝ} (hα : 0 < α) :
    fourierCoeff (chordProfileCircle α hα) 0 = (circleMoment α : ℂ) := by
  rw [fourierCoeff_chordProfile_eq_integral hα]
  unfold chordCoeffIntegral circleMoment
  simp only [Int.cast_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul,
    intervalIntegral.integral_ofReal]

/-- Exact positive-frequency coefficient statement.  The theorem below is
the remaining special-function target: all aliasing and asymptotic
consequences are developed independently of its proof. -/
def HasExactPositiveChordCoefficients (α : ℝ) (hα : 0 < α) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    fourierCoeff (chordProfileCircle α hα) (n : ℤ) =
      (chordFourierCoeffGamma α n : ℂ)

/-! ### Beta-integral route to the exact coefficient -/

/-- Real form of the symmetric beta integral used by the sine-power moment. -/
noncomputable def realSymmetricBetaIntegral (p : ℝ) : ℝ :=
  ∫ t : ℝ in (0)..1, t ^ (p - 1) * (1 - t) ^ (p - 1)

/-- The real symmetric beta integral is the restriction of mathlib's complex
beta integral to a positive real parameter. -/
theorem ofReal_realSymmetricBetaIntegral_eq_beta (p : ℝ) :
    (realSymmetricBetaIntegral p : ℂ) =
      Complex.betaIntegral (p : ℂ) (p : ℂ) := by
  unfold realSymmetricBetaIntegral Complex.betaIntegral
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t ht
  norm_num at ht
  change (((t ^ (p - 1) * (1 - t) ^ (p - 1) : ℝ)) : ℂ) = _
  rw [Complex.ofReal_mul]
  rw [Complex.ofReal_cpow ht.1, Complex.ofReal_cpow (sub_nonneg.mpr ht.2)]
  push_cast
  ring

/-- Pointwise algebra behind the substitution `t = (1 - cos x) / 2`. -/
theorem symmetricBeta_substitution_integrand {α x : ℝ} (hα : 0 < α)
    (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    (2 : ℝ) ^ α *
          (((1 - Real.cos x) / 2) ^ ((α - 1) / 2) *
            (1 - (1 - Real.cos x) / 2) ^ ((α - 1) / 2)) *
        (Real.sin x / 2) =
      Real.sin x ^ α := by
  have hs : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxπ
  rcases hs.eq_or_lt with hs0 | hspos
  · rw [← hs0]
    simp [Real.zero_rpow hα.ne']
  have ht0 : 0 ≤ (1 - Real.cos x) / 2 := by
    nlinarith [Real.cos_le_one x]
  have ht1 : 0 ≤ 1 - (1 - Real.cos x) / 2 := by
    nlinarith [Real.neg_one_le_cos x]
  have hprod :
      ((1 - Real.cos x) / 2) * (1 - (1 - Real.cos x) / 2) =
        (Real.sin x / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [← Real.mul_rpow ht0 ht1, hprod]
  rw [← Real.rpow_natCast_mul (div_nonneg hs (by norm_num : (0 : ℝ) ≤ 2)) 2
    ((α - 1) / 2)]
  have hexp : ((2 : ℕ) : ℝ) * ((α - 1) / 2) = α - 1 := by norm_num; ring
  rw [hexp]
  have hbpos : 0 < Real.sin x / 2 := by positivity
  have hcombine :
      (Real.sin x / 2) ^ (α - 1) * (Real.sin x / 2) =
        (Real.sin x / 2) ^ α := by
    calc
      _ = (Real.sin x / 2) ^ (α - 1) * (Real.sin x / 2) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (Real.sin x / 2) ^ ((α - 1) + 1) :=
        (Real.rpow_add hbpos (α - 1) 1).symm
      _ = _ := by ring_nf
  rw [mul_assoc, hcombine]
  rw [Real.div_rpow hs (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) α).ne']

/-- Exact beta evaluation of the real sine-power integral.  The general
change-of-variables theorem is used because the beta kernel can be singular
at both endpoints when `0 < α < 1`. -/
theorem integral_sin_rpow_eq_symmetricBeta {α : ℝ} (hα : 0 < α) :
    (∫ x : ℝ in (0)..Real.pi, Real.sin x ^ α) =
      (2 : ℝ) ^ α * realSymmetricBetaIntegral ((α + 1) / 2) := by
  let p : ℝ := (α + 1) / 2
  let f : ℝ → ℝ := fun x => (1 - Real.cos x) / 2
  let f' : ℝ → ℝ := fun x => Real.sin x / 2
  let g : ℝ → ℝ := fun t =>
    (2 : ℝ) ^ α * (t ^ (p - 1) * (1 - t) ^ (p - 1))
  have hp : 0 < p := by dsimp [p]; linarith
  have hf : ContinuousOn f (Set.uIcc (0 : ℝ) Real.pi) := by
    exact (continuous_const.sub Real.continuous_cos).div_const 2 |>.continuousOn
  have hff' : ∀ x ∈ Ioo (min (0 : ℝ) Real.pi) (max (0 : ℝ) Real.pi),
      HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    apply HasDerivAt.hasDerivWithinAt
    dsimp [f, f']
    convert ((hasDerivAt_const x 1).sub (Real.hasDerivAt_cos x)).div_const 2 using 1 <;>
      ring
  have himageOpen : f '' Ioo (min (0 : ℝ) Real.pi) (max (0 : ℝ) Real.pi) ⊆
      Ioo (0 : ℝ) 1 := by
    rintro y ⟨x, hx, rfl⟩
    simp only [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at hx
    have hxmem : x ∈ Icc (0 : ℝ) Real.pi := ⟨hx.1.le, hx.2.le⟩
    have hc1 : Real.cos x < 1 := by
      simpa using Real.strictAntiOn_cos (show (0 : ℝ) ∈ Icc 0 Real.pi by
        exact ⟨le_rfl, Real.pi_pos.le⟩) hxmem hx.1
    have hcn : -1 < Real.cos x := by
      simpa using Real.strictAntiOn_cos hxmem
        (show Real.pi ∈ Icc (0 : ℝ) Real.pi by exact ⟨Real.pi_pos.le, le_rfl⟩) hx.2
    dsimp [f]
    constructor <;> linarith
  have hg_cont : ContinuousOn g
      (f '' Ioo (min (0 : ℝ) Real.pi) (max (0 : ℝ) Real.pi)) := by
    apply ContinuousOn.mono _ himageOpen
    dsimp [g]
    exact continuousOn_const.mul
      ((continuousOn_id.rpow_const (fun t ht => Or.inl ht.1.ne')).mul
        ((continuousOn_const.sub continuousOn_id).rpow_const
          (fun t ht => Or.inl (sub_pos.mpr ht.2).ne')))
  have hkernel : IntervalIntegrable
      (fun t : ℝ => t ^ (p - 1) * (1 - t) ^ (p - 1)) volume 0 1 := by
    have hc := Complex.betaIntegral_convergent
      (u := (p : ℂ)) (v := (p : ℂ)) (by simpa) (by simpa)
    have hcre : IntervalIntegrable
        (fun t : ℝ => ((t : ℂ) ^ ((p : ℂ) - 1) *
          (1 - (t : ℂ)) ^ ((p : ℂ) - 1)).re) volume 0 1 :=
      ⟨hc.1.re, hc.2.re⟩
    apply hcre.congr
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t ht
    norm_num [uIoc_of_le] at ht
    change ((t : ℂ) ^ ((p : ℂ) - 1) *
      (1 - (t : ℂ)) ^ ((p : ℂ) - 1)).re =
        (((t ^ (p - 1) * (1 - t) ^ (p - 1) : ℝ) : ℂ)).re
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1.le,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2)]
    push_cast
    ring
  have himageClosed : f '' (Set.uIcc (0 : ℝ) Real.pi) ⊆ Icc (0 : ℝ) 1 := by
    rintro y ⟨x, hx, rfl⟩
    simp only [uIcc_of_le Real.pi_pos.le, mem_Icc] at hx
    dsimp [f]
    constructor <;> nlinarith [Real.cos_le_one x, Real.neg_one_le_cos x]
  have hg1 : IntegrableOn g (f '' (Set.uIcc (0 : ℝ) Real.pi)) := by
    have hgint : IntervalIntegrable g volume 0 1 := by
      dsimp [g]
      exact hkernel.const_mul ((2 : ℝ) ^ α)
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).1 hgint).mono_set himageClosed
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x)
      (Set.uIcc (0 : ℝ) Real.pi) := by
    have hsint : IntegrableOn (fun x : ℝ => Real.sin x ^ α)
        (Icc (0 : ℝ) Real.pi) :=
      (Real.continuous_sin.rpow_const (fun _ => Or.inr hα.le)).integrableOn_Icc
    rw [uIcc_of_le Real.pi_pos.le]
    refine hsint.congr_fun (fun x hx => ?_) measurableSet_Icc
    dsimp [g, f, f', p, Function.comp_apply]
    simpa only [show (α + 1) / 2 - 1 = (α - 1) / 2 by ring] using
      (symmetricBeta_substitution_integrand hα hx.1 hx.2).symm
  have hsub := intervalIntegral.integral_comp_mul_deriv''' hf hff' hg_cont hg1 hg2
  calc
    (∫ x : ℝ in (0)..Real.pi, Real.sin x ^ α) =
        ∫ x : ℝ in (0)..Real.pi, (g ∘ f) x * f' x := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [uIcc_of_le Real.pi_pos.le, mem_Icc] at hx
      dsimp [g, f, f', p, Function.comp_apply]
      simpa only [show (α + 1) / 2 - 1 = (α - 1) / 2 by ring] using
        (symmetricBeta_substitution_integrand hα hx.1 hx.2).symm
    _ = ∫ t : ℝ in (f 0)..(f Real.pi), g t := hsub
    _ = (2 : ℝ) ^ α * realSymmetricBetaIntegral ((α + 1) / 2) := by
      simp only [f, Real.cos_zero, Real.cos_pi, sub_self, zero_div, sub_neg_eq_add,
        one_add_one_eq_two, div_self (by norm_num : (2 : ℝ) ≠ 0)]
      rw [intervalIntegral.integral_const_mul]
      rfl

/-- The point of the unit additive circle represented by `j / w`. -/
noncomputable def rootPoint (w : ℕ) [NeZero w] (j : ZMod w) : AddCircle (1 : ℝ) :=
  ((((j.val : ℕ) : ℝ) / (w : ℝ) : ℝ) : AddCircle (1 : ℝ))

lemma fourier_rootPoint_eq_stdAddChar (w : ℕ) [NeZero w]
    (n : ℤ) (j : ZMod w) :
    @fourier (1 : ℝ) n (rootPoint w j) = ZMod.stdAddChar ((n : ZMod w) * j) := by
  rw [show (n : ZMod w) * j = n • j by simp [zsmul_eq_mul],
    AddChar.map_zsmul_eq_zpow]
  rw [rootPoint, fourier_coe_apply, ZMod.stdAddChar_apply,
    ZMod.toCircle_apply]
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  field_simp
  ring

/-- Orthogonality of characters on the `w`-point root grid. -/
theorem sum_fourier_rootPoint (w : ℕ) [NeZero w] (n : ℤ) :
    ∑ j : ZMod w, @fourier (1 : ℝ) n (rootPoint w j) =
      if (n : ZMod w) = 0 then (w : ℂ) else 0 := by
  simp_rw [fourier_rootPoint_eq_stdAddChar]
  have h := AddChar.sum_mulShift ((n : ZMod w))
    (ZMod.isPrimitive_stdAddChar w)
  by_cases hn : (n : ZMod w) = 0
  · rw [if_pos hn]
    simpa [hn, ZMod.card, mul_comm (n : ZMod w)] using h
  · rw [if_neg hn]
    simpa [hn, ZMod.card, mul_comm (n : ZMod w)] using h

theorem sum_fourier_rootPoint_of_dvd (w : ℕ) [NeZero w]
    (n : ℤ) (hn : (w : ℤ) ∣ n) :
    ∑ j : ZMod w, @fourier (1 : ℝ) n (rootPoint w j) = (w : ℂ) := by
  rw [sum_fourier_rootPoint, if_pos]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd n w).2 hn

theorem sum_fourier_rootPoint_of_not_dvd (w : ℕ) [NeZero w]
    (n : ℤ) (hn : ¬(w : ℤ) ∣ n) :
    ∑ j : ZMod w, @fourier (1 : ℝ) n (rootPoint w j) = 0 := by
  rw [sum_fourier_rootPoint, if_neg]
  exact fun h => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd n w).1 h)

/-- Sum of a continuous function over the complete `w`-point root grid. -/
noncomputable def rootGridSum (w : ℕ) [NeZero w]
    (f : C(AddCircle (1 : ℝ), ℂ)) : ℂ :=
  ∑ j : ZMod w, f (rootPoint w j)

/-- Exact root-grid alias identity in `HasSum` form.  Absolute summability of
the Fourier coefficients justifies summing the pointwise Fourier expansions
over the finite grid; character orthogonality then removes every frequency
not divisible by `w`. -/
theorem hasSum_fourierCoeff_filtered_by_rootGrid
    (w : ℕ) [NeZero w] (f : C(AddCircle (1 : ℝ), ℂ))
    (hs : Summable (fourierCoeff f)) :
    HasSum
      (fun n : ℤ =>
        if (n : ZMod w) = 0 then (w : ℂ) * fourierCoeff f n else 0)
      (rootGridSum w f) := by
  have hj : ∀ j ∈ (Finset.univ : Finset (ZMod w)),
      HasSum
        (fun n : ℤ => fourierCoeff f n •
          @fourier (1 : ℝ) n (rootPoint w j))
        (f (rootPoint w j)) := by
    intro j _
    exact has_pointwise_sum_fourier_series_of_summable hs (rootPoint w j)
  have hsum := hasSum_sum hj
  unfold rootGridSum
  refine HasSum.congr_fun hsum (fun n => ?_)
  simp only [smul_eq_mul]
  rw [← Finset.mul_sum]
  rw [sum_fourier_rootPoint]
  split_ifs <;> ring

/-- Tsum form of the exact root-grid alias identity. -/
theorem rootGridSum_eq_tsum_filtered_fourierCoeff
    (w : ℕ) [NeZero w] (f : C(AddCircle (1 : ℝ), ℂ))
    (hs : Summable (fourierCoeff f)) :
    rootGridSum w f =
      ∑' n : ℤ,
        if (n : ZMod w) = 0 then (w : ℂ) * fourierCoeff f n else 0 := by
  exact (hasSum_fourierCoeff_filtered_by_rootGrid w f hs).tsum_eq.symm

/-! ## A machine-checked sufficient criterion for the full circle limit -/

/-- The regular-polygon chord-power sum, in the manuscript's normalization. -/
noncomputable def circlePowerSum (α : ℝ) (w : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (w - 1),
    (2 * Real.sin (((k : ℝ) + 1) * (Real.pi / (w : ℝ)))) ^ α

/-- Full general-`α` circle Euler--Maclaurin statement. -/
def CircleEulerMaclaurin (α : ℝ) : Prop :=
  Tendsto
    (fun w : ℕ => (w : ℝ) ^ α *
      (circlePowerSum α w - (w : ℝ) * circleMoment α))
    atTop
    (𝓝 (2 * (2 * Real.pi) ^ α * realZeta (-α)))

/-- The exact normalized alias formula supplied by an absolutely convergent,
even Fourier expansion.  It is separated out so that the special-function
calculation and the generic Fourier argument have a sharp interface. -/
def HasNormalizedCircleAlias (α : ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ᶠ w : ℕ in atTop,
    (w : ℝ) ^ α *
        (circlePowerSum α w - (w : ℝ) * circleMoment α) =
      2 * scaledPositiveAliasTail α a w

/-- Fourier aliasing plus the cusp coefficient limit closes the complete
general-`α` endpoint Euler--Maclaurin theorem.  No Euler--Maclaurin formula is
used here: Tannery and the zeta functional equation do all remaining work. -/
theorem circleEulerMaclaurin_of_fourier_alias
    {α D : ℝ} {a : ℕ → ℝ} (hα : 0 < α)
    (hAlias : HasNormalizedCircleAlias α a)
    (hpoint : ∀ m : ℕ,
      Tendsto (fun w : ℕ => (w : ℝ) ^ (1 + α) * a ((m + 1) * w)) atTop
        (𝓝 (fourierCuspConstant α /
          ((m + 1 : ℕ) : ℝ) ^ (1 + α))))
    (hbound : ∀ᶠ w : ℕ in atTop, ∀ m : ℕ,
      ‖(w : ℝ) ^ (1 + α) * a ((m + 1) * w)‖ ≤
        D / ((m + 1 : ℕ) : ℝ) ^ (1 + α)) :
    CircleEulerMaclaurin α := by
  apply (tendsto_two_mul_scaledPositiveAliasTail hα hpoint hbound).congr'
  filter_upwards [hAlias] with w hw
  exact hw.symm

end BEMOC.CircleFourier
