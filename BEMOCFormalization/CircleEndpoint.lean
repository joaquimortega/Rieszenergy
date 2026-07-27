import BEMOCFormalization.EulerSmooth
import BEMOCFormalization.EulerPower

/-!
# General endpoint Euler--Maclaurin calculation for a circle

This module proves the singular endpoint-subtraction algebra and its smooth
Euler--Maclaurin remainder for Lemma 3.1 in `BEMOCRieszEnergies.tex`, without
importing the canonical root module or introducing axioms.
-/

open scoped BigOperators Topology Interval
open Filter Set MeasureTheory Complex

namespace BEMOC.CircleGeneral

/-- Chord length to the power `α` in unit-period angular coordinates. -/
noncomputable def circleProfile (α x : ℝ) : ℝ :=
  (2 * Real.sin (Real.pi * x)) ^ α

/-- The chord-power sum from one vertex of a regular `w`-gon. -/
noncomputable def circleChordPowerSum (α : ℝ) (w : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 w,
    (2 * Real.sin (Real.pi * (k : ℝ) / (w : ℝ))) ^ α

/-- The normalized angular average in Lemma 3.1. -/
noncomputable def angularAverage (α : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, circleProfile α x


/-! ## Elementary normalization facts -/

theorem circleChordPowerSum_zero (α : ℝ) :
    circleChordPowerSum α 0 = 0 := by
  simp [circleChordPowerSum]

theorem circleChordPowerSum_one (α : ℝ) :
    circleChordPowerSum α 1 = 0 := by
  simp [circleChordPowerSum]

theorem circleChordPowerSum_eq_profile_mesh (α : ℝ) (w : ℕ) :
    circleChordPowerSum α w =
      ∑ k ∈ Finset.Ico 1 w, circleProfile α ((k : ℝ) / (w : ℝ)) := by
  apply Finset.sum_congr rfl
  intro k _
  unfold circleProfile
  congr 2
  ring

/-! ## Explicit singular endpoint subtraction -/

/-- Symmetric endpoint model.  The quadratic term makes both ordinary first
derivatives match; this is the cancellation needed when `1 < β`. -/
noncomputable def endpointModel (β x : ℝ) : ℝ :=
  x ^ β + (1 - x) ^ β - 1 + β * x * (1 - x)

/-- The leading singular term of `(2 sin (πx))^α` at both endpoints,
including the quadratic correction that cancels the ordinary `B₂` term. -/
noncomputable def circleEndpointResidual (α x : ℝ) : ℝ :=
  circleProfile α x
    - (2 * Real.pi) ^ α * endpointModel α x

@[simp] theorem endpointModel_zero {β : ℝ} (hβ : 0 < β) :
    endpointModel β 0 = 0 := by
  simp [endpointModel, Real.zero_rpow hβ.ne']

@[simp] theorem endpointModel_one {β : ℝ} (hβ : 0 < β) :
    endpointModel β 1 = 0 := by
  simp [endpointModel, Real.zero_rpow hβ.ne']

theorem circleEndpointResidual_zero {α : ℝ} (hα : 0 < α) :
    circleEndpointResidual α 0 = 0 := by
  simp [circleEndpointResidual, circleProfile, endpointModel, hα,
    Real.zero_rpow hα.ne']

theorem circleEndpointResidual_one {α : ℝ} (hα : 0 < α) :
    circleEndpointResidual α 1 = 0 := by
  simp [circleEndpointResidual, circleProfile, endpointModel, hα,
    Real.zero_rpow hα.ne']

/-- Scaling a power sum from the integer mesh to `[0,1]`. -/
theorem sum_mesh_rpow (β : ℝ) (w : ℕ) (hw : 0 < w) :
    (∑ k ∈ Finset.Ico 1 w, ((k : ℝ) / (w : ℝ)) ^ β) =
      (w : ℝ) ^ (-β) * EulerPower.powerSum β w := by
  unfold EulerPower.powerSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Real.div_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg w)]
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  rw [Real.rpow_neg hwR.le]
  ring

/-- Reflection exchanges the two endpoint power sums. -/
theorem sum_mesh_one_sub_rpow (β : ℝ) (w : ℕ) (hw : 0 < w) :
    (∑ k ∈ Finset.Ico 1 w, (1 - (k : ℝ) / (w : ℝ)) ^ β) =
      ∑ k ∈ Finset.Ico 1 w, ((k : ℝ) / (w : ℝ)) ^ β := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have href := Finset.sum_range_reflect
    (fun k : ℕ => (((k + 1 : ℕ) : ℝ) / (w : ℝ)) ^ β) (w - 1)
  calc
    (∑ k ∈ Finset.range (w - 1), (1 - (↑(1 + k) / ↑w : ℝ)) ^ β) =
        ∑ k ∈ Finset.range (w - 1),
          ((↑(w - 1 - 1 - k + 1) / ↑w : ℝ) ^ β) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < w - 1 := Finset.mem_range.mp hk
      congr 2
      have heq : w - 1 - 1 - k + 1 = w - (1 + k) := by omega
      rw [heq, Nat.cast_sub (by omega : 1 + k ≤ w)]
      push_cast
      field_simp
    _ = ∑ k ∈ Finset.range (w - 1), ((↑(k + 1) / ↑w : ℝ) ^ β) := href
    _ = ∑ k ∈ Finset.range (w - 1), ((↑(1 + k) / ↑w : ℝ) ^ β) := by
      simp only [add_comm]

private theorem sum_range_cast_id (w : ℕ) :
    (∑ k ∈ Finset.range w, (k : ℝ)) =
      (w : ℝ) * ((w : ℝ) - 1) / 2 := by
  induction w with
  | zero => simp
  | succ w ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_range_cast_sq (w : ℕ) :
    (∑ k ∈ Finset.range w, (k : ℝ) ^ 2) =
      (w : ℝ) * ((w : ℝ) - 1) * (2 * (w : ℝ) - 1) / 6 := by
  induction w with
  | zero => simp
  | succ w ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem sum_mesh_mul_one_sub (w : ℕ) (hw : 0 < w) :
    (∑ k ∈ Finset.Ico 1 w,
      ((k : ℝ) / (w : ℝ)) * (1 - (k : ℝ) / (w : ℝ))) =
      ((w : ℝ) ^ 2 - 1) / (6 * (w : ℝ)) := by
  have hw1 : 1 ≤ w := hw
  rw [Finset.sum_Ico_eq_sub (fun k : ℕ =>
    ((k : ℝ) / (w : ℝ)) * (1 - (k : ℝ) / (w : ℝ))) hw1]
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_div, zero_mul, sub_zero]
  simp_rw [mul_sub, mul_one, div_mul_eq_div_mul_one_div,
    ← pow_two, div_pow]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    sum_range_cast_id, sum_range_cast_sq]
  field_simp
  ring

/-- Exact finite-mesh evaluation of the symmetric endpoint model. -/
theorem sum_endpointModel (β : ℝ) (w : ℕ) (hw : 0 < w) :
    (∑ k ∈ Finset.Ico 1 w,
      endpointModel β ((k : ℝ) / (w : ℝ))) =
      2 * (w : ℝ) ^ (-β) * EulerPower.powerSum β w - ((w : ℝ) - 1) +
        β * (((w : ℝ) ^ 2 - 1) / (6 * (w : ℝ))) := by
  unfold endpointModel
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_mesh_one_sub_rpow β w hw,
    sum_mesh_rpow β w hw]
  have hfactor :
      (∑ x ∈ Finset.Ico 1 w,
        β * ((x : ℝ) / (w : ℝ)) * (1 - (x : ℝ) / (w : ℝ))) =
        β * ∑ x ∈ Finset.Ico 1 w,
          ((x : ℝ) / (w : ℝ)) * (1 - (x : ℝ) / (w : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hfactor]
  rw [sum_mesh_mul_one_sub w hw]
  simp
  rw [Nat.cast_sub (by omega : 1 ≤ w)]
  push_cast
  ring

/-- Exact integral of the symmetric endpoint model. -/
theorem integral_endpointModel {β : ℝ} (hβ : 0 < β) :
    (∫ x in (0 : ℝ)..1, endpointModel β x) =
      2 / (β + 1) - 1 + β / 6 := by
  have hpow : IntervalIntegrable (fun x : ℝ => x ^ β) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_id.rpow continuousOn_const
      (fun _ _ => Or.inr hβ)
  have hpow' : IntervalIntegrable (fun x : ℝ => (1 - x) ^ β) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_const.sub continuousOn_id).rpow continuousOn_const
      (fun _ _ => Or.inr hβ)
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hpoly : IntervalIntegrable
      (fun x : ℝ => β * x * (1 - x)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hlin : IntervalIntegrable (fun x : ℝ => β * x) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hquad : IntervalIntegrable (fun x : ℝ => β * x ^ 2) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpolyval :
      (∫ x in (0 : ℝ)..1, β * x * (1 - x)) = β / 6 := by
    rw [show (fun x : ℝ => β * x * (1 - x)) =
        fun x : ℝ => β * x - β * x ^ 2 by funext x; ring]
    rw [intervalIntegral.integral_sub hlin hquad]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    norm_num [integral_pow]
    ring
  unfold endpointModel
  rw [intervalIntegral.integral_add ((hpow.add hpow').sub hone) hpoly,
    intervalIntegral.integral_sub (hpow.add hpow') hone,
    intervalIntegral.integral_add hpow hpow']
  have hp : (∫ x in (0 : ℝ)..1, x ^ β) = 1 / (β + 1) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < β))]
    have hβ1 : 0 < β + 1 := by linarith
    simp [Real.zero_rpow hβ1.ne']
  have hp' : (∫ x in (0 : ℝ)..1, (1 - x) ^ β) = 1 / (β + 1) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ β) 1]
    simpa using hp
  rw [hp, hp']
  rw [hpolyval]
  norm_num
  ring

/-- The endpoint model contributes exactly twice the corrected canonical
power sum.  This is the singular algebra at the heart of Lemma 3.1. -/
theorem endpointModel_mesh_error_eq_renormalized
    {β : ℝ} (hβ : 0 < β) (w : ℕ) (hw : 0 < w) :
    (∑ k ∈ Finset.Ico 1 w,
        endpointModel β ((k : ℝ) / (w : ℝ))) -
      (w : ℝ) * (∫ x in (0 : ℝ)..1, endpointModel β x) =
      2 * (w : ℝ) ^ (-β) * EulerPower.renormalizedPowerSum β w := by
  rw [sum_endpointModel β w hw, integral_endpointModel hβ]
  unfold EulerPower.renormalizedPowerSum
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have h1 : (w : ℝ) ^ (-β) * (w : ℝ) ^ (β + 1) = (w : ℝ) := by
    rw [← Real.rpow_add hwR]
    convert Real.rpow_one (w : ℝ) using 2 <;> ring
  have h0 : (w : ℝ) ^ (-β) * (w : ℝ) ^ β = 1 := by
    rw [← Real.rpow_add hwR]
    convert Real.rpow_zero (w : ℝ) using 2 <;> ring
  have hm1 : (w : ℝ) ^ (-β) * (w : ℝ) ^ (β - 1) =
      1 / (w : ℝ) := by
    rw [← Real.rpow_add hwR]
    rw [show -β + (β - 1) = (-1 : ℝ) by ring, Real.rpow_neg_one]
    simp only [one_div]
  have hβ1 : β + 1 ≠ 0 := by linarith
  have hleft :
      2 * (w : ℝ) ^ (-β) * EulerPower.powerSum β w - ((w : ℝ) - 1) +
          β * (((w : ℝ) ^ 2 - 1) / (6 * (w : ℝ))) -
          (w : ℝ) * (2 / (β + 1) - 1 + β / 6) =
        2 * (w : ℝ) ^ (-β) * EulerPower.powerSum β w -
          2 * (w : ℝ) / (β + 1) + 1 - β / (6 * (w : ℝ)) := by
    field_simp [hwR.ne', hβ1]
    ring
  have hright :
      2 * (w : ℝ) ^ (-β) *
          (EulerPower.powerSum β w -
            (w : ℝ) ^ (β + 1) / (β + 1) +
            (1 / 2 : ℝ) * (w : ℝ) ^ β -
            (β / 12) * (w : ℝ) ^ (β - 1)) =
        2 * (w : ℝ) ^ (-β) * EulerPower.powerSum β w -
          2 * (w : ℝ) / (β + 1) + 1 - β / (6 * (w : ℝ)) := by
    calc
      _ = 2 * (w : ℝ) ^ (-β) * EulerPower.powerSum β w -
            2 * ((w : ℝ) ^ (-β) * (w : ℝ) ^ (β + 1)) / (β + 1) +
            ((w : ℝ) ^ (-β) * (w : ℝ) ^ β) -
            β / 6 * ((w : ℝ) ^ (-β) * (w : ℝ) ^ (β - 1)) := by ring
      _ = _ := by
        rw [h1, h0, hm1]
        field_simp [hwR.ne']
  exact hleft.trans hright.symm

theorem circleProfile_intervalIntegrable {α : ℝ} (hα : 0 < α) :
    IntervalIntegrable (circleProfile α) volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  unfold circleProfile
  have hb : Continuous (fun x : ℝ => 2 * Real.sin (Real.pi * x)) := by
    fun_prop
  exact hb.continuousOn.rpow continuousOn_const
    (fun _ _ => Or.inr hα)

theorem endpointModel_intervalIntegrable {β : ℝ} (hβ : 0 < β) :
    IntervalIntegrable (endpointModel β) volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  unfold endpointModel
  have hx : ContinuousOn (fun x : ℝ => x ^ β) (Icc (0 : ℝ) 1) :=
    continuousOn_id.rpow continuousOn_const (fun _ _ => Or.inr hβ)
  have h1x : ContinuousOn (fun x : ℝ => (1 - x) ^ β) (Icc (0 : ℝ) 1) :=
    (continuousOn_const.sub continuousOn_id).rpow continuousOn_const
      (fun _ _ => Or.inr hβ)
  have honeC : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) 1) :=
    continuousOn_const
  have hβC : ContinuousOn (fun _ : ℝ => β) (Icc (0 : ℝ) 1) :=
    continuousOn_const
  simpa only [id_eq] using
    ((hx.add h1x).sub honeC).add
      ((hβC.mul continuousOn_id).mul (honeC.sub continuousOn_id))

theorem circleEndpointResidual_intervalIntegrable {α : ℝ} (hα : 0 < α) :
    IntervalIntegrable (circleEndpointResidual α) volume (0 : ℝ) 1 := by
  unfold circleEndpointResidual
  exact (circleProfile_intervalIntegrable hα).sub
    ((endpointModel_intervalIntegrable hα).const_mul _)

/-- The actual mesh error of the endpoint-subtracted profile. -/
noncomputable def endpointResidualMeshError (α : ℝ) (w : ℕ) : ℝ :=
  (∑ k ∈ Finset.Ico 1 w,
      circleEndpointResidual α ((k : ℝ) / (w : ℝ))) -
    (w : ℝ) * (∫ x in (0 : ℝ)..1, circleEndpointResidual α x)

/-- Exact finite-`w` decomposition into the canonical singular power model
and the residual to which `BEMOCEulerSmooth` applies. -/
theorem circle_mesh_error_decomposition
    {α : ℝ} (hα : 0 < α) (w : ℕ) :
    circleChordPowerSum α w - (w : ℝ) * angularAverage α =
      (2 * Real.pi) ^ α *
        ((∑ k ∈ Finset.Ico 1 w,
            endpointModel α ((k : ℝ) / (w : ℝ))) -
          (w : ℝ) * (∫ x in (0 : ℝ)..1, endpointModel α x)) +
        endpointResidualMeshError α w := by
  have hsum :
      (∑ k ∈ Finset.Ico 1 w, circleProfile α ((k : ℝ) / (w : ℝ))) =
        (2 * Real.pi) ^ α *
          (∑ k ∈ Finset.Ico 1 w,
            endpointModel α ((k : ℝ) / (w : ℝ))) +
          ∑ k ∈ Finset.Ico 1 w,
            circleEndpointResidual α ((k : ℝ) / (w : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    unfold circleEndpointResidual
    ring
  have hintResidual := intervalIntegral.integral_sub
    (circleProfile_intervalIntegrable hα)
    ((endpointModel_intervalIntegrable hα).const_mul ((2 * Real.pi) ^ α))
  have hintResidual' :
      (∫ x in (0 : ℝ)..1, circleEndpointResidual α x) =
        (∫ x in (0 : ℝ)..1, circleProfile α x) -
          (2 * Real.pi) ^ α *
            (∫ x in (0 : ℝ)..1, endpointModel α x) := by
    unfold circleEndpointResidual
    simpa only [intervalIntegral.integral_const_mul] using hintResidual
  have hint :
      (∫ x in (0 : ℝ)..1, circleProfile α x) =
        (2 * Real.pi) ^ α *
          (∫ x in (0 : ℝ)..1, endpointModel α x) +
        ∫ x in (0 : ℝ)..1, circleEndpointResidual α x := by
    rw [hintResidual']
    ring
  rw [circleChordPowerSum_eq_profile_mesh,
    angularAverage, hsum, hint]
  unfold endpointResidualMeshError
  ring

/-- Precise local regularity package still needed for the explicit residual.
It permits an auxiliary global extension because the canonical smooth theorem
is formulated with global first derivatives; only equality on `[0,1]` enters
the mesh and integral. -/
structure EndpointResidualData (α : ℝ) where
  g : ℝ → ℝ
  deriv1 : ℝ → ℝ
  deriv2 : ℝ → ℝ
  deriv3 : ℝ → ℝ
  eqOn : ∀ x ∈ Icc (0 : ℝ) 1, g x = circleEndpointResidual α x
  hasDeriv : ∀ x, HasDerivAt g (deriv1 x) x
  hasDeriv' : ∀ x, HasDerivAt deriv1 (deriv2 x) x
  continuousOn_second : ContinuousOn deriv2 (Icc (0 : ℝ) 1)
  hasDeriv_second : ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt deriv2 (deriv3 x) x
  third_integrable : IntervalIntegrable deriv3 volume (0 : ℝ) 1
  deriv_endpoints : deriv1 1 = deriv1 0

theorem EulerSmooth.interiorMeshSum_eq_Ico
    (g : ℝ → ℝ) (w : ℕ) :
    EulerSmooth.interiorMeshSum g w =
      ∑ k ∈ Finset.Ico 1 w, g ((k : ℝ) / (w : ℝ)) := by
  rw [Finset.sum_Ico_eq_sum_range]
  unfold EulerSmooth.interiorMeshSum
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  push_cast
  ring

/-- Machine-checked application of `BEMOCEulerSmooth`: the explicit endpoint
residual has the required `o(w⁻α)` mesh error as soon as the local derivative
and `L¹` package above is supplied. -/
theorem endpointResidualMeshError_isLittleO
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (d : EndpointResidualData α) :
    endpointResidualMeshError α =o[atTop]
      (fun w : ℕ => (w : ℝ) ^ (-α)) := by
  have hg0 : d.g 0 = 0 := by
    rw [d.eqOn 0 ⟨le_rfl, zero_le_one⟩,
      circleEndpointResidual_zero hα0]
  have hg1 : d.g 1 = 0 := by
    rw [d.eqOn 1 ⟨zero_le_one, le_rfl⟩,
      circleEndpointResidual_one hα0]
  have hbase := EulerSmooth.interiorMeshSum_sub_integral_isLittleO_of_integrable
    hα0 hα2 d.hasDeriv d.hasDeriv' d.continuousOn_second
      d.hasDeriv_second d.third_integrable hg0 hg1 d.deriv_endpoints
  have hint :
      (∫ x in (0 : ℝ)..1, d.g x) =
        ∫ x in (0 : ℝ)..1, circleEndpointResidual α x := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply d.eqOn x
    simpa only [uIcc_of_le zero_le_one] using hx
  have heq : endpointResidualMeshError α =ᶠ[atTop]
      (fun w : ℕ => EulerSmooth.interiorMeshSum d.g w -
        (w : ℝ) * (∫ x in (0 : ℝ)..1, d.g x)) := by
    filter_upwards [eventually_ge_atTop 1] with w hw
    have hwpos : 0 < w := Nat.zero_lt_of_lt hw
    unfold endpointResidualMeshError
    rw [EulerSmooth.interiorMeshSum_eq_Ico, hint]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    apply (d.eqOn _ ?_).symm
    have hk' := Finset.mem_Ico.mp hk
    have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hwpos
    constructor
    · positivity
    · rw [div_le_one hwR]
      exact_mod_cast hk'.2.le
  exact hbase.congr' heq.symm EventuallyEq.rfl

/-- Abstract `SmoothEndpointSubtraction`: after removing the canonical
renormalized power sum, the normalized circle error tends to zero from an
`EndpointResidualData` package.  The explicit package is constructed in
`EndpointResidualData.lean`. -/
theorem smoothEndpointSubtraction_of_data
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (d : EndpointResidualData α) :
    Tendsto
      (fun w : ℕ =>
        (w : ℝ) ^ α *
            (circleChordPowerSum α w - (w : ℝ) * angularAverage α) -
          2 * (2 * Real.pi) ^ α *
            EulerPower.renormalizedPowerSum α w)
      atTop (𝓝 0) := by
  have hres := endpointResidualMeshError_isLittleO hα0 hα2 d
  have hdiv := hres.tendsto_div_nhds_zero
  have hscaled : Tendsto
      (fun w : ℕ => (w : ℝ) ^ α * endpointResidualMeshError α w)
      atTop (𝓝 0) := by
    refine hdiv.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with w hw
    have hwR : (0 : ℝ) < (w : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hw)
    rw [Real.rpow_neg hwR.le]
    field_simp [(Real.rpow_pos_of_pos hwR α).ne']
    ring
  refine hscaled.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with w hw
  have hwpos : 0 < w := Nat.zero_lt_of_lt hw
  have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hwpos
  rw [circle_mesh_error_decomposition hα0,
    endpointModel_mesh_error_eq_renormalized hα0 w hwpos]
  have hpow : (w : ℝ) ^ α * (w : ℝ) ^ (-α) = 1 := by
    rw [← Real.rpow_add hwR]
    norm_num
  linear_combination
    -2 * (2 * Real.pi) ^ α * EulerPower.renormalizedPowerSum α w * hpow

end BEMOC.CircleGeneral
