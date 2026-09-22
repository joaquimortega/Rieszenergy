import BEMOCFormalization.LatitudeWeakSingularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Derivatives of the universal reduced latitude cusp

For a positive gap parameter the angular cusp is smooth.  This file
justifies differentiation under the angular integral and records the exact
derivative recurrence.  Iterating it gives the fourth derivative as an
explicit singular angular moment, which is the direct-integral starting
point for the local branch expansion.
-/

open scoped BigOperators
open scoped Topology Interval
open MeasureTheory Set Filter Metric

namespace BEMOC

/-- Angular cusp moment with arbitrary exponent. -/
noncomputable def reducedCuspMoment (β x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ θ in (0 : ℝ)..2 * Real.pi,
      (x + (1 - Real.cos θ)) ^ β

theorem reducedLatitudeCusp_eq_moment (α x : ℝ) :
    reducedLatitudeCusp α x = reducedCuspMoment (α / 2) x := rfl

theorem reducedCuspMoment_nonneg
    {β x : ℝ} (hx : 0 ≤ x) :
    0 ≤ reducedCuspMoment β x := by
  unfold reducedCuspMoment
  apply mul_nonneg
  · positivity
  · apply intervalIntegral.integral_nonneg
    · positivity
    · intro θ _
      exact Real.rpow_nonneg
        (add_nonneg hx (sub_nonneg.mpr (Real.cos_le_one θ))) _

/-- A simple but uniform off-diagonal moment bound.  For a nonpositive
exponent, dropping the angular contribution can only increase the
integrand. -/
theorem reducedCuspMoment_le_gap_rpow
    {β x : ℝ} (hx : 0 < x) (hβ : β ≤ 0) :
    reducedCuspMoment β x ≤ x ^ β := by
  let f : ℝ → ℝ := fun θ ↦ (x + (1 - Real.cos θ)) ^ β
  have hfcont : Continuous f := by
    dsimp [f]
    exact
      (continuous_const.add
        (continuous_const.sub Real.continuous_cos)).rpow_const
          (fun θ ↦ Or.inl (by
            have : 0 < x + (1 - Real.cos θ) := by
              have := sub_nonneg.mpr (Real.cos_le_one θ)
              linarith
            exact this.ne'))
  have hpoint (θ : ℝ) :
      f θ ≤ x ^ β := by
    dsimp [f]
    apply Real.rpow_le_rpow_of_nonpos hx
    · exact le_add_of_nonneg_right
        (sub_nonneg.mpr (Real.cos_le_one θ))
    · exact hβ
  have hmono :=
    intervalIntegral.integral_mono_on
      (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
      (f := f) (g := fun _ : ℝ ↦ x ^ β)
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hfcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
      (fun θ _ ↦ hpoint θ)
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  unfold reducedCuspMoment
  change (1 / (2 * Real.pi)) *
      (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) ≤ x ^ β
  calc
    (1 / (2 * Real.pi)) *
        (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) ≤
      (1 / (2 * Real.pi)) *
        (∫ _θ in (0 : ℝ)..2 * Real.pi, x ^ β) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = x ^ β := by
      rw [intervalIntegral.integral_const]
      field_simp

/-- Absolute version of the preceding bound after multiplication by an
arbitrary coefficient. -/
theorem abs_mul_reducedCuspMoment_le
    {c β x : ℝ} (hx : 0 < x) (hβ : β ≤ 0) :
    |c * reducedCuspMoment β x| ≤ |c| * x ^ β := by
  rw [abs_mul, abs_of_nonneg (reducedCuspMoment_nonneg hx.le)]
  exact mul_le_mul_of_nonneg_left
    (reducedCuspMoment_le_gap_rpow hx hβ) (abs_nonneg c)

/-- Exact elementary integral used to extract the half-power gain from a
quadratic angular lower bound. -/
theorem integral_inv_add_mul_sq_eq
    {x c a b : ℝ} (hx : 0 < x) (hc : 0 < c) :
    (∫ θ in a..b, (x + c * θ ^ 2)⁻¹) =
      x⁻¹ * (Real.sqrt (c / x))⁻¹ *
        (Real.arctan (b * Real.sqrt (c / x)) -
          Real.arctan (a * Real.sqrt (c / x))) := by
  let k : ℝ := Real.sqrt (c / x)
  have hk : 0 < k := by
    dsimp [k]
    positivity
  have hk2 : k ^ 2 = c / x := by
    dsimp [k]
    rw [Real.sq_sqrt]
    positivity
  have hkc : x * k ^ 2 = c := by
    rw [hk2]
    field_simp [hx.ne']
  have hpoint (θ : ℝ) :
      (x + c * θ ^ 2)⁻¹ =
        x⁻¹ * (1 + (θ * k) ^ 2)⁻¹ := by
    have hx0 : x ≠ 0 := hx.ne'
    have hsum : x + c * θ ^ 2 ≠ 0 := by positivity
    have hone : 1 + (θ * k) ^ 2 ≠ 0 := by positivity
    field_simp [hx0, hsum, hone]
    calc
      x * (1 + (θ * k) ^ 2) =
          x + (x * k ^ 2) * θ ^ 2 := by ring
      _ = x + c * θ ^ 2 := by rw [hkc]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_right
    (fun u : ℝ ↦ (1 + u ^ 2)⁻¹) hk.ne']
  simp only [smul_eq_mul]
  rw [integral_inv_one_add_sq]
  dsimp [k]
  ring

/-- Centered reciprocal-quadratic integral bound. -/
theorem integral_inv_add_mul_sq_le
    {x c L : ℝ} (hx : 0 < x) (hc : 0 < c) (_hL : 0 ≤ L) :
    (∫ θ in (-L)..L, (x + c * θ ^ 2)⁻¹) ≤
      x⁻¹ * (Real.sqrt (c / x))⁻¹ * Real.pi := by
  rw [integral_inv_add_mul_sq_eq hx hc]
  have hk : 0 < Real.sqrt (c / x) := by positivity
  have hupper :
      Real.arctan (L * Real.sqrt (c / x)) < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hlower :
      -(Real.pi / 2) <
        Real.arctan ((-L) * Real.sqrt (c / x)) :=
    Real.neg_pi_div_two_lt_arctan _
  have hdiff :
      Real.arctan (L * Real.sqrt (c / x)) -
          Real.arctan ((-L) * Real.sqrt (c / x)) ≤ Real.pi := by
    linarith
  exact mul_le_mul_of_nonneg_left hdiff (by positivity)

/-- Sharp half-power moment bound obtained from the quadratic lower bound
for `1 - cos θ`.  It is stated in an unsimplified scale form to keep all
normalizations exact:
`x^(γ+1) x⁻¹ sqrt((2/π²)/x)⁻¹` is a constant multiple of
`x^(γ+1/2)`. -/
theorem reducedCuspMoment_le_halfPowerScale
    {γ x : ℝ} (hx : 0 < x) (hγ : γ ≤ -1) :
    reducedCuspMoment γ x ≤
      (1 / 2) * x ^ (γ + 1) * x⁻¹ *
        (Real.sqrt ((2 / Real.pi ^ 2) / x))⁻¹ := by
  let c : ℝ := 2 / Real.pi ^ 2
  let f : ℝ → ℝ := fun θ ↦ (x + (1 - Real.cos θ)) ^ γ
  let g : ℝ → ℝ :=
    fun θ ↦ x ^ (γ + 1) * (x + c * θ ^ 2)⁻¹
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hfper : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp [f]
    rw [Real.cos_add_two_pi]
  have hcenter :
      (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) =
        ∫ θ in (-Real.pi)..Real.pi, f θ := by
    have h := hfper.intervalIntegral_add_eq (-Real.pi) 0
    symm
    convert h using 1 <;> ring_nf
  have hfcont : Continuous f := by
    dsimp [f]
    exact
      (continuous_const.add
        (continuous_const.sub Real.continuous_cos)).rpow_const
          (fun θ ↦ Or.inl (by
            have : 0 < x + (1 - Real.cos θ) := by
              have := sub_nonneg.mpr (Real.cos_le_one θ)
              linarith
            exact this.ne'))
  have hgcont : Continuous g := by
    dsimp [g]
    apply continuous_const.mul
    apply
      (continuous_const.add
        (continuous_const.mul (continuous_id.pow 2))).inv₀
    intro θ
    positivity
  have hpoint :
      ∀ θ ∈ Icc (-Real.pi) Real.pi, f θ ≤ g θ := by
    intro θ hθ
    have habs : |θ| ≤ Real.pi := abs_le.mpr hθ
    have hcos := Real.cos_le_one_sub_mul_cos_sq habs
    have hquad : c * θ ^ 2 ≤ 1 - Real.cos θ := by
      dsimp [c]
      linarith
    have hq : 0 < x + c * θ ^ 2 := by positivity
    have hz : 0 < x + (1 - Real.cos θ) := by
      have := sub_nonneg.mpr (Real.cos_le_one θ)
      linarith
    have hqz : x + c * θ ^ 2 ≤ x + (1 - Real.cos θ) := by linarith
    have hγ0 : γ ≤ 0 := hγ.trans (by norm_num)
    have hfirst :
        (x + (1 - Real.cos θ)) ^ γ ≤ (x + c * θ ^ 2) ^ γ :=
      Real.rpow_le_rpow_of_nonpos hq hqz hγ0
    have hqpow :
        (x + c * θ ^ 2) ^ (γ + 1) ≤ x ^ (γ + 1) := by
      apply Real.rpow_le_rpow_of_nonpos hx
      · nlinarith [hc.le, sq_nonneg θ]
      · linarith
    have hsplit :
        (x + c * θ ^ 2) ^ γ =
          (x + c * θ ^ 2) ^ (γ + 1) *
            (x + c * θ ^ 2)⁻¹ := by
      calc
        (x + c * θ ^ 2) ^ γ =
            (x + c * θ ^ 2) ^ ((γ + 1) + (-1 : ℝ)) := by
              congr 1
              ring
        _ = (x + c * θ ^ 2) ^ (γ + 1) *
            (x + c * θ ^ 2) ^ (-1 : ℝ) :=
              Real.rpow_add hq (γ + 1) (-1)
        _ = _ := by rw [Real.rpow_neg_one]
    dsimp [f, g]
    calc
      (x + (1 - Real.cos θ)) ^ γ ≤
          (x + c * θ ^ 2) ^ γ := hfirst
      _ = (x + c * θ ^ 2) ^ (γ + 1) *
          (x + c * θ ^ 2)⁻¹ := hsplit
      _ ≤ x ^ (γ + 1) * (x + c * θ ^ 2)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hqpow (inv_nonneg.mpr hq.le)
  have hmono :=
    intervalIntegral.integral_mono_on
      (μ := volume) (a := -Real.pi) (b := Real.pi)
      (f := f) (g := g)
      (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)
      (hfcont.intervalIntegrable _ _)
      (hgcont.intervalIntegrable _ _)
      hpoint
  have hinv :=
    integral_inv_add_mul_sq_le
      (x := x) (c := c) (L := Real.pi) hx hc Real.pi_pos.le
  have hxpow : 0 ≤ x ^ (γ + 1) := Real.rpow_nonneg hx.le _
  have hgint :
      (∫ θ in (-Real.pi)..Real.pi, g θ) ≤
        x ^ (γ + 1) *
          (x⁻¹ * (Real.sqrt (c / x))⁻¹ * Real.pi) := by
    dsimp [g]
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hinv hxpow
  unfold reducedCuspMoment
  change (1 / (2 * Real.pi)) *
      (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) ≤ _
  rw [hcenter]
  calc
    (1 / (2 * Real.pi)) *
        (∫ θ in (-Real.pi)..Real.pi, f θ) ≤
      (1 / (2 * Real.pi)) *
        (∫ θ in (-Real.pi)..Real.pi, g θ) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ (1 / (2 * Real.pi)) *
        (x ^ (γ + 1) *
          (x⁻¹ * (Real.sqrt (c / x))⁻¹ * Real.pi)) :=
      mul_le_mul_of_nonneg_left hgint (by positivity)
    _ = (1 / 2) * x ^ (γ + 1) * x⁻¹ *
        (Real.sqrt ((2 / Real.pi ^ 2) / x))⁻¹ := by
      dsimp [c]
      field_simp [Real.pi_ne_zero]
      ; ring

/-- Simplification of the exact half-power scale. -/
theorem halfPowerScale_eq_rpow
    {γ x : ℝ} (hx : 0 < x) :
    (1 / 2) * x ^ (γ + 1) * x⁻¹ *
        (Real.sqrt ((2 / Real.pi ^ 2) / x))⁻¹ =
      (Real.pi / (2 * Real.sqrt 2)) * x ^ (γ + 1 / 2) := by
  have hsqrt :
      Real.sqrt ((2 / Real.pi ^ 2) / x) =
        Real.sqrt 2 / (Real.pi * Real.sqrt x) := by
    rw [Real.sqrt_div (by positivity : 0 ≤ 2 / Real.pi ^ 2)]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos Real.pi_pos]
    ring
  have hpow :
      x ^ (γ + 1) * x⁻¹ * Real.sqrt x =
        x ^ (γ + 1 / 2) := by
    rw [← Real.rpow_neg_one x, Real.sqrt_eq_rpow]
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    ring
  rw [hsqrt]
  have hinv :
      (Real.sqrt 2 / (Real.pi * Real.sqrt x))⁻¹ =
        Real.pi * Real.sqrt x / Real.sqrt 2 := by
    rw [inv_div]
  rw [hinv]
  calc
    (1 / 2) * x ^ (γ + 1) * x⁻¹ *
          (Real.pi * Real.sqrt x / Real.sqrt 2) =
        (Real.pi / (2 * Real.sqrt 2)) *
          (x ^ (γ + 1) * x⁻¹ * Real.sqrt x) := by ring
    _ = (Real.pi / (2 * Real.sqrt 2)) * x ^ (γ + 1 / 2) := by
      rw [hpow]

/-- Clean power form of the sharp moment estimate. -/
theorem reducedCuspMoment_le_rpow_half
    {γ x : ℝ} (hx : 0 < x) (hγ : γ ≤ -1) :
    reducedCuspMoment γ x ≤
      (Real.pi / (2 * Real.sqrt 2)) * x ^ (γ + 1 / 2) := by
  rw [← halfPowerScale_eq_rpow hx]
  exact reducedCuspMoment_le_halfPowerScale hx hγ

/-- Absolute coefficient form of the sharp half-power estimate. -/
theorem abs_mul_reducedCuspMoment_le_halfPowerScale
    {c γ x : ℝ} (hx : 0 < x) (hγ : γ ≤ -1) :
    |c * reducedCuspMoment γ x| ≤
      |c| * ((1 / 2) * x ^ (γ + 1) * x⁻¹ *
        (Real.sqrt ((2 / Real.pi ^ 2) / x))⁻¹) := by
  rw [abs_mul, abs_of_nonneg (reducedCuspMoment_nonneg hx.le)]
  exact mul_le_mul_of_nonneg_left
    (reducedCuspMoment_le_halfPowerScale hx hγ) (abs_nonneg c)

/-- Values of the second, third and fourth derivatives of the universal
reduced latitude cusp at a positive gap. -/
noncomputable def reducedLatitudeCuspD1Value (α x : ℝ) : ℝ :=
  (α / 2) * reducedCuspMoment (α / 2 - 1) x

noncomputable def reducedLatitudeCuspD2Value (α x : ℝ) : ℝ :=
  (α / 2) * (α / 2 - 1) *
    reducedCuspMoment (α / 2 - 2) x

noncomputable def reducedLatitudeCuspD3Value (α x : ℝ) : ℝ :=
  (α / 2) * (α / 2 - 1) * (α / 2 - 2) *
    reducedCuspMoment (α / 2 - 3) x

noncomputable def reducedLatitudeCuspD4Value (α x : ℝ) : ℝ :=
  (α / 2) * (α / 2 - 1) * (α / 2 - 2) * (α / 2 - 3) *
    reducedCuspMoment (α / 2 - 4) x

/-- A robust first-derivative bound.  At the resonant value `α = 1` the
true growth is logarithmic; this power majorant is deliberately coarser but
uniform and sufficient when the term is multiplied by higher derivatives
of the quadratic gap. -/
theorem abs_reducedLatitudeCuspD1Value_le
    {α x : ℝ} (hx : 0 < x) (hα : α ≤ 2) :
    |reducedLatitudeCuspD1Value α x| ≤
      |α / 2| * x ^ (α / 2 - 1) := by
  unfold reducedLatitudeCuspD1Value
  apply abs_mul_reducedCuspMoment_le hx
  linarith

/-- Sharp singular scale for the second derivative, valid throughout the
project range `α ≤ 2`. -/
theorem abs_reducedLatitudeCuspD2Value_le
    {α x : ℝ} (hx : 0 < x) (hα : α ≤ 2) :
    |reducedLatitudeCuspD2Value α x| ≤
      |(α / 2) * (α / 2 - 1)| *
        ((1 / 2) * x ^ (α / 2 - 1) * x⁻¹ *
          (Real.sqrt ((2 / Real.pi ^ 2) / x))⁻¹) := by
  unfold reducedLatitudeCuspD2Value
  have h := abs_mul_reducedCuspMoment_le_halfPowerScale
    (c := (α / 2) * (α / 2 - 1))
    (γ := α / 2 - 2) hx (by linarith)
  convert h using 1 ; ring_nf

/-- Sharp singular scale for the third derivative. -/
theorem abs_reducedLatitudeCuspD3Value_le
    {α x : ℝ} (hx : 0 < x) (hα : α ≤ 2) :
    |reducedLatitudeCuspD3Value α x| ≤
      |(α / 2) * (α / 2 - 1) * (α / 2 - 2)| *
        ((1 / 2) * x ^ (α / 2 - 2) * x⁻¹ *
          (Real.sqrt ((2 / Real.pi ^ 2) / x))⁻¹) := by
  unfold reducedLatitudeCuspD3Value
  have h := abs_mul_reducedCuspMoment_le_halfPowerScale
    (c := (α / 2) * (α / 2 - 1) * (α / 2 - 2))
    (γ := α / 2 - 3) hx (by linarith)
  convert h using 1 ; ring_nf

/-- Sharp singular scale for the fourth derivative.  This is the direct
integral analogue of differentiating the branch
`x^((1+α)/2)` four times. -/
theorem abs_reducedLatitudeCuspD4Value_le
    {α x : ℝ} (hx : 0 < x) (hα : α ≤ 2) :
    |reducedLatitudeCuspD4Value α x| ≤
      |(α / 2) * (α / 2 - 1) * (α / 2 - 2) * (α / 2 - 3)| *
        ((1 / 2) * x ^ (α / 2 - 3) * x⁻¹ *
          (Real.sqrt ((2 / Real.pi ^ 2) / x))⁻¹) := by
  unfold reducedLatitudeCuspD4Value
  have h := abs_mul_reducedCuspMoment_le_halfPowerScale
    (c := (α / 2) * (α / 2 - 1) * (α / 2 - 2) *
      (α / 2 - 3))
    (γ := α / 2 - 4) hx (by linarith)
  convert h using 1 ; ring_nf

theorem abs_reducedLatitudeCuspD2Value_le_rpow
    {α x : ℝ} (hx : 0 < x) (hα : α ≤ 2) :
    |reducedLatitudeCuspD2Value α x| ≤
      |(α / 2) * (α / 2 - 1)| *
        (Real.pi / (2 * Real.sqrt 2)) *
          x ^ (α / 2 - 3 / 2) := by
  unfold reducedLatitudeCuspD2Value
  rw [abs_mul, abs_of_nonneg (reducedCuspMoment_nonneg hx.le)]
  have hm := reducedCuspMoment_le_rpow_half
    (γ := α / 2 - 2) hx (by linarith)
  have hh := mul_le_mul_of_nonneg_left hm
    (abs_nonneg ((α / 2) * (α / 2 - 1)))
  convert hh using 1 ; ring_nf

theorem abs_reducedLatitudeCuspD3Value_le_rpow
    {α x : ℝ} (hx : 0 < x) (hα : α ≤ 2) :
    |reducedLatitudeCuspD3Value α x| ≤
      |(α / 2) * (α / 2 - 1) * (α / 2 - 2)| *
        (Real.pi / (2 * Real.sqrt 2)) *
          x ^ (α / 2 - 5 / 2) := by
  unfold reducedLatitudeCuspD3Value
  rw [abs_mul, abs_of_nonneg (reducedCuspMoment_nonneg hx.le)]
  have hm := reducedCuspMoment_le_rpow_half
    (γ := α / 2 - 3) hx (by linarith)
  have hh := mul_le_mul_of_nonneg_left hm
    (abs_nonneg ((α / 2) * (α / 2 - 1) * (α / 2 - 2)))
  convert hh using 1 ; ring_nf

theorem abs_reducedLatitudeCuspD4Value_le_rpow
    {α x : ℝ} (hx : 0 < x) (hα : α ≤ 2) :
    |reducedLatitudeCuspD4Value α x| ≤
      |(α / 2) * (α / 2 - 1) * (α / 2 - 2) * (α / 2 - 3)| *
        (Real.pi / (2 * Real.sqrt 2)) *
          x ^ (α / 2 - 7 / 2) := by
  unfold reducedLatitudeCuspD4Value
  rw [abs_mul, abs_of_nonneg (reducedCuspMoment_nonneg hx.le)]
  have hm := reducedCuspMoment_le_rpow_half
    (γ := α / 2 - 4) hx (by linarith)
  have hh := mul_le_mul_of_nonneg_left hm
    (abs_nonneg ((α / 2) * (α / 2 - 1) * (α / 2 - 2) *
      (α / 2 - 3)))
  convert hh using 1 ; ring_nf

/-- Differentiation under the angular integral.  Positivity of `x` keeps
the base uniformly away from zero, so this holds for every real exponent. -/
theorem hasDerivAt_reducedCuspMoment
    {β x : ℝ} (hx : 0 < x) :
    HasDerivAt (reducedCuspMoment β)
      (β * reducedCuspMoment (β - 1) x) x := by
  let ε : ℝ := x / 2
  let lo : ℝ := x / 2
  let hi : ℝ := 3 * x / 2 + 2
  let F : ℝ → ℝ → ℝ :=
    fun y θ ↦ (y + (1 - Real.cos θ)) ^ β
  let F' : ℝ → ℝ → ℝ :=
    fun y θ ↦ β * (y + (1 - Real.cos θ)) ^ (β - 1)
  let C : ℝ :=
    |β| * (lo ^ (β - 1) + hi ^ (β - 1))
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hlo : 0 < lo := by
    dsimp [lo]
    linarith
  have hhi : 0 < hi := by
    dsimp [hi]
    linarith
  have hy_bounds {y : ℝ} (hy : y ∈ ball x ε) :
      lo < y ∧ y < 3 * x / 2 := by
    have habs : |y - x| < x / 2 := by
      simpa [ε, Real.dist_eq] using hy
    constructor
    · dsimp [lo]
      have := (neg_lt_of_abs_lt habs)
      linarith
    · have := (lt_of_abs_lt habs)
      linarith
  have hbase {y θ : ℝ} (hy : y ∈ ball x ε) :
      0 < y + (1 - Real.cos θ) := by
    have hylo := (hy_bounds hy).1
    have hcos : 0 ≤ 1 - Real.cos θ :=
      sub_nonneg.mpr (Real.cos_le_one θ)
    linarith [hlo]
  have hbase_lo {y θ : ℝ} (hy : y ∈ ball x ε) :
      lo ≤ y + (1 - Real.cos θ) := by
    have hylo := (hy_bounds hy).1.le
    have hcos : 0 ≤ 1 - Real.cos θ :=
      sub_nonneg.mpr (Real.cos_le_one θ)
    linarith
  have hbase_hi {y θ : ℝ} (hy : y ∈ ball x ε) :
      y + (1 - Real.cos θ) ≤ hi := by
    have hyhi := (hy_bounds hy).2.le
    have hcos : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    dsimp [hi]
    linarith
  have hF_meas :
      ∀ᶠ y in 𝓝 x,
        AEStronglyMeasurable (F y)
          (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [ball_mem_nhds x hε] with y hy
    have hc : Continuous (F y) := by
      dsimp [F]
      exact
        (continuous_const.add
          (continuous_const.sub Real.continuous_cos)).rpow_const
            (fun θ ↦ Or.inl (hbase hy).ne')
    exact hc.aestronglyMeasurable.restrict
  have hF_int : IntervalIntegrable (F x) volume (0 : ℝ) (2 * Real.pi) := by
    have hxball : x ∈ ball x ε := mem_ball_self hε
    have hc : Continuous (F x) := by
      dsimp [F]
      exact
        (continuous_const.add
          (continuous_const.sub Real.continuous_cos)).rpow_const
            (fun θ ↦ Or.inl (hbase hxball).ne')
    exact hc.intervalIntegrable _ _
  have hF'_meas :
      AEStronglyMeasurable (F' x)
        (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    have hxball : x ∈ ball x ε := mem_ball_self hε
    have hc : Continuous (F' x) := by
      dsimp [F']
      exact continuous_const.mul
        ((continuous_const.add
          (continuous_const.sub Real.continuous_cos)).rpow_const
            (fun θ ↦ Or.inl (hbase hxball).ne'))
    exact hc.aestronglyMeasurable.restrict
  have hbound :
      ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (2 * Real.pi) →
        ∀ y ∈ ball x ε, ‖F' y θ‖ ≤ C := by
    filter_upwards with θ
    intro _ y hy
    let z : ℝ := y + (1 - Real.cos θ)
    have hz : 0 < z := hbase hy
    have hzlo : lo ≤ z := hbase_lo hy
    have hzhi : z ≤ hi := hbase_hi hy
    have hzpow :
        z ^ (β - 1) ≤ lo ^ (β - 1) + hi ^ (β - 1) := by
      by_cases he : 0 ≤ β - 1
      · have hle := Real.rpow_le_rpow hz.le hzhi he
        exact hle.trans (le_add_of_nonneg_left (Real.rpow_nonneg hlo.le _))
      · have he' : β - 1 ≤ 0 := le_of_not_ge he
        have hle := Real.rpow_le_rpow_of_nonpos hlo hzlo he'
        exact hle.trans (le_add_of_nonneg_right (Real.rpow_nonneg hhi.le _))
    have hβ : 0 ≤ |β| := abs_nonneg β
    calc
      ‖F' y θ‖ =
          |β| * z ^ (β - 1) := by
            dsimp [F', z]
            rw [abs_mul,
              abs_of_nonneg (Real.rpow_nonneg hz.le _)]
      _ ≤ |β| * (lo ^ (β - 1) + hi ^ (β - 1)) :=
        mul_le_mul_of_nonneg_left hzpow hβ
      _ = C := rfl
  have hCint :
      IntervalIntegrable (fun _ : ℝ ↦ C) volume
        (0 : ℝ) (2 * Real.pi) :=
    continuous_const.intervalIntegrable _ _
  have hdiff :
      ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (2 * Real.pi) →
        ∀ y ∈ ball x ε,
          HasDerivAt (fun y ↦ F y θ) (F' y θ) y := by
    filter_upwards with θ
    intro _ y hy
    dsimp [F, F']
    convert
      ((hasDerivAt_id y).add_const (1 - Real.cos θ)).rpow_const
        (Or.inl (hbase hy).ne') using 1 ;
      simp only [id_eq] ; ring
  have hraw :=
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) hε hF_meas hF_int hF'_meas hbound hCint hdiff).2
  have havg := hraw.const_mul (1 / (2 * Real.pi))
  have hval :
      (1 / (2 * Real.pi)) *
          ∫ θ in (0 : ℝ)..2 * Real.pi, F' x θ =
        β * ((1 / (2 * Real.pi)) *
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            (x + (1 - Real.cos θ)) ^ (β - 1)) := by
    dsimp only [F']
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [hval] at havg
  simpa only [reducedCuspMoment, F] using havg

/-- Exact second derivative recurrence. -/
theorem hasDerivAt_reducedCuspMoment_D1
    {β x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y ↦ β * reducedCuspMoment (β - 1) y)
      (β * (β - 1) * reducedCuspMoment (β - 2) x) x := by
  convert (hasDerivAt_const x β).mul
    (hasDerivAt_reducedCuspMoment (β := β - 1) hx) using 1 ; ring_nf

/-- Exact third derivative recurrence. -/
theorem hasDerivAt_reducedCuspMoment_D2
    {β x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y ↦ β * (β - 1) * reducedCuspMoment (β - 2) y)
      (β * (β - 1) * (β - 2) *
        reducedCuspMoment (β - 3) x) x := by
  convert (hasDerivAt_const x (β * (β - 1))).mul
    (hasDerivAt_reducedCuspMoment (β := β - 2) hx) using 1 ; ring_nf

/-- Exact fourth derivative recurrence. -/
theorem hasDerivAt_reducedCuspMoment_D3
    {β x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y ↦ β * (β - 1) * (β - 2) *
        reducedCuspMoment (β - 3) y)
      (β * (β - 1) * (β - 2) * (β - 3) *
        reducedCuspMoment (β - 4) x) x := by
  convert (hasDerivAt_const x (β * (β - 1) * (β - 2))).mul
    (hasDerivAt_reducedCuspMoment (β := β - 3) hx) using 1 ; ring_nf

/-- Fourth-derivative chain for the reduced latitude cusp. -/
theorem hasDerivAt_reducedLatitudeCusp_D3
    {α x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y ↦
        (α / 2) * (α / 2 - 1) * (α / 2 - 2) *
          reducedCuspMoment (α / 2 - 3) y)
      ((α / 2) * (α / 2 - 1) * (α / 2 - 2) *
        (α / 2 - 3) * reducedCuspMoment (α / 2 - 4) x) x :=
  hasDerivAt_reducedCuspMoment_D3 hx

theorem hasDerivAt_reducedLatitudeCusp
    {α x : ℝ} (hx : 0 < x) :
    HasDerivAt (reducedLatitudeCusp α)
      (reducedLatitudeCuspD1Value α x) x := by
  simpa only [reducedLatitudeCusp_eq_moment,
    reducedLatitudeCuspD1Value] using
      (hasDerivAt_reducedCuspMoment (β := α / 2) hx)

theorem hasDerivAt_reducedLatitudeCuspD1Value
    {α x : ℝ} (hx : 0 < x) :
    HasDerivAt (reducedLatitudeCuspD1Value α)
      (reducedLatitudeCuspD2Value α x) x := by
  simpa only [reducedLatitudeCuspD1Value,
    reducedLatitudeCuspD2Value] using
      (hasDerivAt_reducedCuspMoment_D1 (β := α / 2) hx)

theorem hasDerivAt_reducedLatitudeCuspD2Value
    {α x : ℝ} (hx : 0 < x) :
    HasDerivAt (reducedLatitudeCuspD2Value α)
      (reducedLatitudeCuspD3Value α x) x := by
  simpa only [reducedLatitudeCuspD2Value,
    reducedLatitudeCuspD3Value] using
      (hasDerivAt_reducedCuspMoment_D2 (β := α / 2) hx)

theorem hasDerivAt_reducedLatitudeCuspD3Value
    {α x : ℝ} (hx : 0 < x) :
    HasDerivAt (reducedLatitudeCuspD3Value α)
      (reducedLatitudeCuspD4Value α x) x := by
  simpa only [reducedLatitudeCuspD3Value,
    reducedLatitudeCuspD4Value] using
      (hasDerivAt_reducedCuspMoment_D3 (β := α / 2) hx)

end BEMOC
