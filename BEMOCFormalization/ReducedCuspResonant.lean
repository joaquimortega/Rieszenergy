import BEMOCFormalization.ReducedCuspLocalDecomposition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The resonant reduced latitude cusp

At `α = 1`, the second derivative of the reduced cusp has a simple
`1 / x` principal part.  This file isolates that constant principal part
directly from the angular integral.  Two integrations then give the local
form

`h₁(x) = C₀ + c₁ x log x + x R(x)`

with `R` bounded.  Keeping `c₁` constant is what prevents a spurious
logarithm of the band scale in neighboring latitude blocks.
-/

open MeasureTheory Set
open scoped Interval

namespace BEMOC

set_option maxHeartbeats 1200000

/-- The quadratic angular model for the resonant second derivative. -/
noncomputable def resonantQuadraticMomentModel (x θ : ℝ) : ℝ :=
  (x + θ ^ 2 / 2) ^ (-(3 : ℝ) / 2)

/-- Elementary antiderivative of the quadratic model. -/
private theorem hasDerivAt_resonantQuadraticMomentPrimitive
    {x θ : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun u : ℝ ↦ u / (x * Real.sqrt (x + u ^ 2 / 2)))
      (resonantQuadraticMomentModel x θ) θ := by
  let q : ℝ → ℝ := fun u ↦ x + u ^ 2 / 2
  have hq : 0 < q θ := by
    dsimp [q]
    positivity
  have hqD : HasDerivAt q θ θ := by
    dsimp [q]
    convert (hasDerivAt_const θ x).add
      ((hasDerivAt_pow 2 θ).div_const 2) using 1 <;> ring
  have hsqrt :
      HasDerivAt (fun u ↦ Real.sqrt (q u))
        (θ / (2 * Real.sqrt (q θ))) θ := by
    convert (Real.hasDerivAt_sqrt hq.ne').comp θ hqD using 1 <;> ring
  have hden :
      HasDerivAt (fun u ↦ x * Real.sqrt (q u))
        (x * (θ / (2 * Real.sqrt (q θ)))) θ :=
    by convert (hasDerivAt_const θ x).mul hsqrt using 1 <;> ring
  have hden0 : x * Real.sqrt (q θ) ≠ 0 := by positivity
  have hquot :=
    (hasDerivAt_id θ).div hden hden0
  convert hquot using 1
  unfold resonantQuadraticMomentModel
  simp only [id_eq]
  have hsqrt0 : Real.sqrt (q θ) ≠ 0 := by positivity
  have hsqrtSq : Real.sqrt (q θ) ^ 2 = q θ := by
    rw [Real.sq_sqrt hq.le]
  have hsqrtTwice :
      Real.sqrt (q θ) * (2 * Real.sqrt (q θ)) = 2 * q θ := by
    calc
      Real.sqrt (q θ) * (2 * Real.sqrt (q θ)) =
          2 * Real.sqrt (q θ) ^ 2 := by ring
      _ = 2 * q θ := by rw [hsqrtSq]
  have hpow :
      q θ ^ (-(3 : ℝ) / 2) =
        1 / (q θ * Real.sqrt (q θ)) := by
    have hhalf :
        q θ ^ (-(1 : ℝ) / 2) = (Real.sqrt (q θ))⁻¹ := by
      rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg hq.le, ← Real.sqrt_eq_rpow]
    rw [show -(3 : ℝ) / 2 = (-1 : ℝ) + (-(1 : ℝ) / 2) by ring,
      Real.rpow_add hq, Real.rpow_neg_one, hhalf]
    field_simp [hq.ne', hsqrt0]
  change q θ ^ (-(3 : ℝ) / 2) = _
  rw [hpow]
  have hnum :
      1 * (x * Real.sqrt (q θ)) -
          θ * (x * (θ / (2 * Real.sqrt (q θ)))) =
        x ^ 2 / Real.sqrt (q θ) := by
    calc
      1 * (x * Real.sqrt (q θ)) -
            θ * (x * (θ / (2 * Real.sqrt (q θ)))) =
          x / (2 * Real.sqrt (q θ)) *
            (2 * Real.sqrt (q θ) ^ 2 - θ ^ 2) := by
              field_simp [hsqrt0]
              rw [mul_assoc]
              rw [hsqrtTwice]
              ring
      _ = x / (2 * Real.sqrt (q θ)) * (2 * q θ - θ ^ 2) := by
        rw [hsqrtSq]
      _ = x / (2 * Real.sqrt (q θ)) * (2 * x) := by
        dsimp [q]
        ring
      _ = x ^ 2 / Real.sqrt (q θ) := by
        field_simp [hsqrt0]
        ring
  rw [hnum]
  rw [mul_pow, hsqrtSq]
  field_simp [hx.ne', hsqrt0, hq.ne']
  ring

/-- Exact integral of the quadratic angular model on a symmetric interval. -/
theorem integral_resonantQuadraticMomentModel
    {x L : ℝ} (hx : 0 < x) (hL : 0 ≤ L) :
    (∫ θ in (-L)..L, resonantQuadraticMomentModel x θ) =
      2 * L / (x * Real.sqrt (x + L ^ 2 / 2)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ ↦ hasDerivAt_resonantQuadraticMomentPrimitive hx)]
  · rw [neg_sq]
    ring
  · apply ContinuousOn.intervalIntegrable_of_Icc
    · linarith
    · intro θ _
      unfold resonantQuadraticMomentModel
      apply
        (continuousWithinAt_const.add
          ((continuousWithinAt_id.pow 2).div_const 2)).rpow_const
      exact Or.inl (by positivity)

/-- Mean-value bound for the negative three-halves power.  The separate
lower scale `L` is useful when both arguments are angular quadratic
perturbations of `x`. -/
private theorem abs_rpow_neg_three_halves_sub_le
    {a b L : ℝ} (hL : 0 < L) (hLa : L ≤ a) (hLb : L ≤ b) :
    |a ^ (-(3 : ℝ) / 2) - b ^ (-(3 : ℝ) / 2)| ≤
      (3 / 2 : ℝ) * L ^ (-(5 : ℝ) / 2) * |a - b| := by
  let f : ℝ → ℝ := fun z ↦ z ^ (-(3 : ℝ) / 2)
  let f' : ℝ → ℝ :=
    fun z ↦ (-(3 : ℝ) / 2) * z ^ (-(5 : ℝ) / 2)
  have hderiv {z : ℝ} (hz : 0 < z) : HasDerivAt f (f' z) z := by
    dsimp [f, f']
    convert Real.hasDerivAt_rpow_const (x := z)
      (p := -(3 : ℝ) / 2) (Or.inl hz.ne') using 1 <;> ring
  have hordered :
      ∀ {u v : ℝ}, L ≤ u → L ≤ v → u ≤ v →
        |u ^ (-(3 : ℝ) / 2) - v ^ (-(3 : ℝ) / 2)| ≤
          (3 / 2 : ℝ) * L ^ (-(5 : ℝ) / 2) * |u - v| := by
    intro u v hLu hLv huv
    have hu : 0 < u := hL.trans_le hLu
    have hseg :
        ∀ z ∈ Icc u v, HasDerivWithinAt f (f' z) (Icc u v) z := by
      intro z hz
      exact (hderiv (hu.trans_le hz.1)).hasDerivWithinAt
    have hbound :
        ∀ z ∈ Ico u v,
          ‖f' z‖ ≤ (3 / 2 : ℝ) * L ^ (-(5 : ℝ) / 2) := by
      intro z hz
      have hz0 : 0 < z := hu.trans_le hz.1
      have hLz : L ≤ z := hLu.trans hz.1
      have hp :
          z ^ (-(5 : ℝ) / 2) ≤ L ^ (-(5 : ℝ) / 2) := by
        exact Real.rpow_le_rpow_of_nonpos hL hLz (by norm_num)
      dsimp [f']
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hz0.le _)]
      have hcoeff : |(-(3 : ℝ) / 2)| = 3 / 2 := by norm_num
      rw [hcoeff]
      exact mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have hmv :=
      norm_image_sub_le_of_norm_deriv_le_segment'
        (a := u) (b := v) hseg hbound v (right_mem_Icc.mpr huv)
    dsimp [f] at hmv
    rw [abs_sub_comm] at hmv
    have habs : |u - v| = v - u := by
      rw [abs_of_nonpos (sub_nonpos.mpr huv)]
      ring
    simpa [habs] using hmv
  rcases le_total a b with hab | hba
  · exact hordered hLa hLb hab
  · simpa [abs_sub_comm] using hordered hLb hLa hba

/-- Pointwise comparison with the exact quadratic model on the singular
central angular interval. -/
theorem abs_resonantMoment_sub_quadraticModel_le
    {x θ : ℝ} (hx : 0 < x) (hθ : |θ| ≤ 1) :
    |(x + (1 - Real.cos θ)) ^ (-(3 : ℝ) / 2) -
        resonantQuadraticMomentModel x θ| ≤
      (3 / 2 : ℝ) *
        (x + (2 / Real.pi ^ 2) * θ ^ 2) ^ (-(5 : ℝ) / 2) *
          (|θ| ^ 4 * (5 / 96)) := by
  let L : ℝ := x + (2 / Real.pi ^ 2) * θ ^ 2
  have hc : 0 < (2 / Real.pi ^ 2 : ℝ) := by positivity
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hθpi : |θ| ≤ Real.pi := hθ.trans (by linarith [Real.pi_gt_three])
  have hLa : L ≤ x + (1 - Real.cos θ) := by
    have hcos := Real.cos_le_one_sub_mul_cos_sq hθpi
    dsimp [L]
    linarith
  have hcHalf : (2 / Real.pi ^ 2 : ℝ) ≤ 1 / 2 := by
    have hpiSq : (4 : ℝ) ≤ Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 2)).2
    nlinarith
  have hLb : L ≤ x + θ ^ 2 / 2 := by
    dsimp [L]
    nlinarith [sq_nonneg θ]
  have hmv := abs_rpow_neg_three_halves_sub_le hL hLa hLb
  have hcos := Real.cos_bound hθ
  unfold resonantQuadraticMomentModel
  calc
    |(x + (1 - Real.cos θ)) ^ (-(3 : ℝ) / 2) -
        (x + θ ^ 2 / 2) ^ (-(3 : ℝ) / 2)| ≤
      (3 / 2 : ℝ) * L ^ (-(5 : ℝ) / 2) *
        |(x + (1 - Real.cos θ)) - (x + θ ^ 2 / 2)| := hmv
    _ ≤ (3 / 2 : ℝ) * L ^ (-(5 : ℝ) / 2) *
        (|θ| ^ 4 * (5 / 96)) := by
      apply mul_le_mul_of_nonneg_left
      · rw [show
          (x + (1 - Real.cos θ)) - (x + θ ^ 2 / 2) =
            -(Real.cos θ - (1 - θ ^ 2 / 2)) by ring,
          abs_neg]
        exact hcos
      · positivity
    _ = _ := by rfl

/-- The central comparison error has the integrable resonant scale
`x⁻¹/²`, uniformly in the angle. -/
theorem abs_resonantMoment_sub_quadraticModel_le_invSqrt
    {x θ : ℝ} (hx : 0 < x) (hθ : |θ| ≤ 1) :
    |(x + (1 - Real.cos θ)) ^ (-(3 : ℝ) / 2) -
        resonantQuadraticMomentModel x θ| ≤
      (15 / 192 : ℝ) * (Real.pi ^ 2 / 2) ^ 2 *
        x ^ (-(1 : ℝ) / 2) := by
  let c : ℝ := 2 / Real.pi ^ 2
  let L : ℝ := x + c * θ ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hxL : x ≤ L := by
    dsimp [L]
    exact le_add_of_nonneg_right (mul_nonneg hc.le (sq_nonneg θ))
  have hctheta : c * θ ^ 2 ≤ L := by
    dsimp [L]
    linarith
  have hsquare : c ^ 2 * θ ^ 4 ≤ L ^ 2 := by
    have hsq :=
      pow_le_pow_left₀ (mul_nonneg hc.le (sq_nonneg θ)) hctheta 2
    convert hsq using 1 <;> ring
  have hpow :
      θ ^ 4 * L ^ (-(5 : ℝ) / 2) ≤
        c⁻¹ ^ 2 * L ^ (-(1 : ℝ) / 2) := by
    have hnonneg : 0 ≤ L ^ (-(5 : ℝ) / 2) :=
      Real.rpow_nonneg hL.le _
    have hmul := mul_le_mul_of_nonneg_right hsquare hnonneg
    have hcombine :
        L ^ 2 * L ^ (-(5 : ℝ) / 2) =
          L ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hL]
      congr 1
      norm_num
    calc
      θ ^ 4 * L ^ (-(5 : ℝ) / 2) =
          c⁻¹ ^ 2 *
            ((c ^ 2 * θ ^ 4) * L ^ (-(5 : ℝ) / 2)) := by
              field_simp [hc.ne']
              ring
      _ ≤ c⁻¹ ^ 2 *
          (L ^ 2 * L ^ (-(5 : ℝ) / 2)) := by
            exact mul_le_mul_of_nonneg_left hmul (sq_nonneg c⁻¹)
      _ = c⁻¹ ^ 2 * L ^ (-(1 : ℝ) / 2) := by rw [hcombine]
  have hLx :
      L ^ (-(1 : ℝ) / 2) ≤ x ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hx hxL (by norm_num)
  have hraw := abs_resonantMoment_sub_quadraticModel_le hx hθ
  have habsPow : |θ| ^ 4 = θ ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ θ ^ 4)]
  have hmajor :
      (3 / 2 : ℝ) * L ^ (-(5 : ℝ) / 2) *
          (|θ| ^ 4 * (5 / 96)) ≤
        (15 / 192 : ℝ) * c⁻¹ ^ 2 *
          x ^ (-(1 : ℝ) / 2) := by
    rw [habsPow]
    calc
      (3 / 2 : ℝ) * L ^ (-(5 : ℝ) / 2) *
          (θ ^ 4 * (5 / 96)) =
        (15 / 192 : ℝ) *
          (θ ^ 4 * L ^ (-(5 : ℝ) / 2)) := by ring
      _ ≤ (15 / 192 : ℝ) *
          (c⁻¹ ^ 2 * L ^ (-(1 : ℝ) / 2)) := by
            exact mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ (15 / 192 : ℝ) *
          (c⁻¹ ^ 2 * x ^ (-(1 : ℝ) / 2)) := by
            gcongr
      _ = _ := by ring
  refine hraw.trans ?_
  have hcinv : c⁻¹ = Real.pi ^ 2 / 2 := by
    dsimp [c]
    field_simp [Real.pi_ne_zero]
  rw [show x + (2 / Real.pi ^ 2) * θ ^ 2 = L by rfl]
  rw [hcinv] at hmajor
  exact hmajor

/-- Away from the central angular interval both the cosine cusp and the
quadratic model are uniformly nonsingular.  The harmless `x⁻¹/²` factor
puts this estimate on the same scale as the central comparison. -/
theorem abs_resonantMoment_sub_quadraticModel_le_invSqrt_away
    {x θ : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hθ1 : 1 ≤ |θ|) (hθpi : |θ| ≤ Real.pi) :
    |(x + (1 - Real.cos θ)) ^ (-(3 : ℝ) / 2) -
        resonantQuadraticMomentModel x θ| ≤
      ((2 / Real.pi ^ 2) ^ (-(3 : ℝ) / 2) +
          (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2)) *
        x ^ (-(1 : ℝ) / 2) := by
  let c : ℝ := 2 / Real.pi ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hθsq : 1 ≤ θ ^ 2 := by
    rw [← sq_abs]
    nlinarith
  have haLower : c ≤ x + (1 - Real.cos θ) := by
    have hcos := Real.cos_le_one_sub_mul_cos_sq hθpi
    have : c ≤ c * θ ^ 2 := by
      nlinarith
    dsimp [c] at hcos ⊢
    linarith
  have hbLower : (1 / 2 : ℝ) ≤ x + θ ^ 2 / 2 := by
    nlinarith
  have ha0 : 0 < x + (1 - Real.cos θ) := by
    have := sub_nonneg.mpr (Real.cos_le_one θ)
    linarith
  have hb0 : 0 < x + θ ^ 2 / 2 := by positivity
  have haPow :
      (x + (1 - Real.cos θ)) ^ (-(3 : ℝ) / 2) ≤
        c ^ (-(3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hc haLower (by norm_num)
  have hbPow :
      (x + θ ^ 2 / 2) ^ (-(3 : ℝ) / 2) ≤
        (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hbLower (by norm_num)
  have hxPow : 1 ≤ x ^ (-(1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow_of_nonpos hx hx1 (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
    simpa using h
  unfold resonantQuadraticMomentModel
  calc
    |(x + (1 - Real.cos θ)) ^ (-(3 : ℝ) / 2) -
        (x + θ ^ 2 / 2) ^ (-(3 : ℝ) / 2)| ≤
      |(x + (1 - Real.cos θ)) ^ (-(3 : ℝ) / 2)| +
        |(x + θ ^ 2 / 2) ^ (-(3 : ℝ) / 2)| := abs_sub _ _
    _ = (x + (1 - Real.cos θ)) ^ (-(3 : ℝ) / 2) +
        (x + θ ^ 2 / 2) ^ (-(3 : ℝ) / 2) := by
      rw [abs_of_nonneg (Real.rpow_nonneg ha0.le _),
        abs_of_nonneg (Real.rpow_nonneg hb0.le _)]
    _ ≤ c ^ (-(3 : ℝ) / 2) +
        (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2) :=
      add_le_add haPow hbPow
    _ ≤ (c ^ (-(3 : ℝ) / 2) +
          (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2)) *
        x ^ (-(1 : ℝ) / 2) := by
      exact le_mul_of_one_le_right
        (add_nonneg (Real.rpow_nonneg hc.le _)
          (Real.rpow_nonneg (by norm_num) _)) hxPow
    _ = _ := by rfl

/-- A single explicit coefficient dominating the central and away angular
comparison estimates. -/
noncomputable def resonantMomentComparisonCoefficient : ℝ :=
  (15 / 192 : ℝ) * (Real.pi ^ 2 / 2) ^ 2 +
    (2 / Real.pi ^ 2) ^ (-(3 : ℝ) / 2) +
    (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2)

theorem resonantMomentComparisonCoefficient_nonneg :
    0 ≤ resonantMomentComparisonCoefficient := by
  unfold resonantMomentComparisonCoefficient
  positivity

/-- Uniform pointwise comparison on the whole centered angular period. -/
theorem abs_resonantMoment_sub_quadraticModel_le_invSqrt_full
    {x θ : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hθpi : |θ| ≤ Real.pi) :
    |(x + (1 - Real.cos θ)) ^ (-(3 : ℝ) / 2) -
        resonantQuadraticMomentModel x θ| ≤
      resonantMomentComparisonCoefficient * x ^ (-(1 : ℝ) / 2) := by
  rcases le_total |θ| 1 with hsmall | hlarge
  · have h := abs_resonantMoment_sub_quadraticModel_le_invSqrt hx hsmall
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
    unfold resonantMomentComparisonCoefficient
    have hrest :
        0 ≤ (2 / Real.pi ^ 2) ^ (-(3 : ℝ) / 2) +
          (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2) := by positivity
    linarith
  · have h := abs_resonantMoment_sub_quadraticModel_le_invSqrt_away
      hx hx1 hlarge hθpi
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
    unfold resonantMomentComparisonCoefficient
    have hfirst :
        0 ≤ (15 / 192 : ℝ) * (Real.pi ^ 2 / 2) ^ 2 := by positivity
    linarith

/-- The averaged true angular moment differs from its exact quadratic
model by at most `O(x⁻¹/²)`. -/
theorem abs_reducedCuspMoment_one_neg_three_halves_sub_model_le
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |reducedCuspMoment (-(3 : ℝ) / 2) x -
        1 / (x * Real.sqrt (x + Real.pi ^ 2 / 2))| ≤
      resonantMomentComparisonCoefficient * x ^ (-(1 : ℝ) / 2) := by
  let f : ℝ → ℝ :=
    fun θ ↦ (x + (1 - Real.cos θ)) ^ (-(3 : ℝ) / 2)
  let g : ℝ → ℝ := fun θ ↦ resonantQuadraticMomentModel x θ
  have hfper : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp [f]
    rw [Real.cos_add_two_pi]
  have hcenter :
      (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) =
        ∫ θ in (-Real.pi)..Real.pi, f θ := by
    have h := hfper.intervalIntegral_add_eq (-Real.pi) 0
    symm
    convert h using 1 <;> ring
  have hpoint :
      ∀ θ ∈ Ι (-Real.pi) Real.pi,
        ‖f θ - g θ‖ ≤
          resonantMomentComparisonCoefficient * x ^ (-(1 : ℝ) / 2) := by
    intro θ hθ
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    rw [Real.norm_eq_abs]
    exact abs_resonantMoment_sub_quadraticModel_le_invSqrt_full
      hx hx1 (abs_le.mpr ⟨hθ.1.le, hθ.2⟩)
  have hfint : IntervalIntegrable f volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    dsimp [f]
    apply
      (continuous_const.add
        (continuous_const.sub Real.continuous_cos)).rpow_const
    intro θ
    exact Or.inl (by
      have := sub_nonneg.mpr (Real.cos_le_one θ)
      linarith)
  have hgint : IntervalIntegrable g volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    dsimp [g, resonantQuadraticMomentModel]
    apply
      (continuous_const.add
        ((continuous_id.pow 2).div_const 2)).rpow_const
    intro θ
    exact Or.inl (by positivity)
  have hint :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hdiff :
      |(∫ θ in (-Real.pi)..Real.pi, f θ) -
          ∫ θ in (-Real.pi)..Real.pi, g θ| ≤
        (2 * Real.pi) *
          (resonantMomentComparisonCoefficient *
            x ^ (-(1 : ℝ) / 2)) := by
    rw [← intervalIntegral.integral_sub hfint hgint]
    rw [show Real.pi - (-Real.pi) = 2 * Real.pi by ring,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hint
    simpa only [Real.norm_eq_abs, mul_comm] using hint
  have hg :=
    integral_resonantQuadraticMomentModel
      (x := x) (L := Real.pi) hx Real.pi_pos.le
  unfold reducedCuspMoment
  change
    |(1 / (2 * Real.pi)) *
          (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) -
        1 / (x * Real.sqrt (x + Real.pi ^ 2 / 2))| ≤ _
  rw [hcenter]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hmodel :
      (1 / (2 * Real.pi)) *
          (∫ θ in (-Real.pi)..Real.pi, g θ) =
        1 / (x * Real.sqrt (x + Real.pi ^ 2 / 2)) := by
    dsimp [g]
    rw [hg]
    field_simp [hpi]
  rw [← hmodel]
  rw [← mul_sub]
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) *
        |(∫ θ in (-Real.pi)..Real.pi, f θ) -
          ∫ θ in (-Real.pi)..Real.pi, g θ| ≤
      (1 / (2 * Real.pi)) *
        ((2 * Real.pi) *
          (resonantMomentComparisonCoefficient *
            x ^ (-(1 : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = _ := by field_simp [hpi]

/-- The exact quadratic model has the same `1/x` principal coefficient as
its zero-gap normalization, with a uniformly bounded difference. -/
theorem abs_resonantQuadraticModelAverage_sub_principal_le_one
    {x : ℝ} (hx : 0 < x) :
    |1 / (x * Real.sqrt (x + Real.pi ^ 2 / 2)) -
        1 / (x * Real.sqrt (Real.pi ^ 2 / 2))| ≤ 1 := by
  let a : ℝ := Real.pi ^ 2 / 2
  let r : ℝ := Real.sqrt (x + a)
  let r₀ : ℝ := Real.sqrt a
  have ha : 1 < a := by
    dsimp [a]
    nlinarith [Real.pi_gt_three]
  have hr₀ : 1 < r₀ := by
    dsimp [r₀]
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
    exact ha
  have hr : r₀ < r := by
    dsimp [r, r₀]
    rw [Real.sqrt_lt (by positivity) (by positivity),
      Real.sq_sqrt (by positivity)]
    linarith
  have hr0pos : 0 < r := lt_trans (by linarith) hr
  have hr₀0 : 0 < r₀ := by linarith
  have hrSq : r ^ 2 = x + a := by
    dsimp [r]
    rw [Real.sq_sqrt (by positivity)]
  have hr₀Sq : r₀ ^ 2 = a := by
    dsimp [r₀]
    rw [Real.sq_sqrt (by linarith)]
  have hxFactor : x = (r - r₀) * (r + r₀) := by
    calc
      x = r ^ 2 - r₀ ^ 2 := by rw [hrSq, hr₀Sq]; ring
      _ = (r - r₀) * (r + r₀) := by ring
  have hraw :
      1 / (x * r) - 1 / (x * r₀) =
        -1 / (r * r₀ * (r + r₀)) := by
    have hdiff : r - r₀ ≠ 0 := sub_ne_zero.mpr hr.ne'
    have hsum : r + r₀ ≠ 0 := by positivity
    rw [hxFactor]
    field_simp [hdiff, hsum, hr0pos.ne', hr₀0.ne']
    ring
  have hden : 1 ≤ r * r₀ * (r + r₀) := by
    have hr1 : 1 ≤ r := by linarith
    have hr₀1 : 1 ≤ r₀ := hr₀.le
    nlinarith [mul_le_mul hr1 hr₀1 (by norm_num) hr0pos.le,
      mul_le_mul (by nlinarith : 1 ≤ r * r₀)
        (by nlinarith : 1 ≤ r + r₀) (by norm_num) (by positivity : 0 ≤ r * r₀)]
  change |1 / (x * r) - 1 / (x * r₀)| ≤ 1
  rw [hraw, abs_div, abs_neg, abs_one,
    abs_of_nonneg (by positivity : 0 ≤ r * r₀ * (r + r₀))]
  simpa using (inv_le_one₀ (by positivity : 0 < r * r₀ * (r + r₀))).2 hden

/-- The resonant angular moment has a constant `1/x` principal part and an
integrable `O(x⁻¹/²)` remainder. -/
theorem abs_reducedCuspMoment_one_neg_three_halves_sub_principal_le
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |reducedCuspMoment (-(3 : ℝ) / 2) x -
        1 / (x * Real.sqrt (Real.pi ^ 2 / 2))| ≤
      (resonantMomentComparisonCoefficient + 1) *
        x ^ (-(1 : ℝ) / 2) := by
  have hmodel :=
    abs_reducedCuspMoment_one_neg_three_halves_sub_model_le hx hx1
  have hprincipal :=
    abs_resonantQuadraticModelAverage_sub_principal_le_one hx
  have hxPow : 1 ≤ x ^ (-(1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow_of_nonpos hx hx1
      (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
    simpa using h
  calc
    |reducedCuspMoment (-(3 : ℝ) / 2) x -
        1 / (x * Real.sqrt (Real.pi ^ 2 / 2))| ≤
      |reducedCuspMoment (-(3 : ℝ) / 2) x -
        1 / (x * Real.sqrt (x + Real.pi ^ 2 / 2))| +
      |1 / (x * Real.sqrt (x + Real.pi ^ 2 / 2)) -
        1 / (x * Real.sqrt (Real.pi ^ 2 / 2))| := by
          rw [show
            reducedCuspMoment (-(3 : ℝ) / 2) x -
                1 / (x * Real.sqrt (Real.pi ^ 2 / 2)) =
              (reducedCuspMoment (-(3 : ℝ) / 2) x -
                1 / (x * Real.sqrt (x + Real.pi ^ 2 / 2))) +
              (1 / (x * Real.sqrt (x + Real.pi ^ 2 / 2)) -
                1 / (x * Real.sqrt (Real.pi ^ 2 / 2))) by ring]
          exact abs_add _ _
    _ ≤ resonantMomentComparisonCoefficient *
          x ^ (-(1 : ℝ) / 2) + 1 :=
      add_le_add hmodel hprincipal
    _ ≤ resonantMomentComparisonCoefficient *
          x ^ (-(1 : ℝ) / 2) + x ^ (-(1 : ℝ) / 2) :=
      add_le_add_left hxPow _
    _ = _ := by ring

/-- Constant coefficient of the resonant `x log x` branch. -/
noncomputable def reducedCuspResonantPrincipalCoefficient : ℝ :=
  -1 / (4 * Real.sqrt (Real.pi ^ 2 / 2))

/-- Principal-singularity subtraction for the actual reduced cusp.  This is
the decisive resonant local estimate: the remaining second derivative is
integrable at zero. -/
theorem abs_reducedLatitudeCuspD2Value_one_sub_principal_le
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |reducedLatitudeCuspD2Value 1 x -
        reducedCuspResonantPrincipalCoefficient * x⁻¹| ≤
      ((resonantMomentComparisonCoefficient + 1) / 4) *
        x ^ (-(1 : ℝ) / 2) := by
  have hm :=
    abs_reducedCuspMoment_one_neg_three_halves_sub_principal_le hx hx1
  have hxne : x ≠ 0 := hx.ne'
  have hrewrite :
      reducedLatitudeCuspD2Value 1 x -
          reducedCuspResonantPrincipalCoefficient * x⁻¹ =
        (-1 / 4) *
          (reducedCuspMoment (-(3 : ℝ) / 2) x -
            1 / (x * Real.sqrt (Real.pi ^ 2 / 2))) := by
    unfold reducedLatitudeCuspD2Value
      reducedCuspResonantPrincipalCoefficient
    norm_num
    field_simp [hxne]
    ring
  rw [hrewrite, abs_mul]
  have hcoeff : |(-1 / 4 : ℝ)| = 1 / 4 := by norm_num
  rw [hcoeff]
  calc
    (1 / 4 : ℝ) *
        |reducedCuspMoment (-(3 : ℝ) / 2) x -
          1 / (x * Real.sqrt (Real.pi ^ 2 / 2))| ≤
      (1 / 4 : ℝ) *
        ((resonantMomentComparisonCoefficient + 1) *
          x ^ (-(1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

noncomputable def reducedCuspResonantD2Remainder (x : ℝ) : ℝ :=
  if 0 < x then
    reducedLatitudeCuspD2Value 1 x -
      reducedCuspResonantPrincipalCoefficient * x⁻¹
  else 0

noncomputable def reducedCuspResonantRemainderCoefficient : ℝ :=
  (resonantMomentComparisonCoefficient + 1) / 4

theorem reducedCuspResonantRemainderCoefficient_nonneg :
    0 ≤ reducedCuspResonantRemainderCoefficient := by
  unfold reducedCuspResonantRemainderCoefficient
  have := resonantMomentComparisonCoefficient_nonneg
  positivity

private theorem aestronglyMeasurable_reducedCuspResonantD2Remainder :
    AEStronglyMeasurable reducedCuspResonantD2Remainder volume := by
  have hcont :
      ContinuousOn
        (fun x ↦ reducedLatitudeCuspD2Value 1 x -
          reducedCuspResonantPrincipalCoefficient * x⁻¹) (Ioi 0) := by
    intro x hx
    exact
      ((hasDerivAt_reducedLatitudeCuspD2Value
        (α := 1) hx).continuousAt.sub
          (continuousAt_const.mul
            (continuousAt_id.inv₀ hx.ne'))).continuousWithinAt
  have hpos :
      AEStronglyMeasurable
        (fun x ↦ reducedLatitudeCuspD2Value 1 x -
          reducedCuspResonantPrincipalCoefficient * x⁻¹)
        (volume.restrict (Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have hzero :
      AEStronglyMeasurable (fun _ : ℝ ↦ (0 : ℝ))
        (volume.restrict (Ioi (0 : ℝ))ᶜ) :=
    aestronglyMeasurable_const
  have hp := hpos.piecewise measurableSet_Ioi hzero
  simpa [reducedCuspResonantD2Remainder, Set.piecewise] using hp

/-- The principal-subtracted second derivative is integrable at zero. -/
theorem intervalIntegrable_reducedCuspResonantD2Remainder :
    IntervalIntegrable reducedCuspResonantD2Remainder volume 0 1 := by
  let K := reducedCuspResonantRemainderCoefficient
  have hmajor :
      IntervalIntegrable (fun x : ℝ ↦ K * x ^ (-(1 : ℝ) / 2))
        volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K
  apply hmajor.mono_fun
  · exact
      aestronglyMeasurable_reducedCuspResonantD2Remainder.mono_measure
        Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    have hb :=
      abs_reducedLatitudeCuspD2Value_one_sub_principal_le hx0 hx.2
    simp only [Real.norm_eq_abs]
    rw [reducedCuspResonantD2Remainder, if_pos hx0]
    rw [abs_of_nonneg (mul_nonneg
      reducedCuspResonantRemainderCoefficient_nonneg
      (Real.rpow_nonneg hx0.le _))]
    simpa [K, reducedCuspResonantRemainderCoefficient] using hb

noncomputable def reducedCuspResonantLinearCoefficient : ℝ :=
  reducedLatitudeCuspD1Value 1 1 -
    reducedCuspResonantPrincipalCoefficient -
    ∫ y in (0 : ℝ)..1, reducedCuspResonantD2Remainder y

noncomputable def reducedCuspResonantD1Remainder (x : ℝ) : ℝ :=
  if 0 < x then
    reducedLatitudeCuspD1Value 1 x -
      reducedCuspResonantPrincipalCoefficient * (Real.log x + 1) -
      reducedCuspResonantLinearCoefficient
  else 0

/-- Exact first integration of the principal-subtracted second
derivative. -/
theorem reducedCuspResonantD1Remainder_eq_integral
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    reducedCuspResonantD1Remainder x =
      ∫ y in (0 : ℝ)..x, reducedCuspResonantD2Remainder y := by
  have hint := intervalIntegrable_reducedCuspResonantD2Remainder
  have h0x :=
    hint.mono_set
      (uIcc_subset_uIcc (a₁ := 0) (b₁ := x)
        (a₂ := 0) (b₂ := 1) (by simp) (by simp [hx.le, hx1]))
  have hx1int :=
    hint.mono_set
      (uIcc_subset_uIcc (a₁ := x) (b₁ := 1)
        (a₂ := 0) (b₂ := 1)
        (by simp [hx.le, hx1]) (by simp))
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals h0x hx1int
  have heqOn :
      (∫ y in x..1, reducedCuspResonantD2Remainder y) =
        ∫ y in x..1,
          (reducedLatitudeCuspD2Value 1 y -
            reducedCuspResonantPrincipalCoefficient * y⁻¹) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx1] at hy
    have hy0 : 0 < y := hx.trans_le hy.1
    simp [reducedCuspResonantD2Remainder, hy0]
  let H : ℝ → ℝ := fun y ↦
    reducedLatitudeCuspD1Value 1 y -
      reducedCuspResonantPrincipalCoefficient * (Real.log y + 1)
  have hFTC :
      (∫ y in x..1,
          (reducedLatitudeCuspD2Value 1 y -
            reducedCuspResonantPrincipalCoefficient * y⁻¹)) =
        H 1 - H x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro y hy
      rw [uIcc_of_le hx1] at hy
      have hy0 : 0 < y := hx.trans_le hy.1
      have hlog :
          HasDerivAt (fun z : ℝ ↦ Real.log z + 1) y⁻¹ y :=
        (Real.hasDerivAt_log hy0.ne').add_const 1
      dsimp [H]
      convert
        (hasDerivAt_reducedLatitudeCuspD1Value
          (α := 1) hy0).sub
            ((hasDerivAt_const y
              reducedCuspResonantPrincipalCoefficient).mul hlog) using 1 <;>
        ring
    · apply ContinuousOn.intervalIntegrable_of_Icc hx1
      intro y hy
      have hy0 : 0 < y := hx.trans_le hy.1
      exact
        ((hasDerivAt_reducedLatitudeCuspD2Value
          (α := 1) hy0).continuousAt.sub
            (continuousAt_const.mul
              (continuousAt_id.inv₀ hy0.ne'))).continuousWithinAt
  unfold reducedCuspResonantD1Remainder
  rw [if_pos hx]
  rw [heqOn, hFTC] at hadd
  unfold reducedCuspResonantLinearCoefficient
  dsimp [H] at hadd
  rw [Real.log_one] at hadd
  ring_nf at hadd ⊢
  linarith

/-- Square-root bound after the first integration. -/
theorem abs_reducedCuspResonantD1Remainder_le
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |reducedCuspResonantD1Remainder x| ≤
      (2 * reducedCuspResonantRemainderCoefficient) *
        x ^ (1 / 2 : ℝ) := by
  let K := reducedCuspResonantRemainderCoefficient
  have hmajor :
      IntervalIntegrable (fun y : ℝ ↦ K * y ^ (-(1 : ℝ) / 2))
        volume 0 x :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (f := reducedCuspResonantD2Remainder)
    (g := fun y : ℝ ↦ K * y ^ (-(1 : ℝ) / 2)) (by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
      rw [uIoc_of_le hx.le] at hy
      have hy0 : 0 < y := hy.1
      have hb :=
        abs_reducedLatitudeCuspD2Value_one_sub_principal_le
          hy0 (hy.2.trans hx1)
      simp only [Real.norm_eq_abs]
      rw [reducedCuspResonantD2Remainder, if_pos hy0]
      simpa [K, reducedCuspResonantRemainderCoefficient] using hb) hmajor
  rw [reducedCuspResonantD1Remainder_eq_integral hx hx1]
  have hnorm' :
      |∫ y in (0 : ℝ)..x, reducedCuspResonantD2Remainder y| ≤
        |∫ y in (0 : ℝ)..x, K * y ^ (-(1 : ℝ) / 2)| := by
    simpa [Real.norm_eq_abs] using hnorm
  calc
    _ ≤ |∫ y in (0 : ℝ)..x, K * y ^ (-(1 : ℝ) / 2)| := hnorm'
    _ = (2 * K) * x ^ (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num))]
      rw [show (-(1 : ℝ) / 2) + 1 = 1 / 2 by ring,
        Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero]
      rw [abs_of_nonneg (mul_nonneg
        reducedCuspResonantRemainderCoefficient_nonneg
        (div_nonneg (Real.rpow_nonneg hx.le _) (by norm_num)))]
      ring
    _ = _ := by rfl

private theorem aestronglyMeasurable_reducedCuspResonantD1Remainder :
    AEStronglyMeasurable reducedCuspResonantD1Remainder volume := by
  have hcont :
      ContinuousOn
        (fun x ↦ reducedLatitudeCuspD1Value 1 x -
          reducedCuspResonantPrincipalCoefficient * (Real.log x + 1) -
          reducedCuspResonantLinearCoefficient) (Ioi 0) := by
    intro x hx
    exact
      (((hasDerivAt_reducedLatitudeCuspD1Value
        (α := 1) hx).continuousAt.sub
          (continuousAt_const.mul
            ((Real.continuousAt_log hx.ne').add continuousAt_const))).sub
              continuousAt_const).continuousWithinAt
  have hpos :
      AEStronglyMeasurable
        (fun x ↦ reducedLatitudeCuspD1Value 1 x -
          reducedCuspResonantPrincipalCoefficient * (Real.log x + 1) -
          reducedCuspResonantLinearCoefficient)
        (volume.restrict (Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have hzero :
      AEStronglyMeasurable (fun _ : ℝ ↦ (0 : ℝ))
        (volume.restrict (Ioi (0 : ℝ))ᶜ) :=
    aestronglyMeasurable_const
  have hp := hpos.piecewise measurableSet_Ioi hzero
  simpa [reducedCuspResonantD1Remainder, Set.piecewise] using hp

theorem intervalIntegrable_reducedCuspResonantD1Remainder :
    IntervalIntegrable reducedCuspResonantD1Remainder volume 0 1 := by
  let K := 2 * reducedCuspResonantRemainderCoefficient
  have hmajor :
      IntervalIntegrable (fun x : ℝ ↦ K * x ^ (1 / 2 : ℝ))
        volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K
  apply hmajor.mono_fun
  · exact
      aestronglyMeasurable_reducedCuspResonantD1Remainder.mono_measure
        Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    have hb := abs_reducedCuspResonantD1Remainder_le hx0 hx.2
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg
      (mul_nonneg (by norm_num)
        reducedCuspResonantRemainderCoefficient_nonneg)
      (Real.rpow_nonneg hx0.le _))]
    simpa [K] using hb

noncomputable def reducedCuspResonantConstantCoefficient : ℝ :=
  reducedLatitudeCusp 1 1 -
    reducedCuspResonantLinearCoefficient -
    ∫ y in (0 : ℝ)..1, reducedCuspResonantD1Remainder y

/-- Exact second integration of the principal-subtracted cusp. -/
theorem reducedLatitudeCusp_one_sub_resonant_model_eq_integral
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    reducedLatitudeCusp 1 x -
        (reducedCuspResonantConstantCoefficient +
          reducedCuspResonantLinearCoefficient * x +
          reducedCuspResonantPrincipalCoefficient * x * Real.log x) =
      ∫ y in (0 : ℝ)..x, reducedCuspResonantD1Remainder y := by
  have hint := intervalIntegrable_reducedCuspResonantD1Remainder
  have h0x :=
    hint.mono_set
      (uIcc_subset_uIcc (a₁ := 0) (b₁ := x)
        (a₂ := 0) (b₂ := 1) (by simp) (by simp [hx.le, hx1]))
  have hx1int :=
    hint.mono_set
      (uIcc_subset_uIcc (a₁ := x) (b₁ := 1)
        (a₂ := 0) (b₂ := 1)
        (by simp [hx.le, hx1]) (by simp))
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals h0x hx1int
  have heqOn :
      (∫ y in x..1, reducedCuspResonantD1Remainder y) =
        ∫ y in x..1,
          (reducedLatitudeCuspD1Value 1 y -
            reducedCuspResonantPrincipalCoefficient * (Real.log y + 1) -
            reducedCuspResonantLinearCoefficient) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx1] at hy
    have hy0 : 0 < y := hx.trans_le hy.1
    simp [reducedCuspResonantD1Remainder, hy0]
  let H : ℝ → ℝ := fun y ↦
    reducedLatitudeCusp 1 y -
      reducedCuspResonantPrincipalCoefficient * y * Real.log y -
      reducedCuspResonantLinearCoefficient * y
  have hFTC :
      (∫ y in x..1,
          (reducedLatitudeCuspD1Value 1 y -
            reducedCuspResonantPrincipalCoefficient * (Real.log y + 1) -
            reducedCuspResonantLinearCoefficient)) =
        H 1 - H x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro y hy
      rw [uIcc_of_le hx1] at hy
      have hy0 : 0 < y := hx.trans_le hy.1
      have hmulLog := Real.hasDerivAt_mul_log hy0.ne'
      dsimp [H]
      convert
        ((hasDerivAt_reducedLatitudeCusp
          (α := 1) hy0).sub
            ((hasDerivAt_const y
              reducedCuspResonantPrincipalCoefficient).mul hmulLog)).sub
                ((hasDerivAt_const y
                  reducedCuspResonantLinearCoefficient).mul
                    (hasDerivAt_id y)) using 1
      · funext z
        simp only [id_eq]
        ring
      · ring
    · apply ContinuousOn.intervalIntegrable_of_Icc hx1
      intro y hy
      have hy0 : 0 < y := hx.trans_le hy.1
      exact
        (((hasDerivAt_reducedLatitudeCuspD1Value
          (α := 1) hy0).continuousAt.sub
            (continuousAt_const.mul
              ((Real.continuousAt_log hy0.ne').add continuousAt_const))).sub
                continuousAt_const).continuousWithinAt
  rw [heqOn, hFTC] at hadd
  unfold reducedCuspResonantConstantCoefficient
  dsimp [H] at hadd
  rw [Real.log_one] at hadd
  ring_nf at hadd ⊢
  linarith

noncomputable def reducedCuspResonantBranchFactor (x : ℝ) : ℝ :=
  (reducedLatitudeCusp 1 x -
      (reducedCuspResonantConstantCoefficient +
        reducedCuspResonantLinearCoefficient * x +
        reducedCuspResonantPrincipalCoefficient * x * Real.log x)) /
    x ^ (3 / 2 : ℝ)

/-- Full resonant local decomposition with a constant logarithmic
coefficient and a bounded higher-order branch factor. -/
theorem reducedLatitudeCusp_one_eq_resonant_decomposition
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    reducedLatitudeCusp 1 x =
        reducedCuspResonantConstantCoefficient +
          reducedCuspResonantLinearCoefficient * x +
          reducedCuspResonantPrincipalCoefficient * x * Real.log x +
          x ^ (3 / 2 : ℝ) * reducedCuspResonantBranchFactor x ∧
      |reducedCuspResonantBranchFactor x| ≤
        (4 / 3 : ℝ) * reducedCuspResonantRemainderCoefficient := by
  have hxpow : 0 < x ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  constructor
  · unfold reducedCuspResonantBranchFactor
    field_simp [hxpow.ne']
  · let K := 2 * reducedCuspResonantRemainderCoefficient
    have hmajor :
        IntervalIntegrable (fun y : ℝ ↦ K * y ^ (1 / 2 : ℝ))
          volume 0 x :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le
      (f := reducedCuspResonantD1Remainder)
      (g := fun y : ℝ ↦ K * y ^ (1 / 2 : ℝ)) (by
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
        rw [uIoc_of_le hx.le] at hy
        have hy0 : 0 < y := hy.1
        have hb :=
          abs_reducedCuspResonantD1Remainder_le
            hy0 (hy.2.trans hx1)
        simp only [Real.norm_eq_abs]
        simpa [K] using hb) hmajor
    have hnorm' :
        |∫ y in (0 : ℝ)..x, reducedCuspResonantD1Remainder y| ≤
          |∫ y in (0 : ℝ)..x, K * y ^ (1 / 2 : ℝ)| := by
      simpa [Real.norm_eq_abs] using hnorm
    have hint :
        |∫ y in (0 : ℝ)..x, reducedCuspResonantD1Remainder y| ≤
          ((4 / 3 : ℝ) * reducedCuspResonantRemainderCoefficient) *
            x ^ (3 / 2 : ℝ) := by
      calc
        _ ≤ |∫ y in (0 : ℝ)..x, K * y ^ (1 / 2 : ℝ)| := hnorm'
        _ = ((4 / 3 : ℝ) *
              reducedCuspResonantRemainderCoefficient) *
            x ^ (3 / 2 : ℝ) := by
          rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inl (by norm_num))]
          rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by ring,
            Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0), sub_zero]
          rw [abs_of_nonneg (mul_nonneg
            (mul_nonneg (by norm_num)
              reducedCuspResonantRemainderCoefficient_nonneg)
            (div_nonneg (Real.rpow_nonneg hx.le _) (by norm_num)))]
          ring
    unfold reducedCuspResonantBranchFactor
    rw [reducedLatitudeCusp_one_sub_resonant_model_eq_integral hx hx1,
      abs_div, abs_of_pos hxpow]
    apply (div_le_iff₀ hxpow).2
    simpa [mul_assoc] using hint

end BEMOC
