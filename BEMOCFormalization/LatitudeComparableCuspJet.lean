import BEMOCFormalization.LatitudeComparableSharpJetClosure

/-!
# Graded reduced-cusp values on the comparable fixed chart

The comparable geometry places the normalized gap in `0 < q ≤ 3200`.
This file records a uniform bound for the cusp itself and retains the sharp
individual powers for its first four derivatives.
-/

open MeasureTheory Set

namespace BEMOC

theorem abs_reducedLatitudeCusp_le_fixedChart
    {α x : ℝ} (hα0 : 0 < α) (hx0 : 0 ≤ x) (hx : x ≤ 3200) :
    |reducedLatitudeCusp α x| ≤ (3202 : ℝ) ^ (α / 2) := by
  have hβ : 0 ≤ α / 2 := by linarith
  have hmoment0 :
      0 ≤ reducedCuspMoment (α / 2) x :=
    reducedCuspMoment_nonneg hx0
  rw [reducedLatitudeCusp_eq_moment, abs_of_nonneg hmoment0]
  let f : ℝ → ℝ := fun θ ↦
    (x + (1 - Real.cos θ)) ^ (α / 2)
  have hfcont : Continuous f := by
    dsimp [f]
    exact
      (continuous_const.add
        (continuous_const.sub Real.continuous_cos)).rpow_const
          (fun _ ↦ Or.inr (by linarith : 0 ≤ α / 2))
  have hpoint (θ : ℝ) :
      f θ ≤ (3202 : ℝ) ^ (α / 2) := by
    dsimp [f]
    apply Real.rpow_le_rpow
    · exact add_nonneg hx0 (sub_nonneg.mpr (Real.cos_le_one θ))
    · have hcos := Real.neg_one_le_cos θ
      linarith
    · exact hβ
  have hmono :=
    intervalIntegral.integral_mono_on
      (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
      (f := f) (g := fun _ : ℝ ↦ (3202 : ℝ) ^ (α / 2))
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hfcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
      (fun θ _ ↦ hpoint θ)
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  unfold reducedCuspMoment
  change (1 / (2 * Real.pi)) *
      (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) ≤
        (3202 : ℝ) ^ (α / 2)
  calc
    (1 / (2 * Real.pi)) *
        (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) ≤
      (1 / (2 * Real.pi)) *
        (∫ _θ in (0 : ℝ)..2 * Real.pi,
          (3202 : ℝ) ^ (α / 2)) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (3202 : ℝ) ^ (α / 2) := by
      rw [intervalIntegral.integral_const]
      field_simp

noncomputable def latitudeComparableCuspDerivativeConstant
    (α : ℝ) : ℝ :=
  1 + (3202 : ℝ) ^ (α / 2) + |α / 2| +
    |(α / 2) * (α / 2 - 1)| *
      (Real.pi / (2 * Real.sqrt 2)) +
    |(α / 2) * (α / 2 - 1) * (α / 2 - 2)| *
      (Real.pi / (2 * Real.sqrt 2)) +
    |(α / 2) * (α / 2 - 1) * (α / 2 - 2) *
      (α / 2 - 3)| * (Real.pi / (2 * Real.sqrt 2))

def LatitudeComparableCuspDerivativeBound
    (α x A : ℝ) : Prop :=
  0 ≤ A ∧
  |reducedLatitudeCusp α x| ≤ A ∧
  |reducedLatitudeCuspD1Value α x| ≤
    A * x ^ (α / 2 - 1) ∧
  |reducedLatitudeCuspD2Value α x| ≤
    A * x ^ (α / 2 - 3 / 2) ∧
  |reducedLatitudeCuspD3Value α x| ≤
    A * x ^ (α / 2 - 5 / 2) ∧
  |reducedLatitudeCuspD4Value α x| ≤
    A * x ^ (α / 2 - 7 / 2)

theorem latitudeComparableCuspDerivativeBound
    {α x : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hx0 : 0 < x) (hx : x ≤ 3200) :
    LatitudeComparableCuspDerivativeBound α x
      (latitudeComparableCuspDerivativeConstant α) := by
  let A := latitudeComparableCuspDerivativeConstant α
  have hpi : 0 ≤ Real.pi / (2 * Real.sqrt 2) := by positivity
  have hA : 0 ≤ A := by
    dsimp [A, latitudeComparableCuspDerivativeConstant]
    positivity
  have hn0 : 0 ≤ (3202 : ℝ) ^ (α / 2) := by positivity
  have hn1 : 0 ≤ |α / 2| := abs_nonneg _
  have hn2 : 0 ≤ |(α / 2) * (α / 2 - 1)| *
      (Real.pi / (2 * Real.sqrt 2)) := mul_nonneg (abs_nonneg _) hpi
  have hn3 : 0 ≤
      |(α / 2) * (α / 2 - 1) * (α / 2 - 2)| *
        (Real.pi / (2 * Real.sqrt 2)) :=
    mul_nonneg (abs_nonneg _) hpi
  have hn4 : 0 ≤
      |(α / 2) * (α / 2 - 1) * (α / 2 - 2) *
        (α / 2 - 3)| * (Real.pi / (2 * Real.sqrt 2)) :=
    mul_nonneg (abs_nonneg _) hpi
  have h0c : (3202 : ℝ) ^ (α / 2) ≤ A := by
    dsimp [A, latitudeComparableCuspDerivativeConstant]
    linarith
  have h1c : |α / 2| ≤ A := by
    dsimp [A, latitudeComparableCuspDerivativeConstant]
    linarith
  have h2c :
      |(α / 2) * (α / 2 - 1)| *
          (Real.pi / (2 * Real.sqrt 2)) ≤ A := by
    dsimp [A, latitudeComparableCuspDerivativeConstant]
    linarith
  have h3c :
      |(α / 2) * (α / 2 - 1) * (α / 2 - 2)| *
          (Real.pi / (2 * Real.sqrt 2)) ≤ A := by
    dsimp [A, latitudeComparableCuspDerivativeConstant]
    linarith
  have h4c :
      |(α / 2) * (α / 2 - 1) * (α / 2 - 2) *
          (α / 2 - 3)| *
          (Real.pi / (2 * Real.sqrt 2)) ≤ A := by
    dsimp [A, latitudeComparableCuspDerivativeConstant]
    linarith
  refine ⟨hA,
    (abs_reducedLatitudeCusp_le_fixedChart hα0 hx0.le hx).trans h0c,
    ?_, ?_, ?_, ?_⟩
  · exact (abs_reducedLatitudeCuspD1Value_le hx0 hα2.le).trans
      (mul_le_mul_of_nonneg_right h1c (Real.rpow_nonneg hx0.le _))
  · exact (abs_reducedLatitudeCuspD2Value_le_rpow hx0 hα2.le).trans
      (mul_le_mul_of_nonneg_right h2c (Real.rpow_nonneg hx0.le _))
  · exact (abs_reducedLatitudeCuspD3Value_le_rpow hx0 hα2.le).trans
      (mul_le_mul_of_nonneg_right h3c (Real.rpow_nonneg hx0.le _))
  · exact (abs_reducedLatitudeCuspD4Value_le_rpow hx0 hα2.le).trans
      (mul_le_mul_of_nonneg_right h4c (Real.rpow_nonneg hx0.le _))

end BEMOC
