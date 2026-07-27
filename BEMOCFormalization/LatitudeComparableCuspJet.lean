import BEMOCFormalization.LatitudeComparableSharpJetClosure

/-!
# Graded reduced-cusp values on the comparable fixed chart

The comparable geometry places the normalized gap in `0 < q ≤ 3200`.
This file records a uniform bound for the cusp itself and retains the sharp
individual powers for its first four derivatives.
-/

open MeasureTheory Set

namespace BEMOC

/-- The fixed chart gives the quadratic normalized-gap lower bound with
constant `3202` in place of the unavailable unit-chart constant `3`. -/
theorem normalizedLatitudeGap_quadratic_lower_fixedChart
    {s t R : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hR : 0 < R)
    (hsupper : heightRadius s ≤ 40 * R)
    (htupper : heightRadius t ≤ 40 * R)
    (hgap0 : 0 ≤ normalizedLatitudeGap s t)
    (hgap : normalizedLatitudeGap s t ≤ 3200) :
    (((3202 : ℝ) * 40 ^ 4)⁻¹) * (s - t) ^ 2 *
        (R ^ 4)⁻¹ ≤ normalizedLatitudeGap s t := by
  have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
  have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
  have hprod :
      (heightRadius s * heightRadius t) ^ 2 ≤
        (40 * R) ^ 4 := by
    have hmul :
        heightRadius s * heightRadius t ≤ (40 * R) ^ 2 := by
      calc
        heightRadius s * heightRadius t ≤ (40 * R) * (40 * R) := by
          gcongr
        _ = (40 * R) ^ 2 := by ring
    have hleft : 0 ≤ heightRadius s * heightRadius t := by positivity
    have hright : 0 ≤ (40 * R) ^ 2 := by positivity
    nlinarith
  have hid := normalizedLatitudeGap_mul_add_two hs ht
  have hx2 : normalizedLatitudeGap s t + 2 ≤ 3202 := by linarith
  have hmain :
      (s - t) ^ 2 ≤
        ((3202 : ℝ) * 40 ^ 4) * R ^ 4 *
          normalizedLatitudeGap s t := by
    rw [← hid]
    calc
      (heightRadius s * heightRadius t) ^ 2 *
          (normalizedLatitudeGap s t *
            (normalizedLatitudeGap s t + 2)) ≤
        (heightRadius s * heightRadius t) ^ 2 *
          (normalizedLatitudeGap s t * 3202) := by gcongr
      _ ≤ (40 * R) ^ 4 *
          (normalizedLatitudeGap s t * 3202) := by gcongr
      _ = ((3202 : ℝ) * 40 ^ 4) * R ^ 4 *
          normalizedLatitudeGap s t := by ring
  have hc : (0 : ℝ) < 3202 * 40 ^ 4 := by norm_num
  have hR4 : 0 < R ^ 4 := by positivity
  apply (mul_inv_le_iff₀ hR4).2
  apply (inv_mul_le_iff₀ hc).2
  nlinarith

/-- Literal separated comparable rectangles satisfy the preceding
quadratic lower bound without a chart premise. -/
theorem separatedComparableSame_rectangle_normalizedGap_quadratic_lower
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : SeparatedComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (((3202 : ℝ) * 40 ^ 4)⁻¹) * (s - t) ^ 2 *
        ((comparableLatitudeRadiusFloor N j) ^ 4)⁻¹ ≤
      normalizedLatitudeGap s t := by
  have hrect :=
    separatedComparableSame_rectangle_interior_offDiagonal hM hjk hs ht
  have hR : 0 < comparableLatitudeRadiusFloor N j := by
    unfold comparableLatitudeRadiusFloor
    have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hdr : (0 : ℝ) < latitudeBandScale N j := by
      exact_mod_cast latitudeBandScale_pos N j
    positivity
  have hupper :=
    comparableSame_rectangle_common_radius_ceiling hM hjk.1 hs ht
  have hq0 :
      0 ≤ normalizedLatitudeGap s t :=
    (normalizedLatitudeGap_pos hrect.1 hrect.2.1 hrect.2.2).le
  exact normalizedLatitudeGap_quadratic_lower_fixedChart
    hrect.1 hrect.2.1 hR hupper.1 hupper.2 hq0
      (comparableSame_rectangle_normalizedLatitudeGap_le hM hjk.1 hs ht)

/-- Every nonpositive normalized-gap power converts to the precise
separation/radius grading on a separated comparable rectangle. -/
theorem separatedComparableSame_rectangle_normalizedGap_rpow_le
    {e : ℝ} (he : e ≤ 0)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : SeparatedComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    normalizedLatitudeGap s t ^ e ≤
      (((3202 : ℝ) * 40 ^ 4)⁻¹) ^ e *
        |s - t| ^ (2 * e) *
        (comparableLatitudeRadiusFloor N j) ^ ((-4) * e) := by
  have hrect :=
    separatedComparableSame_rectangle_interior_offDiagonal hM hjk hs ht
  have hq :
      0 < normalizedLatitudeGap s t :=
    normalizedLatitudeGap_pos hrect.1 hrect.2.1 hrect.2.2
  have hR : 0 < comparableLatitudeRadiusFloor N j := by
    unfold comparableLatitudeRadiusFloor
    have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hdr : (0 : ℝ) < latitudeBandScale N j := by
      exact_mod_cast latitudeBandScale_pos N j
    positivity
  have hd : 0 < |s - t| :=
    abs_pos.mpr (sub_ne_zero.mpr hrect.2.2)
  have hlower :=
    separatedComparableSame_rectangle_normalizedGap_quadratic_lower
      hM hjk hs ht
  have hlower' :
      (((3202 : ℝ) * 40 ^ 4)⁻¹) *
          |s - t| ^ (2 : ℝ) *
          (comparableLatitudeRadiusFloor N j) ^ (-4 : ℝ) ≤
        normalizedLatitudeGap s t := by
    have habs : |s - t| ^ (2 : ℝ) = (s - t) ^ 2 := by
      rw [Real.rpow_two]
      exact sq_abs (s - t)
    have hRpow :
        (comparableLatitudeRadiusFloor N j) ^ (-4 : ℝ) =
          ((comparableLatitudeRadiusFloor N j) ^ 4)⁻¹ := by
      rw [Real.rpow_neg hR.le]
      exact congrArg Inv.inv (Real.rpow_natCast _ 4)
    rw [habs, hRpow]
    exact hlower
  exact rpow_le_of_comparable_quadratic_gap hq
    (by positivity) hd hR he hlower'

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
