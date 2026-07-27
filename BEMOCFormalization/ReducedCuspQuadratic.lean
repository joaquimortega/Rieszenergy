import BEMOCFormalization.ReducedCuspDerivatives

/-!
# Transfer of reduced-cusp bounds through a quadratic gap

The local radial gap is quadratic in the transverse height difference to
leading order.  This file records the exact fourth-order chain rule for the
canonical model `hα(c w²)`.  It is the reusable algebraic transfer from the
angular moment estimates to the `|w|^(α-3)` mixed-derivative scale.
-/

open Set

namespace BEMOC

noncomputable def reducedCuspQuadratic (α c w : ℝ) : ℝ :=
  reducedLatitudeCusp α (c * w ^ 2)

noncomputable def reducedCuspQuadraticD1 (α c w : ℝ) : ℝ :=
  2 * c * w * reducedLatitudeCuspD1Value α (c * w ^ 2)

noncomputable def reducedCuspQuadraticD2 (α c w : ℝ) : ℝ :=
  2 * c * reducedLatitudeCuspD1Value α (c * w ^ 2) +
    4 * c ^ 2 * w ^ 2 * reducedLatitudeCuspD2Value α (c * w ^ 2)

noncomputable def reducedCuspQuadraticD3 (α c w : ℝ) : ℝ :=
  12 * c ^ 2 * w * reducedLatitudeCuspD2Value α (c * w ^ 2) +
    8 * c ^ 3 * w ^ 3 * reducedLatitudeCuspD3Value α (c * w ^ 2)

noncomputable def reducedCuspQuadraticD4 (α c w : ℝ) : ℝ :=
  12 * c ^ 2 * reducedLatitudeCuspD2Value α (c * w ^ 2) +
    48 * c ^ 3 * w ^ 2 * reducedLatitudeCuspD3Value α (c * w ^ 2) +
    16 * c ^ 4 * w ^ 4 * reducedLatitudeCuspD4Value α (c * w ^ 2)

theorem hasDerivAt_reducedCuspQuadratic
    {α c w : ℝ} (hc : 0 < c) (hw : w ≠ 0) :
    HasDerivAt (reducedCuspQuadratic α c)
      (reducedCuspQuadraticD1 α c w) w := by
  have hx : 0 < c * w ^ 2 := mul_pos hc (sq_pos_of_ne_zero hw)
  have hinner :
      HasDerivAt (fun y : ℝ ↦ c * y ^ 2) (2 * c * w) w := by
    convert (hasDerivAt_const w c).mul (hasDerivAt_pow 2 w) using 1 <;> ring
  unfold reducedCuspQuadratic reducedCuspQuadraticD1
  convert (hasDerivAt_reducedLatitudeCusp (α := α) hx).comp w hinner using 1 <;>
    ring

theorem hasDerivAt_reducedCuspQuadraticD1
    {α c w : ℝ} (hc : 0 < c) (hw : w ≠ 0) :
    HasDerivAt (reducedCuspQuadraticD1 α c)
      (reducedCuspQuadraticD2 α c w) w := by
  have hx : 0 < c * w ^ 2 := mul_pos hc (sq_pos_of_ne_zero hw)
  have hinner :
      HasDerivAt (fun y : ℝ ↦ c * y ^ 2) (2 * c * w) w := by
    convert (hasDerivAt_const w c).mul (hasDerivAt_pow 2 w) using 1 <;> ring
  have hout :=
    (hasDerivAt_reducedLatitudeCuspD1Value (α := α) hx).comp w hinner
  unfold reducedCuspQuadraticD1 reducedCuspQuadraticD2
  convert
    (((hasDerivAt_const w (2 * c)).mul (hasDerivAt_id w)).mul hout)
      using 1 <;> simp only [Function.comp_apply, id_eq] <;> ring

theorem hasDerivAt_reducedCuspQuadraticD2
    {α c w : ℝ} (hc : 0 < c) (hw : w ≠ 0) :
    HasDerivAt (reducedCuspQuadraticD2 α c)
      (reducedCuspQuadraticD3 α c w) w := by
  have hx : 0 < c * w ^ 2 := mul_pos hc (sq_pos_of_ne_zero hw)
  have hinner :
      HasDerivAt (fun y : ℝ ↦ c * y ^ 2) (2 * c * w) w := by
    convert (hasDerivAt_const w c).mul (hasDerivAt_pow 2 w) using 1 <;> ring
  have hD1 :=
    (hasDerivAt_reducedLatitudeCuspD1Value (α := α) hx).comp w hinner
  have hD2 :=
    (hasDerivAt_reducedLatitudeCuspD2Value (α := α) hx).comp w hinner
  unfold reducedCuspQuadraticD2 reducedCuspQuadraticD3
  convert
    ((hasDerivAt_const w (2 * c)).mul hD1).add
      ((((hasDerivAt_const w (4 * c ^ 2)).mul
        (hasDerivAt_pow 2 w)).mul hD2)) using 1 <;>
    simp only [Function.comp_apply, id_eq] <;> ring

theorem hasDerivAt_reducedCuspQuadraticD3
    {α c w : ℝ} (hc : 0 < c) (hw : w ≠ 0) :
    HasDerivAt (reducedCuspQuadraticD3 α c)
      (reducedCuspQuadraticD4 α c w) w := by
  have hx : 0 < c * w ^ 2 := mul_pos hc (sq_pos_of_ne_zero hw)
  have hinner :
      HasDerivAt (fun y : ℝ ↦ c * y ^ 2) (2 * c * w) w := by
    convert (hasDerivAt_const w c).mul (hasDerivAt_pow 2 w) using 1 <;> ring
  have hD2 :=
    (hasDerivAt_reducedLatitudeCuspD2Value (α := α) hx).comp w hinner
  have hD3 :=
    (hasDerivAt_reducedLatitudeCuspD3Value (α := α) hx).comp w hinner
  unfold reducedCuspQuadraticD3 reducedCuspQuadraticD4
  convert
    ((((hasDerivAt_const w (12 * c ^ 2)).mul
      (hasDerivAt_id w)).mul hD2).add
      ((((hasDerivAt_const w (8 * c ^ 3)).mul
        (hasDerivAt_pow 3 w)).mul hD3))) using 1 <;>
    simp only [Function.comp_apply, id_eq] <;> ring

/-- Quantitative fourth derivative bound after the quadratic transfer.
Every term on the right has the same `|w|^(α-3)` homogeneity after the
clean moment bounds are substituted. -/
theorem abs_reducedCuspQuadraticD4_le
    {α c w : ℝ} (hc : 0 < c) (hw : w ≠ 0) (hα : α ≤ 2) :
    |reducedCuspQuadraticD4 α c w| ≤
      12 * c ^ 2 * |reducedLatitudeCuspD2Value α (c * w ^ 2)| +
      48 * c ^ 3 * |w| ^ 2 *
        |reducedLatitudeCuspD3Value α (c * w ^ 2)| +
      16 * c ^ 4 * |w| ^ 4 *
        |reducedLatitudeCuspD4Value α (c * w ^ 2)| := by
  have hc0 : 0 ≤ c := hc.le
  unfold reducedCuspQuadraticD4
  calc
    |12 * c ^ 2 * reducedLatitudeCuspD2Value α (c * w ^ 2) +
        48 * c ^ 3 * w ^ 2 * reducedLatitudeCuspD3Value α (c * w ^ 2) +
        16 * c ^ 4 * w ^ 4 * reducedLatitudeCuspD4Value α (c * w ^ 2)| ≤
      |12 * c ^ 2 * reducedLatitudeCuspD2Value α (c * w ^ 2)| +
        |48 * c ^ 3 * w ^ 2 * reducedLatitudeCuspD3Value α (c * w ^ 2)| +
        |16 * c ^ 4 * w ^ 4 * reducedLatitudeCuspD4Value α (c * w ^ 2)| := by
          exact (abs_add _ _).trans
            (add_le_add_right (abs_add _ _) _)
    _ = _ := by
      simp only [abs_mul, abs_pow, abs_of_nonneg hc0]
      norm_num

end BEMOC
