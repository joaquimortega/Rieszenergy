import BEMOCFormalization.LatitudeKernelLocal
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Exact weak-singularity normal form for the latitude kernel

This file isolates the geometric normal form which is used in the local
latitude analysis.  The squared chord splits into a radial gap and a
one-dimensional angular cusp.  We also record the complete fourth-derivative
chain of the resonant model `w² log |w|`; importantly, its fourth derivative
has no logarithm.
-/

open scoped BigOperators
open MeasureTheory Set

namespace BEMOC

/-- Squared Euclidean gap between the two points of the meridian having
heights `s,t` and nonnegative horizontal coordinates. -/
noncomputable def latitudeRadialGapSq (s t : ℝ) : ℝ :=
  (s - t) ^ 2 +
    (Real.sqrt (1 - s ^ 2) - Real.sqrt (1 - t ^ 2)) ^ 2

/-- The radial gap is nonnegative without any restriction on the heights. -/
theorem latitudeRadialGapSq_nonneg (s t : ℝ) :
    0 ≤ latitudeRadialGapSq s t := by
  unfold latitudeRadialGapSq
  positivity

/-- The radial gap controls the vertical separation. -/
theorem height_sq_le_latitudeRadialGapSq (s t : ℝ) :
    (s - t) ^ 2 ≤ latitudeRadialGapSq s t := by
  unfold latitudeRadialGapSq
  nlinarith [sq_nonneg
    (Real.sqrt (1 - s ^ 2) - Real.sqrt (1 - t ^ 2))]

/-- Exact meridional-plus-angular decomposition of the squared chord. -/
theorem angularPairKernel_base_eq_radialGap_add
    {s t θ : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    2 - 2 * s * t -
          2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) *
            Real.cos θ =
      latitudeRadialGapSq s t +
        2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) *
          (1 - Real.cos θ) := by
  have hrs : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hrt : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hsqr : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 :=
    Real.sq_sqrt hrs
  have htqr : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 :=
    Real.sq_sqrt hrt
  unfold latitudeRadialGapSq
  ring_nf
  rw [hsqr, htqr]
  ring

/-- Half-angle version of the exact squared-chord decomposition. -/
theorem angularPairKernel_base_eq_radialGap_add_sin
    {s t θ : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    2 - 2 * s * t -
          2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) *
            Real.cos θ =
      latitudeRadialGapSq s t +
        4 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) *
          Real.sin (θ / 2) ^ 2 := by
  rw [angularPairKernel_base_eq_radialGap_add hs ht]
  rw [Real.sin_sq_eq_half_sub]
  rw [show 2 * (θ / 2) = θ by ring]
  ring

/-- Exact weak-cusp normal form of the pointwise angular kernel. -/
theorem angularPairKernel_eq_radialGap_cusp
    {α s t θ : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    angularPairKernel α s t θ =
      (latitudeRadialGapSq s t +
        4 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) *
          Real.sin (θ / 2) ^ 2) ^ (α / 2) := by
  unfold angularPairKernel
  rw [angularPairKernel_base_eq_radialGap_add_sin hs ht]

/-- Averaged exact weak-cusp normal form of the latitude kernel. -/
theorem latitudeKernel_eq_radialGap_cusp_average
    {α s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    latitudeKernel α s t =
      (1 / (2 * Real.pi)) *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          (latitudeRadialGapSq s t +
            4 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) *
              Real.sin (θ / 2) ^ 2) ^ (α / 2) := by
  unfold latitudeKernel
  congr 2
  funext θ
  exact angularPairKernel_eq_radialGap_cusp hs ht

/-- Natural angular scale in the radial-gap decomposition. -/
noncomputable def latitudeAngularScale (s t : ℝ) : ℝ :=
  2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)

/-- Universal one-parameter angular cusp obtained after dividing by the
positive angular scale. -/
noncomputable def reducedLatitudeCusp (α x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ θ in (0 : ℝ)..2 * Real.pi,
      (x + (1 - Real.cos θ)) ^ (α / 2)

/-- Exact scaled form of the latitude kernel away from the polar boundary.
It is the height-coordinate counterpart of `p^(α/2) hα(q/p)` in the
blueprint. -/
theorem latitudeKernel_eq_scale_mul_reducedCusp
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    latitudeKernel α s t =
      latitudeAngularScale s t ^ (α / 2) *
        reducedLatitudeCusp α
          (latitudeRadialGapSq s t / latitudeAngularScale s t) := by
  have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hrs : 0 < Real.sqrt (1 - s ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [hs.1, hs.2]
  have hrt : 0 < Real.sqrt (1 - t ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [ht.1, ht.2]
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    positivity
  have hq : 0 ≤ latitudeRadialGapSq s t :=
    latitudeRadialGapSq_nonneg s t
  have hfactor (θ : ℝ) :
      latitudeRadialGapSq s t +
          latitudeAngularScale s t * (1 - Real.cos θ) =
        latitudeAngularScale s t *
          (latitudeRadialGapSq s t / latitudeAngularScale s t +
            (1 - Real.cos θ)) := by
    field_simp [hp.ne']
    ; ring
  have hinside (θ : ℝ) :
      0 ≤ latitudeRadialGapSq s t / latitudeAngularScale s t +
        (1 - Real.cos θ) := by
    exact add_nonneg (div_nonneg hq hp.le)
      (sub_nonneg.mpr (Real.cos_le_one θ))
  rw [latitudeKernel]
  simp_rw [angularPairKernel, angularPairKernel_base_eq_radialGap_add hs' ht']
  change
    (1 / (2 * Real.pi)) *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          (latitudeRadialGapSq s t +
            latitudeAngularScale s t * (1 - Real.cos θ)) ^ (α / 2) =
      _
  simp_rw [hfactor]
  simp_rw [Real.mul_rpow hp.le (hinside _)]
  rw [intervalIntegral.integral_const_mul]
  unfold reducedLatitudeCusp
  ring

/-- The nonresonant branch model occurring in the local expansion. -/
noncomputable def latitudePowerBranch (α w : ℝ) : ℝ :=
  |w| ^ (1 + α)

/-- A convenient derivative lemma for arbitrary real powers of `|x|`,
away from zero on the positive half-line. -/
theorem hasDerivAt_const_mul_abs_rpow_of_pos
    {c p w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun x : ℝ ↦ c * |x| ^ p)
      (c * p * |w| ^ (p - 1)) w := by
  have habs : HasDerivAt (fun x : ℝ ↦ |x|) 1 w :=
    hasDerivAt_abs_pos hw
  have hpow : HasDerivAt (fun y : ℝ ↦ y ^ p)
      (p * |w| ^ (p - 1)) |w| :=
    Real.hasDerivAt_rpow_const
      (Or.inl (abs_ne_zero.mpr hw.ne'))
  convert (hasDerivAt_const w c).mul (hpow.comp w habs) using 1 ; ring

/-- The corresponding derivative lemma on the negative half-line. -/
theorem hasDerivAt_const_mul_abs_rpow_of_neg
    {c p w : ℝ} (hw : w < 0) :
    HasDerivAt (fun x : ℝ ↦ c * |x| ^ p)
      (-(c * p * |w| ^ (p - 1))) w := by
  have habs : HasDerivAt (fun x : ℝ ↦ |x|) (-1) w :=
    hasDerivAt_abs_neg hw
  have hpow : HasDerivAt (fun y : ℝ ↦ y ^ p)
      (p * |w| ^ (p - 1)) |w| :=
    Real.hasDerivAt_rpow_const
      (Or.inl (abs_ne_zero.mpr hw.ne))
  convert (hasDerivAt_const w c).mul (hpow.comp w habs) using 1 ; ring

noncomputable def latitudePowerBranchD1 (α w : ℝ) : ℝ :=
  (1 + α) * |w| ^ α

noncomputable def latitudePowerBranchD2 (α w : ℝ) : ℝ :=
  (1 + α) * α * |w| ^ (α - 1)

noncomputable def latitudePowerBranchD3 (α w : ℝ) : ℝ :=
  (1 + α) * α * (α - 1) * |w| ^ (α - 2)

noncomputable def latitudePowerBranchD4 (α w : ℝ) : ℝ :=
  (1 + α) * α * (α - 1) * (α - 2) * |w| ^ (α - 3)

/-- First link in the positive-side derivative chain of `|w|^(1+α)`. -/
theorem hasDerivAt_latitudePowerBranch_of_pos
    {α w : ℝ} (hw : 0 < w) :
    HasDerivAt (latitudePowerBranch α) (latitudePowerBranchD1 α w) w := by
  unfold latitudePowerBranch latitudePowerBranchD1
  convert hasDerivAt_const_mul_abs_rpow_of_pos
    (c := (1 : ℝ)) (p := 1 + α) hw using 1 <;> ring_nf

theorem hasDerivAt_latitudePowerBranchD1_of_pos
    {α w : ℝ} (hw : 0 < w) :
    HasDerivAt (latitudePowerBranchD1 α) (latitudePowerBranchD2 α w) w := by
  unfold latitudePowerBranchD1 latitudePowerBranchD2
  convert hasDerivAt_const_mul_abs_rpow_of_pos
    (c := 1 + α) (p := α) hw using 1

theorem hasDerivAt_latitudePowerBranchD2_of_pos
    {α w : ℝ} (hw : 0 < w) :
    HasDerivAt (latitudePowerBranchD2 α) (latitudePowerBranchD3 α w) w := by
  unfold latitudePowerBranchD2 latitudePowerBranchD3
  convert hasDerivAt_const_mul_abs_rpow_of_pos
    (c := (1 + α) * α) (p := α - 1) hw using 1 ; ring_nf

theorem hasDerivAt_latitudePowerBranchD3_of_pos
    {α w : ℝ} (hw : 0 < w) :
    HasDerivAt (latitudePowerBranchD3 α) (latitudePowerBranchD4 α w) w := by
  unfold latitudePowerBranchD3 latitudePowerBranchD4
  convert hasDerivAt_const_mul_abs_rpow_of_pos
    (c := (1 + α) * α * (α - 1)) (p := α - 2) hw using 1 ; ring_nf

/-- The same chain on the negative side.  Odd derivatives change sign and
the fourth derivative agrees with the positive-side formula. -/
theorem hasDerivAt_latitudePowerBranch_of_neg
    {α w : ℝ} (hw : w < 0) :
    HasDerivAt (latitudePowerBranch α) (-latitudePowerBranchD1 α w) w := by
  unfold latitudePowerBranch latitudePowerBranchD1
  convert hasDerivAt_const_mul_abs_rpow_of_neg
    (c := (1 : ℝ)) (p := 1 + α) hw using 1 <;> ring_nf

theorem hasDerivAt_neg_latitudePowerBranchD1_of_neg
    {α w : ℝ} (hw : w < 0) :
    HasDerivAt (fun x ↦ -latitudePowerBranchD1 α x)
      (latitudePowerBranchD2 α w) w := by
  unfold latitudePowerBranchD1 latitudePowerBranchD2
  convert hasDerivAt_const_mul_abs_rpow_of_neg
    (c := -(1 + α)) (p := α) hw using 1 <;> ring_nf

theorem hasDerivAt_latitudePowerBranchD2_of_neg
    {α w : ℝ} (hw : w < 0) :
    HasDerivAt (latitudePowerBranchD2 α) (-latitudePowerBranchD3 α w) w := by
  unfold latitudePowerBranchD2 latitudePowerBranchD3
  convert hasDerivAt_const_mul_abs_rpow_of_neg
    (c := (1 + α) * α) (p := α - 1) hw using 1 ; ring_nf

theorem hasDerivAt_neg_latitudePowerBranchD3_of_neg
    {α w : ℝ} (hw : w < 0) :
    HasDerivAt (fun x ↦ -latitudePowerBranchD3 α x)
      (latitudePowerBranchD4 α w) w := by
  unfold latitudePowerBranchD3 latitudePowerBranchD4
  convert hasDerivAt_const_mul_abs_rpow_of_neg
    (c := -((1 + α) * α * (α - 1))) (p := α - 2) hw using 1 <;> ring_nf

/-- Exact magnitude of the mixed-fourth branch coefficient.  When the
branch is composed with `s-t`, two derivatives in each variable have total
sign `+`, hence this is the model behind
`|∂s²∂t² F| ≤ C |s-t|^(α-3)`. -/
theorem abs_latitudePowerBranchD4 (α w : ℝ) :
    |latitudePowerBranchD4 α w| =
      |(1 + α) * α * (α - 1) * (α - 2)| * |w| ^ (α - 3) := by
  unfold latitudePowerBranchD4
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg w) _)]

/-- First `s` derivative of the branch kernel on the `s > t` component. -/
theorem hasDerivAt_latitudePowerBranch_sub_left_of_gt
    {α s t : ℝ} (hst : t < s) :
    HasDerivAt (fun x ↦ latitudePowerBranch α (x - t))
      (latitudePowerBranchD1 α (s - t)) s := by
  simpa [Function.comp_def] using
    (hasDerivAt_latitudePowerBranch_of_pos (sub_pos.mpr hst)).comp s
      ((hasDerivAt_id s).sub_const t)

/-- Second `s` derivative on the `s > t` component. -/
theorem hasDerivAt_latitudePowerBranchD1_sub_left_of_gt
    {α s t : ℝ} (hst : t < s) :
    HasDerivAt (fun x ↦ latitudePowerBranchD1 α (x - t))
      (latitudePowerBranchD2 α (s - t)) s := by
  simpa [Function.comp_def] using
    (hasDerivAt_latitudePowerBranchD1_of_pos (sub_pos.mpr hst)).comp s
      ((hasDerivAt_id s).sub_const t)

/-- After the two `s` derivatives, the first `t` derivative has the expected
minus sign on the `s > t` component. -/
theorem hasDerivAt_latitudePowerBranchD2_sub_right_of_gt
    {α s t : ℝ} (hst : t < s) :
    HasDerivAt (fun y ↦ latitudePowerBranchD2 α (s - y))
      (-latitudePowerBranchD3 α (s - t)) t := by
  convert
    (hasDerivAt_latitudePowerBranchD2_of_pos (sub_pos.mpr hst)).comp t
      ((hasDerivAt_const t s).sub (hasDerivAt_id t)) using 1 ; ring

/-- The second `t` derivative completes the mixed `s²t²` chain and equals
the fourth one-variable derivative. -/
theorem hasDerivAt_neg_latitudePowerBranchD3_sub_right_of_gt
    {α s t : ℝ} (hst : t < s) :
    HasDerivAt (fun y ↦ -latitudePowerBranchD3 α (s - y))
      (latitudePowerBranchD4 α (s - t)) t := by
  convert
    (hasDerivAt_latitudePowerBranchD3_of_pos (sub_pos.mpr hst)).neg.comp t
      ((hasDerivAt_const t s).sub (hasDerivAt_id t)) using 1 ; ring

/-- First `s` derivative on the reflected `s < t` component. -/
theorem hasDerivAt_latitudePowerBranch_sub_left_of_lt
    {α s t : ℝ} (hst : s < t) :
    HasDerivAt (fun x ↦ latitudePowerBranch α (x - t))
      (-latitudePowerBranchD1 α (s - t)) s := by
  simpa [Function.comp_def] using
    (hasDerivAt_latitudePowerBranch_of_neg (sub_neg.mpr hst)).comp s
      ((hasDerivAt_id s).sub_const t)

/-- Second `s` derivative on the reflected `s < t` component. -/
theorem hasDerivAt_neg_latitudePowerBranchD1_sub_left_of_lt
    {α s t : ℝ} (hst : s < t) :
    HasDerivAt (fun x ↦ -latitudePowerBranchD1 α (x - t))
      (latitudePowerBranchD2 α (s - t)) s := by
  simpa [Function.comp_def] using
    (hasDerivAt_neg_latitudePowerBranchD1_of_neg (sub_neg.mpr hst)).comp s
      ((hasDerivAt_id s).sub_const t)

/-- First `t` derivative after the two `s` derivatives on `s < t`. -/
theorem hasDerivAt_latitudePowerBranchD2_sub_right_of_lt
    {α s t : ℝ} (hst : s < t) :
    HasDerivAt (fun y ↦ latitudePowerBranchD2 α (s - y))
      (latitudePowerBranchD3 α (s - t)) t := by
  convert
    (hasDerivAt_latitudePowerBranchD2_of_neg (sub_neg.mpr hst)).comp t
      ((hasDerivAt_const t s).sub (hasDerivAt_id t)) using 1 ; ring

/-- Completion of the mixed chain on `s < t`; again the answer is `D4`. -/
theorem hasDerivAt_latitudePowerBranchD3_sub_right_of_lt
    {α s t : ℝ} (hst : s < t) :
    HasDerivAt (fun y ↦ latitudePowerBranchD3 α (s - y))
      (latitudePowerBranchD4 α (s - t)) t := by
  have h :=
    (hasDerivAt_neg_latitudePowerBranchD3_of_neg
      (α := α) (sub_neg.mpr hst)).neg.comp t
      ((hasDerivAt_const t s).sub (hasDerivAt_id t))
  simpa [Function.comp_def] using h

/-- The resonant branch model.  Mathlib's real logarithm satisfies
`log w = log |w|`, so this is exactly `w² log |w|`. -/
noncomputable def resonantLatitudeBranch (w : ℝ) : ℝ :=
  w ^ 2 * Real.log w

theorem resonantLatitudeBranch_eq_sq_mul_log_abs (w : ℝ) :
    resonantLatitudeBranch w = w ^ 2 * Real.log |w| := by
  rw [resonantLatitudeBranch, Real.log_abs]

/-- First derivative of the resonant branch away from the diagonal. -/
theorem hasDerivAt_resonantLatitudeBranch
    {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt resonantLatitudeBranch
      (2 * w * Real.log w + w) w := by
  unfold resonantLatitudeBranch
  convert ((hasDerivAt_pow 2 w).mul (Real.hasDerivAt_log hw)) using 1 ;
    field_simp [hw] ; ring

/-- Second derivative in a derivative chain for the resonant branch. -/
theorem hasDerivAt_resonantLatitudeBranch_first
    {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ 2 * x * Real.log x + x)
      (2 * Real.log w + 3) w := by
  convert
    (((hasDerivAt_const w 2).mul (hasDerivAt_id w)).mul
      (Real.hasDerivAt_log hw) |>.add (hasDerivAt_id w)) using 1 ;
    field_simp ; ring

/-- Third derivative in a derivative chain for the resonant branch. -/
theorem hasDerivAt_resonantLatitudeBranch_second
    {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ 2 * Real.log x + 3)
      (2 / w) w := by
  convert ((hasDerivAt_const w 2).mul (Real.hasDerivAt_log hw) |>.add_const 3)
    using 1 ; field_simp

/-- Fourth derivative in a derivative chain for the resonant branch.  This
is the key resonance fact: after four derivatives no logarithm remains. -/
theorem hasDerivAt_resonantLatitudeBranch_third
    {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ 2 / x)
      (-2 / w ^ 2) w := by
  convert (hasDerivAt_const w 2).div (hasDerivAt_id w) hw using 1 ;
    field_simp

/-- Quantitative fourth-derivative estimate for the `α = 1` branch model. -/
theorem abs_resonantLatitudeBranch_fourth
    {w : ℝ} (_hw : w ≠ 0) :
    |-2 / w ^ 2| = 2 / |w| ^ 2 := by
  rw [abs_div, abs_neg, abs_pow]
  norm_num

/-- First `s` derivative of the resonant branch kernel off the diagonal. -/
theorem hasDerivAt_resonantLatitudeBranch_sub_left
    {s t : ℝ} (hst : s ≠ t) :
    HasDerivAt (fun x ↦ resonantLatitudeBranch (x - t))
      (2 * (s - t) * Real.log (s - t) + (s - t)) s := by
  simpa [Function.comp_def] using
    (hasDerivAt_resonantLatitudeBranch (sub_ne_zero.mpr hst)).comp s
      ((hasDerivAt_id s).sub_const t)

/-- Second `s` derivative of the resonant branch kernel. -/
theorem hasDerivAt_resonantLatitudeBranch_first_sub_left
    {s t : ℝ} (hst : s ≠ t) :
    HasDerivAt
      (fun x ↦ 2 * (x - t) * Real.log (x - t) + (x - t))
      (2 * Real.log (s - t) + 3) s := by
  simpa [Function.comp_def] using
    (hasDerivAt_resonantLatitudeBranch_first (sub_ne_zero.mpr hst)).comp s
      ((hasDerivAt_id s).sub_const t)

/-- First `t` derivative after the two `s` derivatives in the resonant
mixed chain. -/
theorem hasDerivAt_resonantLatitudeBranch_second_sub_right
    {s t : ℝ} (hst : s ≠ t) :
    HasDerivAt (fun y ↦ 2 * Real.log (s - y) + 3)
      (-(2 / (s - t))) t := by
  convert
    (hasDerivAt_resonantLatitudeBranch_second (sub_ne_zero.mpr hst)).comp t
      ((hasDerivAt_const t s).sub (hasDerivAt_id t)) using 1 ; ring

/-- Completion of the resonant mixed `s²t²` chain.  The endpoint contains
no logarithm and has the sharp inverse-square singularity. -/
theorem hasDerivAt_neg_resonantLatitudeBranch_third_sub_right
    {s t : ℝ} (hst : s ≠ t) :
    HasDerivAt (fun y ↦ -(2 / (s - y)))
      (-2 / (s - t) ^ 2) t := by
  convert
    (hasDerivAt_resonantLatitudeBranch_third
      (sub_ne_zero.mpr hst)).neg.comp t
      ((hasDerivAt_const t s).sub (hasDerivAt_id t)) using 1 ;
    field_simp [sub_ne_zero.mpr hst]

end BEMOC
