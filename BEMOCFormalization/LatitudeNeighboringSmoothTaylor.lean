import BEMOCFormalization.LatitudeNeighboringAnalytic
import BEMOCFormalization.LatitudeMixedTaylorSpecialization

/-!
# A diagonal-valid tensor Taylor estimate for neighboring smooth kernels

The affine analytic part of every neighboring reduced cusp is a linear
combination of two honest powers of the positive angular scale.  Consequently
its derivative chain remains valid on the diagonal.  This file records that
chain and applies the explicit one-variable Taylor estimate twice.
-/

open Set

namespace BEMOC

noncomputable def neighboringAffineSmoothKernelDs
    (α H L s t : ℝ) : ℝ :=
  (H - L) * latitudePowerDs α s t +
    2 * L * (-t * latitudePower (α - 2) s t +
      (1 - s * t) * latitudePowerDs (α - 2) s t)

noncomputable def neighboringAffineSmoothKernelDss
    (α H L s t : ℝ) : ℝ :=
  (H - L) * latitudePowerDss α s t +
    2 * L * ((1 - s * t) * latitudePowerDss (α - 2) s t -
      2 * t * latitudePowerDs (α - 2) s t)

noncomputable def neighboringAffineSmoothKernelDst
    (α H L s t : ℝ) : ℝ :=
  (H - L) * latitudePowerDst α s t +
    2 * L * (-latitudePower (α - 2) s t -
      t * latitudePowerDt (α - 2) s t -
      s * latitudePowerDs (α - 2) s t +
      (1 - s * t) * latitudePowerDst (α - 2) s t)

noncomputable def neighboringAffineSmoothKernelDstt
    (α H L s t : ℝ) : ℝ :=
  (H - L) * latitudePowerDstt α s t +
    2 * L * (-2 * latitudePowerDt (α - 2) s t -
      t * latitudePowerDtt (α - 2) s t -
      2 * s * latitudePowerDst (α - 2) s t +
      (1 - s * t) * latitudePowerDstt (α - 2) s t)

noncomputable def neighboringAffineSmoothKernelDsst
    (α H L s t : ℝ) : ℝ :=
  (H - L) * latitudePowerDsst α s t +
    2 * L * (-s * latitudePowerDss (α - 2) s t +
      (1 - s * t) * latitudePowerDsst (α - 2) s t -
      2 * latitudePowerDs (α - 2) s t -
      2 * t * latitudePowerDst (α - 2) s t)

theorem hasDerivAt_latitudePower_left
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x ↦ latitudePower α x t)
      (latitudePowerDs α s t) s := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos
      (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  unfold latitudePower latitudePowerDs
  convert
    (Real.hasDerivAt_rpow_const (x := latitudeAngularScale s t)
      (p := α / 2) (Or.inl hp.ne')).comp s
        (hasDerivAt_latitudeAngularScale_left (s := s) (t := t) hs)
      using 1 <;>
    simp only [Function.comp_apply] <;> ring

theorem hasDerivAt_latitudePowerDs_left
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x ↦ latitudePowerDs α x t)
      (latitudePowerDss α s t) s := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos
      (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hpow :
      HasDerivAt
        (fun x ↦ latitudeAngularScale x t ^ (α / 2 - 1))
        ((α / 2 - 1) * latitudeAngularScale s t ^ (α / 2 - 2) *
          latitudeAngularScaleDs s t) s := by
    have he : α / 2 - 1 - 1 = α / 2 - 2 := by ring
    simpa only [Function.comp_apply, he] using
      (Real.hasDerivAt_rpow_const (x := latitudeAngularScale s t)
        (p := α / 2 - 1) (Or.inl hp.ne')).comp s
          (hasDerivAt_latitudeAngularScale_left (s := s) (t := t) hs)
  unfold latitudePowerDs latitudePowerDss
  convert
    (((hasDerivAt_const s (α / 2)).mul hpow).mul
      (hasDerivAt_latitudeAngularScaleDs_left (s := s) (t := t) hs))
      using 1 <;>
    ring

theorem hasDerivAt_neighboringAffineSmoothKernel_left
    {α H L s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x ↦ neighboringAffineSmoothKernel α H L x t)
      (neighboringAffineSmoothKernelDs α H L s t) s := by
  have hP := hasDerivAt_latitudePower_left (α := α) hs ht
  have hQ := hasDerivAt_latitudePower_left (α := α - 2) hs ht
  unfold neighboringAffineSmoothKernel neighboringAffineSmoothKernelDs
  have h :=
    ((hasDerivAt_const s (H - L)).mul hP).add
      ((hasDerivAt_const s (2 * L)).mul
        (((hasDerivAt_const s 1).sub
          ((hasDerivAt_id s).mul_const t)).mul hQ))
  convert h using 1
  · funext x
    simp only [id_eq]
    ring
  · simp only [id_eq]
    ring

theorem hasDerivAt_neighboringAffineSmoothKernelDs_right
    {α H L s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ neighboringAffineSmoothKernelDs α H L s y)
      (neighboringAffineSmoothKernelDst α H L s t) t := by
  have hP := hasDerivAt_latitudePowerDs_right (α := α) hs ht
  have hQ := hasDerivAt_latitudePower_right (α := α - 2) hs ht
  have hQs := hasDerivAt_latitudePowerDs_right (α := α - 2) hs ht
  unfold neighboringAffineSmoothKernelDs neighboringAffineSmoothKernelDst
  convert
    ((hasDerivAt_const t (H - L)).mul hP).add
      ((hasDerivAt_const t (2 * L)).mul
        (((hasDerivAt_id t).neg.mul hQ).add
          (((hasDerivAt_const t 1).sub
            ((hasDerivAt_const t s).mul (hasDerivAt_id t))).mul hQs)))
      using 1 <;>
    (try { funext y }) <;> simp only [id_eq] <;> ring

theorem hasDerivAt_neighboringAffineSmoothKernelDst_right
    {α H L s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ neighboringAffineSmoothKernelDst α H L s y)
      (neighboringAffineSmoothKernelDstt α H L s t) t := by
  have hP := hasDerivAt_latitudePowerDst_right (α := α) hs ht
  have hQ := hasDerivAt_latitudePower_right (α := α - 2) hs ht
  have hQt := hasDerivAt_latitudePowerDt_right (α := α - 2) hs ht
  have hQs := hasDerivAt_latitudePowerDs_right (α := α - 2) hs ht
  have hQst := hasDerivAt_latitudePowerDst_right (α := α - 2) hs ht
  unfold neighboringAffineSmoothKernelDst neighboringAffineSmoothKernelDstt
  have hinside :=
    (((hQ.neg.sub ((hasDerivAt_id t).mul hQt)).sub
      ((hasDerivAt_const t s).mul hQs)).add
      (((hasDerivAt_const t 1).sub
        ((hasDerivAt_const t s).mul (hasDerivAt_id t))).mul hQst))
  convert
    ((hasDerivAt_const t (H - L)).mul hP).add
      ((hasDerivAt_const t (2 * L)).mul hinside)
      using 1 <;>
    (try { funext y }) <;> simp only [id_eq] <;> ring

theorem hasDerivAt_neighboringAffineSmoothKernelDs_left
    {α H L s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x ↦ neighboringAffineSmoothKernelDs α H L x t)
      (neighboringAffineSmoothKernelDss α H L s t) s := by
  have hP := hasDerivAt_latitudePowerDs_left (α := α) hs ht
  have hQ := hasDerivAt_latitudePower_left (α := α - 2) hs ht
  have hQs := hasDerivAt_latitudePowerDs_left (α := α - 2) hs ht
  unfold neighboringAffineSmoothKernelDs neighboringAffineSmoothKernelDss
  convert
    ((hasDerivAt_const s (H - L)).mul hP).add
      ((hasDerivAt_const s (2 * L)).mul
        (((hasDerivAt_const s (-t)).mul hQ).add
          (((hasDerivAt_const s 1).sub
            ((hasDerivAt_id s).mul_const t)).mul hQs)))
      using 1 <;>
    (try { funext x }) <;> simp only [id_eq] <;> ring

theorem hasDerivAt_neighboringAffineSmoothKernelDss_right
    {α H L s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ neighboringAffineSmoothKernelDss α H L s y)
      (neighboringAffineSmoothKernelDsst α H L s t) t := by
  have hP := hasDerivAt_latitudePowerDss_right (α := α) hs ht
  have hQ := hasDerivAt_latitudePowerDss_right (α := α - 2) hs ht
  have hQs := hasDerivAt_latitudePowerDs_right (α := α - 2) hs ht
  unfold neighboringAffineSmoothKernelDss neighboringAffineSmoothKernelDsst
  convert
    ((hasDerivAt_const t (H - L)).mul hP).add
      ((hasDerivAt_const t (2 * L)).mul
        (((((hasDerivAt_const t 1).sub
            ((hasDerivAt_const t s).mul (hasDerivAt_id t))).mul hQ).sub
          (((hasDerivAt_const t 2).mul (hasDerivAt_id t)).mul hQs))))
      using 1 <;>
    (try { funext y }) <;> simp only [id_eq] <;> ring

theorem hasDerivAt_neighboringAffineSmoothKernelDsst_right
    {α H L s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y ↦ neighboringAffineSmoothKernelDsst α H L s y)
      (neighboringAffineSmoothKernelDsstt α H L s t) t := by
  have hP := hasDerivAt_latitudePowerDsst_right (α := α) hs ht
  have hQss := hasDerivAt_latitudePowerDss_right (α := α - 2) hs ht
  have hQsst := hasDerivAt_latitudePowerDsst_right (α := α - 2) hs ht
  have hQs := hasDerivAt_latitudePowerDs_right (α := α - 2) hs ht
  have hQst := hasDerivAt_latitudePowerDst_right (α := α - 2) hs ht
  unfold neighboringAffineSmoothKernelDsst neighboringAffineSmoothKernelDsstt
  convert
    ((hasDerivAt_const t (H - L)).mul hP).add
      ((hasDerivAt_const t (2 * L)).mul
        (((((hasDerivAt_const t (-s)).mul hQss).add
          (((hasDerivAt_const t 1).sub
            ((hasDerivAt_const t s).mul (hasDerivAt_id t))).mul hQsst)).sub
          ((hasDerivAt_const t 2).mul hQs)).sub
          (((hasDerivAt_const t 2).mul (hasDerivAt_id t)).mul hQst)))
      using 1 <;>
    (try { funext y }) <;> simp only [id_eq] <;> ring

theorem neighboringAffineSmoothKernelDstt_eq_Dsst_swap
    (α H L s t : ℝ) :
    neighboringAffineSmoothKernelDstt α H L s t =
      neighboringAffineSmoothKernelDsst α H L t s := by
  unfold neighboringAffineSmoothKernelDstt neighboringAffineSmoothKernelDsst
  rw [latitudePowerDstt_eq_Dsst_swap,
    latitudePowerDt_eq_Ds_swap,
    latitudePowerDtt_eq_Dss_swap,
    latitudePowerDst_comm,
    latitudePowerDstt_eq_Dsst_swap]
  ring

noncomputable def neighboringSmoothRightTaylorError
    (α H L c s t : ℝ) : ℝ :=
  neighboringAffineSmoothKernel α H L s t -
    neighboringAffineSmoothKernel α H L s c -
      (t - c) * neighboringAffineSmoothKernelDs α H L c s

noncomputable def neighboringSmoothRightTaylorErrorDs
    (α H L c s t : ℝ) : ℝ :=
  neighboringAffineSmoothKernelDs α H L s t -
    neighboringAffineSmoothKernelDs α H L s c -
      (t - c) * neighboringAffineSmoothKernelDst α H L c s

noncomputable def neighboringSmoothRightTaylorErrorDss
    (α H L c s t : ℝ) : ℝ :=
  neighboringAffineSmoothKernelDss α H L s t -
    neighboringAffineSmoothKernelDss α H L s c -
      (t - c) * neighboringAffineSmoothKernelDstt α H L c s

noncomputable def neighboringSmoothMixedRemainder
    (α H L a c s t : ℝ) : ℝ :=
  neighboringSmoothRightTaylorError α H L c s t -
    neighboringSmoothRightTaylorError α H L c a t -
      (s - a) * neighboringSmoothRightTaylorErrorDs α H L c a t

theorem hasDerivAt_neighboringSmoothRightTaylorError_left
    {α H L c s t : ℝ}
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x ↦ neighboringSmoothRightTaylorError α H L c x t)
      (neighboringSmoothRightTaylorErrorDs α H L c s t) s := by
  have hK := hasDerivAt_neighboringAffineSmoothKernel_left
    (α := α) (H := H) (L := L) hs ht
  have hKc := hasDerivAt_neighboringAffineSmoothKernel_left
    (α := α) (H := H) (L := L) hs hc
  have hDs := hasDerivAt_neighboringAffineSmoothKernelDs_right
    (α := α) (H := H) (L := L) hc hs
  unfold neighboringSmoothRightTaylorError neighboringSmoothRightTaylorErrorDs
  convert (hK.sub hKc).sub ((hasDerivAt_const s (t - c)).mul hDs)
    using 1 <;> ring

theorem hasDerivAt_neighboringSmoothRightTaylorErrorDs_left
    {α H L c s t : ℝ}
    (hc : c ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x ↦ neighboringSmoothRightTaylorErrorDs α H L c x t)
      (neighboringSmoothRightTaylorErrorDss α H L c s t) s := by
  have hK := hasDerivAt_neighboringAffineSmoothKernelDs_left
    (α := α) (H := H) (L := L) hs ht
  have hKc := hasDerivAt_neighboringAffineSmoothKernelDs_left
    (α := α) (H := H) (L := L) hs hc
  have hDst := hasDerivAt_neighboringAffineSmoothKernelDst_right
    (α := α) (H := H) (L := L) hc hs
  unfold neighboringSmoothRightTaylorErrorDs neighboringSmoothRightTaylorErrorDss
  convert (hK.sub hKc).sub
    ((hasDerivAt_const s (t - c)).mul hDst) using 1 <;> ring

theorem neighboringSmoothMixedRemainder_decomposition
    (α H L a c s t : ℝ) :
    neighboringAffineSmoothKernel α H L s t =
      neighboringSmoothMixedRemainder α H L a c s t +
        (neighboringAffineSmoothKernelDs α H L c s * t +
          (neighboringAffineSmoothKernel α H L s c -
            c * neighboringAffineSmoothKernelDs α H L c s)) +
        (neighboringSmoothRightTaylorErrorDs α H L c a t * s +
          (neighboringSmoothRightTaylorError α H L c a t -
            a * neighboringSmoothRightTaylorErrorDs α H L c a t)) := by
  unfold neighboringSmoothMixedRemainder neighboringSmoothRightTaylorError
  ring

theorem abs_neighboringSmoothMixedRemainder_le
    {α H L a b c d C s t : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hC : 0 ≤ C)
    (hrect : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      x ∈ Ioo (-1 : ℝ) 1 ∧ y ∈ Ioo (-1 : ℝ) 1)
    (hmixed : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      |neighboringAffineSmoothKernelDsstt α H L x y| ≤ C)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc c d) :
    |neighboringSmoothMixedRemainder α H L a c s t| ≤
      C * (b - a) ^ 2 * (d - c) ^ 2 := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hcI : c ∈ Icc c d := ⟨le_rfl, hcd⟩
  have hinner (x : ℝ) (hx : x ∈ Icc a b) :
      |neighboringSmoothRightTaylorErrorDss α H L c x t| ≤
        C * (d - c) ^ 2 := by
    have hchain := abs_sub_linear_le_of_hasDerivAt_chain
      (f := fun y ↦ neighboringAffineSmoothKernelDss α H L x y)
      (f₁ := fun y ↦ neighboringAffineSmoothKernelDsst α H L x y)
      (f₂ := fun y ↦ neighboringAffineSmoothKernelDsstt α H L x y)
      hcd ht hC
      (fun y hy ↦
        hasDerivAt_neighboringAffineSmoothKernelDss_right
          (hrect x hx y hy).1 (hrect x hx y hy).2)
      (fun y hy ↦
        hasDerivAt_neighboringAffineSmoothKernelDsst_right
          (hrect x hx y hy).1 (hrect x hx y hy).2)
      (fun y hy ↦ hmixed x hx y hy)
    rw [neighboringSmoothRightTaylorErrorDss,
      neighboringAffineSmoothKernelDstt_eq_Dsst_swap]
    exact hchain
  have hmain := abs_sub_linear_le_of_hasDerivAt_chain
    (f := fun x ↦ neighboringSmoothRightTaylorError α H L c x t)
    (f₁ := fun x ↦ neighboringSmoothRightTaylorErrorDs α H L c x t)
    (f₂ := fun x ↦ neighboringSmoothRightTaylorErrorDss α H L c x t)
    hab hs (mul_nonneg hC (sq_nonneg _))
    (fun x hx ↦
      hasDerivAt_neighboringSmoothRightTaylorError_left
        (hrect x hx c hcI).2 (hrect x hx t ht).1
          (hrect x hx t ht).2)
    (fun x hx ↦
      hasDerivAt_neighboringSmoothRightTaylorErrorDs_left
        (hrect x hx c hcI).2 (hrect x hx t ht).1
          (hrect x hx t ht).2)
    (fun x hx ↦ hinner x hx)
  unfold neighboringSmoothMixedRemainder
  calc
    |neighboringSmoothRightTaylorError α H L c s t -
        neighboringSmoothRightTaylorError α H L c a t -
          (s - a) * neighboringSmoothRightTaylorErrorDs α H L c a t| ≤
      (C * (d - c) ^ 2) * (b - a) ^ 2 := hmain
    _ = C * (b - a) ^ 2 * (d - c) ^ 2 := by ring

end BEMOC
