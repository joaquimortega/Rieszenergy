import BEMOCFormalization.LatitudeCoefficientDerivatives
import BEMOCFormalization.LatitudePolarBlocks

/-!
# Comparable nonpolar latitude blocks

This module connects the exact variable-coefficient weak-cusp normal form to
the concrete two-moment band rules.  It records the first two derivatives in
one height variable of the *actual* latitude kernel off the diagonal, and
packages the final local affine remainder estimate in precisely the form
which implies the manuscript L5 block bound.

The latter theorem contains no summation or asymptotic loss: once the local
remainder is supplied, the two concrete band variations give the desired
`d_j M⁻ᵅ (1+|j-k|)^(α-3)` estimate exactly.
-/

open MeasureTheory Set

namespace BEMOC

/-- The true latitude kernel in the coefficient notation used by the local
derivative calculation. -/
noncomputable def variableReducedLatitudeKernel (α s t : ℝ) : ℝ :=
  latitudeAngularScale s t ^ (α / 2) *
    reducedLatitudeCusp α (normalizedLatitudeGap s t)

theorem latitudeKernel_eq_variableReducedLatitudeKernel
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    latitudeKernel α s t = variableReducedLatitudeKernel α s t := by
  rw [latitudeKernel_eq_scale_mul_reducedCusp hs ht]
  unfold variableReducedLatitudeKernel
  rw [normalizedLatitudeGap_eq hs ht]

/-- Off the diagonal, the normalized gap is strictly positive. -/
theorem normalizedLatitudeGap_pos
    {s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    0 < normalizedLatitudeGap s t := by
  rw [normalizedLatitudeGap_eq hs ht]
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos
      (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  apply div_pos
  · unfold latitudeRadialGapSq
    have hsq : 0 < (s - t) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hst)
    nlinarith [sq_nonneg (heightRadius s - heightRadius t)]
  · exact hp

noncomputable def variableReducedLatitudeKernelDs (α s t : ℝ) : ℝ :=
  (α / 2) * latitudeAngularScale s t ^ (α / 2 - 1) *
        latitudeAngularScaleDs s t *
        reducedLatitudeCusp α (normalizedLatitudeGap s t) +
    latitudeAngularScale s t ^ (α / 2) *
      reducedLatitudeCuspD1Value α (normalizedLatitudeGap s t) *
        normalizedLatitudeGapDs s t

noncomputable def variableReducedLatitudeKernelDss (α s t : ℝ) : ℝ :=
  ((α / 2) * (α / 2 - 1) *
        latitudeAngularScale s t ^ (α / 2 - 2) *
        latitudeAngularScaleDs s t ^ 2 +
      (α / 2) * latitudeAngularScale s t ^ (α / 2 - 1) *
        latitudeAngularScaleDss s t) *
      reducedLatitudeCusp α (normalizedLatitudeGap s t) +
    2 * ((α / 2) * latitudeAngularScale s t ^ (α / 2 - 1) *
        latitudeAngularScaleDs s t) *
      reducedLatitudeCuspD1Value α (normalizedLatitudeGap s t) *
        normalizedLatitudeGapDs s t +
    latitudeAngularScale s t ^ (α / 2) *
      (reducedLatitudeCuspD2Value α (normalizedLatitudeGap s t) *
          normalizedLatitudeGapDs s t ^ 2 +
        reducedLatitudeCuspD1Value α (normalizedLatitudeGap s t) *
          normalizedLatitudeGapDss s t)

/-- First height derivative of the exact variable-coefficient reduced cusp. -/
theorem hasDerivAt_variableReducedLatitudeKernel_left
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ variableReducedLatitudeKernel α y t)
      (variableReducedLatitudeKernelDs α s t) s := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos
      (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hq := normalizedLatitudeGap_pos hs ht hst
  have hpDeriv := hasDerivAt_latitudeAngularScale_left (s := s) (t := t) hs
  have hqDeriv :=
    hasDerivAt_normalizedLatitudeGap_left (s := s) (t := t) hs ht
  have hpPow :
      HasDerivAt (fun y ↦ latitudeAngularScale y t ^ (α / 2))
        ((α / 2) * latitudeAngularScale s t ^ (α / 2 - 1) *
          latitudeAngularScaleDs s t) s := by
    convert
      (Real.hasDerivAt_rpow_const (x := latitudeAngularScale s t)
        (p := α / 2) (Or.inl hp.ne')).comp s hpDeriv using 1
  have hCusp :=
    (hasDerivAt_reducedLatitudeCusp (α := α) hq).comp s hqDeriv
  unfold variableReducedLatitudeKernel variableReducedLatitudeKernelDs
  convert hpPow.mul hCusp using 1 ;
    simp only [Function.comp_apply] ; ring

/-- Second height derivative of the exact variable-coefficient reduced cusp.
This is the first half of the mixed `(2,2)` chain used on separated L5
rectangles. -/
theorem hasDerivAt_variableReducedLatitudeKernelDs_left
    {α s t : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hst : s ≠ t) :
    HasDerivAt (fun y ↦ variableReducedLatitudeKernelDs α y t)
      (variableReducedLatitudeKernelDss α s t) s := by
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos
      (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hq := normalizedLatitudeGap_pos hs ht hst
  have hpD := hasDerivAt_latitudeAngularScale_left (s := s) (t := t) hs
  have hpDD := hasDerivAt_latitudeAngularScaleDs_left
    (s := s) (t := t) hs
  have hqD := hasDerivAt_normalizedLatitudeGap_left
    (s := s) (t := t) hs ht
  have hqDD := hasDerivAt_normalizedLatitudeGapDs_left
    (s := s) (t := t) hs ht
  have hpPow (e : ℝ) :
      HasDerivAt (fun y ↦ latitudeAngularScale y t ^ e)
        (e * latitudeAngularScale s t ^ (e - 1) *
          latitudeAngularScaleDs s t) s := by
    convert
      (Real.hasDerivAt_rpow_const (x := latitudeAngularScale s t)
        (p := e) (Or.inl hp.ne')).comp s hpD using 1
  have hC0 :=
    (hasDerivAt_reducedLatitudeCusp (α := α) hq).comp s hqD
  have hC1 :=
    (hasDerivAt_reducedLatitudeCuspD1Value (α := α) hq).comp s hqD
  let A : ℝ → ℝ := fun y ↦
    (α / 2) * latitudeAngularScale y t ^ (α / 2 - 1) *
      latitudeAngularScaleDs y t
  have hA : HasDerivAt A
      ((α / 2) * (α / 2 - 1) *
          latitudeAngularScale s t ^ (α / 2 - 2) *
          latitudeAngularScaleDs s t ^ 2 +
        (α / 2) * latitudeAngularScale s t ^ (α / 2 - 1) *
          latitudeAngularScaleDss s t) s := by
    dsimp [A]
    convert
      (((hasDerivAt_const s (α / 2)).mul (hpPow (α / 2 - 1))).mul
        hpDD) using 1 ; ring_nf
  let P : ℝ → ℝ := fun y ↦ latitudeAngularScale y t ^ (α / 2)
  have hP := hpPow (α / 2)
  unfold variableReducedLatitudeKernelDs variableReducedLatitudeKernelDss
  change HasDerivAt
    (fun y ↦ A y * reducedLatitudeCusp α (normalizedLatitudeGap y t) +
      P y * reducedLatitudeCuspD1Value α (normalizedLatitudeGap y t) *
        normalizedLatitudeGapDs y t) _ s
  convert (hA.mul hC0).add ((hP.mul hC1).mul hqDD) using 1 ;
    dsimp [A, P] ; ring

/-- The exact remainder amplitude which the concrete variation estimate
must see in order to yield the manuscript comparable-block weight. -/
noncomputable def comparableLatitudeRemainderAmplitude
    (α C : ℝ) (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : ℝ :=
  C * (latitudeBandScale N j : ℝ) *
      (bandCount N : ℝ) ^ (-α) *
      (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) /
    (4 * (finiteBandPopulation N j : ℝ) *
      (finiteBandPopulation N k : ℝ))

/-- Local analytic premise for the regular same-hemisphere comparable
rectangles.  It asks for precisely the affine-in-the-inner-variable
remainder produced by a tensor Peano argument. -/
def HasComparableSameLatitudeAffineRemainders
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    ComparableSameLatitudePair N j k →
      ∃ R : ℝ → ℝ → ℝ, ∃ u v : ℝ → ℝ,
        (∀ s, IntervalIntegrable (R s) volume
          (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k)) ∧
        (∀ s t, latitudeKernel α s t =
          R s t + (u s * t + v s)) ∧
        ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
            (bandBoundaryHeight N j),
          ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
            (bandBoundaryHeight N k),
            |R s t| ≤ comparableLatitudeRemainderAmplitude α C N j k

/-- A checked local affine remainder gives the exact L5 manuscript weight
for every nonpolar comparable same-hemisphere pair. -/
theorem comparableSame_block_bound_of_affineRemainders
    {α C : ℝ} {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    (hC : 0 ≤ C)
    (h : HasComparableSameLatitudeAffineRemainders α N C) :
    ∀ j k, ComparableSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        C * (latitudeBandScale N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) *
          (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
  intro j k hjk
  obtain ⟨R, u, v, hR, hdecomp, hbound⟩ := h j k hjk
  have hMpos : 0 < (bandCount N : ℝ) := by exact_mod_cast (by omega : 0 < bandCount N)
  have hjpopNat : 0 < finiteBandPopulation N j := by
    have := three_mul_latitudeBandScale_le_population hM j
    have hd := latitudeBandScale_pos N j
    omega
  have hkpopNat : 0 < finiteBandPopulation N k := by
    have := three_mul_latitudeBandScale_le_population hM k
    have hd := latitudeBandScale_pos N k
    omega
  have hjpop : 0 < (finiteBandPopulation N j : ℝ) := by exact_mod_cast hjpopNat
  have hkpop : 0 < (finiteBandPopulation N k : ℝ) := by exact_mod_cast hkpopNat
  have hamp : 0 ≤ comparableLatitudeRemainderAmplitude α C N j k := by
    unfold comparableLatitudeRemainderAmplitude
    positivity
  have hvariation :=
    abs_bandPairError_le_of_band_rectangle_bound hN j k R
      (comparableLatitudeRemainderAmplitude α C N j k) hamp hbound
  rw [bandPairError_eq_of_affine_inner_remainder hN j k
    (latitudeKernel α) R u v hR hdecomp]
  calc
    |bandPairError N j k R| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            comparableLatitudeRemainderAmplitude α C N j k := hvariation
    _ = _ := by
      unfold comparableLatitudeRemainderAmplitude
      field_simp [hjpop.ne', hkpop.ne']

end BEMOC
