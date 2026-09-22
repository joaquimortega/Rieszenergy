import BEMOCFormalization.LatitudeEstimate
import BEMOCFormalization.LatitudeWeakSingularity

/-!
# Concrete reductions for latitude blocks

Band rules only sample and integrate heights in `[-1,1]`.  This module makes
that support fact usable by the generic variation estimates in
`LatitudeBands`: kernels may be clipped outside the physical height interval
without changing any band or band-pair error.
-/

open MeasureTheory Set

namespace BEMOC

/-- Restriction of a height function to the physical sphere interval. -/
noncomputable def restrictSphereHeight (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ∈ Icc (-1 : ℝ) 1 then f t else 0

theorem bandBoundaryHeight_succ_le {N : ℕ}
    (j : Fin (bandTailCount N + 1)) :
    bandBoundaryHeight N (j + 1) ≤ bandBoundaryHeight N j := by
  rw [← sub_nonneg, bandBoundaryHeight_sub_succ]
  positivity

theorem bandAtomicValue_restrictSphereHeight {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) :
    bandAtomicValue N j (restrictSphereHeight f) =
      bandAtomicValue N j f := by
  unfold bandAtomicValue restrictSphereHeight
  rw [if_pos (bandMidpointHeight_mem hN j),
    if_pos (bandBoundaryHeight_mem hN j),
    if_pos (bandBoundaryHeight_mem hN (j + 1))]

theorem bandContinuousValue_restrictSphereHeight {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) :
    bandContinuousValue N j (restrictSphereHeight f) =
      bandContinuousValue N j f := by
  unfold bandContinuousValue
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have horder := bandBoundaryHeight_succ_le j
  rw [uIcc_of_le horder] at ht
  have hlo := bandBoundaryHeight_mem hN (j + 1)
  have hhi := bandBoundaryHeight_mem hN j
  unfold restrictSphereHeight
  rw [if_pos ⟨hlo.1.trans ht.1, ht.2.trans hhi.2⟩]

theorem bandError_restrictSphereHeight {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) :
    bandError N j (restrictSphereHeight f) = bandError N j f := by
  unfold bandError
  rw [bandAtomicValue_restrictSphereHeight hN,
    bandContinuousValue_restrictSphereHeight hN]

/-- Two functions agreeing on physical heights have identical band errors. -/
theorem bandError_congr_on_sphereHeight {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) {f g : ℝ → ℝ}
    (hfg : ∀ t ∈ Icc (-1 : ℝ) 1, f t = g t) :
    bandError N j f = bandError N j g := by
  rw [← bandError_restrictSphereHeight hN j f,
    ← bandError_restrictSphereHeight hN j g]
  congr 2
  funext t
  unfold restrictSphereHeight
  split_ifs with ht
  · exact hfg t ht
  · rfl

/-- A kernel clipped to the physical height square. -/
noncomputable def restrictSphereHeightKernel (K : ℝ → ℝ → ℝ) (s t : ℝ) : ℝ :=
  if s ∈ Icc (-1 : ℝ) 1 ∧ t ∈ Icc (-1 : ℝ) 1 then K s t else 0

theorem bandPairError_restrictSphereHeightKernel {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1)) (K : ℝ → ℝ → ℝ) :
    bandPairError N j k (restrictSphereHeightKernel K) =
      bandPairError N j k K := by
  unfold bandPairError
  apply bandError_congr_on_sphereHeight hN
  intro s hs
  apply bandError_congr_on_sphereHeight hN
  intro t ht
  simp [restrictSphereHeightKernel, hs, ht]

/-- Localized form of the bounded-kernel block estimate.  Unlike the generic
version, its hypothesis is required only on actual sphere heights. -/
theorem abs_bandPairError_le_of_sphereHeight_bound
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1)) (K : ℝ → ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hbound : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      |K s t| ≤ C) :
    |bandPairError N j k K| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) * C := by
  rw [← bandPairError_restrictSphereHeightKernel hN j k K]
  apply abs_bandPairError_le_of_uniform_bound hN j k _ C hC
  intro s t
  unfold restrictSphereHeightKernel
  split_ifs with hst
  · exact hbound s hst.1 t hst.2
  · simp [hC]

/-- Scaled version used directly on polar fixed rectangles. -/
theorem abs_bandPairError_le_of_scaled_sphereHeight_bound
    {α C : ℝ} {N : ℕ} (hN : 0 < N) (hM : 0 < bandCount N)
    (hC : 0 ≤ C)
    (j k : Fin (bandTailCount N + 1)) (K : ℝ → ℝ → ℝ)
    (hbound : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      |K s t| ≤ C * (bandCount N : ℝ) ^ (-α)) :
    |bandPairError N j k K| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) * C *
          (bandCount N : ℝ) ^ (-α) := by
  have hMreal : 0 ≤ (bandCount N : ℝ) := by positivity
  have hscale : 0 ≤ C * (bandCount N : ℝ) ^ (-α) :=
    mul_nonneg hC (Real.rpow_nonneg hMreal _)
  have h := abs_bandPairError_le_of_sphereHeight_bound hN j k K
    (C * (bandCount N : ℝ) ^ (-α)) hscale hbound
  calc
    |bandPairError N j k K| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (C * (bandCount N : ℝ) ^ (-α)) := h
    _ = _ := by ring

/-- Unconditional coarse bound for every concrete latitude block.  This is
sharp enough for finitely many rescaled/polar blocks once their kernel has
been factored by the appropriate `M⁻ᵅ` scale. -/
theorem abs_latitudeKernel_bandPairError_le_global
    {α : ℝ} (hα : 0 ≤ α) {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1)) :
    |bandPairError N j k (latitudeKernel α)| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) * (2 : ℝ) ^ α := by
  apply abs_bandPairError_le_of_sphereHeight_bound hN j k _ _ (by positivity)
  intro s hs t ht
  exact abs_latitudeKernel_le_global hα hs ht

/-- The row interface is inhabited unconditionally for each fixed `N`.
The displayed constant grows like `N M^α`, so this is deliberately not the
uniform analytic estimate needed by the endpoint.  It proves that the only
missing content of L5--L6 is the gain furnished by two-moment cancellation,
not finiteness or support control. -/
theorem hasLatitudeBlockRowBound_coarse
    {α : ℝ} (hα : 0 ≤ α) {N : ℕ} (hN : 0 < N)
    (hM : 0 < bandCount N) :
    HasLatitudeBlockRowBound α N
      (4 * (2 : ℝ) ^ α * (N : ℝ) * (bandCount N : ℝ) ^ α) := by
  intro j
  let M : ℝ := bandCount N
  have hMreal : 0 < M := by
    dsimp [M]
    exact_mod_cast hM
  calc
    (∑ k : Fin (bandTailCount N + 1),
        |bandPairError N j k (latitudeKernel α)|) ≤
        ∑ k : Fin (bandTailCount N + 1),
          4 * (finiteBandPopulation N j : ℝ) *
            (finiteBandPopulation N k : ℝ) * (2 : ℝ) ^ α :=
      Finset.sum_le_sum fun k hk ↦
        abs_latitudeKernel_bandPairError_le_global hα hN j k
    _ = 4 * (finiteBandPopulation N j : ℝ) * (N : ℝ) *
          (2 : ℝ) ^ α := by
      calc
        (∑ k : Fin (bandTailCount N + 1),
            4 * (finiteBandPopulation N j : ℝ) *
              (finiteBandPopulation N k : ℝ) * (2 : ℝ) ^ α) =
            (∑ k : Fin (bandTailCount N + 1),
              (finiteBandPopulation N k : ℝ)) *
                (4 * (finiteBandPopulation N j : ℝ) * (2 : ℝ) ^ α) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = _ := by rw [sum_finiteBandPopulation_cast]; ring
    _ = (4 * (2 : ℝ) ^ α * (N : ℝ) * M ^ α) *
          (finiteBandPopulation N j : ℝ) * M ^ (-α) := by
      have hp : M ^ α * M ^ (-α) = 1 := by
        rw [← Real.rpow_add hMreal]
        norm_num
      calc
        4 * (finiteBandPopulation N j : ℝ) * (N : ℝ) * (2 : ℝ) ^ α =
            (4 * (2 : ℝ) ^ α * (N : ℝ)) *
              (finiteBandPopulation N j : ℝ) := by ring
        _ = (4 * (2 : ℝ) ^ α * (N : ℝ)) *
              (finiteBandPopulation N j : ℝ) * (M ^ α * M ^ (-α)) := by
          rw [hp, mul_one]
        _ = _ := by ring
    _ = (4 * (2 : ℝ) ^ α * (N : ℝ) *
          (bandCount N : ℝ) ^ α) *
          (finiteBandPopulation N j : ℝ) *
            (bandCount N : ℝ) ^ (-α) := by rfl

theorem hasCompleteLatitudeBlockEstimate_coarse
    {α : ℝ} (hα : 0 ≤ α) {N : ℕ} (hN : 0 < N)
    (hM : 0 < bandCount N) :
    HasCompleteLatitudeBlockEstimate α N
      (4 * (2 : ℝ) ^ α * (N : ℝ) * (bandCount N : ℝ) ^ α) :=
  ⟨hasLatitudeBlockRowBound_coarse hα hN hM⟩

end BEMOC
