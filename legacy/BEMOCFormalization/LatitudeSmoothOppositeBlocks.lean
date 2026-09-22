import BEMOCFormalization.LatitudePairClassification
import BEMOCFormalization.LatitudeConcreteBlocks
import BEMOCFormalization.TwoMomentPeano

/-!
# Smooth opposite-hemisphere latitude blocks

This module instantiates the fixed-rectangle remainder mechanism on the
literal BEMOC band rules.  The analytic input is an affine-in-the-second-
variable decomposition whose remainder gains two powers of each band width.
The two exact moments then give the expected cubic population weights and
the `N⁻⁴` smooth-block scale.
-/

open scoped BigOperators
open MeasureTheory Set

namespace BEMOC

/-- Clip a function to the support interval of one concrete band. -/
noncomputable def restrictLatitudeBand (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j) then f t else 0

theorem bandAtomicValue_restrictLatitudeBand {N : ℕ}
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) :
    bandAtomicValue N j (restrictLatitudeBand N j f) =
      bandAtomicValue N j f := by
  have hab := bandBoundaryHeight_succ_le j
  have hmid : bandMidpointHeight N j ∈
      Icc (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) := by
    unfold bandMidpointHeight
    constructor <;> linarith
  unfold bandAtomicValue restrictLatitudeBand
  rw [if_pos hmid, if_pos ⟨hab, le_rfl⟩, if_pos ⟨le_rfl, hab⟩]

theorem bandContinuousValue_restrictLatitudeBand
    (N : ℕ) (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) :
    bandContinuousValue N j (restrictLatitudeBand N j f) =
      bandContinuousValue N j f := by
  unfold bandContinuousValue
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (bandBoundaryHeight_succ_le j)] at ht
  simp [restrictLatitudeBand, ht]

theorem bandError_restrictLatitudeBand {N : ℕ}
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) :
    bandError N j (restrictLatitudeBand N j f) = bandError N j f := by
  unfold bandError
  rw [bandAtomicValue_restrictLatitudeBand,
    bandContinuousValue_restrictLatitudeBand]

/-- Local total-variation estimate on the actual support of a band. -/
theorem abs_bandError_le_of_band_bound {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j), |f t| ≤ C) :
    |bandError N j f| ≤ 2 * (finiteBandPopulation N j : ℝ) * C := by
  rw [← bandError_restrictLatitudeBand j f]
  apply abs_bandError_le_of_uniform_bound hN j _ C hC
  intro t
  unfold restrictLatitudeBand
  split_ifs with ht
  · exact hbound t ht
  · simpa using hC

/-- Local rectangle version of the elementary two-band variation bound. -/
theorem abs_bandPairError_le_of_band_rectangle_bound
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1)) (K : ℝ → ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hbound : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k), |K s t| ≤ C) :
    |bandPairError N j k K| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) * C := by
  unfold bandPairError
  have hinner : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j),
      |bandError N k (fun t ↦ K s t)| ≤
        2 * (finiteBandPopulation N k : ℝ) * C := by
    intro s hs
    exact abs_bandError_le_of_band_bound hN k _ C hC (hbound s hs)
  have hD : 0 ≤ 2 * (finiteBandPopulation N k : ℝ) * C := by positivity
  calc
    |bandError N j (fun s ↦ bandError N k (fun t ↦ K s t))| ≤
        2 * (finiteBandPopulation N j : ℝ) *
          (2 * (finiteBandPopulation N k : ℝ) * C) :=
      abs_bandError_le_of_band_bound hN j _ _ hD hinner
    _ = 4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) * C := by ring

/-- Removing a remainder which differs from the kernel by a function affine
in the inner variable does not change the paired band error. -/
theorem bandPairError_eq_of_affine_inner_remainder
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (K R : ℝ → ℝ → ℝ) (u v : ℝ → ℝ)
    (hR : ∀ s, IntervalIntegrable (R s) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k))
    (hdecomp : ∀ s t, K s t = R s t + (u s * t + v s)) :
    bandPairError N j k K = bandPairError N j k R := by
  unfold bandPairError
  congr 1
  funext s
  rw [show (fun t ↦ K s t) =
      fun t ↦ R s t + (u s * t + v s) by
        funext t
        exact hdecomp s t]
  change bandError N k
      (fun t ↦ R s t + (fun z ↦ u s * z + v s) t) =
    bandError N k (R s)
  rw [bandError_add N k (R s) (fun t ↦ u s * t + v s) (hR s)
    ((continuous_const.mul continuous_id).add continuous_const
      |>.intervalIntegrable _ _)]
  rw [bandError_affine hN]
  ring

/-- Concrete bilinear-Taylor cancellation.  Terms affine in either height
variable disappear under the paired band rule.  The extra integrability
hypotheses are exactly those needed to use interval-integral linearity. -/
theorem bandPairError_eq_of_biaffine_remainder
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (K R : ℝ → ℝ → ℝ)
    (uRight vRight uLeft vLeft : ℝ → ℝ)
    (hR : ∀ s, IntervalIntegrable (R s) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k))
    (hOuterR : IntervalIntegrable
      (fun s ↦ bandError N k (R s)) volume
      (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j))
    (huLeft : IntervalIntegrable uLeft volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k))
    (hvLeft : IntervalIntegrable vLeft volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k))
    (hdecomp : ∀ s t, K s t =
      R s t + (uRight s * t + vRight s) +
        (uLeft t * s + vLeft t)) :
    bandPairError N j k K = bandPairError N j k R := by
  unfold bandPairError
  have hinner (s : ℝ) :
      bandError N k (fun t ↦ K s t) =
        bandError N k (R s) +
          ((bandError N k uLeft) * s + bandError N k vLeft) := by
    rw [show (fun t ↦ K s t) =
        fun t ↦ (R s t + (uRight s * t + vRight s)) +
          (uLeft t * s + vLeft t) by
      funext t
      exact hdecomp s t]
    have hright : IntervalIntegrable (fun t ↦ uRight s * t + vRight s)
        volume (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k) :=
      ((continuous_const.mul continuous_id).add continuous_const)
        |>.intervalIntegrable _ _
    have hleft : IntervalIntegrable (fun t ↦ uLeft t * s + vLeft t)
        volume (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k) := by
      rw [show (fun t ↦ uLeft t * s + vLeft t) =
          fun t ↦ s * uLeft t + vLeft t by
        funext t
        ring]
      exact (huLeft.const_mul s).add hvLeft
    rw [bandError_add N k _ _ ((hR s).add hright) hleft,
      bandError_add N k _ _ (hR s) hright,
      bandError_affine hN]
    rw [show (fun t ↦ uLeft t * s + vLeft t) =
        fun t ↦ s * uLeft t + vLeft t by
          funext t
          ring,
      bandError_add N k _ _ (huLeft.const_mul s) hvLeft,
      bandError_const_mul]
    ring
  rw [show (fun s ↦ bandError N k (fun t ↦ K s t)) =
      fun s ↦ bandError N k (R s) +
        ((bandError N k uLeft) * s + bandError N k vLeft) by
      funext s
      exact hinner s]
  have houterAffine : IntervalIntegrable
      (fun s ↦ (bandError N k uLeft) * s + bandError N k vLeft)
      volume (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j) :=
    ((continuous_const.mul continuous_id).add continuous_const)
      |>.intervalIntegrable _ _
  rw [bandError_add N j _ _ hOuterR houterAffine,
    bandError_affine hN]
  ring

/-- Concrete mixed-remainder estimate, with the two width gains exposed. -/
theorem abs_bandPairError_le_of_mixed_remainder
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (K R : ℝ → ℝ → ℝ) (u v : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hR : ∀ s, IntervalIntegrable (R s) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k))
    (hdecomp : ∀ s t, K s t = R s t + (u s * t + v s))
    (hbound : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
        |R s t| ≤ C * bandWidth N j ^ 2 * bandWidth N k ^ 2) :
    |bandPairError N j k K| ≤
      64 * C * (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  rw [bandPairError_eq_of_affine_inner_remainder hN j k K R u v hR hdecomp]
  have hw : 0 ≤ C * bandWidth N j ^ 2 * bandWidth N k ^ 2 := by positivity
  have hlocal := abs_bandPairError_le_of_band_rectangle_bound hN j k R
    (C * bandWidth N j ^ 2 * bandWidth N k ^ 2) hw hbound
  refine hlocal.trans_eq ?_
  rw [bandWidth_eq_population, bandWidth_eq_population]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- Concrete mixed-remainder estimate using the full bilinear Taylor
nullspace. -/
theorem abs_bandPairError_le_of_biaffine_mixed_remainder
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (K R : ℝ → ℝ → ℝ)
    (uRight vRight uLeft vLeft : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hR : ∀ s, IntervalIntegrable (R s) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k))
    (hOuterR : IntervalIntegrable
      (fun s ↦ bandError N k (R s)) volume
      (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j))
    (huLeft : IntervalIntegrable uLeft volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k))
    (hvLeft : IntervalIntegrable vLeft volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k))
    (hdecomp : ∀ s t, K s t =
      R s t + (uRight s * t + vRight s) +
        (uLeft t * s + vLeft t))
    (hbound : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
        |R s t| ≤ C * bandWidth N j ^ 2 * bandWidth N k ^ 2) :
    |bandPairError N j k K| ≤
      64 * C * (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  rw [bandPairError_eq_of_biaffine_remainder hN j k K R
    uRight vRight uLeft vLeft hR hOuterR huLeft hvLeft hdecomp]
  have hw : 0 ≤ C * bandWidth N j ^ 2 * bandWidth N k ^ 2 := by
    positivity
  have hlocal := abs_bandPairError_le_of_band_rectangle_bound hN j k R
    (C * bandWidth N j ^ 2 * bandWidth N k ^ 2) hw hbound
  refine hlocal.trans_eq ?_
  rw [bandWidth_eq_population, bandWidth_eq_population]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- Analytic input for all smooth opposite-hemisphere rectangles. -/
def HasSmoothOppositeAffineRemainders
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    SmoothOppositeLatitudePair N j k →
      ∃ R : ℝ → ℝ → ℝ, ∃ u v : ℝ → ℝ,
        (∀ s, IntervalIntegrable (R s) volume
          (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k)) ∧
        (∀ s t, latitudeKernel α s t =
          R s t + (u s * t + v s)) ∧
        ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
            (bandBoundaryHeight N j),
          ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
            (bandBoundaryHeight N k),
            |R s t| ≤ C * bandWidth N j ^ 2 * bandWidth N k ^ 2

/-- Correct bilinear-Taylor analytic input for smooth opposite-hemisphere
rectangles. -/
def HasSmoothOppositeBiaffineRemainders
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    SmoothOppositeLatitudePair N j k →
      ∃ R : ℝ → ℝ → ℝ,
      ∃ uRight vRight uLeft vLeft : ℝ → ℝ,
        (∀ s, IntervalIntegrable (R s) volume
          (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k)) ∧
        IntervalIntegrable (fun s ↦ bandError N k (R s)) volume
          (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) ∧
        IntervalIntegrable uLeft volume
          (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k) ∧
        IntervalIntegrable vLeft volume
          (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k) ∧
        (∀ s t, latitudeKernel α s t =
          R s t + (uRight s * t + vRight s) +
            (uLeft t * s + vLeft t)) ∧
        ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
            (bandBoundaryHeight N j),
          ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
            (bandBoundaryHeight N k),
            |R s t| ≤ C * bandWidth N j ^ 2 * bandWidth N k ^ 2

/-- The smooth-opposite field obtained from the explicit affine-remainder
hypothesis. -/
theorem smoothOpposite_block_bound_of_affineRemainders
    {α C : ℝ} {N : ℕ} (hN : 0 < N) (hC : 0 ≤ C)
    (h : HasSmoothOppositeAffineRemainders α N C) :
    ∀ j k, SmoothOppositeLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        64 * C * (finiteBandPopulation N j : ℝ) ^ 3 *
          (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  intro j k hjk
  obtain ⟨R, u, v, hR, hdecomp, hbound⟩ := h j k hjk
  exact abs_bandPairError_le_of_mixed_remainder hN j k
    (latitudeKernel α) R u v C hC hR hdecomp hbound

theorem smoothOpposite_block_bound_of_biaffineRemainders
    {α C : ℝ} {N : ℕ} (hN : 0 < N) (hC : 0 ≤ C)
    (h : HasSmoothOppositeBiaffineRemainders α N C) :
    ∀ j k, SmoothOppositeLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        64 * C * (finiteBandPopulation N j : ℝ) ^ 3 *
          (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  intro j k hjk
  obtain ⟨R, uRight, vRight, uLeft, vLeft,
    hR, hOuterR, huLeft, hvLeft, hdecomp, hbound⟩ := h j k hjk
  exact abs_bandPairError_le_of_biaffine_mixed_remainder hN j k
    (latitudeKernel α) R uRight vRight uLeft vLeft C hC
    hR hOuterR huLeft hvLeft hdecomp hbound

end BEMOC
