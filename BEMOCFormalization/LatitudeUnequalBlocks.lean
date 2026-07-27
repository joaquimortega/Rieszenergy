import BEMOCFormalization.LatitudeSmoothOppositeBlocks
import BEMOCFormalization.LatitudeCoefficientDerivatives

/-!
# Unequal-scale same-hemisphere latitude blocks

This module isolates the genuinely analytic part of the L6 far-block
estimate from its completely elementary BEMOC scale arithmetic.

The exact squared chord is written as `A - B cos θ`, and the potentially
singular square roots disappear after angular averaging because every even
power of `B` is a polynomial in the height variables.  The final theorem
below turns the mixed Peano remainder at the predicted large-radius scale
into the precise L6 block majorant.
-/

open scoped BigOperators
open MeasureTheory Set

namespace BEMOC

/-- Squaring the angular coefficient removes both square roots.  This is
the polynomial identity used term-by-term in the unequal-scale binomial
series. -/
theorem angularKernelB_sq_eq_four_mul
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    angularKernelB s t ^ 2 =
      4 * (1 - s ^ 2) * (1 - t ^ 2) := by
  have hrs : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hrt : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  unfold angularKernelB
  rw [show (2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 =
      4 * Real.sqrt (1 - s ^ 2) ^ 2 *
        Real.sqrt (1 - t ^ 2) ^ 2 by ring,
    Real.sq_sqrt hrs, Real.sq_sqrt hrt]

/-- Every northern noncentral BEMOC population is at most four times its
manuscript depth. -/
theorem finiteBandPopulation_le_four_scale_of_northern
    {N : ℕ} {j : Fin (bandTailCount N + 1)}
    (hj : IsNorthernLatitudeBand N j) :
    finiteBandPopulation N j ≤ 4 * latitudeBandScale N j := by
  rw [latitudeBandScale_eq_north hj,
    concrete_finiteBandPopulation_north j hj]
  exact (ordinaryPopulation_between_three_and_four_mul ((j : ℕ) + 1)
    (by omega)).2

/-- The same population bound on the reflected southern half. -/
theorem finiteBandPopulation_le_four_scale_of_southern
    {N : ℕ} {j : Fin (bandTailCount N + 1)}
    (hj : IsSouthernLatitudeBand N j) :
    finiteBandPopulation N j ≤ 4 * latitudeBandScale N j := by
  let jr := concreteReflectBandIndex N j
  have hjr : IsNorthernLatitudeBand N jr :=
    reflect_southern_is_northern hj
  rw [← latitudeBandScale_reflect N j,
    concrete_finiteBandPopulation_reflect N j]
  exact finiteBandPopulation_le_four_scale_of_northern hjr

/-- Same-hemisphere pairs never use the exceptional central population, so
both population bounds are uniform. -/
theorem finiteBandPopulations_le_four_scales_of_same
    {N : ℕ} {j k : Fin (bandTailCount N + 1)}
    (hjk : SameLatitudeHemisphere N j k) :
    finiteBandPopulation N j ≤ 4 * latitudeBandScale N j ∧
      finiteBandPopulation N k ≤ 4 * latitudeBandScale N k := by
  rcases hjk with hNN | hSS
  · exact
      ⟨finiteBandPopulation_le_four_scale_of_northern hNN.1,
        finiteBandPopulation_le_four_scale_of_northern hNN.2⟩
  · exact
      ⟨finiteBandPopulation_le_four_scale_of_southern hSS.1,
        finiteBandPopulation_le_four_scale_of_southern hSS.2⟩

/-- The precise analytic datum still required from the normally convergent
even-power series.  Unlike a global block-bound assumption, this records
the local mixed Peano remainder at its natural large-radius scale. -/
def HasUnequalLatitudeAffineRemainders
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    LeftSmallSameLatitudePair N j k →
      ∃ R : ℝ → ℝ → ℝ, ∃ u v : ℝ → ℝ,
        (∀ s, IntervalIntegrable (R s) volume
          (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k)) ∧
        (∀ s t, latitudeKernel α s t =
          R s t + (u s * t + v s)) ∧
        ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
            (bandBoundaryHeight N j),
          ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
            (bandBoundaryHeight N k),
            |R s t| ≤
              C * (bandCount N : ℝ) ^ (8 - α) *
                (latitudeBandScale N k : ℝ) ^ (α - 8) *
                bandWidth N j ^ 2 * bandWidth N k ^ 2

/-- Concrete Peano output before simplifying the literal populations and
the relation `N ≍ M²`. -/
theorem unequal_block_bound_of_affineRemainders_raw
    {α C : ℝ} {N : ℕ} (hN : 0 < N) (hC : 0 ≤ C)
    (h : HasUnequalLatitudeAffineRemainders α N C) :
    ∀ j k, LeftSmallSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        64 * (C * (bandCount N : ℝ) ^ (8 - α) *
          (latitudeBandScale N k : ℝ) ^ (α - 8)) *
          (finiteBandPopulation N j : ℝ) ^ 3 *
          (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  intro j k hjk
  obtain ⟨R, u, v, hR, hdecomp, hbound⟩ := h j k hjk
  exact abs_bandPairError_le_of_mixed_remainder hN j k
    (latitudeKernel α) R u v
    (C * (bandCount N : ℝ) ^ (8 - α) *
      (latitudeBandScale N k : ℝ) ^ (α - 8))
    (by positivity) hR hdecomp hbound

/-- Scale arithmetic behind the far-block exponent.  It is stated over
positive real variables so it can also be reused for variants of the band
construction. -/
theorem unequal_scale_arithmetic
    {α C M N dj dk pj pk : ℝ}
    (hC : 0 ≤ C) (hM : 0 < M) (hN : 0 < N)
    (hdj : 0 < dj) (hdk : 0 < dk)
    (hpj : 0 ≤ pj) (hpk : 0 ≤ pk)
    (hpj' : pj ≤ 4 * dj) (hpk' : pk ≤ 4 * dk)
    (hMN : 4 * M ^ 2 ≤ N) :
    64 * (C * M ^ (8 - α) * dk ^ (α - 8)) *
          pj ^ 3 * pk ^ 3 / N ^ 4 ≤
      1024 * C * dj ^ 3 * M ^ (-α) * dk ^ (α - 5) := by
  have hcoef : 0 ≤ C * M ^ (8 - α) * dk ^ (α - 8) := by positivity
  have hpj3 : pj ^ 3 ≤ (4 * dj) ^ 3 := by gcongr
  have hpk3 : pk ^ 3 ≤ (4 * dk) ^ 3 := by gcongr
  have hnum :
      64 * (C * M ^ (8 - α) * dk ^ (α - 8)) *
          pj ^ 3 * pk ^ 3 ≤
        64 * (C * M ^ (8 - α) * dk ^ (α - 8)) *
          (4 * dj) ^ 3 * (4 * dk) ^ 3 := by
    gcongr
  have hden : (4 * M ^ 2) ^ 4 ≤ N ^ 4 := by gcongr
  have hMcombine :
      M ^ (8 - α) * (M ^ 8)⁻¹ = M ^ (-α) := by
    rw [← Real.rpow_natCast M 8, ← Real.rpow_neg hM.le]
    rw [← Real.rpow_add hM]
    congr 1
    ring
  have hdkcombine :
      dk ^ (α - 8) * dk ^ 3 = dk ^ (α - 5) := by
    rw [← Real.rpow_natCast dk 3, ← Real.rpow_add hdk]
    congr 1
    ring
  calc
    64 * (C * M ^ (8 - α) * dk ^ (α - 8)) *
          pj ^ 3 * pk ^ 3 / N ^ 4 ≤
        (64 * (C * M ^ (8 - α) * dk ^ (α - 8)) *
          (4 * dj) ^ 3 * (4 * dk) ^ 3) / N ^ 4 := by
      exact div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (64 * (C * M ^ (8 - α) * dk ^ (α - 8)) *
          (4 * dj) ^ 3 * (4 * dk) ^ 3) /
          (4 * M ^ 2) ^ 4 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 1024 * C * dj ^ 3 * M ^ (-α) * dk ^ (α - 5) := by
      rw [div_eq_mul_inv]
      rw [show (4 * M ^ 2) ^ 4 = 256 * M ^ 8 by ring]
      calc
        64 * (C * M ^ (8 - α) * dk ^ (α - 8)) *
              (4 * dj) ^ 3 * (4 * dk) ^ 3 *
              (256 * M ^ 8)⁻¹ =
            1024 * C * dj ^ 3 *
              (M ^ (8 - α) * (M ^ 8)⁻¹) *
              (dk ^ (α - 8) * dk ^ 3) := by
                rw [mul_inv]
                norm_num
                ring
        _ = _ := by rw [hMcombine, hdkcombine]

/-- The desired L6 far-block estimate for every classified same-hemisphere
pair, with a universal numerical loss of `1024` in passing from literal
BEMOC populations to manuscript scales. -/
theorem unequal_sameHemisphere_block_bound_of_affineRemainders
    {α C : ℝ} {N : ℕ} (hM : 1 ≤ bandCount N) (hC : 0 ≤ C)
    (h : HasUnequalLatitudeAffineRemainders α N C) :
    ∀ j k, LeftSmallSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        (1024 * C) * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
          (bandCount N : ℝ) ^ (-α) *
          (latitudeBandScale N k : ℝ) ^ (α - 5) := by
  have hMNnat := four_mul_bandCount_sq_le N
  have hN : 0 < N := by
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hMpos : 0 < (bandCount N : ℝ) := by exact_mod_cast hM
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hMN : 4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast hMNnat
  intro j k hjk
  have hraw :=
    unequal_block_bound_of_affineRemainders_raw hN hC h j k hjk
  have hpops :=
    finiteBandPopulations_le_four_scales_of_same hjk.2.2.1
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤
        4 * (latitudeBandScale N j : ℝ) := by
    exact_mod_cast hpops.1
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤
        4 * (latitudeBandScale N k : ℝ) := by
    exact_mod_cast hpops.2
  have hscale := unequal_scale_arithmetic
    (α := α) (C := C) (M := (bandCount N : ℝ)) (N := (N : ℝ))
    (dj := (latitudeBandScale N j : ℝ))
    (dk := (latitudeBandScale N k : ℝ))
    (pj := (finiteBandPopulation N j : ℝ))
    (pk := (finiteBandPopulation N k : ℝ))
    hC hMpos hNpos
    (by exact_mod_cast latitudeBandScale_pos N j)
    (by exact_mod_cast latitudeBandScale_pos N k)
    (by positivity) (by positivity) hpj hpk hMN
  exact hraw.trans (by
    convert hscale using 1)

end BEMOC
