import BEMOCFormalization.LatitudeDiagonalBandBridge
import BEMOCFormalization.LatitudeResonantExtraction

/-!
# Scale-normalized resonant latitude bridge

The resonant branch is most useful on a neighboring rectangle after the
physical height difference has been divided by a fixed positive square
radius.  This module records that normalization directly at the literal
band-pair level.  The apparent logarithm of the radius multiplies
`(s - t)²`, hence is annihilated exactly by the two-moment rule.
-/

open MeasureTheory Set

namespace BEMOC

set_option maxHeartbeats 800000

/-- Constant factors pass through both nested band-error rules. -/
theorem bandPairError_const_mul
    (N : ℕ) (j k : Fin (bandTailCount N + 1))
    (c : ℝ) (K : ℝ → ℝ → ℝ) :
    bandPairError N j k (fun s t ↦ c * K s t) =
      c * bandPairError N j k K := by
  unfold bandPairError
  simp_rw [bandError_const_mul]

/-- On every fixed interval the resonant branch is bounded by a constant
times the first power of its argument.  This deliberately coarse estimate
is useful after a dimensionless coefficient has been frozen: its
oscillation contributes the second small factor. -/
theorem exists_resonantLatitudeBranch_linear_bound
    (D : ℝ) (hD : 0 ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : ℝ, |x| ≤ D →
        |resonantLatitudeBranch x| ≤ B * |x| := by
  have hzero : (0 : ℝ) ∈ Icc (-D) D := by
    constructor <;> linarith
  obtain ⟨z, hz, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn
      ⟨0, hzero⟩ Real.continuous_mul_log.abs.continuousOn
  refine ⟨|z * Real.log z|, abs_nonneg _, ?_⟩
  intro x hx
  have hg : |x * Real.log x| ≤ |z * Real.log z| :=
    hmax (abs_le.mp hx)
  rw [show resonantLatitudeBranch x =
      x * (x * Real.log x) by
    unfold resonantLatitudeBranch
    ring]
  rw [abs_mul]
  nlinarith [abs_nonneg x]

/-- A single fixed bound for the unit resonant profile. -/
noncomputable def resonantUnitBranchConstant : ℝ :=
  Classical.choose
    (exists_resonantLatitudeBranch_bound 1 (by norm_num))

theorem resonantUnitBranchConstant_nonneg :
    0 ≤ resonantUnitBranchConstant :=
  (Classical.choose_spec
    (exists_resonantLatitudeBranch_bound 1 (by norm_num))).1

theorem abs_resonantLatitudeBranch_le_unitConstant
    {x : ℝ} (hx : |x| ≤ 1) :
    |resonantLatitudeBranch x| ≤ resonantUnitBranchConstant :=
  (Classical.choose_spec
    (exists_resonantLatitudeBranch_bound 1 (by norm_num))).2 x hx

/-- Exact dimensionless quadratic-gap identity at an arbitrary positive
radius scale. -/
theorem normalizedLatitudeGap_eq_scaledQuadraticCoefficient_mul_sq
    {R s t : ℝ} (hR : 0 < R)
    (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    normalizedLatitudeGap s t =
      (R ^ 4 * latitudeQuadraticGapCoefficient s t) *
        ((s - t) / R ^ 2) ^ 2 := by
  rw [normalizedLatitudeGap_eq_quadraticCoefficient_mul_sq hs ht]
  field_simp [hR.ne']
  ring

/-- In dimensionless coordinates the resonant reduced gap has no logarithm
of the physical radius.  The only logarithm is that of the bounded
dimensionless quadratic coefficient. -/
theorem normalizedGap_mul_log_eq_scaled_resonant_extraction
    {R s t : ℝ} (hR : 0 < R)
    (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    normalizedLatitudeGap s t *
        Real.log (normalizedLatitudeGap s t) =
      (R ^ 4 * latitudeQuadraticGapCoefficient s t) *
          Real.log (R ^ 4 * latitudeQuadraticGapCoefficient s t) *
            ((s - t) / R ^ 2) ^ 2 +
        2 * (R ^ 4 * latitudeQuadraticGapCoefficient s t) *
          resonantLatitudeBranch ((s - t) / R ^ 2) := by
  let c := R ^ 4 * latitudeQuadraticGapCoefficient s t
  let w := (s - t) / R ^ 2
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (by positivity)
      (latitudeQuadraticGapCoefficient_pos hs ht)
  have hq : normalizedLatitudeGap s t = c * w ^ 2 := by
    simpa [c, w] using
      normalizedLatitudeGap_eq_scaledQuadraticCoefficient_mul_sq hR hs ht
  calc
    normalizedLatitudeGap s t *
        Real.log (normalizedLatitudeGap s t) =
      quadraticReducedResonantBranch c w := by
        unfold quadraticReducedResonantBranch
        rw [hq]
    _ = c * Real.log c * w ^ 2 +
        2 * c * resonantLatitudeBranch w :=
      quadraticReducedResonantBranch_eq hc
    _ = _ := by rfl

/-- The physical neighboring resonant error with the globally fixed unit
constant.  This is the uniform, non-existential form needed when one common
constant is chosen before quantifying over `N`. -/
theorem abs_bandPairError_resonantLatitudeBranch_le_unitConstant
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k
        (fun s t ↦ resonantLatitudeBranch (s - t))| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (neighboringBandLength N j k ^ 2 *
            resonantUnitBranchConstant) := by
  let a := neighboringBandLength N j k
  let T : ℝ → ℝ → ℝ :=
    fun s t ↦ a ^ 2 * resonantLatitudeBranch ((s - t) / a)
  have ha : 0 < a := neighboringBandLength_pos hN hM j k
  have hT : ∀ s, IntervalIntegrable (T s) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k) := by
    intro s
    exact
      (continuous_const.mul
        (continuous_resonantLatitudeBranch.comp
          ((continuous_const.sub continuous_id).div_const a))).intervalIntegrable _ _
  have hJoint : Continuous
      (fun p : ℝ × ℝ ↦ T p.1 p.2) := by
    exact continuous_const.mul
      (continuous_resonantLatitudeBranch.comp
        ((continuous_fst.sub continuous_snd).div_const a))
  have hOuter : IntervalIntegrable
      (fun s ↦ bandError N k (T s)) volume
      (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) := by
    exact (continuous_bandError_right k hJoint).intervalIntegrable _ _
  have heq :
      bandPairError N j k
          (fun s t ↦ resonantLatitudeBranch (s - t)) =
        bandPairError N j k T := by
    apply bandPairError_eq_of_biaffine_remainder hN j k _ T
      (fun s ↦ -2 * Real.log a * s)
      (fun s ↦ Real.log a * s ^ 2)
      (fun _ ↦ 0)
      (fun t ↦ Real.log a * t ^ 2)
      hT hOuter
      (continuous_const.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _)
    intro s t
    have hscale := resonantLatitudeBranch_mul
      (a := a) (x := (s - t) / a) ha
    rw [show a * ((s - t) / a) = s - t by
      field_simp [ha.ne']] at hscale
    have hquad :
        a ^ 2 * ((s - t) / a) ^ 2 = (s - t) ^ 2 := by
      field_simp [ha.ne']
    have hcorr :
        a ^ 2 * Real.log a * ((s - t) / a) ^ 2 =
          Real.log a * (s - t) ^ 2 := by
      calc
        a ^ 2 * Real.log a * ((s - t) / a) ^ 2 =
            Real.log a *
              (a ^ 2 * ((s - t) / a) ^ 2) := by ring
        _ = _ := by rw [hquad]
    rw [hcorr] at hscale
    dsimp [T]
    rw [hscale]
    ring
  rw [heq]
  apply abs_bandPairError_le_of_band_rectangle_bound hN j k T
    (a ^ 2 * resonantUnitBranchConstant)
    (mul_nonneg (sq_nonneg a) resonantUnitBranchConstant_nonneg)
  intro s hs t ht
  have hunit := abs_normalized_neighboring_sub_le_one
    hN hM j k hneigh hs ht
  dsimp [T]
  rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
  exact mul_le_mul_of_nonneg_left
    (abs_resonantLatitudeBranch_le_unitConstant hunit) (sq_nonneg a)

/-- Dividing the physical difference by a positive square radius extracts
exactly the fourth inverse power of that radius from the paired resonant
error.  The logarithmic scaling correction is quadratic and therefore
vanishes. -/
theorem bandPairError_resonantLatitudeBranch_div_radiusSq
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    {R : ℝ} (hR : 0 < R) :
    bandPairError N j k
        (fun s t ↦ resonantLatitudeBranch ((s - t) / R ^ 2)) =
      (R ^ 2)⁻¹ ^ 2 *
        bandPairError N j k
          (fun s t ↦ resonantLatitudeBranch (s - t)) := by
  let b : ℝ := R ^ 2
  let c : ℝ := -(b⁻¹ ^ 2 * Real.log b)
  let T : ℝ → ℝ → ℝ :=
    fun s t ↦ b⁻¹ ^ 2 * resonantLatitudeBranch (s - t)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hT : ∀ s, IntervalIntegrable (T s) volume
      (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k) := by
    intro s
    exact
      (continuous_const.mul
        (continuous_resonantLatitudeBranch.comp
          (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have hjoint : Continuous
      (fun p : ℝ × ℝ ↦ T p.1 p.2) := by
    exact continuous_const.mul
      (continuous_resonantLatitudeBranch.comp
        (continuous_fst.sub continuous_snd))
  have hOuter : IntervalIntegrable
      (fun s ↦ bandError N k (T s)) volume
      (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) := by
    exact (continuous_bandError_right k hjoint).intervalIntegrable _ _
  have heq :
      bandPairError N j k
          (fun s t ↦ resonantLatitudeBranch ((s - t) / R ^ 2)) =
        bandPairError N j k T := by
    apply bandPairError_eq_of_biaffine_remainder hN j k
      (fun s t ↦ resonantLatitudeBranch ((s - t) / R ^ 2)) T
      (fun s ↦ -2 * c * s) (fun s ↦ c * s ^ 2)
      (fun _ ↦ 0) (fun t ↦ c * t ^ 2)
      hT hOuter
      (continuous_const.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _)
    intro s t
    have hscale := resonantLatitudeBranch_mul
      (a := b) (x := (s - t) / b) hb
    rw [show b * ((s - t) / b) = s - t by field_simp [hb.ne']] at hscale
    have hquad : b ^ 2 * ((s - t) / b) ^ 2 = (s - t) ^ 2 := by
      field_simp [hb.ne']
    have hbinv : b⁻¹ ^ 2 * b ^ 2 = 1 := by
      field_simp [hb.ne']
    have hscale' :
        resonantLatitudeBranch (s - t) =
          b ^ 2 * resonantLatitudeBranch ((s - t) / b) +
            Real.log b * (s - t) ^ 2 := by
      calc
        resonantLatitudeBranch (s - t) =
            b ^ 2 * resonantLatitudeBranch ((s - t) / b) +
              b ^ 2 * Real.log b * ((s - t) / b) ^ 2 := hscale
        _ = b ^ 2 * resonantLatitudeBranch ((s - t) / b) +
              Real.log b *
                (b ^ 2 * ((s - t) / b) ^ 2) := by ring
        _ = _ := by rw [hquad]
    have hsolve :
        b ^ 2 * resonantLatitudeBranch ((s - t) / b) =
          resonantLatitudeBranch (s - t) -
            Real.log b * (s - t) ^ 2 := by
      linarith [hscale']
    calc
      resonantLatitudeBranch ((s - t) / R ^ 2) =
          b⁻¹ ^ 2 *
            (b ^ 2 * resonantLatitudeBranch ((s - t) / b)) := by
        dsimp [b]
        rw [← mul_assoc, hbinv]
        ring
      _ = b⁻¹ ^ 2 *
          (resonantLatitudeBranch (s - t) -
            Real.log b * (s - t) ^ 2) := by rw [hsolve]
      _ = T s t +
          ((-2 * c * s) * t + c * s ^ 2) +
            (0 * s + c * t ^ 2) := by
        dsimp [T, c]
        ring
  rw [heq]
  dsimp [T, b]
  rw [bandPairError_const_mul]

/-- Premise-free normalized resonant bound on a neighboring rectangle.
The right side is the square of the dimensionless rectangle length
`a / R²`; in particular it contains no logarithm of `R`. -/
theorem exists_abs_bandPairError_scaled_resonantLatitudeBranch_le
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ B : ℝ, 0 ≤ B ∧
      |bandPairError N j k
          (fun s t ↦
            resonantLatitudeBranch ((s - t) / R ^ 2))| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (((neighboringBandLength N j k / R ^ 2) ^ 2) * B) := by
  obtain ⟨B, hB, hraw⟩ :=
    exists_abs_bandPairError_resonantLatitudeBranch_sub_le_concrete
      hN hM j k hneigh
  refine ⟨B, hB, ?_⟩
  rw [bandPairError_resonantLatitudeBranch_div_radiusSq
    hN j k hR, abs_mul,
    abs_of_nonneg (sq_nonneg (R ^ 2)⁻¹)]
  calc
    (R ^ 2)⁻¹ ^ 2 *
        |bandPairError N j k
          (fun s t ↦ resonantLatitudeBranch (s - t))| ≤
      (R ^ 2)⁻¹ ^ 2 *
        (4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (neighboringBandLength N j k ^ 2 * B)) := by
      gcongr
    _ = 4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (((neighboringBandLength N j k / R ^ 2) ^ 2) * B) := by
      field_simp [hR.ne']

/-- Uniform normalized resonant bound using the fixed unit-profile
constant. -/
theorem abs_bandPairError_scaled_resonantLatitudeBranch_le_unitConstant
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {R : ℝ} (hR : 0 < R) :
    |bandPairError N j k
        (fun s t ↦
          resonantLatitudeBranch ((s - t) / R ^ 2))| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (((neighboringBandLength N j k / R ^ 2) ^ 2) *
            resonantUnitBranchConstant) := by
  rw [bandPairError_resonantLatitudeBranch_div_radiusSq
    hN j k hR, abs_mul,
    abs_of_nonneg (sq_nonneg (R ^ 2)⁻¹)]
  calc
    (R ^ 2)⁻¹ ^ 2 *
        |bandPairError N j k
          (fun s t ↦ resonantLatitudeBranch (s - t))| ≤
      (R ^ 2)⁻¹ ^ 2 *
        (4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (neighboringBandLength N j k ^ 2 *
              resonantUnitBranchConstant)) := by
      gcongr
      exact abs_bandPairError_resonantLatitudeBranch_le_unitConstant
        hN hM j k hneigh
    _ = 4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (((neighboringBandLength N j k / R ^ 2) ^ 2) *
              resonantUnitBranchConstant) := by
      field_simp [hR.ne']

end BEMOC
