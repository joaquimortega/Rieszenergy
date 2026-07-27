import BEMOCFormalization.LatitudeSmoothOppositeBlocks

/-!
# Comparable polar latitude blocks

The first two bands at either pole have fixed rescaled height coordinates.
For a comparable same-hemisphere pair meeting this polar exception, both
band scales are at most four.  This file turns that elementary observation
into the concrete `M⁻ᵅ` block bound used for the polar part of L5.
-/

open MeasureTheory Set

namespace BEMOC

/-- If two physical heights are within `A` and `B` of the north pole, then
their squared chord is at most `4(A+B)`, uniformly in the angular variable. -/
theorem angularPairKernel_base_le_of_north_gaps
    {s t θ A B : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA : 1 - s ≤ A) (hB : 1 - t ≤ B) :
    2 - 2 * s * t -
        2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * Real.cos θ
      ≤ 4 * (A + B) := by
  have hsgap : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  have htgap : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hrs : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hrt : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hsqr : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 :=
    Real.sq_sqrt hrs
  have htqr : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 :=
    Real.sq_sqrt hrt
  have hrprod :
      Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
        (1 - s) + (1 - t) := by
    have hsq :
        2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
          Real.sqrt (1 - s ^ 2) ^ 2 +
            Real.sqrt (1 - t ^ 2) ^ 2 := by
      nlinarith [sq_nonneg
        (Real.sqrt (1 - s ^ 2) - Real.sqrt (1 - t ^ 2))]
    rw [hsqr, htqr] at hsq
    have hsrad : 1 - s ^ 2 ≤ 2 * (1 - s) := by
      have hsplus : 0 ≤ 1 + s := by linarith [hs.1]
      nlinarith [mul_nonneg hsgap hsplus]
    have htrad : 1 - t ^ 2 ≤ 2 * (1 - t) := by
      have htplus : 0 ≤ 1 + t := by linarith [ht.1]
      nlinarith [mul_nonneg htgap htplus]
    nlinarith
  have hprod : 1 - s * t ≤ (1 - s) + (1 - t) := by
    nlinarith [mul_nonneg hsgap htgap]
  have hcos := Real.neg_one_le_cos θ
  have hrad0 :
      0 ≤ Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hbase :
      2 - 2 * s * t -
          2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) *
            Real.cos θ
        ≤ 4 * ((1 - s) + (1 - t)) := by
    nlinarith
  nlinarith [hbase, hA, hB]

/-- Pointwise chord-power version of the preceding north-polar estimate. -/
theorem angularPairKernel_le_of_north_gaps
    {α s t θ A B : ℝ} (hα : 0 ≤ α)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : 1 - s ≤ A) (hB : 1 - t ≤ B) :
    angularPairKernel α s t θ ≤ (4 * (A + B)) ^ (α / 2) := by
  unfold angularPairKernel
  apply Real.rpow_le_rpow
  · have hd := parallelPoint_dist_sq hs ht (θ := θ) (φ := 0)
    simp only [sub_zero] at hd
    rw [← hd]
    positivity
  · exact angularPairKernel_base_le_of_north_gaps hs ht hA hB
  · positivity

/-- Averaging the pointwise polar estimate preserves the same bound. -/
theorem abs_latitudeKernel_le_of_north_gaps
    {α s t A B : ℝ} (hα : 0 ≤ α)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : 1 - s ≤ A) (hB : 1 - t ≤ B) :
    |latitudeKernel α s t| ≤ (4 * (A + B)) ^ (α / 2) := by
  have hnonneg := latitudeKernel_nonneg (α := α) hs ht
  rw [abs_of_nonneg hnonneg]
  let C : ℝ := (4 * (A + B)) ^ (α / 2)
  have hC : 0 ≤ C := Real.rpow_nonneg (by positivity) _
  have hcont : Continuous (fun θ : ℝ ↦ angularPairKernel α s t θ) := by
    by_cases hα0 : α = 0
    · subst α
      simpa [angularPairKernel] using
        (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ)))
    · exact (continuous_angularPairKernel
        (lt_of_le_of_ne hα (Ne.symm hα0))).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
    (f := fun θ ↦ angularPairKernel α s t θ) (g := fun _ : ℝ ↦ C)
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    (fun θ _ ↦ angularPairKernel_le_of_north_gaps hα hs ht hA0 hB0 hA hB)
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  unfold latitudeKernel
  dsimp [C] at hmono ⊢
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  calc
    (1 / (2 * Real.pi)) *
        ∫ θ in (0 : ℝ)..2 * Real.pi, angularPairKernel α s t θ
      ≤ (1 / (2 * Real.pi)) *
          ((4 * (A + B)) ^ (α / 2) * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left
          (hmono.trans_eq (by ring)) (by positivity)
    _ = (4 * (A + B)) ^ (α / 2) := by field_simp

/-- Simultaneous reflection of both heights leaves the angular kernel
unchanged. -/
theorem angularPairKernel_neg_neg (α s t θ : ℝ) :
    angularPairKernel α (-s) (-t) θ = angularPairKernel α s t θ := by
  unfold angularPairKernel
  congr 1
  ring_nf

/-- The averaged kernel has the same north--south reflection symmetry. -/
theorem latitudeKernel_neg_neg (α s t : ℝ) :
    latitudeKernel α (-s) (-t) = latitudeKernel α s t := by
  unfold latitudeKernel
  congr 2
  funext θ
  exact angularPairKernel_neg_neg α s t θ

/-- South-polar version of `abs_latitudeKernel_le_of_north_gaps`. -/
theorem abs_latitudeKernel_le_of_south_gaps
    {α s t A B : ℝ} (hα : 0 ≤ α)
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : 1 + s ≤ A) (hB : 1 + t ≤ B) :
    |latitudeKernel α s t| ≤ (4 * (A + B)) ^ (α / 2) := by
  have hns : -s ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  have hnt : -t ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have h := abs_latitudeKernel_le_of_north_gaps hα hns hnt hA0 hB0
    (by simpa using hA) (by simpa using hB)
  rwa [latitudeKernel_neg_neg] at h

/-- Every height in a northern band of scale at most four is within
`18 / M²` of the north pole. -/
theorem northern_polar_rectangle_height_gap
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    (j : Fin (bandTailCount N + 1))
    (hjNorth : IsNorthernLatitudeBand N j)
    (hjScale : latitudeBandScale N j ≤ 4)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    0 ≤ 1 - s ∧
      1 - s ≤ 18 / (bandCount N : ℝ) ^ 2 := by
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 := by
    have hlo := bandBoundaryHeight_mem hN (j + 1)
    have hhi := bandBoundaryHeight_mem hN j
    exact ⟨hlo.1.trans hs.1, hs.2.trans hhi.2⟩
  have hjIndex : (j : ℕ) + 1 ≤ 4 := by
    rw [latitudeBandScale_eq_north hjNorth] at hjScale
    exact hjScale
  have hjBoundary : (j : ℕ) + 1 ≤ bandCount N - 1 := by
    unfold IsNorthernLatitudeBand at hjNorth
    omega
  have hformula := concrete_bandBoundaryHeight_north
    (N := N) (j := (j : ℕ) + 1) hjBoundary
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hNMnat := four_mul_bandCount_sq_le N
  have hNM : 4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast hNMnat
  constructor
  · linarith [hsSphere.2]
  · have hgap :
        1 - s ≤
          2 * (((j : ℕ) + 1 : ℕ) : ℝ) *
            (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) / N := by
      rw [hformula] at hs
      linarith [hs.1]
    have hjIndexR :
        (((j : ℕ) + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hjIndex
    have hgap72 : 1 - s ≤ 72 / (N : ℝ) := by
      calc
        1 - s ≤
            2 * (((j : ℕ) + 1 : ℕ) : ℝ) *
              (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) / N := hgap
        _ ≤ 72 / (N : ℝ) := by
          apply div_le_div_of_nonneg_right _ hNreal.le
          nlinarith [show (0 : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ) by positivity]
    calc
      1 - s ≤ 72 / (N : ℝ) := hgap72
      _ ≤ 18 / (bandCount N : ℝ) ^ 2 := by
        apply (div_le_div_iff₀ hNreal (sq_pos_of_pos hMreal)).2
        nlinarith

/-- Every height in a southern band of scale at most four is within
`18 / M²` of the south pole. -/
theorem southern_polar_rectangle_height_gap
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    (j : Fin (bandTailCount N + 1))
    (hjSouth : IsSouthernLatitudeBand N j)
    (hjScale : latitudeBandScale N j ≤ 4)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    0 ≤ 1 + s ∧
      1 + s ≤ 18 / (bandCount N : ℝ) ^ 2 := by
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 := by
    have hlo := bandBoundaryHeight_mem hN (j + 1)
    have hhi := bandBoundaryHeight_mem hN j
    exact ⟨hlo.1.trans hs.1, hs.2.trans hhi.2⟩
  let d : ℕ := bandTailCount N + 1 - (j : ℕ)
  have hdScale : latitudeBandScale N j = d :=
    latitudeBandScale_eq_south hjSouth
  have hd4 : d ≤ 4 := by
    rw [hdScale] at hjScale
    exact hjScale
  have hdM : d ≤ bandCount N - 1 := by
    dsimp [d]
    unfold IsSouthernLatitudeBand at hjSouth
    simp [bandTailCount] at *
    omega
  have hdLength : d ≤ (symmetricBandPopulations N).length := by
    rw [length_symmetricBandPopulations_eq_tail_succ]
    simp [bandTailCount]
    omega
  have hjReflect :
      (symmetricBandPopulations N).length - d = (j : ℕ) := by
    rw [length_symmetricBandPopulations_eq_tail_succ]
    dsimp [d]
    omega
  have hreflect := concrete_bandBoundaryHeight_reflect hN hdLength
  rw [hjReflect] at hreflect
  have hformula := concrete_bandBoundaryHeight_north
    (N := N) (j := d) hdM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hNMnat := four_mul_bandCount_sq_le N
  have hNM : 4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast hNMnat
  constructor
  · linarith [hsSphere.1]
  · have hgap :
        1 + s ≤ 2 * (d : ℝ) * (2 * (d : ℝ) + 1) / N := by
      rw [hformula] at hreflect
      linarith [hs.2]
    have hd4R : (d : ℝ) ≤ 4 := by exact_mod_cast hd4
    have hgap72 : 1 + s ≤ 72 / (N : ℝ) := by
      calc
        1 + s ≤ 2 * (d : ℝ) * (2 * (d : ℝ) + 1) / N := hgap
        _ ≤ 72 / (N : ℝ) := by
          apply div_le_div_of_nonneg_right _ hNreal.le
          nlinarith [show (0 : ℝ) ≤ (d : ℝ) by positivity]
    calc
      1 + s ≤ 72 / (N : ℝ) := hgap72
      _ ≤ 18 / (bandCount N : ℝ) ^ 2 := by
        apply (div_le_div_iff₀ hNreal (sq_pos_of_pos hMreal)).2
        nlinarith

/-- A comparable pair meeting the polar exception has both scales at most
four. -/
theorem polar_comparable_scales_le_four
    {N : ℕ} {j k : Fin (bandTailCount N + 1)}
    (hp : PolarLatitudePair N j k)
    (hc : ComparableLatitudeScales N j k) :
    latitudeBandScale N j ≤ 4 ∧ latitudeBandScale N k ≤ 4 := by
  unfold PolarLatitudePair IsPolarLatitudeBand at hp
  unfold ComparableLatitudeScales at hc
  omega

/-- Concrete north-polar L5 bound.  The constant `144` is deliberately
loose; crucially it is independent of `N`, `j`, and `k`. -/
theorem abs_latitudeKernel_bandPairError_le_north_polar_comparable
    {α : ℝ} (hα : 0 ≤ α) {N : ℕ} (hN : 0 < N)
    (hM : 1 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hp : PolarLatitudePair N j k)
    (hc : ComparableLatitudeScales N j k)
    (hNorth : IsNorthernLatitudeBand N j ∧
      IsNorthernLatitudeBand N k) :
    |bandPairError N j k (latitudeKernel α)| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (144 / (bandCount N : ℝ) ^ 2) ^ (α / 2) := by
  obtain ⟨hj4, hk4⟩ := polar_comparable_scales_le_four hp hc
  apply abs_bandPairError_le_of_band_rectangle_bound hN j k
    (latitudeKernel α)
    ((144 / (bandCount N : ℝ) ^ 2) ^ (α / 2))
    (Real.rpow_nonneg (by positivity) _)
  intro s hs t ht
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 := by
    have hlo := bandBoundaryHeight_mem hN (j + 1)
    have hhi := bandBoundaryHeight_mem hN j
    exact ⟨hlo.1.trans hs.1, hs.2.trans hhi.2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 := by
    have hlo := bandBoundaryHeight_mem hN (k + 1)
    have hhi := bandBoundaryHeight_mem hN k
    exact ⟨hlo.1.trans ht.1, ht.2.trans hhi.2⟩
  obtain ⟨hsgap0, hsgap⟩ :=
    northern_polar_rectangle_height_gap hN hM j hNorth.1 hj4 hs
  obtain ⟨htgap0, htgap⟩ :=
    northern_polar_rectangle_height_gap hN hM k hNorth.2 hk4 ht
  have hlocal := abs_latitudeKernel_le_of_north_gaps
    (A := 18 / (bandCount N : ℝ) ^ 2)
    (B := 18 / (bandCount N : ℝ) ^ 2)
    hα hsSphere htSphere (by positivity) (by positivity) hsgap htgap
  convert hlocal using 1
  congr 2
  ring

/-- Concrete south-polar L5 bound, obtained on the literal southern band
rectangles. -/
theorem abs_latitudeKernel_bandPairError_le_south_polar_comparable
    {α : ℝ} (hα : 0 ≤ α) {N : ℕ} (hN : 0 < N)
    (hM : 1 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hp : PolarLatitudePair N j k)
    (hc : ComparableLatitudeScales N j k)
    (hSouth : IsSouthernLatitudeBand N j ∧
      IsSouthernLatitudeBand N k) :
    |bandPairError N j k (latitudeKernel α)| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (144 / (bandCount N : ℝ) ^ 2) ^ (α / 2) := by
  obtain ⟨hj4, hk4⟩ := polar_comparable_scales_le_four hp hc
  apply abs_bandPairError_le_of_band_rectangle_bound hN j k
    (latitudeKernel α)
    ((144 / (bandCount N : ℝ) ^ 2) ^ (α / 2))
    (Real.rpow_nonneg (by positivity) _)
  intro s hs t ht
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 := by
    have hlo := bandBoundaryHeight_mem hN (j + 1)
    have hhi := bandBoundaryHeight_mem hN j
    exact ⟨hlo.1.trans hs.1, hs.2.trans hhi.2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 := by
    have hlo := bandBoundaryHeight_mem hN (k + 1)
    have hhi := bandBoundaryHeight_mem hN k
    exact ⟨hlo.1.trans ht.1, ht.2.trans hhi.2⟩
  obtain ⟨hsgap0, hsgap⟩ :=
    southern_polar_rectangle_height_gap hN hM j hSouth.1 hj4 hs
  obtain ⟨htgap0, htgap⟩ :=
    southern_polar_rectangle_height_gap hN hM k hSouth.2 hk4 ht
  have hlocal := abs_latitudeKernel_le_of_south_gaps
    (A := 18 / (bandCount N : ℝ) ^ 2)
    (B := 18 / (bandCount N : ℝ) ^ 2)
    hα hsSphere htSphere (by positivity) (by positivity) hsgap htgap
  convert hlocal using 1
  congr 2
  ring

/-- The full same-hemisphere comparable-polar estimate.  This is the
unconditional analytic input for the polar rectangles in the manuscript's
comparable-block argument. -/
theorem abs_latitudeKernel_bandPairError_le_polar_comparable_same
    {α : ℝ} (hα : 0 ≤ α) {N : ℕ} (hN : 0 < N)
    (hM : 1 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hp : PolarLatitudePair N j k)
    (hc : ComparableLatitudeScales N j k)
    (hSame : SameLatitudeHemisphere N j k) :
    |bandPairError N j k (latitudeKernel α)| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (144 / (bandCount N : ℝ) ^ 2) ^ (α / 2) := by
  rcases hSame with hNorth | hSouth
  · exact abs_latitudeKernel_bandPairError_le_north_polar_comparable
      hα hN hM j k hp hc hNorth
  · exact abs_latitudeKernel_bandPairError_le_south_polar_comparable
      hα hN hM j k hp hc hSouth

end BEMOC
