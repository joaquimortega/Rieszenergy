import BEMOCFormalization.LatitudeCentralComparableClosure
import BEMOCFormalization.LatitudeNeighboringPointwiseClosure

/-!
# Premise-free smooth neighboring comparable blocks

The analytic pieces in the two nonresonant local decompositions are
manifestly smooth affine kernels.  This file retains the radius grading in
their fourth mixed derivative, applies the diagonal-valid tensor Taylor
formula, and converts the resulting Peano estimate to the comparable block
majorant.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace BEMOC

set_option maxHeartbeats 1200000

noncomputable def neighboringAffineSmoothGradedConstant
    (α H L : ℝ) : ℝ :=
  |H - L| * latitudeComparablePowerJetConstant α +
    6416 * |L| * latitudeComparablePowerJetConstant (α - 2)

theorem neighboringAffineSmoothGradedConstant_nonneg
    (α H L : ℝ) :
    0 ≤ neighboringAffineSmoothGradedConstant α H L := by
  unfold neighboringAffineSmoothGradedConstant
    latitudeComparablePowerJetConstant
    latitudeComparablePowerRpowConstant
    latitudePowerCoefficientEnvelope
  positivity

private theorem comparableLatitudeRadiusFloor_le_one
    {N : ℕ} (hM : 1 ≤ bandCount N)
    (j : Fin (bandTailCount N + 1)) :
    comparableLatitudeRadiusFloor N j ≤ 1 := by
  unfold comparableLatitudeRadiusFloor
  have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast (by omega :
    0 < bandCount N)
  have hd :
      (latitudeBandScale N j : ℝ) ≤ bandCount N := by
    exact_mod_cast latitudeBandScale_le_bandCount hM j
  apply (div_le_iff₀ (by positivity : 0 < 10 * (bandCount N : ℝ))).2
  nlinarith

private theorem neighboringComparable_abs_one_sub_mul_le
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |1 - s * t| ≤
      3200 * comparableLatitudeRadiusFloor N j ^ 2 := by
  let R := comparableLatitudeRadiusFloor N j
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    positivity
  have hchart :=
    neighboringComparable_largeDepth_rectangle_chart
      hM hjk hdepth hs ht
  have hceil :=
    comparableSame_rectangle_common_radius_ceiling hM hjk.1 hs ht
  have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
  have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
  have hrprod :
      heightRadius s * heightRadius t ≤ 1600 * R ^ 2 := by
    calc
      heightRadius s * heightRadius t ≤
          (40 * R) * (40 * R) := by
        exact mul_le_mul
          (by simpa [R] using hceil.1) (by simpa [R] using hceil.2)
          hrt0 (by positivity : 0 ≤ 40 * R)
      _ = 1600 * R ^ 2 := by ring
  have hrs : 0 < heightRadius s := heightRadius_pos hchart.1
  have hrt : 0 < heightRadius t := heightRadius_pos hchart.2.1
  have hp : 0 < heightRadius s * heightRadius t := mul_pos hrs hrt
  have hone :
      1 - s * t =
        (normalizedLatitudeGap s t + 1) *
          (heightRadius s * heightRadius t) := by
    unfold normalizedLatitudeGap
    field_simp [hp.ne']
  have hst : s * t ≤ 1 := by
    have hsabs : |s| ≤ 1 := abs_le.mpr ⟨hchart.1.1.le, hchart.1.2.le⟩
    have htabs : |t| ≤ 1 := abs_le.mpr
      ⟨hchart.2.1.1.le, hchart.2.1.2.le⟩
    have habs : |s * t| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg s, abs_nonneg t]
    exact (le_abs_self (s * t)).trans habs
  rw [abs_of_nonneg (sub_nonneg.mpr hst), hone]
  have hq : normalizedLatitudeGap s t + 1 ≤ 2 := by
    linarith [hchart.2.2.2]
  have hq0 : 0 ≤ normalizedLatitudeGap s t + 1 := by
    linarith [hchart.2.2.1]
  calc
    (normalizedLatitudeGap s t + 1) *
        (heightRadius s * heightRadius t) ≤
      2 * (1600 * R ^ 2) := by gcongr
    _ = 3200 * comparableLatitudeRadiusFloor N j ^ 2 := by
      dsimp [R]
      ring

/-- Sharp radius grading for the diagonal-valid affine analytic kernel.
The first product below is the essential one: the factor `1-st` contributes
two radius powers before it is multiplied by
`latitudePowerDsstt (α-2)`. -/
theorem abs_neighboringAffineSmoothKernelDsstt_le_neighboring
    {α H L : ℝ} (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringAffineSmoothKernelDsstt α H L s t| ≤
      neighboringAffineSmoothGradedConstant α H L *
        comparableLatitudeRadiusFloor N j ^ (α - 8) := by
  let R := comparableLatitudeRadiusFloor N j
  let P := latitudeComparablePowerJetConstant α
  let Q := latitudeComparablePowerJetConstant (α - 2)
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    positivity
  have hR1 : R ≤ 1 := by
    simpa [R] using comparableLatitudeRadiusFloor_le_one hM j
  have hang :=
    comparableSame_rectangle_angularJetBound hM hjk.1 hs ht
  rcases latitudeComparablePowerJetGradedBound hα2 hR hang with
    ⟨hP0, _, _, _, _, _, _, _, _, hPsstt⟩
  rcases latitudeComparablePowerJetGradedBound
      (α := α - 2) (by linarith) hR hang with
    ⟨hQ0, _, _, _, _, hQst, _, hQsst, hQstt, hQsstt⟩
  unfold ScaledAbs at hPsstt hQst hQsst hQstt hQsstt
  change
    |latitudePowerDsstt α s t| ≤ P * R ^ (α - 8) at hPsstt
  have hQst' :
      |latitudePowerDst (α - 2) s t| ≤ Q * R ^ (α - 6) := by
    simpa only [Q, show α - 2 - 4 = α - 6 by ring] using hQst
  have hQsst' :
      |latitudePowerDsst (α - 2) s t| ≤ Q * R ^ (α - 8) := by
    simpa only [Q, show α - 2 - 6 = α - 8 by ring] using hQsst
  have hQstt' :
      |latitudePowerDstt (α - 2) s t| ≤ Q * R ^ (α - 8) := by
    simpa only [Q, show α - 2 - 6 = α - 8 by ring] using hQstt
  have hQsstt' :
      |latitudePowerDsstt (α - 2) s t| ≤ Q * R ^ (α - 10) := by
    simpa only [Q, show α - 2 - 8 = α - 10 by ring] using hQsstt
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 := by
    have hc := neighboringComparable_largeDepth_rectangle_chart
      hM hjk hdepth hs ht
    exact ⟨hc.1.1.le, hc.1.2.le⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 := by
    have hc := neighboringComparable_largeDepth_rectangle_chart
      hM hjk hdepth hs ht
    exact ⟨hc.2.1.1.le, hc.2.1.2.le⟩
  have hsabs : |s| ≤ 1 := abs_le.mpr hsSphere
  have htabs : |t| ≤ 1 := abs_le.mpr htSphere
  have hone := neighboringComparable_abs_one_sub_mul_le
    hM hjk hdepth hs ht
  have hstShift :
      |latitudePowerDst (α - 2) s t| ≤ Q * R ^ (α - 8) := by
    have hp :
        R ^ (α - 6) ≤ R ^ (α - 8) :=
      Real.rpow_le_rpow_of_exponent_ge hR hR1 (by linarith)
    exact hQst'.trans (mul_le_mul_of_nonneg_left hp hQ0)
  unfold neighboringAffineSmoothKernelDsstt
  have hinner :
      |(1 - s * t) * latitudePowerDsstt (α - 2) s t -
          2 * s * latitudePowerDsst (α - 2) s t -
          4 * latitudePowerDst (α - 2) s t -
          2 * t * latitudePowerDstt (α - 2) s t| ≤
        |1 - s * t| * |latitudePowerDsstt (α - 2) s t| +
          2 * |s| * |latitudePowerDsst (α - 2) s t| +
          4 * |latitudePowerDst (α - 2) s t| +
          2 * |t| * |latitudePowerDstt (α - 2) s t| := by
    calc
      |_ - _| ≤
          |(1 - s * t) * latitudePowerDsstt (α - 2) s t -
            2 * s * latitudePowerDsst (α - 2) s t -
            4 * latitudePowerDst (α - 2) s t| +
          |2 * t * latitudePowerDstt (α - 2) s t| := abs_sub _ _
      _ ≤
          (|(1 - s * t) * latitudePowerDsstt (α - 2) s t -
            2 * s * latitudePowerDsst (α - 2) s t| +
            |4 * latitudePowerDst (α - 2) s t|) +
          |2 * t * latitudePowerDstt (α - 2) s t| := by
            gcongr
            exact abs_sub _ _
      _ ≤
          ((|(1 - s * t) * latitudePowerDsstt (α - 2) s t| +
            |2 * s * latitudePowerDsst (α - 2) s t|) +
            |4 * latitudePowerDst (α - 2) s t|) +
          |2 * t * latitudePowerDstt (α - 2) s t| := by
            gcongr
            exact abs_sub _ _
      _ = _ := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    |_ + _| ≤
        |H - L| * |latitudePowerDsstt α s t| +
        2 * |L| *
          (|1 - s * t| *
              |latitudePowerDsstt (α - 2) s t| +
            2 * |s| * |latitudePowerDsst (α - 2) s t| +
            4 * |latitudePowerDst (α - 2) s t| +
          2 * |t| * |latitudePowerDstt (α - 2) s t|) := by
      calc
        |_ + _| ≤
            |(H - L) * latitudePowerDsstt α s t| +
              |2 * L *
                ((1 - s * t) * latitudePowerDsstt (α - 2) s t -
                  2 * s * latitudePowerDsst (α - 2) s t -
                  4 * latitudePowerDst (α - 2) s t -
                  2 * t * latitudePowerDstt (α - 2) s t)| :=
          abs_add _ _
        _ = |H - L| * |latitudePowerDsstt α s t| +
              2 * |L| *
                |(1 - s * t) * latitudePowerDsstt (α - 2) s t -
                  2 * s * latitudePowerDsst (α - 2) s t -
                  4 * latitudePowerDst (α - 2) s t -
                  2 * t * latitudePowerDstt (α - 2) s t| := by
            simp only [abs_mul, abs_of_nonneg
              (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ _ := add_le_add_left
          (mul_le_mul_of_nonneg_left hinner
            (mul_nonneg (by norm_num) (abs_nonneg L))) _
    _ ≤
        (|H - L| * P + 6416 * |L| * Q) * R ^ (α - 8) := by
      have hRpow : 0 ≤ R ^ (α - 8) := Real.rpow_nonneg hR.le _
      have hz1 :
          |1 - s * t| *
              |latitudePowerDsstt (α - 2) s t| ≤
            3200 * Q * R ^ (α - 8) := by
        calc
          _ ≤ (3200 * R ^ 2) * (Q * R ^ (α - 10)) := by
            gcongr
          _ = 3200 * Q * (R ^ 2 * R ^ (α - 10)) := by ring
          _ = 3200 * Q * R ^ (α - 8) := by
            rw [← Real.rpow_natCast R 2, ← Real.rpow_add hR]
            congr 2
            ring
      have hz2 :
          2 * |s| * |latitudePowerDsst (α - 2) s t| ≤
            2 * Q * R ^ (α - 8) := by
        calc
          _ ≤ 2 * 1 * (Q * R ^ (α - 8)) := by
            gcongr
          _ = _ := by ring
      have hz3 :
          4 * |latitudePowerDst (α - 2) s t| ≤
            4 * Q * R ^ (α - 8) := by nlinarith
      have hz4 :
          2 * |t| * |latitudePowerDstt (α - 2) s t| ≤
            2 * Q * R ^ (α - 8) := by
        calc
          _ ≤ 2 * 1 * (Q * R ^ (α - 8)) := by
            gcongr
          _ = _ := by ring
      have hsum :
            |1 - s * t| * |latitudePowerDsstt (α - 2) s t| +
                2 * |s| * |latitudePowerDsst (α - 2) s t| +
                4 * |latitudePowerDst (α - 2) s t| +
                2 * |t| * |latitudePowerDstt (α - 2) s t| ≤
              3208 * Q * R ^ (α - 8) := by linarith
      calc
        _ ≤ |H - L| * (P * R ^ (α - 8)) +
            2 * |L| * (3208 * Q * R ^ (α - 8)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hPsstt (abs_nonneg (H - L)))
            (mul_le_mul_of_nonneg_left hsum
              (mul_nonneg (by norm_num) (abs_nonneg L)))
        _ = _ := by ring
    _ = neighboringAffineSmoothGradedConstant α H L *
        comparableLatitudeRadiusFloor N j ^ (α - 8) := by
      simp [neighboringAffineSmoothGradedConstant, P, Q, R]

/-- Joint continuity of the diagonal-valid tensor remainder on a
large-depth neighboring rectangle. -/
theorem continuousOn_neighboringSmoothMixedRemainder_neighboringRectangle
    {α H L : ℝ}
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦
        neighboringSmoothMixedRemainder α H L
          (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N (k + 1)) p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
  let a := bandBoundaryHeight N (j + 1)
  let c := bandBoundaryHeight N (k + 1)
  have haI : a ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j) :=
    ⟨le_rfl, bandBoundaryHeight_succ_le j⟩
  have hcI : c ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k) :=
    ⟨le_rfl, bandBoundaryHeight_succ_le k⟩
  intro p hp
  have chart (x : ℝ)
      (hx : x ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j))
      (y : ℝ)
      (hy : y ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)) :
      x ∈ Ioo (-1 : ℝ) 1 ∧ y ∈ Ioo (-1 : ℝ) 1 := by
    have hc := neighboringComparable_largeDepth_rectangle_chart
      hM hjk hdepth hx hy
    exact ⟨hc.1, hc.2.1⟩
  have hpc := chart p.1 hp.1 p.2 hp.2
  have hsc := chart p.1 hp.1 c hcI
  have hat := chart a haI p.2 hp.2
  have hKst : ContinuousAt
      (fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernel α H L q.1 q.2) p :=
    continuousAt_neighboringAffineSmoothKernel_joint hpc.1 hpc.2
  have hKsc : ContinuousAt
      (fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernel α H L q.1 c) p :=
    ContinuousAt.comp'
      (f := fun q : ℝ × ℝ ↦ (q.1, c))
      (g := fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernel α H L q.1 q.2)
      (continuousAt_neighboringAffineSmoothKernel_joint hsc.1 hsc.2)
      (continuousAt_fst.prodMk continuousAt_const)
  have hKdscs : ContinuousAt
      (fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernelDs α H L c q.1) p :=
    ContinuousAt.comp'
      (f := fun q : ℝ × ℝ ↦ (c, q.1))
      (g := fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernelDs α H L q.1 q.2)
      (continuousAt_neighboringAffineSmoothKernelDs_joint hsc.2 hsc.1)
      (continuousAt_const.prodMk continuousAt_fst)
  have hKat : ContinuousAt
      (fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernel α H L a q.2) p :=
    ContinuousAt.comp'
      (f := fun q : ℝ × ℝ ↦ (a, q.2))
      (g := fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernel α H L q.1 q.2)
      (continuousAt_neighboringAffineSmoothKernel_joint hat.1 hat.2)
      (continuousAt_const.prodMk continuousAt_snd)
  have hKdsa : ContinuousAt
      (fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernelDs α H L a q.2) p :=
    ContinuousAt.comp'
      (f := fun q : ℝ × ℝ ↦ (a, q.2))
      (g := fun q : ℝ × ℝ ↦ neighboringAffineSmoothKernelDs α H L q.1 q.2)
      (continuousAt_neighboringAffineSmoothKernelDs_joint hat.1 hat.2)
      (continuousAt_const.prodMk continuousAt_snd)
  have htminus : ContinuousAt (fun q : ℝ × ℝ ↦ q.2 - c) p :=
    continuousAt_snd.sub continuousAt_const
  have hsminus : ContinuousAt (fun q : ℝ × ℝ ↦ q.1 - a) p :=
    continuousAt_fst.sub continuousAt_const
  have hE : ContinuousAt (fun q : ℝ × ℝ ↦
      neighboringAffineSmoothKernel α H L q.1 q.2 -
        neighboringAffineSmoothKernel α H L q.1 c -
          (q.2 - c) * neighboringAffineSmoothKernelDs α H L c q.1) p :=
    (hKst.sub hKsc).sub (htminus.mul hKdscs)
  have hEa : ContinuousAt (fun q : ℝ × ℝ ↦
      neighboringAffineSmoothKernel α H L a q.2 -
        neighboringAffineSmoothKernel α H L a c -
          (q.2 - c) * neighboringAffineSmoothKernelDs α H L c a) p :=
    (hKat.sub continuousAt_const).sub
      (htminus.mul continuousAt_const)
  have hEDs : ContinuousAt (fun q : ℝ × ℝ ↦
      neighboringAffineSmoothKernelDs α H L a q.2 -
        neighboringAffineSmoothKernelDs α H L a c -
          (q.2 - c) * neighboringAffineSmoothKernelDst α H L c a) p :=
    (hKdsa.sub continuousAt_const).sub
      (htminus.mul continuousAt_const)
  have hfinal : ContinuousAt (fun q : ℝ × ℝ ↦
      (neighboringAffineSmoothKernel α H L q.1 q.2 -
          neighboringAffineSmoothKernel α H L q.1 c -
            (q.2 - c) * neighboringAffineSmoothKernelDs α H L c q.1) -
        (neighboringAffineSmoothKernel α H L a q.2 -
          neighboringAffineSmoothKernel α H L a c -
            (q.2 - c) * neighboringAffineSmoothKernelDs α H L c a) -
        (q.1 - a) *
          (neighboringAffineSmoothKernelDs α H L a q.2 -
            neighboringAffineSmoothKernelDs α H L a c -
              (q.2 - c) * neighboringAffineSmoothKernelDst α H L c a)) p :=
    (hE.sub hEa).sub (hsminus.mul hEDs)
  simpa [a, c, neighboringSmoothMixedRemainder,
    neighboringSmoothRightTaylorError,
    neighboringSmoothRightTaylorErrorDs] using hfinal.continuousWithinAt

/-- Premise-free Peano estimate for the affine smooth part on a
large-depth neighboring rectangle. -/
theorem abs_bandPairError_neighboringAffineSmoothKernel_neighboring
    {α H L : ℝ} (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j) :
    |bandPairError N j k (neighboringAffineSmoothKernel α H L)| ≤
      64 * (neighboringAffineSmoothGradedConstant α H L *
        comparableLatitudeRadiusFloor N j ^ (α - 8)) *
        (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let Is : Set ℝ := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It : Set ℝ := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  let a := bandBoundaryHeight N (j + 1)
  let c := bandBoundaryHeight N (k + 1)
  let R : ℝ → ℝ → ℝ := fun s t ↦
    neighboringSmoothMixedRemainder α H L a c s t
  let C := neighboringAffineSmoothGradedConstant α H L *
    comparableLatitudeRadiusFloor N j ^ (α - 8)
  have hC : 0 ≤ C := mul_nonneg
    (neighboringAffineSmoothGradedConstant_nonneg α H L)
    (Real.rpow_nonneg (by
      unfold comparableLatitudeRadiusFloor
      positivity) _)
  have hcontR : ContinuousOn (fun p : ℝ × ℝ ↦ R p.1 p.2)
      (Is ×ˢ It) :=
    continuousOn_neighboringSmoothMixedRemainder_neighboringRectangle
      hM hjk hdepth
  let fR : C(Is ×ˢ It, ℝ) :=
    ⟨fun p ↦ R p.1.1 p.1.2,
      (continuousOn_iff_continuous_restrict.mp hcontR)⟩
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq
    (isClosed_Icc.prod isClosed_Icc) fR
  have hGeq : ∀ p ∈ Is ×ˢ It, G p = R p.1 p.2 := by
    intro p hp
    exact DFunLike.congr_fun hG (⟨p, hp⟩ : Is ×ˢ It)
  let uRight : ℝ → ℝ := fun s ↦
    neighboringAffineSmoothKernelDs α H L c s
  let vRight : ℝ → ℝ := fun s ↦
    neighboringAffineSmoothKernel α H L s c -
      c * neighboringAffineSmoothKernelDs α H L c s
  let uLeft : ℝ → ℝ := fun t ↦
    neighboringSmoothRightTaylorErrorDs α H L c a t
  let vLeft : ℝ → ℝ := fun t ↦
    neighboringSmoothRightTaylorError α H L c a t -
      a * neighboringSmoothRightTaylorErrorDs α H L c a t
  let Kext : ℝ → ℝ → ℝ := fun s t ↦
    G (s, t) + (uRight s * t + vRight s) +
      (uLeft t * s + vLeft t)
  have hpair :
      bandPairError N j k (neighboringAffineSmoothKernel α H L) =
        bandPairError N j k Kext := by
    apply bandPairError_congr_on_literalRectangle j k
    intro s hs t ht
    rw [neighboringSmoothMixedRemainder_decomposition]
    have hGR : G (s, t) = R s t := hGeq (s, t) ⟨hs, ht⟩
    dsimp [Kext, uRight, vRight, uLeft, vLeft, R, a, c]
    rw [hGR]
  rw [hpair]
  apply abs_bandPairError_le_of_biaffine_mixed_remainder hN j k
    Kext (fun s t ↦ G (s, t)) uRight vRight uLeft vLeft C hC
  · intro s
    exact (G.continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (continuous_bandError_right k G.continuous).intervalIntegrable _ _
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (bandBoundaryHeight_succ_le k)]
    intro t ht
    have haI : a ∈ Is := ⟨le_rfl, bandBoundaryHeight_succ_le j⟩
    have hcI : c ∈ It := ⟨le_rfl, bandBoundaryHeight_succ_le k⟩
    have hat := neighboringComparable_largeDepth_rectangle_chart
      hM hjk hdepth haI ht
    dsimp [uLeft]
    unfold neighboringSmoothRightTaylorErrorDs
    exact
      (((continuousAt_neighboringAffineSmoothKernelDs_joint
          hat.1 hat.2.1).comp'
          (continuousAt_const.prodMk continuousAt_id)).sub
        continuousAt_const).sub
        ((continuousAt_id.sub continuousAt_const).mul
          continuousAt_const) |>.continuousWithinAt
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (bandBoundaryHeight_succ_le k)]
    intro t ht
    have haI : a ∈ Is := ⟨le_rfl, bandBoundaryHeight_succ_le j⟩
    have hcI : c ∈ It := ⟨le_rfl, bandBoundaryHeight_succ_le k⟩
    have hat := neighboringComparable_largeDepth_rectangle_chart
      hM hjk hdepth haI ht
    dsimp [vLeft]
    unfold neighboringSmoothRightTaylorError
      neighboringSmoothRightTaylorErrorDs
    have hK : ContinuousAt
        (fun y ↦ neighboringAffineSmoothKernel α H L a y) t :=
      (continuousAt_neighboringAffineSmoothKernel_joint
        hat.1 hat.2.1).comp'
        (continuousAt_const.prodMk continuousAt_id)
    have hDs : ContinuousAt
        (fun y ↦ neighboringAffineSmoothKernelDs α H L a y) t :=
      (continuousAt_neighboringAffineSmoothKernelDs_joint
        hat.1 hat.2.1).comp'
        (continuousAt_const.prodMk continuousAt_id)
    exact
      (((hK.sub continuousAt_const).sub
          ((continuousAt_id.sub continuousAt_const).mul
            continuousAt_const)).sub
        (continuousAt_const.mul
          ((hDs.sub continuousAt_const).sub
            ((continuousAt_id.sub continuousAt_const).mul
              continuousAt_const)))) |>.continuousWithinAt
  · intro s t
    rfl
  · intro s hs t ht
    rw [hGeq (s, t) ⟨hs, ht⟩]
    apply abs_neighboringSmoothMixedRemainder_le
      (bandBoundaryHeight_succ_le j)
      (bandBoundaryHeight_succ_le k) hC
    · intro x hx y hy
      have hc := neighboringComparable_largeDepth_rectangle_chart
        hM hjk hdepth hx hy
      exact ⟨hc.1, hc.2.1⟩
    · intro x hx y hy
      exact abs_neighboringAffineSmoothKernelDsstt_le_neighboring
        hα2 hM hjk hdepth hx hy
    · exact hs
    · exact ht

private theorem neighboringSmooth_radiusScale_identity
    {α d M : ℝ} (hd : 0 < d) (hM : 0 < M) :
    (d / (10 * M)) ^ (α - 8) =
      (10 : ℝ) ^ (8 - α) * M ^ (8 - α) * d ^ (α - 8) := by
  rw [Real.div_rpow hd.le (by positivity : 0 ≤ 10 * M)]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) hM.le]
  rw [div_eq_mul_inv, mul_inv_rev]
  rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10),
    ← Real.rpow_neg hM.le]
  rw [show -(α - 8) = 8 - α by ring]
  ring

noncomputable def neighboringAffineSmoothBlockConstant
    (α H L : ℝ) : ℝ :=
  8192 * (10 : ℝ) ^ (8 - α) *
    neighboringAffineSmoothGradedConstant α H L

theorem neighboringAffineSmoothBlockConstant_nonneg
    (α H L : ℝ) :
    0 ≤ neighboringAffineSmoothBlockConstant α H L := by
  unfold neighboringAffineSmoothBlockConstant
  have hS := neighboringAffineSmoothGradedConstant_nonneg α H L
  positivity

/-- The neighboring affine Peano remainder is at the exact comparable
majorant scale. -/
theorem abs_bandPairError_neighboringAffineSmoothKernel_le_majorant
    {α H L : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j) :
    |bandPairError N j k (neighboringAffineSmoothKernel α H L)| ≤
      comparableLatitudeBlockMajorant α
        (neighboringAffineSmoothBlockConstant α H L) N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let S := neighboringAffineSmoothGradedConstant α H L
  let C := (10 : ℝ) ^ (8 - α) * S
  let M : ℝ := bandCount N
  let d : ℝ := latitudeBandScale N j
  let D : ℝ := 1 + Nat.dist (j : ℕ) (k : ℕ)
  let p : ℝ := finiteBandPopulation N j
  let q : ℝ := finiteBandPopulation N k
  have hS : 0 ≤ S := neighboringAffineSmoothGradedConstant_nonneg α H L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hMr : 0 < M := by dsimp [M]; positivity
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast latitudeBandScale_pos N j
  have hD : 0 < D := by dsimp [D]; positivity
  have hDd : D ≤ d := by
    have hn := hjk.2
    have hd600 : (600 : ℝ) ≤ d := by
      dsimp [d]
      exact_mod_cast hdepth
    have hD2 : D ≤ 2 := by
      dsimp [D]
      exact_mod_cast (show
        1 + Nat.dist (j : ℕ) (k : ℕ) ≤ 2 by omega)
    linarith
  have hpow :
      d ^ (α - 8) ≤ d ^ (-5 : ℝ) * D ^ (α - 3) := by
    have hneg : α - 3 ≤ 0 := by linarith
    have hmono :
        d ^ (α - 3) ≤ D ^ (α - 3) :=
      Real.rpow_le_rpow_of_nonpos hD hDd hneg
    calc
      d ^ (α - 8) = d ^ (-5 : ℝ) * d ^ (α - 3) := by
        rw [← Real.rpow_add hd]
        congr 1
        ring
      _ ≤ d ^ (-5 : ℝ) * D ^ (α - 3) := by gcongr
  have hRscale :
      S * comparableLatitudeRadiusFloor N j ^ (α - 8) ≤
        C * M ^ (8 - α) * d ^ (-5 : ℝ) * D ^ (α - 3) := by
    rw [show comparableLatitudeRadiusFloor N j =
      d / (10 * M) by rfl]
    rw [neighboringSmooth_radiusScale_identity hd hMr]
    calc
      S * (10 ^ (8 - α) * M ^ (8 - α) * d ^ (α - 8)) ≤
          S * (10 ^ (8 - α) * M ^ (8 - α) *
            (d ^ (-5 : ℝ) * D ^ (α - 3))) := by gcongr
      _ = C * M ^ (8 - α) *
          d ^ (-5 : ℝ) * D ^ (α - 3) := by
        dsimp [C]
        ring
  have hraw :=
    abs_bandPairError_neighboringAffineSmoothKernel_neighboring
      (H := H) (L := L) hα2
      (by omega : 1 ≤ bandCount N) hjk hdepth
  have hpops :=
    finiteBandPopulations_le_four_scales_of_same hjk.1.2.2.1
  have hp' : p ≤ 4 * d := by
    dsimp [p, d]
    exact_mod_cast hpops.1
  have hq0 :
      (finiteBandPopulation N k : ℝ) ≤
        4 * (latitudeBandScale N k : ℝ) := by
    exact_mod_cast hpops.2
  have hcomp :
      (latitudeBandScale N k : ℝ) ≤ 2 * d := by
    dsimp [d]
    exact_mod_cast hjk.1.2.2.2.2
  have hq' : q ≤ 8 * d := by dsimp [q]; linarith
  have hMN : 4 * M ^ 2 ≤ (N : ℝ) := by
    dsimp [M]
    exact_mod_cast four_mul_bandCount_sq_le N
  have hscale := separatedComparable_scale_arithmetic
    (α := α) (C := C) (M := M) (N := (N : ℝ))
    (d := d) (p := p) (q := q) (D := D)
    hC hMr (by exact_mod_cast hN) hd (by positivity) (by positivity)
    hD hp' hq' hMN
  calc
    |bandPairError N j k (neighboringAffineSmoothKernel α H L)| ≤
        64 * (S * comparableLatitudeRadiusFloor N j ^ (α - 8)) *
          p ^ 3 * q ^ 3 / (N : ℝ) ^ 4 := by
      simpa [S, p, q] using hraw
    _ ≤ 64 * (C * M ^ (8 - α) * d ^ (-5 : ℝ) *
          D ^ (α - 3)) * p ^ 3 * q ^ 3 / (N : ℝ) ^ 4 := by
      gcongr
    _ ≤ 8192 * C * d * M ^ (-α) * D ^ (α - 3) := hscale
    _ = comparableLatitudeBlockMajorant α
          (neighboringAffineSmoothBlockConstant α H L) N j k := by
      unfold comparableLatitudeBlockMajorant
        neighboringAffineSmoothBlockConstant
      dsimp [C, S, M, d, D]
      ring

noncomputable def neighboringUpperSmoothBlockConstant (α : ℝ) : ℝ :=
  neighboringAffineSmoothBlockConstant α
    (reducedCuspUpperConstantCoefficient α)
    (reducedCuspUpperLinearCoefficient α)

noncomputable def neighboringLowerSmoothBlockConstant (α : ℝ) : ℝ :=
  neighboringAffineSmoothBlockConstant α
    (reducedCuspLowerConstantCoefficient α) 0

theorem neighboringUpperSmoothBlockConstant_nonneg (α : ℝ) :
    0 ≤ neighboringUpperSmoothBlockConstant α :=
  neighboringAffineSmoothBlockConstant_nonneg _ _ _

theorem neighboringLowerSmoothBlockConstant_nonneg (α : ℝ) :
    0 ≤ neighboringLowerSmoothBlockConstant α :=
  neighboringAffineSmoothBlockConstant_nonneg _ _ _

/-- Unconditional large-depth smooth input in the upper nonresonant
range. -/
theorem hasLargeDepthNeighboringUpperSmoothBlockBound
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    HasLargeDepthNeighboringUpperSmoothBlockBound α N
      (neighboringUpperSmoothBlockConstant α) := by
  intro j k hjk hdepth
  let A := neighboringAffineSmoothKernel α
    (reducedCuspUpperConstantCoefficient α)
    (reducedCuspUpperLinearCoefficient α)
  let B := neighboringUpperBranchKernel α
  have hA : ContinuousOn (fun p : ℝ × ℝ ↦ A p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
    intro p hp
    have hc := neighboringComparable_largeDepth_rectangle_chart
      (by omega : 1 ≤ bandCount N) hjk hdepth hp.1 hp.2
    exact (continuousAt_neighboringAffineSmoothKernel_joint
      (α := α)
      (H := reducedCuspUpperConstantCoefficient α)
      (L := reducedCuspUpperLinearCoefficient α)
      hc.1 hc.2.1).continuousWithinAt
  have hdecomp :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          latitudeKernel α s t = A s t + B s t := by
    intro s hs t ht
    have hc := neighboringComparable_largeDepth_rectangle_chart
      (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
    rw [latitudeKernel_eq_neighboringUpperAnalytic_add_branch_on_unitChart
      hα1 hα2 hc.1 hc.2.1 hc.2.2.2]
    rw [neighboringUpperAnalyticKernel_eq_smooth hc.1 hc.2.1]
  have heq :=
    bandPairError_eq_add_of_continuous_decomposition_on_literalRectangle
      j k (latitudeKernel α) A B
      (continuous_latitudeKernel (by linarith)) hA hdecomp
  have ha :=
    abs_bandPairError_neighboringAffineSmoothKernel_le_majorant
      (H := reducedCuspUpperConstantCoefficient α)
      (L := reducedCuspUpperLinearCoefficient α)
      (by linarith : 0 < α) hα2 hM hjk hdepth
  change
    |bandPairError N j k (latitudeKernel α) -
        bandPairError N j k (neighboringUpperBranchKernel α)| ≤ _
  rw [heq]
  simpa [A, B, neighboringUpperSmoothBlockConstant] using ha

/-- Unconditional large-depth smooth input in the lower nonresonant
range. -/
theorem hasLargeDepthNeighboringLowerSmoothBlockBound
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    HasLargeDepthNeighboringLowerSmoothBlockBound α N
      (neighboringLowerSmoothBlockConstant α) := by
  intro j k hjk hdepth
  let A := neighboringAffineSmoothKernel α
    (reducedCuspLowerConstantCoefficient α) 0
  let B := neighboringLowerBranchKernel α
  have hA : ContinuousOn (fun p : ℝ × ℝ ↦ A p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
    intro p hp
    have hc := neighboringComparable_largeDepth_rectangle_chart
      (by omega : 1 ≤ bandCount N) hjk hdepth hp.1 hp.2
    exact (continuousAt_neighboringAffineSmoothKernel_joint
      (α := α) (H := reducedCuspLowerConstantCoefficient α)
      (L := 0) hc.1 hc.2.1).continuousWithinAt
  have hdecomp :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          latitudeKernel α s t = A s t + B s t := by
    intro s hs t ht
    have hc := neighboringComparable_largeDepth_rectangle_chart
      (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
    rw [latitudeKernel_eq_neighboringLowerAnalytic_add_branch_on_unitChart
      hα0 hα1 hc.1 hc.2.1 hc.2.2.2]
    rw [neighboringLowerAnalyticKernel_eq_power]
    unfold A neighboringAffineSmoothKernel
    ring
  have heq :=
    bandPairError_eq_add_of_continuous_decomposition_on_literalRectangle
      j k (latitudeKernel α) A B
      (continuous_latitudeKernel hα0) hA hdecomp
  have ha :=
    abs_bandPairError_neighboringAffineSmoothKernel_le_majorant
      (H := reducedCuspLowerConstantCoefficient α) (L := 0)
      hα0 (by linarith : α < 2) hM hjk hdepth
  change
    |bandPairError N j k (latitudeKernel α) -
        bandPairError N j k (neighboringLowerBranchKernel α)| ≤ _
  rw [heq]
  simpa [A, B, neighboringLowerSmoothBlockConstant] using ha

/-- Every upper-range neighboring comparable block, including the finite
depth branch. -/
theorem neighboringComparable_upper_block_bound
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    ∀ j k : Fin (bandTailCount N + 1),
      NeighboringComparableLatitudePair N j k →
        |bandPairError N j k (latitudeKernel α)| ≤
          comparableLatitudeBlockMajorant α
            (neighboringSmallDepthBlockConstant α +
              neighboringUpperSmoothBlockConstant α +
              neighboringUpperBranchBlockConstant α) N j k :=
  neighboringComparable_upper_block_bound_of_smooth
    hα1 hα2 hM (neighboringUpperSmoothBlockConstant_nonneg α)
    (hasLargeDepthNeighboringUpperSmoothBlockBound hα1 hα2 hM)

/-- Every lower-range neighboring comparable block, including the finite
depth branch. -/
theorem neighboringComparable_lower_block_bound
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    ∀ j k : Fin (bandTailCount N + 1),
      NeighboringComparableLatitudePair N j k →
        |bandPairError N j k (latitudeKernel α)| ≤
          comparableLatitudeBlockMajorant α
            (neighboringSmallDepthBlockConstant α +
              neighboringLowerSmoothBlockConstant α +
              neighboringLowerBranchBlockConstant α) N j k :=
  neighboringComparable_lower_block_bound_of_smooth
    hα0 hα1 hM (neighboringLowerSmoothBlockConstant_nonneg α)
    (hasLargeDepthNeighboringLowerSmoothBlockBound hα0 hα1 hM)

end BEMOC
