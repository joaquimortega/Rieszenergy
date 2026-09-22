import BEMOCFormalization.LatitudeResonantExtraction

/-! Uniform bounds for the extracted resonant coefficient in the central chart. -/

open Set

namespace BEMOC

set_option maxHeartbeats 800000

theorem centralComparable_neighboring_quadraticGapCoefficient_bounds
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 : ℝ) / 3 ≤ latitudeQuadraticGapCoefficient s t ∧
      latitudeQuadraticGapCoefficient s t ≤ 8 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hchart :=
    centralComparable_neighboring_rectangle_chart hM hcentral hcomp
      hneigh hs ht
  have hgap :=
    centralComparable_neighboring_normalizedLatitudeGap_le_sq
      hM hcentral hcomp hneigh hs ht
  have habs :=
    abs_centralComparable_neighboring_rectangle_le hM hcentral hcomp
      hneigh hs ht
  have hrsq := heightRadius_sq hsSphere
  have hrtsq := heightRadius_sq htSphere
  have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
  have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
  have hsSq : s ^ 2 ≤ (1 : ℝ) / 1600 := by
    have hmul := mul_self_le_mul_self (abs_nonneg s) habs.1
    norm_num at hmul ⊢
    simpa [pow_two] using hmul
  have htSq : t ^ 2 ≤ (1 : ℝ) / 1600 := by
    have hmul := mul_self_le_mul_self (abs_nonneg t) habs.2
    norm_num at hmul ⊢
    simpa [pow_two] using hmul
  have hrs : (1 : ℝ) / 2 ≤ heightRadius s := by nlinarith
  have hrt : (1 : ℝ) / 2 ≤ heightRadius t := by nlinarith
  have hrs1 := heightRadius_le_one hsSphere
  have hrt1 := heightRadius_le_one htSphere
  let r := heightRadius s * heightRadius t
  let q := normalizedLatitudeGap s t
  have hrlo : (1 : ℝ) / 4 ≤ r := by dsimp [r]; nlinarith
  have hrhi : r ≤ 1 := by
    dsimp [r]
    nlinarith [mul_le_mul hrs1 hrt1 hrt0 (by norm_num : (0 : ℝ) ≤ 1)]
  have hr2lo : (1 : ℝ) / 16 ≤ r ^ 2 := by
    nlinarith [sq_nonneg (r - (1 : ℝ) / 4)]
  have hr2hi : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - r)]
  have hq0 : 0 ≤ q := by simpa [q] using hgap.1
  have hq1 : q ≤ 1 := by
    simpa [q] using
      centralComparable_neighboring_rectangle_normalizedLatitudeGap_le_one
        hM hcentral hcomp hneigh hs ht
  let den := r ^ 2 * (q + 2)
  have hdenlo : (1 : ℝ) / 8 ≤ den := by
    dsimp [den]
    have hm := mul_le_mul hr2lo (by linarith : (2 : ℝ) ≤ q + 2)
      (by norm_num) (by positivity : (0 : ℝ) ≤ r ^ 2)
    nlinarith
  have hdenhi : den ≤ 3 := by
    dsimp [den]
    exact (mul_le_mul hr2hi (by linarith : q + 2 ≤ (3 : ℝ))
      (by positivity) (by norm_num)).trans_eq (by ring)
  have hdenpos : 0 < den := lt_of_lt_of_le (by norm_num) hdenlo
  have hcpos := latitudeQuadraticGapCoefficient_pos hchart.1 hchart.2.1
  have hceq : latitudeQuadraticGapCoefficient s t * den = 1 := by
    dsimp [den, r, q]
    unfold latitudeQuadraticGapCoefficient
    field_simp
  have hlmul :=
    mul_le_mul_of_nonneg_left hdenhi hcpos.le
  have humul :=
    mul_le_mul_of_nonneg_left hdenlo hcpos.le
  constructor <;> nlinarith

end BEMOC
