import BEMOCFormalization.LatitudeNeighboringUnifiedChart

/-! Quadratic physical scale of the central neighboring normalized gap. -/

open Set

namespace BEMOC

/-- On a central neighboring rectangle the normalized radial gap is
uniformly controlled by the square of the physical height difference.
This is the scale conversion needed by both the power branch and the
resonant `q log q` branch. -/
theorem centralComparable_neighboring_normalizedLatitudeGap_le_sq
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
    0 ≤ normalizedLatitudeGap s t ∧
      normalizedLatitudeGap s t ≤ 8 * (s - t) ^ 2 := by
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
  have habs :=
    abs_centralComparable_neighboring_rectangle_le hM hcentral hcomp
      hneigh hs ht
  have hrsq := heightRadius_sq hsSphere
  have hrtsq := heightRadius_sq htSphere
  have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
  have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
  have hsides := abs_le.mp habs.1
  have htides := abs_le.mp habs.2
  have hrs : (1 : ℝ) / 2 ≤ heightRadius s := by
    have hsSq : s ^ 2 ≤ (1 : ℝ) / 1600 := by
      have hmul := mul_self_le_mul_self (abs_nonneg s) habs.1
      norm_num at hmul ⊢
      simpa [pow_two] using hmul
    nlinarith
  have hrt : (1 : ℝ) / 2 ≤ heightRadius t := by
    have htSq : t ^ 2 ≤ (1 : ℝ) / 1600 := by
      have hmul := mul_self_le_mul_self (abs_nonneg t) habs.2
      norm_num at hmul ⊢
      simpa [pow_two] using hmul
    nlinarith
  let q := normalizedLatitudeGap s t
  have hq : 0 ≤ q := by
    dsimp [q]
    rw [normalizedLatitudeGap_eq hchart.1 hchart.2.1]
    exact div_nonneg (latitudeRadialGapSq_nonneg s t)
      (by unfold latitudeAngularScale; positivity)
  have hr : (1 : ℝ) / 4 ≤ heightRadius s * heightRadius t := by
    nlinarith
  have hr2 :
      (1 : ℝ) / 16 ≤ (heightRadius s * heightRadius t) ^ 2 := by
    nlinarith [sq_nonneg (heightRadius s * heightRadius t - (1 : ℝ) / 4)]
  have hq2 : 2 * q ≤ q * (q + 2) := by nlinarith [sq_nonneg q]
  have hmul :
      ((1 : ℝ) / 16) * (2 * q) ≤
        (heightRadius s * heightRadius t) ^ 2 * (q * (q + 2)) :=
    mul_le_mul hr2 hq2 (by positivity) (by positivity)
  have hid := normalizedLatitudeGap_mul_add_two hchart.1 hchart.2.1
  dsimp [q] at hq hmul
  rw [hid] at hmul
  exact ⟨hq, by nlinarith⟩

end BEMOC
