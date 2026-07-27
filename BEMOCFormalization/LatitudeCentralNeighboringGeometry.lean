import BEMOCFormalization.LatitudeTransitionNeighboring

/-!
# The unit cusp chart across the central neighboring transition

At large depth, the central band and either adjacent band have very small
physical height width.  The origin lies in the central band, so the generic
neighboring-length lemma immediately puts both rectangles in a fixed
equatorial chart.
-/

open Set

namespace BEMOC

theorem zero_mem_central_band_rectangle
    {N : ℕ} (hM : 1 ≤ bandCount N) :
    (0 : ℝ) ∈ Icc
      (bandBoundaryHeight N (concreteCentralBandIndex N + 1))
      (bandBoundaryHeight N (concreteCentralBandIndex N)) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  rw [central_bandBoundaryHeight_succ_eq hN hM,
    central_bandBoundaryHeight_eq hN hM]
  have hp : 0 ≤ (centralPopulation N : ℝ) / N := by positivity
  constructor
  · rw [neg_div]
    exact neg_nonpos.mpr hp
  · exact hp

/-- A central band, or a band of at most twice the central scale, has width
at most `1/80` once `M ≥ 600`. -/
theorem bandWidth_le_one_eighty_of_central_or_scale_le
    {N : ℕ} (hM : 600 ≤ bandCount N)
    (j : Fin (bandTailCount N + 1))
    (hj : IsCentralLatitudeBand N j ∨
      latitudeBandScale N j ≤ 2 * bandCount N) :
    bandWidth N j ≤ (1 : ℝ) / 80 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hpop : finiteBandPopulation N j ≤ 15 * bandCount N := by
    rcases latitudeBand_region_trichotomy N j with hjN | hjC | hjS
    · have hp := finiteBandPopulation_le_four_scale_of_northern hjN
      have hs : latitudeBandScale N j ≤ 2 * bandCount N := by
        rcases hj with hc | hs
        · exact (northern_not_central hjN hc).elim
        · exact hs
      omega
    · have hjeq :=
        (isCentralLatitudeBand_iff_eq_concreteCentralBandIndex j).mp hjC
      subst j
      rw [concrete_finiteBandPopulation_central (by omega)]
      exact centralPopulation_le_fifteen_mul_bandCount (by omega)
    · have hp := finiteBandPopulation_le_four_scale_of_southern hjS
      have hs : latitudeBandScale N j ≤ 2 * bandCount N := by
        rcases hj with hc | hs
        · exact (southern_not_central hjS hc).elim
        · exact hs
      omega
  have hpopR :
      (finiteBandPopulation N j : ℝ) ≤
        15 * (bandCount N : ℝ) := by exact_mod_cast hpop
  have hMN :
      4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  have hMreal : (600 : ℝ) ≤ bandCount N := by exact_mod_cast hM
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [bandWidth_eq_population]
  apply (div_le_iff₀ hNreal).2
  nlinarith

theorem centralComparable_bandWidths_le_one_eighty
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k) :
    bandWidth N j ≤ (1 : ℝ) / 80 ∧
      bandWidth N k ≤ (1 : ℝ) / 80 := by
  have hM1 : 1 ≤ bandCount N := by omega
  unfold ComparableLatitudeScales at hcomp
  rcases hcentral.2 with hjC | hkC
  · have hjScale := latitudeBandScale_eq_central hM1 hjC
    constructor
    · exact bandWidth_le_one_eighty_of_central_or_scale_le hM j (Or.inl hjC)
    · apply bandWidth_le_one_eighty_of_central_or_scale_le hM k
      right
      rw [hjScale] at hcomp
      exact hcomp.2
  · have hkScale := latitudeBandScale_eq_central hM1 hkC
    constructor
    · apply bandWidth_le_one_eighty_of_central_or_scale_le hM j
      right
      rw [hkScale] at hcomp
      exact hcomp.1
    · exact bandWidth_le_one_eighty_of_central_or_scale_le hM k (Or.inl hkC)

/-- Both rectangles of a neighboring comparable central pair lie within
`1/40` of the equator. -/
theorem abs_centralComparable_neighboring_rectangle_le
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
    |s| ≤ (1 : ℝ) / 40 ∧ |t| ≤ (1 : ℝ) / 40 := by
  let c := concreteCentralBandIndex N
  have hzero := zero_mem_central_band_rectangle (N := N)
    (by omega : 1 ≤ bandCount N)
  have hw := centralComparable_bandWidths_le_one_eighty hM hcentral hcomp
  have hcwidth :
      bandWidth N c ≤ (1 : ℝ) / 80 := by
    apply bandWidth_le_one_eighty_of_central_or_scale_le hM c
    left
    exact (isCentralLatitudeBand_iff_eq_concreteCentralBandIndex c).2 rfl
  rcases centralLatitudePair_has_concreteCentralBand hcentral with hjc | hkc
  · subst j
    have hs0 := abs_sub_le_neighboringBandLength c c (by simp) hs hzero
    have ht0 := abs_sub_le_neighboringBandLength k c
      (by simpa [Nat.dist_comm] using hneigh) ht hzero
    dsimp [neighboringBandLength] at hs0 ht0
    constructor
    · simpa using hs0.trans (by linarith)
    · simpa using ht0.trans (by linarith)
  · subst k
    have hs0 := abs_sub_le_neighboringBandLength j c hneigh hs hzero
    have ht0 := abs_sub_le_neighboringBandLength c c (by simp) ht hzero
    dsimp [neighboringBandLength] at hs0 ht0
    constructor
    · simpa using hs0.trans (by linarith)
    · simpa using ht0.trans (by linarith)

/-- The complete central neighboring rectangle lies in the same unit
normalized-gap chart as a regular neighboring same-hemisphere pair. -/
theorem centralComparable_neighboring_rectangle_normalizedLatitudeGap_le_one
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
    normalizedLatitudeGap s t ≤ 1 := by
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
  have habs :=
    abs_centralComparable_neighboring_rectangle_le hM hcentral hcomp
      hneigh hs ht
  have hsInterior : s ∈ Ioo (-1 : ℝ) 1 := by
    have hsides := abs_le.mp habs.1
    constructor <;> linarith
  have htInterior : t ∈ Ioo (-1 : ℝ) 1 := by
    have htsides := abs_le.mp habs.2
    constructor <;> linarith
  have hrsq := heightRadius_sq hsSphere
  have hrtsq := heightRadius_sq htSphere
  have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
  have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
  have hsSq : s ^ 2 ≤ (1 : ℝ) / 1600 := by
    have hmul := mul_self_le_mul_self (abs_nonneg s) habs.1
    rw [← sq_abs]
    norm_num at hmul ⊢
    simpa [pow_two] using hmul
  have htSq : t ^ 2 ≤ (1 : ℝ) / 1600 := by
    have hmul := mul_self_le_mul_self (abs_nonneg t) habs.2
    rw [← sq_abs]
    norm_num at hmul ⊢
    simpa [pow_two] using hmul
  have hrs : (1 : ℝ) / 2 ≤ heightRadius s := by nlinarith
  have hrt : (1 : ℝ) / 2 ≤ heightRadius t := by nlinarith
  have hw := abs_sub_le_neighboringBandLength j k hneigh hs ht
  have hwidths :=
    centralComparable_bandWidths_le_one_eighty hM hcentral hcomp
  have hlen : neighboringBandLength N j k ≤ (1 : ℝ) / 40 := by
    unfold neighboringBandLength
    linarith
  have hwprod : |s - t| ≤ heightRadius s * heightRadius t := by
    calc
      |s - t| ≤ neighboringBandLength N j k := hw
      _ ≤ (1 : ℝ) / 40 := hlen
      _ ≤ heightRadius s * heightRadius t := by nlinarith
  have hq0 : 0 ≤ normalizedLatitudeGap s t := by
    rw [normalizedLatitudeGap_eq hsInterior htInterior]
    exact div_nonneg (latitudeRadialGapSq_nonneg s t)
      (by unfold latitudeAngularScale; positivity)
  have hid := normalizedLatitudeGap_mul_add_two hsInterior htInterior
  have hsq :
      (s - t) ^ 2 ≤ (heightRadius s * heightRadius t) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hwprod 2
  have hrpos : 0 < (heightRadius s * heightRadius t) ^ 2 := by positivity
  apply le_of_not_gt
  intro hqgt
  have hprodgt :
      3 < normalizedLatitudeGap s t *
        (normalizedLatitudeGap s t + 2) := by nlinarith
  have hmul := mul_lt_mul_of_pos_left hprodgt hrpos
  nlinarith

end BEMOC
