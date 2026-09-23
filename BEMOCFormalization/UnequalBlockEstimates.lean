import BEMOCFormalization.UnequalBlocks
import BEMOCFormalization.SeparatedComplete

open scoped BigOperators
namespace BEMOC.Definitive

/-- The largest occupied ring has population at most `12M+3`. -/
theorem occupied_population_le {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    population N j ≤ 12 * bandParameter N + 3 := by
  let M := bandParameter N
  rcases lt_trichotomy j M with hn | hc | hs
  · rw [north_population N j hn]
    omega
  · subst j
    exact (central_population_bounds hN).2
  · rw [south_population N j hs]
    omega

/-- A smaller ring in an eightfold unequal pair cannot be the central ring. -/
theorem small_unequal_not_central {N j k : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (hscale : 8 * population N j < population N k) :
    j ≠ bandParameter N := by
  intro hcenter
  subst j
  have hlo := (central_population_bounds hN).1
  have hhi := occupied_population_le hN hk1 hk2
  omega

/-- The smaller ring must lie within the polar half of its hemisphere. -/
theorem small_unequal_polar_half {N j k : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (hscale : 8 * population N j < population N k) :
    (j < bandParameter N ∧ 2 * j ≤ bandParameter N) ∨
      (bandParameter N < j ∧ 2 * (2 * bandParameter N - j) ≤ bandParameter N) := by
  let M := bandParameter N
  have hhi := occupied_population_le hN hk1 hk2
  rcases lt_trichotomy j M with hn | hc | hs
  · left
    rw [north_population N j hn] at hscale
    constructor
    · exact hn
    · omega
  · exact False.elim (small_unequal_not_central hN hj1 hj2 hk1 hk2 hscale hc)
  · right
    rw [south_population N j hs] at hscale
    constructor
    · exact hs
    · omega

/-- Northern unequal populations force the larger index past eight times the smaller. -/
theorem northern_unequal_index_gap {N j k : ℕ}
    (hj : j < bandParameter N) (hk : k < bandParameter N)
    (hscale : 8 * population N j < population N k) :
    8 * j < k := by
  rw [north_population N j hj, north_population N k hk] at hscale
  omega

/-- Northern boundaries are nonnegative. -/
private theorem north_boundary_nonneg_local {N j : ℕ} (hN : 4 ≤ N)
    (hj : j < bandParameter N) : 0 ≤ boundary N j := by
  have hNlow : 4 * (bandParameter N : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hjr : (j : ℝ) + 1 ≤ bandParameter N := by
    exact_mod_cast (by omega : j + 1 ≤ bandParameter N)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [north_boundary hN hj]
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hNr).2
  nlinarith

/-- A northern eightfold unequal rectangle has a fixed algebraic separation. -/
theorem northern_unequal_rectangle_gap {N j k : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hjM : j < bandParameter N)
    (hk1 : 1 ≤ k) (hkM : k < bandParameter N)
    (hscale : 8 * population N j < population N k)
    {s t : ℝ} (hs : s ∈ band N j) (ht : t ∈ band N k) :
    1 - s * t ≤ 8 * (s - t) := by
  have hjk := northern_unequal_index_gap hjM hkM hscale
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hkr : (9 : ℝ) ≤ k := by exact_mod_cast (by omega : 9 ≤ k)
  let x : ℝ := 1 - (k : ℝ) ^ 2 / N
  have hpoly : 4 * (j : ℝ) * ((j : ℝ) + 1) ≤ (k : ℝ) ^ 2 := by
    have hkj : 8 * (j : ℝ) < k := by exact_mod_cast hjk
    nlinarith [sq_nonneg ((k : ℝ) - 8 * j)]
  have hsx : x ≤ s := by
    have hb : boundary N j ≤ s := hs.1
    rw [north_boundary hN hjM] at hb
    dsimp [x]
    apply le_trans _ hb
    apply sub_le_sub_left
    exact (div_le_div_iff₀ hNr hNr).2 (by nlinarith [hpoly])
  have hxt : 0 ≤ x := by
    have hkM' : (k : ℝ) ≤ bandParameter N := by
      exact_mod_cast (by omega : k ≤ bandParameter N)
    have hNlow : 4 * (bandParameter N : ℝ) ^ 2 ≤ N := by
      exact_mod_cast (bandParameter_bounds N).1
    dsimp [x]
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hNr).2
    nlinarith
  have hprev : k - 1 < bandParameter N := by omega
  have hupper : t ≤ boundary N (k - 1) := ht.2
  have hlower : boundary N k ≤ t := ht.1
  have hk0 : 0 ≤ boundary N k := north_boundary_nonneg_local hN hkM
  have ht0 : 0 ≤ t := hk0.trans hlower
  have hprod : x * boundary N k ≤ s * t :=
    mul_le_mul hsx hlower hk0 (le_trans hxt hsx)
  have hscalar : 1 - x * boundary N k ≤
      8 * (x - boundary N (k - 1)) := by
    have hkn : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk1]
      norm_num
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNr
    have heq :
        8 * (x - boundary N (k - 1)) - (1 - x * boundary N k) =
          (19 * (k : ℝ) ^ 2 - 36 * k) / N +
            4 * (k : ℝ) ^ 3 * (k + 1) / (N : ℝ) ^ 2 := by
      rw [north_boundary hN hkM, north_boundary hN hprev]
      dsimp [x]
      rw [← hkn]
      field_simp
      ring
    have hnum : 0 ≤ 19 * (k : ℝ) ^ 2 - 36 * k := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by positivity)
        (show (0 : ℝ) ≤ (k : ℝ) - 9 by linarith)]
    have hge : 0 ≤
        8 * (x - boundary N (k - 1)) - (1 - x * boundary N k) := by
      rw [heq]
      positivity
    linarith
  nlinarith

/-- The angular coupling stays uniformly below the radial term under the height gap. -/
theorem angular_coupling_le_of_height_gap {s t : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hgap : 1 - s * t ≤ 8 * (s - t)) :
    2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
      (1 - (1 / 256 : ℝ)) * (2 - 2 * s * t) := by
  have has : 0 ≤ 1 - s ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2)
      (show 0 ≤ 1 + s by linarith [hs.1])]
  have hat : 0 ≤ 1 - t ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2)
      (show 0 ≤ 1 + t by linarith [ht.1])]
  have hz : 0 ≤ 1 - s * t := by
    have hsa : |s| ≤ 1 := abs_le.mpr hs
    have hta : |t| ≤ 1 := abs_le.mpr ht
    have hst : |s * t| ≤ 1 := by
      rw [abs_mul]
      nlinarith [mul_nonneg (abs_nonneg s) (sub_nonneg.mpr hta),
        mul_nonneg (abs_nonneg t) (sub_nonneg.mpr hsa)]
    linarith [le_abs_self (s * t)]
  have hd : 0 ≤ s - t := by linarith
  have hsq : (1 - s * t) ^ 2 ≤ 64 * (s - t) ^ 2 := by
    nlinarith [sq_nonneg (8 * (s - t) - (1 - s * t))]
  have hid : (1 - s * t) ^ 2 -
      (1 - s ^ 2) * (1 - t ^ 2) = (s - t) ^ 2 := by ring
  have hprod : (1 - s ^ 2) * (1 - t ^ 2) ≤
      (63 / 64 : ℝ) * (1 - s * t) ^ 2 := by
    nlinarith [hid, hsq]
  have hv : 0 ≤ 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) := by
    positivity
  have hu : 0 ≤ (1 - (1 / 256 : ℝ)) * (2 - 2 * s * t) := by
    nlinarith
  have hv2 :
      (2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 =
        4 * ((1 - s ^ 2) * (1 - t ^ 2)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt has, Real.sq_sqrt hat]
    ring
  have hu2 :
      ((1 - (1 / 256 : ℝ)) * (2 - 2 * s * t)) ^ 2 =
        (255 / 256 : ℝ) ^ 2 * 4 * (1 - s * t) ^ 2 := by ring
  rw [← sq_le_sq₀ hv hu]
  rw [hv2, hu2]
  nlinarith [hprod, sq_nonneg (1 - s * t)]

/-- Every point of an occupied height band lies in the physical height interval. -/
theorem occupied_band_mem_unit {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    {s : ℝ} (hs : s ∈ band N j) : s ∈ Set.Icc (-1 : ℝ) 1 := by
  have hprev : j - 1 < 2 * bandParameter N := by omega
  exact ⟨(boundary_ge_neg_one hN hj2).trans hs.1,
    hs.2.trans (boundary_le_one hN hprev)⟩

/-- Reflecting a height reflects its occupied band index. -/
theorem neg_mem_reflected_band {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    {s : ℝ} (hs : s ∈ band N j) :
    -s ∈ band N (2 * bandParameter N - j) := by
  let M := bandParameter N
  let L := 2 * M - 1
  have hjL : j ≤ L := by dsimp [L, M]; omega
  have hpL : j - 1 ≤ L := by dsimp [L, M]; omega
  have hrj := boundary_reflect hN hjL
  have hrp := boundary_reflect hN hpL
  have hidx1 : 2 * M - j = L - (j - 1) := by dsimp [L]; omega
  have hidx2 : 2 * M - j - 1 = L - j := by dsimp [L]; omega
  change boundary N (2 * M - j) ≤ -s ∧
    -s ≤ boundary N (2 * M - j - 1)
  rw [hidx2, hidx1, hrp, hrj]
  exact ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- The northern eightfold rectangle lies in a uniform separated-kernel region. -/
theorem northern_unequal_rectangle_separated {N j k : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hjM : j < bandParameter N)
    (hk1 : 1 ≤ k) (hkM : k < bandParameter N)
    (hscale : 8 * population N j < population N k)
    {s t : ℝ} (hs : s ∈ band N j) (ht : t ∈ band N k) :
    0 < 2 - 2 * s * t ∧
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
        (1 - (1 / 256 : ℝ)) * (2 - 2 * s * t) := by
  have hjk := northern_unequal_index_gap hjM hkM hscale
  have hkp1 : 1 ≤ k - 1 := by omega
  have hkp2 : k - 1 < 2 * bandParameter N := by omega
  have hkk : k - 2 < 2 * bandParameter N := by omega
  have hprev : boundary N (k - 1) < boundary N (k - 2) := by
    have h := boundary_strict hN hkp1 hkp2
    simpa only [Nat.sub_sub, show k - 1 - 1 = k - 2 by omega] using h
  have htlt : t < 1 :=
    lt_of_le_of_lt ht.2
      (lt_of_lt_of_le hprev (boundary_le_one hN hkk))
  have ht0 : 0 ≤ t :=
    (north_boundary_nonneg_local hN hkM).trans ht.1
  have hs1 : s ≤ 1 := (occupied_band_mem_unit hN hj1 (by omega) hs).2
  have hst : s * t ≤ t := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) ht0]
  have hpos : 0 < 2 - 2 * s * t := by linarith
  refine ⟨hpos, ?_⟩
  exact angular_coupling_le_of_height_gap
    (occupied_band_mem_unit hN hj1 (by omega) hs)
    (occupied_band_mem_unit hN hk1 (by omega) ht)
    (northern_unequal_rectangle_gap hN hj1 hjM hk1 hkM hscale hs ht)

/-- Eightfold unequal same-side blocks have one uniform angular ratio bound. -/
theorem sameSide_unequal_rectangle_separated {N j k : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (hscale : 8 * population N j < population N k)
    (hside : SameSide N j k)
    {s t : ℝ} (hs : s ∈ band N j) (ht : t ∈ band N k) :
    0 < 2 - 2 * s * t ∧
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
        (1 - (1 / 256 : ℝ)) * (2 - 2 * s * t) := by
  rcases hside with hn | hsouth
  · exact northern_unequal_rectangle_separated hN hj1 hn.1 hk1 hn.2
      hscale hs ht
  · let jr := 2 * bandParameter N - j
    let kr := 2 * bandParameter N - k
    have hjr1 : 1 ≤ jr := by dsimp [jr]; omega
    have hkr1 : 1 ≤ kr := by dsimp [kr]; omega
    have hjrM : jr < bandParameter N := by dsimp [jr]; omega
    have hkrM : kr < bandParameter N := by dsimp [kr]; omega
    have hpopj := population_reflect hN hj1 hj2
    have hpopk := population_reflect hN hk1 hk2
    have hscaleR : 8 * population N jr < population N kr := by
      dsimp [jr, kr]
      rw [hpopj, hpopk]
      exact hscale
    have hnegs : -s ∈ band N jr := neg_mem_reflected_band hN hj1 hj2 hs
    have hnegt : -t ∈ band N kr := neg_mem_reflected_band hN hk1 hk2 ht
    have h := northern_unequal_rectangle_separated hN hjr1 hjrM hkr1 hkrM
      hscaleR hnegs hnegt
    simpa only [neg_sq, mul_neg, neg_mul, neg_neg] using h

/-- Large configurations have at least sixteen northern ring labels. -/
theorem bandParameter_ge_sixteen {N : ℕ} (hN : 1024 ≤ N) :
    16 ≤ bandParameter N := by
  apply (Nat.le_sqrt').2
  dsimp [bandParameter]
  omega

/-- The north edge of the central band lies below height `1/5`. -/
theorem central_north_boundary_le_fifth {N : ℕ} (hN : 1024 ≤ N) :
    boundary N (bandParameter N - 1) ≤ (1 / 5 : ℝ) := by
  let M := bandParameter N
  have hN4 : 4 ≤ N := by omega
  have hM16 : 16 ≤ M := bandParameter_ge_sixteen hN
  have hMp : 1 ≤ M := by omega
  have hw := boundary_width hN4 (j := M) hMp
  have hc := central_height hN4
  have hcb : population N M ≤ 12 * M + 3 :=
    (central_population_bounds hN4).2
  have hNlow : 4 * M ^ 2 ≤ N := (bandParameter_bounds N).1
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hmass : 5 * population N M ≤ N := by
    have hM : 16 ≤ M := hM16
    nlinarith [sq_nonneg ((M : ℝ) - 16)]
  have hmassR : 5 * (population N M : ℝ) ≤ N := by exact_mod_cast hmass
  have hupper : boundary N (M - 1) = (population N M : ℝ) / N := by
    unfold height at hc
    change (boundary N (M - 1) + boundary N M) / 2 = 0 at hc
    have hw' : boundary N (M - 1) - boundary N M =
        2 * ((population N M : ℝ) / N) := by
      convert hw using 1; ring
    linarith
  rw [hupper]
  exact (div_le_iff₀ hNreal).2 (by nlinarith [hmassR])

/-- A polar northern small band stays above height `23/32`. -/
theorem small_north_band_height_lower {N j : ℕ} (hN : 1024 ≤ N)
    (hj1 : 1 ≤ j) (hjM : j < bandParameter N)
    (hjhalf : 2 * j ≤ bandParameter N)
    {s : ℝ} (hs : s ∈ band N j) : (23 / 32 : ℝ) ≤ s := by
  have hN4 : 4 ≤ N := by omega
  have hM16 := bandParameter_ge_sixteen hN
  have hNlow : 4 * bandParameter N ^ 2 ≤ N := (bandParameter_bounds N).1
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hjr : 2 * (j : ℝ) ≤ bandParameter N := by exact_mod_cast hjhalf
  have hMr : (16 : ℝ) ≤ bandParameter N := by exact_mod_cast hM16
  have hNrlo : 4 * (bandParameter N : ℝ) ^ 2 ≤ N := by
    exact_mod_cast hNlow
  have hb : boundary N j ≤ s := hs.1
  rw [north_boundary hN4 hjM] at hb
  have hbound : 4 * (j : ℝ) * (j + 1) / N ≤ (9 / 32 : ℝ) := by
    apply (div_le_iff₀ hNr).2
    nlinarith [sq_nonneg ((bandParameter N : ℝ) - 16),
      mul_nonneg (show (0 : ℝ) ≤ j by positivity)
        (show (0 : ℝ) ≤ bandParameter N - 2 * j by linarith)]
  linarith

/-- A central or southern large band stays below height `1/5`. -/
theorem central_or_south_band_height_upper {N k : ℕ} (hN : 1024 ≤ N)
    (hk1 : bandParameter N ≤ k) (hk2 : k < 2 * bandParameter N)
    {t : ℝ} (ht : t ∈ band N k) : t ≤ (1 / 5 : ℝ) := by
  have hN4 : 4 ≤ N := by omega
  have hM : 1 ≤ bandParameter N := bandParameter_pos hN4
  have hprev : bandParameter N - 1 ≤ k - 1 := by omega
  have hb := boundary_antitone hN4 hprev (by omega : k - 1 < 2 * bandParameter N)
  exact ht.2.trans (hb.trans (central_north_boundary_le_fifth hN))

/-- Northern small and central/southern large rectangles have absolute separation. -/
theorem northern_opposite_rectangle_separated {N j k : ℕ} (hN : 1024 ≤ N)
    (hj1 : 1 ≤ j) (hjM : j < bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (hscale : 8 * population N j < population N k)
    (hnot : ¬SameSide N j k)
    {s t : ℝ} (hs : s ∈ band N j) (ht : t ∈ band N k) :
    (8 / 5 : ℝ) ≤ 2 - 2 * s * t ∧
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
        (1 - (1 / 256 : ℝ)) * (2 - 2 * s * t) := by
  have hkM : bandParameter N ≤ k := by
    by_contra h
    exact hnot (Or.inl ⟨hjM, by omega⟩)
  have hjhalf : 2 * j ≤ bandParameter N :=
    ((small_unequal_polar_half (by omega : 4 ≤ N) hj1 (by omega)
      hk1 hk2 hscale).resolve_right (by omega)).2
  have hslo : (23 / 32 : ℝ) ≤ s :=
    small_north_band_height_lower hN hj1 hjM hjhalf hs
  have htup : t ≤ (1 / 5 : ℝ) :=
    central_or_south_band_height_upper hN hkM hk2 ht
  have hsphys := occupied_band_mem_unit (by omega : 4 ≤ N) hj1 (by omega) hs
  have htphys := occupied_band_mem_unit (by omega : 4 ≤ N) hk1 hk2 ht
  have hs0 : 0 ≤ s := by linarith
  have hst : s * t ≤ (1 / 5 : ℝ) := by
    have hst1 : s * t ≤ s / 5 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr htup)]
    linarith [hsphys.2]
  have hU : (8 / 5 : ℝ) ≤ 2 - 2 * s * t := by linarith
  have hgap : 1 - s * t ≤ 8 * (s - t) := by
    have hfactor : 0 ≤ 8 + t := by linarith [htphys.1]
    have hs23 : (2 / 3 : ℝ) ≤ s := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hs23) hfactor]
  exact ⟨hU, angular_coupling_le_of_height_gap hsphys htphys hgap⟩

/-- Opposite-side or central eightfold rectangles have absolute separation. -/
theorem opposite_unequal_rectangle_separated {N j k : ℕ} (hN : 1024 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (hscale : 8 * population N j < population N k)
    (hnot : ¬SameSide N j k)
    {s t : ℝ} (hs : s ∈ band N j) (ht : t ∈ band N k) :
    (8 / 5 : ℝ) ≤ 2 - 2 * s * t ∧
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
        (1 - (1 / 256 : ℝ)) * (2 - 2 * s * t) := by
  have hpolar := small_unequal_polar_half (by omega : 4 ≤ N)
    hj1 hj2 hk1 hk2 hscale
  rcases hpolar with ⟨hjM, _⟩ | ⟨hMj, _⟩
  · exact northern_opposite_rectangle_separated hN hj1 hjM hk1 hk2
      hscale hnot hs ht
  · let jr := 2 * bandParameter N - j
    let kr := 2 * bandParameter N - k
    have hjr1 : 1 ≤ jr := by dsimp [jr]; omega
    have hkr1 : 1 ≤ kr := by dsimp [kr]; omega
    have hjrM : jr < bandParameter N := by dsimp [jr]; omega
    have hkr2 : kr < 2 * bandParameter N := by dsimp [kr]; omega
    have hpopj := population_reflect (by omega : 4 ≤ N) hj1 hj2
    have hpopk := population_reflect (by omega : 4 ≤ N) hk1 hk2
    have hscaleR : 8 * population N jr < population N kr := by
      dsimp [jr, kr]
      rw [hpopj, hpopk]
      exact hscale
    have hnotR : ¬SameSide N jr kr := by
      intro hside
      rcases hside with hnn | hss
      · exact hnot (Or.inr (by dsimp [jr, kr] at hnn; omega))
      · exact hnot (Or.inl (by dsimp [jr, kr] at hss; omega))
    have hnegs : -s ∈ band N jr :=
      neg_mem_reflected_band (by omega : 4 ≤ N) hj1 hj2 hs
    have hnegt : -t ∈ band N kr :=
      neg_mem_reflected_band (by omega : 4 ≤ N) hk1 hk2 ht
    have h := northern_opposite_rectangle_separated hN hjr1 hjrM hkr1 hkr2
      hscaleR hnotR hnegs hnegt
    simpa only [neg_sq, mul_neg, neg_mul, neg_neg] using h

/-- The radial term on a northern unequal rectangle controls the large ring scale. -/
theorem northern_unequal_radial_lower {N j k : ℕ} (hN : 1024 ≤ N)
    (hj1 : 1 ≤ j) (hjM : j < bandParameter N)
    (hk1 : 1 ≤ k) (hkM : k < bandParameter N)
    (hscale : 8 * population N j < population N k)
    {s t : ℝ} (hs : s ∈ band N j) (ht : t ∈ band N k) :
    ((population N k : ℝ) / bandParameter N) ^ 2 / 64 ≤
      2 - 2 * s * t := by
  have hN4 : 4 ≤ N := by omega
  have hjk := northern_unequal_index_gap hjM hkM hscale
  have hk2 : 2 ≤ k := by omega
  have hMpos : (0 : ℝ) < bandParameter N := by
    exact_mod_cast bandParameter_pos hN4
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hM1 : (1 : ℝ) ≤ bandParameter N := by
    exact_mod_cast bandParameter_pos hN4
  have hNtop : (N : ℝ) ≤ 16 * (bandParameter N : ℝ) ^ 2 := by
    have htop : (N : ℝ) < 4 * ((bandParameter N : ℝ) + 1) ^ 2 := by
      exact_mod_cast (bandParameter_bounds N).2
    nlinarith
  have ht0 : 0 ≤ t :=
    (north_boundary_nonneg_local hN4 hkM).trans ht.1
  have hs1 : s ≤ 1 := (occupied_band_mem_unit hN4 hj1 (by omega) hs).2
  have hst : s * t ≤ t := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) ht0]
  have hkp : k - 1 < bandParameter N := by omega
  have htup : t ≤ 1 - 4 * ((k - 1 : ℕ) : ℝ) * k / N := by
    have hkone : ((k - 1 : ℕ) : ℝ) + 1 = k := by
      exact_mod_cast (by omega : k - 1 + 1 = k)
    simpa [north_boundary hN4 hkp, hkone] using ht.2
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  rw [hkcast] at htup
  have hbase : 8 * (k : ℝ) * ((k : ℝ) - 1) / N ≤
      2 - 2 * s * t := by
    calc
      8 * (k : ℝ) * ((k : ℝ) - 1) / N =
          2 * (4 * ((k : ℝ) - 1) * k / N) := by ring
      _ ≤ 2 * (1 - t) := by gcongr; linarith
      _ ≤ 2 - 2 * s * t := by linarith
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hcross : (k : ℝ) ^ 2 * N ≤
      32 * (bandParameter N : ℝ) ^ 2 * k * (k - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hNtop
      (sq_nonneg (k : ℝ))
    nlinarith [mul_nonneg (sq_nonneg (bandParameter N : ℝ))
      (show (0 : ℝ) ≤ 2 * (k : ℝ) * ((k : ℝ) - 1) - (k : ℝ) ^ 2 by
        nlinarith)]
  rw [north_population N k hkM]
  push_cast
  have hden : (0 : ℝ) < 4 * (bandParameter N : ℝ) ^ 2 := by positivity
  have hgoal : (k : ℝ) ^ 2 / (4 * (bandParameter N : ℝ) ^ 2) ≤
      8 * (k : ℝ) * ((k : ℝ) - 1) / N := by
    apply (div_le_div_iff₀ hden hNr).2
    nlinarith [hcross]
  calc
    ((4 * (k : ℝ)) / bandParameter N) ^ 2 / 64 =
        (k : ℝ) ^ 2 / (4 * (bandParameter N : ℝ) ^ 2) := by ring
    _ ≤ 8 * (k : ℝ) * ((k : ℝ) - 1) / N := hgoal
    _ ≤ 2 - 2 * s * t := hbase

/-- The same scale lower bound holds after north–south reflection. -/
theorem sameSide_unequal_radial_lower {N j k : ℕ} (hN : 1024 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (hscale : 8 * population N j < population N k)
    (hside : SameSide N j k)
    {s t : ℝ} (hs : s ∈ band N j) (ht : t ∈ band N k) :
    ((population N k : ℝ) / bandParameter N) ^ 2 / 64 ≤
      2 - 2 * s * t := by
  rcases hside with hn | hsouth
  · exact northern_unequal_radial_lower hN hj1 hn.1 hk1 hn.2
      hscale hs ht
  · let jr := 2 * bandParameter N - j
    let kr := 2 * bandParameter N - k
    have hjr1 : 1 ≤ jr := by dsimp [jr]; omega
    have hkr1 : 1 ≤ kr := by dsimp [kr]; omega
    have hjrM : jr < bandParameter N := by dsimp [jr]; omega
    have hkrM : kr < bandParameter N := by dsimp [kr]; omega
    have hpopj := population_reflect (by omega : 4 ≤ N) hj1 hj2
    have hpopk := population_reflect (by omega : 4 ≤ N) hk1 hk2
    have hscaleR : 8 * population N jr < population N kr := by
      dsimp [jr, kr]
      rw [hpopj, hpopk]
      exact hscale
    have hnegs : -s ∈ band N jr :=
      neg_mem_reflected_band (by omega : 4 ≤ N) hj1 hj2 hs
    have hnegt : -t ∈ band N kr :=
      neg_mem_reflected_band (by omega : 4 ≤ N) hk1 hk2 ht
    have h := northern_unequal_radial_lower hN hjr1 hjrM hkr1 hkrM
      hscaleR hnegs hnegt
    dsimp [jr, kr] at h
    rw [hpopk] at h
    simpa only [mul_neg, neg_mul, neg_neg] using h

/-- A band rule only depends on values on its closed physical band. -/
theorem bandError_congr_on_occupied_band {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (f g : ℝ → ℝ) (hfg : ∀ t ∈ band N j, f t = g t) :
    bandError N j f = bandError N j g := by
  have horder : boundary N j ≤ boundary N (j - 1) :=
    (boundary_strict hN hj1 hj2).le
  have hint : (∫ t in boundary N j..boundary N (j - 1), f t) =
      ∫ t in boundary N j..boundary N (j - 1), g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply hfg
    simpa only [band, Set.uIcc_of_le horder] using ht
  have hmid := hfg (height N j) (show height N j ∈ band N j from
    ⟨(height_inside_band hN hj1 hj2).1.le,
      (height_inside_band hN hj1 hj2).2.le⟩)
  unfold bandError
  rw [hint, hmid]

/-- A tensor band block only depends on the kernel on its closed rectangle. -/
theorem bandBlock_congr_on_rectangle {N j k : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (G H : ℝ × ℝ → ℝ)
    (hGH : ∀ p ∈ band N j ×ˢ band N k, G p = H p) :
    bandBlock N j k G = bandBlock N j k H := by
  unfold bandBlock
  apply bandError_congr_on_occupied_band hN hj1 hj2
  intro s hs
  apply bandError_congr_on_occupied_band hN hk1 hk2
  intro t ht
  exact hGH (s, t) ⟨hs, ht⟩

/-- A single smooth extension on a full rectangle yields the mixed Taylor block estimate. -/
theorem kernelBlock_le_of_global_extension
    (hmixed : MixedTaylorBound) {α : ℝ} {N : ℕ} (hN : 4 ≤ N)
    (j k : RingIndex N) (G : ℝ × ℝ → ℝ) (W : Set (ℝ × ℝ))
    (hW : IsOpen W)
    (hrect : band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ W)
    (hG : ContDiffOn ℝ 4 G W)
    (heq : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      G p = latitudeKernel α p.1 p.2)
    (L : ℝ) (hL : 0 ≤ L)
    (hderiv : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      |mixedFourth G p.1 p.2| ≤ L) :
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
      (population N (j.val + 1) : ℝ) ^ 3 *
        (population N (k.val + 1) : ℝ) ^ 3 /
          (bandParameter N : ℝ) ^ 8 * L := by
  have hq (i : RingIndex N) :
      1 ≤ i.val + 1 ∧ i.val + 1 < 2 * bandParameter N := by
    have := i.isLt
    omega
  have hcongr := bandBlock_congr_on_rectangle hN
    (hq j).1 (hq j).2 (hq k).1 (hq k).2 G
    (fun p => latitudeKernel α p.1 p.2) heq
  unfold kernelBlock
  rw [← hcongr]
  exact hmixed N hN j k G W hW hrect hG L hL hderiv

/-- The radial derivative scale has exactly the manuscript's far-block powers. -/
theorem far_block_scale_identity (α rj rk M : ℝ)
    (hrk : 0 < rk) (hM : 0 < M) :
    rj ^ 3 * rk ^ 3 / M ^ 8 *
        (((rk / M) ^ 2 / 64) ^ (α / 2 - 4)) =
      64 ^ (4 - α / 2) * rj ^ 3 /
        (M ^ α * rk ^ (5 - α)) := by
  have hx : 0 < rk / M := div_pos hrk hM
  have hy : 0 < (rk / M) ^ 2 / 64 := by positivity
  have h64 : (0 : ℝ) < 64 := by norm_num
  rw [Real.div_rpow (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 64)]
  rw [← Real.rpow_two (rk / M)]
  rw [← Real.rpow_mul hx.le]
  rw [show (2 : ℝ) * (α / 2 - 4) = α - 8 by ring]
  rw [Real.div_rpow hrk.le hM.le]
  have hrkpow : rk ^ (α - 8) = rk ^ (α - 5) / rk ^ 3 := by
    calc
      rk ^ (α - 8) = rk ^ ((α - 5) - 3) := by congr 1; ring
      _ = rk ^ (α - 5) / rk ^ (3 : ℝ) := Real.rpow_sub hrk _ _
      _ = rk ^ (α - 5) / rk ^ 3 :=
        congrArg (fun z : ℝ => rk ^ (α - 5) / z) (Real.rpow_natCast rk 3)
  have hMpow : M ^ (α - 8) = M ^ α / M ^ 8 := by
    calc
      M ^ (α - 8) = M ^ α / M ^ (8 : ℝ) := Real.rpow_sub hM _ _
      _ = M ^ α / M ^ 8 :=
        congrArg (fun z : ℝ => M ^ α / z) (Real.rpow_natCast M 8)
  have h64pow : (64 : ℝ) ^ (4 - α / 2) =
      (64 : ℝ) ^ 4 / (64 : ℝ) ^ (α / 2) := by
    convert Real.rpow_sub h64 4 (α / 2) using 1
    norm_num [Real.rpow_natCast]
  have h64pow' : (64 : ℝ) ^ (α / 2 - 4) =
      (64 : ℝ) ^ (α / 2) / (64 : ℝ) ^ 4 := by
    convert Real.rpow_sub h64 (α / 2) 4 using 1
    norm_num [Real.rpow_natCast]
  have hrkneg : rk ^ (α - 5) = (rk ^ (5 - α))⁻¹ := by
    rw [show α - 5 = -(5 - α) by ring, Real.rpow_neg hrk.le]
  rw [hrkpow, hMpow, h64pow, h64pow', hrkneg]
  have hMα : M ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hM α)
  have hrkα : rk ^ (5 - α) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hrk _)
  have h64α : (64 : ℝ) ^ (α / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos h64 _)
  field_simp
  ring

/-- A global C⁴ extension with the separated derivative estimate gives the far-block rate. -/
theorem sameSide_kernelBlock_le_of_global_extension
    (hmixed : MixedTaylorBound) {α : ℝ} (hα2 : α < 2)
    {N : ℕ} (hN : 1024 ≤ N) (j k : RingIndex N)
    (hscale : 8 * population N (j.val + 1) < population N (k.val + 1))
    (hside : SameSide N (j.val + 1) (k.val + 1))
    (C : ℝ) (hC : 0 < C)
    (G : ℝ × ℝ → ℝ) (W : Set (ℝ × ℝ))
    (hW : IsOpen W)
    (hrect : band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ W)
    (hG : ContDiffOn ℝ 4 G W)
    (heq : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      G p = latitudeKernel α p.1 p.2)
    (hderiv : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      |mixedFourth G p.1 p.2| ≤
        C * (2 - 2 * p.1 * p.2) ^ (α / 2 - 4)) :
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
      (C * 64 ^ (4 - α / 2)) *
        (population N (j.val + 1) : ℝ) ^ 3 /
          ((bandParameter N : ℝ) ^ α *
            (population N (k.val + 1) : ℝ) ^ (5 - α)) := by
  let rj : ℝ := population N (j.val + 1)
  let rk : ℝ := population N (k.val + 1)
  let M : ℝ := bandParameter N
  let b : ℝ := (rk / M) ^ 2 / 64
  have hjpos : 0 < population N (j.val + 1) :=
    population_pos (by omega : 4 ≤ N) (by omega)
      (by have := j.isLt; omega)
  have hkpos : 0 < population N (k.val + 1) :=
    population_pos (by omega : 4 ≤ N) (by omega)
      (by have := k.isLt; omega)
  have hrj : 0 < rj := by
    dsimp [rj]
    exact_mod_cast hjpos
  have hrk : 0 < rk := by
    dsimp [rk]
    exact_mod_cast hkpos
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast (show 0 < bandParameter N from by
      have := bandParameter_pos (by omega : 4 ≤ N)
      omega)
  have hb : 0 < b := by dsimp [b]; positivity
  have he : α / 2 - 4 ≤ 0 := by linarith
  have hbound (p : ℝ × ℝ)
      (hp : p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1)) :
      b ≤ 2 - 2 * p.1 * p.2 :=
    sameSide_unequal_radial_lower hN (by omega)
      (by have := j.isLt; omega) (by omega)
      (by have := k.isLt; omega) hscale hside hp.1 hp.2
  have hderiv' : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      |mixedFourth G p.1 p.2| ≤ C * b ^ (α / 2 - 4) := by
    intro p hp
    exact (hderiv p hp).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hb (hbound p hp) he) hC.le)
  have hraw := kernelBlock_le_of_global_extension hmixed
    (by omega : 4 ≤ N) j k G W hW hrect hG heq
    (C * b ^ (α / 2 - 4)) (by positivity) hderiv'
  change |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
    rj ^ 3 * rk ^ 3 / M ^ 8 * (C * b ^ (α / 2 - 4)) at hraw
  calc
    _ ≤ rj ^ 3 * rk ^ 3 / M ^ 8 * (C * b ^ (α / 2 - 4)) := hraw
    _ = (C * 64 ^ (4 - α / 2)) * rj ^ 3 /
          (M ^ α * rk ^ (5 - α)) := by
      have hscale' := far_block_scale_identity α rj rk M hrk hM
      rw [← mul_assoc, mul_comm (rj ^ 3 * rk ^ 3 / M ^ 8) C,
        mul_assoc, hscale']
      ring

/-- A global C⁴ extension gives the absolute opposite/central block rate. -/
theorem opposite_kernelBlock_le_of_global_extension
    (hmixed : MixedTaylorBound) {α : ℝ} (hα2 : α < 2)
    {N : ℕ} (hN : 1024 ≤ N) (j k : RingIndex N)
    (hscale : 8 * population N (j.val + 1) < population N (k.val + 1))
    (hnot : ¬SameSide N (j.val + 1) (k.val + 1))
    (C : ℝ) (hC : 0 < C)
    (G : ℝ × ℝ → ℝ) (W : Set (ℝ × ℝ))
    (hW : IsOpen W)
    (hrect : band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ W)
    (hG : ContDiffOn ℝ 4 G W)
    (heq : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      G p = latitudeKernel α p.1 p.2)
    (hderiv : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      |mixedFourth G p.1 p.2| ≤
        C * (2 - 2 * p.1 * p.2) ^ (α / 2 - 4)) :
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
      (C * (8 / 5 : ℝ) ^ (α / 2 - 4)) *
        (population N (j.val + 1) : ℝ) ^ 3 *
          (population N (k.val + 1) : ℝ) ^ 3 /
            (bandParameter N : ℝ) ^ 8 := by
  have he : α / 2 - 4 ≤ 0 := by linarith
  have hderiv' : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      |mixedFourth G p.1 p.2| ≤ C * (8 / 5 : ℝ) ^ (α / 2 - 4) := by
    intro p hp
    have hsep := opposite_unequal_rectangle_separated hN
      (by omega) (by have := j.isLt; omega)
      (by omega) (by have := k.isLt; omega) hscale hnot hp.1 hp.2
    exact (hderiv p hp).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by norm_num) hsep.1 he) hC.le)
  have hraw := kernelBlock_le_of_global_extension hmixed
    (by omega : 4 ≤ N) j k G W hW hrect hG heq
    (C * (8 / 5 : ℝ) ^ (α / 2 - 4)) (by positivity) hderiv'
  calc
    _ ≤ (population N (j.val + 1) : ℝ) ^ 3 *
        (population N (k.val + 1) : ℝ) ^ 3 /
          (bandParameter N : ℝ) ^ 8 *
            (C * (8 / 5 : ℝ) ^ (α / 2 - 4)) := hraw
    _ = _ := by ring

/-- A fixed angular ratio gap places a physical pair inside the even-series domain. -/
theorem separated_series_domain_of_ratio {s t : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hU : 0 < 2 - 2 * s * t)
    (hV : 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
      (1 - (1 / 256 : ℝ)) * (2 - 2 * s * t)) :
    |4 * (1 - s ^ 2) * (1 - t ^ 2)| < (2 - 2 * s * t) ^ 2 := by
  have has : 0 ≤ 1 - s ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2)
      (show 0 ≤ 1 + s by linarith [hs.1])]
  have hat : 0 ≤ 1 - t ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2)
      (show 0 ≤ 1 + t by linarith [ht.1])]
  have hV0 : 0 ≤ 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) := by
    positivity
  have hV2 :
      (2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 =
        4 * (1 - s ^ 2) * (1 - t ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt has, Real.sq_sqrt hat]
    ring
  have hq : (1 - (1 / 256 : ℝ)) ^ 2 < 1 := by norm_num
  have hsq :
      (2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 ≤
      ((1 - (1 / 256 : ℝ)) * (2 - 2 * s * t)) ^ 2 := by
    nlinarith
  rw [hV2] at hsq
  have hstrict : 4 * (1 - s ^ 2) * (1 - t ^ 2) <
      (2 - 2 * s * t) ^ 2 := by
    nlinarith [sq_pos_of_pos hU]
  rw [abs_of_nonneg (by positivity)]
  exact hstrict

/-- Every same-side unequal band rectangle lies in the global smooth domain. -/
theorem sameSide_rectangle_subset_separatedOpen {N : ℕ} (hN : 1024 ≤ N)
    (j k : RingIndex N)
    (hscale : 8 * population N (j.val + 1) < population N (k.val + 1))
    (hside : SameSide N (j.val + 1) (k.val + 1)) :
    band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ separatedOpen := by
  intro p hp
  have hj : 1 ≤ j.val + 1 ∧ j.val + 1 < 2 * bandParameter N := by
    have := j.isLt; omega
  have hk : 1 ≤ k.val + 1 ∧ k.val + 1 < 2 * bandParameter N := by
    have := k.isLt; omega
  have hsep := sameSide_unequal_rectangle_separated (by omega : 4 ≤ N)
    hj.1 hj.2 hk.1 hk.2 hscale hside hp.1 hp.2
  have hs := occupied_band_mem_unit (by omega : 4 ≤ N) hj.1 hj.2 hp.1
  have ht := occupied_band_mem_unit (by omega : 4 ≤ N) hk.1 hk.2 hp.2
  exact ⟨by simpa [angularKernelA] using hsep.1,
    by simpa [angularKernelA] using
      separated_series_domain_of_ratio hs ht hsep.1 hsep.2⟩

/-- Every opposite or central unequal rectangle lies in the global smooth domain. -/
theorem opposite_rectangle_subset_separatedOpen {N : ℕ} (hN : 1024 ≤ N)
    (j k : RingIndex N)
    (hscale : 8 * population N (j.val + 1) < population N (k.val + 1))
    (hnot : ¬SameSide N (j.val + 1) (k.val + 1)) :
    band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ separatedOpen := by
  intro p hp
  have hj : 1 ≤ j.val + 1 ∧ j.val + 1 < 2 * bandParameter N := by
    have := j.isLt; omega
  have hk : 1 ≤ k.val + 1 ∧ k.val + 1 < 2 * bandParameter N := by
    have := k.isLt; omega
  have hsep := opposite_unequal_rectangle_separated hN
    hj.1 hj.2 hk.1 hk.2 hscale hnot hp.1 hp.2
  have hU : 0 < 2 - 2 * p.1 * p.2 := by linarith [hsep.1]
  have hs := occupied_band_mem_unit (by omega : 4 ≤ N) hj.1 hj.2 hp.1
  have ht := occupied_band_mem_unit (by omega : 4 ≤ N) hk.1 hk.2 hp.2
  exact ⟨by simpa [angularKernelA] using hU,
    by simpa [angularKernelA] using
      separated_series_domain_of_ratio hs ht hU hsep.2⟩

/-- The one global smooth extension agrees with the kernel on every unequal rectangle. -/
theorem separatedSmoothExtension_eq_on_unequal_rectangle
    {α : ℝ} {N : ℕ} (hN : 1024 ≤ N) (j k : RingIndex N)
    (hrect : band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ separatedOpen) :
    ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      separatedSmoothExtension α p = latitudeKernel α p.1 p.2 := by
  intro p hp
  have hj : 1 ≤ j.val + 1 ∧ j.val + 1 < 2 * bandParameter N := by
    have := j.isLt; omega
  have hk : 1 ≤ k.val + 1 ∧ k.val + 1 < 2 * bandParameter N := by
    have := k.isLt; omega
  exact separatedSmoothExtension_eq_latitudeKernel (hrect hp)
    (occupied_band_mem_unit (by omega : 4 ≤ N) hj.1 hj.2 hp.1)
    (occupied_band_mem_unit (by omega : 4 ≤ N) hk.1 hk.2 hp.2)

/-- The uniform derivative estimate for the one global separated extension. -/
def UniformSeparatedFourthBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ p ∈ separatedOpen,
      p.1 ∈ Set.Icc (-1 : ℝ) 1 →
      p.2 ∈ Set.Icc (-1 : ℝ) 1 →
      2 * Real.sqrt (1 - p.1 ^ 2) * Real.sqrt (1 - p.2 ^ 2) ≤
        (1 - (1 / 256 : ℝ)) * (2 - 2 * p.1 * p.2) →
      |mixedFourth (separatedSmoothExtension α) p.1 p.2| ≤
        C * (2 - 2 * p.1 * p.2) ^ (α / 2 - 4)

/-- The global fourth-derivative estimate closes both unequal block contracts. -/
theorem unequalBlockBounds_of_uniformSeparatedFourthBound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hfourth : UniformSeparatedFourthBound α) :
    SameSideBlockBound α ∧ OppositeBlockBound α := by
  obtain ⟨C, hC, hbound⟩ := hfourth
  constructor
  · refine ⟨C * (64 : ℝ) ^ (4 - α / 2), by positivity, ?_⟩
    intro N hN j k hscale hside
    have hrect := sameSide_rectangle_subset_separatedOpen hN j k hscale hside
    have heq := separatedSmoothExtension_eq_on_unequal_rectangle
      (α := α) hN j k hrect
    apply sameSide_kernelBlock_le_of_global_extension mixedTaylorBound hα2
      hN j k hscale hside C hC (separatedSmoothExtension α) separatedOpen
      isOpen_separatedOpen hrect
      (separatedSmoothExtension_contDiffOn hα0 hα2) heq
    intro p hp
    have hj : 1 ≤ j.val + 1 ∧ j.val + 1 < 2 * bandParameter N := by
      have := j.isLt; omega
    have hk : 1 ≤ k.val + 1 ∧ k.val + 1 < 2 * bandParameter N := by
      have := k.isLt; omega
    have hsep := sameSide_unequal_rectangle_separated (by omega : 4 ≤ N)
      hj.1 hj.2 hk.1 hk.2 hscale hside hp.1 hp.2
    exact hbound p (hrect hp)
      (occupied_band_mem_unit (by omega : 4 ≤ N) hj.1 hj.2 hp.1)
      (occupied_band_mem_unit (by omega : 4 ≤ N) hk.1 hk.2 hp.2)
      hsep.2

  · refine ⟨C * (8 / 5 : ℝ) ^ (α / 2 - 4), by positivity, ?_⟩
    intro N hN j k hscale hnot
    have hrect := opposite_rectangle_subset_separatedOpen hN j k hscale hnot
    have heq := separatedSmoothExtension_eq_on_unequal_rectangle
      (α := α) hN j k hrect
    apply opposite_kernelBlock_le_of_global_extension mixedTaylorBound hα2
      hN j k hscale hnot C hC (separatedSmoothExtension α) separatedOpen
      isOpen_separatedOpen hrect
      (separatedSmoothExtension_contDiffOn hα0 hα2) heq
    intro p hp
    have hj : 1 ≤ j.val + 1 ∧ j.val + 1 < 2 * bandParameter N := by
      have := j.isLt; omega
    have hk : 1 ≤ k.val + 1 ∧ k.val + 1 < 2 * bandParameter N := by
      have := k.isLt; omega
    have hsep := opposite_unequal_rectangle_separated hN
      hj.1 hj.2 hk.1 hk.2 hscale hnot hp.1 hp.2
    exact hbound p (hrect hp)
      (occupied_band_mem_unit (by omega : 4 ≤ N) hj.1 hj.2 hp.1)
      (occupied_band_mem_unit (by omega : 4 ≤ N) hk.1 hk.2 hp.2)
      hsep.2

/-- The global separated-series estimate supplies the fixed angular-gap
derivative bound needed by every unequal-height block. -/
theorem uniformSeparatedFourthBound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) : UniformSeparatedFourthBound α := by
  obtain ⟨C, hC, hbound⟩ :=
    uniform_separatedSmoothExtension_mixedFourth_le hα0 hα2
      (show (0 : ℝ) < 1 / 256 by norm_num)
      (show (1 / 256 : ℝ) < 1 by norm_num)
  refine ⟨C, hC, ?_⟩
  intro p hp hs ht hsep
  exact hbound p.1 hs p.2 ht hp.1 hsep

/-- The concrete unequal-height block bounds follow from the one global
smooth extension and its uniform mixed-fourth estimate. -/
theorem unequalBlockBounds {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    SameSideBlockBound α ∧ OppositeBlockBound α :=
  unequalBlockBounds_of_uniformSeparatedFourthBound hα0 hα2
    (uniformSeparatedFourthBound hα0 hα2)

/-- The manuscript's same-side unequal-block estimate. -/
theorem sameSideBlockBound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) : SameSideBlockBound α :=
  (unequalBlockBounds hα0 hα2).1

/-- The manuscript's opposite-side unequal-block estimate. -/
theorem oppositeBlockBound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) : OppositeBlockBound α :=
  (unequalBlockBounds hα0 hα2).2

end BEMOC.Definitive
