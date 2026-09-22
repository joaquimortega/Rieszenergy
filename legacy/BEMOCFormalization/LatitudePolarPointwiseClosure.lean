import BEMOCFormalization.LatitudePolarEndpointPeano

/-!
# Premise-free polar pointwise closure

The endpoint Peano transfer is combined here with the finite polar
geometry and the manuscript scale arithmetic.
-/

open Set

namespace BEMOC

theorem polar_leftSmall_orientation
    {N : ℕ} {j k : Fin (bandTailCount N + 1)}
    (hp : PolarLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k) :
    IsPolarLatitudeBand N j ∧ IsRegularLatitudeBand N k := by
  have hjpos := latitudeBandScale_pos N j
  have hkpos := latitudeBandScale_pos N k
  unfold PolarLatitudePair IsPolarLatitudeBand IsRegularLatitudeBand at *
  omega

theorem polar_leftSmall_same_baseGeometry
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)}
    (hp : PolarLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    (hsame : SameLatitudeHemisphere N j k) :
    LatitudeEvenPowerSeriesBaseGeometry N j k
      (2 * (latitudeBandScale N k : ℝ) ^ 2 / N) where
  base_pos := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hk : (0 : ℝ) < latitudeBandScale N k := by
      exact_mod_cast latitudeBandScale_pos N k
    positivity
  base_le s hs t ht := by
    obtain ⟨_hjpolar, hkreg⟩ := polar_leftSmall_orientation hp hscale
    rcases hsame with hNN | hSS
    · have hb :=
        northern_regular_rectangle_radiusSq_scale_bounds
          hN k hNN.2 hkreg ht
      rw [angularKernelA_eq_radiusSq_add]
      nlinarith [show 0 ≤ 1 - s ^ 2 by
        have hsI : s ∈ Icc (-1 : ℝ) 1 :=
          ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
            hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
        nlinarith [hsI.1, hsI.2], sq_nonneg (s - t)]
    · let jr := concreteReflectBandIndex N j
      let kr := concreteReflectBandIndex N k
      have htr := neg_mem_reflected_band_rectangle_unequal hN k ht
      have hkrN : IsNorthernLatitudeBand N kr :=
        reflect_southern_is_northern hSS.2
      have hkrReg : IsRegularLatitudeBand N kr := by
        simpa [kr] using hkreg
      have hb :=
        northern_regular_rectangle_radiusSq_scale_bounds
          hN kr hkrN hkrReg htr
      have hscaleEq :
          latitudeBandScale N kr = latitudeBandScale N k := by
        simp [kr]
      rw [angularKernelA_eq_radiusSq_add]
      rw [hscaleEq] at hb
      nlinarith [show 0 ≤ 1 - s ^ 2 by
        have hsI : s ∈ Icc (-1 : ℝ) 1 :=
          ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
            hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
        nlinarith [hsI.1, hsI.2], sq_nonneg (s - t)]
  ratio_le s hs t ht := by
    obtain ⟨_hjpolar, hkreg⟩ := polar_leftSmall_orientation hp hscale
    have hsI : s ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
        hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
    have hu : 0 ≤ 1 - s ^ 2 := by nlinarith [hsI.1, hsI.2]
    rcases hsame with hNN | hSS
    · have hb := northern_regular_rectangle_radiusSq_scale_bounds
          hN k hNN.2 hkreg ht
      have hv : 0 < 1 - t ^ 2 := by
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        have hk : (0 : ℝ) < latitudeBandScale N k := by
          exact_mod_cast latitudeBandScale_pos N k
        exact (by positivity :
          0 < 2 * (latitudeBandScale N k : ℝ) ^ 2 / N) |>.trans_le hb.1
      exact unequalAngularRatio_le_fifteen_sixteen_of_radiusSq hu hv
        (northern_unequal_rectangle_radiusSq_ratio
          hN j k hNN.1 hNN.2 hscale hs ht)
    · let kr := concreteReflectBandIndex N k
      have htr := neg_mem_reflected_band_rectangle_unequal hN k ht
      have hkrN : IsNorthernLatitudeBand N kr :=
        reflect_southern_is_northern hSS.2
      have hkrReg : IsRegularLatitudeBand N kr := by
        simpa [kr] using hkreg
      have hb := northern_regular_rectangle_radiusSq_scale_bounds
          hN kr hkrN hkrReg htr
      have hv : 0 < 1 - t ^ 2 := by
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        have hk : (0 : ℝ) < latitudeBandScale N kr := by
          exact_mod_cast latitudeBandScale_pos N kr
        have hz : 0 < 1 - (-t) ^ 2 :=
          (by positivity :
            0 < 2 * (latitudeBandScale N kr : ℝ) ^ 2 / N) |>.trans_le hb.1
        nlinarith
      exact unequalAngularRatio_le_fifteen_sixteen_of_radiusSq hu hv
        (southern_unequal_rectangle_radiusSq_ratio
          hN j k hSS.1 hSS.2 hscale hs ht)

theorem polarLatitude_seriesScale_le_manuscriptScale
    {α : ℝ} (_hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    (k : Fin (bandTailCount N + 1)) :
    (2 * (latitudeBandScale N k : ℝ) ^ 2 / N) ^ (α / 2 - 4) ≤
      10 ^ (4 - α / 2) *
        (bandCount N : ℝ) ^ (8 - α) *
        (latitudeBandScale N k : ℝ) ^ (α - 8) := by
  let M : ℝ := bandCount N
  let d : ℝ := latitudeBandScale N k
  let L : ℝ := 2 * d ^ 2 / N
  let p : ℝ := 4 - α / 2
  have hMpos : 0 < M := by
    dsimp [M]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast latitudeBandScale_pos N k
  have hL : 0 < L := by
    dsimp [L]
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hNupper : (N : ℝ) ≤ 20 * M ^ 2 := by
    dsimp [M]
    exact_mod_cast bemoc_N_le_twenty_bandCount_sq hM
  have hLinv : L⁻¹ = (N : ℝ) / (2 * d ^ 2) := by
    dsimp [L]
    field_simp
  have hbase : L⁻¹ ≤ 10 * M ^ 2 / d ^ 2 := by
    rw [hLinv]
    calc
      (N : ℝ) / (2 * d ^ 2) ≤
          (20 * M ^ 2) / (2 * d ^ 2) := by
        exact div_le_div_of_nonneg_right hNupper (by positivity)
      _ = 10 * M ^ 2 / d ^ 2 := by ring
  have hrpow :
      L⁻¹ ^ p ≤ (10 * M ^ 2 / d ^ 2) ^ p :=
    Real.rpow_le_rpow (inv_nonneg.2 hL.le) hbase hp
  calc
    (2 * (latitudeBandScale N k : ℝ) ^ 2 / N) ^ (α / 2 - 4) =
        L ^ (-p) := by
      dsimp [L, d, p]
      congr 1
      ring
    _ = L⁻¹ ^ p := by
      rw [Real.rpow_neg hL.le, Real.inv_rpow hL.le]
    _ ≤ (10 * M ^ 2 / d ^ 2) ^ p := hrpow
    _ = 10 ^ p * M ^ (2 * p) * d ^ (-2 * p) := by
      rw [Real.div_rpow (mul_nonneg (by norm_num) (sq_nonneg M))
          (sq_nonneg d),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) (sq_nonneg M)]
      rw [show M ^ 2 = M ^ (2 : ℝ) by
          exact (Real.rpow_natCast M 2).symm,
        show d ^ 2 = d ^ (2 : ℝ) by
          exact (Real.rpow_natCast d 2).symm,
        ← Real.rpow_mul hMpos.le, ← Real.rpow_mul hdpos.le,
        div_eq_mul_inv, ← Real.rpow_neg hdpos.le]
      ring_nf
    _ = 10 ^ (4 - α / 2) *
        (bandCount N : ℝ) ^ (8 - α) *
        (latitudeBandScale N k : ℝ) ^ (α - 8) := by
      dsimp [M, d, p]
      congr 1 <;> ring_nf

theorem polar_leftSmall_same_unequal_bound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hp : PolarLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    (hsame : SameLatitudeHemisphere N j k) :
    |bandPairError N j k (latitudeKernel α)| ≤
      unequalLatitudeBlockMajorant α
        (1024 * unequalLatitudeDssttConstant α) N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let L : ℝ := 2 * (latitudeBandScale N k : ℝ) ^ 2 / N
  let C : ℝ := unequalLatitudeDssttSeriesConstant α * L ^ (α / 2 - 4)
  have hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L := by
    simpa [L] using
      polar_leftSmall_same_baseGeometry hN hp hscale hsame
  have hraw :=
    abs_latitudeKernel_bandPairError_le_of_evenSeriesDsstt
      hα0 hα2 hN hM j k (C := C) hgeo
      (mul_nonneg (unequalLatitudeDssttSeriesConstant_nonneg α)
        (Real.rpow_nonneg (by positivity) _))
      (fun x hx y hy ↦ by
        have h :=
          abs_latitudeEvenPowerDSSTTSeriesSum_le_series_scale
            hα0 hα2 hN hgeo.swap hy hx
        simpa [C] using h)
  have hscalePow :=
    polarLatitude_seriesScale_le_manuscriptScale
      hα0 hα2 hN (by omega) k
  have hCscale :
      C ≤ unequalLatitudeDssttConstant α *
        (bandCount N : ℝ) ^ (8 - α) *
        (latitudeBandScale N k : ℝ) ^ (α - 8) := by
    dsimp [C, L]
    calc
      unequalLatitudeDssttSeriesConstant α *
          (2 * (latitudeBandScale N k : ℝ) ^ 2 / N) ^
            (α / 2 - 4) ≤
        unequalLatitudeDssttSeriesConstant α *
          (10 ^ (4 - α / 2) *
            (bandCount N : ℝ) ^ (8 - α) *
            (latitudeBandScale N k : ℝ) ^ (α - 8)) :=
        mul_le_mul_of_nonneg_left hscalePow
          (unequalLatitudeDssttSeriesConstant_nonneg α)
      _ = unequalLatitudeDssttConstant α *
          (bandCount N : ℝ) ^ (8 - α) *
          (latitudeBandScale N k : ℝ) ^ (α - 8) := by
        unfold unequalLatitudeDssttConstant
        ring
  have hpops := finiteBandPopulations_le_four_scales_of_same hsame
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤
        4 * (latitudeBandScale N j : ℝ) := by exact_mod_cast hpops.1
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤
        4 * (latitudeBandScale N k : ℝ) := by exact_mod_cast hpops.2
  have hMN : 4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  have harith := unequal_scale_arithmetic
    (α := α) (C := unequalLatitudeDssttConstant α)
    (M := (bandCount N : ℝ)) (N := (N : ℝ))
    (dj := (latitudeBandScale N j : ℝ))
    (dk := (latitudeBandScale N k : ℝ))
    (pj := (finiteBandPopulation N j : ℝ))
    (pk := (finiteBandPopulation N k : ℝ))
    (unequalLatitudeDssttConstant_nonneg α)
    (by positivity) (by exact_mod_cast hN)
    (by exact_mod_cast latitudeBandScale_pos N j)
    (by exact_mod_cast latitudeBandScale_pos N k)
    (by positivity) (by positivity) hpj hpk hMN
  unfold unequalLatitudeBlockMajorant
  calc
    |bandPairError N j k (latitudeKernel α)| ≤
        64 * C * (finiteBandPopulation N j : ℝ) ^ 3 *
          (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := hraw
    _ ≤
        64 * (unequalLatitudeDssttConstant α *
          (bandCount N : ℝ) ^ (8 - α) *
          (latitudeBandScale N k : ℝ) ^ (α - 8)) *
          (finiteBandPopulation N j : ℝ) ^ 3 *
          (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
      gcongr
    _ ≤ 1024 * unequalLatitudeDssttConstant α *
        (latitudeBandScale N j : ℝ) ^ 3 *
        (bandCount N : ℝ) ^ (-α) *
        (latitudeBandScale N k : ℝ) ^ (α - 5) := harith

theorem polar_leftSmall_nonsame_half_height_gap
    {N : ℕ} (hN : 0 < N) (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hp : PolarLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    (hnotsame : ¬ SameLatitudeHemisphere N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 : ℝ) / 2 ≤ |s - t| := by
  obtain ⟨hjpolar, _hkreg⟩ := polar_leftSmall_orientation hp hscale
  have hjNotCentral : ¬ IsCentralLatitudeBand N j := by
    intro hjc
    have hjM := latitudeBandScale_eq_central (by omega) hjc
    unfold IsPolarLatitudeBand at hjpolar
    omega
  have hjdepth : 2 * latitudeBandScale N j ≤ bandCount N := by
    unfold IsPolarLatitudeBand at hjpolar
    omega
  by_cases hkc : IsCentralLatitudeBand N k
  · have hkEq : k = concreteCentralBandIndex N :=
      (isCentralLatitudeBand_iff_eq_concreteCentralBandIndex k).mp hkc
    have htQuarter : |t| ≤ (1 : ℝ) / 4 := by
      rw [hkEq] at ht
      exact abs_central_band_rectangle_le_quarter hM ht
    have hMreal : (15 : ℝ) ≤ bandCount N := by exact_mod_cast hM
    have hsmall : 18 / (bandCount N : ℝ) ^ 2 ≤ (1 : ℝ) / 4 := by
      have hMpos : (0 : ℝ) < bandCount N := by positivity
      apply (div_le_iff₀ (sq_pos_of_pos hMpos)).2
      nlinarith
    rcases latitudeBand_region_trichotomy N j with hjN | hjC | hjS
    · have hgap := northern_polar_rectangle_height_gap
        hN (by omega) j hjN (by
          unfold IsPolarLatitudeBand at hjpolar
          omega) hs
      have hsThree : (3 : ℝ) / 4 ≤ s := by
        linarith [hgap.2.trans hsmall]
      have htUpper : t ≤ (1 : ℝ) / 4 := (abs_le.mp htQuarter).2
      rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]
      linarith
    · exact (hjNotCentral hjC).elim
    · have hgap := southern_polar_rectangle_height_gap
        hN (by omega) j hjS (by
          unfold IsPolarLatitudeBand at hjpolar
          omega) hs
      have hsThree : s ≤ -(3 : ℝ) / 4 := by
        linarith [hgap.2.trans hsmall]
      have htLower : -(1 : ℝ) / 4 ≤ t := by
        linarith [(abs_le.mp htQuarter).1]
      rw [abs_of_nonpos (by linarith : s - t ≤ 0)]
      linarith
  · have hopp : OppositeLatitudeHemispheres N j k := by
      rcases same_or_opposite_of_noncentral hjNotCentral hkc with hsame | hopp
      · exact (hnotsame hsame).elim
      · exact hopp
    exact opposite_band_rectangle_height_gap_of_half_depth
      hN (by omega) j k hopp (Or.inl hjdepth) hs ht

theorem polar_leftSmall_nonsame_baseGeometry
    {N : ℕ} (hN : 0 < N) (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hp : PolarLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    (hnotsame : ¬ SameLatitudeHemisphere N j k) :
    LatitudeEvenPowerSeriesBaseGeometry N j k ((1 : ℝ) / 4) where
  base_pos := by norm_num
  base_le s hs t ht := by
    have hsI : s ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
        hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
    have htI : t ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
        ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
    exact quarter_le_angularKernelA_of_half_height_gap hsI htI
      (polar_leftSmall_nonsame_half_height_gap
        hN hM hp hscale hnotsame hs ht)
  ratio_le s hs t ht := by
    have hsI : s ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
        hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
    have htI : t ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
        ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
    exact unequalAngularRatio_le_fifteen_sixteen_of_height_gap hsI htI
      (polar_leftSmall_nonsame_half_height_gap
        hN hM hp hscale hnotsame hs ht)

theorem fifthPower_bound_le_unequalMajorant
    {α C : ℝ} (hα2 : α < 2) (hC : 0 ≤ C)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hbound :
      |bandPairError N j k (latitudeKernel α)| ≤
        C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) /
          (bandCount N : ℝ) ^ (5 : ℕ)) :
    |bandPairError N j k (latitudeKernel α)| ≤
      unequalLatitudeBlockMajorant α C N j k := by
  let M : ℝ := bandCount N
  let d : ℝ := latitudeBandScale N k
  have hMpos : 0 < M := by
    dsimp [M]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast latitudeBandScale_pos N k
  have hdM : d ≤ M := by
    dsimp [d, M]
    exact_mod_cast latitudeBandScale_le_bandCount hM k
  have he : α - 5 ≤ 0 := by linarith
  have hpow : M ^ (α - 5) ≤ d ^ (α - 5) :=
    Real.rpow_le_rpow_of_nonpos hdpos hdM he
  have hMcombine :
      M ^ (-α) * M ^ (α - 5) = M ^ (-5 : ℝ) := by
    rw [← Real.rpow_add hMpos]
    congr 1
    ring
  unfold unequalLatitudeBlockMajorant
  refine hbound.trans ?_
  rw [show M ^ (5 : ℕ) = M ^ (5 : ℝ) by
      exact (Real.rpow_natCast M 5).symm,
    div_eq_mul_inv, ← Real.rpow_neg hMpos.le]
  dsimp [M, d] at hMcombine hpow ⊢
  calc
    C * (latitudeBandScale N j : ℝ) ^ 3 *
        (bandCount N : ℝ) ^ (-5 : ℝ) =
      C * (latitudeBandScale N j : ℝ) ^ 3 *
        ((bandCount N : ℝ) ^ (-α) *
          (bandCount N : ℝ) ^ (α - 5)) := by rw [hMcombine]
    _ ≤ C * (latitudeBandScale N j : ℝ) ^ 3 *
        ((bandCount N : ℝ) ^ (-α) *
          (latitudeBandScale N k : ℝ) ^ (α - 5)) := by
      gcongr
    _ = C * (latitudeBandScale N j : ℝ) ^ 3 *
        (bandCount N : ℝ) ^ (-α) *
        (latitudeBandScale N k : ℝ) ^ (α - 5) := by ring

theorem polar_leftSmall_nonsame_unequal_bound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 15 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hp : PolarLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    (hnotsame : ¬ SameLatitudeHemisphere N j k) :
    |bandPairError N j k (latitudeKernel α)| ≤
      unequalLatitudeBlockMajorant α
        (54000 * exceptionalLatitudeDssttConstant α) N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let C : ℝ := exceptionalLatitudeDssttConstant α
  have hC : 0 ≤ C := by
    dsimp [C]
    exact exceptionalLatitudeDssttConstant_nonneg α
  have hgeo :=
    polar_leftSmall_nonsame_baseGeometry hN hM hp hscale hnotsame
  have hraw :=
    abs_latitudeKernel_bandPairError_le_of_evenSeriesDsstt
      hα0 hα2 hN (by omega) j k (C := C) hgeo
      (exceptionalLatitudeDssttConstant_nonneg α)
      (fun x hx y hy ↦ by
        have h :=
          abs_latitudeEvenPowerDSSTTSeriesSum_le_series_scale
            hα0 hα2 hN hgeo.swap hy hx
        simpa [C, exceptionalLatitudeDssttConstant] using h)
  obtain ⟨hjpolar, _hkreg⟩ := polar_leftSmall_orientation hp hscale
  have hjNotCentral : ¬ IsCentralLatitudeBand N j := by
    intro hjc
    have hjM := latitudeBandScale_eq_central (by omega) hjc
    unfold IsPolarLatitudeBand at hjpolar
    omega
  have hpjNat :
      finiteBandPopulation N j ≤ 4 * latitudeBandScale N j := by
    rcases latitudeBand_region_trichotomy N j with hjN | hjC | hjS
    · exact finiteBandPopulation_le_four_scale_of_northern hjN
    · exact (hjNotCentral hjC).elim
    · exact finiteBandPopulation_le_four_scale_of_southern hjS
  have hpkNat :=
    finiteBandPopulation_le_fifteen_mul_bandCount (by omega) k
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤
        4 * (latitudeBandScale N j : ℝ) := by exact_mod_cast hpjNat
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤
        15 * (bandCount N : ℝ) := by exact_mod_cast hpkNat
  have hMN : 4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  have hpj3 :
      (finiteBandPopulation N j : ℝ) ^ 3 ≤
        (4 * (latitudeBandScale N j : ℝ)) ^ 3 := by gcongr
  have hpk3 :
      (finiteBandPopulation N k : ℝ) ^ 3 ≤
        (15 * (bandCount N : ℝ)) ^ 3 := by gcongr
  have hden :
      (4 * (bandCount N : ℝ) ^ 2) ^ 4 ≤ (N : ℝ) ^ 4 := by gcongr
  have hcoarse :
      |bandPairError N j k (latitudeKernel α)| ≤
        54000 * C * (latitudeBandScale N j : ℝ) ^ 3 /
          (bandCount N : ℝ) ^ 5 := by
    calc
      |bandPairError N j k (latitudeKernel α)| ≤
          64 * C * (finiteBandPopulation N j : ℝ) ^ 3 *
            (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := hraw
      _ ≤ (64 * C * (4 * (latitudeBandScale N j : ℝ)) ^ 3 *
            (15 * (bandCount N : ℝ)) ^ 3) / (N : ℝ) ^ 4 := by
        gcongr
      _ ≤ (64 * C * (4 * (latitudeBandScale N j : ℝ)) ^ 3 *
            (15 * (bandCount N : ℝ)) ^ 3) /
            (4 * (bandCount N : ℝ) ^ 2) ^ 4 := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 54000 * C * (latitudeBandScale N j : ℝ) ^ 3 /
          (bandCount N : ℝ) ^ 5 := by
        field_simp
        ring
  exact fifthPower_bound_le_unequalMajorant
    hα2 (by positivity) (by omega) j k (by
      simpa [C, mul_assoc] using hcoarse)

/-- Premise-free oriented polar field for the global unequal assembly. -/
theorem polar_leftSmall_unequal_bound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 15 ≤ bandCount N) :
    ∀ j k, PolarLatitudePair N j k →
      2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α
          (1024 * unequalLatitudeDssttConstant α +
            54000 * exceptionalLatitudeDssttConstant α) N j k := by
  intro j k hp hscale
  by_cases hsame : SameLatitudeHemisphere N j k
  · exact (polar_leftSmall_same_unequal_bound_series
      hα0 hα2 (by omega) j k hp hscale hsame).trans
        (unequalLatitudeBlockMajorant_mono (by
          have hE := exceptionalLatitudeDssttConstant_nonneg α
          nlinarith))
  · exact (polar_leftSmall_nonsame_unequal_bound_series
      hα0 hα2 hM j k hp hscale hsame).trans
        (unequalLatitudeBlockMajorant_mono (by
          have hU := unequalLatitudeDssttConstant_nonneg α
          nlinarith))

theorem polar_same_dist_le_three
    {N : ℕ} {j k : Fin (bandTailCount N + 1)}
    (hp : PolarLatitudePair N j k)
    (hc : ComparableLatitudeScales N j k)
    (hsame : SameLatitudeHemisphere N j k) :
    Nat.dist (j : ℕ) (k : ℕ) ≤ 3 := by
  obtain ⟨hj4, hk4⟩ := polar_comparable_scales_le_four hp hc
  rcases hsame with hNN | hSS
  · have hjEq := latitudeBandScale_eq_north hNN.1
    have hkEq := latitudeBandScale_eq_north hNN.2
    rw [hjEq] at hj4
    rw [hkEq] at hk4
    by_cases hjk : (j : ℕ) ≤ (k : ℕ)
    · rw [Nat.dist_eq_sub_of_le hjk]
      omega
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega : (k : ℕ) ≤ (j : ℕ))]
      omega
  · have hjEq := latitudeBandScale_eq_south hSS.1
    have hkEq := latitudeBandScale_eq_south hSS.2
    rw [hjEq] at hj4
    rw [hkEq] at hk4
    by_cases hjk : (j : ℕ) ≤ (k : ℕ)
    · rw [Nat.dist_eq_sub_of_le hjk]
      omega
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega : (k : ℕ) ≤ (j : ℕ))]
      omega

theorem polar_comparable_same_bound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hp : PolarLatitudePair N j k)
    (hc : ComparableLatitudeScales N j k)
    (hsame : SameLatitudeHemisphere N j k) :
    |bandPairError N j k (latitudeKernel α)| ≤
      comparableLatitudeBlockMajorant α
        (32768 * 144 ^ (α / 2)) N j k := by
  have hraw :=
    abs_latitudeKernel_bandPairError_le_polar_comparable_same
      hα0.le (by
        have hfour := four_mul_bandCount_sq_le N
        have : 0 < 4 * bandCount N ^ 2 := by positivity
        omega) hM j k hp hc hsame
  obtain ⟨hj4, hk4⟩ := polar_comparable_scales_le_four hp hc
  have hpops := finiteBandPopulations_le_four_scales_of_same hsame
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤
        4 * (latitudeBandScale N j : ℝ) := by exact_mod_cast hpops.1
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤
        4 * (latitudeBandScale N k : ℝ) := by exact_mod_cast hpops.2
  have hdk :
      (latitudeBandScale N k : ℝ) ≤
        2 * (latitudeBandScale N j : ℝ) := by
    exact_mod_cast hc.2
  have hdj4 : (latitudeBandScale N j : ℝ) ≤ 4 := by exact_mod_cast hj4
  have hpopprod :
      4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) ≤
        512 * (latitudeBandScale N j : ℝ) := by
    have hdj : (0 : ℝ) ≤ latitudeBandScale N j := by positivity
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hpj) (sub_nonneg.mpr hpk)]
  have hMpos : (0 : ℝ) < bandCount N := by positivity
  have hrpow :
      (144 / (bandCount N : ℝ) ^ 2) ^ (α / 2) =
        144 ^ (α / 2) * (bandCount N : ℝ) ^ (-α) := by
    rw [Real.div_rpow (by norm_num) (sq_nonneg _),
      show (bandCount N : ℝ) ^ 2 =
        (bandCount N : ℝ) ^ (2 : ℝ) by
          exact (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hMpos.le, div_eq_mul_inv,
      ← Real.rpow_neg hMpos.le]
    congr 2
    ring
  have hdist := polar_same_dist_le_three hp hc hsame
  have hD : (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ≤ 4 := by
    exact_mod_cast (show 1 + Nat.dist (j : ℕ) (k : ℕ) ≤ 4 by omega)
  have he : α - 3 ≤ 0 := by linarith
  have hweight :
      (1 : ℝ) / 64 ≤
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
    have hbase : (0 : ℝ) < 1 + Nat.dist (j : ℕ) (k : ℕ) := by positivity
    have hpow := Real.rpow_le_rpow_of_nonpos hbase hD he
    have hexp : (-3 : ℝ) ≤ α - 3 := by linarith
    have htwo :
        (4 : ℝ) ^ (-3 : ℝ) ≤ 4 ^ (α - 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    norm_num at htwo ⊢
    exact htwo.trans hpow
  unfold comparableLatitudeBlockMajorant
  rw [hrpow] at hraw
  calc
    |bandPairError N j k (latitudeKernel α)| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
          (144 ^ (α / 2) * (bandCount N : ℝ) ^ (-α)) := hraw
    _ ≤ 512 * (latitudeBandScale N j : ℝ) *
        (144 ^ (α / 2) * (bandCount N : ℝ) ^ (-α)) := by
      gcongr
    _ ≤ 32768 * 144 ^ (α / 2) *
        (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α) *
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
      have hnonneg :
          0 ≤ 512 * (latitudeBandScale N j : ℝ) *
            (144 ^ (α / 2) * (bandCount N : ℝ) ^ (-α)) := by positivity
      nlinarith

theorem polar_comparable_nonsame_geometry
    {N : ℕ} (hN : 0 < N) (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hp : PolarLatitudePair N j k)
    (hc : ComparableLatitudeScales N j k)
    (hnotsame : ¬ SameLatitudeHemisphere N j k) :
    OppositeLatitudeHemispheres N j k ∧
      LatitudeEvenPowerSeriesBaseGeometry N j k ((1 : ℝ) / 4) := by
  obtain ⟨hj4, hk4⟩ := polar_comparable_scales_le_four hp hc
  have hjNot : ¬ IsCentralLatitudeBand N j := by
    intro hj
    have hjM := latitudeBandScale_eq_central (by omega) hj
    omega
  have hkNot : ¬ IsCentralLatitudeBand N k := by
    intro hk
    have hkM := latitudeBandScale_eq_central (by omega) hk
    omega
  have hopp : OppositeLatitudeHemispheres N j k := by
    rcases same_or_opposite_of_noncentral hjNot hkNot with hs | ho
    · exact (hnotsame hs).elim
    · exact ho
  refine ⟨hopp, {
    base_pos := by norm_num
    base_le := ?_
    ratio_le := ?_ }⟩
  · intro s hs t ht
    have hsI : s ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
        hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
    have htI : t ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
        ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
    have hgap := opposite_band_rectangle_height_gap_of_half_depth
      hN (by omega) j k hopp (Or.inl (by omega)) hs ht
    exact quarter_le_angularKernelA_of_half_height_gap hsI htI hgap
  · intro s hs t ht
    have hsI : s ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
        hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
    have htI : t ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
        ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
    have hgap := opposite_band_rectangle_height_gap_of_half_depth
      hN (by omega) j k hopp (Or.inl (by omega)) hs ht
    exact unequalAngularRatio_le_fifteen_sixteen_of_height_gap hsI htI hgap

theorem one_add_band_dist_le_two_bandCount
    {N : ℕ} (hM : 1 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1)) :
    1 + Nat.dist (j : ℕ) (k : ℕ) ≤ 2 * bandCount N := by
  have hj : (j : ℕ) ≤ bandTailCount N := by omega
  have hk : (k : ℕ) ≤ bandTailCount N := by omega
  have hd : Nat.dist (j : ℕ) (k : ℕ) ≤ bandTailCount N := by
    by_cases hjk : (j : ℕ) ≤ (k : ℕ)
    · rw [Nat.dist_eq_sub_of_le hjk]
      omega
    · rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (by omega : (k : ℕ) ≤ (j : ℕ))]
      omega
  simp [bandTailCount] at hd ⊢
  omega

theorem polar_comparable_nonsame_bound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 15 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hp : PolarLatitudePair N j k)
    (hc : ComparableLatitudeScales N j k)
    (hnotsame : ¬ SameLatitudeHemisphere N j k) :
    |bandPairError N j k (latitudeKernel α)| ≤
      comparableLatitudeBlockMajorant α
        (8388608 * exceptionalLatitudeDssttConstant α) N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  obtain ⟨hopp, hgeo⟩ :=
    polar_comparable_nonsame_geometry hN hM hp hc hnotsame
  let C : ℝ := exceptionalLatitudeDssttConstant α
  have hC : 0 ≤ C := by
    dsimp [C]
    exact exceptionalLatitudeDssttConstant_nonneg α
  have hraw :=
    abs_latitudeKernel_bandPairError_le_of_evenSeriesDsstt
      hα0 hα2 hN (by omega) j k (C := C) hgeo
      hC (fun x hx y hy ↦ by
        have h :=
          abs_latitudeEvenPowerDSSTTSeriesSum_le_series_scale
            hα0 hα2 hN hgeo.swap hy hx
        simpa [C, exceptionalLatitudeDssttConstant] using h)
  obtain ⟨hj4, hk4⟩ := polar_comparable_scales_le_four hp hc
  have hpops :
      finiteBandPopulation N j ≤ 4 * latitudeBandScale N j ∧
        finiteBandPopulation N k ≤ 4 * latitudeBandScale N k := by
    rcases hopp with hNS | hSN
    · exact
        ⟨finiteBandPopulation_le_four_scale_of_northern hNS.1,
          finiteBandPopulation_le_four_scale_of_southern hNS.2⟩
    · exact
        ⟨finiteBandPopulation_le_four_scale_of_southern hSN.1,
          finiteBandPopulation_le_four_scale_of_northern hSN.2⟩
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤
        4 * (latitudeBandScale N j : ℝ) := by exact_mod_cast hpops.1
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤
        4 * (latitudeBandScale N k : ℝ) := by exact_mod_cast hpops.2
  have hMN : 4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  have hden :
      (4 * (bandCount N : ℝ) ^ 2) ^ 4 ≤ (N : ℝ) ^ 4 := by gcongr
  have hcoarse :
      |bandPairError N j k (latitudeKernel α)| ≤
        1048576 * C * (latitudeBandScale N j : ℝ) /
          (bandCount N : ℝ) ^ 8 := by
    calc
      |bandPairError N j k (latitudeKernel α)| ≤
          64 * C * (finiteBandPopulation N j : ℝ) ^ 3 *
            (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := hraw
      _ ≤ (64 * C * (4 * (latitudeBandScale N j : ℝ)) ^ 3 *
            (4 * (latitudeBandScale N k : ℝ)) ^ 3) / (N : ℝ) ^ 4 := by
        gcongr
      _ ≤ (64 * C * (4 * (latitudeBandScale N j : ℝ)) ^ 3 *
            (4 * (latitudeBandScale N k : ℝ)) ^ 3) /
            (4 * (bandCount N : ℝ) ^ 2) ^ 4 := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 1024 * C * (latitudeBandScale N j : ℝ) ^ 3 *
          (latitudeBandScale N k : ℝ) ^ 3 /
          (bandCount N : ℝ) ^ 8 := by
        have hMpos : (0 : ℝ) < bandCount N := by positivity
        field_simp
        ring
      _ ≤ 1024 * C * (16 * (latitudeBandScale N j : ℝ)) *
          64 / (bandCount N : ℝ) ^ 8 := by
        have hjR : (latitudeBandScale N j : ℝ) ≤ 4 := by exact_mod_cast hj4
        have hkR : (latitudeBandScale N k : ℝ) ≤ 4 := by exact_mod_cast hk4
        have hjpos : (0 : ℝ) < latitudeBandScale N j := by
          exact_mod_cast latitudeBandScale_pos N j
        have hj3 :
            (latitudeBandScale N j : ℝ) ^ 3 ≤
              16 * (latitudeBandScale N j : ℝ) := by
          calc
            (latitudeBandScale N j : ℝ) ^ 3 =
                (latitudeBandScale N j : ℝ) *
                  (latitudeBandScale N j : ℝ) ^ 2 := by ring
            _ ≤ (latitudeBandScale N j : ℝ) * 4 ^ 2 := by gcongr
            _ = 16 * (latitudeBandScale N j : ℝ) := by ring
        have hk3 : (latitudeBandScale N k : ℝ) ^ 3 ≤ 64 := by
          calc
            (latitudeBandScale N k : ℝ) ^ 3 ≤ (4 : ℝ) ^ 3 := by gcongr
            _ = 64 := by norm_num
        gcongr
      _ = 1048576 * C * (latitudeBandScale N j : ℝ) /
          (bandCount N : ℝ) ^ 8 := by ring
  let M : ℝ := bandCount N
  let D : ℝ := 1 + Nat.dist (j : ℕ) (k : ℕ)
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by dsimp [M]; exact_mod_cast (by omega : 1 ≤ bandCount N)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hDupper : D ≤ 2 * M := by
    dsimp [D, M]
    exact_mod_cast one_add_band_dist_le_two_bandCount (by omega) j k
  have he : α - 3 ≤ 0 := by linarith
  have hbasePow :
      (2 * M) ^ (α - 3) ≤ D ^ (α - 3) :=
    Real.rpow_le_rpow_of_nonpos hDpos hDupper he
  have htwo :
      (1 : ℝ) / 8 ≤ 2 ^ (α - 3) := by
    have := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by linarith : (-3 : ℝ) ≤ α - 3)
    norm_num at this ⊢
    exact this
  have hweight :
      (1 / 8) * M ^ (α - 3) ≤ D ^ (α - 3) := by
    calc
      (1 / 8) * M ^ (α - 3) ≤
          2 ^ (α - 3) * M ^ (α - 3) := by gcongr
      _ = (2 * M) ^ (α - 3) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hMpos.le]
      _ ≤ D ^ (α - 3) := hbasePow
  have hMpow :
      M ^ (-8 : ℝ) ≤ M ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)
  have hcombine :
      M ^ (-α) * M ^ (α - 3) = M ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hMpos]
    congr 1
    ring
  unfold comparableLatitudeBlockMajorant
  have hcoarse' :
      |bandPairError N j k (latitudeKernel α)| ≤
        1048576 * C * (latitudeBandScale N j : ℝ) *
          M ^ (-8 : ℝ) := by
    rw [show M ^ (8 : ℕ) = M ^ (8 : ℝ) by
        exact (Real.rpow_natCast M 8).symm,
      div_eq_mul_inv, ← Real.rpow_neg hMpos.le] at hcoarse
    simpa [M, mul_assoc] using hcoarse
  calc
    |bandPairError N j k (latitudeKernel α)| ≤
        1048576 * C * (latitudeBandScale N j : ℝ) *
          M ^ (-8 : ℝ) := hcoarse'
    _ ≤ 1048576 * C * (latitudeBandScale N j : ℝ) *
          M ^ (-3 : ℝ) := by gcongr
    _ = 8388608 * C * (latitudeBandScale N j : ℝ) *
          (M ^ (-α) * ((1 / 8) * M ^ (α - 3))) := by
      rw [show M ^ (-3 : ℝ) =
        M ^ (-α) * M ^ (α - 3) by exact hcombine.symm]
      ring
    _ ≤ 8388608 * C * (latitudeBandScale N j : ℝ) *
          (M ^ (-α) * D ^ (α - 3)) := by gcongr
    _ = 8388608 * exceptionalLatitudeDssttConstant α *
        (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α) *
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
      dsimp [C, M, D]
      ring

/-- Premise-free polar field for the broad comparable-scale assembly. -/
theorem polar_comparable_bound_series
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 15 ≤ bandCount N) :
    ∀ j k, PolarLatitudePair N j k →
      ComparableLatitudeScales N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α
          (32768 * 144 ^ (α / 2) +
            8388608 * exceptionalLatitudeDssttConstant α) N j k := by
  intro j k hp hc
  by_cases hsame : SameLatitudeHemisphere N j k
  · exact (polar_comparable_same_bound_series
      hα0 hα2 (by omega) j k hp hc hsame).trans
        (comparableLatitudeBlockMajorant_mono (by
          have hE := exceptionalLatitudeDssttConstant_nonneg α
          nlinarith))
  · exact (polar_comparable_nonsame_bound_series
      hα0 hα2 hM j k hp hc hsame).trans
        (comparableLatitudeBlockMajorant_mono (by
          have hpow : 0 ≤ (144 : ℝ) ^ (α / 2) :=
            Real.rpow_nonneg (by norm_num) _
          nlinarith))

end BEMOC
