import BEMOCFormalization.LatitudeCentralGeometry
import BEMOCFormalization.LatitudeMixedTaylorSpecialization
import BEMOCFormalization.LatitudePointwiseAssembly
import BEMOCFormalization.LatitudeRowArithmetic
import BEMOCFormalization.LatitudeUnequalBlocks
import BEMOCFormalization.LatitudeUnequalGeometry

/-!
# Geometry and arithmetic of exceptional unequal latitude pairs

The broad unequal-scale interface is oriented by `2 d_j < d_k`.  In that
orientation a central pair necessarily has its central band in the second
slot, while an opposite-hemisphere pair necessarily has a half-depth band
in the first slot.  These elementary facts isolate the two remaining
off-diagonal analytic estimates:

* a central block of size `C d_j^3 / M^5`;
* a smooth opposite block of size `C d_j^3 d_k^3 / M^8`.

The final two theorems below check that these two estimates have exactly the
unequal-block majorant required by the row arithmetic.
-/

open Set

namespace BEMOC

theorem centralPair_leftSmall_orientation
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hc : CentralLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k) :
    ¬ IsCentralLatitudeBand N j ∧
      IsCentralLatitudeBand N k ∧
      latitudeBandScale N k = bandCount N ∧
      2 * latitudeBandScale N j < bandCount N := by
  have hkUpper := latitudeBandScale_le_bandCount hM k
  have hjNot : ¬ IsCentralLatitudeBand N j := by
    intro hj
    have hjScale := latitudeBandScale_eq_central hM hj
    omega
  have hk : IsCentralLatitudeBand N k := by
    rcases hc.2 with hj | hk
    · exact (hjNot hj).elim
    · exact hk
  have hkScale := latitudeBandScale_eq_central hM hk
  exact ⟨hjNot, hk, hkScale, by omega⟩

theorem centralPair_leftSmall_has_fixed_height_gap
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hc : CentralLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 : ℝ) / 4 ≤ |s - t| := by
  obtain ⟨hjNot, hk, _hkScale, hjDepth⟩ :=
    centralPair_leftSmall_orientation (by omega) hc hscale
  have hkEq : k = concreteCentralBandIndex N := by
    exact (isCentralLatitudeBand_iff_eq_concreteCentralBandIndex k).mp hk
  subst k
  have hgap := central_band_rectangle_height_gap_of_half_depth
    hM j hjNot (by omega) ht hs
  simpa [abs_sub_comm] using hgap

private theorem three_quarters_le_northern_rectangle_of_two_scale_lt
    {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1))
    (hj : IsNorthernLatitudeBand N j)
    (hscale : 2 * latitudeBandScale N j < bandCount N)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    (3 : ℝ) / 4 ≤ s := by
  let d : ℕ := (j : ℕ) + 1
  have hd : latitudeBandScale N j = d :=
    latitudeBandScale_eq_north hj
  have h2d : 2 * d < bandCount N := by simpa [hd] using hscale
  have hdM : d ≤ bandCount N - 1 := by
    unfold IsNorthernLatitudeBand at hj
    dsimp [d]
    omega
  have hformula := concrete_bandBoundaryHeight_north
    (N := N) (j := d) hdM
  rw [hformula] at hs
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMN : 4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  have h2dR : 2 * (d : ℝ) ≤ bandCount N := by
    exact_mod_cast (show 2 * d ≤ bandCount N by omega)
  have h2d1R : 2 * (d : ℝ) + 1 ≤ bandCount N := by
    exact_mod_cast (show 2 * d + 1 ≤ bandCount N by omega)
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hnum :
      2 * (d : ℝ) * (2 * (d : ℝ) + 1) ≤
        (N : ℝ) / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    nlinarith [mul_le_mul h2dR h2d1R (by positivity)
      (by positivity : (0 : ℝ) ≤ bandCount N)]
  have hfrac :
      2 * (d : ℝ) * (2 * (d : ℝ) + 1) / N ≤
        (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hNr).2
    nlinarith
  linarith [hs.1]

private theorem southern_rectangle_le_neg_three_quarters_of_two_scale_lt
    {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1))
    (hj : IsSouthernLatitudeBand N j)
    (hscale : 2 * latitudeBandScale N j < bandCount N)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    s ≤ -(3 : ℝ) / 4 := by
  have hsr := neg_mem_reflected_band_rectangle_unequal hN j hs
  have hjr := reflect_southern_is_northern hj
  have hscaleR :
      2 * latitudeBandScale N (concreteReflectBandIndex N j) <
        bandCount N := by simpa using hscale
  have hthree :=
    three_quarters_le_northern_rectangle_of_two_scale_lt
      hN (concreteReflectBandIndex N j) hjr hscaleR hsr
  linarith

/-- The strict oriented central scale inequality improves the convenient
quarter-gap estimate to a half-gap.  This puts central separated
rectangles under the same `15/16` angular-ratio constant as the opposite
case. -/
theorem centralPair_leftSmall_has_half_height_gap
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hc : CentralLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 : ℝ) / 2 ≤ |s - t| := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  obtain ⟨hjNot, hk, hkScale, hjDepth⟩ :=
    centralPair_leftSmall_orientation (by omega) hc hscale
  have hkEq : k = concreteCentralBandIndex N :=
    (isCentralLatitudeBand_iff_eq_concreteCentralBandIndex k).mp hk
  have htQuarter : |t| ≤ (1 : ℝ) / 4 := by
    rw [hkEq] at ht
    exact abs_central_band_rectangle_le_quarter hM ht
  rcases latitudeBand_region_trichotomy N j with hjN | hjC | hjS
  · have hsThree :=
      three_quarters_le_northern_rectangle_of_two_scale_lt
        hN j hjN hjDepth hs
    have htUpper : t ≤ (1 : ℝ) / 4 := (abs_le.mp htQuarter).2
    rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]
    linarith
  · exact (hjNot hjC).elim
  · have hsThree :=
      southern_rectangle_le_neg_three_quarters_of_two_scale_lt
        hN j hjS hjDepth hs
    have htLower : -(1 : ℝ) / 4 ≤ t := by
      linarith [(abs_le.mp htQuarter).1]
    rw [abs_of_nonpos (by linarith : s - t ≤ 0)]
    linarith

theorem quarter_le_angularKernelA_of_half_height_gap
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hgap : (1 : ℝ) / 2 ≤ |s - t|) :
    (1 : ℝ) / 4 ≤ angularKernelA s t := by
  have hsrad : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have htrad : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hgapsq : (1 : ℝ) / 4 ≤ (s - t) ^ 2 := by
    nlinarith [sq_nonneg (|s - t| - 1 / 2), sq_abs (s - t)]
  rw [angularKernelA_eq_radiusSq_add]
  linarith

theorem centralPair_leftSmall_series_geometry
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hc : CentralLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 : ℝ) / 4 ≤ angularKernelA s t ∧
      unequalAngularRatio s t ≤ (15 : ℝ) / 16 := by
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
  have hgap :=
    centralPair_leftSmall_has_half_height_gap hM hc hscale hs ht
  exact
    ⟨quarter_le_angularKernelA_of_half_height_gap hsSphere htSphere hgap,
      unequalAngularRatio_le_fifteen_sixteen_of_height_gap
        hsSphere htSphere hgap⟩

theorem smoothOppositePair_leftSmall_has_halfDepth
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (_ho : SmoothOppositeLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k) :
    2 * latitudeBandScale N j ≤ bandCount N := by
  have hkUpper := latitudeBandScale_le_bandCount hM k
  omega

theorem smoothOppositePair_leftSmall_has_fixed_height_gap
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (ho : SmoothOppositeLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 : ℝ) / 2 ≤ |s - t| := by
  apply opposite_band_rectangle_height_gap_of_half_depth
    hN hM j k ho.2.2
  · exact Or.inl
      (smoothOppositePair_leftSmall_has_halfDepth hM ho hscale)
  · exact hs
  · exact ht

theorem smoothOppositePair_leftSmall_series_geometry
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (ho : SmoothOppositeLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 : ℝ) / 4 ≤ angularKernelA s t ∧
      unequalAngularRatio s t ≤ (15 : ℝ) / 16 := by
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hgap :=
    smoothOppositePair_leftSmall_has_fixed_height_gap
      hN hM ho hscale hs ht
  exact
    ⟨quarter_le_angularKernelA_of_half_height_gap hsSphere htSphere hgap,
      unequalAngularRatio_le_fifteen_sixteen_of_height_gap
        hsSphere htSphere hgap⟩

/-- Exact remaining analytic input for the separated opposite-hemisphere
case: a constant mixed derivative bound on every oriented unequal
rectangle. -/
def HasSmoothOppositeLeftSmallDssttBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    SmoothOppositeLatitudePair N j k →
    2 * latitudeBandScale N j < latitudeBandScale N k →
    ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
        |variableReducedLatitudeKernelDsstt α s t| ≤ C

private theorem regular_noncentral_rectangle_interior
    {N : ℕ} (hN : 0 < N)
    {j : Fin (bandTailCount N + 1)}
    (hreg : IsRegularLatitudeBand N j)
    (hnc : ¬ IsCentralLatitudeBand N j)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    s ∈ Ioo (-1 : ℝ) 1 := by
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  rcases latitudeBand_region_trichotomy N j with hjN | hjC | hjS
  · have hb :=
      northern_regular_rectangle_radiusSq_scale_bounds hN j hjN hreg hs
    have hrad : 0 < 1 - s ^ 2 := by
      have hd : (0 : ℝ) < latitudeBandScale N j := by
        exact_mod_cast latitudeBandScale_pos N j
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      exact (by positivity :
        0 < 2 * (latitudeBandScale N j : ℝ) ^ 2 / N).trans_le hb.1
    constructor <;> nlinarith [hsSphere.1, hsSphere.2]
  · exact (hnc hjC).elim
  · let jr := concreteReflectBandIndex N j
    have hjr : IsNorthernLatitudeBand N jr :=
      reflect_southern_is_northern hjS
    have hsr := neg_mem_reflected_band_rectangle_unequal hN j hs
    have hjreg : IsRegularLatitudeBand N jr := by
      simpa [jr] using hreg
    have hb :=
      northern_regular_rectangle_radiusSq_scale_bounds
        hN jr hjr hjreg hsr
    have hrad : 0 < 1 - (-s) ^ 2 := by
      have hd : (0 : ℝ) < latitudeBandScale N jr := by
        exact_mod_cast latitudeBandScale_pos N jr
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      exact (by positivity :
        0 < 2 * (latitudeBandScale N jr : ℝ) ^ 2 / N).trans_le hb.1
    constructor <;> nlinarith [hsSphere.1, hsSphere.2]

theorem smoothOpposite_leftSmall_rectangle_interior_offDiagonal
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (ho : SmoothOppositeLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧ s ≠ t := by
  have hreg := smoothOpposite_pair_regular ho
  have hsI := regular_noncentral_rectangle_interior hN hreg.1
    (fun hj ↦ ho.2.1 (Or.inl hj)) hs
  have htI := regular_noncentral_rectangle_interior hN hreg.2
    (fun hk ↦ ho.2.1 (Or.inr hk)) ht
  have hgap := smoothOppositePair_leftSmall_has_fixed_height_gap
    hN hM ho hscale hs ht
  exact ⟨hsI, htI, fun hst ↦ by subst t; norm_num at hgap⟩

private theorem smoothOpposite_scale_arithmetic
    {C M N dj dk pj pk : ℝ}
    (hC : 0 ≤ C) (hM : 0 < M) (hN : 0 < N)
    (hdj : 0 < dj) (hdk : 0 < dk)
    (hpj : 0 ≤ pj) (hpk : 0 ≤ pk)
    (hpj' : pj ≤ 4 * dj) (hpk' : pk ≤ 4 * dk)
    (hMN : 4 * M ^ 2 ≤ N) :
    64 * C * pj ^ 3 * pk ^ 3 / N ^ 4 ≤
      1024 * C * dj ^ 3 * dk ^ 3 / M ^ 8 := by
  have hpj3 : pj ^ 3 ≤ (4 * dj) ^ 3 := by gcongr
  have hpk3 : pk ^ 3 ≤ (4 * dk) ^ 3 := by gcongr
  have hnum :
      64 * C * pj ^ 3 * pk ^ 3 ≤
        64 * C * (4 * dj) ^ 3 * (4 * dk) ^ 3 := by
    gcongr
  have hden : (4 * M ^ 2) ^ 4 ≤ N ^ 4 := by gcongr
  calc
    64 * C * pj ^ 3 * pk ^ 3 / N ^ 4 ≤
        (64 * C * (4 * dj) ^ 3 * (4 * dk) ^ 3) / N ^ 4 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (64 * C * (4 * dj) ^ 3 * (4 * dk) ^ 3) /
          (4 * M ^ 2) ^ 4 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 1024 * C * dj ^ 3 * dk ^ 3 / M ^ 8 := by
      field_simp
      ring

/-- The mixed-Peano bridge for the smooth opposite unequal case.  After
the geometric reduction above, a uniform DSSTT bound gives the exact
`M⁻⁸` smooth block scale with an explicit loss `1024`. -/
theorem smoothOpposite_leftSmall_block_bound_of_Dsstt
    {α C : ℝ} {N : ℕ} (hM : 1 ≤ bandCount N)
    (hα : 0 < α) (hC : 0 ≤ C)
    (h : HasSmoothOppositeLeftSmallDssttBound α N C) :
    ∀ j k, SmoothOppositeLatitudePair N j k →
      2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        1024 * C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
          (latitudeBandScale N k : ℝ) ^ (3 : ℕ) /
          (bandCount N : ℝ) ^ (8 : ℕ) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hMpos : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMN : 4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  intro j k ho hscale
  have hraw := abs_latitudeKernel_bandPairError_le_of_Dsstt
    hN hα hC j k
    (fun s hs t ht ↦
      smoothOpposite_leftSmall_rectangle_interior_offDiagonal
        hN hM ho hscale hs ht)
    (fun s hs t ht ↦ h j k ho hscale s hs t ht)
  have hpops :
      finiteBandPopulation N j ≤ 4 * latitudeBandScale N j ∧
        finiteBandPopulation N k ≤ 4 * latitudeBandScale N k := by
    rcases ho.2.2 with hNS | hSN
    · exact
        ⟨finiteBandPopulation_le_four_scale_of_northern hNS.1,
          finiteBandPopulation_le_four_scale_of_southern hNS.2⟩
    · exact
        ⟨finiteBandPopulation_le_four_scale_of_southern hSN.1,
          finiteBandPopulation_le_four_scale_of_northern hSN.2⟩
  have harith := smoothOpposite_scale_arithmetic
    (C := C) (M := (bandCount N : ℝ)) (N := (N : ℝ))
    (dj := (latitudeBandScale N j : ℝ))
    (dk := (latitudeBandScale N k : ℝ))
    (pj := (finiteBandPopulation N j : ℝ))
    (pk := (finiteBandPopulation N k : ℝ))
    hC hMpos hNpos
    (by exact_mod_cast latitudeBandScale_pos N j)
    (by exact_mod_cast latitudeBandScale_pos N k)
    (by positivity) (by positivity)
    (by exact_mod_cast hpops.1) (by exact_mod_cast hpops.2) hMN
  exact hraw.trans harith

/-- Uniform off-diagonal derivative input for the central/half-depth
rectangles.  The geometry forces the central band into the second slot. -/
def HasCentralLeftSmallDssttBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    CentralLatitudePair N j k →
    2 * latitudeBandScale N j < latitudeBandScale N k →
    ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
        |variableReducedLatitudeKernelDsstt α s t| ≤ C

theorem central_leftSmall_rectangle_interior_offDiagonal
    {N : ℕ} (hM : 15 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hc : CentralLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧ s ≠ t := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  obtain ⟨hjNot, hk, _hkScale, _hjDepth⟩ :=
    centralPair_leftSmall_orientation (by omega) hc hscale
  have hreg := regular_of_not_polar (fun hp ↦ hc.1 (Or.inl hp))
  have hsI := regular_noncentral_rectangle_interior hN hreg hjNot hs
  have hkEq : k = concreteCentralBandIndex N :=
    (isCentralLatitudeBand_iff_eq_concreteCentralBandIndex k).mp hk
  have htQuarter : |t| ≤ (1 : ℝ) / 4 := by
    rw [hkEq] at ht
    exact abs_central_band_rectangle_le_quarter hM ht
  have htI : t ∈ Ioo (-1 : ℝ) 1 := by
    have htBounds := abs_le.mp htQuarter
    constructor <;> linarith
  have hgap :=
    centralPair_leftSmall_has_fixed_height_gap hM hc hscale hs ht
  exact ⟨hsI, htI, fun hst ↦ by subst t; norm_num at hgap⟩

private theorem centralLeftSmall_scale_arithmetic
    {C M N dj pj pk : ℝ}
    (hC : 0 ≤ C) (hM : 0 < M) (hN : 0 < N)
    (hdj : 0 < dj) (hpj : 0 ≤ pj) (hpk : 0 ≤ pk)
    (hpj' : pj ≤ 4 * dj) (hpk' : pk ≤ 15 * M)
    (hMN : 4 * M ^ 2 ≤ N) :
    64 * C * pj ^ 3 * pk ^ 3 / N ^ 4 ≤
      54000 * C * dj ^ 3 / M ^ 5 := by
  have hpj3 : pj ^ 3 ≤ (4 * dj) ^ 3 := by gcongr
  have hpk3 : pk ^ 3 ≤ (15 * M) ^ 3 := by gcongr
  have hnum :
      64 * C * pj ^ 3 * pk ^ 3 ≤
        64 * C * (4 * dj) ^ 3 * (15 * M) ^ 3 := by
    gcongr
  have hden : (4 * M ^ 2) ^ 4 ≤ N ^ 4 := by gcongr
  calc
    64 * C * pj ^ 3 * pk ^ 3 / N ^ 4 ≤
        (64 * C * (4 * dj) ^ 3 * (15 * M) ^ 3) / N ^ 4 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (64 * C * (4 * dj) ^ 3 * (15 * M) ^ 3) /
          (4 * M ^ 2) ^ 4 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 54000 * C * dj ^ 3 / M ^ 5 := by
      field_simp
      ring

/-- A smooth opposite estimate has the ordered unequal scale once
`d_k ≤ M` is inserted. -/
theorem smoothOpposite_bound_le_unequalMajorant
    {α C : ℝ} (hα2 : α < 2) (hC : 0 ≤ C)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hbound :
      |bandPairError N j k (latitudeKernel α)| ≤
        C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
          (latitudeBandScale N k : ℝ) ^ (3 : ℕ) /
          (bandCount N : ℝ) ^ (8 : ℕ)) :
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
    simpa [d, M] using
      (show (latitudeBandScale N k : ℝ) ≤ bandCount N by
        exact_mod_cast latitudeBandScale_le_bandCount hM k)
  have he : 0 < 8 - α := by linarith
  have hp := Real.rpow_le_rpow hdpos.le hdM he.le
  have hpow :
      d ^ (8 - α) ≤ M ^ (8 - α) := hp
  have hscale :
      d ^ (3 : ℕ) / M ^ (8 : ℕ) ≤
        M ^ (-α) * d ^ (α - 5) := by
    rw [show d ^ (3 : ℕ) = d ^ (3 : ℝ) by
      exact (Real.rpow_natCast d 3).symm]
    rw [show M ^ (8 : ℕ) = M ^ (8 : ℝ) by
      exact (Real.rpow_natCast M 8).symm]
    rw [div_eq_mul_inv, ← Real.rpow_neg hMpos.le]
    have hdcombine :
        d ^ (α - 5) * d ^ (8 - α) = d ^ (3 : ℝ) := by
      rw [← Real.rpow_add hdpos]
      congr 1
      ring
    have hMcombine :
        M ^ (-8 : ℝ) * M ^ (8 - α) = M ^ (-α) := by
      rw [← Real.rpow_add hMpos]
      congr 1
      ring
    have hnonneg : 0 ≤ M ^ (-8 : ℝ) * d ^ (α - 5) :=
      mul_nonneg (Real.rpow_nonneg hMpos.le _)
        (Real.rpow_nonneg hdpos.le _)
    calc
      d ^ (3 : ℝ) * M ^ (-8 : ℝ) =
          M ^ (-8 : ℝ) * d ^ (3 : ℝ) := by ring
      _ = M ^ (-8 : ℝ) *
          (d ^ (α - 5) * d ^ (8 - α)) := by rw [hdcombine]
      _ =
          (M ^ (-8 : ℝ) * d ^ (α - 5)) * d ^ (8 - α) := by
        ring
      _ ≤ (M ^ (-8 : ℝ) * d ^ (α - 5)) * M ^ (8 - α) :=
        mul_le_mul_of_nonneg_left hpow hnonneg
      _ = M ^ (-α) * d ^ (α - 5) := by
        rw [show
          (M ^ (-8 : ℝ) * d ^ (α - 5)) * M ^ (8 - α) =
            (M ^ (-8 : ℝ) * M ^ (8 - α)) * d ^ (α - 5) by ring,
          hMcombine]
  unfold unequalLatitudeBlockMajorant
  refine hbound.trans ?_
  have hj0 : 0 ≤ (latitudeBandScale N j : ℝ) ^ (3 : ℕ) := by positivity
  calc
    C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
          (latitudeBandScale N k : ℝ) ^ (3 : ℕ) /
          (bandCount N : ℝ) ^ (8 : ℕ) =
        (C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ)) *
          (d ^ (3 : ℕ) / M ^ (8 : ℕ)) := by
            dsimp [d, M]
            ring
    _ ≤ (C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ)) *
          (M ^ (-α) * d ^ (α - 5)) := by
      gcongr
    _ = C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
          (bandCount N : ℝ) ^ (-α) *
          (latitudeBandScale N k : ℝ) ^ (α - 5) := by
      dsimp [d, M]
      ring

/-- On an oriented central unequal pair, the central scale is exactly `M`;
hence the manuscript's `C d_j^3/M^5` estimate is literally the broad
unequal majorant. -/
theorem central_leftSmall_bound_eq_unequalMajorant
    {α C : ℝ} {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hc : CentralLatitudePair N j k)
    (hscale : 2 * latitudeBandScale N j < latitudeBandScale N k)
    (hbound :
      |bandPairError N j k (latitudeKernel α)| ≤
        C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) /
          (bandCount N : ℝ) ^ (5 : ℕ)) :
    |bandPairError N j k (latitudeKernel α)| ≤
      unequalLatitudeBlockMajorant α C N j k := by
  obtain ⟨_hjNot, _hk, hkScale, _hjDepth⟩ :=
    centralPair_leftSmall_orientation hM hc hscale
  unfold unequalLatitudeBlockMajorant
  rw [hkScale]
  have hMpos : (0 : ℝ) < bandCount N := by positivity
  refine hbound.trans_eq ?_
  rw [show (bandCount N : ℝ) ^ (5 : ℕ) =
      (bandCount N : ℝ) ^ (5 : ℝ) by
    exact (Real.rpow_natCast (bandCount N : ℝ) 5).symm]
  rw [div_eq_mul_inv, ← Real.rpow_neg hMpos.le]
  have hcombine :
      (bandCount N : ℝ) ^ (-α) *
          (bandCount N : ℝ) ^ (α - 5) =
        (bandCount N : ℝ) ^ (-5 : ℝ) := by
    rw [← Real.rpow_add hMpos]
    congr 1
    ring
  calc
    C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
        (bandCount N : ℝ) ^ (-5 : ℝ) =
      C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
        ((bandCount N : ℝ) ^ (-α) *
          (bandCount N : ℝ) ^ (α - 5)) := by rw [hcombine]
    _ = C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
        (bandCount N : ℝ) ^ (-α) *
        (bandCount N : ℝ) ^ (α - 5) := by ring

/-- A uniform mixed derivative bound on oriented smooth-opposite
rectangles supplies their broad unequal-scale field. -/
theorem smoothOpposite_leftSmall_unequal_bound_of_Dsstt
    {α C : ℝ} {N : ℕ} (hM : 1 ≤ bandCount N)
    (hα : 0 < α) (hα2 : α < 2) (hC : 0 ≤ C)
    (h : HasSmoothOppositeLeftSmallDssttBound α N C) :
    ∀ j k, SmoothOppositeLatitudePair N j k →
      2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α (1024 * C) N j k := by
  intro j k ho hscale
  apply smoothOpposite_bound_le_unequalMajorant hα2
    (mul_nonneg (by norm_num) hC) hM
  exact smoothOpposite_leftSmall_block_bound_of_Dsstt
    hM hα hC h j k ho hscale

/-- Central separated rectangles have the manuscript scale
`C d_j^3/M^5`; composing with the preceding exact scale identity gives
their broad unequal majorant. -/
theorem central_leftSmall_unequal_bound_of_Dsstt
    {α C : ℝ} {N : ℕ} (hM : 15 ≤ bandCount N)
    (hα : 0 < α) (hC : 0 ≤ C)
    (h : HasCentralLeftSmallDssttBound α N C) :
    ∀ j k, CentralLatitudePair N j k →
      2 * latitudeBandScale N j < latitudeBandScale N k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α (54000 * C) N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hMpos : (0 : ℝ) < bandCount N := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMN : 4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  intro j k hc hscale
  have hraw := abs_latitudeKernel_bandPairError_le_of_Dsstt
    hN hα hC j k
    (fun s hs t ht ↦
      central_leftSmall_rectangle_interior_offDiagonal
        hM hc hscale hs ht)
    (fun s hs t ht ↦ h j k hc hscale s hs t ht)
  obtain ⟨hjNot, _hk, _hkScale, _hjDepth⟩ :=
    centralPair_leftSmall_orientation (by omega) hc hscale
  have hpj :
      finiteBandPopulation N j ≤ 4 * latitudeBandScale N j := by
    rcases latitudeBand_region_trichotomy N j with hjN | hjC | hjS
    · exact finiteBandPopulation_le_four_scale_of_northern hjN
    · exact (hjNot hjC).elim
    · exact finiteBandPopulation_le_four_scale_of_southern hjS
  have hpk :=
    finiteBandPopulation_le_fifteen_mul_bandCount (by omega) k
  have harith := centralLeftSmall_scale_arithmetic
    (C := C) (M := (bandCount N : ℝ)) (N := (N : ℝ))
    (dj := (latitudeBandScale N j : ℝ))
    (pj := (finiteBandPopulation N j : ℝ))
    (pk := (finiteBandPopulation N k : ℝ))
    hC hMpos hNpos
    (by exact_mod_cast latitudeBandScale_pos N j)
    (by positivity) (by positivity)
    (by exact_mod_cast hpj) (by exact_mod_cast hpk) hMN
  apply central_leftSmall_bound_eq_unequalMajorant
    (α := α) (C := 54000 * C) (by omega) hc hscale
  exact hraw.trans harith

end BEMOC
