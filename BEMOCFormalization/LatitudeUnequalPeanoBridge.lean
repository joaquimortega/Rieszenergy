import BEMOCFormalization.LatitudeMixedTaylorSpecialization
import BEMOCFormalization.LatitudeUnequalGeometry
import BEMOCFormalization.LatitudeUnequalBlocks
import BEMOCFormalization.LatitudePointwiseAssembly

/-!
# Mixed-Peano bridge for unequal latitude blocks

This file turns a pointwise bound for the already computed mixed derivative
into the final left-small block majorant.  It removes the older abstract
affine-remainder premise from this part of the argument.
-/

open Set

namespace BEMOC

/-- The exact pointwise analytic input at the scale predicted by (5.6). -/
def HasLeftSmallLatitudeDssttBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    LeftSmallSameLatitudePair N j k →
    ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
        |variableReducedLatitudeKernelDsstt α s t| ≤
          C * (bandCount N : ℝ) ^ (8 - α) *
            (latitudeBandScale N k : ℝ) ^ (α - 8)

/-- Regular left-small rectangles lie wholly in the interior height chart
and are separated from the diagonal. -/
theorem leftSmallSame_rectangle_interior_offDiagonal
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : LeftSmallSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧ s ≠ t := by
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hreg := leftSmallSame_pair_regular hjk
  have hsRad : 0 < 1 - s ^ 2 := by
    rcases hjk.2.2.1 with hNN | hSS
    · have hb := northern_regular_rectangle_radiusSq_scale_bounds
        hN j hNN.1 hreg.1 hs
      have hlo :
          0 < 2 * (latitudeBandScale N j : ℝ) ^ 2 / N := by
        have hd : (0 : ℝ) < latitudeBandScale N j := by
          exact_mod_cast latitudeBandScale_pos N j
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        positivity
      exact hlo.trans_le hb.1
    · let jr := concreteReflectBandIndex N j
      have hjr : IsNorthernLatitudeBand N jr :=
        reflect_southern_is_northern hSS.1
      have hsr := neg_mem_reflected_band_rectangle_unequal hN j hs
      have hjreg : IsRegularLatitudeBand N jr := by
        simpa [jr] using hreg.1
      have hb := northern_regular_rectangle_radiusSq_scale_bounds
        hN jr hjr hjreg hsr
      have hlo :
          0 < 2 * (latitudeBandScale N jr : ℝ) ^ 2 / N := by
        have hd : (0 : ℝ) < latitudeBandScale N jr := by
          exact_mod_cast latitudeBandScale_pos N jr
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        positivity
      have : 0 < 1 - (-s) ^ 2 := hlo.trans_le hb.1
      nlinarith
  have htRad : 0 < 1 - t ^ 2 := by
    exact (leftSmallSame_rectangle_largeRadiusSq_bounds
      hN j k hjk ht).1 |>.trans_lt' (by
        have hd : (0 : ℝ) < latitudeBandScale N k := by
          exact_mod_cast latitudeBandScale_pos N k
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        positivity)
  have hsInterior : s ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith [hsSphere.1, hsSphere.2]
  have htInterior : t ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith [htSphere.1, htSphere.2]
  refine ⟨hsInterior, htInterior, ?_⟩
  intro hst
  subst t
  have hratio :=
    leftSmallSame_rectangle_radiusSq_ratio hN j k hjk hs ht
  nlinarith

/-- The pointwise mixed-derivative estimate gives the raw concrete Peano
block bound, before simplifying populations and `N ≍ M²`. -/
theorem leftSmallSame_block_bound_of_Dsstt_raw
    {α C : ℝ} {N : ℕ} (hM : 1 ≤ bandCount N)
    (hα : 0 < α) (hC : 0 ≤ C)
    (h : HasLeftSmallLatitudeDssttBound α N C) :
    ∀ j k, LeftSmallSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        64 * (C * (bandCount N : ℝ) ^ (8 - α) *
          (latitudeBandScale N k : ℝ) ^ (α - 8)) *
          (finiteBandPopulation N j : ℝ) ^ 3 *
          (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  intro j k hjk
  apply abs_latitudeKernel_bandPairError_le_of_Dsstt
    hN hα (by positivity) j k
  · intro s hs t ht
    exact leftSmallSame_rectangle_interior_offDiagonal hN hjk hs ht
  · intro s hs t ht
    exact h j k hjk s hs t ht

/-- Final L6 left-small block estimate, with the same universal numerical
loss `1024` as the existing scale-arithmetic theorem. -/
theorem leftSmallSame_block_bound_of_Dsstt
    {α C : ℝ} {N : ℕ} (hM : 1 ≤ bandCount N)
    (hα : 0 < α) (hC : 0 ≤ C)
    (h : HasLeftSmallLatitudeDssttBound α N C) :
    ∀ j k, LeftSmallSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        unequalLatitudeBlockMajorant α (1024 * C) N j k := by
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
    leftSmallSame_block_bound_of_Dsstt_raw hM hα hC h j k hjk
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
  unfold unequalLatitudeBlockMajorant
  exact hraw.trans (by
    convert hscale using 1)

end BEMOC
