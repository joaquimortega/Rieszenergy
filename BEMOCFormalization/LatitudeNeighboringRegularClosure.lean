import BEMOCFormalization.LatitudeNeighboringRegularBlocks

/-! Finite-depth closure for neighboring regular latitude rectangles. -/

open MeasureTheory Set

namespace BEMOC

/-- Uniform north-pole coordinate bound for any fixed depth cutoff. -/
theorem northern_rectangle_height_gap_of_scale_le
    {N D : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    (j : Fin (bandTailCount N + 1))
    (hjNorth : IsNorthernLatitudeBand N j)
    (hjD : latitudeBandScale N j ≤ D)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    0 ≤ 1 - s ∧
      1 - s ≤
        ((D : ℝ) * (2 * D + 1)) /
          (2 * (bandCount N : ℝ) ^ 2) := by
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have hjIndex : (j : ℕ) + 1 ≤ D := by
    rw [latitudeBandScale_eq_north hjNorth] at hjD
    exact hjD
  have hjBoundary : (j : ℕ) + 1 ≤ bandCount N - 1 := by
    unfold IsNorthernLatitudeBand at hjNorth
    omega
  have hformula := concrete_bandBoundaryHeight_north
    (N := N) (j := (j : ℕ) + 1) hjBoundary
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hNM : 4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  constructor
  · linarith [hsSphere.2]
  · have hraw :
        1 - s ≤
          2 * (((j : ℕ) + 1 : ℕ) : ℝ) *
            (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) / N := by
      rw [hformula] at hs
      linarith [hs.1]
    have hjR : ((((j : ℕ) + 1 : ℕ) : ℝ)) ≤ D := by
      exact_mod_cast hjIndex
    have hnum :
        2 * ((((j : ℕ) + 1 : ℕ) : ℝ)) *
            (2 * ((((j : ℕ) + 1 : ℕ) : ℝ)) + 1) ≤
          2 * (D : ℝ) * (2 * D + 1) := by
      have hj0 : 0 ≤ ((((j : ℕ) + 1 : ℕ) : ℝ)) := by positivity
      have hD0 : 0 ≤ (D : ℝ) := by positivity
      nlinarith
    calc
      1 - s ≤
          2 * ((((j : ℕ) + 1 : ℕ) : ℝ)) *
            (2 * ((((j : ℕ) + 1 : ℕ) : ℝ)) + 1) / N := hraw
      _ ≤ (2 * (D : ℝ) * (2 * D + 1)) / N := by
        exact div_le_div_of_nonneg_right hnum hNreal.le
      _ ≤ ((D : ℝ) * (2 * D + 1)) /
          (2 * (bandCount N : ℝ) ^ 2) := by
        apply (div_le_div_iff₀ hNreal
          (by positivity : 0 < 2 * (bandCount N : ℝ) ^ 2)).2
        have hcoef : 0 ≤ (D : ℝ) * (2 * D + 1) := by positivity
        nlinarith

/-- Reflection gives the identical fixed-depth estimate at the south pole. -/
theorem southern_rectangle_height_gap_of_scale_le
    {N D : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    (j : Fin (bandTailCount N + 1))
    (hjSouth : IsSouthernLatitudeBand N j)
    (hjD : latitudeBandScale N j ≤ D)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    0 ≤ 1 + s ∧
      1 + s ≤
        ((D : ℝ) * (2 * D + 1)) /
          (2 * (bandCount N : ℝ) ^ 2) := by
  let jr := concreteReflectBandIndex N j
  have hjr : IsNorthernLatitudeBand N jr :=
    reflect_southern_is_northern hjSouth
  have hsr := neg_mem_reflected_band_rectangle hN j hs
  have hjrD : latitudeBandScale N jr ≤ D := by
    simpa [jr] using hjD
  have h := northern_rectangle_height_gap_of_scale_le
    hN hM jr hjr hjrD hsr
  simpa using h

/-- A genuinely premise-free bound for the finite set of regular depths
below the unit-chart threshold. -/
theorem abs_bandPairError_neighboringComparable_smallDepth
    {α : ℝ} (hα : 0 ≤ α)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : NeighboringComparableLatitudePair N j k)
    (hsmall : latitudeBandScale N j < 600) :
    |bandPairError N j k (latitudeKernel α)| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (8 * ((1200 : ℝ) * (2 * 1200 + 1) /
            (2 * (bandCount N : ℝ) ^ 2))) ^ (α / 2) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hjD : latitudeBandScale N j ≤ 1200 := by omega
  have hkD : latitudeBandScale N k ≤ 1200 := by
    have hc := hjk.1.2.2.2.2
    omega
  apply abs_bandPairError_le_of_band_rectangle_bound hN j k _ _
    (Real.rpow_nonneg (by positivity) _)
  intro s hs t ht
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  let A : ℝ := (1200 : ℝ) * (2 * 1200 + 1) /
    (2 * (bandCount N : ℝ) ^ 2)
  rcases hjk.1.2.2.1 with hNN | hSS
  · have hjgap := northern_rectangle_height_gap_of_scale_le
      hN hM j hNN.1 hjD hs
    have hkgap := northern_rectangle_height_gap_of_scale_le
      hN hM k hNN.2 hkD ht
    have hbound :=
      abs_latitudeKernel_le_of_north_gaps
        (A := A) (B := A) hα hsSphere htSphere
        (by positivity) (by positivity)
        (by simpa [A] using hjgap.2)
        (by simpa [A] using hkgap.2)
    convert hbound using 1 <;> dsimp [A] <;> ring
  · have hjgap := southern_rectangle_height_gap_of_scale_le
      hN hM j hSS.1 hjD hs
    have hkgap := southern_rectangle_height_gap_of_scale_le
      hN hM k hSS.2 hkD ht
    have hbound :=
      abs_latitudeKernel_le_of_south_gaps
        (A := A) (B := A) hα hsSphere htSphere
        (by positivity) (by positivity)
        (by simpa [A] using hjgap.2)
        (by simpa [A] using hkgap.2)
    convert hbound using 1 <;> dsimp [A] <;> ring

end BEMOC
