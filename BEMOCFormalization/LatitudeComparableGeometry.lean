import BEMOCFormalization.LatitudeComparableBlocks

/-!
# Geometry of comparable nonpolar latitude rectangles

This file records the concrete geometric estimates used when the mixed
derivative bounds for the reduced latitude kernel are specialized to BEMOC
bands.  The constants are intentionally loose.  Their useful feature is
that they are uniform in `N` and expressed in the manuscript depth
`latitudeBandScale`.
-/

open Set

namespace BEMOC

/-- Every northern noncentral band lies in the closed northern hemisphere. -/
theorem northern_band_rectangle_nonnegative
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j : Fin (bandTailCount N + 1)}
    (hj : IsNorthernLatitudeBand N j)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    0 ≤ s := by
  have hj1 : (j : ℕ) + 1 ≤ bandCount N - 1 := by
    unfold IsNorthernLatitudeBand at hj
    omega
  have hformula := concrete_bandBoundaryHeight_north
    (N := N) (j := (j : ℕ) + 1) hj1
  have hNMnat := four_mul_bandCount_sq_le N
  have hcast :
      4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast hNMnat
  have hjM : ((j : ℕ) + 1 : ℝ) ≤ (bandCount N : ℝ) - 1 := by
    exact_mod_cast hj1
  have hNpos : (0 : ℝ) < N := by
    have hMp : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    nlinarith
  rw [hformula] at hs
  have hquad :
      2 * (((j : ℕ) + 1 : ℝ)) *
          (2 * (((j : ℕ) + 1 : ℝ)) + 1) ≤
        4 * (bandCount N : ℝ) ^ 2 := by
    nlinarith
  have :
      0 ≤ 1 -
        2 * (((j : ℕ) + 1 : ℝ)) *
          (2 * (((j : ℕ) + 1 : ℝ)) + 1) / (N : ℝ) := by
    rw [sub_nonneg]
    apply (div_le_iff₀ hNpos).2
    nlinarith [hquad.trans hcast]
  norm_num [Nat.cast_add, Nat.cast_one] at hs
  linarith [this, hs.1]

/-- On a regular northern band, the sphere radius has a uniform lower
bound proportional to the band depth divided by `M`. -/
theorem northern_band_heightRadius_floor
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j : Fin (bandTailCount N + 1)}
    (hjNorth : IsNorthernLatitudeBand N j)
    (hjRegular : IsRegularLatitudeBand N j)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    (latitudeBandScale N j : ℝ) /
        (5 * (bandCount N : ℝ)) ≤ heightRadius s := by
  have hN : 0 < N := by
    have hMN := four_mul_bandCount_sq_le N
    have hMp : 0 < bandCount N := by omega
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 := by
    have hlo := bandBoundaryHeight_mem hN (j + 1)
    have hhi := bandBoundaryHeight_mem hN j
    exact ⟨hlo.1.trans hs.1, hs.2.trans hhi.2⟩
  have hs0 := northern_band_rectangle_nonnegative hM hjNorth hs
  have hjIndex : latitudeBandScale N j = (j : ℕ) + 1 :=
    latitudeBandScale_eq_north hjNorth
  have hjTop : (j : ℕ) ≤ bandCount N - 1 := by
    unfold IsNorthernLatitudeBand at hjNorth
    omega
  have htop := concrete_bandBoundaryHeight_north
    (N := N) (j := (j : ℕ)) hjTop
  have hNhiNat := bemoc_N_le_twenty_bandCount_sq hM
  have hNhi :
      (N : ℝ) ≤ 20 * (bandCount N : ℝ) ^ 2 := by
    exact_mod_cast hNhiNat
  have hMpos : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hj3Nat : 3 ≤ (j : ℕ) + 1 := by
    unfold IsRegularLatitudeBand at hjRegular
    rw [hjIndex] at hjRegular
    omega
  have hj3 : (3 : ℝ) ≤ ((j : ℕ) + 1 : ℕ) := by
    exact_mod_cast hj3Nat
  have hgap :
      (((j : ℕ) + 1 : ℕ) : ℝ) ^ 2 /
          (25 * (bandCount N : ℝ) ^ 2) ≤ 1 - s := by
    have hstop : s ≤
        1 - 2 * (j : ℝ) * (2 * (j : ℝ) + 1) / (N : ℝ) := by
      simpa [htop] using hs.2
    have hpoly :
        20 * (((j : ℕ) + 1 : ℕ) : ℝ) ^ 2 ≤
          25 * (2 * (j : ℝ) * (2 * (j : ℝ) + 1)) := by
      norm_num [Nat.cast_add, Nat.cast_one] at hj3 ⊢
      nlinarith
    have hcross :
        (N : ℝ) * (((j : ℕ) + 1 : ℕ) : ℝ) ^ 2 ≤
          (25 * (bandCount N : ℝ) ^ 2) *
            (2 * (j : ℝ) * (2 * (j : ℝ) + 1)) := by
      nlinarith [mul_le_mul_of_nonneg_right hNhi
        (sq_nonneg (((j : ℕ) + 1 : ℕ) : ℝ))]
    have hgapN :
        2 * (j : ℝ) * (2 * (j : ℝ) + 1) / (N : ℝ) ≤
          1 - s := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hgapN
      (show 0 ≤ 25 * (bandCount N : ℝ) ^ 2 by positivity)
    have hx :
        (((j : ℕ) + 1 : ℕ) : ℝ) ^ 2 ≤
          (25 * (bandCount N : ℝ) ^ 2) *
            (2 * (j : ℝ) * (2 * (j : ℝ) + 1) / (N : ℝ)) := by
      calc
        (((j : ℕ) + 1 : ℕ) : ℝ) ^ 2 ≤
            ((25 * (bandCount N : ℝ) ^ 2) *
              (2 * (j : ℝ) * (2 * (j : ℝ) + 1))) / (N : ℝ) := by
                apply (le_div_iff₀ hNpos).2
                nlinarith [hcross]
        _ = _ := by ring
    apply (div_le_iff₀ (by positivity :
      0 < 25 * (bandCount N : ℝ) ^ 2)).2
    nlinarith [hx, hmul]
  have hrsq := heightRadius_sq hsSphere
  have hsq :
      (((latitudeBandScale N j : ℝ) /
          (5 * (bandCount N : ℝ))) ^ 2) ≤ heightRadius s ^ 2 := by
    rw [hjIndex]
    have hplus : 1 ≤ 1 + s := by linarith
    rw [hrsq]
    have hfactor : 1 - s ^ 2 = (1 - s) * (1 + s) := by ring
    rw [hfactor]
    calc
      ((((j : ℕ) + 1 : ℕ) : ℝ) /
          (5 * (bandCount N : ℝ))) ^ 2 =
          (((j : ℕ) + 1 : ℕ) : ℝ) ^ 2 /
            (25 * (bandCount N : ℝ) ^ 2) := by
              field_simp
              <;> ring
      _ ≤ 1 - s := hgap
      _ ≤ (1 - s) * (1 + s) := by
        nlinarith [sub_nonneg.mpr hsSphere.2]
  have hleft :
      0 ≤ (latitudeBandScale N j : ℝ) /
        (5 * (bandCount N : ℝ)) := by positivity
  have hright : 0 ≤ heightRadius s := by
    unfold heightRadius
    positivity
  nlinarith [sq_nonneg
    (heightRadius s -
      (latitudeBandScale N j : ℝ) / (5 * (bandCount N : ℝ)))]

/-- Exact lower separation of two ordered northern rectangles.  The loss of
one index is unavoidable because consecutive closed rectangles share their
boundary. -/
theorem northern_band_rectangle_separation
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hj : IsNorthernLatitudeBand N j)
    (hk : IsNorthernLatitudeBand N k)
    (hjk : (j : ℕ) + 1 < (k : ℕ))
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (latitudeBandScale N j : ℝ) *
        (((k : ℕ) - (j : ℕ) - 1 : ℕ) : ℝ) /
          (5 * (bandCount N : ℝ) ^ 2) ≤ s - t := by
  have hj1 : (j : ℕ) + 1 ≤ bandCount N - 1 := by
    unfold IsNorthernLatitudeBand at hj
    omega
  have hk0 : (k : ℕ) ≤ bandCount N - 1 := by
    unfold IsNorthernLatitudeBand at hk
    omega
  have hbj := concrete_bandBoundaryHeight_north
    (N := N) (j := (j : ℕ) + 1) hj1
  have hbk := concrete_bandBoundaryHeight_north
    (N := N) (j := (k : ℕ)) hk0
  have hNhiNat := bemoc_N_le_twenty_bandCount_sq hM
  have hNhi :
      (N : ℝ) ≤ 20 * (bandCount N : ℝ) ^ 2 := by
    exact_mod_cast hNhiNat
  have hMpos : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hNpos : (0 : ℝ) < N := by
    have hNM := four_mul_bandCount_sq_le N
    have hMp : 0 < bandCount N := by omega
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    have hNnat : 0 < N := this.trans_le hNM
    exact_mod_cast hNnat
  have hst :
      bandBoundaryHeight N (j + 1) -
          bandBoundaryHeight N k ≤ s - t := by
    linarith [hs.1, ht.2]
  have hscalej := latitudeBandScale_eq_north hj
  rw [hbj, hbk] at hst
  rw [hscalej]
  have hfactor :
      2 * (k : ℝ) * (2 * (k : ℝ) + 1) -
          2 * (((j : ℕ) + 1 : ℕ) : ℝ) *
            (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) =
        2 * (((k : ℕ) - (j : ℕ) - 1 : ℕ) : ℝ) *
          (2 * ((k : ℝ) + (((j : ℕ) + 1 : ℕ) : ℝ)) + 1) := by
    have hsub :
        (((k : ℕ) - (j : ℕ) - 1 : ℕ) : ℝ) =
          (k : ℝ) - (j : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ (k : ℕ) - (j : ℕ)),
        Nat.cast_sub (by omega : (j : ℕ) ≤ (k : ℕ))]
      norm_num
    rw [hsub]
    push_cast
    ring
  have hpoly :
      4 * ((((j : ℕ) + 1 : ℕ) : ℝ) *
          (((k : ℕ) - (j : ℕ) - 1 : ℕ) : ℝ)) ≤
        2 * (k : ℝ) * (2 * (k : ℝ) + 1) -
          2 * (((j : ℕ) + 1 : ℕ) : ℝ) *
            (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) := by
    rw [hfactor]
    have : 0 ≤ (((k : ℕ) - (j : ℕ) - 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hcross :
      (N : ℝ) *
          ((((j : ℕ) + 1 : ℕ) : ℝ) *
            (((k : ℕ) - (j : ℕ) - 1 : ℕ) : ℝ)) ≤
        (5 * (bandCount N : ℝ) ^ 2) *
          (2 * (k : ℝ) * (2 * (k : ℝ) + 1) -
            2 * (((j : ℕ) + 1 : ℕ) : ℝ) *
              (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1)) := by
    have hnon :
        0 ≤ (((j : ℕ) + 1 : ℕ) : ℝ) *
          (((k : ℕ) - (j : ℕ) - 1 : ℕ) : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hNhi hnon]
  have hgeom :
      (((j : ℕ) + 1 : ℕ) : ℝ) *
          (((k : ℕ) - (j : ℕ) - 1 : ℕ) : ℝ) /
            (5 * (bandCount N : ℝ) ^ 2) ≤
        (2 * (k : ℝ) * (2 * (k : ℝ) + 1) -
          2 * (((j : ℕ) + 1 : ℕ) : ℝ) *
            (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1)) / (N : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hNpos).2
    convert hcross using 1 <;> ring
  exact hgeom.trans (by
    convert hst using 1 <;> ring)

/-- Symmetric distance form of the preceding estimate.  For rectangles
separated by at least one intervening band, index distance controls physical
height separation at scale `d_j/M²`. -/
theorem northern_band_rectangle_dist_separation
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hj : IsNorthernLatitudeBand N j)
    (hk : IsNorthernLatitudeBand N k)
    (hsep : 2 ≤ Nat.dist (j : ℕ) (k : ℕ))
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (min (latitudeBandScale N j) (latitudeBandScale N k) : ℝ) *
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
          (15 * (bandCount N : ℝ) ^ 2) ≤ |s - t| := by
  rcases Nat.le_total (j : ℕ) (k : ℕ) with hjk | hkj
  · have hjk' : (j : ℕ) + 1 < (k : ℕ) := by
      rw [Nat.dist_eq_sub_of_le hjk] at hsep
      omega
    have hraw := northern_band_rectangle_separation hM hj hk hjk' hs ht
    have hmin :
        min (latitudeBandScale N j) (latitudeBandScale N k) =
          latitudeBandScale N j := by
      rw [latitudeBandScale_eq_north hj, latitudeBandScale_eq_north hk,
        Nat.min_eq_left]
      omega
    have hdist :
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) / 3 ≤
          (((k : ℕ) - (j : ℕ) - 1 : ℕ) : ℝ) := by
      have hdistNat :
          1 + Nat.dist (j : ℕ) (k : ℕ) ≤
            3 * ((k : ℕ) - (j : ℕ) - 1) := by
        rw [Nat.dist_eq_sub_of_le hjk]
        omega
      have hdistR :
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ≤
          3 * (((k : ℕ) - (j : ℕ) - 1 : ℕ) : ℝ) := by
        exact_mod_cast hdistNat
      linarith [hdistR]
    have hminR :
        min (latitudeBandScale N j : ℝ) (latitudeBandScale N k : ℝ) =
          (latitudeBandScale N j : ℝ) := by
      exact_mod_cast hmin
    rw [hminR]
    have hMpos : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hjpos : 0 ≤ (latitudeBandScale N j : ℝ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hdist hjpos
    have hden := div_le_div_of_nonneg_right hscaled
      (show 0 ≤ 5 * (bandCount N : ℝ) ^ 2 by positivity)
    have hrawLeft :
        0 ≤ (latitudeBandScale N j : ℝ) *
          (((k : ℕ) - (j : ℕ) - 1 : ℕ) : ℝ) /
            (5 * (bandCount N : ℝ) ^ 2) := by positivity
    rw [abs_of_nonneg (by linarith [hraw, hrawLeft])]
    convert hden.trans hraw using 1 <;> ring
  · have hkj' : (k : ℕ) + 1 < (j : ℕ) := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj] at hsep
      omega
    have hraw := northern_band_rectangle_separation hM hk hj hkj' ht hs
    have hmin :
        min (latitudeBandScale N j) (latitudeBandScale N k) =
          latitudeBandScale N k := by
      rw [latitudeBandScale_eq_north hj, latitudeBandScale_eq_north hk,
        Nat.min_eq_right]
      omega
    have hdist :
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) / 3 ≤
          (((j : ℕ) - (k : ℕ) - 1 : ℕ) : ℝ) := by
      have hdistNat :
          1 + Nat.dist (j : ℕ) (k : ℕ) ≤
            3 * ((j : ℕ) - (k : ℕ) - 1) := by
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj]
        omega
      have hdistR :
          (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ≤
            3 * (((j : ℕ) - (k : ℕ) - 1 : ℕ) : ℝ) := by
        exact_mod_cast hdistNat
      linarith
    have hminR :
        min (latitudeBandScale N j : ℝ) (latitudeBandScale N k : ℝ) =
          (latitudeBandScale N k : ℝ) := by
      exact_mod_cast hmin
    rw [hminR]
    have hMpos : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hkpos : 0 ≤ (latitudeBandScale N k : ℝ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hdist hkpos
    have hden := div_le_div_of_nonneg_right hscaled
      (show 0 ≤ 5 * (bandCount N : ℝ) ^ 2 by positivity)
    have hrawLeft :
        0 ≤ (latitudeBandScale N k : ℝ) *
          (((j : ℕ) - (k : ℕ) - 1 : ℕ) : ℝ) /
            (5 * (bandCount N : ℝ) ^ 2) := by positivity
    rw [abs_sub_comm,
      abs_of_nonneg (by linarith [hraw, hrawLeft])]
    convert hden.trans hraw using 1 <;> ring

/-- Factor-two comparability turns the two individual radius floors into one
floor expressed using the row scale `d_j`. -/
theorem northern_comparable_common_radius_floor
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hj : IsNorthernLatitudeBand N j)
    (hk : IsNorthernLatitudeBand N k)
    (hregj : IsRegularLatitudeBand N j)
    (hregk : IsRegularLatitudeBand N k)
    (hcomp : ComparableLatitudeScales N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ)) ≤ heightRadius s ∧
      (latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ)) ≤ heightRadius t := by
  have hsFloor := northern_band_heightRadius_floor hM hj hregj hs
  have htFloor := northern_band_heightRadius_floor hM hk hregk ht
  have hMpos : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hcompR :
      (latitudeBandScale N j : ℝ) ≤
        2 * (latitudeBandScale N k : ℝ) := by
    exact_mod_cast hcomp.1
  constructor
  · calc
      (latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ)) ≤
        (latitudeBandScale N j : ℝ) /
          (5 * (bandCount N : ℝ)) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            nlinarith
      _ ≤ heightRadius s := hsFloor
  · calc
      (latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ)) =
        ((latitudeBandScale N j : ℝ) / 2) /
          (5 * (bandCount N : ℝ)) := by ring
      _ ≤ (latitudeBandScale N k : ℝ) /
          (5 * (bandCount N : ℝ)) := by
            apply div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ heightRadius t := htFloor

@[simp] theorem heightRadius_neg (s : ℝ) :
    heightRadius (-s) = heightRadius s := by
  unfold heightRadius
  congr 2
  ring

/-- Negating a height in a southern band places it in the reflected
northern band rectangle. -/
theorem neg_mem_reflected_band_rectangle
    {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1))
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    -s ∈ Icc
      (bandBoundaryHeight N (concreteReflectBandIndex N j + 1))
      (bandBoundaryHeight N (concreteReflectBandIndex N j)) := by
  have hj :
      (j : ℕ) ≤ (symmetricBandPopulations N).length := by
    rw [length_symmetricBandPopulations_eq_tail_succ]
    omega
  have hj1 :
      (j : ℕ) + 1 ≤ (symmetricBandPopulations N).length := by
    rw [length_symmetricBandPopulations_eq_tail_succ]
    exact j.isLt
  have hlo :
      bandBoundaryHeight N ((concreteReflectBandIndex N j : ℕ) + 1) =
        -bandBoundaryHeight N j := by
    rw [show
      (concreteReflectBandIndex N j : ℕ) + 1 =
          (symmetricBandPopulations N).length - (j : ℕ) by
      rw [length_symmetricBandPopulations_eq_tail_succ]
      simp only [concreteReflectBandIndex, Fin.val_mk]
      omega]
    exact concrete_bandBoundaryHeight_reflect hN hj
  have hhi :
      bandBoundaryHeight N (concreteReflectBandIndex N j) =
        -bandBoundaryHeight N (j + 1) := by
    rw [show
      ((concreteReflectBandIndex N j :
        Fin (bandTailCount N + 1)) : ℕ) =
          (symmetricBandPopulations N).length - ((j : ℕ) + 1) by
      simp [concreteReflectBandIndex, bandTailCount]]
    exact concrete_bandBoundaryHeight_reflect hN hj1
  rw [hlo, hhi]
  constructor <;> linarith [hs.1, hs.2]

theorem dist_reflected_band_indices (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) :
    Nat.dist (concreteReflectBandIndex N j : ℕ)
        (concreteReflectBandIndex N k : ℕ) =
      Nat.dist (j : ℕ) (k : ℕ) := by
  have hj : (j : ℕ) ≤ bandTailCount N := by omega
  have hk : (k : ℕ) ≤ bandTailCount N := by omega
  rcases Nat.le_total (j : ℕ) (k : ℕ) with hjk | hkj
  · simp only [concreteReflectBandIndex, Fin.val_mk]
    rw [Nat.dist_eq_sub_of_le hjk, Nat.dist_comm,
      Nat.dist_eq_sub_of_le (show
        bandTailCount N - (k : ℕ) ≤
          bandTailCount N - (j : ℕ) by omega)]
    omega
  · simp only [concreteReflectBandIndex, Fin.val_mk]
    rw [Nat.dist_eq_sub_of_le (show
        bandTailCount N - (j : ℕ) ≤
          bandTailCount N - (k : ℕ) by omega),
      Nat.dist_comm, Nat.dist_eq_sub_of_le hkj]
    omega

/-- Uniform common radius floor for every regular same-hemisphere comparable
pair.  This is the denominator floor used in the variable-coefficient
derivative estimates. -/
theorem comparable_sameHemisphere_common_radius_floor
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hsame : SameLatitudeHemisphere N j k)
    (hregj : IsRegularLatitudeBand N j)
    (hregk : IsRegularLatitudeBand N k)
    (hcomp : ComparableLatitudeScales N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ)) ≤ heightRadius s ∧
      (latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ)) ≤ heightRadius t := by
  rcases hsame with hNN | hSS
  · exact northern_comparable_common_radius_floor hM hNN.1 hNN.2
      hregj hregk hcomp hs ht
  · have hN : 0 < N := by
      have hMN := four_mul_bandCount_sq_le N
      have hMp : 0 < bandCount N := by omega
      have hp : 0 < 4 * bandCount N ^ 2 := by positivity
      exact hp.trans_le hMN
    let jr := concreteReflectBandIndex N j
    let kr := concreteReflectBandIndex N k
    have hjr : IsNorthernLatitudeBand N jr :=
      reflect_southern_is_northern hSS.1
    have hkr : IsNorthernLatitudeBand N kr :=
      reflect_southern_is_northern hSS.2
    have hregjr : IsRegularLatitudeBand N jr := by
      simpa [jr] using hregj
    have hregkr : IsRegularLatitudeBand N kr := by
      simpa [kr] using hregk
    have hcompr : ComparableLatitudeScales N jr kr := by
      simpa [jr, kr, ComparableLatitudeScales] using hcomp
    have hsr := neg_mem_reflected_band_rectangle hN j hs
    have htr := neg_mem_reflected_band_rectangle hN k ht
    have hr := northern_comparable_common_radius_floor hM hjr hkr
      hregjr hregkr hcompr hsr htr
    simpa [jr, kr] using hr

/-- Consequently, the angular coefficient `p=2ρ(s)ρ(t)` has the expected
comparable-block lower scale `d_j²/M²`. -/
theorem comparable_sameHemisphere_angularScale_floor
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hsame : SameLatitudeHemisphere N j k)
    (hregj : IsRegularLatitudeBand N j)
    (hregk : IsRegularLatitudeBand N k)
    (hcomp : ComparableLatitudeScales N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (latitudeBandScale N j : ℝ) ^ 2 /
        (50 * (bandCount N : ℝ) ^ 2) ≤
      latitudeAngularScale s t := by
  have hr := comparable_sameHemisphere_common_radius_floor hM
    hsame hregj hregk hcomp hs ht
  have hMpos : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  rw [latitudeAngularScale_eq_heightRadius]
  have hmul := mul_le_mul hr.1 hr.2 (by positivity)
    (show 0 ≤ heightRadius s by unfold heightRadius; positivity)
  calc
    (latitudeBandScale N j : ℝ) ^ 2 /
        (50 * (bandCount N : ℝ) ^ 2) =
      2 * ((latitudeBandScale N j : ℝ) /
        (10 * (bandCount N : ℝ))) *
        ((latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ))) := by
            field_simp
            <;> ring
    _ ≤ 2 * heightRadius s * heightRadius t := by nlinarith

/-- Same-hemisphere version of the physical separation estimate.  Reflection
shows that the identical constant works in the southern hemisphere. -/
theorem sameHemisphere_band_rectangle_dist_separation
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hsame : SameLatitudeHemisphere N j k)
    (hsep : 2 ≤ Nat.dist (j : ℕ) (k : ℕ))
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (min (latitudeBandScale N j) (latitudeBandScale N k) : ℝ) *
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
          (15 * (bandCount N : ℝ) ^ 2) ≤ |s - t| := by
  rcases hsame with hNN | hSS
  · exact northern_band_rectangle_dist_separation hM hNN.1 hNN.2
      hsep hs ht
  · have hN : 0 < N := by
      have hMN := four_mul_bandCount_sq_le N
      have hMp : 0 < bandCount N := by omega
      have hp : 0 < 4 * bandCount N ^ 2 := by positivity
      exact hp.trans_le hMN
    let jr := concreteReflectBandIndex N j
    let kr := concreteReflectBandIndex N k
    have hjr : IsNorthernLatitudeBand N jr :=
      reflect_southern_is_northern hSS.1
    have hkr : IsNorthernLatitudeBand N kr :=
      reflect_southern_is_northern hSS.2
    have hsr := neg_mem_reflected_band_rectangle hN j hs
    have htr := neg_mem_reflected_band_rectangle hN k ht
    have hd :
        Nat.dist (jr : ℕ) (kr : ℕ) =
          Nat.dist (j : ℕ) (k : ℕ) := by
      exact dist_reflected_band_indices N j k
    have hsepR : 2 ≤ Nat.dist (jr : ℕ) (kr : ℕ) := by
      rwa [hd]
    have hr := northern_band_rectangle_dist_separation hM hjr hkr
      hsepR hsr htr
    rw [hd] at hr
    rw [show -s - -t = -(s - t) by ring, abs_neg] at hr
    simpa [jr, kr] using hr

/-- For factor-two comparable scales, the separation bound may be written
entirely in the row scale `d_j`. -/
theorem comparable_sameHemisphere_rowScale_separation
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hsame : SameLatitudeHemisphere N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hsep : 2 ≤ Nat.dist (j : ℕ) (k : ℕ))
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (latitudeBandScale N j : ℝ) *
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
          (30 * (bandCount N : ℝ) ^ 2) ≤ |s - t| := by
  have hraw := sameHemisphere_band_rectangle_dist_separation hM
    hsame hsep hs ht
  have hcompR :
      (latitudeBandScale N j : ℝ) ≤
        2 * (latitudeBandScale N k : ℝ) := by
    exact_mod_cast hcomp.1
  have hmin :
      (latitudeBandScale N j : ℝ) / 2 ≤
        min (latitudeBandScale N j : ℝ)
          (latitudeBandScale N k : ℝ) := by
    rw [le_min_iff]
    constructor
    · have : 0 ≤ (latitudeBandScale N j : ℝ) := by positivity
      linarith
    · linarith
  have hfac :
      0 ≤ (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) := by positivity
  have hMpos : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  calc
    (latitudeBandScale N j : ℝ) *
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
          (30 * (bandCount N : ℝ) ^ 2) =
      ((latitudeBandScale N j : ℝ) / 2) *
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
          (15 * (bandCount N : ℝ) ^ 2) := by ring
    _ ≤ min (latitudeBandScale N j : ℝ)
          (latitudeBandScale N k : ℝ) *
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
          (15 * (bandCount N : ℝ) ^ 2) := by
            gcongr
    _ ≤ |s - t| := hraw

/-- Direct specialization to a classified comparable same-hemisphere pair:
all points of its rectangle obey both the common radius floor and, away from
the diagonal and adjacent bands, the index-distance separation. -/
theorem comparableSame_rectangle_geometry
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : ComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    ((latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ)) ≤ heightRadius s ∧
      (latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ)) ≤ heightRadius t) ∧
    (latitudeBandScale N j : ℝ) ^ 2 /
        (50 * (bandCount N : ℝ) ^ 2) ≤
          latitudeAngularScale s t ∧
    (2 ≤ Nat.dist (j : ℕ) (k : ℕ) →
      (latitudeBandScale N j : ℝ) *
          (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
            (30 * (bandCount N : ℝ) ^ 2) ≤ |s - t|) := by
  have hreg := comparableSame_pair_regular hjk
  refine ⟨?_, ?_, ?_⟩
  · exact comparable_sameHemisphere_common_radius_floor hM
      hjk.2.2.1 hreg.1 hreg.2 hjk.2.2.2 hs ht
  · exact comparable_sameHemisphere_angularScale_floor hM
      hjk.2.2.1 hreg.1 hreg.2 hjk.2.2.2 hs ht
  · intro hsep
    exact comparable_sameHemisphere_rowScale_separation hM
      hjk.2.2.1 hjk.2.2.2 hsep hs ht

end BEMOC
