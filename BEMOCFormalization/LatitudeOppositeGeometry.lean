import BEMOCFormalization.LatitudeUnequalGeometry

/-!
# Opposite-hemisphere angular geometry

The unequal-ring power series only needs a uniform bound strictly below one
for the squared angular ratio.  Same-hemisphere unequal rectangles obtain
this from a radius comparison.  On opposite hemispheres away from the
equator, the vertical gap gives the same conclusion directly.
-/

open Set

namespace BEMOC

/-- The discriminant of the angular normal form is exactly the squared
vertical separation. -/
theorem angularKernelA_sq_sub_angularKernelB_sq
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    angularKernelA s t ^ 2 - angularKernelB s t ^ 2 =
      4 * (s - t) ^ 2 := by
  have hrs : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hrt : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  unfold angularKernelA angularKernelB
  rw [show
      (2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 =
        4 * Real.sqrt (1 - s ^ 2) ^ 2 *
          Real.sqrt (1 - t ^ 2) ^ 2 by ring,
    Real.sq_sqrt hrs, Real.sq_sqrt hrt]
  ring

/-- Any strict bound below one for the endpoint-safe squared ratio supplies
the literal binomial-series hypothesis `|B/A| < 1`. -/
theorem abs_angularKernelB_div_A_lt_one_of_unequalAngularRatio_lt_one
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hQ : unequalAngularRatio s t < 1) :
    |angularKernelB s t / angularKernelA s t| < 1 := by
  have hEq := unequalAngularRatio_eq_sq_div hs ht
  have hzsq :
      |angularKernelB s t / angularKernelA s t| ^ 2 =
        unequalAngularRatio s t := by
    rw [sq_abs, div_pow, hEq]
  have hz0 :
      0 ≤ |angularKernelB s t / angularKernelA s t| := abs_nonneg _
  nlinarith [sq_nonneg
    (|angularKernelB s t / angularKernelA s t| + 1)]

/-- A fixed vertical separation gives the same `15/16` normal-convergence
ratio used on unequal same-hemisphere rectangles. -/
theorem unequalAngularRatio_le_fifteen_sixteen_of_height_gap
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hgap : (1 : ℝ) / 2 ≤ |s - t|) :
    unequalAngularRatio s t ≤ (15 : ℝ) / 16 := by
  have hA0 := angularKernelA_nonneg hs ht
  have hAupper : angularKernelA s t ≤ 4 := by
    unfold angularKernelA
    have hst : -1 ≤ s * t := by
      calc
        -1 ≤ -(|s| * |t|) := by
          have habs : |s| * |t| ≤ 1 := by
            calc
              |s| * |t| ≤ 1 * 1 := by
                exact mul_le_mul (abs_le.mpr hs) (abs_le.mpr ht)
                  (abs_nonneg _) (by norm_num)
              _ = 1 := by norm_num
          linarith
        _ ≤ s * t := by
          rw [← abs_mul]
          exact neg_abs_le (s * t)
    linarith
  have hgapSq : (1 : ℝ) / 4 ≤ (s - t) ^ 2 := by
    have := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (abs_nonneg (s - t))).2 hgap
    rw [sq_abs] at this
    norm_num at this ⊢
    exact this
  have hApos : 0 < angularKernelA s t := by
    have hdisc := angularKernelA_sq_sub_angularKernelB_sq hs ht
    have hBsq : 0 ≤ angularKernelB s t ^ 2 := sq_nonneg _
    nlinarith
  have hdisc := angularKernelA_sq_sub_angularKernelB_sq hs ht
  have hmain :
      16 * angularKernelB s t ^ 2 ≤
        15 * angularKernelA s t ^ 2 := by
    have hAsq : angularKernelA s t ^ 2 ≤ 16 := by nlinarith
    nlinarith
  rw [unequalAngularRatio_eq_sq_div hs ht]
  apply (div_le_iff₀ (sq_pos_of_pos hApos)).2
  nlinarith

/-- The weaker quarter-gap version used for a central band paired with a
half-depth noncentral band. -/
theorem unequalAngularRatio_le_sixty_three_sixty_four_of_height_gap
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hgap : (1 : ℝ) / 4 ≤ |s - t|) :
    unequalAngularRatio s t ≤ (63 : ℝ) / 64 := by
  have hA0 := angularKernelA_nonneg hs ht
  have hAupper : angularKernelA s t ≤ 4 := by
    unfold angularKernelA
    have hst : -1 ≤ s * t := by
      calc
        -1 ≤ -(|s| * |t|) := by
          have habs : |s| * |t| ≤ 1 := by
            calc
              |s| * |t| ≤ 1 * 1 := by
                exact mul_le_mul (abs_le.mpr hs) (abs_le.mpr ht)
                  (abs_nonneg _) (by norm_num)
              _ = 1 := by norm_num
          linarith
        _ ≤ s * t := by
          rw [← abs_mul]
          exact neg_abs_le (s * t)
    linarith
  have hgapSq : (1 : ℝ) / 16 ≤ (s - t) ^ 2 := by
    have h := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (abs_nonneg (s - t))).2 hgap
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hApos : 0 < angularKernelA s t := by
    have hdisc := angularKernelA_sq_sub_angularKernelB_sq hs ht
    have hBsq : 0 ≤ angularKernelB s t ^ 2 := sq_nonneg _
    nlinarith
  have hdisc := angularKernelA_sq_sub_angularKernelB_sq hs ht
  have hmain :
      64 * angularKernelB s t ^ 2 ≤
        63 * angularKernelA s t ^ 2 := by
    have hAsq : angularKernelA s t ^ 2 ≤ 16 := by nlinarith
    nlinarith
  rw [unequalAngularRatio_eq_sq_div hs ht]
  apply (div_le_iff₀ (sq_pos_of_pos hApos)).2
  nlinarith

/-- A northern band whose depth is at most half the latitude count stays
uniformly above the equator. -/
theorem half_le_northern_band_rectangle_of_two_scale_le
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    (j : Fin (bandTailCount N + 1))
    (hj : IsNorthernLatitudeBand N j)
    (hscale : 2 * latitudeBandScale N j ≤ bandCount N)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    (1 : ℝ) / 2 ≤ s := by
  let d : ℕ := (j : ℕ) + 1
  have hd : latitudeBandScale N j = d :=
    latitudeBandScale_eq_north hj
  have h2d : 2 * d ≤ bandCount N := by
    simpa [hd] using hscale
  have hdR : (0 : ℝ) ≤ d := by positivity
  have hMR : (1 : ℝ) ≤ bandCount N := by exact_mod_cast hM
  have h2dR : 2 * (d : ℝ) ≤ bandCount N := by exact_mod_cast h2d
  have hminus :
      0 ≤ (bandCount N : ℝ) - 2 * (d : ℝ) := by linarith
  have hplus :
      0 ≤ (bandCount N : ℝ) + 2 * (d : ℝ) := by positivity
  have hsquare :
      4 * (d : ℝ) ^ 2 ≤ (bandCount N : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hminus hplus]
  have hnum :
      4 * (d : ℝ) * (2 * (d : ℝ) + 1) ≤
        4 * (bandCount N : ℝ) ^ 2 := by
    nlinarith
  have hMN : 4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  have hnumN :
      4 * (d : ℝ) * (2 * (d : ℝ) + 1) ≤ (N : ℝ) :=
    hnum.trans hMN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hfrac :
      2 * (d : ℝ) * (2 * (d : ℝ) + 1) / N ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hNreal).2
    nlinarith
  have hdM : d ≤ bandCount N - 1 := by
    unfold IsNorthernLatitudeBand at hj
    dsimp [d]
    omega
  have hformula := concrete_bandBoundaryHeight_north
    (N := N) (j := d) hdM
  rw [hformula] at hs
  linarith [hs.1]

/-- Every point of a southern noncentral band has nonpositive height. -/
theorem southern_band_rectangle_nonpos
    {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1))
    (hj : IsSouthernLatitudeBand N j)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    s ≤ 0 := by
  have href := neg_mem_reflected_band_rectangle_unequal hN j hs
  have hjr := reflect_southern_is_northern hj
  have hnonneg :=
    northern_band_rectangle_nonneg hN
      (concreteReflectBandIndex N j) hjr href
  linarith

/-- The reflected southern half-depth rectangle stays below `-1/2`. -/
theorem southern_band_rectangle_le_neg_half_of_two_scale_le
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    (j : Fin (bandTailCount N + 1))
    (hj : IsSouthernLatitudeBand N j)
    (hscale : 2 * latitudeBandScale N j ≤ bandCount N)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    s ≤ -(1 : ℝ) / 2 := by
  have href := neg_mem_reflected_band_rectangle_unequal hN j hs
  have hjr := reflect_southern_is_northern hj
  have hscaleR :
      2 * latitudeBandScale N (concreteReflectBandIndex N j) ≤
        bandCount N := by
    simpa using hscale
  have hhalf := half_le_northern_band_rectangle_of_two_scale_le
    hN hM (concreteReflectBandIndex N j) hjr hscaleR href
  linarith

/-- If an opposite-hemisphere pair has at least one half-depth band, every
point of its product rectangle has vertical separation at least `1/2`. -/
theorem opposite_band_rectangle_height_gap_of_half_depth
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hopp : OppositeLatitudeHemispheres N j k)
    (hdepth :
      2 * latitudeBandScale N j ≤ bandCount N ∨
        2 * latitudeBandScale N k ≤ bandCount N)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 : ℝ) / 2 ≤ |s - t| := by
  rcases hopp with hNS | hSN
  · have hs0 := northern_band_rectangle_nonneg hN j hNS.1 hs
    have ht0 := southern_band_rectangle_nonpos hN k hNS.2 ht
    rcases hdepth with hj | hk
    · have hsHalf :=
        half_le_northern_band_rectangle_of_two_scale_le
          hN hM j hNS.1 hj hs
      rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]
      linarith
    · have htHalf :=
        southern_band_rectangle_le_neg_half_of_two_scale_le
          hN hM k hNS.2 hk ht
      rw [abs_of_nonneg (by linarith : 0 ≤ s - t)]
      linarith
  · have ht0 := northern_band_rectangle_nonneg hN k hSN.2 ht
    have hs0 := southern_band_rectangle_nonpos hN j hSN.1 hs
    rcases hdepth with hj | hk
    · have hsHalf :=
        southern_band_rectangle_le_neg_half_of_two_scale_le
          hN hM j hSN.1 hj hs
      rw [abs_of_nonpos (by linarith : s - t ≤ 0)]
      linarith
    · have htHalf :=
        half_le_northern_band_rectangle_of_two_scale_le
          hN hM k hSN.2 hk ht
      rw [abs_of_nonpos (by linarith : s - t ≤ 0)]
      linarith

/-- Hence the endpoint-safe angular series has its standard uniform ratio
on every such opposite-hemisphere rectangle. -/
theorem opposite_band_rectangle_unequalAngularRatio_le
    {N : ℕ} (hN : 0 < N) (hM : 1 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hopp : OppositeLatitudeHemispheres N j k)
    (hdepth :
      2 * latitudeBandScale N j ≤ bandCount N ∨
        2 * latitudeBandScale N k ≤ bandCount N)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    unequalAngularRatio s t ≤ (15 : ℝ) / 16 := by
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 := by
    have hlo := bandBoundaryHeight_mem hN (j + 1)
    have hhi := bandBoundaryHeight_mem hN j
    exact ⟨hlo.1.trans hs.1, hs.2.trans hhi.2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 := by
    have hlo := bandBoundaryHeight_mem hN (k + 1)
    have hhi := bandBoundaryHeight_mem hN k
    exact ⟨hlo.1.trans ht.1, ht.2.trans hhi.2⟩
  exact unequalAngularRatio_le_fifteen_sixteen_of_height_gap
    hsSphere htSphere
      (opposite_band_rectangle_height_gap_of_half_depth
        hN hM j k hopp hdepth hs ht)

end BEMOC
