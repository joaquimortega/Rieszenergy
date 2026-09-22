import BEMOCFormalization.LatitudeUnequalSeries
import BEMOCFormalization.LatitudePairClassification

/-!
# Geometry of unequal-scale latitude rectangles

This file supplies the geometric input used by the normally convergent
even-power expansion in (5.6).  On a same-hemisphere rectangle whose left
band has less than half the scale of the right band, the squared radius in
the left band is at most `3/5` of the squared radius in the right band.
Consequently the endpoint-safe angular ratio

`Q = 4 (1-s²) (1-t²) / A(s,t)²`

is at most `15/16`, uniformly even when the smaller radius vanishes.
-/

open Set

namespace BEMOC

/-- The elementary identity relating the angular coefficient to the two
squared radii and the vertical separation. -/
theorem angularKernelA_eq_radiusSq_add
    (s t : ℝ) :
    angularKernelA s t =
      (1 - s ^ 2) + (1 - t ^ 2) + (s - t) ^ 2 := by
  unfold angularKernelA
  ring

/-- On one closed hemisphere, `A` is controlled by the sum of the two
squared radii. -/
theorem angularKernelA_le_two_mul_radiusSq_add
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hsame : (0 ≤ s ∧ 0 ≤ t) ∨ (s ≤ 0 ∧ t ≤ 0)) :
    angularKernelA s t ≤
      2 * ((1 - s ^ 2) + (1 - t ^ 2)) := by
  rcases hsame with hpos | hneg
  · have hsGap : 0 ≤ 1 - s := by linarith [hs.2]
    have htGap : 0 ≤ 1 - t := by linarith [ht.2]
    have hts : t * (1 - s) ≤ 1 - s :=
      mul_le_of_le_one_left hsGap ht.2
    have hsRad : 1 - s ≤ 1 - s ^ 2 := by
      nlinarith [mul_nonneg hsGap hpos.1]
    have htRad : 1 - t ≤ 1 - t ^ 2 := by
      nlinarith [mul_nonneg htGap hpos.2]
    unfold angularKernelA
    nlinarith
  · have hns : -s ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2]
    have hnt : -t ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hsGap : 0 ≤ 1 + s := by linarith [hs.1]
    have htGap : 0 ≤ 1 + t := by linarith [ht.1]
    have hts : (-t) * (1 + s) ≤ 1 + s :=
      mul_le_of_le_one_left hsGap (by linarith [ht.1])
    have hsRad : 1 + s ≤ 1 - s ^ 2 := by
      nlinarith [mul_nonneg hsGap (by linarith : 0 ≤ 1 - s)]
    have htRad : 1 + t ≤ 1 - t ^ 2 := by
      nlinarith [mul_nonneg htGap (by linarith : 0 ≤ 1 - t)]
    unfold angularKernelA
    nlinarith

/-- A radius-ratio bound of `3/5` forces the uniform angular-series ratio
`Q ≤ 15/16`.  No positivity of the smaller squared radius is required. -/
theorem unequalAngularRatio_le_fifteen_sixteen_of_radiusSq
    {s t : ℝ}
    (hu : 0 ≤ 1 - s ^ 2) (hv : 0 < 1 - t ^ 2)
    (hratio : 5 * (1 - s ^ 2) ≤ 3 * (1 - t ^ 2)) :
    unequalAngularRatio s t ≤ (15 : ℝ) / 16 := by
  let u : ℝ := 1 - s ^ 2
  let v : ℝ := 1 - t ^ 2
  let A : ℝ := angularKernelA s t
  have hv0 : 0 ≤ v := hv.le
  have hvpos : 0 < v := by simpa [v] using hv
  have hu0 : 0 ≤ u := by simpa [u] using hu
  have hAuv : u + v ≤ A := by
    dsimp [A, u, v]
    rw [angularKernelA_eq_radiusSq_add]
    nlinarith [sq_nonneg (s - t)]
  have hA : 0 < A := lt_of_lt_of_le (by linarith) hAuv
  have hfactor : 0 ≤ (3 * v - 5 * u) * (5 * v - 3 * u) := by
    have hfirst : 0 ≤ 3 * v - 5 * u := by
      dsimp [u, v] at *
      linarith
    have hsecond : 0 ≤ 5 * v - 3 * u := by
      have huv : u ≤ v := by
        dsimp [u, v] at *
        nlinarith
      nlinarith
    positivity
  have huvSq : 64 * u * v ≤ 15 * (u + v) ^ 2 := by
    nlinarith [hfactor]
  have hA2 : (u + v) ^ 2 ≤ A ^ 2 := by
    nlinarith [show 0 ≤ u + v by positivity]
  have hmain : 64 * u * v ≤ 15 * A ^ 2 :=
    huvSq.trans (mul_le_mul_of_nonneg_left hA2 (by norm_num))
  unfold unequalAngularRatio
  dsimp [u, v, A] at hmain hA
  apply (div_le_iff₀ (sq_pos_of_pos hA)).2
  nlinarith

/-- Every point of a northern noncentral band has nonnegative height. -/
theorem northern_band_rectangle_nonneg
    {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1))
    (hj : IsNorthernLatitudeBand N j)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    0 ≤ s := by
  let d : ℕ := (j : ℕ) + 1
  have hdM : d ≤ bandCount N - 1 := by
    dsimp [d]
    unfold IsNorthernLatitudeBand at hj
    omega
  have hformula := concrete_bandBoundaryHeight_north
    (N := N) (j := d) hdM
  have hMNnat := four_mul_bandCount_sq_le N
  have hnumNat :
      2 * d * (2 * d + 1) ≤ 4 * bandCount N ^ 2 := by
    have hdSucc : d + 1 ≤ bandCount N := by omega
    have hdR : (d : ℝ) + 1 ≤ (bandCount N : ℝ) := by
      exact_mod_cast hdSucc
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hMR : (1 : ℝ) ≤ bandCount N := by
      exact_mod_cast (show 1 ≤ bandCount N by omega)
    exact_mod_cast (show
      2 * (d : ℝ) * (2 * (d : ℝ) + 1) ≤
        4 * (bandCount N : ℝ) ^ 2 by nlinarith)
  have hnumN : 2 * d * (2 * d + 1) ≤ N :=
    hnumNat.trans hMNnat
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hnumReal :
      2 * (d : ℝ) * (2 * (d : ℝ) + 1) ≤ (N : ℝ) := by
    exact_mod_cast hnumN
  rw [hformula] at hs
  have : 0 ≤ 1 - 2 * (d : ℝ) * (2 * (d : ℝ) + 1) / N := by
    apply sub_nonneg.mpr
    exact (div_le_one hNreal).2 hnumReal
  exact this.trans hs.1

/-- Northern-band squared-radius bounds, uniform on the whole band
rectangle.  The lower bound is used only away from the north-polar band. -/
theorem northern_band_rectangle_radiusSq_bounds
    {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1))
    (hj : IsNorthernLatitudeBand N j)
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    2 * ((j : ℝ)) * (2 * (j : ℝ) + 1) / N ≤ 1 - s ^ 2 ∧
      1 - s ^ 2 ≤
        4 * (((j : ℕ) + 1 : ℕ) : ℝ) *
          (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) / N := by
  have hs0 := northern_band_rectangle_nonneg hN j hj hs
  have hs1 : s ≤ 1 :=
    hs.2.trans (bandBoundaryHeight_mem hN j).2
  have hsj : (j : ℕ) ≤ bandCount N - 1 := by
    unfold IsNorthernLatitudeBand at hj
    omega
  have hsj1 : (j : ℕ) + 1 ≤ bandCount N - 1 := by
    unfold IsNorthernLatitudeBand at hj
    omega
  have hleft := concrete_bandBoundaryHeight_north
    (N := N) (j := (j : ℕ)) hsj
  have hright := concrete_bandBoundaryHeight_north
    (N := N) (j := (j : ℕ) + 1) hsj1
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hleft, hright] at hs
  constructor
  · have hgap :
        2 * (j : ℝ) * (2 * (j : ℝ) + 1) / N ≤ 1 - s := by
      linarith [hs.2]
    have hfac : 1 ≤ 1 + s := by linarith
    calc
      2 * (j : ℝ) * (2 * (j : ℝ) + 1) / N ≤ 1 - s := hgap
      _ ≤ (1 - s) * (1 + s) := by
        exact le_mul_of_one_le_right (by linarith) hfac
      _ = 1 - s ^ 2 := by ring
  · have hgap :
        1 - s ≤
          2 * (((j : ℕ) + 1 : ℕ) : ℝ) *
            (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) / N := by
      linarith [hs.1]
    calc
      1 - s ^ 2 = (1 - s) * (1 + s) := by ring
      _ ≤ (1 - s) * 2 := by
        have hgap0 : 0 ≤ 1 - s := by linarith
        exact mul_le_mul_of_nonneg_left (by linarith) hgap0
      _ ≤
          4 * (((j : ℕ) + 1 : ℕ) : ℝ) *
            (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) / N := by
        calc
          (1 - s) * 2 ≤
              (2 * (((j : ℕ) + 1 : ℕ) : ℝ) *
                (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) / N) * 2 :=
            mul_le_mul_of_nonneg_right hgap (by norm_num)
          _ = _ := by ring

/-- The exact factor-two depth separation implies a `3/5` squared-radius
separation on northern product rectangles. -/
theorem northern_unequal_rectangle_radiusSq_ratio
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (hj : IsNorthernLatitudeBand N j)
    (hk : IsNorthernLatitudeBand N k)
    (hscale : 2 * latitudeBandScale N j <
      latitudeBandScale N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    5 * (1 - s ^ 2) ≤ 3 * (1 - t ^ 2) := by
  have hjScale := latitudeBandScale_eq_north hj
  have hkScale := latitudeBandScale_eq_north hk
  rw [hjScale, hkScale] at hscale
  have hsBound :=
    (northern_band_rectangle_radiusSq_bounds hN j hj hs).2
  have htBound :=
    (northern_band_rectangle_radiusSq_bounds hN k hk ht).1
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hknat : 2 * ((j : ℕ) + 1) ≤ (k : ℕ) := by omega
  have hknatR :
      2 * (((j : ℕ) + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hknat
  have hjR0 :
      (0 : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ) := by positivity
  have hjR1 :
      (1 : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ (j : ℕ) + 1 by omega)
  have hindex :
      5 * (4 * (((j : ℕ) + 1 : ℕ) : ℝ) *
          (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1)) ≤
        3 * (2 * (k : ℝ) * (2 * (k : ℝ) + 1)) := by
    calc
      5 * (4 * (((j : ℕ) + 1 : ℕ) : ℝ) *
          (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1)) ≤
          3 * (2 * (2 * (((j : ℕ) + 1 : ℕ) : ℝ)) *
            (2 * (2 * (((j : ℕ) + 1 : ℕ) : ℝ)) + 1)) := by
        nlinarith
      _ ≤ 3 * (2 * (k : ℝ) * (2 * (k : ℝ) + 1)) := by
        gcongr
  calc
    5 * (1 - s ^ 2) ≤
        5 * (4 * (((j : ℕ) + 1 : ℕ) : ℝ) *
          (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) / N) := by
      gcongr
    _ ≤
        3 * (2 * (k : ℝ) * (2 * (k : ℝ) + 1) / N) := by
      calc
        5 * (4 * (((j : ℕ) + 1 : ℕ) : ℝ) *
            (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1) / N) =
            (5 * (4 * (((j : ℕ) + 1 : ℕ) : ℝ) *
              (2 * (((j : ℕ) + 1 : ℕ) : ℝ) + 1))) / N := by ring
        _ ≤
            (3 * (2 * (k : ℝ) * (2 * (k : ℝ) + 1))) / N :=
          (div_le_div_iff_of_pos_right hNreal).2 hindex
        _ = 3 * (2 * (k : ℝ) * (2 * (k : ℝ) + 1) / N) := by ring
    _ ≤ 3 * (1 - t ^ 2) := by
      gcongr

/-- Reflection carries a southern band rectangle to the corresponding
northern band rectangle. -/
theorem neg_mem_reflected_band_rectangle_unequal
    {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1))
    {s : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    -s ∈ Icc
      (bandBoundaryHeight N (concreteReflectBandIndex N j + 1))
      (bandBoundaryHeight N (concreteReflectBandIndex N j)) := by
  have hj : (j : ℕ) ≤ (symmetricBandPopulations N).length := by
    rw [length_symmetricBandPopulations_eq_tail_succ]
    omega
  have hj1 : (j : ℕ) + 1 ≤
      (symmetricBandPopulations N).length := by
    rw [length_symmetricBandPopulations_eq_tail_succ]
    exact j.isLt
  have hleft := concrete_bandBoundaryHeight_reflect hN hj
  have hright := concrete_bandBoundaryHeight_reflect hN hj1
  have href :
      ((concreteReflectBandIndex N j : Fin (bandTailCount N + 1)) : ℕ) =
        (symmetricBandPopulations N).length - ((j : ℕ) + 1) := by
    simp [concreteReflectBandIndex, bandTailCount]
  have hrect :
      -s ∈ Icc
        (-bandBoundaryHeight N j)
        (-bandBoundaryHeight N (j + 1)) :=
    ⟨neg_le_neg hs.2, neg_le_neg hs.1⟩
  rw [show
      ((concreteReflectBandIndex N j : Fin (bandTailCount N + 1)) : ℕ) + 1 =
        (symmetricBandPopulations N).length - (j : ℕ) by
      rw [href]
      omega,
    href, hleft, hright]
  exact hrect

/-- The northern squared-radius ratio, reflected to southern rectangles. -/
theorem southern_unequal_rectangle_radiusSq_ratio
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (hj : IsSouthernLatitudeBand N j)
    (hk : IsSouthernLatitudeBand N k)
    (hscale : 2 * latitudeBandScale N j <
      latitudeBandScale N k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    5 * (1 - s ^ 2) ≤ 3 * (1 - t ^ 2) := by
  let jr := concreteReflectBandIndex N j
  let kr := concreteReflectBandIndex N k
  have hjr : IsNorthernLatitudeBand N jr :=
    reflect_southern_is_northern hj
  have hkr : IsNorthernLatitudeBand N kr :=
    reflect_southern_is_northern hk
  have hscaleR :
      2 * latitudeBandScale N jr < latitudeBandScale N kr := by
    simpa [jr, kr] using hscale
  have hsR := neg_mem_reflected_band_rectangle_unequal hN j hs
  have htR := neg_mem_reflected_band_rectangle_unequal hN k ht
  have h := northern_unequal_rectangle_radiusSq_ratio hN jr kr
    hjr hkr hscaleR hsR htR
  simpa [jr, kr] using h

/-- Concrete geometry for every classified left-small same-hemisphere pair.
It includes the smaller-radius pole because the conclusion only uses squared
radii. -/
theorem leftSmallSame_rectangle_radiusSq_ratio
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : LeftSmallSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    5 * (1 - s ^ 2) ≤ 3 * (1 - t ^ 2) := by
  rcases hjk.2.2.1 with hNN | hSS
  · exact northern_unequal_rectangle_radiusSq_ratio hN j k
      hNN.1 hNN.2 hjk.2.2.2 hs ht
  · exact southern_unequal_rectangle_radiusSq_ratio hN j k
      hSS.1 hSS.2 hjk.2.2.2 hs ht

/-- Scale form of the northern radius bounds for a regular band. -/
theorem northern_regular_rectangle_radiusSq_scale_bounds
    {N : ℕ} (hN : 0 < N)
    (k : Fin (bandTailCount N + 1))
    (hk : IsNorthernLatitudeBand N k)
    (hkRegular : IsRegularLatitudeBand N k)
    {t : ℝ}
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    2 * (latitudeBandScale N k : ℝ) ^ 2 / N ≤ 1 - t ^ 2 ∧
      1 - t ^ 2 ≤
        12 * (latitudeBandScale N k : ℝ) ^ 2 / N := by
  have hb := northern_band_rectangle_radiusSq_bounds hN k hk ht
  have hkScale := latitudeBandScale_eq_north hk
  have hkNat : 2 ≤ (k : ℕ) := by
    unfold IsRegularLatitudeBand at hkRegular
    rw [hkScale] at hkRegular
    omega
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkNat
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hkScale]
  constructor
  · calc
      2 * (((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 / N ≤
          2 * (k : ℝ) * (2 * (k : ℝ) + 1) / N := by
        apply (div_le_div_iff_of_pos_right hNreal).2
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith
      _ ≤ 1 - t ^ 2 := hb.1
  · calc
      1 - t ^ 2 ≤
          4 * (((k : ℕ) + 1 : ℕ) : ℝ) *
            (2 * (((k : ℕ) + 1 : ℕ) : ℝ) + 1) / N := hb.2
      _ ≤ 12 * (((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 / N := by
        apply (div_le_div_iff_of_pos_right hNreal).2
        have : (0 : ℝ) ≤ (((k : ℕ) + 1 : ℕ) : ℝ) := by positivity
        norm_num [Nat.cast_add, Nat.cast_one] at this ⊢
        nlinarith

/-- The larger band has squared radius comparable to its manuscript scale
`d_k²/N`, uniformly on its whole rectangle. -/
theorem leftSmallSame_rectangle_largeRadiusSq_bounds
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : LeftSmallSameLatitudePair N j k)
    {t : ℝ}
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    2 * (latitudeBandScale N k : ℝ) ^ 2 / N ≤ 1 - t ^ 2 ∧
      1 - t ^ 2 ≤
        12 * (latitudeBandScale N k : ℝ) ^ 2 / N := by
  have hkRegular := (leftSmallSame_pair_regular hjk).2
  rcases hjk.2.2.1 with hNN | hSS
  · exact northern_regular_rectangle_radiusSq_scale_bounds
      hN k hNN.2 hkRegular ht
  · let kr := concreteReflectBandIndex N k
    have hkr : IsNorthernLatitudeBand N kr :=
      reflect_southern_is_northern hSS.2
    have htR := neg_mem_reflected_band_rectangle_unequal hN k ht
    have hkRegularR : IsRegularLatitudeBand N kr := by
      simpa [kr] using hkRegular
    have h := northern_regular_rectangle_radiusSq_scale_bounds
      hN kr hkr hkRegularR htR
    simpa [kr] using h

/-- On an unequal same-hemisphere rectangle, `A` is positive and comparable
to the squared large-radius scale.  Together with the next theorem this is
the complete geometric input to (5.6). -/
theorem leftSmallSame_rectangle_angularKernelA_bounds
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : LeftSmallSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    0 < angularKernelA s t ∧
      2 * (latitudeBandScale N k : ℝ) ^ 2 / N ≤
        angularKernelA s t ∧
      angularKernelA s t ≤
        48 * (latitudeBandScale N k : ℝ) ^ 2 / N := by
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hlarge :=
    leftSmallSame_rectangle_largeRadiusSq_bounds hN j k hjk ht
  have hratio :=
    leftSmallSame_rectangle_radiusSq_ratio hN j k hjk hs ht
  have hsameSign :
      (0 ≤ s ∧ 0 ≤ t) ∨ (s ≤ 0 ∧ t ≤ 0) := by
    rcases hjk.2.2.1 with hNN | hSS
    · exact Or.inl
        ⟨northern_band_rectangle_nonneg hN j hNN.1 hs,
          northern_band_rectangle_nonneg hN k hNN.2 ht⟩
    · have hsR := neg_mem_reflected_band_rectangle_unequal hN j hs
      have htR := neg_mem_reflected_band_rectangle_unequal hN k ht
      exact Or.inr
        ⟨by
          have := northern_band_rectangle_nonneg hN
            (concreteReflectBandIndex N j)
            (reflect_southern_is_northern hSS.1) hsR
          linarith,
        by
          have := northern_band_rectangle_nonneg hN
            (concreteReflectBandIndex N k)
            (reflect_southern_is_northern hSS.2) htR
          linarith⟩
  have hAlo : 1 - t ^ 2 ≤ angularKernelA s t := by
    rw [angularKernelA_eq_radiusSq_add]
    have hu : 0 ≤ 1 - s ^ 2 := by nlinarith [hsSphere.1, hsSphere.2]
    nlinarith [sq_nonneg (s - t)]
  have hAupper0 := angularKernelA_le_two_mul_radiusSq_add
    hsSphere htSphere hsameSign
  have hAupper : angularKernelA s t ≤ 4 * (1 - t ^ 2) := by
    nlinarith
  have hscalePos :
      0 < 2 * (latitudeBandScale N k : ℝ) ^ 2 / N := by
    have hscale : (0 : ℝ) < latitudeBandScale N k := by
      exact_mod_cast latitudeBandScale_pos N k
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  refine ⟨hscalePos.trans_le (hlarge.1.trans hAlo),
    hlarge.1.trans hAlo, ?_⟩
  calc
    angularKernelA s t ≤ 4 * (1 - t ^ 2) := hAupper
    _ ≤ 4 * (12 * (latitudeBandScale N k : ℝ) ^ 2 / N) := by
      exact mul_le_mul_of_nonneg_left hlarge.2 (by norm_num)
    _ = 48 * (latitudeBandScale N k : ℝ) ^ 2 / N := by ring

/-- Uniform `Q<1` on every left-small same-hemisphere band rectangle. -/
theorem leftSmallSame_rectangle_unequalAngularRatio_le
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : LeftSmallSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    unequalAngularRatio s t ≤ (15 : ℝ) / 16 := by
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hv : 0 < 1 - t ^ 2 := by
    rcases hjk.2.2.1 with hNN | hSS
    · have ht0 := northern_band_rectangle_nonneg hN k hNN.2 ht
      have hregular := (leftSmallSame_pair_regular hjk).2
      have hkpos : 0 < (k : ℕ) := by
        unfold IsRegularLatitudeBand at hregular
        rw [latitudeBandScale_eq_north hNN.2] at hregular
        omega
      have hupper :
          t < 1 := by
        have hf := concrete_bandBoundaryHeight_north
          (N := N) (j := (k : ℕ))
          (by unfold IsNorthernLatitudeBand at hNN; omega)
        rw [hf] at ht
        have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
        have hkreal : (0 : ℝ) < (k : ℕ) := by exact_mod_cast hkpos
        have hfrac :
            0 < 2 * (k : ℝ) * (2 * (k : ℝ) + 1) / N := by positivity
        linarith [ht.2]
      nlinarith
    · have htR := neg_mem_reflected_band_rectangle_unequal hN k ht
      have hkr := reflect_southern_is_northern hSS.2
      have hregular :
          IsRegularLatitudeBand N (concreteReflectBandIndex N k) := by
        simpa using (leftSmallSame_pair_regular hjk).2
      have hneg0 := northern_band_rectangle_nonneg hN
        (concreteReflectBandIndex N k) hkr htR
      have hkpos :
          0 < ((concreteReflectBandIndex N k : Fin
            (bandTailCount N + 1)) : ℕ) := by
        unfold IsRegularLatitudeBand at hregular
        rw [latitudeBandScale_eq_north hkr] at hregular
        omega
      have hnegUpper : -t < 1 := by
        have hf := concrete_bandBoundaryHeight_north
          (N := N)
          (j := ((concreteReflectBandIndex N k :
            Fin (bandTailCount N + 1)) : ℕ))
          (by unfold IsNorthernLatitudeBand at hkr; omega)
        rw [hf] at htR
        have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
        have hkreal :
            (0 : ℝ) < ((concreteReflectBandIndex N k :
              Fin (bandTailCount N + 1)) : ℕ) := by exact_mod_cast hkpos
        have hfrac :
            0 < 2 * (((concreteReflectBandIndex N k :
                Fin (bandTailCount N + 1)) : ℕ) : ℝ) *
                (2 * (((concreteReflectBandIndex N k :
                  Fin (bandTailCount N + 1)) : ℕ) : ℝ) + 1) / N := by
          positivity
        linarith [htR.2]
      nlinarith
  exact unequalAngularRatio_le_fifteen_sixteen_of_radiusSq
    (by nlinarith [hsSphere.1, hsSphere.2])
    hv
    (leftSmallSame_rectangle_radiusSq_ratio hN j k hjk hs ht)

/-- Consequently the degree-four differentiated-series majorant is normally
summable at every point of every literal unequal-scale band rectangle.  The
ratio is the fixed numerical constant `15/16`, independent of `N`, the
indices, and the endpoint radii. -/
theorem leftSmallSame_rectangle_summable_polyseriesDerivative_majorant
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : LeftSmallSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    Summable (fun m : ℕ ↦
      ((m : ℝ) + 3) ^ (4 : ℕ) *
        (unequalAngularRatio s t ^ m +
          unequalAngularRatio s t ^ (m + 2))) := by
  apply summable_polyseriesDerivative_majorant
  · have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
        hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
    have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
      ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
        ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
    exact unequalAngularRatio_nonneg hsSphere htSphere
  · exact (leftSmallSame_rectangle_unequalAngularRatio_le
      hN j k hjk hs ht).trans_lt (by norm_num)

end BEMOC
