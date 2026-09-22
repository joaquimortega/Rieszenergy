import BEMOCFormalization.LatitudeNeighboringPointwiseClosure

/-!
# Resonant neighboring block arithmetic

This module contains only the population/radius conversion needed after a
resonant neighboring remainder has been bounded in normalized coordinates.
-/

namespace BEMOC

noncomputable def neighboringResonantNormalizedBandLength
    (N : ℕ) (j k : Fin (bandTailCount N + 1)) : ℝ :=
  neighboringBandLength N j k /
    comparableLatitudeRadiusFloor N j ^ 2

private theorem radius_mul_normalizedLength_sq
    {R a : ℝ} (hR : 0 < R) :
    R * (a / R ^ 2) ^ 2 = R ^ (-3 : ℝ) * a ^ 2 := by
  rw [Real.rpow_neg hR.le]
  rw [show R ^ (3 : ℝ) = R ^ 3 by
    exact Real.rpow_natCast R 3]
  rw [div_pow]
  field_simp [hR.ne']
  ring

private theorem resonant_neighboring_scale_identity
    {d M : ℝ} (hd : 0 < d) (hM : 0 < M) :
    (d / (10 * M)) ^ (-3 : ℝ) *
        (6 * d / M ^ 2) ^ 2 =
      (10 : ℝ) ^ 3 * (6 : ℝ) ^ 2 *
        d ^ (-1 : ℝ) * M ^ (-1 : ℝ) := by
  rw [Real.rpow_neg (by positivity : 0 ≤ d / (10 * M)),
    show (d / (10 * M)) ^ (3 : ℝ) =
      (d / (10 * M)) ^ 3 by
        exact Real.rpow_natCast (d / (10 * M)) 3,
    Real.rpow_neg hd.le, Real.rpow_one,
    Real.rpow_neg hM.le, Real.rpow_one]
  rw [div_pow, div_pow]
  field_simp [hd.ne', hM.ne']
  ring

/-- A normalized resonant rectangle remainder has the exact neighboring
comparable block scale.  The deliberately uniform factor `1024` also
absorbs the worst neighboring distance weight. -/
theorem neighboringResonant_raw_bound_to_majorant
    {B E : ℝ} (hB : 0 ≤ B)
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : NeighboringComparableLatitudePair N j k)
    (hraw :
      |E| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (B * (comparableLatitudeRadiusFloor N j *
              neighboringResonantNormalizedBandLength N j k ^ 2))) :
    |E| ≤
      comparableLatitudeBlockMajorant 1
        (1024 * B * (10 : ℝ) ^ 3 * (6 : ℝ) ^ 2) N j k := by
  let d : ℝ := latitudeBandScale N j
  let M : ℝ := bandCount N
  let a : ℝ := neighboringBandLength N j k
  let R : ℝ := comparableLatitudeRadiusFloor N j
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast latitudeBandScale_pos N j
  have hMr : 0 < M := by dsimp [M]; positivity
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    positivity
  have ha : 0 < a := by
    have hN : 0 < N := by
      have hfour := four_mul_bandCount_sq_le N
      have : 0 < 4 * bandCount N ^ 2 := by positivity
      omega
    dsimp [a]
    exact neighboringBandLength_pos hN hM j k
  have halen : a ≤ 6 * d / M ^ 2 := by
    simpa [a, d, M] using
      neighboringComparable_bandLength_le_scale
        (by omega : 1 ≤ bandCount N) hjk
  have ha2 :
      a ^ 2 ≤ (6 * d / M ^ 2) ^ 2 := by gcongr
  have hnormalized :
      R * neighboringResonantNormalizedBandLength N j k ^ 2 =
        R ^ (-3 : ℝ) * a ^ 2 := by
    simpa [neighboringResonantNormalizedBandLength, R, a] using
      radius_mul_normalizedLength_sq (R := R) (a := a) hR
  have hscale :
      R * neighboringResonantNormalizedBandLength N j k ^ 2 ≤
        (10 : ℝ) ^ 3 * 6 ^ 2 *
          d ^ (-1 : ℝ) * M ^ (-1 : ℝ) := by
    rw [hnormalized]
    calc
      R ^ (-3 : ℝ) * a ^ 2 ≤
          R ^ (-3 : ℝ) * (6 * d / M ^ 2) ^ 2 := by gcongr
      _ = _ := by
        simpa [R, comparableLatitudeRadiusFloor, d, M] using
          resonant_neighboring_scale_identity hd hMr
  have hpops :=
    finiteBandPopulations_le_four_scales_of_same hjk.1.2.2.1
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤ 4 * d := by
    dsimp [d]
    exact_mod_cast hpops.1
  have hpk0 :
      (finiteBandPopulation N k : ℝ) ≤
        4 * (latitudeBandScale N k : ℝ) := by
    exact_mod_cast hpops.2
  have hdk :
      (latitudeBandScale N k : ℝ) ≤ 2 * d := by
    dsimp [d]
    exact_mod_cast hjk.1.2.2.2.2
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤ 8 * d := by linarith
  have hpop :
      4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) ≤ 128 * d ^ 2 := by
    calc
      4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) ≤
        4 * (4 * d) * (8 * d) := by gcongr
      _ = 128 * d ^ 2 := by ring
  have hD :
      (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ≤ 2 := by
    have hn := hjk.2
    exact_mod_cast (show
      1 + Nat.dist (j : ℕ) (k : ℕ) ≤ 2 by omega)
  have hweight :
      (1 : ℝ) / 8 ≤
        (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (-2 : ℝ) := by
    have hbase :
        (0 : ℝ) < 1 + Nat.dist (j : ℕ) (k : ℕ) := by positivity
    have hp :=
      Real.rpow_le_rpow_of_nonpos hbase hD (by norm_num : (-2 : ℝ) ≤ 0)
    have htwo : (1 : ℝ) / 8 ≤ 2 ^ (-2 : ℝ) := by norm_num
    exact htwo.trans hp
  have hdInv : d ^ (-1 : ℝ) = d⁻¹ := by
    rw [Real.rpow_neg hd.le, Real.rpow_one]
  have hMInv : M ^ (-1 : ℝ) = M ^ (-(1 : ℝ)) := by norm_num
  unfold comparableLatitudeBlockMajorant
  norm_num only [Nat.cast_one, one_div] at *
  have hfactor :
      B * (R * neighboringResonantNormalizedBandLength N j k ^ 2) ≤
        B * (36000 *
          d ^ (-1 : ℝ) * M ^ (-1 : ℝ)) :=
    mul_le_mul_of_nonneg_left hscale hB
  have hfactor0 :
      0 ≤ B * (36000 *
        d ^ (-1 : ℝ) * M ^ (-1 : ℝ)) := by positivity
  calc
    |E| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (B * (R *
              neighboringResonantNormalizedBandLength N j k ^ 2)) := hraw
    _ ≤ 128 * d ^ 2 *
          (B * (36000 *
            d ^ (-1 : ℝ) * M ^ (-1 : ℝ))) := by
      calc
        4 * (finiteBandPopulation N j : ℝ) *
            (finiteBandPopulation N k : ℝ) *
              (B * (R *
                neighboringResonantNormalizedBandLength N j k ^ 2)) ≤
          4 * (finiteBandPopulation N j : ℝ) *
            (finiteBandPopulation N k : ℝ) *
              (B * (36000 *
                d ^ (-1 : ℝ) * M ^ (-1 : ℝ))) :=
          mul_le_mul_of_nonneg_left hfactor (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right hpop hfactor0
    _ = 128 * B * (10 : ℝ) ^ 3 * 6 ^ 2 * d * M ^ (-1 : ℝ) := by
      rw [hdInv]
      field_simp [hd.ne']
      ring
    _ ≤ 1024 * B * (10 : ℝ) ^ 3 * 6 ^ 2 *
          d * M ^ (-1 : ℝ) *
            (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (-2 : ℝ) := by
      have hnonneg :
          0 ≤ 128 * B * (10 : ℝ) ^ 3 * 6 ^ 2 *
            d * M ^ (-1 : ℝ) := by positivity
      nlinarith
    _ = 1024 * B * 1000 * 36 *
          (latitudeBandScale N j : ℝ) *
          (bandCount N : ℝ) ^ (-1 : ℝ) *
          (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (-2 : ℝ) := by
      dsimp [d, M]
      norm_num

end BEMOC
