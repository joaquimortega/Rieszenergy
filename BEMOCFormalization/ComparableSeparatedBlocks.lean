import BEMOCFormalization.ComparableBlockEstimates
import BEMOCFormalization.SeparatedComplete
import BEMOCFormalization.ComparablePowerScaling

open Set
namespace BEMOC.Definitive

/-- If a separation lies between `M` and `2M`, the comparable power weight
is at least the cubic inverse scale. -/
theorem endpoint_comparable_power_lower {α M D : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hM : 0 < M) (hMD : M ≤ D) (hDM : D ≤ 2 * M) :
    1 / (8 * M ^ 3) ≤ M ^ (-α) * D ^ (α - 3) := by
  have hD : 0 < D := hM.trans_le hMD
  have hβ : 0 ≤ 3 - α := by linarith
  have hpow := Real.rpow_le_rpow hM.le hMD hα0.le
  have hβnonneg : 0 ≤ D ^ (3 - α) := Real.rpow_nonneg hD.le _
  have hprod : M ^ α * D ^ (3 - α) ≤ D ^ α * D ^ (3 - α) :=
    mul_le_mul_of_nonneg_right hpow hβnonneg
  have hcombine : D ^ α * D ^ (3 - α) = D ^ (3 : ℕ) := by
    rw [← Real.rpow_add hD]
    convert (Real.rpow_natCast D 3) using 1 <;> ring
  have hcube : D ^ (3 : ℕ) ≤ 8 * M ^ (3 : ℕ) := by
    calc
      D ^ (3 : ℕ) ≤ (2 * M) ^ (3 : ℕ) := by gcongr
      _ = 8 * M ^ (3 : ℕ) := by ring
  have hdenom : M ^ α * D ^ (3 - α) ≤ 8 * M ^ (3 : ℕ) := by
    calc
      _ ≤ D ^ α * D ^ (3 - α) := hprod
      _ = D ^ (3 : ℕ) := hcombine
      _ ≤ _ := hcube
  have hdenompos : 0 < M ^ α * D ^ (3 - α) := by positivity
  have hfrac : 1 / (8 * M ^ (3 : ℕ)) ≤ 1 / (M ^ α * D ^ (3 - α)) :=
    one_div_le_one_div_of_le hdenompos hdenom
  calc
    1 / (8 * M ^ (3 : ℕ)) ≤ 1 / (M ^ α * D ^ (3 - α)) := hfrac
    _ = M ^ (-α) * D ^ (α - 3) := by
      rw [show α - 3 = -(3 - α) by ring, Real.rpow_neg hM.le,
        Real.rpow_neg hD.le]
      ring

/-- Opposite endpoint labels have separation between `M` and `2M`. -/
theorem opposite_small_bands_index_scale {N : ℕ} (hN : 1024 ≤ N)
    (j k : RingIndex N) (hj8 : j.val + 1 ≤ 8)
    (hk8 : 2 * bandParameter N - (k.val + 1) ≤ 8) :
    (bandParameter N : ℝ) ≤ 1 + |(j.val : ℝ) - k.val| ∧
      1 + |(j.val : ℝ) - k.val| ≤ 2 * bandParameter N := by
  have hM16 := bandParameter_ge_sixteen_of_ge_1024 hN
  have hjk : j.val ≤ k.val := by
    have := k.isLt
    omega
  have hreal : (j.val : ℝ) ≤ k.val := by exact_mod_cast hjk
  have habs : |(j.val : ℝ) - k.val| = (k.val : ℝ) - j.val := by
    rw [abs_of_nonpos (sub_nonpos.mpr hreal)]
    ring
  rw [habs]
  have hjNat : j.val ≤ 7 := by omega
  have hkNat : 2 * bandParameter N ≤ k.val + 9 := by omega
  have hkTop : k.val + 2 ≤ 2 * bandParameter N := by
    have := k.isLt
    omega
  have hjReal : (j.val : ℝ) ≤ 7 := by exact_mod_cast hjNat
  have hkReal : 2 * (bandParameter N : ℝ) ≤ (k.val : ℝ) + 9 := by
    exact_mod_cast hkNat
  have hkTopReal : (k.val : ℝ) + 2 ≤ 2 * bandParameter N := by
    exact_mod_cast hkTop
  have hMreal : (16 : ℝ) ≤ bandParameter N := by exact_mod_cast hM16
  constructor <;> linarith

theorem opposite_small_bands_population_le {N : ℕ} (hN : 1024 ≤ N)
    (j k : RingIndex N) (hj8 : j.val + 1 ≤ 8)
    (hk8 : 2 * bandParameter N - (k.val + 1) ≤ 8) :
    population N (j.val + 1) ≤ 32 ∧
      population N (k.val + 1) ≤ 32 := by
  have hM16 := bandParameter_ge_sixteen_of_ge_1024 hN
  constructor
  · rw [north_population N (j.val + 1) (by omega)]
    omega
  · rw [south_population N (k.val + 1) (by omega)]
    omega

/-- Numerical conversion of the opposite-pole eighth-order Taylor remainder
to the required comparable cubic separation weight. -/
theorem opposite_endpoint_taylor_scale {α M D r r' C : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (hM : 1 ≤ M) (hMD : M ≤ D) (hDM : D ≤ 2 * M)
    (hr0 : 0 ≤ r) (hr32 : r ≤ 32)
    (hr'0 : 0 ≤ r') (hr'32 : r' ≤ 32) (hC : 0 ≤ C) :
    r ^ 3 * r' ^ 3 / M ^ 8 * C ≤
      (8 * 32 ^ 5 * C) * (r / M ^ α) * D ^ (α - 3) := by
  have hM0 : 0 < M := by linarith
  have hscale := endpoint_comparable_power_lower hα0 hα2
    hM0 hMD hDM
  have hscaled : r / (8 * M ^ 3) ≤ r / M ^ α * D ^ (α - 3) := by
    calc
      r / (8 * M ^ 3) = r * (1 / (8 * M ^ 3)) := by ring
      _ ≤ r * (M ^ (-α) * D ^ (α - 3)) :=
        mul_le_mul_of_nonneg_left hscale hr0
      _ = r / M ^ α * D ^ (α - 3) := by
        rw [Real.rpow_neg hM0.le]
        ring
  have hprod : r ^ 3 * r' ^ 3 ≤ r * 32 ^ 5 := by
    calc
      r ^ 3 * r' ^ 3 = r * (r ^ 2 * r' ^ 3) := by ring
      _ ≤ r * (32 ^ 2 * 32 ^ 3) := by gcongr
      _ = r * 32 ^ 5 := by norm_num
  have hMpower : M ^ 3 ≤ M ^ 8 :=
    pow_le_pow_right₀ hM (by omega : 3 ≤ 8)
  have hdenom : 1 / M ^ 8 ≤ 1 / M ^ 3 :=
    one_div_le_one_div_of_le (pow_pos hM0 3) hMpower
  calc
    r ^ 3 * r' ^ 3 / M ^ 8 * C =
        (r ^ 3 * r' ^ 3) * (1 / M ^ 8) * C := by ring
    _ ≤ (r * 32 ^ 5) * (1 / M ^ 3) * C := by gcongr
    _ = (8 * 32 ^ 5 * C) * (r / (8 * M ^ 3)) := by ring
    _ ≤ (8 * 32 ^ 5 * C) * (r / M ^ α * D ^ (α - 3)) := by
      gcongr
    _ = (8 * 32 ^ 5 * C) * (r / M ^ α) * D ^ (α - 3) := by ring

/-- The separated series and the two-moment Taylor theorem give a uniform
fourth-order bound on all opposite first-eight polar rectangles. -/
theorem opposite_small_bands_taylor_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
      j.val + 1 ≤ 8 →
      2 * bandParameter N - (k.val + 1) ≤ 8 →
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        (population N (j.val + 1) : ℝ) ^ 3 *
          (population N (k.val + 1) : ℝ) ^ 3 /
            (bandParameter N : ℝ) ^ 8 * C := by
  obtain ⟨C, hC, hderiv⟩ :=
    uniform_separatedSmoothExtension_mixedFourth_le hα0 hα2
      (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)
  refine ⟨C, hC, ?_⟩
  intro N hN j k hj8 hk8
  let q := 2 * bandParameter N - (k.val + 1)
  have hj1 : 1 ≤ j.val + 1 := by omega
  have hq1 : 1 ≤ q := by
    dsimp [q]
    have := k.isLt
    omega
  have hqeq : 2 * bandParameter N - q = k.val + 1 := by
    dsimp [q]
    have := k.isLt
    omega
  have hq8 : q ≤ 8 := hk8
  let G := separatedSmoothExtension α
  let W := separatedOpen
  have hrect : band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ W := by
    intro p hp
    rw [← hqeq] at hp
    exact opposite_small_bands_mem_separatedOpen hN hj1 hj8 hq1 hq8 hp.1 hp.2
  have heq : ∀ s ∈ band N (j.val + 1), ∀ t ∈ band N (k.val + 1),
      G (s, t) = latitudeKernel α s t := by
    intro s hs t ht
    have hp : (s, t) ∈ W := hrect ⟨hs, ht⟩
    have hsI : s ∈ Icc (-1 : ℝ) 1 := by
      have h := north_small_band_height_bounds hN hj1 hj8 hs
      constructor <;> linarith [h.1, h.2.1]
    have htI : t ∈ Icc (-1 : ℝ) 1 := by
      have h := north_small_band_height_bounds hN hq1 hq8
        (south_small_band_neg_mem_north_small hN hq1 hq8 (hqeq ▸ ht))
      constructor <;> linarith [h.1, h.2.1]
    exact separatedSmoothExtension_eq_latitudeKernel hp hsI htI
  have hfourth : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      |mixedFourth G p.1 p.2| ≤ C := by
    intro p hp
    have hs := north_small_band_height_bounds hN hj1 hj8 hp.1
    have ht := north_small_band_height_bounds hN hq1 hq8
      (south_small_band_neg_mem_north_small hN hq1 hq8 (hqeq ▸ hp.2))
    have hsI : p.1 ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2.1]
    have htI : p.2 ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2.1]
    have hsep := opposite_small_bands_separated hN hj1 hj8 hq1 hq8
      hp.1 (hqeq ▸ hp.2)
    have hraw := hderiv p.1 hsI p.2 htI hsep.1 hsep.2
    have hUone : 1 ≤ 2 - 2 * p.1 * p.2 := by
      have ht0 : p.2 ≤ 0 := by linarith only [ht.1]
      have hprod : p.1 * p.2 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs.1 ht0
      nlinarith only [hprod]
    have hexp : α / 2 - 4 ≤ 0 := by linarith
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos hUone hexp
    have hmul := mul_le_mul_of_nonneg_left hpow hC.le
    dsimp [G] at *
    nlinarith [hraw, hmul]
  exact kernelBlock_le_of_smooth_extension (by omega : 4 ≤ N) j k α G W
    isOpen_separatedOpen hrect
    (separatedSmoothExtension_contDiffOn hα0 hα2) heq C hC.le hfourth

/-- Opposite polar endpoint blocks satisfy the manuscript's exact comparable
majorant, with a constant independent of `N` and both ring labels. -/
theorem opposite_small_bands_comparable_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
      j.val + 1 ≤ 8 →
      2 * bandParameter N - (k.val + 1) ≤ 8 →
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        C * population N (j.val + 1) / (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
  obtain ⟨C₀, hC₀, hT⟩ := opposite_small_bands_taylor_bound hα0 hα2
  refine ⟨8 * 32 ^ 5 * C₀, by positivity, ?_⟩
  intro N hN j k hj8 hk8
  have hpop := opposite_small_bands_population_le hN j k hj8 hk8
  have hidx := opposite_small_bands_index_scale hN j k hj8 hk8
  have hM : (1 : ℝ) ≤ bandParameter N := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ (16 : ℕ))
      (bandParameter_ge_sixteen_of_ge_1024 hN))
  have hr0 : (0 : ℝ) ≤ population N (j.val + 1) := by positivity
  have hr'0 : (0 : ℝ) ≤ population N (k.val + 1) := by positivity
  have hscale := opposite_endpoint_taylor_scale hα0 hα2 hM hidx.1 hidx.2
    hr0 (by exact_mod_cast hpop.1) hr'0 (by exact_mod_cast hpop.2) hC₀.le
  calc
    _ ≤ (population N (j.val + 1) : ℝ) ^ 3 *
          (population N (k.val + 1) : ℝ) ^ 3 /
            (bandParameter N : ℝ) ^ 8 * C₀ := hT N hN j k hj8 hk8
    _ ≤ (8 * 32 ^ 5 * C₀) *
          ((population N (j.val + 1) : ℝ) /
            (bandParameter N : ℝ) ^ α) *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := hscale
    _ = _ := by ring

/-- Swapping the two opposite polar corners costs at most the factor eight
already present in population comparability. -/
theorem reverse_opposite_small_bands_comparable_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
      2 * bandParameter N - (j.val + 1) ≤ 8 →
      k.val + 1 ≤ 8 →
      Comparable N (j.val + 1) (k.val + 1) →
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        C * population N (j.val + 1) / (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
  obtain ⟨C₀, hC₀, hbase⟩ :=
    opposite_small_bands_comparable_bound hα0 hα2
  refine ⟨8 * C₀, by positivity, ?_⟩
  intro N hN j k hj8 hk8 hcomp
  have hsym := blockSymmetry_of_pos hα0 N (by omega : 4 ≤ N) j k
  have hraw := hbase N hN k j hk8 hj8
  rw [← hsym, abs_sub_comm (k.val : ℝ) j.val] at hraw
  have hpop : (population N (k.val + 1) : ℝ) ≤
      8 * population N (j.val + 1) := hcomp.2
  let Q : ℝ := C₀ / (bandParameter N : ℝ) ^ α *
    (1 + |(j.val : ℝ) - k.val|) ^ (α - 3)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  calc
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        C₀ * population N (k.val + 1) /
          (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := hraw
    _ = (population N (k.val + 1) : ℝ) * Q := by dsimp [Q]; ring
    _ ≤ (8 * population N (j.val + 1) : ℝ) * Q :=
      mul_le_mul_of_nonneg_right hpop hQ
    _ = (8 * C₀) * population N (j.val + 1) /
          (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
      dsimp [Q]
      ring

/-- The same global extension yields a Taylor estimate on regular far
comparable rectangles, retaining the exact angular-gap scale for conversion
to the manuscript's block majorant. -/
theorem far_comparable_taylor_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
      j.val ≠ 0 → j.val + 1 ≠ 2 * bandParameter N - 1 →
      k.val ≠ 0 → k.val + 1 ≠ 2 * bandParameter N - 1 →
      Comparable N (j.val + 1) (k.val + 1) →
      2 ≤ |(j.val : ℤ) - k.val| →
      2 * (population N (j.val + 1) : ℝ) <
        |(j.val : ℝ) - k.val| →
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        (population N (j.val + 1) : ℝ) ^ 3 *
          (population N (k.val + 1) : ℝ) ^ 3 /
            (bandParameter N : ℝ) ^ 8 *
              (C * ((|(j.val : ℝ) - k.val| /
                (bandParameter N : ℝ)) ^ 2 / 3600) ^ (α / 2 - 4)) := by
  obtain ⟨C, hC, hderiv⟩ :=
    uniform_separatedSmoothExtension_mixedFourth_le hα0 hα2
      (by norm_num : (0 : ℝ) < 1 / 4000000)
      (by norm_num : (1 / 4000000 : ℝ) < 1)
  refine ⟨C, hC, ?_⟩
  intro N hN j k hjfirst hjlast hkfirst hklast hcomp hjk hfar
  let G := separatedSmoothExtension α
  let W := separatedOpen
  have hpair (s t : ℝ)
      (hs : s ∈ band N (j.val + 1))
      (ht : t ∈ band N (k.val + 1)) :
      0 < angularKernelA s t ∧
        (|(j.val : ℝ) - k.val| / (bandParameter N : ℝ)) ^ 2 / 3600 ≤
          angularKernelA s t ∧
        angularKernelA s t ≤
          904 * (|(j.val : ℝ) - k.val| / (bandParameter N : ℝ)) ^ 2 ∧
        angularKernelB s t ≤
          (1 - (1 / 4000000 : ℝ)) * angularKernelA s t :=
    far_comparable_rectangle_separation hN j k hjfirst hjlast
      hkfirst hklast hcomp hjk hfar hs ht
  have hsI (s : ℝ) (hs : s ∈ band N (j.val + 1)) :
      s ∈ Icc (-1 : ℝ) 1 := by
    have hlo := boundary_ge_neg_one (by omega : 4 ≤ N)
      (by have := j.isLt; omega : j.val + 1 < 2 * bandParameter N)
    have hhi := boundary_le_one (by omega : 4 ≤ N)
      (by have := j.isLt; omega : j.val < 2 * bandParameter N)
    exact ⟨hlo.trans hs.1, hs.2.trans hhi⟩
  have htI (t : ℝ) (ht : t ∈ band N (k.val + 1)) :
      t ∈ Icc (-1 : ℝ) 1 := by
    have hlo := boundary_ge_neg_one (by omega : 4 ≤ N)
      (by have := k.isLt; omega : k.val + 1 < 2 * bandParameter N)
    have hhi := boundary_le_one (by omega : 4 ≤ N)
      (by have := k.isLt; omega : k.val < 2 * bandParameter N)
    exact ⟨hlo.trans ht.1, ht.2.trans hhi⟩
  have hrect : band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ W := by
    intro p hp
    have hg := hpair p.1 p.2 hp.1 hp.2
    apply mem_separatedOpen_of_physical_ratio_lt_one
      (hsI p.1 hp.1) (htI p.2 hp.2) hg.1
    exact separatedRatio_lt_one (hsI p.1 hp.1) (htI p.2 hp.2)
      hg.1 (by norm_num) (by norm_num) hg.2.2.2
  have heq : ∀ s ∈ band N (j.val + 1), ∀ t ∈ band N (k.val + 1),
      G (s, t) = latitudeKernel α s t := by
    intro s hs t ht
    exact separatedSmoothExtension_eq_latitudeKernel
      (hrect ⟨hs, ht⟩) (hsI s hs) (htI t ht)
  have hM : (0 : ℝ) < bandParameter N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (16 : ℕ))
      (bandParameter_ge_sixteen_of_ge_1024 hN))
  have hd : 0 < |(j.val : ℝ) - k.val| / (bandParameter N : ℝ) := by
    apply div_pos _ hM
    have hr : 0 ≤ (population N (j.val + 1) : ℝ) := by positivity
    linarith [abs_nonneg ((j.val : ℝ) - k.val)]
  have hbase : 0 <
      (|(j.val : ℝ) - k.val| / (bandParameter N : ℝ)) ^ 2 / 3600 :=
    div_pos (sq_pos_of_pos hd) (by norm_num)
  let L : ℝ := C *
    ((|(j.val : ℝ) - k.val| / (bandParameter N : ℝ)) ^ 2 / 3600) ^
      (α / 2 - 4)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg hC.le (Real.rpow_nonneg hbase.le _)
  have hfourth : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      |mixedFourth G p.1 p.2| ≤ L := by
    intro p hp
    have hg := hpair p.1 p.2 hp.1 hp.2
    have hraw := hderiv p.1 (hsI p.1 hp.1) p.2 (htI p.2 hp.2)
      hg.1 hg.2.2.2
    have hexp : α / 2 - 4 ≤ 0 := by linarith
    have hpow := Real.rpow_le_rpow_of_nonpos hbase hg.2.1 hexp
    dsimp [G, L]
    exact hraw.trans (mul_le_mul_of_nonneg_left hpow hC.le)
  exact kernelBlock_le_of_smooth_extension (by omega : 4 ≤ N) j k α G W
    isOpen_separatedOpen hrect
    (separatedSmoothExtension_contDiffOn hα0 hα2) heq L hL hfourth

/-- The global separated kernel closes the regular far-comparable block
estimate at the exact row and index scale. -/
theorem far_comparable_block_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
      j.val ≠ 0 → j.val + 1 ≠ 2 * bandParameter N - 1 →
      k.val ≠ 0 → k.val + 1 ≠ 2 * bandParameter N - 1 →
      Comparable N (j.val + 1) (k.val + 1) →
      2 ≤ |(j.val : ℤ) - k.val| →
      2 * (population N (j.val + 1) : ℝ) <
        |(j.val : ℝ) - k.val| →
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        C * population N (j.val + 1) / (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
  obtain ⟨C₀, hC₀, hT⟩ := far_comparable_taylor_bound hα0 hα2
  let C : ℝ := 128 * 3600 ^ (4 - α / 2) * C₀
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N hN j k hjfirst hjlast hkfirst hklast hcomp hjk hfar
  let M : ℝ := bandParameter N
  let r : ℝ := population N (j.val + 1)
  let r' : ℝ := population N (k.val + 1)
  let ℓ : ℝ := |(j.val : ℝ) - k.val|
  have hM : 16 ≤ M := by
    dsimp [M]
    exact_mod_cast bandParameter_ge_sixteen_of_ge_1024 hN
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast population_pos (by omega : 4 ≤ N) (by omega)
      (by have := j.isLt; omega)
  have hr' : 0 ≤ r' := by positivity
  have hr'le : r' ≤ 8 * r := hcomp.2
  have hℓ : 2 ≤ ℓ := by
    dsimp [ℓ]
    exact_mod_cast hjk
  have hsc := comparable_far_power_scaling hα0 hα2 hM hr hr' hr'le hfar hℓ
  calc
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        r ^ 3 * r' ^ 3 / M ^ 8 *
          (C₀ * ((ℓ / M) ^ 2 / 3600) ^ (α / 2 - 4)) :=
      hT N hN j k hjfirst hjlast hkfirst hklast hcomp hjk hfar
    _ = C₀ *
          (r ^ 3 * r' ^ 3 / M ^ 8 *
            ((ℓ / M) ^ 2 / 3600) ^ (α / 2 - 4)) := by ring
    _ ≤ C₀ * ((128 * 3600 ^ (4 - α / 2)) *
          (r / M ^ α) * (1 + ℓ) ^ (α - 3)) :=
      mul_le_mul_of_nonneg_left hsc hC₀.le
    _ = C * population N (j.val + 1) / (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
      dsimp [C, r, ℓ, M]
      ring

end BEMOC.Definitive
