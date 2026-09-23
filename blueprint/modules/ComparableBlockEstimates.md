# ComparableBlockEstimates proof guide

Source anchor: `definitive.tex`, the proof of `eq:comparableblock` around lines 1897–2041. This auxiliary module develops concrete polar cases and reusable bridges for the full `ComparableBlockBound`; it does not weaken that predicate.

The signed band rule has total variation at most `2r_j` on its literal interval. Therefore a kernel bounded by `C` on the literal rectangle has tensor block magnitude at most `4r_jr_k C`. The module proves this directly for the current `bandError`, including the actual midpoint and interval endpoints. It also proves a rectangle-local congruence theorem and `kernelBlock_le_of_smooth_extension`, which feeds any genuine `C⁴` extension of `latitudeKernel` to the now proved `mixedTaylorBound`.

For `N≥1024`, `M≥16`. The first northern band lies within `8/N` of the north pole, giving chord-square bound `64/N`; the first eight bands lie within `288/N`, giving chord-square bound `2304/N`. Angular averaging and total variation yield the raw block estimates. `north_small_bands_comparable_bound` converts the first-eight estimate to the exact manuscript majorant, with explicit constant `65536*24^α`, for `0<α<2`. The proofs of `bandError_reflect` and `kernelBlock_reflect` transfer this estimate to the last eight southern bands in `south_small_bands_comparable_bound`. The sharper first and last diagonal bounds have constant `16*4^α`.

An index with population at most 32 is among the first or last eight bands; comparability with either endpoint puts both indices in these finite polar regions. For first-eight north versus last-eight south, `opposite_small_bands_separated` proves `U>0` and `V≤(1−1/4)U` on the literal rectangle. `opposite_small_bands_mem_separatedOpen` places the entire rectangle in the global smooth-series domain. The later separated mixed derivative estimate combines with `kernelBlock_le_of_smooth_extension` to cover opposite endpoint pairs. The new `far_comparable_rectangle_separation` proves that every nonendpoint far-comparable rectangle has `U>0`, `d²/3600≤U≤904d²` for `d=|j−k|/M`, and `V≤(1−1/4000000)U`, using the checked polar-angle gap, chord, and radius comparisons; this supplies the far-regime geometry for the same separated extension and Taylor theorem.

This module provides the endpoint and far geometry used downstream. `ComparableSeparatedBlocks`, `ComparableIntermediateClosure`, `ComparableNearTailClosure`, and `ComparableAssembly` complete the remaining cases; `comparable_block_bound` now inhabits `ComparableBlockBound α`. `lake build BEMOCFormalization.ComparableBlockEstimates` passes; no proof shortcuts or whitespace errors are present.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.ComparableBlocks
import BEMOCFormalization.LatitudePotential
import BEMOCFormalization.SeparatedSmoothExtension
import BEMOCFormalization.AngularDistance

open scoped BigOperators
open MeasureTheory Set
namespace BEMOC.Definitive

/-- Total-variation control of one band error by a bound on its own band. -/
theorem abs_bandError_le_of_band_bound {N j : ℕ}
    (hN : 4 ≤ N) (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (f : ℝ → ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ t ∈ band N j, |f t| ≤ C) :
    |bandError N j f| ≤ 2 * (population N j : ℝ) * C := by
  have hab : boundary N j ≤ boundary N (j - 1) := by
    rw [← sub_nonneg, boundary_width hN hj1]
    positivity
  have hmid : height N j ∈ band N j := by
    have hm := height_inside_band hN hj1 hj2
    exact ⟨hm.1.le, hm.2.le⟩
  have hint : |∫ t in boundary N j..boundary N (j - 1), f t| ≤
      C * (boundary N (j - 1) - boundary N j) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := boundary N j) (b := boundary N (j - 1)) (C := C)
      (f := f) (by
        intro t ht
        rw [Real.norm_eq_abs]
        exact hbound t (by
          change t ∈ Set.uIoc (boundary N j) (boundary N (j - 1)) at ht
          rw [Set.uIoc_of_le hab] at ht
          exact ⟨ht.1.le, ht.2⟩))
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using h
  have hwidth := boundary_width hN hj1
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmass : (N : ℝ) / 2 *
      (boundary N (j - 1) - boundary N j) = population N j := by
    rw [hwidth]
    field_simp
    ring
  unfold bandError
  calc
    |(N : ℝ) / 2 * (∫ t in boundary N j..boundary N (j - 1), f t) -
        (population N j : ℝ) * f (height N j)| ≤
        |(N : ℝ) / 2 * (∫ t in boundary N j..boundary N (j - 1), f t)| +
          |(population N j : ℝ) * f (height N j)| := by
            simpa [sub_eq_add_neg] using abs_add_le
              ((N : ℝ) / 2 * (∫ t in boundary N j..boundary N (j - 1), f t))
              (-(population N j : ℝ) * f (height N j))
    _ ≤ (N : ℝ) / 2 * (C * (boundary N (j - 1) - boundary N j)) +
          (population N j : ℝ) * C := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / 2),
              abs_of_nonneg (by positivity : 0 ≤ (population N j : ℝ))]
            gcongr
            exact hbound _ hmid
    _ = 2 * (population N j : ℝ) * C := by
      calc
        _ = ((N : ℝ) / 2 * (boundary N (j - 1) - boundary N j)) * C +
            (population N j : ℝ) * C := by ring
        _ = _ := by rw [hmass]; ring

/-- Bounding a kernel on the literal rectangle bounds its tensor band error. -/
theorem abs_bandBlock_le_of_rectangle_bound {N j k : ℕ}
    (hN : 4 ≤ N) (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (G : ℝ × ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s ∈ band N j, ∀ t ∈ band N k, |G (s,t)| ≤ C) :
    |bandBlock N j k G| ≤
      4 * (population N j : ℝ) * (population N k : ℝ) * C := by
  unfold bandBlock
  have hinner : ∀ s ∈ band N j,
      |bandError N k (fun t ↦ G (s,t))| ≤
        2 * (population N k : ℝ) * C := by
    intro s hs
    exact abs_bandError_le_of_band_bound hN hk1 hk2 _ hC (hbound s hs)
  have hD : 0 ≤ 2 * (population N k : ℝ) * C := by positivity
  calc
    |bandError N j (fun s ↦ bandError N k (fun t ↦ G (s,t)))| ≤
        2 * (population N j : ℝ) *
          (2 * (population N k : ℝ) * C) :=
      abs_bandError_le_of_band_bound hN hj1 hj2 _ hD hinner
    _ = _ := by ring

theorem abs_kernelBlock_le_of_rectangle_bound {N j k : ℕ}
    (hN : 4 ≤ N) (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (α : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s ∈ band N j, ∀ t ∈ band N k,
      |latitudeKernel α s t| ≤ C) :
    |kernelBlock α N j k| ≤
      4 * (population N j : ℝ) * (population N k : ℝ) * C := by
  exact abs_bandBlock_le_of_rectangle_bound hN hj1 hj2 hk1 hk2
    (fun p ↦ latitudeKernel α p.1 p.2) hC hbound

/-- Equality of kernels on the literal rectangle suffices for equality of
their band tensors. -/
theorem kernelBlock_eq_bandBlock_of_eqOn_rectangle
    {N : ℕ} (hN : 4 ≤ N) (j k : RingIndex N) (α : ℝ)
    (G : ℝ × ℝ → ℝ)
    (hG : ∀ s ∈ band N (j.val + 1), ∀ t ∈ band N (k.val + 1),
      G (s,t) = latitudeKernel α s t) :
    kernelBlock α N (j.val + 1) (k.val + 1) =
      bandBlock N (j.val + 1) (k.val + 1) G := by
  unfold kernelBlock bandBlock
  apply bandError_congr_on_band hN j
  intro s hs
  apply bandError_congr_on_band hN k
  intro t ht
  exact (hG s hs t ht).symm

/-- A smooth extension of the actual latitude kernel can be fed directly to
the proved two-moment Taylor estimate. -/
theorem kernelBlock_le_of_smooth_extension
    {N : ℕ} (hN : 4 ≤ N) (j k : RingIndex N) (α : ℝ)
    (G : ℝ × ℝ → ℝ) (W : Set (ℝ × ℝ))
    (hW : IsOpen W)
    (hrect : band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ W)
    (hG : ContDiffOn ℝ 4 G W)
    (heq : ∀ s ∈ band N (j.val + 1), ∀ t ∈ band N (k.val + 1),
      G (s,t) = latitudeKernel α s t)
    (L : ℝ) (hL : 0 ≤ L)
    (hfourth : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      |mixedFourth G p.1 p.2| ≤ L) :
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
      (population N (j.val + 1) : ℝ) ^ 3 *
        (population N (k.val + 1) : ℝ) ^ 3 /
          (bandParameter N : ℝ) ^ 8 * L := by
  rw [kernelBlock_eq_bandBlock_of_eqOn_rectangle hN j k α G heq]
  exact mixedTaylorBound N hN j k G W hW hrect hG L hL hfourth

theorem bandParameter_ge_two_of_ge_1024 {N : ℕ} (hN : 1024 ≤ N) :
    2 ≤ bandParameter N := by
  by_contra h
  have hb := (bandParameter_bounds N).2
  have hsmall : bandParameter N ≤ 1 := by omega
  interval_cases hparam : bandParameter N
  · norm_num [hparam] at hb
    omega
  · norm_num [hparam] at hb
    omega

theorem bandParameter_ge_sixteen_of_ge_1024 {N : ℕ} (hN : 1024 ≤ N) :
    16 ≤ bandParameter N := by
  by_contra h
  have hm : bandParameter N ≤ 15 := by omega
  have hb := (bandParameter_bounds N).2
  nlinarith

/-- A population at most 32 can only occur among the first or last eight
occupied bands when `M≥16`. -/
theorem small_population_index_is_polar {N q : ℕ} (hN : 1024 ≤ N)
    (hq1 : 1 ≤ q) (hq2 : q < 2 * bandParameter N)
    (hpop : population N q ≤ 32) :
    q ≤ 8 ∨ 2 * bandParameter N - q ≤ 8 := by
  let M := bandParameter N
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  rcases lt_trichotomy q M with hnorth | hcenter | hsouth
  · left
    rw [north_population N q hnorth] at hpop
    omega
  · subst q
    have hc := (central_population_bounds (by omega : 4 ≤ N)).1
    dsimp [M] at *
    omega
  · right
    rw [south_population N q hsouth] at hpop
    omega

theorem population_first_eq_four {N : ℕ} (hN : 1024 ≤ N) :
    population N 1 = 4 :=
  north_population N 1 (by have hM := bandParameter_ge_sixteen_of_ge_1024 hN; omega)

theorem population_last_eq_four {N : ℕ} (hN : 1024 ≤ N) :
    population N (2 * bandParameter N - 1) = 4 := by
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  rw [south_population N (2 * bandParameter N - 1)
    (by omega : bandParameter N < 2 * bandParameter N - 1)]
  have hsub : 2 * bandParameter N - (2 * bandParameter N - 1) = 1 := by omega
  rw [hsub]

/-- Comparable populations with either index at an endpoint force both
indices into the finite polar corner regions. -/
theorem comparable_endpoint_indices_polar {N j k : ℕ} (hN : 1024 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (hcomp : Comparable N j k)
    (hend : j = 1 ∨ j = 2 * bandParameter N - 1 ∨
      k = 1 ∨ k = 2 * bandParameter N - 1) :
    (j ≤ 8 ∨ 2 * bandParameter N - j ≤ 8) ∧
      (k ≤ 8 ∨ 2 * bandParameter N - k ≤ 8) := by
  dsimp [Comparable] at hcomp
  have hpop : population N j ≤ 32 ∧ population N k ≤ 32 := by
    rcases hend with hj | hj | hk | hk
    · rw [hj, population_first_eq_four hN] at hcomp ⊢
      norm_num at hcomp
      constructor
      · omega
      · exact_mod_cast hcomp.2
    · rw [hj, population_last_eq_four hN] at hcomp ⊢
      norm_num at hcomp
      constructor
      · omega
      · exact_mod_cast hcomp.2
    · rw [hk, population_first_eq_four hN] at hcomp ⊢
      constructor
      · exact_mod_cast (show (population N j : ℝ) ≤ 32 by linarith [hcomp.1])
      · omega
    · rw [hk, population_last_eq_four hN] at hcomp ⊢
      constructor
      · exact_mod_cast (show (population N j : ℝ) ≤ 32 by linarith [hcomp.1])
      · omega
  exact ⟨small_population_index_is_polar hN hj1 hj2 hpop.1,
    small_population_index_is_polar hN hk1 hk2 hpop.2⟩

/-- In the first north-polar band, the height is within `8/N` of the pole. -/
theorem north_first_band_height_bounds {N : ℕ} (hN : 1024 ≤ N)
    {s : ℝ} (hs : s ∈ band N 1) :
    0 ≤ s ∧ s ≤ 1 ∧ 1 - s ≤ 8 / (N : ℝ) := by
  have hM := bandParameter_ge_two_of_ge_1024 hN
  have hb : boundary N 1 = 1 - 8 / (N : ℝ) := by
    rw [north_boundary (by omega : 4 ≤ N) (by omega : 1 < bandParameter N)]
    ring
  have hs' : 1 - 8 / (N : ℝ) ≤ s ∧ s ≤ 1 := by
    simpa [band, hb, boundary_zero] using hs
  have hNr : (1024 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < N := by positivity
  have hdiv : 0 ≤ 8 / (N : ℝ) ∧ 8 / (N : ℝ) ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_iff₀ hNr0).2 (by linarith)
  constructor
  · linarith
  constructor
  · exact hs'.2
  · linarith

/-- Every one of the first eight bands stays within `288/N` of the north pole. -/
theorem north_small_band_height_bounds {N k : ℕ} (hN : 1024 ≤ N)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {t : ℝ} (ht : t ∈ band N k) :
    0 ≤ t ∧ t ≤ 1 ∧ 1 - t ≤ 288 / (N : ℝ) := by
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  have hkM : k < bandParameter N := by omega
  have hb : boundary N k = 1 - 4 * (k : ℝ) * (k + 1) / N :=
    north_boundary (by omega : 4 ≤ N) hkM
  have hprev : k - 1 < 2 * bandParameter N := by omega
  have hupper : boundary N (k - 1) ≤ 1 :=
    boundary_le_one (by omega : 4 ≤ N) hprev
  have ht' : 1 - 4 * (k : ℝ) * (k + 1) / N ≤ t ∧ t ≤ 1 := by
    have h := ht
    dsimp [band] at h
    rw [hb] at h
    exact ⟨h.1, h.2.trans hupper⟩
  have hkr : (k : ℝ) ≤ 8 := by exact_mod_cast hk8
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsmall : 4 * (k : ℝ) * (k + 1) ≤ 288 := by nlinarith [hk1]
  have hdiv : 4 * (k : ℝ) * (k + 1) / N ≤ 288 / (N : ℝ) :=
    div_le_div_of_nonneg_right hsmall hNr.le
  have hNr1024 : (1024 : ℝ) ≤ N := by exact_mod_cast hN
  have htotal : 288 / (N : ℝ) ≤ 1 :=
    (div_le_iff₀ hNr).2 (by linarith)
  constructor
  · linarith
  constructor
  · exact ht'.2
  · linarith

/-- Squared chordal distance between two points in the first polar band is
at most `64/N`, uniformly in angular separation. -/
theorem north_first_band_chord_sq_le {N : ℕ} (hN : 1024 ≤ N)
    {s t θ : ℝ} (hs : s ∈ band N 1) (ht : t ∈ band N 1) :
    2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ ≤ 64 / (N : ℝ) := by
  have hsb := north_first_band_height_bounds hN hs
  have htb := north_first_band_height_bounds hN ht
  have hNr : (0 : ℝ) < N := by positivity
  have hsa : 0 ≤ 1 - s ^ 2 := by nlinarith [hsb.1, hsb.2.1]
  have hta : 0 ≤ 1 - t ^ 2 := by nlinarith [htb.1, htb.2.1]
  have hsrad : 1 - s ^ 2 ≤ 16 / (N : ℝ) := by
    calc
      1 - s ^ 2 = (1 - s) * (1 + s) := by ring
      _ ≤ 8 / (N : ℝ) * (1 + s) :=
        mul_le_mul_of_nonneg_right hsb.2.2 (by linarith)
      _ ≤ 8 / (N : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 16 / (N : ℝ) := by ring
  have htrad : 1 - t ^ 2 ≤ 16 / (N : ℝ) := by
    calc
      1 - t ^ 2 = (1 - t) * (1 + t) := by ring
      _ ≤ 8 / (N : ℝ) * (1 + t) :=
        mul_le_mul_of_nonneg_right htb.2.2 (by linarith)
      _ ≤ 8 / (N : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 16 / (N : ℝ) := by ring
  have hrad : 0 ≤ Real.sqrt (1 - s ^ 2) := Real.sqrt_nonneg _
  have hrad' : 0 ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
  have hsq := sq_nonneg (Real.sqrt (1 - s ^ 2) - Real.sqrt (1 - t ^ 2))
  rw [sub_sq, Real.sq_sqrt hsa, Real.sq_sqrt hta] at hsq
  have hcos := Real.neg_one_le_cos θ
  have hxy := mul_nonneg (sub_nonneg.mpr hsb.2.1) (sub_nonneg.mpr htb.2.1)
  have hcosprod := mul_le_mul_of_nonneg_left hcos
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hrad hrad'))
  have hfirst : 2 - 2 * s * t ≤ 32 / (N : ℝ) := by
    calc
      2 - 2 * s * t ≤ 2 * ((1 - s) + (1 - t)) := by nlinarith [hxy]
      _ ≤ 2 * (8 / (N : ℝ) + 8 / (N : ℝ)) := by
        gcongr
        · exact hsb.2.2
        · exact htb.2.2
      _ = 32 / (N : ℝ) := by ring
  have hsecond : -(2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ) ≤ 32 / (N : ℝ) := by
    calc
      _ ≤ 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) := by
        nlinarith [hcosprod]
      _ ≤ (1 - s ^ 2) + (1 - t ^ 2) := by nlinarith [hsq]
      _ ≤ 16 / (N : ℝ) + 16 / (N : ℝ) := add_le_add hsrad htrad
      _ = 32 / (N : ℝ) := by ring
  calc
    _ = (2 - 2 * s * t) +
        (-(2 * Real.sqrt (1 - s ^ 2) *
          Real.sqrt (1 - t ^ 2) * Real.cos θ)) := by ring
    _ ≤ 32 / (N : ℝ) + 32 / (N : ℝ) := add_le_add hfirst hsecond
    _ = 64 / (N : ℝ) := by ring

/-- The latitude kernel on the first polar square is at its natural
`N^{-α/2}` scale. -/
theorem north_first_band_latitudeKernel_bound {N : ℕ} (hN : 1024 ≤ N)
    {α : ℝ} (hα : 0 < α) {s t : ℝ}
    (hs : s ∈ band N 1) (ht : t ∈ band N 1) :
    |latitudeKernel α s t| ≤ (64 / (N : ℝ)) ^ (α / 2) := by
  have hsb := north_first_band_height_bounds hN hs
  have htb := north_first_band_height_bounds hN ht
  have hsunit : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hsb.1], hsb.2.1⟩
  have htunit : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [htb.1], htb.2.1⟩
  have hbase (θ : ℝ) : 0 ≤ 2 - 2 * s * t -
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * Real.cos θ := by
    have hdist := parallelPoint_dist_sq hsunit htunit (θ := θ) (φ := 0)
    simpa [Real.cos_neg] using (sq_nonneg (dist (parallelPoint s θ hsunit)
      (parallelPoint t 0 htunit))) |>.trans_eq hdist
  have hprof (θ : ℝ) :
      0 ≤ latitudeProfile α s t θ ∧
        latitudeProfile α s t θ ≤ (64 / (N : ℝ)) ^ (α / 2) := by
    unfold latitudeProfile
    exact ⟨Real.rpow_nonneg (hbase θ) _,
      Real.rpow_le_rpow (hbase θ) (north_first_band_chord_sq_le hN hs ht) (by linarith)⟩
  have hzero : 0 ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, latitudeProfile α s t θ := by
    exact intervalIntegral.integral_nonneg (by positivity) (fun θ _ ↦ (hprof θ).1)
  have hcont : Continuous (latitudeProfile α s t) :=
    (continuous_latitudeProfile hα).comp
      ((continuous_const.prodMk continuous_const).prodMk continuous_id)
  have htop : (∫ θ in (0 : ℝ)..2 * Real.pi, latitudeProfile α s t θ) ≤
      ∫ _θ in (0 : ℝ)..2 * Real.pi, (64 / (N : ℝ)) ^ (α / 2) := by
    exact intervalIntegral.integral_mono_on (by positivity)
      (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (fun θ _ ↦ (hprof θ).2)
  rw [latitudeKernel_eq_profile_integral]
  rw [abs_of_nonneg (mul_nonneg (by positivity) hzero)]
  rw [intervalIntegral.integral_const] at htop
  simp only [smul_eq_mul] at htop
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hnorm : (1 / (2 * Real.pi)) * ((2 * Real.pi) * (64 / (N : ℝ)) ^ (α / 2)) =
      (64 / (N : ℝ)) ^ (α / 2) := by field_simp
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((2 * Real.pi) *
        (64 / (N : ℝ)) ^ (α / 2)) := by
          apply mul_le_mul_of_nonneg_left
          simpa using htop
          positivity
    _ = _ := hnorm

/-- The literal first-band diagonal tensor has its polar `N^{-α/2}` size. -/
theorem north_first_diagonal_block_bound {N : ℕ} (hN : 1024 ≤ N)
    {α : ℝ} (hα : 0 < α) :
    |kernelBlock α N 1 1| ≤ 64 * (64 / (N : ℝ)) ^ (α / 2) := by
  have hM := bandParameter_ge_two_of_ge_1024 hN
  have hpop : population N 1 = 4 :=
    north_population N 1 (by omega : 1 < bandParameter N)
  have h := abs_kernelBlock_le_of_rectangle_bound
    (by omega : 4 ≤ N) (by omega : 1 ≤ 1)
    (by omega : 1 < 2 * bandParameter N)
    (by omega : 1 ≤ 1) (by omega : 1 < 2 * bandParameter N)
    α (Real.rpow_nonneg (by positivity : 0 ≤ 64 / (N : ℝ)) _)
    (fun s hs t ht ↦ north_first_band_latitudeKernel_bound hN hα hs ht)
  rw [hpop] at h
  norm_num at h ⊢
  exact h

/-- The first diagonal block satisfies the manuscript's comparable majorant. -/
theorem north_first_diagonal_comparable_bound {N : ℕ} (hN : 1024 ≤ N)
    {α : ℝ} (hα : 0 < α) :
    |kernelBlock α N 1 1| ≤
      (16 * (4 : ℝ) ^ α) * (population N 1 : ℝ) /
        (bandParameter N : ℝ) ^ α := by
  let M := bandParameter N
  have hM : (0 : ℝ) < M := by
    have hMnat : 0 < M := by
      have hm := bandParameter_ge_two_of_ge_1024 hN
      dsimp [M]
      omega
    exact_mod_cast hMnat
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb : 4 * (M : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hbase : 64 / (N : ℝ) ≤ 16 / (M : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ hNr (sq_pos_of_pos hM)).2
    nlinarith [hb]
  have hpow : (64 / (N : ℝ)) ^ (α / 2) ≤
      (16 / (M : ℝ) ^ 2) ^ (α / 2) :=
    Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hrewrite : (16 / (M : ℝ) ^ 2) ^ (α / 2) =
      (4 : ℝ) ^ α / (M : ℝ) ^ α := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg (M : ℝ))]
    rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    congr 1 <;> ring
  have hpop : population N 1 = 4 :=
    north_population N 1 (by have h := bandParameter_ge_two_of_ge_1024 hN; omega)
  calc
    |kernelBlock α N 1 1| ≤ 64 * (64 / (N : ℝ)) ^ (α / 2) :=
      north_first_diagonal_block_bound hN hα
    _ ≤ 64 * (16 / (M : ℝ) ^ 2) ^ (α / 2) := by gcongr
    _ = 64 * ((4 : ℝ) ^ α / (M : ℝ) ^ α) := by rw [hrewrite]
    _ = (16 * (4 : ℝ) ^ α) * (population N 1 : ℝ) /
        (bandParameter N : ℝ) ^ α := by rw [hpop]; dsimp [M]; ring

theorem latitudeKernel_neg_neg (α s t : ℝ) :
    latitudeKernel α (-s) (-t) = latitudeKernel α s t := by
  unfold latitudeKernel
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [neg_sq, neg_mul_neg]
  congr 1
  ring

/-- Reflection sends the last south-polar band to the first north-polar band. -/
theorem south_last_band_neg_mem_north_first {N : ℕ} (hN : 1024 ≤ N)
    {s : ℝ} (hs : s ∈ band N (2 * bandParameter N - 1)) :
    -s ∈ band N 1 := by
  let M := bandParameter N
  have hM := bandParameter_ge_two_of_ge_1024 hN
  have hlast : boundary N (2 * M - 1) = -1 :=
    boundary_last (by omega : 4 ≤ N)
  have href := boundary_reflect (N := N) (j := 1)
    (by omega : 4 ≤ N) (by omega : 1 ≤ 2 * M - 1)
  have hidx : 2 * M - 1 - 1 = 2 * M - 2 := by omega
  have hpred : (2 * M - 1) - 1 = 2 * M - 2 := by omega
  rw [hidx] at href
  have hs' : -1 ≤ s ∧ s ≤ -boundary N 1 := by
    simpa [band, M, hlast, hpred, href] using hs
  have hboundary : boundary N 0 = 1 := boundary_zero N
  change boundary N 1 ≤ -s ∧ -s ≤ boundary N 0
  rw [hboundary]
  constructor <;> linarith [hs'.1, hs'.2]

theorem south_last_diagonal_block_bound {N : ℕ} (hN : 1024 ≤ N)
    {α : ℝ} (hα : 0 < α) :
    |kernelBlock α N (2 * bandParameter N - 1)
      (2 * bandParameter N - 1)| ≤
      64 * (64 / (N : ℝ)) ^ (α / 2) := by
  let M := bandParameter N
  have hM := bandParameter_ge_two_of_ge_1024 hN
  have hj1 : 1 ≤ 2 * M - 1 := by omega
  have hj2 : 2 * M - 1 < 2 * M := by omega
  have hpop : population N (2 * M - 1) = 4 := by
    rw [south_population N (2 * M - 1) (by omega : M < 2 * M - 1)]
    have hsub : 2 * M - (2 * M - 1) = 1 := by omega
    rw [hsub]
  have h := abs_kernelBlock_le_of_rectangle_bound
    (by omega : 4 ≤ N) hj1 hj2 hj1 hj2 α
    (Real.rpow_nonneg (by positivity : 0 ≤ 64 / (N : ℝ)) _)
    (fun s hs t ht ↦ by
      rw [← latitudeKernel_neg_neg α s t]
      exact north_first_band_latitudeKernel_bound hN hα
        (south_last_band_neg_mem_north_first hN hs)
        (south_last_band_neg_mem_north_first hN ht))
  dsimp [M] at hpop ⊢
  rw [hpop] at h
  norm_num at h ⊢
  exact h

theorem south_last_diagonal_comparable_bound {N : ℕ} (hN : 1024 ≤ N)
    {α : ℝ} (hα : 0 < α) :
    |kernelBlock α N (2 * bandParameter N - 1)
      (2 * bandParameter N - 1)| ≤
      (16 * (4 : ℝ) ^ α) *
        (population N (2 * bandParameter N - 1) : ℝ) /
          (bandParameter N : ℝ) ^ α := by
  let M := bandParameter N
  have hMnat := bandParameter_ge_two_of_ge_1024 hN
  have hM : (0 : ℝ) < M := by
    have hm : 0 < M := by dsimp [M]; omega
    exact_mod_cast hm
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb : 4 * (M : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hbase : 64 / (N : ℝ) ≤ 16 / (M : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ hNr (sq_pos_of_pos hM)).2
    nlinarith [hb]
  have hpow : (64 / (N : ℝ)) ^ (α / 2) ≤
      (16 / (M : ℝ) ^ 2) ^ (α / 2) :=
    Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hrewrite : (16 / (M : ℝ) ^ 2) ^ (α / 2) =
      (4 : ℝ) ^ α / (M : ℝ) ^ α := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg (M : ℝ))]
    rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    congr 1 <;> ring
  have hpop : population N (2 * M - 1) = 4 := by
    rw [south_population N (2 * M - 1) (by omega : M < 2 * M - 1)]
    have hsub : 2 * M - (2 * M - 1) = 1 := by omega
    rw [hsub]
  calc
    |kernelBlock α N (2 * bandParameter N - 1)
      (2 * bandParameter N - 1)| ≤
        64 * (64 / (N : ℝ)) ^ (α / 2) :=
      south_last_diagonal_block_bound hN hα
    _ ≤ 64 * (16 / (M : ℝ) ^ 2) ^ (α / 2) := by gcongr
    _ = 64 * ((4 : ℝ) ^ α / (M : ℝ) ^ α) := by rw [hrewrite]
    _ = (16 * (4 : ℝ) ^ α) *
        (population N (2 * bandParameter N - 1) : ℝ) /
          (bandParameter N : ℝ) ^ α := by rw [hpop]; dsimp [M]; ring

/-- Chordal distance estimate for two heights within `q` of the north pole. -/
theorem polar_chord_sq_le_of_height {s t q θ : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hsq : 1 - s ≤ q) (htq : 1 - t ≤ q) (hq : 0 ≤ q) :
    2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ ≤ 8 * q := by
  have hsa : 0 ≤ 1 - s ^ 2 := by nlinarith
  have hta : 0 ≤ 1 - t ^ 2 := by nlinarith
  have hsrad : 1 - s ^ 2 ≤ 2 * q := by
    calc
      1 - s ^ 2 = (1 - s) * (1 + s) := by ring
      _ ≤ q * (1 + s) := mul_le_mul_of_nonneg_right hsq (by linarith)
      _ ≤ q * 2 := mul_le_mul_of_nonneg_left (by linarith) hq
      _ = 2 * q := by ring
  have htrad : 1 - t ^ 2 ≤ 2 * q := by
    calc
      1 - t ^ 2 = (1 - t) * (1 + t) := by ring
      _ ≤ q * (1 + t) := mul_le_mul_of_nonneg_right htq (by linarith)
      _ ≤ q * 2 := mul_le_mul_of_nonneg_left (by linarith) hq
      _ = 2 * q := by ring
  have hrad : 0 ≤ Real.sqrt (1 - s ^ 2) := Real.sqrt_nonneg _
  have hrad' : 0 ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
  have hroot := sq_nonneg (Real.sqrt (1 - s ^ 2) - Real.sqrt (1 - t ^ 2))
  rw [sub_sq, Real.sq_sqrt hsa, Real.sq_sqrt hta] at hroot
  have hcos := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hrad hrad'))
  have hxy := mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr ht1)
  have hfirst : 2 - 2 * s * t ≤ 4 * q := by
    calc
      _ ≤ 2 * ((1 - s) + (1 - t)) := by nlinarith [hxy]
      _ ≤ 2 * (q + q) := by gcongr
      _ = 4 * q := by ring
  have hsecond : -(2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ) ≤ 4 * q := by
    calc
      _ ≤ 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) := by
        nlinarith [hcos]
      _ ≤ (1 - s ^ 2) + (1 - t ^ 2) := by nlinarith [hroot]
      _ ≤ 2 * q + 2 * q := add_le_add hsrad htrad
      _ = 4 * q := by ring
  calc
    _ = (2 - 2 * s * t) +
        (-(2 * Real.sqrt (1 - s ^ 2) *
          Real.sqrt (1 - t ^ 2) * Real.cos θ)) := by ring
    _ ≤ 4 * q + 4 * q := add_le_add hfirst hsecond
    _ = 8 * q := by ring

theorem north_small_bands_chord_sq_le {N j k : ℕ} (hN : 1024 ≤ N)
    (hj1 : 1 ≤ j) (hj8 : j ≤ 8) (hk1 : 1 ≤ k) (hk8 : k ≤ 8)
    {s t θ : ℝ} (hs : s ∈ band N j) (ht : t ∈ band N k) :
    2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ ≤ 2304 / (N : ℝ) := by
  have hs' := north_small_band_height_bounds hN hj1 hj8 hs
  have ht' := north_small_band_height_bounds hN hk1 hk8 ht
  have h := polar_chord_sq_le_of_height (θ := θ) hs'.1 hs'.2.1 ht'.1 ht'.2.1
    hs'.2.2 ht'.2.2 (by positivity : 0 ≤ 288 / (N : ℝ))
  convert h using 1; ring

/-- A uniform chord-square bound controls the actual angular average. -/
theorem latitudeKernel_abs_le_of_chord_sq {α s t B : ℝ}
    (hα : 0 < α) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (_hB : 0 ≤ B)
    (hchord : ∀ θ : ℝ,
      2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
        Real.sqrt (1 - t ^ 2) * Real.cos θ ≤ B) :
    |latitudeKernel α s t| ≤ B ^ (α / 2) := by
  have hbase (θ : ℝ) : 0 ≤ 2 - 2 * s * t -
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * Real.cos θ := by
    have hdist := parallelPoint_dist_sq hs ht (θ := θ) (φ := 0)
    simpa [Real.cos_neg] using (sq_nonneg (dist (parallelPoint s θ hs)
      (parallelPoint t 0 ht))) |>.trans_eq hdist
  have hprof (θ : ℝ) :
      0 ≤ latitudeProfile α s t θ ∧ latitudeProfile α s t θ ≤ B ^ (α / 2) := by
    unfold latitudeProfile
    exact ⟨Real.rpow_nonneg (hbase θ) _,
      Real.rpow_le_rpow (hbase θ) (hchord θ) (by linarith)⟩
  have hzero : 0 ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, latitudeProfile α s t θ :=
    intervalIntegral.integral_nonneg (by positivity) (fun θ _ ↦ (hprof θ).1)
  have hcont : Continuous (latitudeProfile α s t) :=
    (continuous_latitudeProfile hα).comp
      ((continuous_const.prodMk continuous_const).prodMk continuous_id)
  have htop : (∫ θ in (0 : ℝ)..2 * Real.pi, latitudeProfile α s t θ) ≤
      ∫ _θ in (0 : ℝ)..2 * Real.pi, B ^ (α / 2) :=
    intervalIntegral.integral_mono_on (by positivity)
      (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (fun θ _ ↦ (hprof θ).2)
  rw [latitudeKernel_eq_profile_integral]
  rw [abs_of_nonneg (mul_nonneg (by positivity) hzero)]
  rw [intervalIntegral.integral_const] at htop
  simp only [smul_eq_mul] at htop
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((2 * Real.pi) * B ^ (α / 2)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa using htop
      · positivity
    _ = _ := by field_simp

theorem north_small_bands_latitudeKernel_bound {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {α s t : ℝ} (hα : 0 < α)
    (hs : s ∈ band N j) (ht : t ∈ band N k) :
    |latitudeKernel α s t| ≤ (2304 / (N : ℝ)) ^ (α / 2) := by
  have hsb := north_small_band_height_bounds hN hj1 hj8 hs
  have htb := north_small_band_height_bounds hN hk1 hk8 ht
  exact latitudeKernel_abs_le_of_chord_sq hα
    ⟨by linarith [hsb.1], hsb.2.1⟩
    ⟨by linarith [htb.1], htb.2.1⟩
    (by positivity)
    (fun θ ↦ north_small_bands_chord_sq_le hN hj1 hj8 hk1 hk8 hs ht)

theorem north_small_bands_block_bound {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {α : ℝ} (hα : 0 < α) :
    |kernelBlock α N j k| ≤
      4 * (population N j : ℝ) * (population N k : ℝ) *
        (2304 / (N : ℝ)) ^ (α / 2) := by
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  exact abs_kernelBlock_le_of_rectangle_bound
    (by omega : 4 ≤ N) hj1 (by omega : j < 2 * bandParameter N)
    hk1 (by omega : k < 2 * bandParameter N) α
    (Real.rpow_nonneg (by positivity : 0 ≤ 2304 / (N : ℝ)) _)
    (fun s hs t ht ↦ north_small_bands_latitudeKernel_bound hN
      hj1 hj8 hk1 hk8 hα hs ht)

/-- The first eight north-polar bands satisfy the exact comparable majorant. -/
theorem north_small_bands_comparable_bound {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    |kernelBlock α N j k| ≤
      (65536 * (24 : ℝ) ^ α) * (population N j : ℝ) /
        (bandParameter N : ℝ) ^ α *
          (1 + |(j : ℝ) - k|) ^ (α - 3) := by
  let M := bandParameter N
  have hMnat := bandParameter_ge_sixteen_of_ge_1024 hN
  have hM : (0 : ℝ) < M := by
    have hm : 0 < M := by dsimp [M]; omega
    exact_mod_cast hm
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb : 4 * (M : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hbase : 2304 / (N : ℝ) ≤ 576 / (M : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ hNr (sq_pos_of_pos hM)).2
    nlinarith [hb]
  have hpow : (2304 / (N : ℝ)) ^ (α / 2) ≤
      (576 / (M : ℝ) ^ 2) ^ (α / 2) :=
    Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hrewrite : (576 / (M : ℝ) ^ 2) ^ (α / 2) =
      (24 : ℝ) ^ α / (M : ℝ) ^ α := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 576) (sq_nonneg (M : ℝ))]
    rw [show (576 : ℝ) = 24 ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 24)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    congr 1 <;> ring
  have hkM : k < M := by omega
  have hpopk : (population N k : ℝ) ≤ 32 := by
    rw [north_population N k hkM]
    exact_mod_cast (by omega : 4 * k ≤ 32)
  have hjr : (j : ℝ) ≤ 8 := by exact_mod_cast hj8
  have hkr : (k : ℝ) ≤ 8 := by exact_mod_cast hk8
  have hjr1 : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hkr1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  let d : ℝ := 1 + |(j : ℝ) - k|
  have hd1 : 0 < d := by dsimp [d]; positivity
  have hd8 : d ≤ 8 := by
    have hdabs : |(j : ℝ) - k| ≤ 7 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    dsimp [d]
    linarith
  have hfactor : (1 / 512 : ℝ) ≤ d ^ (α - 3) := by
    have hle := Real.rpow_le_rpow_of_nonpos hd1 hd8 (by linarith : α - 3 ≤ 0)
    have hexp := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 8) (by linarith : (-3 : ℝ) ≤ α - 3)
    have hn : (8 : ℝ) ^ (-3 : ℝ) = 1 / 512 := by norm_num
    rw [← hn]
    exact hexp.trans hle
  have hpJ : 0 ≤ (population N j : ℝ) := by positivity
  have hpowM : 0 < (M : ℝ) ^ α := Real.rpow_pos_of_pos hM _
  have hpow24 : 0 ≤ (24 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  calc
    |kernelBlock α N j k| ≤
        4 * (population N j : ℝ) * (population N k : ℝ) *
          (2304 / (N : ℝ)) ^ (α / 2) :=
      north_small_bands_block_bound hN hj1 hj8 hk1 hk8 hα0
    _ ≤ 4 * (population N j : ℝ) * (population N k : ℝ) *
          ((24 : ℝ) ^ α / (M : ℝ) ^ α) := by
            rw [← hrewrite]
            gcongr
    _ ≤ 128 * (population N j : ℝ) *
          ((24 : ℝ) ^ α / (M : ℝ) ^ α) := by
            have hcoef : 4 * (population N j : ℝ) *
                (population N k : ℝ) ≤ 128 * (population N j : ℝ) := by
              nlinarith [mul_nonneg hpJ (by linarith : 0 ≤ 32 - (population N k : ℝ))]
            exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ (65536 * (24 : ℝ) ^ α) * (population N j : ℝ) /
          (M : ℝ) ^ α * d ^ (α - 3) := by
            have hmul := mul_le_mul_of_nonneg_left hfactor
              (by positivity : 0 ≤ 65536 * (24 : ℝ) ^ α *
                (population N j : ℝ) / (M : ℝ) ^ α)
            calc
              _ = (65536 * (24 : ℝ) ^ α) * (population N j : ℝ) /
                    (M : ℝ) ^ α * (1 / 512) := by ring
              _ ≤ _ := hmul
    _ = _ := by dsimp [M, d]

/-- Height reflection identifies each of the last eight bands with its
northern partner. -/
theorem south_small_band_neg_mem_north_small {N q : ℕ}
    (hN : 1024 ≤ N) (hq1 : 1 ≤ q) (hq8 : q ≤ 8)
    {s : ℝ} (hs : s ∈ band N (2 * bandParameter N - q)) :
    -s ∈ band N q := by
  let M := bandParameter N
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  have hqM : q ≤ 2 * M - 1 := by omega
  have hqm : q - 1 ≤ 2 * M - 1 := by omega
  have hrA := boundary_reflect (N := N) (j := q - 1)
    (by omega : 4 ≤ N) hqm
  have hrB := boundary_reflect (N := N) (j := q)
    (by omega : 4 ≤ N) hqM
  have hidxA : 2 * M - 1 - (q - 1) = 2 * M - q := by omega
  have hidxB : 2 * M - 1 - q = (2 * M - q) - 1 := by omega
  rw [hidxA] at hrA
  rw [hidxB] at hrB
  have hs' : boundary N (2 * M - q) ≤ s ∧
      s ≤ boundary N ((2 * M - q) - 1) := by
    simpa [band, M] using hs
  change boundary N q ≤ -s ∧ -s ≤ boundary N (q - 1)
  rw [hrA, hrB] at hs'
  constructor <;> linarith [hs'.1, hs'.2]

/-- Reflection of the signed midpoint band functional. -/
theorem bandError_reflect {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) (f : ℝ → ℝ) :
    bandError N (2 * bandParameter N - j) f =
      bandError N j (fun s ↦ f (-s)) := by
  let M := bandParameter N
  have hL : j ≤ 2 * M - 1 := by omega
  have hprev : j - 1 ≤ 2 * M - 1 := by omega
  have hrA := boundary_reflect hN (j := j - 1) hprev
  have hrB := boundary_reflect hN (j := j) hL
  have hidxA : 2 * M - 1 - (j - 1) = 2 * M - j := by omega
  have hidxB : 2 * M - 1 - j = (2 * M - j) - 1 := by omega
  rw [hidxA] at hrA
  rw [hidxB] at hrB
  have hheight := height_reflect hN hj1 hj2
  have hpop := population_reflect hN hj1 hj2
  unfold bandError
  rw [hrA, hrB, hheight, hpop]
  rw [intervalIntegral.integral_comp_neg]

theorem kernelBlock_reflect {N j k : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N) (α : ℝ) :
    kernelBlock α N (2 * bandParameter N - j)
      (2 * bandParameter N - k) = kernelBlock α N j k := by
  unfold kernelBlock bandBlock
  rw [bandError_reflect hN hj1 hj2]
  congr 1
  funext s
  rw [bandError_reflect hN hk1 hk2]
  congr 1
  funext t
  exact latitudeKernel_neg_neg α s t

theorem south_small_bands_comparable_bound {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    |kernelBlock α N (2 * bandParameter N - j)
      (2 * bandParameter N - k)| ≤
      (65536 * (24 : ℝ) ^ α) *
        (population N (2 * bandParameter N - j) : ℝ) /
          (bandParameter N : ℝ) ^ α *
            (1 + |((2 * bandParameter N - j : ℕ) : ℝ) -
              (2 * bandParameter N - k : ℕ)|) ^ (α - 3) := by
  let M := bandParameter N
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  have hj2 : j < 2 * M := by omega
  have hk2 : k < 2 * M := by omega
  have hjle : j ≤ 2 * M := by omega
  have hkle : k ≤ 2 * M := by omega
  have hpop := population_reflect (N := N) (j := j)
    (by omega : 4 ≤ N) hj1 hj2
  have habs : |((2 * M - j : ℕ) : ℝ) - (2 * M - k : ℕ)| =
      |(j : ℝ) - k| := by
    rw [Nat.cast_sub hjle, Nat.cast_sub hkle]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hring : (2 * (M : ℝ) - j) - (2 * (M : ℝ) - k) =
        (k : ℝ) - j := by ring
    rw [hring]
    exact abs_sub_comm _ _
  rw [kernelBlock_reflect (by omega : 4 ≤ N) hj1 hj2 hk1 hk2,
    hpop, habs]
  exact north_small_bands_comparable_bound hN hj1 hj8 hk1 hk8 hα0 hα2

theorem south_small_bands_block_bound {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {α : ℝ} (hα : 0 < α) :
    |kernelBlock α N (2 * bandParameter N - j)
      (2 * bandParameter N - k)| ≤
      4 * (population N (2 * bandParameter N - j) : ℝ) *
        (population N (2 * bandParameter N - k) : ℝ) *
          (2304 / (N : ℝ)) ^ (α / 2) := by
  let M := bandParameter N
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  have hjlow : 1 ≤ 2 * M - j := by omega
  have hjhigh : 2 * M - j < 2 * M := by omega
  have hklow : 1 ≤ 2 * M - k := by omega
  have hkhigh : 2 * M - k < 2 * M := by omega
  apply abs_kernelBlock_le_of_rectangle_bound
    (by omega : 4 ≤ N) hjlow hjhigh hklow hkhigh α
    (Real.rpow_nonneg (by positivity : 0 ≤ 2304 / (N : ℝ)) _)
  intro s hs t ht
  rw [← latitudeKernel_neg_neg α s t]
  exact north_small_bands_latitudeKernel_bound hN
    hj1 hj8 hk1 hk8 hα
    (south_small_band_neg_mem_north_small hN hj1 hj8 hs)
    (south_small_band_neg_mem_north_small hN hk1 hk8 ht)

/-- Opposite endpoint rectangles lie uniformly in the separated analytic
region of the averaged kernel. -/
theorem opposite_small_bands_separated {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {s t : ℝ}
    (hs : s ∈ band N j)
    (ht : t ∈ band N (2 * bandParameter N - k)) :
    0 < 2 - 2 * s * t ∧
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
        (1 - (1 / 4 : ℝ)) * (2 - 2 * s * t) := by
  have hsb := north_small_band_height_bounds hN hj1 hj8 hs
  have htb := north_small_band_height_bounds hN hk1 hk8
    (south_small_band_neg_mem_north_small hN hk1 hk8 ht)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNr1024 : (1024 : ℝ) ≤ N := by exact_mod_cast hN
  have hq : 288 / (N : ℝ) ≤ 1 / 2 :=
    (div_le_iff₀ hNr).2 (by linarith)
  have hs_half : (1 / 2 : ℝ) ≤ s := by linarith [hsb.2.2]
  have ht_half : t ≤ -(1 / 2 : ℝ) := by linarith [htb.2.2]
  have hsabs : s ^ 2 ≤ 1 := by nlinarith [hsb.1, hsb.2.1]
  have htabs : t ^ 2 ≤ 1 := by nlinarith [htb.1, htb.2.1]
  have hA : 0 ≤ 1 - s ^ 2 := by linarith
  have hB : 0 ≤ 1 - t ^ 2 := by linarith
  have hAupper : 1 - s ^ 2 ≤ 3 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
  have hBupper : 1 - t ^ 2 ≤ 3 / 4 := by nlinarith [sq_nonneg (t + 1 / 2)]
  have hroot := sq_nonneg (Real.sqrt (1 - s ^ 2) - Real.sqrt (1 - t ^ 2))
  rw [sub_sq, Real.sq_sqrt hA, Real.sq_sqrt hB] at hroot
  have hV : 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤ 3 / 2 := by
    nlinarith [hroot, hAupper, hBupper]
  have hprod : s * t ≤ -(1 / 4 : ℝ) := by
    have hm := mul_nonneg hsb.1 (by linarith : 0 ≤ -t - 1 / 2)
    nlinarith [hm, hs_half]
  have hU : (5 / 2 : ℝ) ≤ 2 - 2 * s * t := by linarith
  constructor
  · linarith
  · nlinarith [hV, hU]

/-- The fixed opposite-pole corner lies inside the global smooth-series domain. -/
theorem opposite_small_bands_mem_separatedOpen {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {s t : ℝ}
    (hs : s ∈ band N j)
    (ht : t ∈ band N (2 * bandParameter N - k)) :
    (s, t) ∈ separatedOpen := by
  obtain ⟨hU, hV⟩ := opposite_small_bands_separated hN hj1 hj8 hk1 hk8 hs ht
  have hsI : s ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := north_small_band_height_bounds hN hj1 hj8 hs
    constructor <;> linarith [h.1, h.2.1]
  have htI : t ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := north_small_band_height_bounds hN hk1 hk8
      (south_small_band_neg_mem_north_small hN hk1 hk8 ht)
    constructor <;> linarith [h.1, h.2.1]
  have hB : 0 ≤ angularKernelB s t := by
    unfold angularKernelB
    positivity
  have hBlt : angularKernelB s t < angularKernelA s t := by
    dsimp [angularKernelA, angularKernelB] at *
    nlinarith
  constructor
  · simpa only [angularKernelA] using hU
  · rw [← angularKernelB_sq_eq_four_radiusSq hsI htI]
    rw [abs_of_nonneg (sq_nonneg _)]
    have hA : 0 < angularKernelA s t := by
      simpa only [angularKernelA] using hU
    nlinarith [mul_pos (sub_pos.mpr hBlt) (by linarith : 0 < angularKernelA s t + angularKernelB s t)]

set_option maxHeartbeats 1000000 in
/-- A far comparable rectangle has a fixed separated angular ratio. The
generous constants keep the index geometry independent of the exponent. -/
theorem far_comparable_rectangle_separation {N : ℕ} (hN : 1024 ≤ N)
    (j k : RingIndex N)
    (hjfirst : j.val ≠ 0)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val ≠ 0)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    (hjk : 2 ≤ |(j.val : ℤ) - k.val|)
    (hfar : 2 * (population N (j.val + 1) : ℝ) <
      |(j.val : ℝ) - k.val|)
    {s t : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1)) :
    0 < angularKernelA s t ∧
      (|(j.val : ℝ) - k.val| / (bandParameter N : ℝ)) ^ 2 / 3600 ≤
        angularKernelA s t ∧
      angularKernelA s t ≤
        904 * (|(j.val : ℝ) - k.val| / (bandParameter N : ℝ)) ^ 2 ∧
      angularKernelB s t ≤
        (1 - (1 / 4000000 : ℝ)) * angularKernelA s t := by
  let M : ℝ := bandParameter N
  let d : ℝ := |(j.val : ℝ) - k.val| / M
  let r : ℝ := (population N (j.val + 1) : ℝ) / M
  let a : ℝ := Real.sqrt (1 - s ^ 2)
  let b : ℝ := Real.sqrt (1 - t ^ 2)
  let δ : ℝ := |Real.arccos s - Real.arccos t|
  let U : ℝ := angularKernelA s t
  let V : ℝ := angularKernelB s t
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (16 : ℕ))
      (bandParameter_ge_sixteen_of_ge_1024 hN))
  have hd0 : 0 ≤ d := div_nonneg (abs_nonneg _) hM.le
  have hr0 : 0 ≤ r := by positivity
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hδ0 : 0 ≤ δ := abs_nonneg _
  have hδ := separated_band_arccos_gap (by omega : 4 ≤ N)
    (bandParameter_ge_sixteen_of_ge_1024 hN) j k hjk hs ht
  have hδlo : d / 30 ≤ δ := by
    simpa [d, δ, M, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hδ.1
  have hδhi : δ ≤ 30 * d := by
    simpa [d, δ, M, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hδ.2
  have hRj := (band_radius_comparison (by omega : 4 ≤ N)
    (bandParameter_ge_sixteen_of_ge_1024 hN) j hjfirst hjlast hs).2
  have hRk := (band_radius_comparison (by omega : 4 ≤ N)
    (bandParameter_ge_sixteen_of_ge_1024 hN) k hkfirst hklast ht).2
  have hpopk : (population N (k.val + 1) : ℝ) ≤
      8 * population N (j.val + 1) := hcomp.2
  have ha : a ≤ r := by simpa [a, r, M] using hRj
  have hb : b ≤ 8 * r := by
    have h := div_le_div_of_nonneg_right hpopk hM.le
    calc
      b ≤ (population N (k.val + 1) : ℝ) / M := hRk
      _ ≤ 8 * r := by simpa [r, M, mul_div_assoc] using h
  have hfar' : 2 * r < d := by
    have h := div_lt_div_of_pos_right hfar hM
    simpa [r, d, M, mul_div_assoc] using h
  have hV : V ≤ 4 * d ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
    change 2 * a * b ≤ 4 * d ^ 2
    nlinarith [sq_nonneg (d - 2 * r)]
  have hsI : s ∈ Set.Icc (-1 : ℝ) 1 := by
    have hlo := boundary_ge_neg_one (by omega : 4 ≤ N)
      (by have := j.isLt; omega : j.val + 1 < 2 * bandParameter N)
    have hhi := boundary_le_one (by omega : 4 ≤ N) (by have := j.isLt; omega : j.val < 2 * bandParameter N)
    exact ⟨hlo.trans hs.1, hs.2.trans hhi⟩
  have htI : t ∈ Set.Icc (-1 : ℝ) 1 := by
    have hlo := boundary_ge_neg_one (by omega : 4 ≤ N)
      (by have := k.isLt; omega : k.val + 1 < 2 * bandParameter N)
    have hhi := boundary_le_one (by omega : 4 ≤ N) (by have := k.isLt; omega : k.val < 2 * bandParameter N)
    exact ⟨hlo.trans ht.1, ht.2.trans hhi⟩
  have hchord := heightChordSquare_comparison hsI htI
    (by simpa using Real.pi_nonneg : |(0 : ℝ)| ≤ Real.pi)
  have hchord' : (1 / 4 : ℝ) * δ ^ 2 ≤ U - V ∧
      U - V ≤ δ ^ 2 := by
    simpa [δ, U, V, angularKernelA, angularKernelB, sq_abs] using hchord
  have hLlo : d ^ 2 / 3600 ≤ U - V := by
    have hsq := mul_nonneg (sub_nonneg.mpr hδlo)
      (add_nonneg hδ0 (by positivity : 0 ≤ d / 30))
    nlinarith [hchord'.1]
  have hLhi : U - V ≤ 900 * d ^ 2 := by
    have hsq := mul_nonneg (sub_nonneg.mpr hδhi)
      (add_nonneg (by positivity : 0 ≤ 30 * d) hδ0)
    nlinarith [hchord'.2]
  have hUhi : U ≤ 904 * d ^ 2 := by linarith
  have hdpos : 0 < d := by
    have hpop : 0 < population N (j.val + 1) :=
      population_pos (by omega : 4 ≤ N) (by omega)
        (by have := j.isLt; omega)
    have hrpos : 0 < r := div_pos (by exact_mod_cast hpop) hM
    linarith
  have hV0 : 0 ≤ V := by
    change 0 ≤ 2 * a * b
    exact mul_nonneg (mul_nonneg (by norm_num) ha0) hb0
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 < U
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hdpos
    have hddiv : 0 < d ^ 2 / 3600 :=
      div_pos hd2 (by norm_num)
    linarith only [hLlo, hV0, hddiv]
  · change d ^ 2 / 3600 ≤ U
    linarith only [hLlo, hV0]
  · change U ≤ 904 * d ^ 2
    exact hUhi
  · change V ≤ (1 - (1 / 4000000 : ℝ)) * U
    have hcoef : (904 : ℝ) ≤ 4000000 / 3600 := by norm_num
    have hscaled : 904 * d ^ 2 ≤ 4000000 * (d ^ 2 / 3600) := by
      calc
        904 * d ^ 2 ≤ (4000000 / 3600) * d ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg d)
        _ = 4000000 * (d ^ 2 / 3600) := by ring
    have hmul : 4000000 * (d ^ 2 / 3600) ≤ 4000000 * (U - V) :=
      mul_le_mul_of_nonneg_left hLlo (by norm_num : (0 : ℝ) ≤ 4000000)
    have hmain : U ≤ 4000000 * (U - V) :=
      (hUhi.trans hscaled).trans hmul
    have hratio : U / 4000000 ≤ U - V := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4000000)).2
      simpa only [mul_comm] using hmain
    calc
      V = U - (U - V) := by ring
      _ ≤ U - U / 4000000 := sub_le_sub_left hratio U
      _ = (1 - (1 / 4000000 : ℝ)) * U := by ring

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.ComparableBlocks
import BEMOCFormalization.LatitudePotential
import BEMOCFormalization.SeparatedSmoothExtension
import BEMOCFormalization.AngularDistance

open scoped BigOperators
open MeasureTheory Set
namespace BEMOC.Definitive

/-- Total-variation control of one band error by a bound on its own band. -/
theorem abs_bandError_le_of_band_bound {N j : ℕ}
    (hN : 4 ≤ N) (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (f : ℝ → ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ t ∈ band N j, |f t| ≤ C) :
    |bandError N j f| ≤ 2 * (population N j : ℝ) * C := by
  have hab : boundary N j ≤ boundary N (j - 1) := by
    rw [← sub_nonneg, boundary_width hN hj1]
    positivity
  have hmid : height N j ∈ band N j := by
    have hm := height_inside_band hN hj1 hj2
    exact ⟨hm.1.le, hm.2.le⟩
  have hint : |∫ t in boundary N j..boundary N (j - 1), f t| ≤
      C * (boundary N (j - 1) - boundary N j) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := boundary N j) (b := boundary N (j - 1)) (C := C)
      (f := f) (by
        intro t ht
        rw [Real.norm_eq_abs]
        exact hbound t (by
          change t ∈ Set.uIoc (boundary N j) (boundary N (j - 1)) at ht
          rw [Set.uIoc_of_le hab] at ht
          exact ⟨ht.1.le, ht.2⟩))
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using h
  have hwidth := boundary_width hN hj1
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmass : (N : ℝ) / 2 *
      (boundary N (j - 1) - boundary N j) = population N j := by
    rw [hwidth]
    field_simp
    ring
  unfold bandError
  calc
    |(N : ℝ) / 2 * (∫ t in boundary N j..boundary N (j - 1), f t) -
        (population N j : ℝ) * f (height N j)| ≤
        |(N : ℝ) / 2 * (∫ t in boundary N j..boundary N (j - 1), f t)| +
          |(population N j : ℝ) * f (height N j)| := by
            simpa [sub_eq_add_neg] using abs_add_le
              ((N : ℝ) / 2 * (∫ t in boundary N j..boundary N (j - 1), f t))
              (-(population N j : ℝ) * f (height N j))
    _ ≤ (N : ℝ) / 2 * (C * (boundary N (j - 1) - boundary N j)) +
          (population N j : ℝ) * C := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / 2),
              abs_of_nonneg (by positivity : 0 ≤ (population N j : ℝ))]
            gcongr
            exact hbound _ hmid
    _ = 2 * (population N j : ℝ) * C := by
      calc
        _ = ((N : ℝ) / 2 * (boundary N (j - 1) - boundary N j)) * C +
            (population N j : ℝ) * C := by ring
        _ = _ := by rw [hmass]; ring

/-- Bounding a kernel on the literal rectangle bounds its tensor band error. -/
theorem abs_bandBlock_le_of_rectangle_bound {N j k : ℕ}
    (hN : 4 ≤ N) (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (G : ℝ × ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s ∈ band N j, ∀ t ∈ band N k, |G (s,t)| ≤ C) :
    |bandBlock N j k G| ≤
      4 * (population N j : ℝ) * (population N k : ℝ) * C := by
  unfold bandBlock
  have hinner : ∀ s ∈ band N j,
      |bandError N k (fun t ↦ G (s,t))| ≤
        2 * (population N k : ℝ) * C := by
    intro s hs
    exact abs_bandError_le_of_band_bound hN hk1 hk2 _ hC (hbound s hs)
  have hD : 0 ≤ 2 * (population N k : ℝ) * C := by positivity
  calc
    |bandError N j (fun s ↦ bandError N k (fun t ↦ G (s,t)))| ≤
        2 * (population N j : ℝ) *
          (2 * (population N k : ℝ) * C) :=
      abs_bandError_le_of_band_bound hN hj1 hj2 _ hD hinner
    _ = _ := by ring

theorem abs_kernelBlock_le_of_rectangle_bound {N j k : ℕ}
    (hN : 4 ≤ N) (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (α : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s ∈ band N j, ∀ t ∈ band N k,
      |latitudeKernel α s t| ≤ C) :
    |kernelBlock α N j k| ≤
      4 * (population N j : ℝ) * (population N k : ℝ) * C := by
  exact abs_bandBlock_le_of_rectangle_bound hN hj1 hj2 hk1 hk2
    (fun p ↦ latitudeKernel α p.1 p.2) hC hbound

/-- Equality of kernels on the literal rectangle suffices for equality of
their band tensors. -/
theorem kernelBlock_eq_bandBlock_of_eqOn_rectangle
    {N : ℕ} (hN : 4 ≤ N) (j k : RingIndex N) (α : ℝ)
    (G : ℝ × ℝ → ℝ)
    (hG : ∀ s ∈ band N (j.val + 1), ∀ t ∈ band N (k.val + 1),
      G (s,t) = latitudeKernel α s t) :
    kernelBlock α N (j.val + 1) (k.val + 1) =
      bandBlock N (j.val + 1) (k.val + 1) G := by
  unfold kernelBlock bandBlock
  apply bandError_congr_on_band hN j
  intro s hs
  apply bandError_congr_on_band hN k
  intro t ht
  exact (hG s hs t ht).symm

/-- A smooth extension of the actual latitude kernel can be fed directly to
the proved two-moment Taylor estimate. -/
theorem kernelBlock_le_of_smooth_extension
    {N : ℕ} (hN : 4 ≤ N) (j k : RingIndex N) (α : ℝ)
    (G : ℝ × ℝ → ℝ) (W : Set (ℝ × ℝ))
    (hW : IsOpen W)
    (hrect : band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ W)
    (hG : ContDiffOn ℝ 4 G W)
    (heq : ∀ s ∈ band N (j.val + 1), ∀ t ∈ band N (k.val + 1),
      G (s,t) = latitudeKernel α s t)
    (L : ℝ) (hL : 0 ≤ L)
    (hfourth : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      |mixedFourth G p.1 p.2| ≤ L) :
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
      (population N (j.val + 1) : ℝ) ^ 3 *
        (population N (k.val + 1) : ℝ) ^ 3 /
          (bandParameter N : ℝ) ^ 8 * L := by
  rw [kernelBlock_eq_bandBlock_of_eqOn_rectangle hN j k α G heq]
  exact mixedTaylorBound N hN j k G W hW hrect hG L hL hfourth

theorem bandParameter_ge_two_of_ge_1024 {N : ℕ} (hN : 1024 ≤ N) :
    2 ≤ bandParameter N := by
  by_contra h
  have hb := (bandParameter_bounds N).2
  have hsmall : bandParameter N ≤ 1 := by omega
  interval_cases hparam : bandParameter N
  · norm_num [hparam] at hb
    omega
  · norm_num [hparam] at hb
    omega

theorem bandParameter_ge_sixteen_of_ge_1024 {N : ℕ} (hN : 1024 ≤ N) :
    16 ≤ bandParameter N := by
  by_contra h
  have hm : bandParameter N ≤ 15 := by omega
  have hb := (bandParameter_bounds N).2
  nlinarith

/-- A population at most 32 can only occur among the first or last eight
occupied bands when `M≥16`. -/
theorem small_population_index_is_polar {N q : ℕ} (hN : 1024 ≤ N)
    (hq1 : 1 ≤ q) (hq2 : q < 2 * bandParameter N)
    (hpop : population N q ≤ 32) :
    q ≤ 8 ∨ 2 * bandParameter N - q ≤ 8 := by
  let M := bandParameter N
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  rcases lt_trichotomy q M with hnorth | hcenter | hsouth
  · left
    rw [north_population N q hnorth] at hpop
    omega
  · subst q
    have hc := (central_population_bounds (by omega : 4 ≤ N)).1
    dsimp [M] at *
    omega
  · right
    rw [south_population N q hsouth] at hpop
    omega

theorem population_first_eq_four {N : ℕ} (hN : 1024 ≤ N) :
    population N 1 = 4 :=
  north_population N 1 (by have hM := bandParameter_ge_sixteen_of_ge_1024 hN; omega)

theorem population_last_eq_four {N : ℕ} (hN : 1024 ≤ N) :
    population N (2 * bandParameter N - 1) = 4 := by
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  rw [south_population N (2 * bandParameter N - 1)
    (by omega : bandParameter N < 2 * bandParameter N - 1)]
  have hsub : 2 * bandParameter N - (2 * bandParameter N - 1) = 1 := by omega
  rw [hsub]

/-- Comparable populations with either index at an endpoint force both
indices into the finite polar corner regions. -/
theorem comparable_endpoint_indices_polar {N j k : ℕ} (hN : 1024 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N)
    (hcomp : Comparable N j k)
    (hend : j = 1 ∨ j = 2 * bandParameter N - 1 ∨
      k = 1 ∨ k = 2 * bandParameter N - 1) :
    (j ≤ 8 ∨ 2 * bandParameter N - j ≤ 8) ∧
      (k ≤ 8 ∨ 2 * bandParameter N - k ≤ 8) := by
  dsimp [Comparable] at hcomp
  have hpop : population N j ≤ 32 ∧ population N k ≤ 32 := by
    rcases hend with hj | hj | hk | hk
    · rw [hj, population_first_eq_four hN] at hcomp ⊢
      norm_num at hcomp
      constructor
      · omega
      · exact_mod_cast hcomp.2
    · rw [hj, population_last_eq_four hN] at hcomp ⊢
      norm_num at hcomp
      constructor
      · omega
      · exact_mod_cast hcomp.2
    · rw [hk, population_first_eq_four hN] at hcomp ⊢
      constructor
      · exact_mod_cast (show (population N j : ℝ) ≤ 32 by linarith [hcomp.1])
      · omega
    · rw [hk, population_last_eq_four hN] at hcomp ⊢
      constructor
      · exact_mod_cast (show (population N j : ℝ) ≤ 32 by linarith [hcomp.1])
      · omega
  exact ⟨small_population_index_is_polar hN hj1 hj2 hpop.1,
    small_population_index_is_polar hN hk1 hk2 hpop.2⟩

/-- In the first north-polar band, the height is within `8/N` of the pole. -/
theorem north_first_band_height_bounds {N : ℕ} (hN : 1024 ≤ N)
    {s : ℝ} (hs : s ∈ band N 1) :
    0 ≤ s ∧ s ≤ 1 ∧ 1 - s ≤ 8 / (N : ℝ) := by
  have hM := bandParameter_ge_two_of_ge_1024 hN
  have hb : boundary N 1 = 1 - 8 / (N : ℝ) := by
    rw [north_boundary (by omega : 4 ≤ N) (by omega : 1 < bandParameter N)]
    ring
  have hs' : 1 - 8 / (N : ℝ) ≤ s ∧ s ≤ 1 := by
    simpa [band, hb, boundary_zero] using hs
  have hNr : (1024 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < N := by positivity
  have hdiv : 0 ≤ 8 / (N : ℝ) ∧ 8 / (N : ℝ) ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_iff₀ hNr0).2 (by linarith)
  constructor
  · linarith
  constructor
  · exact hs'.2
  · linarith

/-- Every one of the first eight bands stays within `288/N` of the north pole. -/
theorem north_small_band_height_bounds {N k : ℕ} (hN : 1024 ≤ N)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {t : ℝ} (ht : t ∈ band N k) :
    0 ≤ t ∧ t ≤ 1 ∧ 1 - t ≤ 288 / (N : ℝ) := by
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  have hkM : k < bandParameter N := by omega
  have hb : boundary N k = 1 - 4 * (k : ℝ) * (k + 1) / N :=
    north_boundary (by omega : 4 ≤ N) hkM
  have hprev : k - 1 < 2 * bandParameter N := by omega
  have hupper : boundary N (k - 1) ≤ 1 :=
    boundary_le_one (by omega : 4 ≤ N) hprev
  have ht' : 1 - 4 * (k : ℝ) * (k + 1) / N ≤ t ∧ t ≤ 1 := by
    have h := ht
    dsimp [band] at h
    rw [hb] at h
    exact ⟨h.1, h.2.trans hupper⟩
  have hkr : (k : ℝ) ≤ 8 := by exact_mod_cast hk8
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsmall : 4 * (k : ℝ) * (k + 1) ≤ 288 := by nlinarith [hk1]
  have hdiv : 4 * (k : ℝ) * (k + 1) / N ≤ 288 / (N : ℝ) :=
    div_le_div_of_nonneg_right hsmall hNr.le
  have hNr1024 : (1024 : ℝ) ≤ N := by exact_mod_cast hN
  have htotal : 288 / (N : ℝ) ≤ 1 :=
    (div_le_iff₀ hNr).2 (by linarith)
  constructor
  · linarith
  constructor
  · exact ht'.2
  · linarith

/-- Squared chordal distance between two points in the first polar band is
at most `64/N`, uniformly in angular separation. -/
theorem north_first_band_chord_sq_le {N : ℕ} (hN : 1024 ≤ N)
    {s t θ : ℝ} (hs : s ∈ band N 1) (ht : t ∈ band N 1) :
    2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ ≤ 64 / (N : ℝ) := by
  have hsb := north_first_band_height_bounds hN hs
  have htb := north_first_band_height_bounds hN ht
  have hNr : (0 : ℝ) < N := by positivity
  have hsa : 0 ≤ 1 - s ^ 2 := by nlinarith [hsb.1, hsb.2.1]
  have hta : 0 ≤ 1 - t ^ 2 := by nlinarith [htb.1, htb.2.1]
  have hsrad : 1 - s ^ 2 ≤ 16 / (N : ℝ) := by
    calc
      1 - s ^ 2 = (1 - s) * (1 + s) := by ring
      _ ≤ 8 / (N : ℝ) * (1 + s) :=
        mul_le_mul_of_nonneg_right hsb.2.2 (by linarith)
      _ ≤ 8 / (N : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 16 / (N : ℝ) := by ring
  have htrad : 1 - t ^ 2 ≤ 16 / (N : ℝ) := by
    calc
      1 - t ^ 2 = (1 - t) * (1 + t) := by ring
      _ ≤ 8 / (N : ℝ) * (1 + t) :=
        mul_le_mul_of_nonneg_right htb.2.2 (by linarith)
      _ ≤ 8 / (N : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 16 / (N : ℝ) := by ring
  have hrad : 0 ≤ Real.sqrt (1 - s ^ 2) := Real.sqrt_nonneg _
  have hrad' : 0 ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
  have hsq := sq_nonneg (Real.sqrt (1 - s ^ 2) - Real.sqrt (1 - t ^ 2))
  rw [sub_sq, Real.sq_sqrt hsa, Real.sq_sqrt hta] at hsq
  have hcos := Real.neg_one_le_cos θ
  have hxy := mul_nonneg (sub_nonneg.mpr hsb.2.1) (sub_nonneg.mpr htb.2.1)
  have hcosprod := mul_le_mul_of_nonneg_left hcos
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hrad hrad'))
  have hfirst : 2 - 2 * s * t ≤ 32 / (N : ℝ) := by
    calc
      2 - 2 * s * t ≤ 2 * ((1 - s) + (1 - t)) := by nlinarith [hxy]
      _ ≤ 2 * (8 / (N : ℝ) + 8 / (N : ℝ)) := by
        gcongr
        · exact hsb.2.2
        · exact htb.2.2
      _ = 32 / (N : ℝ) := by ring
  have hsecond : -(2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ) ≤ 32 / (N : ℝ) := by
    calc
      _ ≤ 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) := by
        nlinarith [hcosprod]
      _ ≤ (1 - s ^ 2) + (1 - t ^ 2) := by nlinarith [hsq]
      _ ≤ 16 / (N : ℝ) + 16 / (N : ℝ) := add_le_add hsrad htrad
      _ = 32 / (N : ℝ) := by ring
  calc
    _ = (2 - 2 * s * t) +
        (-(2 * Real.sqrt (1 - s ^ 2) *
          Real.sqrt (1 - t ^ 2) * Real.cos θ)) := by ring
    _ ≤ 32 / (N : ℝ) + 32 / (N : ℝ) := add_le_add hfirst hsecond
    _ = 64 / (N : ℝ) := by ring

/-- The latitude kernel on the first polar square is at its natural
`N^{-α/2}` scale. -/
theorem north_first_band_latitudeKernel_bound {N : ℕ} (hN : 1024 ≤ N)
    {α : ℝ} (hα : 0 < α) {s t : ℝ}
    (hs : s ∈ band N 1) (ht : t ∈ band N 1) :
    |latitudeKernel α s t| ≤ (64 / (N : ℝ)) ^ (α / 2) := by
  have hsb := north_first_band_height_bounds hN hs
  have htb := north_first_band_height_bounds hN ht
  have hsunit : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hsb.1], hsb.2.1⟩
  have htunit : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [htb.1], htb.2.1⟩
  have hbase (θ : ℝ) : 0 ≤ 2 - 2 * s * t -
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * Real.cos θ := by
    have hdist := parallelPoint_dist_sq hsunit htunit (θ := θ) (φ := 0)
    simpa [Real.cos_neg] using (sq_nonneg (dist (parallelPoint s θ hsunit)
      (parallelPoint t 0 htunit))) |>.trans_eq hdist
  have hprof (θ : ℝ) :
      0 ≤ latitudeProfile α s t θ ∧
        latitudeProfile α s t θ ≤ (64 / (N : ℝ)) ^ (α / 2) := by
    unfold latitudeProfile
    exact ⟨Real.rpow_nonneg (hbase θ) _,
      Real.rpow_le_rpow (hbase θ) (north_first_band_chord_sq_le hN hs ht) (by linarith)⟩
  have hzero : 0 ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, latitudeProfile α s t θ := by
    exact intervalIntegral.integral_nonneg (by positivity) (fun θ _ ↦ (hprof θ).1)
  have hcont : Continuous (latitudeProfile α s t) :=
    (continuous_latitudeProfile hα).comp
      ((continuous_const.prodMk continuous_const).prodMk continuous_id)
  have htop : (∫ θ in (0 : ℝ)..2 * Real.pi, latitudeProfile α s t θ) ≤
      ∫ _θ in (0 : ℝ)..2 * Real.pi, (64 / (N : ℝ)) ^ (α / 2) := by
    exact intervalIntegral.integral_mono_on (by positivity)
      (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (fun θ _ ↦ (hprof θ).2)
  rw [latitudeKernel_eq_profile_integral]
  rw [abs_of_nonneg (mul_nonneg (by positivity) hzero)]
  rw [intervalIntegral.integral_const] at htop
  simp only [smul_eq_mul] at htop
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hnorm : (1 / (2 * Real.pi)) * ((2 * Real.pi) * (64 / (N : ℝ)) ^ (α / 2)) =
      (64 / (N : ℝ)) ^ (α / 2) := by field_simp
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((2 * Real.pi) *
        (64 / (N : ℝ)) ^ (α / 2)) := by
          apply mul_le_mul_of_nonneg_left
          simpa using htop
          positivity
    _ = _ := hnorm

/-- The literal first-band diagonal tensor has its polar `N^{-α/2}` size. -/
theorem north_first_diagonal_block_bound {N : ℕ} (hN : 1024 ≤ N)
    {α : ℝ} (hα : 0 < α) :
    |kernelBlock α N 1 1| ≤ 64 * (64 / (N : ℝ)) ^ (α / 2) := by
  have hM := bandParameter_ge_two_of_ge_1024 hN
  have hpop : population N 1 = 4 :=
    north_population N 1 (by omega : 1 < bandParameter N)
  have h := abs_kernelBlock_le_of_rectangle_bound
    (by omega : 4 ≤ N) (by omega : 1 ≤ 1)
    (by omega : 1 < 2 * bandParameter N)
    (by omega : 1 ≤ 1) (by omega : 1 < 2 * bandParameter N)
    α (Real.rpow_nonneg (by positivity : 0 ≤ 64 / (N : ℝ)) _)
    (fun s hs t ht ↦ north_first_band_latitudeKernel_bound hN hα hs ht)
  rw [hpop] at h
  norm_num at h ⊢
  exact h

/-- The first diagonal block satisfies the manuscript's comparable majorant. -/
theorem north_first_diagonal_comparable_bound {N : ℕ} (hN : 1024 ≤ N)
    {α : ℝ} (hα : 0 < α) :
    |kernelBlock α N 1 1| ≤
      (16 * (4 : ℝ) ^ α) * (population N 1 : ℝ) /
        (bandParameter N : ℝ) ^ α := by
  let M := bandParameter N
  have hM : (0 : ℝ) < M := by
    have hMnat : 0 < M := by
      have hm := bandParameter_ge_two_of_ge_1024 hN
      dsimp [M]
      omega
    exact_mod_cast hMnat
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb : 4 * (M : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hbase : 64 / (N : ℝ) ≤ 16 / (M : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ hNr (sq_pos_of_pos hM)).2
    nlinarith [hb]
  have hpow : (64 / (N : ℝ)) ^ (α / 2) ≤
      (16 / (M : ℝ) ^ 2) ^ (α / 2) :=
    Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hrewrite : (16 / (M : ℝ) ^ 2) ^ (α / 2) =
      (4 : ℝ) ^ α / (M : ℝ) ^ α := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg (M : ℝ))]
    rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    congr 1 <;> ring
  have hpop : population N 1 = 4 :=
    north_population N 1 (by have h := bandParameter_ge_two_of_ge_1024 hN; omega)
  calc
    |kernelBlock α N 1 1| ≤ 64 * (64 / (N : ℝ)) ^ (α / 2) :=
      north_first_diagonal_block_bound hN hα
    _ ≤ 64 * (16 / (M : ℝ) ^ 2) ^ (α / 2) := by gcongr
    _ = 64 * ((4 : ℝ) ^ α / (M : ℝ) ^ α) := by rw [hrewrite]
    _ = (16 * (4 : ℝ) ^ α) * (population N 1 : ℝ) /
        (bandParameter N : ℝ) ^ α := by rw [hpop]; dsimp [M]; ring

theorem latitudeKernel_neg_neg (α s t : ℝ) :
    latitudeKernel α (-s) (-t) = latitudeKernel α s t := by
  unfold latitudeKernel
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [neg_sq, neg_mul_neg]
  congr 1
  ring

/-- Reflection sends the last south-polar band to the first north-polar band. -/
theorem south_last_band_neg_mem_north_first {N : ℕ} (hN : 1024 ≤ N)
    {s : ℝ} (hs : s ∈ band N (2 * bandParameter N - 1)) :
    -s ∈ band N 1 := by
  let M := bandParameter N
  have hM := bandParameter_ge_two_of_ge_1024 hN
  have hlast : boundary N (2 * M - 1) = -1 :=
    boundary_last (by omega : 4 ≤ N)
  have href := boundary_reflect (N := N) (j := 1)
    (by omega : 4 ≤ N) (by omega : 1 ≤ 2 * M - 1)
  have hidx : 2 * M - 1 - 1 = 2 * M - 2 := by omega
  have hpred : (2 * M - 1) - 1 = 2 * M - 2 := by omega
  rw [hidx] at href
  have hs' : -1 ≤ s ∧ s ≤ -boundary N 1 := by
    simpa [band, M, hlast, hpred, href] using hs
  have hboundary : boundary N 0 = 1 := boundary_zero N
  change boundary N 1 ≤ -s ∧ -s ≤ boundary N 0
  rw [hboundary]
  constructor <;> linarith [hs'.1, hs'.2]

theorem south_last_diagonal_block_bound {N : ℕ} (hN : 1024 ≤ N)
    {α : ℝ} (hα : 0 < α) :
    |kernelBlock α N (2 * bandParameter N - 1)
      (2 * bandParameter N - 1)| ≤
      64 * (64 / (N : ℝ)) ^ (α / 2) := by
  let M := bandParameter N
  have hM := bandParameter_ge_two_of_ge_1024 hN
  have hj1 : 1 ≤ 2 * M - 1 := by omega
  have hj2 : 2 * M - 1 < 2 * M := by omega
  have hpop : population N (2 * M - 1) = 4 := by
    rw [south_population N (2 * M - 1) (by omega : M < 2 * M - 1)]
    have hsub : 2 * M - (2 * M - 1) = 1 := by omega
    rw [hsub]
  have h := abs_kernelBlock_le_of_rectangle_bound
    (by omega : 4 ≤ N) hj1 hj2 hj1 hj2 α
    (Real.rpow_nonneg (by positivity : 0 ≤ 64 / (N : ℝ)) _)
    (fun s hs t ht ↦ by
      rw [← latitudeKernel_neg_neg α s t]
      exact north_first_band_latitudeKernel_bound hN hα
        (south_last_band_neg_mem_north_first hN hs)
        (south_last_band_neg_mem_north_first hN ht))
  dsimp [M] at hpop ⊢
  rw [hpop] at h
  norm_num at h ⊢
  exact h

theorem south_last_diagonal_comparable_bound {N : ℕ} (hN : 1024 ≤ N)
    {α : ℝ} (hα : 0 < α) :
    |kernelBlock α N (2 * bandParameter N - 1)
      (2 * bandParameter N - 1)| ≤
      (16 * (4 : ℝ) ^ α) *
        (population N (2 * bandParameter N - 1) : ℝ) /
          (bandParameter N : ℝ) ^ α := by
  let M := bandParameter N
  have hMnat := bandParameter_ge_two_of_ge_1024 hN
  have hM : (0 : ℝ) < M := by
    have hm : 0 < M := by dsimp [M]; omega
    exact_mod_cast hm
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb : 4 * (M : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hbase : 64 / (N : ℝ) ≤ 16 / (M : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ hNr (sq_pos_of_pos hM)).2
    nlinarith [hb]
  have hpow : (64 / (N : ℝ)) ^ (α / 2) ≤
      (16 / (M : ℝ) ^ 2) ^ (α / 2) :=
    Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hrewrite : (16 / (M : ℝ) ^ 2) ^ (α / 2) =
      (4 : ℝ) ^ α / (M : ℝ) ^ α := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg (M : ℝ))]
    rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    congr 1 <;> ring
  have hpop : population N (2 * M - 1) = 4 := by
    rw [south_population N (2 * M - 1) (by omega : M < 2 * M - 1)]
    have hsub : 2 * M - (2 * M - 1) = 1 := by omega
    rw [hsub]
  calc
    |kernelBlock α N (2 * bandParameter N - 1)
      (2 * bandParameter N - 1)| ≤
        64 * (64 / (N : ℝ)) ^ (α / 2) :=
      south_last_diagonal_block_bound hN hα
    _ ≤ 64 * (16 / (M : ℝ) ^ 2) ^ (α / 2) := by gcongr
    _ = 64 * ((4 : ℝ) ^ α / (M : ℝ) ^ α) := by rw [hrewrite]
    _ = (16 * (4 : ℝ) ^ α) *
        (population N (2 * bandParameter N - 1) : ℝ) /
          (bandParameter N : ℝ) ^ α := by rw [hpop]; dsimp [M]; ring

/-- Chordal distance estimate for two heights within `q` of the north pole. -/
theorem polar_chord_sq_le_of_height {s t q θ : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hsq : 1 - s ≤ q) (htq : 1 - t ≤ q) (hq : 0 ≤ q) :
    2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ ≤ 8 * q := by
  have hsa : 0 ≤ 1 - s ^ 2 := by nlinarith
  have hta : 0 ≤ 1 - t ^ 2 := by nlinarith
  have hsrad : 1 - s ^ 2 ≤ 2 * q := by
    calc
      1 - s ^ 2 = (1 - s) * (1 + s) := by ring
      _ ≤ q * (1 + s) := mul_le_mul_of_nonneg_right hsq (by linarith)
      _ ≤ q * 2 := mul_le_mul_of_nonneg_left (by linarith) hq
      _ = 2 * q := by ring
  have htrad : 1 - t ^ 2 ≤ 2 * q := by
    calc
      1 - t ^ 2 = (1 - t) * (1 + t) := by ring
      _ ≤ q * (1 + t) := mul_le_mul_of_nonneg_right htq (by linarith)
      _ ≤ q * 2 := mul_le_mul_of_nonneg_left (by linarith) hq
      _ = 2 * q := by ring
  have hrad : 0 ≤ Real.sqrt (1 - s ^ 2) := Real.sqrt_nonneg _
  have hrad' : 0 ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
  have hroot := sq_nonneg (Real.sqrt (1 - s ^ 2) - Real.sqrt (1 - t ^ 2))
  rw [sub_sq, Real.sq_sqrt hsa, Real.sq_sqrt hta] at hroot
  have hcos := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hrad hrad'))
  have hxy := mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr ht1)
  have hfirst : 2 - 2 * s * t ≤ 4 * q := by
    calc
      _ ≤ 2 * ((1 - s) + (1 - t)) := by nlinarith [hxy]
      _ ≤ 2 * (q + q) := by gcongr
      _ = 4 * q := by ring
  have hsecond : -(2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ) ≤ 4 * q := by
    calc
      _ ≤ 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) := by
        nlinarith [hcos]
      _ ≤ (1 - s ^ 2) + (1 - t ^ 2) := by nlinarith [hroot]
      _ ≤ 2 * q + 2 * q := add_le_add hsrad htrad
      _ = 4 * q := by ring
  calc
    _ = (2 - 2 * s * t) +
        (-(2 * Real.sqrt (1 - s ^ 2) *
          Real.sqrt (1 - t ^ 2) * Real.cos θ)) := by ring
    _ ≤ 4 * q + 4 * q := add_le_add hfirst hsecond
    _ = 8 * q := by ring

theorem north_small_bands_chord_sq_le {N j k : ℕ} (hN : 1024 ≤ N)
    (hj1 : 1 ≤ j) (hj8 : j ≤ 8) (hk1 : 1 ≤ k) (hk8 : k ≤ 8)
    {s t θ : ℝ} (hs : s ∈ band N j) (ht : t ∈ band N k) :
    2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ ≤ 2304 / (N : ℝ) := by
  have hs' := north_small_band_height_bounds hN hj1 hj8 hs
  have ht' := north_small_band_height_bounds hN hk1 hk8 ht
  have h := polar_chord_sq_le_of_height (θ := θ) hs'.1 hs'.2.1 ht'.1 ht'.2.1
    hs'.2.2 ht'.2.2 (by positivity : 0 ≤ 288 / (N : ℝ))
  convert h using 1; ring

/-- A uniform chord-square bound controls the actual angular average. -/
theorem latitudeKernel_abs_le_of_chord_sq {α s t B : ℝ}
    (hα : 0 < α) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (_hB : 0 ≤ B)
    (hchord : ∀ θ : ℝ,
      2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
        Real.sqrt (1 - t ^ 2) * Real.cos θ ≤ B) :
    |latitudeKernel α s t| ≤ B ^ (α / 2) := by
  have hbase (θ : ℝ) : 0 ≤ 2 - 2 * s * t -
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * Real.cos θ := by
    have hdist := parallelPoint_dist_sq hs ht (θ := θ) (φ := 0)
    simpa [Real.cos_neg] using (sq_nonneg (dist (parallelPoint s θ hs)
      (parallelPoint t 0 ht))) |>.trans_eq hdist
  have hprof (θ : ℝ) :
      0 ≤ latitudeProfile α s t θ ∧ latitudeProfile α s t θ ≤ B ^ (α / 2) := by
    unfold latitudeProfile
    exact ⟨Real.rpow_nonneg (hbase θ) _,
      Real.rpow_le_rpow (hbase θ) (hchord θ) (by linarith)⟩
  have hzero : 0 ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, latitudeProfile α s t θ :=
    intervalIntegral.integral_nonneg (by positivity) (fun θ _ ↦ (hprof θ).1)
  have hcont : Continuous (latitudeProfile α s t) :=
    (continuous_latitudeProfile hα).comp
      ((continuous_const.prodMk continuous_const).prodMk continuous_id)
  have htop : (∫ θ in (0 : ℝ)..2 * Real.pi, latitudeProfile α s t θ) ≤
      ∫ _θ in (0 : ℝ)..2 * Real.pi, B ^ (α / 2) :=
    intervalIntegral.integral_mono_on (by positivity)
      (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (fun θ _ ↦ (hprof θ).2)
  rw [latitudeKernel_eq_profile_integral]
  rw [abs_of_nonneg (mul_nonneg (by positivity) hzero)]
  rw [intervalIntegral.integral_const] at htop
  simp only [smul_eq_mul] at htop
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((2 * Real.pi) * B ^ (α / 2)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa using htop
      · positivity
    _ = _ := by field_simp

theorem north_small_bands_latitudeKernel_bound {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {α s t : ℝ} (hα : 0 < α)
    (hs : s ∈ band N j) (ht : t ∈ band N k) :
    |latitudeKernel α s t| ≤ (2304 / (N : ℝ)) ^ (α / 2) := by
  have hsb := north_small_band_height_bounds hN hj1 hj8 hs
  have htb := north_small_band_height_bounds hN hk1 hk8 ht
  exact latitudeKernel_abs_le_of_chord_sq hα
    ⟨by linarith [hsb.1], hsb.2.1⟩
    ⟨by linarith [htb.1], htb.2.1⟩
    (by positivity)
    (fun θ ↦ north_small_bands_chord_sq_le hN hj1 hj8 hk1 hk8 hs ht)

theorem north_small_bands_block_bound {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {α : ℝ} (hα : 0 < α) :
    |kernelBlock α N j k| ≤
      4 * (population N j : ℝ) * (population N k : ℝ) *
        (2304 / (N : ℝ)) ^ (α / 2) := by
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  exact abs_kernelBlock_le_of_rectangle_bound
    (by omega : 4 ≤ N) hj1 (by omega : j < 2 * bandParameter N)
    hk1 (by omega : k < 2 * bandParameter N) α
    (Real.rpow_nonneg (by positivity : 0 ≤ 2304 / (N : ℝ)) _)
    (fun s hs t ht ↦ north_small_bands_latitudeKernel_bound hN
      hj1 hj8 hk1 hk8 hα hs ht)

/-- The first eight north-polar bands satisfy the exact comparable majorant. -/
theorem north_small_bands_comparable_bound {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    |kernelBlock α N j k| ≤
      (65536 * (24 : ℝ) ^ α) * (population N j : ℝ) /
        (bandParameter N : ℝ) ^ α *
          (1 + |(j : ℝ) - k|) ^ (α - 3) := by
  let M := bandParameter N
  have hMnat := bandParameter_ge_sixteen_of_ge_1024 hN
  have hM : (0 : ℝ) < M := by
    have hm : 0 < M := by dsimp [M]; omega
    exact_mod_cast hm
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb : 4 * (M : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hbase : 2304 / (N : ℝ) ≤ 576 / (M : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ hNr (sq_pos_of_pos hM)).2
    nlinarith [hb]
  have hpow : (2304 / (N : ℝ)) ^ (α / 2) ≤
      (576 / (M : ℝ) ^ 2) ^ (α / 2) :=
    Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hrewrite : (576 / (M : ℝ) ^ 2) ^ (α / 2) =
      (24 : ℝ) ^ α / (M : ℝ) ^ α := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 576) (sq_nonneg (M : ℝ))]
    rw [show (576 : ℝ) = 24 ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 24)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    congr 1 <;> ring
  have hkM : k < M := by omega
  have hpopk : (population N k : ℝ) ≤ 32 := by
    rw [north_population N k hkM]
    exact_mod_cast (by omega : 4 * k ≤ 32)
  have hjr : (j : ℝ) ≤ 8 := by exact_mod_cast hj8
  have hkr : (k : ℝ) ≤ 8 := by exact_mod_cast hk8
  have hjr1 : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hkr1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  let d : ℝ := 1 + |(j : ℝ) - k|
  have hd1 : 0 < d := by dsimp [d]; positivity
  have hd8 : d ≤ 8 := by
    have hdabs : |(j : ℝ) - k| ≤ 7 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    dsimp [d]
    linarith
  have hfactor : (1 / 512 : ℝ) ≤ d ^ (α - 3) := by
    have hle := Real.rpow_le_rpow_of_nonpos hd1 hd8 (by linarith : α - 3 ≤ 0)
    have hexp := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 8) (by linarith : (-3 : ℝ) ≤ α - 3)
    have hn : (8 : ℝ) ^ (-3 : ℝ) = 1 / 512 := by norm_num
    rw [← hn]
    exact hexp.trans hle
  have hpJ : 0 ≤ (population N j : ℝ) := by positivity
  have hpowM : 0 < (M : ℝ) ^ α := Real.rpow_pos_of_pos hM _
  have hpow24 : 0 ≤ (24 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  calc
    |kernelBlock α N j k| ≤
        4 * (population N j : ℝ) * (population N k : ℝ) *
          (2304 / (N : ℝ)) ^ (α / 2) :=
      north_small_bands_block_bound hN hj1 hj8 hk1 hk8 hα0
    _ ≤ 4 * (population N j : ℝ) * (population N k : ℝ) *
          ((24 : ℝ) ^ α / (M : ℝ) ^ α) := by
            rw [← hrewrite]
            gcongr
    _ ≤ 128 * (population N j : ℝ) *
          ((24 : ℝ) ^ α / (M : ℝ) ^ α) := by
            have hcoef : 4 * (population N j : ℝ) *
                (population N k : ℝ) ≤ 128 * (population N j : ℝ) := by
              nlinarith [mul_nonneg hpJ (by linarith : 0 ≤ 32 - (population N k : ℝ))]
            exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ (65536 * (24 : ℝ) ^ α) * (population N j : ℝ) /
          (M : ℝ) ^ α * d ^ (α - 3) := by
            have hmul := mul_le_mul_of_nonneg_left hfactor
              (by positivity : 0 ≤ 65536 * (24 : ℝ) ^ α *
                (population N j : ℝ) / (M : ℝ) ^ α)
            calc
              _ = (65536 * (24 : ℝ) ^ α) * (population N j : ℝ) /
                    (M : ℝ) ^ α * (1 / 512) := by ring
              _ ≤ _ := hmul
    _ = _ := by dsimp [M, d]

/-- Height reflection identifies each of the last eight bands with its
northern partner. -/
theorem south_small_band_neg_mem_north_small {N q : ℕ}
    (hN : 1024 ≤ N) (hq1 : 1 ≤ q) (hq8 : q ≤ 8)
    {s : ℝ} (hs : s ∈ band N (2 * bandParameter N - q)) :
    -s ∈ band N q := by
  let M := bandParameter N
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  have hqM : q ≤ 2 * M - 1 := by omega
  have hqm : q - 1 ≤ 2 * M - 1 := by omega
  have hrA := boundary_reflect (N := N) (j := q - 1)
    (by omega : 4 ≤ N) hqm
  have hrB := boundary_reflect (N := N) (j := q)
    (by omega : 4 ≤ N) hqM
  have hidxA : 2 * M - 1 - (q - 1) = 2 * M - q := by omega
  have hidxB : 2 * M - 1 - q = (2 * M - q) - 1 := by omega
  rw [hidxA] at hrA
  rw [hidxB] at hrB
  have hs' : boundary N (2 * M - q) ≤ s ∧
      s ≤ boundary N ((2 * M - q) - 1) := by
    simpa [band, M] using hs
  change boundary N q ≤ -s ∧ -s ≤ boundary N (q - 1)
  rw [hrA, hrB] at hs'
  constructor <;> linarith [hs'.1, hs'.2]

/-- Reflection of the signed midpoint band functional. -/
theorem bandError_reflect {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) (f : ℝ → ℝ) :
    bandError N (2 * bandParameter N - j) f =
      bandError N j (fun s ↦ f (-s)) := by
  let M := bandParameter N
  have hL : j ≤ 2 * M - 1 := by omega
  have hprev : j - 1 ≤ 2 * M - 1 := by omega
  have hrA := boundary_reflect hN (j := j - 1) hprev
  have hrB := boundary_reflect hN (j := j) hL
  have hidxA : 2 * M - 1 - (j - 1) = 2 * M - j := by omega
  have hidxB : 2 * M - 1 - j = (2 * M - j) - 1 := by omega
  rw [hidxA] at hrA
  rw [hidxB] at hrB
  have hheight := height_reflect hN hj1 hj2
  have hpop := population_reflect hN hj1 hj2
  unfold bandError
  rw [hrA, hrB, hheight, hpop]
  rw [intervalIntegral.integral_comp_neg]

theorem kernelBlock_reflect {N j k : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hk1 : 1 ≤ k) (hk2 : k < 2 * bandParameter N) (α : ℝ) :
    kernelBlock α N (2 * bandParameter N - j)
      (2 * bandParameter N - k) = kernelBlock α N j k := by
  unfold kernelBlock bandBlock
  rw [bandError_reflect hN hj1 hj2]
  congr 1
  funext s
  rw [bandError_reflect hN hk1 hk2]
  congr 1
  funext t
  exact latitudeKernel_neg_neg α s t

theorem south_small_bands_comparable_bound {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    |kernelBlock α N (2 * bandParameter N - j)
      (2 * bandParameter N - k)| ≤
      (65536 * (24 : ℝ) ^ α) *
        (population N (2 * bandParameter N - j) : ℝ) /
          (bandParameter N : ℝ) ^ α *
            (1 + |((2 * bandParameter N - j : ℕ) : ℝ) -
              (2 * bandParameter N - k : ℕ)|) ^ (α - 3) := by
  let M := bandParameter N
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  have hj2 : j < 2 * M := by omega
  have hk2 : k < 2 * M := by omega
  have hjle : j ≤ 2 * M := by omega
  have hkle : k ≤ 2 * M := by omega
  have hpop := population_reflect (N := N) (j := j)
    (by omega : 4 ≤ N) hj1 hj2
  have habs : |((2 * M - j : ℕ) : ℝ) - (2 * M - k : ℕ)| =
      |(j : ℝ) - k| := by
    rw [Nat.cast_sub hjle, Nat.cast_sub hkle]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hring : (2 * (M : ℝ) - j) - (2 * (M : ℝ) - k) =
        (k : ℝ) - j := by ring
    rw [hring]
    exact abs_sub_comm _ _
  rw [kernelBlock_reflect (by omega : 4 ≤ N) hj1 hj2 hk1 hk2,
    hpop, habs]
  exact north_small_bands_comparable_bound hN hj1 hj8 hk1 hk8 hα0 hα2

theorem south_small_bands_block_bound {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {α : ℝ} (hα : 0 < α) :
    |kernelBlock α N (2 * bandParameter N - j)
      (2 * bandParameter N - k)| ≤
      4 * (population N (2 * bandParameter N - j) : ℝ) *
        (population N (2 * bandParameter N - k) : ℝ) *
          (2304 / (N : ℝ)) ^ (α / 2) := by
  let M := bandParameter N
  have hM := bandParameter_ge_sixteen_of_ge_1024 hN
  have hjlow : 1 ≤ 2 * M - j := by omega
  have hjhigh : 2 * M - j < 2 * M := by omega
  have hklow : 1 ≤ 2 * M - k := by omega
  have hkhigh : 2 * M - k < 2 * M := by omega
  apply abs_kernelBlock_le_of_rectangle_bound
    (by omega : 4 ≤ N) hjlow hjhigh hklow hkhigh α
    (Real.rpow_nonneg (by positivity : 0 ≤ 2304 / (N : ℝ)) _)
  intro s hs t ht
  rw [← latitudeKernel_neg_neg α s t]
  exact north_small_bands_latitudeKernel_bound hN
    hj1 hj8 hk1 hk8 hα
    (south_small_band_neg_mem_north_small hN hj1 hj8 hs)
    (south_small_band_neg_mem_north_small hN hk1 hk8 ht)

/-- Opposite endpoint rectangles lie uniformly in the separated analytic
region of the averaged kernel. -/
theorem opposite_small_bands_separated {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {s t : ℝ}
    (hs : s ∈ band N j)
    (ht : t ∈ band N (2 * bandParameter N - k)) :
    0 < 2 - 2 * s * t ∧
      2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
        (1 - (1 / 4 : ℝ)) * (2 - 2 * s * t) := by
  have hsb := north_small_band_height_bounds hN hj1 hj8 hs
  have htb := north_small_band_height_bounds hN hk1 hk8
    (south_small_band_neg_mem_north_small hN hk1 hk8 ht)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNr1024 : (1024 : ℝ) ≤ N := by exact_mod_cast hN
  have hq : 288 / (N : ℝ) ≤ 1 / 2 :=
    (div_le_iff₀ hNr).2 (by linarith)
  have hs_half : (1 / 2 : ℝ) ≤ s := by linarith [hsb.2.2]
  have ht_half : t ≤ -(1 / 2 : ℝ) := by linarith [htb.2.2]
  have hsabs : s ^ 2 ≤ 1 := by nlinarith [hsb.1, hsb.2.1]
  have htabs : t ^ 2 ≤ 1 := by nlinarith [htb.1, htb.2.1]
  have hA : 0 ≤ 1 - s ^ 2 := by linarith
  have hB : 0 ≤ 1 - t ^ 2 := by linarith
  have hAupper : 1 - s ^ 2 ≤ 3 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
  have hBupper : 1 - t ^ 2 ≤ 3 / 4 := by nlinarith [sq_nonneg (t + 1 / 2)]
  have hroot := sq_nonneg (Real.sqrt (1 - s ^ 2) - Real.sqrt (1 - t ^ 2))
  rw [sub_sq, Real.sq_sqrt hA, Real.sq_sqrt hB] at hroot
  have hV : 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤ 3 / 2 := by
    nlinarith [hroot, hAupper, hBupper]
  have hprod : s * t ≤ -(1 / 4 : ℝ) := by
    have hm := mul_nonneg hsb.1 (by linarith : 0 ≤ -t - 1 / 2)
    nlinarith [hm, hs_half]
  have hU : (5 / 2 : ℝ) ≤ 2 - 2 * s * t := by linarith
  constructor
  · linarith
  · nlinarith [hV, hU]

/-- The fixed opposite-pole corner lies inside the global smooth-series domain. -/
theorem opposite_small_bands_mem_separatedOpen {N j k : ℕ}
    (hN : 1024 ≤ N) (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) {s t : ℝ}
    (hs : s ∈ band N j)
    (ht : t ∈ band N (2 * bandParameter N - k)) :
    (s, t) ∈ separatedOpen := by
  obtain ⟨hU, hV⟩ := opposite_small_bands_separated hN hj1 hj8 hk1 hk8 hs ht
  have hsI : s ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := north_small_band_height_bounds hN hj1 hj8 hs
    constructor <;> linarith [h.1, h.2.1]
  have htI : t ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := north_small_band_height_bounds hN hk1 hk8
      (south_small_band_neg_mem_north_small hN hk1 hk8 ht)
    constructor <;> linarith [h.1, h.2.1]
  have hB : 0 ≤ angularKernelB s t := by
    unfold angularKernelB
    positivity
  have hBlt : angularKernelB s t < angularKernelA s t := by
    dsimp [angularKernelA, angularKernelB] at *
    nlinarith
  constructor
  · simpa only [angularKernelA] using hU
  · rw [← angularKernelB_sq_eq_four_radiusSq hsI htI]
    rw [abs_of_nonneg (sq_nonneg _)]
    have hA : 0 < angularKernelA s t := by
      simpa only [angularKernelA] using hU
    nlinarith [mul_pos (sub_pos.mpr hBlt) (by linarith : 0 < angularKernelA s t + angularKernelB s t)]

set_option maxHeartbeats 1000000 in
/-- A far comparable rectangle has a fixed separated angular ratio. The
generous constants keep the index geometry independent of the exponent. -/
theorem far_comparable_rectangle_separation {N : ℕ} (hN : 1024 ≤ N)
    (j k : RingIndex N)
    (hjfirst : j.val ≠ 0)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val ≠ 0)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    (hjk : 2 ≤ |(j.val : ℤ) - k.val|)
    (hfar : 2 * (population N (j.val + 1) : ℝ) <
      |(j.val : ℝ) - k.val|)
    {s t : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1)) :
    0 < angularKernelA s t ∧
      (|(j.val : ℝ) - k.val| / (bandParameter N : ℝ)) ^ 2 / 3600 ≤
        angularKernelA s t ∧
      angularKernelA s t ≤
        904 * (|(j.val : ℝ) - k.val| / (bandParameter N : ℝ)) ^ 2 ∧
      angularKernelB s t ≤
        (1 - (1 / 4000000 : ℝ)) * angularKernelA s t := by
  let M : ℝ := bandParameter N
  let d : ℝ := |(j.val : ℝ) - k.val| / M
  let r : ℝ := (population N (j.val + 1) : ℝ) / M
  let a : ℝ := Real.sqrt (1 - s ^ 2)
  let b : ℝ := Real.sqrt (1 - t ^ 2)
  let δ : ℝ := |Real.arccos s - Real.arccos t|
  let U : ℝ := angularKernelA s t
  let V : ℝ := angularKernelB s t
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (16 : ℕ))
      (bandParameter_ge_sixteen_of_ge_1024 hN))
  have hd0 : 0 ≤ d := div_nonneg (abs_nonneg _) hM.le
  have hr0 : 0 ≤ r := by positivity
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hδ0 : 0 ≤ δ := abs_nonneg _
  have hδ := separated_band_arccos_gap (by omega : 4 ≤ N)
    (bandParameter_ge_sixteen_of_ge_1024 hN) j k hjk hs ht
  have hδlo : d / 30 ≤ δ := by
    simpa [d, δ, M, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hδ.1
  have hδhi : δ ≤ 30 * d := by
    simpa [d, δ, M, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hδ.2
  have hRj := (band_radius_comparison (by omega : 4 ≤ N)
    (bandParameter_ge_sixteen_of_ge_1024 hN) j hjfirst hjlast hs).2
  have hRk := (band_radius_comparison (by omega : 4 ≤ N)
    (bandParameter_ge_sixteen_of_ge_1024 hN) k hkfirst hklast ht).2
  have hpopk : (population N (k.val + 1) : ℝ) ≤
      8 * population N (j.val + 1) := hcomp.2
  have ha : a ≤ r := by simpa [a, r, M] using hRj
  have hb : b ≤ 8 * r := by
    have h := div_le_div_of_nonneg_right hpopk hM.le
    calc
      b ≤ (population N (k.val + 1) : ℝ) / M := hRk
      _ ≤ 8 * r := by simpa [r, M, mul_div_assoc] using h
  have hfar' : 2 * r < d := by
    have h := div_lt_div_of_pos_right hfar hM
    simpa [r, d, M, mul_div_assoc] using h
  have hV : V ≤ 4 * d ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
    change 2 * a * b ≤ 4 * d ^ 2
    nlinarith [sq_nonneg (d - 2 * r)]
  have hsI : s ∈ Set.Icc (-1 : ℝ) 1 := by
    have hlo := boundary_ge_neg_one (by omega : 4 ≤ N)
      (by have := j.isLt; omega : j.val + 1 < 2 * bandParameter N)
    have hhi := boundary_le_one (by omega : 4 ≤ N) (by have := j.isLt; omega : j.val < 2 * bandParameter N)
    exact ⟨hlo.trans hs.1, hs.2.trans hhi⟩
  have htI : t ∈ Set.Icc (-1 : ℝ) 1 := by
    have hlo := boundary_ge_neg_one (by omega : 4 ≤ N)
      (by have := k.isLt; omega : k.val + 1 < 2 * bandParameter N)
    have hhi := boundary_le_one (by omega : 4 ≤ N) (by have := k.isLt; omega : k.val < 2 * bandParameter N)
    exact ⟨hlo.trans ht.1, ht.2.trans hhi⟩
  have hchord := heightChordSquare_comparison hsI htI
    (by simpa using Real.pi_nonneg : |(0 : ℝ)| ≤ Real.pi)
  have hchord' : (1 / 4 : ℝ) * δ ^ 2 ≤ U - V ∧
      U - V ≤ δ ^ 2 := by
    simpa [δ, U, V, angularKernelA, angularKernelB, sq_abs] using hchord
  have hLlo : d ^ 2 / 3600 ≤ U - V := by
    have hsq := mul_nonneg (sub_nonneg.mpr hδlo)
      (add_nonneg hδ0 (by positivity : 0 ≤ d / 30))
    nlinarith [hchord'.1]
  have hLhi : U - V ≤ 900 * d ^ 2 := by
    have hsq := mul_nonneg (sub_nonneg.mpr hδhi)
      (add_nonneg (by positivity : 0 ≤ 30 * d) hδ0)
    nlinarith [hchord'.2]
  have hUhi : U ≤ 904 * d ^ 2 := by linarith
  have hdpos : 0 < d := by
    have hpop : 0 < population N (j.val + 1) :=
      population_pos (by omega : 4 ≤ N) (by omega)
        (by have := j.isLt; omega)
    have hrpos : 0 < r := div_pos (by exact_mod_cast hpop) hM
    linarith
  have hV0 : 0 ≤ V := by
    change 0 ≤ 2 * a * b
    exact mul_nonneg (mul_nonneg (by norm_num) ha0) hb0
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 < U
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hdpos
    have hddiv : 0 < d ^ 2 / 3600 :=
      div_pos hd2 (by norm_num)
    linarith only [hLlo, hV0, hddiv]
  · change d ^ 2 / 3600 ≤ U
    linarith only [hLlo, hV0]
  · change U ≤ 904 * d ^ 2
    exact hUhi
  · change V ≤ (1 - (1 / 4000000 : ℝ)) * U
    have hcoef : (904 : ℝ) ≤ 4000000 / 3600 := by norm_num
    have hscaled : 904 * d ^ 2 ≤ 4000000 * (d ^ 2 / 3600) := by
      calc
        904 * d ^ 2 ≤ (4000000 / 3600) * d ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg d)
        _ = 4000000 * (d ^ 2 / 3600) := by ring
    have hmul : 4000000 * (d ^ 2 / 3600) ≤ 4000000 * (U - V) :=
      mul_le_mul_of_nonneg_left hLlo (by norm_num : (0 : ℝ) ≤ 4000000)
    have hmain : U ≤ 4000000 * (U - V) :=
      (hUhi.trans hscaled).trans hmul
    have hratio : U / 4000000 ≤ U - V := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4000000)).2
      simpa only [mul_comm] using hmain
    calc
      V = U - (U - V) := by ring
      _ ≤ U - U / 4000000 := sub_le_sub_left hratio U
      _ = (1 - (1 / 4000000 : ℝ)) * U := by ring

end BEMOC.Definitive
```
