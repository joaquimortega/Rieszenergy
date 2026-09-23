# LatitudeSummation: finite block summation

Checked theorem: `latitude_bound_of_blocks` proves `LatitudeBound α` for `0 < α < 2`, conditional on the actual `LatitudeIdentity`, `BlockSymmetry`, `ComparableBlockBound`, `SameSideBlockBound`, and `OppositeBlockBound` contracts. It does not assume `GeometryBounds`; the needed population ceiling `r_j ≤ 15M` is already proved in `Geometry.lean`. The analytic block bounds and exact identity are proved in their respective modules; this theorem keeps them explicit as modular inputs.

The proof follows `definitive.tex`, lines 1019–1060, but uses a coarser summation for unequal populations. A comparable row is encoded by `(Nat.dist j k, k ≤ j)`, an injective code into distance times a Boolean. Thus every distance has multiplicity at most two, and the row sum is bounded by twice a convergent p-series because `α−3 < −1`. Summing the population factor uses the exact `∑_j r_j = N` identity.

Every ordered pair is classified by `Comparable` or one of the two strict inequalities `8r_j < r_k` and `8r_k < r_j`. Symmetry reverses the second orientation. In either unequal orientation, `SameSide` selects the same-side block estimate; its negation includes the central band and selects the opposite/central estimate. Therefore no pair, diagonal, or central exception is dropped.

The target is `O(M^(2−α))`, so the same-side estimate can be summed without proving the manuscript's sharper `O(1)` inequality: when `r_j ≤ r_k` and `α < 2`, `r_j³/r_k^(5−α) ≤ 1`, since occupied populations are at least one. There are fewer than `(2M)²` ordered pairs. The opposite/central estimate is at most a constant times `M⁻²` per pair because both populations are at most `15M`; its full sum is bounded by a constant. The comparable term is `O(N/M^α)`. The construction bounds `M² ≤ N ≤ 16M²` and `M^(2−α) ≤ N^(1−α/2)` close the estimate. Triangle inequalities for both finite sums convert the block bound to the absolute latitude error.

This proves the stated large-size latitude obligation and deliberately leaves the stronger individual regime asymptotics to the manuscript. The proof uses `α < 2`; the positive-exponent input is retained in the public theorem to match the project scope.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Latitude
import Mathlib.Analysis.PSeries

/-!
# Summing the latitude block estimates

This module isolates the finite arithmetic needed to pass from individual
latitude blocks to the full ordered latitude error.
-/

open scoped BigOperators

namespace BEMOC.Definitive

/-- The summable weight in a comparable latitude row. -/
private noncomputable def comparableWeight (α : ℝ) (d : ℕ) : ℝ :=
  ((d + 1 : ℕ) : ℝ) ^ (α - 3)

private theorem comparableWeight_summable {α : ℝ} (hα : α < 2) :
    Summable (comparableWeight α) := by
  have hbase : Summable (fun d : ℕ => (d : ℝ) ^ (α - 3)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  change Summable (fun d : ℕ => ((d + 1 : ℕ) : ℝ) ^ (α - 3))
  simpa [comparableWeight, Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff (f := fun d : ℕ => (d : ℝ) ^ (α - 3)) 1).2 hbase

/-- Each distance from a fixed band occurs at most twice. -/
private def distanceCode {n : ℕ} (j k : Fin n) : Fin n × Bool :=
  (⟨Nat.dist j.val k.val, by
      rw [Nat.dist_eq_max_sub_min]
      omega⟩, decide (k.val ≤ j.val))

private theorem distanceCode_injective {n : ℕ} (j : Fin n) :
    Function.Injective (distanceCode j) := by
  intro k l hkl
  have hd := congrArg (fun z : Fin n × Bool => (z.1 : ℕ)) hkl
  have hs := congrArg (fun z : Fin n × Bool => z.2) hkl
  dsimp [distanceCode] at hd hs
  by_cases hkj : k.val ≤ j.val <;> by_cases hlj : l.val ≤ j.val
  · rw [Nat.dist_eq_sub_of_le_right hkj,
      Nat.dist_eq_sub_of_le_right hlj] at hd
    exact Fin.ext (by omega)
  · simp [hkj, hlj] at hs
  · simp [hkj, hlj] at hs
  · rw [Nat.dist_eq_sub_of_le (by omega),
      Nat.dist_eq_sub_of_le (by omega)] at hd
    exact Fin.ext (by omega)

private theorem real_abs_sub_eq_nat_dist (j k : ℕ) :
    |(j : ℝ) - k| = (Nat.dist j k : ℝ) := by
  rcases le_total j k with h | h
  · have hr : (j : ℝ) ≤ k := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le h, abs_of_nonpos (by linarith), Nat.cast_sub h]
    ring
  · have hr : (k : ℝ) ≤ j := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le_right h, abs_of_nonneg (by linarith), Nat.cast_sub h]

/-- A finite comparable row has a bound independent of the number of bands. -/
theorem comparable_row_weight_le {α : ℝ} (hα : α < 2)
    {n : ℕ} (j : Fin n) :
    (∑ k : Fin n, (1 + |(j.val : ℝ) - k.val|) ^ (α - 3)) ≤
      2 * ∑' d : ℕ, comparableWeight α d := by
  classical
  let w := comparableWeight α
  let g : Fin n × Bool → ℝ := fun z => w z.1
  have hw : Summable w := comparableWeight_summable hα
  have hcode (k : Fin n) :
      (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) = g (distanceCode j k) := by
    rw [real_abs_sub_eq_nat_dist]
    simp [g, w, comparableWeight, distanceCode, add_comm]
  calc
    (∑ k : Fin n, (1 + |(j.val : ℝ) - k.val|) ^ (α - 3)) =
        ∑ z ∈ Finset.univ.image (distanceCode j), g z := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl (fun k _ => hcode k)
      · intro a _ b _ hab
        exact distanceCode_injective j hab
    _ ≤ ∑ z : Fin n × Bool, g z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro z _ _
      dsimp [g, w, comparableWeight]
      positivity
    _ = 2 * ∑ d : Fin n, w d := by
      rw [Fintype.sum_prod_type]
      simp only [g, Fintype.sum_bool]
      rw [Finset.sum_add_distrib]
      ring
    _ ≤ 2 * ∑' d : ℕ, w d := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Fin.sum_univ_eq_sum_range]
      exact hw.sum_le_tsum (Finset.range n) (fun d _ => by
        dsimp [w, comparableWeight]
        positivity)

/-- The ordered contribution of pairs whose populations are comparable. -/
private noncomputable def comparablePart (α : ℝ) (N : ℕ) : ℝ :=
  by
    classical
    exact ∑ j : RingIndex N,
      ∑ k ∈ Finset.univ.filter
        (fun k : RingIndex N => Comparable N (j.val + 1) (k.val + 1)),
        |kernelBlock α N (j.val + 1) (k.val + 1)|

/-- The comparable blocks sum at the claimed latitude scale in terms of `M`. -/
theorem comparable_part_le {α : ℝ} (hα : α < 2)
    (hblocks : ComparableBlockBound α) {N : ℕ} (hN : 1024 ≤ N) :
    comparablePart α N ≤
      hblocks.choose * (2 * ∑' d : ℕ, comparableWeight α d) *
        (N : ℝ) / (bandParameter N : ℝ) ^ α := by
  classical
  obtain ⟨hC, hbound⟩ := hblocks.choose_spec
  have hM : 0 < (bandParameter N : ℝ) := by
    exact_mod_cast bandParameter_pos (by omega : 4 ≤ N)
  have hMpow : 0 ≤ (bandParameter N : ℝ) ^ α :=
    Real.rpow_nonneg hM.le _
  have hweight : 0 ≤ 2 * ∑' d : ℕ, comparableWeight α d := by
    have hs := comparableWeight_summable hα
    have ht : 0 ≤ ∑' d : ℕ, comparableWeight α d :=
      tsum_nonneg (fun d => by unfold comparableWeight; positivity)
    positivity
  have hrow (j : RingIndex N) :
      (∑ k ∈ Finset.univ.filter
        (fun k : RingIndex N => Comparable N (j.val + 1) (k.val + 1)),
        |kernelBlock α N (j.val + 1) (k.val + 1)|) ≤
      hblocks.choose * (population N (j.val + 1) : ℝ) /
        (bandParameter N : ℝ) ^ α *
          (2 * ∑' d : ℕ, comparableWeight α d) := by
    let A : ℝ := hblocks.choose * (population N (j.val + 1) : ℝ) /
      (bandParameter N : ℝ) ^ α
    have hA : 0 ≤ A := by dsimp [A]; positivity
    calc
      _ ≤ ∑ k ∈ Finset.univ.filter
          (fun k : RingIndex N => Comparable N (j.val + 1) (k.val + 1)),
          A * (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
        apply Finset.sum_le_sum
        intro k hk
        have hc : Comparable N (j.val + 1) (k.val + 1) :=
          (Finset.mem_filter.mp hk).2
        simpa only [A] using hbound N hN j k hc
      _ ≤ ∑ k : RingIndex N,
          A * (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro k _ _
        exact mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
      _ = A * ∑ k : RingIndex N,
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
        rw [Finset.mul_sum]
      _ ≤ A * (2 * ∑' d : ℕ, comparableWeight α d) :=
        mul_le_mul_of_nonneg_left (comparable_row_weight_le hα j) hA
      _ = _ := rfl
  calc
    comparablePart α N ≤
        ∑ j : RingIndex N,
          hblocks.choose * (population N (j.val + 1) : ℝ) /
            (bandParameter N : ℝ) ^ α *
              (2 * ∑' d : ℕ, comparableWeight α d) := by
      unfold comparablePart
      exact Finset.sum_le_sum (fun j _ => hrow j)
    _ = hblocks.choose * (2 * ∑' d : ℕ, comparableWeight α d) *
        (N : ℝ) / (bandParameter N : ℝ) ^ α := by
      have hpop := population_sum_eq N (by omega : 4 ≤ N)
      have hpopr : (∑ j : RingIndex N, (population N (j.val + 1) : ℝ)) = N := by
        exact_mod_cast hpop
      calc
        _ = ∑ j : RingIndex N,
            (hblocks.choose * (2 * ∑' d : ℕ, comparableWeight α d) /
              (bandParameter N : ℝ) ^ α) *
              (population N (j.val + 1) : ℝ) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
        _ = _ := by rw [← Finset.mul_sum, hpopr]; ring

/-- An unequal same-side bound loses only one factor of `M⁻ᵅ` when summed crudely. -/
private theorem small_over_large_le_one {α a b : ℝ}
    (hα : α < 2) (ha : 0 ≤ a) (hb : 1 ≤ b) (hab : a ≤ b) :
    a ^ (3 : ℕ) / b ^ (5 - α) ≤ 1 := by
  have hpow : a ^ (3 : ℕ) ≤ b ^ (3 : ℕ) := by gcongr
  have hexp : (b : ℝ) ^ (3 : ℕ) ≤ b ^ (5 - α) := by
    have h := Real.rpow_le_rpow_of_exponent_le hb
      (show (3 : ℝ) ≤ 5 - α by linarith)
    calc
      b ^ (3 : ℕ) = b ^ (3 : ℝ) := (Real.rpow_natCast b 3).symm
      _ ≤ _ := h
  have hden : 0 < b ^ (5 - α) := Real.rpow_pos_of_pos (by linarith) _
  apply (div_le_iff₀ hden).2
  nlinarith

/-- The three pointwise regimes are exhaustive for every ordered pair. -/
private theorem block_le_three_majorants {α : ℝ}
    (hα : α < 2) (hsym : BlockSymmetry α)
    (hc : ComparableBlockBound α)
    (hs : SameSideBlockBound α) (ho : OppositeBlockBound α)
    {N : ℕ} (hN : 1024 ≤ N) (j k : RingIndex N) :
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
      hc.choose * (population N (j.val + 1) : ℝ) /
        (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) +
      hs.choose / (bandParameter N : ℝ) ^ α +
      ho.choose * (15 * (bandParameter N : ℝ)) ^ (6 : ℕ) /
        (bandParameter N : ℝ) ^ (8 : ℕ) := by
  have hN4 : 4 ≤ N := by omega
  have hM : 0 < (bandParameter N : ℝ) := by
    exact_mod_cast bandParameter_pos hN4
  have hpj : 1 ≤ (population N (j.val + 1) : ℝ) := by
    exact_mod_cast population_pos hN4 (by omega) (by have := j.isLt; omega)
  have hpk : 1 ≤ (population N (k.val + 1) : ℝ) := by
    exact_mod_cast population_pos hN4 (by omega) (by have := k.isLt; omega)
  have hpju : (population N (j.val + 1) : ℝ) ≤ 15 * bandParameter N := by
    exact_mod_cast population_le_fifteen hN4 (by omega) (by have := j.isLt; omega)
  have hpku : (population N (k.val + 1) : ℝ) ≤ 15 * bandParameter N := by
    exact_mod_cast population_le_fifteen hN4 (by omega) (by have := k.isLt; omega)
  have hAc : 0 ≤ hc.choose * (population N (j.val + 1) : ℝ) /
      (bandParameter N : ℝ) ^ α *
        (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
    have := hc.choose_spec.1
    positivity
  have hBs : 0 ≤ hs.choose / (bandParameter N : ℝ) ^ α := by
    have := hs.choose_spec.1
    positivity
  have hDo : 0 ≤ ho.choose * (15 * (bandParameter N : ℝ)) ^ (6 : ℕ) /
      (bandParameter N : ℝ) ^ (8 : ℕ) := by
    have := ho.choose_spec.1
    positivity
  by_cases hcomp : Comparable N (j.val + 1) (k.val + 1)
  · have h := hc.choose_spec.2 N hN j k hcomp
    linarith
  · have hsplit :
        8 * population N (j.val + 1) < population N (k.val + 1) ∨
        8 * population N (k.val + 1) < population N (j.val + 1) := by
      unfold Comparable at hcomp
      rcases not_and_or.mp hcomp with h | h
      · right
        have h' : (8 : ℝ) * population N (k.val + 1) < population N (j.val + 1) := by
          have hnot : ¬(population N (j.val + 1) : ℝ) / 8 ≤ population N (k.val + 1) := h
          push_neg at hnot
          nlinarith
        exact_mod_cast h'
      · left
        have h' : (8 : ℝ) * population N (j.val + 1) < population N (k.val + 1) := by
          push_neg at h
          nlinarith
        exact_mod_cast h'
    rcases hsplit with hsmall | hsmall
    · by_cases hside : SameSide N (j.val + 1) (k.val + 1)
      · have h := hs.choose_spec.2 N hN j k hsmall hside
        have hr : (population N (j.val + 1) : ℝ) ≤ population N (k.val + 1) := by
          exact_mod_cast (by omega : population N (j.val + 1) ≤ population N (k.val + 1))
        have hratio := small_over_large_le_one hα (by linarith : 0 ≤ (population N (j.val + 1) : ℝ)) hpk hr
        have hbound : hs.choose * (population N (j.val + 1) : ℝ) ^ (3 : ℕ) /
            ((bandParameter N : ℝ) ^ α * (population N (k.val + 1) : ℝ) ^ (5 - α)) ≤
            hs.choose / (bandParameter N : ℝ) ^ α := by
          have hq : 0 ≤ hs.choose / (bandParameter N : ℝ) ^ α := by exact hBs
          calc
            _ = (hs.choose / (bandParameter N : ℝ) ^ α) *
                ((population N (j.val + 1) : ℝ) ^ (3 : ℕ) /
                  (population N (k.val + 1) : ℝ) ^ (5 - α)) := by ring
            _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hratio hq]
        linarith

      · have h := ho.choose_spec.2 N hN j k hsmall hside
        have hpowj : (population N (j.val + 1) : ℝ) ^ (3 : ℕ) ≤
            (15 * (bandParameter N : ℝ)) ^ (3 : ℕ) := by gcongr
        have hpowk : (population N (k.val + 1) : ℝ) ^ (3 : ℕ) ≤
            (15 * (bandParameter N : ℝ)) ^ (3 : ℕ) := by gcongr
        have hprod : (population N (j.val + 1) : ℝ) ^ (3 : ℕ) *
            (population N (k.val + 1) : ℝ) ^ (3 : ℕ) ≤
            (15 * (bandParameter N : ℝ)) ^ (6 : ℕ) := by
          calc
            _ ≤ (15 * (bandParameter N : ℝ)) ^ (3 : ℕ) *
                (15 * (bandParameter N : ℝ)) ^ (3 : ℕ) :=
              mul_le_mul hpowj hpowk (by positivity) (by positivity)
            _ = _ := by ring
        have hbound : ho.choose * (population N (j.val + 1) : ℝ) ^ (3 : ℕ) *
            (population N (k.val + 1) : ℝ) ^ (3 : ℕ) /
              (bandParameter N : ℝ) ^ (8 : ℕ) ≤
            ho.choose * (15 * (bandParameter N : ℝ)) ^ (6 : ℕ) /
              (bandParameter N : ℝ) ^ (8 : ℕ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          convert mul_le_mul_of_nonneg_left hprod ho.choose_spec.1.le using 1; ring
        linarith
    · have hswap := hsym N hN4 j k
      rw [hswap]
      -- The reverse orientation has the same two unequal-scale alternatives.
      by_cases hside : SameSide N (k.val + 1) (j.val + 1)
      · have h := hs.choose_spec.2 N hN k j hsmall hside
        have hr : (population N (k.val + 1) : ℝ) ≤ population N (j.val + 1) := by
          exact_mod_cast (by omega : population N (k.val + 1) ≤ population N (j.val + 1))
        have hratio := small_over_large_le_one hα (by linarith : 0 ≤ (population N (k.val + 1) : ℝ)) hpj hr
        have hbound : hs.choose * (population N (k.val + 1) : ℝ) ^ (3 : ℕ) /
            ((bandParameter N : ℝ) ^ α * (population N (j.val + 1) : ℝ) ^ (5 - α)) ≤
            hs.choose / (bandParameter N : ℝ) ^ α := by
          calc
            _ = (hs.choose / (bandParameter N : ℝ) ^ α) *
                ((population N (k.val + 1) : ℝ) ^ (3 : ℕ) /
                  (population N (j.val + 1) : ℝ) ^ (5 - α)) := by ring
            _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hratio hBs]
        linarith
      · have h := ho.choose_spec.2 N hN k j hsmall hside
        have hpowj : (population N (j.val + 1) : ℝ) ^ (3 : ℕ) ≤
            (15 * (bandParameter N : ℝ)) ^ (3 : ℕ) := by gcongr
        have hpowk : (population N (k.val + 1) : ℝ) ^ (3 : ℕ) ≤
            (15 * (bandParameter N : ℝ)) ^ (3 : ℕ) := by gcongr
        have hprod : (population N (k.val + 1) : ℝ) ^ (3 : ℕ) *
            (population N (j.val + 1) : ℝ) ^ (3 : ℕ) ≤
            (15 * (bandParameter N : ℝ)) ^ (6 : ℕ) := by
          calc
            _ ≤ (15 * (bandParameter N : ℝ)) ^ (3 : ℕ) *
                (15 * (bandParameter N : ℝ)) ^ (3 : ℕ) :=
              mul_le_mul hpowk hpowj (by positivity) (by positivity)
            _ = _ := by ring
        have hbound : ho.choose * (population N (k.val + 1) : ℝ) ^ (3 : ℕ) *
            (population N (j.val + 1) : ℝ) ^ (3 : ℕ) /
              (bandParameter N : ℝ) ^ (8 : ℕ) ≤
            ho.choose * (15 * (bandParameter N : ℝ)) ^ (6 : ℕ) /
              (bandParameter N : ℝ) ^ (8 : ℕ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          convert mul_le_mul_of_nonneg_left hprod ho.choose_spec.1.le using 1; ring
        linarith

/-- The sum of all comparable-shaped majorants, without a pair filter. -/
private theorem comparable_majorants_sum_le {α : ℝ} (hα : α < 2)
    (hc : ComparableBlockBound α) {N : ℕ} (hN : 1024 ≤ N) :
    (∑ j : RingIndex N, ∑ k : RingIndex N,
      hc.choose * (population N (j.val + 1) : ℝ) /
        (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3)) ≤
      hc.choose * (2 * ∑' d : ℕ, comparableWeight α d) *
        (N : ℝ) / (bandParameter N : ℝ) ^ α := by
  have hM : 0 < (bandParameter N : ℝ) := by
    exact_mod_cast bandParameter_pos (by omega : 4 ≤ N)
  have hC : 0 ≤ hc.choose := hc.choose_spec.1.le
  have hrow (j : RingIndex N) :
      (∑ k : RingIndex N,
        hc.choose * (population N (j.val + 1) : ℝ) /
          (bandParameter N : ℝ) ^ α *
            (1 + |(j.val : ℝ) - k.val|) ^ (α - 3)) ≤
      hc.choose * (population N (j.val + 1) : ℝ) /
        (bandParameter N : ℝ) ^ α *
          (2 * ∑' d : ℕ, comparableWeight α d) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (comparable_row_weight_le hα j)
      (by positivity)
  calc
    _ ≤ ∑ j : RingIndex N,
        hc.choose * (population N (j.val + 1) : ℝ) /
          (bandParameter N : ℝ) ^ α *
            (2 * ∑' d : ℕ, comparableWeight α d) :=
      Finset.sum_le_sum (fun j _ => hrow j)
    _ = _ := by
      have hpop := population_sum_eq N (by omega : 4 ≤ N)
      have hpopr : (∑ j : RingIndex N, (population N (j.val + 1) : ℝ)) = N := by
        exact_mod_cast hpop
      calc
        _ = ∑ j : RingIndex N,
            (hc.choose * (2 * ∑' d : ℕ, comparableWeight α d) /
              (bandParameter N : ℝ) ^ α) *
              (population N (j.val + 1) : ℝ) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
        _ = _ := by rw [← Finset.mul_sum, hpopr]; ring

/-- The full absolute block sum is controlled by three explicit arithmetic terms. -/
private theorem block_abs_sum_le {α : ℝ} (hα : α < 2)
    (hsym : BlockSymmetry α) (hc : ComparableBlockBound α)
    (hs : SameSideBlockBound α) (ho : OppositeBlockBound α)
    {N : ℕ} (hN : 1024 ≤ N) :
    (∑ j : RingIndex N, ∑ k : RingIndex N,
      |kernelBlock α N (j.val + 1) (k.val + 1)|) ≤
      hc.choose * (2 * ∑' d : ℕ, comparableWeight α d) *
        (N : ℝ) / (bandParameter N : ℝ) ^ α +
      (2 * (bandParameter N : ℝ) - 1) ^ (2 : ℕ) *
        (hs.choose / (bandParameter N : ℝ) ^ α +
          ho.choose * (15 * (bandParameter N : ℝ)) ^ (6 : ℕ) /
            (bandParameter N : ℝ) ^ (8 : ℕ)) := by
  have hpoint (j k : RingIndex N) :=
    block_le_three_majorants hα hsym hc hs ho hN j k
  calc
    _ ≤ ∑ j : RingIndex N, ∑ k : RingIndex N,
        (hc.choose * (population N (j.val + 1) : ℝ) /
          (bandParameter N : ℝ) ^ α *
            (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) +
          hs.choose / (bandParameter N : ℝ) ^ α +
          ho.choose * (15 * (bandParameter N : ℝ)) ^ (6 : ℕ) /
            (bandParameter N : ℝ) ^ (8 : ℕ)) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum (fun k _ => hpoint j k)
    _ = (∑ j : RingIndex N, ∑ k : RingIndex N,
          hc.choose * (population N (j.val + 1) : ℝ) /
            (bandParameter N : ℝ) ^ α *
              (1 + |(j.val : ℝ) - k.val|) ^ (α - 3)) +
          (2 * (bandParameter N : ℝ) - 1) ^ (2 : ℕ) *
            (hs.choose / (bandParameter N : ℝ) ^ α +
              ho.choose * (15 * (bandParameter N : ℝ)) ^ (6 : ℕ) /
                (bandParameter N : ℝ) ^ (8 : ℕ)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const_zero]
      have hcard : (Fintype.card (RingIndex N) : ℝ) = 2 * bandParameter N - 1 := by
        have hM := bandParameter_pos (by omega : 4 ≤ N)
        simp only [RingIndex, Fintype.card_fin]
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * bandParameter N)]
        push_cast
        ring
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hcard]
      ring
    _ ≤ _ := by
      exact add_le_add_right (comparable_majorants_sum_le hα hc hN) _

/-- Elementary conversion of the three finite-sum majorants to the `N` scale. -/
private theorem arithmetic_majorants_le_scale
    {α M X A B D : ℝ} (hα : α < 2) (hM : 1 ≤ M)
    (hXlo : M ^ (2 : ℕ) ≤ X) (hXhi : X ≤ 16 * M ^ (2 : ℕ))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    A * X / M ^ α + (2 * M - 1) ^ (2 : ℕ) *
      (B / M ^ α + D * (15 * M) ^ (6 : ℕ) / M ^ (8 : ℕ)) ≤
      (16 * A + 4 * B + 4 * 15 ^ (6 : ℕ) * D) * X ^ (1 - α / 2) := by
  have hMpos : 0 < M := by linarith
  have hMα : 0 < M ^ α := Real.rpow_pos_of_pos hMpos _
  have hM2 : 0 < M ^ (2 : ℕ) := by positivity
  have hcount : (2 * M - 1) ^ (2 : ℕ) ≤ 4 * M ^ (2 : ℕ) := by
    nlinarith
  have hcount0 : 0 ≤ (2 * M - 1) ^ (2 : ℕ) := by positivity
  have hq : M ^ (2 - α) = M ^ (2 : ℕ) / M ^ α := by
    rw [Real.rpow_sub hMpos]
    norm_num [Real.rpow_natCast]
  have hscale : M ^ (2 - α) ≤ X ^ (1 - α / 2) := by
    have hr := Real.rpow_le_rpow (sq_nonneg M) hXlo
      (show 0 ≤ 1 - α / 2 by linarith)
    have heq : M ^ (2 - α) = (M ^ (2 : ℕ)) ^ (1 - α / 2) := by
      calc
        M ^ (2 - α) = M ^ ((2 : ℕ) * (1 - α / 2)) := by congr 1; norm_num; ring
        _ = _ := Real.rpow_natCast_mul hMpos.le 2 _
    rwa [heq]
  have hq1 : 1 ≤ M ^ (2 - α) :=
    Real.one_le_rpow hM (by linarith)
  have hcountD :
      (2 * M - 1) ^ (2 : ℕ) * D * (15 * M) ^ (6 : ℕ) / M ^ (8 : ℕ) ≤
      4 * 15 ^ (6 : ℕ) * D := by
    have hpow : (15 * M) ^ (6 : ℕ) / M ^ (8 : ℕ) =
        15 ^ (6 : ℕ) / M ^ (2 : ℕ) := by
      field_simp
      ring
    rw [mul_div_assoc, hpow]
    have hc : (2 * M - 1) ^ (2 : ℕ) / M ^ (2 : ℕ) ≤ 4 := by
      exact (div_le_iff₀ hM2).2 (by nlinarith [hcount])
    have hcoeff : 0 ≤ D * 15 ^ (6 : ℕ) := by positivity
    have hh := mul_le_mul_of_nonneg_right hc hcoeff
    convert hh using 1 <;> ring
  have hfirst : A * X / M ^ α ≤ 16 * A * M ^ (2 - α) := by
    rw [hq]
    have ht : A * X / M ^ α ≤ (16 * A * M ^ (2 : ℕ)) / M ^ α :=
      div_le_div_of_nonneg_right
        (by nlinarith [mul_le_mul_of_nonneg_left hXhi hA]) hMα.le
    convert ht using 1; ring
  have hsecond : (2 * M - 1) ^ (2 : ℕ) * B / M ^ α ≤
      4 * B * M ^ (2 - α) := by
    rw [hq]
    have ht : (2 * M - 1) ^ (2 : ℕ) * B / M ^ α ≤
        (4 * B * M ^ (2 : ℕ)) / M ^ α :=
      div_le_div_of_nonneg_right
        (by nlinarith [mul_le_mul_of_nonneg_right hcount hB]) hMα.le
    convert ht using 1; ring
  calc
    _ = A * X / M ^ α + (2 * M - 1) ^ (2 : ℕ) * B / M ^ α +
        (2 * M - 1) ^ (2 : ℕ) * D * (15 * M) ^ (6 : ℕ) / M ^ (8 : ℕ) := by ring
    _ ≤ 16 * A * M ^ (2 - α) + 4 * B * M ^ (2 - α) +
        4 * 15 ^ (6 : ℕ) * D := by
      gcongr
    _ ≤ (16 * A + 4 * B + 4 * 15 ^ (6 : ℕ) * D) * M ^ (2 - α) := by
      nlinarith [mul_le_mul_of_nonneg_left hq1
        (show 0 ≤ 4 * 15 ^ (6 : ℕ) * D by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)

/-- The exact latitude identity and the three exhaustive block estimates imply
the full latitude error bound for the Diamond configuration. -/
theorem latitude_bound_of_blocks {α : ℝ} (_hα0 : 0 < α) (hα2 : α < 2)
    (hidentity : LatitudeIdentity α) (hsym : BlockSymmetry α)
    (hc : ComparableBlockBound α) (hs : SameSideBlockBound α)
    (ho : OppositeBlockBound α) : LatitudeBound α := by
  let W : ℝ := 2 * ∑' d : ℕ, comparableWeight α d
  let A : ℝ := hc.choose * W
  let B : ℝ := hs.choose
  let D : ℝ := ho.choose
  let C : ℝ := 16 * A + 4 * B + 4 * 15 ^ (6 : ℕ) * D
  have hW : 0 ≤ W := by
    dsimp [W]
    exact mul_nonneg (by norm_num) (tsum_nonneg (fun d => by
      unfold comparableWeight
      positivity))
  have hA : 0 ≤ A := mul_nonneg hc.choose_spec.1.le hW
  have hB : 0 < B := hs.choose_spec.1
  have hD : 0 < D := ho.choose_spec.1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := by omega
  let M : ℝ := bandParameter N
  have hMnat : 1 ≤ bandParameter N := bandParameter_pos hN4
  have hM : 1 ≤ M := by
    change (1 : ℝ) ≤ bandParameter N
    exact_mod_cast hMnat
  have hXlo : M ^ (2 : ℕ) ≤ (N : ℝ) := by
    have h := (bandParameter_bounds N).1
    dsimp [M]
    exact_mod_cast (by omega : (bandParameter N) ^ 2 ≤ N)
  have hXhi : (N : ℝ) ≤ 16 * M ^ (2 : ℕ) := by
    have hb := (bandParameter_bounds N).2
    have hb' : (N : ℝ) < 4 * ((bandParameter N : ℝ) + 1) ^ (2 : ℕ) := by
      exact_mod_cast hb
    dsimp [M]
    nlinarith [sq_nonneg ((bandParameter N : ℝ) - 1)]
  have habs : |latitudeError α N| ≤
      ∑ j : RingIndex N, ∑ k : RingIndex N,
        |kernelBlock α N (j.val + 1) (k.val + 1)| := by
    rw [hidentity N hN4, abs_neg]
    calc
      |∑ j : RingIndex N, ∑ k : RingIndex N,
          kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        ∑ j : RingIndex N,
          |∑ k : RingIndex N, kernelBlock α N (j.val + 1) (k.val + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _)
  have hblocks := block_abs_sum_le hα2 hsym hc hs ho hN
  have harith := arithmetic_majorants_le_scale hα2 hM hXlo hXhi
    hA hB.le hD.le
  change |latitudeError α N| ≤ C * scale α N
  calc
    |latitudeError α N| ≤
        ∑ j : RingIndex N, ∑ k : RingIndex N,
          |kernelBlock α N (j.val + 1) (k.val + 1)| := habs
    _ ≤ A * (N : ℝ) / M ^ α +
        (2 * M - 1) ^ (2 : ℕ) *
          (B / M ^ α + D * (15 * M) ^ (6 : ℕ) / M ^ (8 : ℕ)) := by
      simpa only [A, B, D, W, M] using hblocks
    _ ≤ C * scale α N := by
      simpa only [C, A, B, D, M, scale] using harith

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
