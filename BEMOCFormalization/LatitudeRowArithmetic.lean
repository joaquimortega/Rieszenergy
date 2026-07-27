import BEMOCFormalization.LatitudePairClassification
import BEMOCFormalization.LatitudePairSymmetry
import Mathlib.Analysis.PSeries

/-!
# Arithmetic of classified latitude rows

Finite rows are encoded by a distance/depth together with one bit recording
the side of the center.  Consequently each distance and each latitude depth
has multiplicity at most two.
-/

open scoped BigOperators Topology

namespace BEMOC

noncomputable def latitudeComparableSumConstant (α : ℝ) : ℝ :=
  2 * ∑' u : ℕ, ((u + 1 : ℕ) : ℝ) ^ (α - 3)

theorem summable_latitudeComparableWeight
    {α : ℝ} (hα2 : α < 2) :
    Summable (fun u : ℕ ↦ ((u + 1 : ℕ) : ℝ) ^ (α - 3)) := by
  have hbase : Summable (fun u : ℕ ↦ (u : ℝ) ^ (α - 3)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  simpa [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff (f := fun u : ℕ ↦ (u : ℝ) ^ (α - 3)) 1).2 hbase

theorem latitudeComparableSumConstant_pos
    {α : ℝ} (hα2 : α < 2) :
    0 < latitudeComparableSumConstant α := by
  have hs := summable_latitudeComparableWeight hα2
  have ht : 0 < ∑' u : ℕ, ((u + 1 : ℕ) : ℝ) ^ (α - 3) := by
    exact hs.tsum_pos (fun u ↦ Real.rpow_nonneg (by positivity) _) 0 (by positivity)
  unfold latitudeComparableSumConstant
  positivity

def latitudeDistanceCode {n : ℕ} (j k : Fin n) : Fin n × Bool :=
  (⟨Nat.dist (j : ℕ) (k : ℕ), by
      rw [Nat.dist_eq_max_sub_min]
      omega⟩,
    decide ((k : ℕ) ≤ (j : ℕ)))

theorem latitudeDistanceCode_injective {n : ℕ} (j : Fin n) :
    Function.Injective (latitudeDistanceCode j) := by
  intro k l hkl
  have hd := congrArg (fun z : Fin n × Bool ↦ (z.1 : ℕ)) hkl
  have hs := congrArg (fun z : Fin n × Bool ↦ z.2) hkl
  dsimp [latitudeDistanceCode] at hd hs
  by_cases hkj : (k : ℕ) ≤ (j : ℕ) <;>
    by_cases hlj : (l : ℕ) ≤ (j : ℕ)
  · rw [Nat.dist_eq_sub_of_le_right hkj,
      Nat.dist_eq_sub_of_le_right hlj] at hd
    apply Fin.ext
    omega
  · simp [hkj, hlj] at hs
  · simp [hkj, hlj] at hs
  · rw [Nat.dist_eq_sub_of_le (by omega),
      Nat.dist_eq_sub_of_le (by omega)] at hd
    apply Fin.ext
    omega

theorem sum_fin_latitudeComparableWeight_le
    {α : ℝ} (hα2 : α < 2) {n : ℕ} (j : Fin n) :
    (∑ k : Fin n,
      ((Nat.dist (j : ℕ) (k : ℕ) + 1 : ℕ) : ℝ) ^ (α - 3)) ≤
      latitudeComparableSumConstant α := by
  classical
  let w : ℕ → ℝ := fun u ↦ ((u + 1 : ℕ) : ℝ) ^ (α - 3)
  let g : Fin n × Bool → ℝ := fun z ↦ w z.1
  have hw : Summable w := summable_latitudeComparableWeight hα2
  have hcode (k : Fin n) :
      ((Nat.dist (j : ℕ) (k : ℕ) + 1 : ℕ) : ℝ) ^ (α - 3) =
        g (latitudeDistanceCode j k) := by rfl
  calc
    (∑ k : Fin n,
        ((Nat.dist (j : ℕ) (k : ℕ) + 1 : ℕ) : ℝ) ^ (α - 3)) =
        ∑ z ∈ Finset.univ.image (latitudeDistanceCode j), g z := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl fun k hk ↦ hcode k
      · intro a ha b hb hab
        exact latitudeDistanceCode_injective j hab
    _ ≤ ∑ z : Fin n × Bool, g z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro z hz hz'
      dsimp [g, w]
      positivity
    _ = 2 * ∑ u : Fin n, w u := by
      rw [Fintype.sum_prod_type]
      simp only [g, Fintype.sum_bool]
      rw [Finset.sum_add_distrib]
      ring
    _ ≤ 2 * ∑' u : ℕ, w u := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Fin.sum_univ_eq_sum_range]
      exact hw.sum_le_tsum (Finset.range n) fun u hu ↦ by
        dsimp [w]
        positivity
    _ = latitudeComparableSumConstant α := by
      rfl

/-- The pointwise L5 estimate implies the comparable part of every
classified row, with the universal convolution constant above. -/
theorem comparableLatitude_row_sum_le
    {α C : ℝ} (hα2 : α < 2) (hC : 0 ≤ C) {N : ℕ}
    (hpoint : HasComparableLatitudeBlockBound α N C)
    (j : Fin (bandTailCount N + 1)) :
    (∑ k ∈ comparableLatitudePartners N j,
      |bandPairError N j k (latitudeKernel α)|) ≤
      (C * latitudeComparableSumConstant α) *
        (latitudeBandScale N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) := by
  let A : ℝ := C * (latitudeBandScale N j : ℝ) *
    (bandCount N : ℝ) ^ (-α)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  calc
    (∑ k ∈ comparableLatitudePartners N j,
        |bandPairError N j k (latitudeKernel α)|) ≤
        ∑ k ∈ comparableLatitudePartners N j,
          A * ((Nat.dist (j : ℕ) (k : ℕ) + 1 : ℕ) : ℝ) ^ (α - 3) := by
      apply Finset.sum_le_sum
      intro k hk
      have hcomp : ComparableLatitudeScales N j k := by
        simpa [comparableLatitudePartners] using hk
      have hp := hpoint j k hcomp
      simpa only [A, Nat.cast_add, Nat.cast_one, add_comm] using hp
    _ ≤ ∑ k : Fin (bandTailCount N + 1),
          A * ((Nat.dist (j : ℕ) (k : ℕ) + 1 : ℕ) : ℝ) ^ (α - 3) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro k hk hk'
      exact mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
    _ = A * ∑ k : Fin (bandTailCount N + 1),
          ((Nat.dist (j : ℕ) (k : ℕ) + 1 : ℕ) : ℝ) ^ (α - 3) := by
      rw [Finset.mul_sum]
    _ ≤ A * latitudeComparableSumConstant α :=
      mul_le_mul_of_nonneg_left (sum_fin_latitudeComparableWeight_le hα2 j) hA
    _ = (C * latitudeComparableSumConstant α) *
        (latitudeBandScale N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) := by
      dsimp [A]
      ring

theorem latitudeBandScale_le_bandCount
    {N : ℕ} (hM : 1 ≤ bandCount N)
    (k : Fin (bandTailCount N + 1)) :
    latitudeBandScale N k ≤ bandCount N := by
  unfold latitudeBandScale bandTailCount
  omega

def latitudeDepthCode {N : ℕ} (hM : 1 ≤ bandCount N)
    (k : Fin (bandTailCount N + 1)) : Fin (bandCount N) × Bool :=
  (⟨latitudeBandScale N k - 1, by
      have hp := latitudeBandScale_pos N k
      have hu := latitudeBandScale_le_bandCount hM k
      omega⟩,
    decide ((k : ℕ) < bandCount N - 1))

theorem latitudeDepthCode_injective {N : ℕ} (hM : 1 ≤ bandCount N) :
    Function.Injective (latitudeDepthCode hM) := by
  intro k l hkl
  have hd := congrArg
    (fun z : Fin (bandCount N) × Bool ↦ (z.1 : ℕ)) hkl
  have hs := congrArg (fun z : Fin (bandCount N) × Bool ↦ z.2) hkl
  dsimp [latitudeDepthCode] at hd hs
  by_cases hk : (k : ℕ) < bandCount N - 1 <;>
    by_cases hl : (l : ℕ) < bandCount N - 1
  · rw [latitudeBandScale_eq_north hk,
      latitudeBandScale_eq_north hl] at hd
    apply Fin.ext
    omega
  · simp [hk, hl] at hs
  · simp [hk, hl] at hs
  · have hk' : bandCount N - 1 ≤ (k : ℕ) := by omega
    have hl' : bandCount N - 1 ≤ (l : ℕ) := by omega
    have hsk :
        latitudeBandScale N k = bandTailCount N + 1 - (k : ℕ) := by
      unfold latitudeBandScale
      rw [Nat.min_eq_right]
      simp [bandTailCount]
      omega
    have hsl :
        latitudeBandScale N l = bandTailCount N + 1 - (l : ℕ) := by
      unfold latitudeBandScale
      rw [Nat.min_eq_right]
      simp [bandTailCount]
      omega
    rw [hsk, hsl] at hd
    apply Fin.ext
    omega

/-- Every positive latitude depth occurs at most twice. -/
theorem sum_fin_latitudeDepthWeight_le
    {α : ℝ} (hα2 : α < 2) {N : ℕ}
    (hM : 1 ≤ bandCount N) :
    (∑ k : Fin (bandTailCount N + 1),
      (latitudeBandScale N k : ℝ) ^ (α - 3)) ≤
      latitudeComparableSumConstant α := by
  classical
  let w : ℕ → ℝ := fun u ↦ ((u + 1 : ℕ) : ℝ) ^ (α - 3)
  let g : Fin (bandCount N) × Bool → ℝ := fun z ↦ w z.1
  have hw : Summable w := summable_latitudeComparableWeight hα2
  have hcode (k : Fin (bandTailCount N + 1)) :
      (latitudeBandScale N k : ℝ) ^ (α - 3) =
        g (latitudeDepthCode hM k) := by
    dsimp [g, w, latitudeDepthCode]
    have hp := latitudeBandScale_pos N k
    congr 2
    omega
  calc
    (∑ k : Fin (bandTailCount N + 1),
        (latitudeBandScale N k : ℝ) ^ (α - 3)) =
        ∑ z ∈ Finset.univ.image (latitudeDepthCode hM), g z := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl fun k hk ↦ hcode k
      · intro a ha b hb hab
        exact latitudeDepthCode_injective hM hab
    _ ≤ ∑ z : Fin (bandCount N) × Bool, g z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro z hz hz'
      dsimp [g, w]
      positivity
    _ = 2 * ∑ u : Fin (bandCount N), w u := by
      rw [Fintype.sum_prod_type]
      simp only [g, Fintype.sum_bool]
      rw [Finset.sum_add_distrib]
      ring
    _ ≤ 2 * ∑' u : ℕ, w u := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Fin.sum_univ_eq_sum_range]
      exact hw.sum_le_tsum (Finset.range (bandCount N)) fun u hu ↦ by
        dsimp [w]
        positivity
    _ = latitudeComparableSumConstant α := by rfl

theorem unequalLatitudeWeight_le_comparableWeight
    {α : ℝ} {e d : ℕ} (he : 0 < e) (hed : e ≤ d) :
    (e : ℝ) ^ (3 : ℕ) * (d : ℝ) ^ (α - 5) ≤
      (e : ℝ) * (d : ℝ) ^ (α - 3) := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast he.trans_le hed
  have hpoly : (e : ℝ) ^ (3 : ℕ) ≤ (e : ℝ) * (d : ℝ) ^ (2 : ℕ) := by
    have heR : 0 ≤ (e : ℝ) := by positivity
    have hedR : (e : ℝ) ≤ (d : ℝ) := by exact_mod_cast hed
    calc
      (e : ℝ) ^ (3 : ℕ) = (e : ℝ) * (e : ℝ) ^ (2 : ℕ) := by ring
      _ ≤ (e : ℝ) * (d : ℝ) ^ (2 : ℕ) := by
        gcongr
  calc
    (e : ℝ) ^ (3 : ℕ) * (d : ℝ) ^ (α - 5) ≤
        ((e : ℝ) * (d : ℝ) ^ (2 : ℕ)) * (d : ℝ) ^ (α - 5) :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hd.le _)
    _ = (e : ℝ) * (d : ℝ) ^ (α - 3) := by
      rw [show (d : ℝ) ^ (2 : ℕ) = (d : ℝ) ^ (2 : ℝ) by
        exact (Real.rpow_natCast (d : ℝ) 2).symm,
        mul_assoc, ← Real.rpow_add hd]
      congr 2
      ring

/-- The oriented unequal-scale pointwise estimate gives the larger-part row.
The elementary inequality `e³ d^(α-5) ≤ e d^(α-3)` reduces it to the same
summable depth series as the comparable case. -/
theorem largerLatitude_row_sum_le
    {α C : ℝ} (hα2 : α < 2) (hC : 0 ≤ C) {N : ℕ}
    (hM : 1 ≤ bandCount N)
    (hpoint : HasUnequalLatitudeBlockBound α N C)
    (j : Fin (bandTailCount N + 1)) :
    (∑ k ∈ largerLatitudePartners N j,
      |bandPairError N j k (latitudeKernel α)|) ≤
      (C * latitudeComparableSumConstant α) *
        (latitudeBandScale N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) := by
  let A : ℝ := C * (bandCount N : ℝ) ^ (-α)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hej : 0 < latitudeBandScale N j := latitudeBandScale_pos N j
  calc
    (∑ k ∈ largerLatitudePartners N j,
        |bandPairError N j k (latitudeKernel α)|) ≤
        ∑ k ∈ largerLatitudePartners N j,
          A * ((latitudeBandScale N j : ℝ) *
            (latitudeBandScale N k : ℝ) ^ (α - 3)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkparts :
          ¬ ComparableLatitudeScales N j k ∧
            2 * latitudeBandScale N j < latitudeBandScale N k := by
        simpa only [largerLatitudePartners, Finset.mem_filter,
          Finset.mem_univ, true_and] using hk
      have hk' : 2 * latitudeBandScale N j < latitudeBandScale N k := by
        exact hkparts.2
      have hp := hpoint j k hk'
      have hw := unequalLatitudeWeight_le_comparableWeight (α := α)
        hej (show latitudeBandScale N j ≤ latitudeBandScale N k by omega)
      calc
        |bandPairError N j k (latitudeKernel α)| ≤
            C * (latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
              (bandCount N : ℝ) ^ (-α) *
                (latitudeBandScale N k : ℝ) ^ (α - 5) := by
          simpa [mul_assoc] using hp
        _ = A * ((latitudeBandScale N j : ℝ) ^ (3 : ℕ) *
              (latitudeBandScale N k : ℝ) ^ (α - 5)) := by
          dsimp [A]
          ring
        _ ≤ A * ((latitudeBandScale N j : ℝ) *
              (latitudeBandScale N k : ℝ) ^ (α - 3)) :=
          mul_le_mul_of_nonneg_left hw hA
    _ ≤ ∑ k : Fin (bandTailCount N + 1),
          A * ((latitudeBandScale N j : ℝ) *
            (latitudeBandScale N k : ℝ) ^ (α - 3)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro k hk hk'
      positivity
    _ = (A * (latitudeBandScale N j : ℝ)) *
        ∑ k : Fin (bandTailCount N + 1),
          (latitudeBandScale N k : ℝ) ^ (α - 3) := by
      rw [Finset.mul_sum]
      ring
    _ ≤ (A * (latitudeBandScale N j : ℝ)) *
        latitudeComparableSumConstant α := by
      apply mul_le_mul_of_nonneg_left
        (sum_fin_latitudeDepthWeight_le hα2 hM)
      positivity
    _ = (C * latitudeComparableSumConstant α) *
        (latitudeBandScale N j : ℝ) *
          (bandCount N : ℝ) ^ (-α) := by
      dsimp [A]
      ring

/-- At most two bands have any given positive depth.  Consequently the sum
of the cubes of all depths strictly below `e` is at most `2 e⁴`. -/
theorem sum_latitudeDepth_cube_lt_le
    {N e : ℕ} (hM : 1 ≤ bandCount N) (he : 0 < e) :
    (∑ k ∈ (Finset.univ.filter
        (fun k : Fin (bandTailCount N + 1) ↦ latitudeBandScale N k < e)),
      (latitudeBandScale N k : ℝ) ^ (3 : ℕ)) ≤
      2 * (e : ℝ) ^ (4 : ℕ) := by
  classical
  let S : Finset (Fin (bandTailCount N + 1)) :=
    Finset.univ.filter (fun k ↦ latitudeBandScale N k < e)
  let code : {k // k ∈ S} → Fin e × Bool := fun k ↦
    (⟨latitudeBandScale N k.1 - 1, by
        have hk : latitudeBandScale N k.1 < e := by
          simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using k.2
        have hp := latitudeBandScale_pos N k.1
        omega⟩,
      decide ((k.1 : ℕ) < bandCount N - 1))
  have hcode : Function.Injective code := by
    intro k l hkl
    apply Subtype.ext
    apply latitudeDepthCode_injective hM
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun z : Fin e × Bool ↦ (z.1 : ℕ)) hkl
    · exact congrArg (fun z : Fin e × Bool ↦ z.2) hkl
  have hcard : S.card ≤ 2 * e := by
    have hc := Fintype.card_le_of_injective code hcode
    simpa [Fintype.card_prod, Nat.mul_comm] using hc
  have hpoint (k : Fin (bandTailCount N + 1)) (hk : k ∈ S) :
      (latitudeBandScale N k : ℝ) ^ (3 : ℕ) ≤ (e : ℝ) ^ (3 : ℕ) := by
    have hke : latitudeBandScale N k ≤ e := by
      have : latitudeBandScale N k < e := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      omega
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hke) _
  calc
    (∑ k ∈ (Finset.univ.filter
        (fun k : Fin (bandTailCount N + 1) ↦ latitudeBandScale N k < e)),
      (latitudeBandScale N k : ℝ) ^ (3 : ℕ)) =
        ∑ k ∈ S, (latitudeBandScale N k : ℝ) ^ (3 : ℕ) := by rfl
    _ ≤ ∑ _k ∈ S, (e : ℝ) ^ (3 : ℕ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hpoint k hk
    _ = (S.card : ℝ) * (e : ℝ) ^ (3 : ℕ) := by
      simp
    _ ≤ ((2 * e : ℕ) : ℝ) * (e : ℝ) ^ (3 : ℕ) := by
      gcongr
    _ = 2 * (e : ℝ) ^ (4 : ℕ) := by
      push_cast
      ring

theorem latitudeHeadWeight_le_linear
    {α : ℝ} (hα2 : α < 2) {e : ℕ} (he : 0 < e) :
    (e : ℝ) ^ (4 : ℕ) * (e : ℝ) ^ (α - 5) ≤ (e : ℝ) := by
  have heR : 0 < (e : ℝ) := by exact_mod_cast he
  have he1 : 1 ≤ (e : ℝ) := by exact_mod_cast he
  calc
    (e : ℝ) ^ (4 : ℕ) * (e : ℝ) ^ (α - 5) =
        (e : ℝ) ^ ((4 : ℝ) + (α - 5)) := by
      rw [show (e : ℝ) ^ (4 : ℕ) = (e : ℝ) ^ (4 : ℝ) by
        exact (Real.rpow_natCast (e : ℝ) 4).symm,
        Real.rpow_add heR]
    _ = (e : ℝ) ^ (α - 1) := by congr 1 <;> ring
    _ ≤ (e : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le he1 (by linarith)
    _ = (e : ℝ) := by simp

/-- The reverse unequal-scale row follows from the oriented estimate after
swapping the symmetric kernel block.  The finite head contributes
`2 * sum_{d<e} d³`, and hence at most `2 e⁴`. -/
theorem smallerLatitude_row_sum_le_of_symm
    {α C : ℝ} (hα2 : α < 2) (hC : 0 ≤ C) {N : ℕ}
    (hM : 1 ≤ bandCount N)
    (hpoint : HasUnequalLatitudeBlockBound α N C)
    (hsymm : ∀ j k : Fin (bandTailCount N + 1),
      bandPairError N j k (latitudeKernel α) =
        bandPairError N k j (latitudeKernel α))
    (j : Fin (bandTailCount N + 1)) :
    (∑ k ∈ smallerLatitudePartners N j,
      |bandPairError N j k (latitudeKernel α)|) ≤
      (2 * C) * (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α) := by
  let e := latitudeBandScale N j
  let A : ℝ := C * (bandCount N : ℝ) ^ (-α) * (e : ℝ) ^ (α - 5)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he : 0 < e := latitudeBandScale_pos N j
  let S : Finset (Fin (bandTailCount N + 1)) :=
    Finset.univ.filter (fun k ↦ latitudeBandScale N k < e)
  calc
    (∑ k ∈ smallerLatitudePartners N j,
        |bandPairError N j k (latitudeKernel α)|) ≤
        ∑ k ∈ smallerLatitudePartners N j,
          A * (latitudeBandScale N k : ℝ) ^ (3 : ℕ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hsmall : 2 * latitudeBandScale N k < e := by
        dsimp [e]
        exact mem_smallerLatitudePartners_scale hk
      have hp := hpoint k j hsmall
      rw [hsymm j k]
      calc
        |bandPairError N k j (latitudeKernel α)| ≤
            C * (latitudeBandScale N k : ℝ) ^ (3 : ℕ) *
              (bandCount N : ℝ) ^ (-α) * (e : ℝ) ^ (α - 5) := by
          simpa [e, mul_assoc] using hp
        _ = A * (latitudeBandScale N k : ℝ) ^ (3 : ℕ) := by
          dsimp [A]
          ring
    _ ≤ ∑ k ∈ S, A * (latitudeBandScale N k : ℝ) ^ (3 : ℕ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        have hsmall := mem_smallerLatitudePartners_scale hk
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using
          (show latitudeBandScale N k < e by omega)
      · intro k hk hk'
        positivity
    _ = A * ∑ k ∈ S, (latitudeBandScale N k : ℝ) ^ (3 : ℕ) := by
      rw [Finset.mul_sum]
    _ ≤ A * (2 * (e : ℝ) ^ (4 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      simpa only [S] using sum_latitudeDepth_cube_lt_le hM he
    _ = (2 * C * (bandCount N : ℝ) ^ (-α)) *
        ((e : ℝ) ^ (4 : ℕ) * (e : ℝ) ^ (α - 5)) := by
      dsimp [A]
      ring
    _ ≤ (2 * C * (bandCount N : ℝ) ^ (-α)) * (e : ℝ) := by
      apply mul_le_mul_of_nonneg_left
        (latitudeHeadWeight_le_linear hα2 he)
      positivity
    _ = (2 * C) * (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α) := by
      dsimp [e]
      ring

/-- The actual latitude kernel is symmetric, so the reverse unequal-scale
row estimate has no additional hypothesis. -/
theorem smallerLatitude_row_sum_le
    {α C : ℝ} (hα : 0 < α) (hα2 : α < 2) (hC : 0 ≤ C) {N : ℕ}
    (hM : 1 ≤ bandCount N)
    (hpoint : HasUnequalLatitudeBlockBound α N C)
    (j : Fin (bandTailCount N + 1)) :
    (∑ k ∈ smallerLatitudePartners N j,
      |bandPairError N j k (latitudeKernel α)|) ≤
      (2 * C) * (latitudeBandScale N j : ℝ) *
        (bandCount N : ℝ) ^ (-α) := by
  exact smallerLatitude_row_sum_le_of_symm hα2 hC hM hpoint
    (fun j k ↦ latitudeKernel_bandPairError_swap hα N j k) j

/-- Complete arithmetic assembly of the pointwise comparable and
unequal-scale estimates into the three classified latitude rows. -/
theorem hasClassifiedLatitudeScaleRows_of_pointwise
    {α C : ℝ} (hα : 0 < α) (hα2 : α < 2) (hC : 0 ≤ C) {N : ℕ}
    (hM : 1 ≤ bandCount N)
    (hcomp : HasComparableLatitudeBlockBound α N C)
    (hunequal : HasUnequalLatitudeBlockBound α N C) :
    HasClassifiedLatitudeScaleRows α N
      (C * latitudeComparableSumConstant α)
      (C * latitudeComparableSumConstant α) (2 * C) where
  comparable := comparableLatitude_row_sum_le hα2 hC hcomp
  larger := largerLatitude_row_sum_le hα2 hC hM hunequal
  smaller := smallerLatitude_row_sum_le hα hα2 hC hM hunequal

/-- The same two pointwise inputs therefore discharge the complete
latitude block-estimate interface used by the axial/L2 bridge. -/
theorem hasCompleteLatitudeBlockEstimate_of_pointwise
    {α C : ℝ} (hα : 0 < α) (hα2 : α < 2) (hC : 0 ≤ C) {N : ℕ}
    (hM : 3 ≤ bandCount N)
    (hcomp : HasComparableLatitudeBlockBound α N C)
    (hunequal : HasUnequalLatitudeBlockBound α N C) :
    HasCompleteLatitudeBlockEstimate α N
      (C * latitudeComparableSumConstant α +
        C * latitudeComparableSumConstant α + 2 * C) := by
  have hclassified :=
    hasClassifiedLatitudeScaleRows_of_pointwise hα hα2 hC
      (show 1 ≤ bandCount N by omega) hcomp hunequal
  exact hclassified.toComplete hM
    (mul_nonneg hC (latitudeComparableSumConstant_pos hα2).le)
    (mul_nonneg hC (latitudeComparableSumConstant_pos hα2).le)
    (mul_nonneg (by norm_num) hC)

end BEMOC
