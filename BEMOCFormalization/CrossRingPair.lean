import BEMOCFormalization.CuspTrapezoid

/-!
# The gcd/lcm cross-ring pair estimate

This file first records the exact common-grid energy.  The geometric
reindexing of two polygons is separated from the analytic estimate so that
the ordered-pair normalisation remains visible.
-/

open scoped BigOperators Real
open Set

namespace BEMOC

open CuspTrapezoid

noncomputable def crossRingCommonGridEnergy
    (α : ℝ) (P Q : OccupiedRing) : ℝ :=
  (Nat.gcd P.population Q.population : ℝ) *
    ∑ k ∈ Finset.range (Nat.lcm P.population Q.population),
      angularPairKernel α P.height Q.height
        (P.phase - Q.phase +
          2 * Real.pi * (k : ℝ) /
            (Nat.lcm P.population Q.population : ℝ))

noncomputable def crossRingCommonGridDeficit
    (α : ℝ) (P Q : OccupiedRing) : ℝ :=
  continuousRingPairEnergy P Q α -
    crossRingCommonGridEnergy α P Q

noncomputable def discreteRingPairEnergy
    (α : ℝ) (P Q : OccupiedRing) : ℝ :=
  ∑ i : Fin P.population, ∑ j : Fin Q.population,
    dist (P.point i) (Q.point j) ^ α

theorem cos_generalGridDifference
    {q r : ℕ} [NeZero q] [NeZero r]
    (phase : ℝ) (i : ZMod q) (j : ZMod r) :
    Real.cos
        (phase + 2 * Real.pi *
          ((GridMultiplicity.generalGridDifferenceHom q r (i, j)).val : ℝ) /
            (Nat.lcm q r : ℝ)) =
      Real.cos
        (phase + 2 * Real.pi *
          ((i.val : ℝ) / (q : ℝ) - (j.val : ℝ) / (r : ℝ))) := by
  let L := Nat.lcm q r
  let a : ℕ := L / q
  let b : ℕ := L / r
  let k := GridMultiplicity.generalGridDifferenceHom q r (i, j)
  let z : ℤ :=
    Int.ofNat a * Int.ofNat i.val -
      Int.ofNat b * Int.ofNat j.val
  have hkcast : (k.val : ZMod L) = (z : ZMod L) := by
    calc
      (k.val : ZMod L) = k := ZMod.natCast_zmod_val k
      _ = GridMultiplicity.generalGridDifferenceHom q r
          ((i.val : ZMod q), (j.val : ZMod r)) := by
        rw [ZMod.natCast_zmod_val i, ZMod.natCast_zmod_val j]
      _ = (z : ZMod L) := by
        have h :=
          GridMultiplicity.generalGridDifferenceHom_intCast q r
            (i.val : ℤ) (j.val : ℤ)
        have hi : (i.val : ZMod q) = ((i.val : ℤ) : ZMod q) := by
          exact (Int.cast_natCast i.val).symm
        have hj : (j.val : ZMod r) = ((j.val : ℤ) : ZMod r) := by
          exact (Int.cast_natCast j.val).symm
        rw [hi, hj]
        rw [h]
        dsimp [z]
        push_cast
        rfl
  have hdvd : (L : ℤ) ∣ z - (k.val : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (k.val : ℤ) z L).1 <| by
      simpa only [Int.cast_natCast] using hkcast
  rcases hdvd with ⟨m, hm⟩
  have hqL : q * a = L :=
    Nat.mul_div_cancel_left' (Nat.dvd_lcm_left q r)
  have hrL : r * b = L :=
    Nat.mul_div_cancel_left' (Nat.dvd_lcm_right q r)
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_neZero q).ne'
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_neZero r).ne'
  have hL : (L : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_pos (Nat.pos_of_neZero q)
      (Nat.pos_of_neZero r)).ne'
  have hmR :
      (z : ℝ) - (k.val : ℝ) = (L : ℝ) * (m : ℝ) := by
    exact_mod_cast hm
  have hzR :
      (z : ℝ) / (L : ℝ) =
        (i.val : ℝ) / (q : ℝ) - (j.val : ℝ) / (r : ℝ) := by
    dsimp [z]
    push_cast
    change
      (((a : ℝ) * (i.val : ℝ) -
          (b : ℝ) * (j.val : ℝ)) / (L : ℝ)) =
        (i.val : ℝ) / (q : ℝ) - (j.val : ℝ) / (r : ℝ)
    have hqLR : (q : ℝ) * (a : ℝ) = (L : ℝ) := by
      exact_mod_cast hqL
    have hrLR : (r : ℝ) * (b : ℝ) = (L : ℝ) := by
      exact_mod_cast hrL
    field_simp [hq, hr, hL]
    calc
      ((a : ℝ) * i.cast - (b : ℝ) * j.cast) *
          ((q : ℝ) * (r : ℝ)) =
        (i.cast * (r : ℝ)) * ((q : ℝ) * (a : ℝ)) -
          ((q : ℝ) * j.cast) * ((r : ℝ) * (b : ℝ)) := by ring
      _ = (i.cast * (r : ℝ)) * (L : ℝ) -
          ((q : ℝ) * j.cast) * (L : ℝ) := by
        rw [hqLR, hrLR]
      _ = (i.cast * (r : ℝ) - (q : ℝ) * j.cast) * (L : ℝ) := by
        ring
  have harg :
      2 * Real.pi * (k.val : ℝ) / (L : ℝ) =
        2 * Real.pi *
            ((i.val : ℝ) / (q : ℝ) - (j.val : ℝ) / (r : ℝ)) -
          (m : ℝ) * (2 * Real.pi) := by
    rw [← hzR]
    have hkR :
        (k.val : ℝ) = (z : ℝ) - (L : ℝ) * (m : ℝ) := by
      linarith
    rw [hkR]
    field_simp [hL]
    ring
  rw [show phase +
        2 * Real.pi * (k.val : ℝ) / (L : ℝ) =
      (phase + 2 * Real.pi *
        ((i.val : ℝ) / (q : ℝ) - (j.val : ℝ) / (r : ℝ))) -
          (m : ℝ) * (2 * Real.pi) by rw [harg]; ring]
  exact Real.cos_sub_int_mul_two_pi _ m

theorem angularPairKernel_generalGridDifference
    {q r : ℕ} [NeZero q] [NeZero r]
    (α s t phase : ℝ) (i : ZMod q) (j : ZMod r) :
    angularPairKernel α s t
        (phase +
          2 * Real.pi *
            ((GridMultiplicity.generalGridDifferenceHom q r (i, j)).val : ℝ) /
              (Nat.lcm q r : ℝ)) =
      angularPairKernel α s t
        (phase +
          2 * Real.pi *
            ((i.val : ℝ) / (q : ℝ) - (j.val : ℝ) / (r : ℝ))) := by
  unfold angularPairKernel
  congr 2
  rw [cos_generalGridDifference phase i j]

theorem finEquiv_symm_val
    (q : ℕ) [NeZero q] (i : ZMod q) :
    (((ZMod.finEquiv q).symm i : Fin q) : ℕ) = i.val := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

set_option maxHeartbeats 800000 in
theorem discreteRingPairEnergy_eq_commonGrid
    {α : ℝ} (P Q : OccupiedRing)
    (hP : 0 < P.population) (hQ : 0 < Q.population) :
    discreteRingPairEnergy α P Q =
      crossRingCommonGridEnergy α P Q := by
  let q := P.population
  let r := Q.population
  letI : NeZero q := ⟨hP.ne'⟩
  letI : NeZero r := ⟨hQ.ne'⟩
  let L := Nat.lcm q r
  let F : ZMod L → ℝ := fun k ↦
    angularPairKernel α P.height Q.height
      (P.phase - Q.phase +
        2 * Real.pi * (k.val : ℝ) / (L : ℝ))
  have hpoint (i : ZMod q) (j : ZMod r) :
      dist
          (P.point ((ZMod.finEquiv q).symm i))
          (Q.point ((ZMod.finEquiv r).symm j)) ^ α =
        F (GridMultiplicity.generalGridDifferenceHom q r (i, j)) := by
    have hi := finEquiv_symm_val q i
    have hj := finEquiv_symm_val r j
    change
      dist
          (parallelPoint P.height
            (P.phase + 2 * Real.pi *
              (((ZMod.finEquiv q).symm i : Fin q) : ℝ) / (q : ℝ))
            P.height_mem)
          (parallelPoint Q.height
            (Q.phase + 2 * Real.pi *
              (((ZMod.finEquiv r).symm j : Fin r) : ℝ) / (r : ℝ))
            Q.height_mem) ^ α =
        F (GridMultiplicity.generalGridDifferenceHom q r (i, j))
    calc
      dist
          (parallelPoint P.height
            (P.phase + 2 * Real.pi *
              (((ZMod.finEquiv q).symm i : Fin q) : ℝ) / (q : ℝ))
            P.height_mem)
          (parallelPoint Q.height
            (Q.phase + 2 * Real.pi *
              (((ZMod.finEquiv r).symm j : Fin r) : ℝ) / (r : ℝ))
            Q.height_mem) ^ α =
        angularPairKernel α P.height Q.height
          (P.phase - Q.phase +
            2 * Real.pi *
              ((i.val : ℝ) / (q : ℝ) -
                (j.val : ℝ) / (r : ℝ))) := by
          rw [← angularPairKernel_eq_dist_rpow_sub
            (α := α)
            (θ := P.phase +
              2 * Real.pi *
                (((ZMod.finEquiv q).symm i : Fin q) : ℝ) / (q : ℝ))
            (φ := Q.phase +
              2 * Real.pi *
                (((ZMod.finEquiv r).symm j : Fin r) : ℝ) / (r : ℝ))
            P.height_mem Q.height_mem]
          congr 2
          push_cast
          rw [hi, hj]
          ring
      _ = F (GridMultiplicity.generalGridDifferenceHom q r (i, j)) := by
        dsimp [F, L]
        exact (angularPairKernel_generalGridDifference
          α P.height Q.height (P.phase - Q.phase) i j).symm
  have hfinToZmod :
      discreteRingPairEnergy α P Q =
        ∑ ij : ZMod q × ZMod r,
          F (GridMultiplicity.generalGridDifferenceHom q r ij) := by
    let e : Fin q × Fin r ≃ ZMod q × ZMod r :=
      (ZMod.finEquiv q).prodCongr (ZMod.finEquiv r)
    let G : ZMod q × ZMod r → ℝ := fun ij ↦
      F (GridMultiplicity.generalGridDifferenceHom q r ij)
    have hterm (x : Fin q × Fin r) :
        dist (P.point x.1) (Q.point x.2) ^ α = G (e x) := by
      simpa [e, G] using
        hpoint (ZMod.finEquiv q x.1) (ZMod.finEquiv r x.2)
    unfold discreteRingPairEnergy
    change (∑ i : Fin q, ∑ j : Fin r,
      dist (P.point i) (Q.point j) ^ α) = _
    calc
      (∑ i : Fin q, ∑ j : Fin r,
          dist (P.point i) (Q.point j) ^ α) =
        ∑ x : Fin q × Fin r,
          dist (P.point x.1) (Q.point x.2) ^ α := by
        rw [Fintype.sum_prod_type]
      _ = ∑ x : Fin q × Fin r, G (e x) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hterm x
      _ = ∑ ij : ZMod q × ZMod r, G ij := e.sum_comp G
      _ = ∑ ij : ZMod q × ZMod r,
          F (GridMultiplicity.generalGridDifferenceHom q r ij) := rfl
  rw [hfinToZmod,
    GridMultiplicity.sum_generalGridDifference_eq_gcd_mul_sum]
  unfold crossRingCommonGridEnergy
  dsimp [F, L, q, r]
  rw [nsmul_eq_mul]
  congr 1
  exact CuspTrapezoid.sum_zmod_val_eq_sum_range
    (Nat.lcm P.population Q.population)
    (fun k : ℕ ↦
      angularPairKernel α P.height Q.height
        (P.phase - Q.phase +
          2 * Real.pi * (k : ℝ) /
            (Nat.lcm P.population Q.population : ℝ)))

theorem crossRingCommonGridDeficit_eq_pairDeficit
    {α : ℝ} (P Q : OccupiedRing)
    (hP : 0 < P.population) (hQ : 0 < Q.population) :
    crossRingCommonGridDeficit α P Q =
      continuousRingPairEnergy P Q α -
        discreteRingPairEnergy α P Q := by
  rw [crossRingCommonGridDeficit, discreteRingPairEnergy_eq_commonGrid P Q hP hQ]

theorem latitudeKernel_eq_A_B_interval
    (α s t : ℝ) :
    latitudeKernel α s t =
      (1 / (2 * Real.pi)) *
        ∫ θ : ℝ in (0)..2 * Real.pi,
          (angularKernelA s t -
            angularKernelB s t * Real.cos θ) ^ (α / 2) := by
  unfold latitudeKernel
  apply congrArg ((1 / (2 * Real.pi)) * ·)
  apply intervalIntegral.integral_congr
  intro θ hθ
  exact angularPairKernel_eq_A_sub_B_cos α s t θ

theorem crossRingCommonGridEnergy_eq_A_B
    (α : ℝ) (P Q : OccupiedRing) :
    crossRingCommonGridEnergy α P Q =
      (Nat.gcd P.population Q.population : ℝ) *
        ∑ k ∈ Finset.range (Nat.lcm P.population Q.population),
          (angularKernelA P.height Q.height -
            angularKernelB P.height Q.height *
              Real.cos
                (P.phase - Q.phase +
                  2 * Real.pi * (k : ℝ) /
                    (Nat.lcm P.population Q.population : ℝ))) ^
              (α / 2) := by
  unfold crossRingCommonGridEnergy
  congr 1

theorem commonGrid_population_identity
    {q r : ℕ} :
    (q : ℝ) * (r : ℝ) =
      (Nat.gcd q r : ℝ) * (Nat.lcm q r : ℝ) := by
  exact_mod_cast (Nat.gcd_mul_lcm q r).symm

theorem gcd_mul_lcm_rpow_identity
    {α : ℝ} {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    (Nat.gcd q r : ℝ) *
        (Nat.lcm q r : ℝ) ^ (-α) =
      (Nat.gcd q r : ℝ) ^ (1 + α) /
        ((q : ℝ) * (r : ℝ)) ^ α := by
  have hd : 0 < (Nat.gcd q r : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left r hq
  have hL : 0 < (Nat.lcm q r : ℝ) := by
    exact_mod_cast Nat.lcm_pos hq hr
  have hprod :
      (q : ℝ) * (r : ℝ) =
        (Nat.gcd q r : ℝ) * (Nat.lcm q r : ℝ) :=
    commonGrid_population_identity
  rw [hprod, Real.mul_rpow hd.le hL.le,
    Real.rpow_add hd]
  rw [Real.rpow_one, Real.rpow_neg hL.le]
  field_simp [(Real.rpow_pos_of_pos hd α).ne',
    (Real.rpow_pos_of_pos hL α).ne']
  ring

/-- Pairwise cross-ring estimate in the exact form used by the arithmetic
summation. -/
theorem exists_crossRingCommonGridDeficit_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q : OccupiedRing),
      0 < P.population → 0 < Q.population →
      |crossRingCommonGridDeficit α P Q| ≤
        C * (P.radius * Q.radius) ^ (α / 2) *
          (Nat.gcd P.population Q.population : ℝ) ^ (1 + α) /
            (((P.population : ℝ) * (Q.population : ℝ)) ^ α) := by
  obtain ⟨C₀, hC₀, htrap⟩ :=
    exists_uniform_cusp_trapezoid_all hα0 hα2
  let C : ℝ := C₀ * (2 : ℝ) ^ (α / 2)
  have htwo : 0 < (2 : ℝ) ^ (α / 2) := by positivity
  refine ⟨C, mul_pos hC₀ htwo, ?_⟩
  intro P Q hP hQ
  have hcoeff := angularKernel_coefficients P.height_mem Q.height_mem
  let q := P.population
  let r := Q.population
  let d := Nat.gcd q r
  let L := Nat.lcm q r
  have hL : 1 ≤ L := by
    dsimp [L, q, r]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero hP.ne' hQ.ne')
  have htrapPair := htrap hcoeff.1 hcoeff.2 L hL (P.phase - Q.phase)
  let S : ℝ :=
    ∑ k ∈ Finset.range L,
      (angularKernelA P.height Q.height -
        angularKernelB P.height Q.height *
          Real.cos
            (P.phase - Q.phase +
              2 * Real.pi * (k : ℝ) / (L : ℝ))) ^ (α / 2)
  let M : ℝ :=
    (1 / (2 * Real.pi)) *
      ∫ θ : ℝ in (0)..2 * Real.pi,
        (angularKernelA P.height Q.height -
          angularKernelB P.height Q.height * Real.cos θ) ^ (α / 2)
  have htrapSM :
      |(1 / (L : ℝ)) * S - M| ≤
        C₀ * angularKernelB P.height Q.height ^ (α / 2) *
          (L : ℝ) ^ (-1 - α) := by
    simpa [S, M] using htrapPair
  have hLreal : (L : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt hL).ne'
  have hdnonneg : 0 ≤ (d : ℝ) := by positivity
  have hLnonneg : 0 ≤ (L : ℝ) := by positivity
  have hform :
      crossRingCommonGridDeficit α P Q =
        -((d : ℝ) * (L : ℝ)) *
          ((1 / (L : ℝ)) * S - M) := by
    unfold crossRingCommonGridDeficit
    rw [continuousRingPairEnergy_eq_latitudeKernel P Q hα0,
      crossRingCommonGridEnergy_eq_A_B,
      latitudeKernel_eq_A_B_interval]
    change (q : ℝ) * (r : ℝ) * M - (d : ℝ) * S =
      -((d : ℝ) * (L : ℝ)) * ((1 / (L : ℝ)) * S - M)
    have hpop : (q : ℝ) * (r : ℝ) = (d : ℝ) * (L : ℝ) := by
      dsimp [d, L]
      exact commonGrid_population_identity
    rw [hpop]
    field_simp [hLreal]
    ring
  have hscaled :
      |crossRingCommonGridDeficit α P Q| ≤
        C₀ * angularKernelB P.height Q.height ^ (α / 2) *
          ((d : ℝ) * (L : ℝ) ^ (-α)) := by
    rw [hform, abs_mul, abs_neg,
      abs_of_nonneg (mul_nonneg hdnonneg hLnonneg)]
    calc
      (d : ℝ) * (L : ℝ) * |(1 / (L : ℝ)) * S - M| ≤
          (d : ℝ) * (L : ℝ) *
            (C₀ * angularKernelB P.height Q.height ^ (α / 2) *
              (L : ℝ) ^ (-1 - α)) :=
        mul_le_mul_of_nonneg_left htrapSM
          (mul_nonneg hdnonneg hLnonneg)
      _ = C₀ * angularKernelB P.height Q.height ^ (α / 2) *
          ((d : ℝ) * (L : ℝ) ^ (-α)) := by
        have hLpos : 0 < (L : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hL
        rw [show -1 - α = -α + -1 by ring,
          Real.rpow_add hLpos,
          Real.rpow_neg_one]
        field_simp [hLreal]
        ring
  calc
    |crossRingCommonGridDeficit α P Q| ≤
        C₀ * angularKernelB P.height Q.height ^ (α / 2) *
          ((d : ℝ) * (L : ℝ) ^ (-α)) := hscaled
    _ = C * (P.radius * Q.radius) ^ (α / 2) *
          (d : ℝ) ^ (1 + α) /
            (((q : ℝ) * (r : ℝ)) ^ α) := by
      have hrP : 0 ≤ P.radius := P.radius_nonneg
      have hrQ : 0 ≤ Q.radius := Q.radius_nonneg
      rw [angularKernelB_eq_two_mul_radius P Q]
      rw [show 2 * P.radius * Q.radius =
          2 * (P.radius * Q.radius) by ring,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (mul_nonneg hrP hrQ)]
      rw [gcd_mul_lcm_rpow_identity
        (α := α) (q := q) (r := r) (by exact hP) (by exact hQ)]
      dsimp [C]
      ring
    _ = C * (P.radius * Q.radius) ^ (α / 2) *
          (Nat.gcd P.population Q.population : ℝ) ^ (1 + α) /
            (((P.population : ℝ) * (Q.population : ℝ)) ^ α) := by
      rfl

/-- The pairwise estimate for the literal point grids.  This is the form
summed over ordered pairs of distinct BEMOC rings. -/
theorem exists_discreteRingPairDeficit_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q : OccupiedRing),
      0 < P.population → 0 < Q.population →
      |continuousRingPairEnergy P Q α -
          discreteRingPairEnergy α P Q| ≤
        C * (P.radius * Q.radius) ^ (α / 2) *
          (Nat.gcd P.population Q.population : ℝ) ^ (1 + α) /
            (((P.population : ℝ) * (Q.population : ℝ)) ^ α) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_crossRingCommonGridDeficit_bound hα0 hα2
  refine ⟨C, hC, ?_⟩
  intro P Q hP hQ
  rw [← crossRingCommonGridDeficit_eq_pairDeficit P Q hP hQ]
  exact hbound P Q hP hQ

end BEMOC
