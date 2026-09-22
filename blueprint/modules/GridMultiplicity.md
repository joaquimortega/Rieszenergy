# `BEMOCFormalization.GridMultiplicity`

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Trapezoid

/-! Finite-group counting for two angular grids, adapted from the legacy Core. -/

open scoped BigOperators Real

namespace BEMOC.Definitive.Grid

/-- Multiplication by an integer, descended from `ℤ` to a cyclic additive
group.  The divisibility assumption makes the map well-defined modulo `n`. -/
def zmodScaleHom (n m : ℕ) (c : ℤ) (h : (m : ℤ) ∣ (n : ℤ) * c) :
    ZMod n →+ ZMod m :=
  ZMod.lift n ⟨
    { toFun := fun z ↦ (z : ZMod m) * (c : ZMod m)
      map_zero' := by simp
      map_add' := by
        intro x y
        push_cast
        ring },
    by
      change ((n : ℤ) * c : ZMod m) = 0
      simpa only [Int.cast_mul] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) * c) m).2 h ⟩

@[simp]
theorem zmodScaleHom_intCast (n m : ℕ) (c z : ℤ)
    (h : (m : ℤ) ∣ (n : ℤ) * c) :
    zmodScaleHom n m c h (z : ZMod n) = (z * c : ℤ) := by
  simp [zmodScaleHom]

/-- Difference of polygon angles, measured on their common grid. -/
def gridDifferenceHom (d a b : ℕ) :
    ZMod (d * a) × ZMod (d * b) →+ ZMod (d * a * b) :=
  (zmodScaleHom (d * a) (d * a * b) b (by
      simpa only [Nat.cast_mul] using
        (dvd_refl ((d : ℤ) * (a : ℤ) * (b : ℤ))))).comp (AddMonoidHom.fst _ _) -
    (zmodScaleHom (d * b) (d * a * b) a (by
      convert (dvd_refl ((d : ℤ) * (a : ℤ) * (b : ℤ))) using 1
      all_goals
        push_cast
        ring)).comp (AddMonoidHom.snd _ _)

@[simp]
theorem gridDifferenceHom_intCast (d a b : ℕ) (i j : ℤ) :
    gridDifferenceHom d a b (i, j) =
      (b : ZMod (d * a * b)) * i - (a : ZMod (d * a * b)) * j := by
  simp [gridDifferenceHom, zmodScaleHom_intCast]
  ring

/-- Bézout's identity makes the common-grid difference map onto when the
reduced populations are coprime. -/
theorem gridDifferenceHom_surjective {d a b : ℕ} (hab : a.Coprime b) :
    Function.Surjective (gridDifferenceHom d a b) := by
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  refine ⟨((b.gcdA a * z : ℤ), (-b.gcdB a * z : ℤ)), ?_⟩
  rw [gridDifferenceHom_intCast]
  have hbezout : (1 : ℤ) = b * b.gcdA a + a * b.gcdB a := by
    rw [← Nat.gcd_eq_gcd_ab]
    exact_mod_cast hab.symm.gcd_eq_one.symm
  calc
    (b : ZMod (d * a * b)) * (b.gcdA a * z : ℤ) -
        (a : ZMod (d * a * b)) * (-b.gcdB a * z : ℤ) =
        ((b * b.gcdA a + a * b.gcdB a) * z : ℤ) := by
          push_cast
          ring
    _ = (z : ZMod (d * a * b)) := by rw [← hbezout, one_mul]

/-- In a coprime factorization, the common modulus is the lcm. -/
theorem lcm_mul_coprime {d a b : ℕ} (hab : a.Coprime b) :
    Nat.lcm (d * a) (d * b) = d * a * b := by
  rw [Nat.lcm_mul_left, hab.lcm_eq_mul]
  ring

/-- In the same factorization, `d` is the gcd of the populations. -/
theorem gcd_mul_coprime {d a b : ℕ} (hab : a.Coprime b) :
    Nat.gcd (d * a) (d * b) = d := by
  rw [Nat.gcd_mul_left, hab.gcd_eq_one, mul_one]

/-- The population product is gcd times lcm. -/
theorem population_product_eq_gcd_mul_lcm {d a b : ℕ} (hab : a.Coprime b) :
    (d * a) * (d * b) = d * Nat.lcm (d * a) (d * b) := by
  rw [lcm_mul_coprime hab]
  ring

/-- Every point on the lcm grid occurs with multiplicity `d` among the
ordered pairs of polygon vertices. -/
theorem gridDifference_fiber_card {d a b : ℕ} [NeZero d] [NeZero a] [NeZero b]
    (hab : a.Coprime b) (k : ZMod (d * a * b)) :
    ((Finset.univ : Finset (ZMod (d * a) × ZMod (d * b))).filter
      (fun ij ↦ gridDifferenceHom d a b ij = k)).card = d := by
  classical
  let f := gridDifferenceHom d a b
  let c := ((Finset.univ : Finset (ZMod (d * a) × ZMod (d * b))).filter
    (fun ij ↦ f ij = k)).card
  have hsurj : Function.Surjective f := gridDifferenceHom_surjective hab
  have hfiber (y : ZMod (d * a * b)) :
      ((Finset.univ : Finset (ZMod (d * a) × ZMod (d * b))).filter
        (fun ij ↦ f ij = y)).card = c := by
    apply AddMonoidHom.card_fiber_eq_of_mem_range f
    · exact hsurj y
    · exact hsurj k
  have hcard : (d * a * b) * c = (d * a) * (d * b) := by
    calc
      (d * a * b) * c =
          ∑ y : ZMod (d * a * b),
            ((Finset.univ : Finset (ZMod (d * a) × ZMod (d * b))).filter
              (fun ij ↦ f ij = y)).card := by
                simp_rw [hfiber]
                rw [Finset.sum_const, Finset.card_univ, ZMod.card]
                norm_num [nsmul_eq_mul]
      _ = Fintype.card (ZMod (d * a) × ZMod (d * b)) := by
            symm
            simpa using
              (Finset.card_eq_sum_card_fiberwise
                (s := (Finset.univ : Finset (ZMod (d * a) × ZMod (d * b))))
                (t := (Finset.univ : Finset (ZMod (d * a * b))))
                (f := f) (by simp))
      _ = (d * a) * (d * b) := by simp [ZMod.card]
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  have hm : 0 < d * a * b := by positivity
  have hc : c = d := by
    apply Nat.eq_of_mul_eq_mul_left hm
    calc
      (d * a * b) * c = (d * a) * (d * b) := hcard
      _ = (d * a * b) * d := by ring
  exact hc

/-- Multiset form of `gridDifference_fiber_card`: summing a function over
all ordered vertex pairs is `d` times its sum over the common grid. -/
theorem sum_gridDifference_eq_gcd_mul_sum {d a b : ℕ}
    [NeZero d] [NeZero a] [NeZero b] (hab : a.Coprime b)
    {A : Type*} [AddCommMonoid A] (F : ZMod (d * a * b) → A) :
    ∑ ij : ZMod (d * a) × ZMod (d * b), F (gridDifferenceHom d a b ij) =
      d • ∑ k : ZMod (d * a * b), F k := by
  classical
  rw [← Finset.sum_fiberwise' Finset.univ
    (fun ij ↦ gridDifferenceHom d a b ij) F]
  simp_rw [Finset.sum_const, gridDifference_fiber_card hab]
  rw [Finset.sum_nsmul]

/-! #### Direct interface for arbitrary positive populations -/

/-- Positivity of both populations makes their lcm a valid `ZMod` modulus. -/
instance neZero_lcm (q r : ℕ) [NeZero q] [NeZero r] : NeZero (Nat.lcm q r) :=
  ⟨(Nat.lcm_pos (Nat.pos_of_neZero q) (Nat.pos_of_neZero r)).ne'⟩

/-- Angular difference for arbitrary populations, valued directly in their
`lcm` grid. -/
def generalGridDifferenceHom (q r : ℕ) :
    ZMod q × ZMod r →+ ZMod (Nat.lcm q r) :=
  (zmodScaleHom q (Nat.lcm q r) (Int.ofNat (Nat.lcm q r / q)) (by
      have hq : q * (Nat.lcm q r / q) = Nat.lcm q r :=
        Nat.mul_div_cancel_left' (Nat.dvd_lcm_left q r)
      have hqz : (q : ℤ) * Int.ofNat (Nat.lcm q r / q) = Nat.lcm q r := by
        calc
          (q : ℤ) * Int.ofNat (Nat.lcm q r / q) =
              Int.ofNat (q * (Nat.lcm q r / q)) := Int.ofNat_mul_out _ _
          _ = Int.ofNat (Nat.lcm q r) := congrArg Int.ofNat hq
      rw [hqz])).comp (AddMonoidHom.fst _ _) -
    (zmodScaleHom r (Nat.lcm q r) (Int.ofNat (Nat.lcm q r / r)) (by
      have hr : r * (Nat.lcm q r / r) = Nat.lcm q r :=
        Nat.mul_div_cancel_left' (Nat.dvd_lcm_right q r)
      have hrz : (r : ℤ) * Int.ofNat (Nat.lcm q r / r) = Nat.lcm q r := by
        calc
          (r : ℤ) * Int.ofNat (Nat.lcm q r / r) =
              Int.ofNat (r * (Nat.lcm q r / r)) := Int.ofNat_mul_out _ _
          _ = Int.ofNat (Nat.lcm q r) := congrArg Int.ofNat hr
      rw [hrz])).comp (AddMonoidHom.snd _ _)

@[simp]
theorem generalGridDifferenceHom_intCast (q r : ℕ) (i j : ℤ) :
    generalGridDifferenceHom q r (i, j) =
      ((Nat.lcm q r / q : ℕ) : ZMod (Nat.lcm q r)) * i -
        ((Nat.lcm q r / r : ℕ) : ZMod (Nat.lcm q r)) * j := by
  simp [generalGridDifferenceHom, zmodScaleHom_intCast]
  have hqcast :
      (((Nat.lcm q r : ℤ) / (q : ℤ) : ℤ) : ZMod (Nat.lcm q r)) =
        ((Nat.lcm q r / q : ℕ) : ZMod (Nat.lcm q r)) := by
    calc
      (((Nat.lcm q r : ℤ) / (q : ℤ) : ℤ) : ZMod (Nat.lcm q r)) =
          (((Nat.lcm q r / q : ℕ) : ℤ) : ZMod (Nat.lcm q r)) :=
        congrArg (fun z : ℤ ↦ (z : ZMod (Nat.lcm q r)))
          (Int.natCast_div (Nat.lcm q r) q).symm
      _ = ((Nat.lcm q r / q : ℕ) : ZMod (Nat.lcm q r)) := Int.cast_natCast _
  have hrcast :
      (((Nat.lcm q r : ℤ) / (r : ℤ) : ℤ) : ZMod (Nat.lcm q r)) =
        ((Nat.lcm q r / r : ℕ) : ZMod (Nat.lcm q r)) := by
    calc
      (((Nat.lcm q r : ℤ) / (r : ℤ) : ℤ) : ZMod (Nat.lcm q r)) =
          (((Nat.lcm q r / r : ℕ) : ℤ) : ZMod (Nat.lcm q r)) :=
        congrArg (fun z : ℤ ↦ (z : ZMod (Nat.lcm q r)))
          (Int.natCast_div (Nat.lcm q r) r).symm
      _ = ((Nat.lcm q r / r : ℕ) : ZMod (Nat.lcm q r)) := Int.cast_natCast _
  rw [hqcast, hrcast]
  ring

/-- Dividing positive populations by their gcd gives coprime factors. -/
theorem div_gcd_coprime {q r : ℕ} [NeZero q] :
    (q / Nat.gcd q r).Coprime (r / Nat.gcd q r) := by
  apply Nat.coprime_div_gcd_div_gcd
  exact Nat.gcd_pos_of_pos_left r (Nat.pos_of_neZero q)

theorem lcm_div_left_eq_div_gcd_right {q r : ℕ} [NeZero q] [NeZero r] :
    Nat.lcm q r / q = r / Nat.gcd q r := by
  let d := Nat.gcd q r
  let a := q / d
  let b := r / d
  change Nat.lcm q r / q = b
  have hd : 0 < d := Nat.gcd_pos_of_pos_left r (Nat.pos_of_neZero q)
  have hq : d * a = q := Nat.mul_div_cancel_left' (Nat.gcd_dvd_left q r)
  have hr : d * b = r := Nat.mul_div_cancel_left' (Nat.gcd_dvd_right q r)
  have ha : 0 < a := by
    have hqpos : 0 < q := Nat.pos_of_neZero q
    nlinarith
  have hab : a.Coprime b := div_gcd_coprime
  have hL : Nat.lcm q r = d * a * b := by
    calc
      Nat.lcm q r = Nat.lcm (d * a) (d * b) := by rw [hq, hr]
      _ = d * a * b := lcm_mul_coprime hab
  rw [hL, ← hq]
  exact Nat.mul_div_cancel_left b (Nat.mul_pos hd ha)

theorem lcm_div_right_eq_div_gcd_left {q r : ℕ} [NeZero q] [NeZero r] :
    Nat.lcm q r / r = q / Nat.gcd q r := by
  rw [Nat.lcm_comm, Nat.gcd_comm]
  exact lcm_div_left_eq_div_gcd_right (q := r) (r := q)

/-- The direct angular-difference map is onto. -/
theorem generalGridDifferenceHom_surjective {q r : ℕ} [NeZero q] [NeZero r] :
    Function.Surjective (generalGridDifferenceHom q r) := by
  let d := Nat.gcd q r
  let a := q / d
  let b := r / d
  have hab : a.Coprime b := div_gcd_coprime
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  refine ⟨((b.gcdA a * z : ℤ), (-b.gcdB a * z : ℤ)), ?_⟩
  rw [generalGridDifferenceHom_intCast,
    lcm_div_left_eq_div_gcd_right, lcm_div_right_eq_div_gcd_left]
  have hbezout : (1 : ℤ) = b * b.gcdA a + a * b.gcdB a := by
    rw [← Nat.gcd_eq_gcd_ab]
    exact_mod_cast hab.symm.gcd_eq_one.symm
  calc
    (b : ZMod (Nat.lcm q r)) * (b.gcdA a * z : ℤ) -
        (a : ZMod (Nat.lcm q r)) * (-b.gcdB a * z : ℤ) =
        ((b * b.gcdA a + a * b.gcdB a) * z : ℤ) := by
          push_cast
          ring
    _ = (z : ZMod (Nat.lcm q r)) := by rw [← hbezout, one_mul]

/-- Every lcm-grid point occurs exactly `gcd q r` times among the `q*r`
ordered pairs. -/
theorem generalGridDifference_fiber_card {q r : ℕ} [NeZero q] [NeZero r]
    (k : ZMod (Nat.lcm q r)) :
    ((Finset.univ : Finset (ZMod q × ZMod r)).filter
      (fun ij ↦ generalGridDifferenceHom q r ij = k)).card = Nat.gcd q r := by
  classical
  let f := generalGridDifferenceHom q r
  let c := ((Finset.univ : Finset (ZMod q × ZMod r)).filter
    (fun ij ↦ f ij = k)).card
  have hsurj : Function.Surjective f := generalGridDifferenceHom_surjective
  have hfiber (y : ZMod (Nat.lcm q r)) :
      ((Finset.univ : Finset (ZMod q × ZMod r)).filter
        (fun ij ↦ f ij = y)).card = c := by
    apply AddMonoidHom.card_fiber_eq_of_mem_range f
    · exact hsurj y
    · exact hsurj k
  have hcard : Nat.lcm q r * c = q * r := by
    calc
      Nat.lcm q r * c =
          ∑ y : ZMod (Nat.lcm q r),
            ((Finset.univ : Finset (ZMod q × ZMod r)).filter
              (fun ij ↦ f ij = y)).card := by
                simp_rw [hfiber]
                rw [Finset.sum_const, Finset.card_univ, ZMod.card]
                norm_num [nsmul_eq_mul]
      _ = Fintype.card (ZMod q × ZMod r) := by
            symm
            simpa using
              (Finset.card_eq_sum_card_fiberwise
                (s := (Finset.univ : Finset (ZMod q × ZMod r)))
                (t := (Finset.univ : Finset (ZMod (Nat.lcm q r))))
                (f := f) (by simp))
      _ = q * r := by simp [ZMod.card]
  have hL : 0 < Nat.lcm q r :=
    Nat.lcm_pos (Nat.pos_of_neZero q) (Nat.pos_of_neZero r)
  apply Nat.eq_of_mul_eq_mul_left hL
  calc
    Nat.lcm q r * c = q * r := hcard
    _ = Nat.lcm q r * Nat.gcd q r := by
      rw [← Nat.gcd_mul_lcm]
      ring

/-- Direct finite-sum form used in Section 4: the `q*r` angular differences
are the lcm grid, each with gcd multiplicity. -/
theorem sum_generalGridDifference_eq_gcd_mul_sum {q r : ℕ}
    [NeZero q] [NeZero r] {A : Type*} [AddCommMonoid A]
    (F : ZMod (Nat.lcm q r) → A) :
    ∑ ij : ZMod q × ZMod r, F (generalGridDifferenceHom q r ij) =
      Nat.gcd q r • ∑ k : ZMod (Nat.lcm q r), F k := by
  classical
  rw [← Finset.sum_fiberwise' Finset.univ (generalGridDifferenceHom q r) F]
  simp_rw [Finset.sum_const, generalGridDifference_fiber_card]
  rw [Finset.sum_nsmul]

theorem periodic_generalGridDifference
    (f : ℝ → ℝ) (hf : Function.Periodic f (2 * Real.pi))
    {q r : ℕ} [NeZero q] [NeZero r]
    (phase : ℝ) (i : ZMod q) (j : ZMod r) :
    f
        (phase + 2 * Real.pi *
          ((generalGridDifferenceHom q r (i, j)).val : ℝ) /
            (Nat.lcm q r : ℝ)) =
      f
        (phase + 2 * Real.pi *
          ((i.val : ℝ) / (q : ℝ) - (j.val : ℝ) / (r : ℝ))) := by
  let L := Nat.lcm q r
  let a : ℕ := L / q
  let b : ℕ := L / r
  let k := generalGridDifferenceHom q r (i, j)
  let z : ℤ :=
    Int.ofNat a * Int.ofNat i.val -
      Int.ofNat b * Int.ofNat j.val
  have hkcast : (k.val : ZMod L) = (z : ZMod L) := by
    calc
      (k.val : ZMod L) = k := ZMod.natCast_zmod_val k
      _ = generalGridDifferenceHom q r
          ((i.val : ZMod q), (j.val : ZMod r)) := by
        rw [ZMod.natCast_zmod_val i, ZMod.natCast_zmod_val j]
      _ = (z : ZMod L) := by
        have h :=
          generalGridDifferenceHom_intCast q r
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
  exact (hf.int_mul m).sub_eq _

/-- The standard equivalence between finite labels and modular labels preserves
their canonical natural-number representatives. -/
private theorem finEquiv_symm_val (q : ℕ) [NeZero q] (i : ZMod q) :
    (((ZMod.finEquiv q).symm i : Fin q) : ℕ) = i.val := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

private theorem finEquiv_val (q : ℕ) [NeZero q] (i : Fin q) :
    (ZMod.finEquiv q i).val = i.val := by
  have h := finEquiv_symm_val q (ZMod.finEquiv q i)
  simpa using h.symm

/-- The generic finite aliasing identity, with arbitrary periodic real data. -/
theorem grid_multiplicity : BEMOC.Definitive.GridMultiplicity := by
  intro q r hq hr f hf φ
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero r := ⟨hr.ne'⟩
  let L := Nat.lcm q r
  let F : ZMod L → ℝ := fun k ↦
    f (φ + 2 * Real.pi * (k.val : ℝ) / (L : ℝ))
  have hpoint (i : ZMod q) (j : ZMod r) :
      f (φ + 2 * Real.pi *
          (((ZMod.finEquiv q).symm i).val / (q : ℝ) -
            ((ZMod.finEquiv r).symm j).val / (r : ℝ))) =
        F (generalGridDifferenceHom q r (i, j)) := by
    rw [finEquiv_symm_val q i, finEquiv_symm_val r j]
    exact (periodic_generalGridDifference f hf φ i j).symm
  have hleft :
      (∑ i : Fin q, ∑ j : Fin r,
        f (φ + 2 * Real.pi * ((i.val : ℝ) / q - (j.val : ℝ) / r))) =
      ∑ ij : ZMod q × ZMod r, F (generalGridDifferenceHom q r ij) := by
    let e : Fin q × Fin r ≃ ZMod q × ZMod r :=
      (ZMod.finEquiv q).prodCongr (ZMod.finEquiv r)
    let G : ZMod q × ZMod r → ℝ := fun ij ↦
      F (generalGridDifferenceHom q r ij)
    calc
      (∑ i : Fin q, ∑ j : Fin r,
          f (φ + 2 * Real.pi * ((i.val : ℝ) / q - (j.val : ℝ) / r))) =
        ∑ x : Fin q × Fin r,
          f (φ + 2 * Real.pi * ((x.1.val : ℝ) / q - (x.2.val : ℝ) / r)) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ x : Fin q × Fin r, G (e x) := by
        apply Finset.sum_congr rfl
        intro x hx
        simpa [e, G] using
          hpoint (ZMod.finEquiv q x.1) (ZMod.finEquiv r x.2)
      _ = ∑ ij : ZMod q × ZMod r, G ij := e.sum_comp G
      _ = ∑ ij : ZMod q × ZMod r,
          F (generalGridDifferenceHom q r ij) := rfl
  have hright :
      (∑ k : ZMod L, F k) =
      ∑ k : Fin L, f (φ + 2 * Real.pi * (k.val : ℝ) / L) := by
    let e : Fin L ≃ ZMod L := ZMod.finEquiv L
    rw [← e.sum_comp F]
    apply Finset.sum_congr rfl
    intro k hk
    change f (φ + 2 * Real.pi *
      (((ZMod.finEquiv L) k).val : ℝ) / L) =
      f (φ + 2 * Real.pi * (k.val : ℝ) / L)
    rw [finEquiv_val L k]
  rw [hleft, sum_generalGridDifference_eq_gcd_mul_sum, hright]
  simp [L, nsmul_eq_mul]


end BEMOC.Definitive.Grid
```

<!-- END_LEAN_STATEMENTS -->

**Checked status.** This module builds with Lean 4.19.0 and proves `BEMOC.Definitive.Grid.grid_multiplicity : BEMOC.Definitive.GridMultiplicity`. The theorem inhabits the exact proposition contract defined in `Trapezoid.lean`; it is not merely a similar identity with fixed cosine data. The source is the finite angular-grid argument in `definitive.tex`, Lemma `BalphaN`, lines 465–485. The finite-group counting lemmas are adapted from the legacy Core's `GridMultiplicity` namespace, while the generic periodic-function bridge adapts the congruence calculation in legacy `CrossRingPair.lean`. The file imports only current `Trapezoid.lean`, and none of the legacy modules, configuration geometry, or analytic Fourier estimates. It uses namespace `BEMOC.Definitive.Grid` to avoid collisions with the contract name and other formalizations.

**Group map.** For positive populations `q,r`, let `L=lcm(q,r)`. A pair of residues in `ZMod q × ZMod r` maps to the difference of their angles, measured on `ZMod L`: `(i,j)↦(L/q)i-(L/r)j`. The helper `zmodScaleHom` makes multiplication by an integer descend from `ℤ` to the quotient, using the divisibility of the target modulus by `q*(L/q)` and `r*(L/r)`. `generalGridDifferenceHom` combines the two maps. Its surjectivity follows from dividing `q,r` by `d=gcd(q,r)` to obtain coprime factors and applying Bézout's identity. The proof is independent of any function being summed.

**Fiber count and finite sum.** Every fiber of a surjective additive homomorphism between finite groups has the same size. The domain has `q*r` elements, the codomain has `L`, and `q*r=d*L`. Therefore each residue in `ZMod L` occurs exactly `d` times. The module expresses this as `generalGridDifference_fiber_card` and then applies `Finset.sum_fiberwise'` to obtain `sum_generalGridDifference_eq_gcd_mul_sum`. These facts use ordered pairs: `(i,j)` and `(j,i)` are distinct when their label types or values differ. When `q=r`, the diagonal pairs remain in the sum. When either population is one, `L` and the fiber count are still positive. All these cases are covered by the hypotheses `0<q`, `0<r`, without a separate coprimality requirement on the original populations.

**Real-angle congruence.** The group count alone concerns residues. `periodic_generalGridDifference` proves that for any `f : ℝ→ℝ` with period `2π`, the value at the representative angle `φ+2π k.val/L` equals the value at the original difference angle `φ+2π(i.val/q-j.val/r)`. It constructs the integer difference between `k.val` and `(L/q)i.val-(L/r)j.val`, divides by positive `L`, and shows the real angles differ by an integer multiple of `2π`. The final equality uses `Function.Periodic.int_mul` and `sub_eq`; no continuity, integrability, evenness, or cosine-specific identity is assumed. This is why the final theorem matches the fully generic contract.

**Interface bridge.** The proof reindexes each `Fin` vertex label through `ZMod.finEquiv`, whose canonical representative has the same natural value. It rewrites the nested `Fin q` and `Fin r` sums as a product sum on `ZMod q × ZMod r`, applies the finite-group sum theorem, and converts the resulting `ZMod L` sum back to `Fin L`. `nsmul_eq_mul` turns the group-theoretic multiplicity into the real scalar `Nat.gcd q r`. The arbitrary phase `φ` passes through unchanged. The endpoint `L=1` is valid because positive `q,r` imply positive lcm, and `ZMod 1` still has one element. The theorem does not use `0<α<2`, since it is purely combinatorial. A later longitude pair bound should apply it to the periodic angular distance-power kernel and combine it with the already proved `trapezoid_bound`.
