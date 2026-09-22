import BEMOCFormalization.CuspSmoothing

/-!
# Uniform trapezoidal estimates for the angular cusp

The root-grid identity below includes an arbitrary translate of the grid.
Its proof is just character orthogonality, but retaining the phase exactly is
important for the later comparison of two independently rotated polygons.
-/

open scoped BigOperators Topology Real
open Filter Set Complex MeasureTheory

namespace BEMOC

namespace CuspTrapezoid

open CuspSmoothing
open CircleFourier

noncomputable def shiftedRootGridAverage
    (L : ℕ) (f : C(AddCircle (1 : ℝ), ℂ))
    (a : AddCircle (1 : ℝ)) : ℂ :=
  if hL : L = 0 then 0 else
    letI : NeZero L := ⟨hL⟩
    (1 / (L : ℂ)) *
      ∑ j : ZMod L, f (CircleFourier.rootPoint L j + a)

theorem hasSum_fourierCoeff_filtered_by_shiftedRootGrid
    (L : ℕ) [NeZero L] (f : C(AddCircle (1 : ℝ), ℂ))
    (a : AddCircle (1 : ℝ)) (hs : Summable (fourierCoeff f)) :
    HasSum
      (fun n : ℤ =>
        if (n : ZMod L) = 0 then
          (L : ℂ) * fourierCoeff f n * fourier n a
        else 0)
      (∑ j : ZMod L, f (CircleFourier.rootPoint L j + a)) := by
  have hj : ∀ j ∈ (Finset.univ : Finset (ZMod L)),
      HasSum
        (fun n : ℤ => fourierCoeff f n *
          @fourier (1 : ℝ) n (CircleFourier.rootPoint L j + a))
        (f (CircleFourier.rootPoint L j + a)) := by
    intro j hj
    simpa only [smul_eq_mul] using
      has_pointwise_sum_fourier_series_of_summable hs
        (CircleFourier.rootPoint L j + a)
  have hsum := hasSum_sum hj
  refine HasSum.congr_fun hsum (fun n ↦ ?_)
  symm
  change (∑ j : ZMod L,
      fourierCoeff f n *
        fourier n (CircleFourier.rootPoint L j + a)) = _
  calc
    (∑ j : ZMod L,
        fourierCoeff f n *
          fourier n (CircleFourier.rootPoint L j + a)) =
      ∑ j : ZMod L,
        fourierCoeff f n *
          (fourier n (CircleFourier.rootPoint L j) * fourier n a) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [fourier_apply, zsmul_add, AddCircle.toCircle_add,
        Circle.coe_mul]
      rfl
    _ =
        fourierCoeff f n * fourier n a *
          ∑ j : ZMod L, fourier n (CircleFourier.rootPoint L j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = if (n : ZMod L) = 0 then
          (L : ℂ) * fourierCoeff f n * fourier n a else 0 := by
      rw [CircleFourier.sum_fourier_rootPoint]
      split_ifs <;> ring

theorem hasSum_fourierCoeff_multiples_shiftedRootGridAverage
    (L : ℕ) [NeZero L] (f : C(AddCircle (1 : ℝ), ℂ))
    (a : AddCircle (1 : ℝ)) (hs : Summable (fourierCoeff f)) :
    HasSum
      (fun m : ℤ =>
        fourierCoeff f ((L : ℤ) * m) *
          fourier ((L : ℤ) * m) a)
      (shiftedRootGridAverage L f a) := by
  have hLpos : 0 < L := Nat.pos_of_neZero L
  have hLcomplex : (L : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
  let filt : ℤ → ℂ := fun n ↦
    if (n : ZMod L) = 0 then
      fourierCoeff f n * fourier n a
    else 0
  have hraw :=
    hasSum_fourierCoeff_filtered_by_shiftedRootGrid L f a hs
  have hnorm : HasSum filt (shiftedRootGridAverage L f a) := by
    have hscaled := hraw.const_smul (1 / (L : ℂ))
    simpa only [shiftedRootGridAverage, NeZero.ne L, dite_false, filt] using
      hscaled.congr_fun (fun n ↦ by
        by_cases hn : (n : ZMod L) = 0
        · simp only [hn, if_true, one_div, smul_eq_mul]
          field_simp
          ring
        · simp only [hn, if_false, smul_zero])
  let g : ℤ → ℤ := fun m ↦ (L : ℤ) * m
  have hg : Function.Injective g := by
    intro m₁ m₂ hm
    dsimp [g] at hm
    exact mul_left_cancel₀ (by exact_mod_cast hLpos.ne') hm
  have hout : ∀ n ∉ Set.range g, filt n = 0 := by
    intro n hn
    dsimp [filt]
    rw [if_neg]
    intro hmod
    have hdvd : (L : ℤ) ∣ n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd n L).1 hmod
    rcases hdvd with ⟨m, hm⟩
    apply hn
    refine ⟨m, ?_⟩
    dsimp [g]
    simpa [mul_comm] using hm.symm
  have hreindexed : HasSum (filt ∘ g)
      (shiftedRootGridAverage L f a) :=
    (hg.hasSum_iff hout).2 hnorm
  refine hreindexed.congr_fun (fun m ↦ ?_)
  dsimp [filt, g, Function.comp_apply]
  rw [if_pos]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((L : ℤ) * m) L).2
    ⟨m, by ring⟩

theorem fourierCoeff_smoothedCuspCircle_neg
    {p δ : ℝ} (hp : 0 < p) (hδ : 0 ≤ δ) (n : ℤ) :
    fourierCoeff (smoothedCuspCircle p δ hp hδ) (-n) =
      fourierCoeff (smoothedCuspCircle p δ hp hδ) n := by
  rw [fourierCoeff_smoothedCuspCircle_eq_cosCoeff hp hδ,
    fourierCoeff_smoothedCuspCircle_eq_cosCoeff hp hδ]
  rw [smoothedCuspCosCoeff_neg]

theorem summable_fourierCoeff_smoothedCuspCircle
    {α δ : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hδ : 0 ≤ δ) :
    Summable
      (fourierCoeff
        (smoothedCuspCircle (α / 2) δ (by linarith) hδ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_fourierCoeff_smoothedCuspCircle_power_bound hα0 hα2
  have hpow : Summable (fun n : ℕ ↦
      C * (n : ℝ) ^ (-1 - α)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left C
  have hpos : Summable (fun n : ℕ ↦
      fourierCoeff
        (smoothedCuspCircle (α / 2) δ (by linarith) hδ) (n : ℤ)) := by
    apply hpow.of_norm_bounded_eventually_nat
    filter_upwards [eventually_atTop.2
      ⟨1, fun n hn ↦ hn⟩] with n hn
    exact hbound hδ n hn
  have hneg : Summable (fun n : ℕ ↦
      fourierCoeff
        (smoothedCuspCircle (α / 2) δ (by linarith) hδ)
          (-((n + 1 : ℕ) : ℤ))) := by
    have hshift : Summable (fun n : ℕ ↦
        C * ((n + 1 : ℕ) : ℝ) ^ (-1 - α)) := by
      exact ((summable_nat_add_iff 1).2
        (Real.summable_nat_rpow.mpr
          (by linarith : -1 - α < -1))).mul_left C
    apply hshift.of_norm_bounded
    intro n
    rw [fourierCoeff_smoothedCuspCircle_neg (by linarith) hδ]
    exact hbound hδ (n + 1) (by omega)
  exact Summable.of_nat_of_neg_add_one hpos hneg

theorem fourierCoeff_smoothedCuspCircle_int_bound
    {α δ : ℝ} (hα0 : 0 < α) (_hα2 : α < 2)
    (hδ : 0 ≤ δ) {C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n →
      ‖fourierCoeff
        (smoothedCuspCircle (α / 2) δ (by linarith) hδ) (n : ℤ)‖ ≤
          C * (n : ℝ) ^ (-1 - α))
    (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff
      (smoothedCuspCircle (α / 2) δ (by linarith) hδ) n‖ ≤
        C * (n.natAbs : ℝ) ^ (-1 - α) := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · have hk : 1 ≤ k := by
      by_contra hk
      have : k = 0 := by omega
      subst k
      exact hn rfl
    simpa using hbound k hk
  · have hk : 1 ≤ k := by
      by_contra hk
      have : k = 0 := by omega
      subst k
      exact hn rfl
    rw [fourierCoeff_smoothedCuspCircle_neg (by linarith) hδ]
    simpa using hbound k hk

noncomputable def cuspZetaTail (α : ℝ) : ℝ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-1 - α)

theorem summable_cuspZetaTail
    {α : ℝ} (hα0 : 0 < α) :
    Summable (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ) ^ (-1 - α)) := by
  exact (summable_nat_add_iff 1).2
    (Real.summable_nat_rpow.mpr (by linarith))

theorem cuspZetaTail_pos
    {α : ℝ} (hα0 : 0 < α) :
    0 < cuspZetaTail α := by
  unfold cuspZetaTail
  exact (summable_cuspZetaTail hα0).tsum_pos
    (fun n ↦ by positivity) 0 (by norm_num)

noncomputable def intPowerMajorant
    (α D : ℝ) (m : ℤ) : ℝ :=
  if m = 0 then 0 else
    D * (m.natAbs : ℝ) ^ (-1 - α)

theorem hasSum_intPowerMajorant
    {α D : ℝ} (hα0 : 0 < α) :
    HasSum (intPowerMajorant α D)
      (2 * D * cuspZetaTail α) := by
  have htail :
      HasSum
        (fun n : ℕ ↦
          D * ((n + 1 : ℕ) : ℝ) ^ (-1 - α))
        (D * cuspZetaTail α) := by
    exact (summable_cuspZetaTail hα0).hasSum.mul_left D
  have hnatTail :
      HasSum
        (fun n : ℕ ↦
          intPowerMajorant α D ((n + 1 : ℕ) : ℤ))
        (D * cuspZetaTail α) := by
    refine htail.congr_fun (fun n ↦ ?_)
    rw [intPowerMajorant, if_neg (by omega)]
    rw [Int.natAbs_ofNat]
  have hnat :
      HasSum
        (fun n : ℕ ↦ intPowerMajorant α D (n : ℤ))
        (D * cuspZetaTail α) := by
    let fNat : ℕ → ℝ :=
      fun n ↦ intPowerMajorant α D (n : ℤ)
    have htail' : HasSum (fun n : ℕ ↦ fNat (n + 1))
        (D * cuspZetaTail α) := by
      simpa only [fNat] using hnatTail
    have hfull := (hasSum_nat_add_iff 1).1 htail'
    simpa [fNat, intPowerMajorant] using hfull
  have hneg :
      HasSum
        (fun n : ℕ ↦
          intPowerMajorant α D (-((n + 1 : ℕ) : ℤ)))
        (D * cuspZetaTail α) := by
    refine htail.congr_fun (fun n ↦ ?_)
    rw [intPowerMajorant, if_neg (by omega)]
    rw [Int.natAbs_neg, Int.natAbs_ofNat]
  have hboth := hnat.of_nat_of_neg_add_one hneg
  convert hboth using 1
  ring

theorem hasSum_shiftedRootGridError
    (L : ℕ) [NeZero L] (f : C(AddCircle (1 : ℝ), ℂ))
    (a : AddCircle (1 : ℝ)) (hs : Summable (fourierCoeff f)) :
    HasSum
      (fun m : ℤ =>
        if m = 0 then 0 else
          fourierCoeff f ((L : ℤ) * m) *
            fourier ((L : ℤ) * m) a)
      (shiftedRootGridAverage L f a - fourierCoeff f 0) := by
  have hall :=
    hasSum_fourierCoeff_multiples_shiftedRootGridAverage L f a hs
  have hsingle : HasSum
      (fun m : ℤ ↦ if m = 0 then fourierCoeff f 0 else 0)
      (fourierCoeff f 0) :=
    hasSum_ite_eq 0 (fourierCoeff f 0)
  have hsub := hall.sub hsingle
  refine hsub.congr_fun (fun m ↦ ?_)
  by_cases hm : m = 0
  · subst m
    simp
  · simp only [hm, if_false]
    ring

theorem shiftedRootGridError_le
    {α δ C : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hδ : 0 ≤ δ)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      ‖fourierCoeff
        (smoothedCuspCircle (α / 2) δ (by linarith) hδ) (n : ℤ)‖ ≤
          C * (n : ℝ) ^ (-1 - α))
    (L : ℕ) (hL : 1 ≤ L) (a : AddCircle (1 : ℝ)) :
    ‖shiftedRootGridAverage L
        (smoothedCuspCircle (α / 2) δ (by linarith) hδ) a -
      fourierCoeff
        (smoothedCuspCircle (α / 2) δ (by linarith) hδ) 0‖ ≤
      (2 * C * cuspZetaTail α) * (L : ℝ) ^ (-1 - α) := by
  letI : NeZero L := ⟨(Nat.zero_lt_of_lt hL).ne'⟩
  let f := smoothedCuspCircle (α / 2) δ (by linarith) hδ
  let D : ℝ := C * (L : ℝ) ^ (-1 - α)
  have herr := hasSum_shiftedRootGridError L f a
    (summable_fourierCoeff_smoothedCuspCircle hα0 hα2 hδ)
  have hmaj := hasSum_intPowerMajorant (D := D) hα0
  have hterm : ∀ m : ℤ,
      ‖if m = 0 then 0 else
          fourierCoeff f ((L : ℤ) * m) *
            fourier ((L : ℤ) * m) a‖ ≤
        intPowerMajorant α D m := by
    intro m
    by_cases hm : m = 0
    · simp [hm, intPowerMajorant]
    · simp only [hm, if_false, intPowerMajorant]
      rw [norm_mul, show ‖fourier ((L : ℤ) * m) a‖ = 1 by
        exact Circle.norm_coe _, mul_one]
      have hLm : (L : ℤ) * m ≠ 0 :=
        mul_ne_zero (by exact_mod_cast (Nat.zero_lt_of_lt hL).ne') hm
      calc
        ‖fourierCoeff f ((L : ℤ) * m)‖ ≤
            C * ((((L : ℤ) * m).natAbs : ℕ) : ℝ) ^ (-1 - α) :=
          fourierCoeff_smoothedCuspCircle_int_bound hα0 hα2 hδ
            hbound ((L : ℤ) * m) hLm
        _ = D * (m.natAbs : ℝ) ^ (-1 - α) := by
          rw [Int.natAbs_mul]
          simp only [Int.natAbs_ofNat, Nat.cast_mul]
          rw [Real.mul_rpow (Nat.cast_nonneg L)
            (Nat.cast_nonneg m.natAbs)]
          dsimp [D]
          ring
  have hnorm := herr.norm_le_of_bounded hmaj hterm
  calc
    _ ≤ 2 * D * cuspZetaTail α := hnorm
    _ = (2 * C * cuspZetaTail α) * (L : ℝ) ^ (-1 - α) := by
      dsimp [D]
      ring

/-- Uniform translated root-grid estimate for all smoothed cusps. -/
theorem exists_uniform_smoothedCusp_trapezoid
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {δ : ℝ} (hδ : 0 ≤ δ)
      (L : ℕ), 1 ≤ L → ∀ a : AddCircle (1 : ℝ),
      ‖shiftedRootGridAverage L
          (smoothedCuspCircle (α / 2) δ (by linarith) hδ) a -
        fourierCoeff
          (smoothedCuspCircle (α / 2) δ (by linarith) hδ) 0‖ ≤
        K * (L : ℝ) ^ (-1 - α) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_fourierCoeff_smoothedCuspCircle_power_bound hα0 hα2
  let K := 2 * C * cuspZetaTail α
  refine ⟨K, by
    exact mul_pos (mul_pos (by norm_num) hC) (cuspZetaTail_pos hα0), ?_⟩
  intro δ hδ L hL a
  exact shiftedRootGridError_le hα0 hα2 hδ (hbound hδ) L hL a

theorem circleCos_one_coe (x : ℝ) :
    circleCos 1 (x : AddCircle (1 : ℝ)) =
      Real.cos (2 * Real.pi * x) := by
  unfold circleCos
  rw [fourier_coe_apply]
  ring_nf
  rw [show (Real.pi : ℂ) * Complex.I * (x : ℂ) *
      ((1 : ℝ) : ℂ)⁻¹ * 2 =
      ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
        push_cast
        ring]
  convert Complex.exp_ofReal_mul_I_re (2 * Real.pi * x) using 1 ; ring_nf

theorem smoothedCuspCircle_coe
    {p δ : ℝ} (hp : 0 < p) (hδ : 0 ≤ δ) (x : ℝ) :
    smoothedCuspCircle p δ hp hδ (x : AddCircle (1 : ℝ)) =
      ((δ + 1 - Real.cos (2 * Real.pi * x)) ^ p : ℝ) := by
  change ((smoothedCuspBase δ (x : AddCircle (1 : ℝ)) ^ p : ℝ) : ℂ) = _
  unfold smoothedCuspBase
  rw [circleCos_one_coe]

theorem smoothedCuspCircle_shiftedRootPoint
    {p δ φ : ℝ} (hp : 0 < p) (hδ : 0 ≤ δ)
    (L : ℕ) [NeZero L] (j : ZMod L) :
    smoothedCuspCircle p δ hp hδ
        (CircleFourier.rootPoint L j +
          (φ / (2 * Real.pi) : AddCircle (1 : ℝ))) =
      ((δ + 1 -
        Real.cos (φ + 2 * Real.pi * (j.val : ℝ) / (L : ℝ))) ^ p : ℝ) := by
  unfold CircleFourier.rootPoint
  rw [← AddCircle.coe_add]
  rw [smoothedCuspCircle_coe hp hδ]
  congr 3
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  field_simp
  ring_nf

theorem sum_zmod_val_eq_sum_range
    (L : ℕ) [NeZero L] (F : ℕ → ℝ) :
    (∑ j : ZMod L, F j.val) =
      ∑ k ∈ Finset.range L, F k := by
  calc
    (∑ j : ZMod L, F j.val) =
        ∑ i : Fin L, F ((ZMod.finEquiv L i).val) := by
      exact ((ZMod.finEquiv L).sum_comp
        (fun j : ZMod L ↦ F j.val)).symm
    _ = ∑ i : Fin L, F i := by
      apply Finset.sum_congr rfl
      intro i hi
      cases L with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ L => rfl
    _ = ∑ k ∈ Finset.range L, F k :=
      Fin.sum_univ_eq_sum_range F L

theorem shiftedRootGridAverage_smoothed_eq
    {p δ φ : ℝ} (hp : 0 < p) (hδ : 0 ≤ δ)
    (L : ℕ) (hL : 1 ≤ L) :
    shiftedRootGridAverage L (smoothedCuspCircle p δ hp hδ)
        (φ / (2 * Real.pi) : AddCircle (1 : ℝ)) =
      ((1 / (L : ℝ)) *
        ∑ k ∈ Finset.range L,
          (δ + 1 -
            Real.cos (φ + 2 * Real.pi * (k : ℝ) / (L : ℝ))) ^ p : ℝ) := by
  letI : NeZero L := ⟨(Nat.zero_lt_of_lt hL).ne'⟩
  unfold shiftedRootGridAverage
  rw [dif_neg (NeZero.ne L)]
  simp_rw [smoothedCuspCircle_shiftedRootPoint hp hδ]
  push_cast
  have hsum := sum_zmod_val_eq_sum_range L
    (fun k : ℕ ↦
      (δ + 1 -
        Real.cos (φ + 2 * Real.pi * (k : ℝ) / (L : ℝ))) ^ p)
  have hsumC := congrArg (fun r : ℝ ↦ (r : ℂ)) hsum
  push_cast at hsumC
  rw [hsumC]

theorem fourierCoeff_smoothedCuspCircle_zero_eq_interval
    {p δ : ℝ} (hp : 0 < p) (hδ : 0 ≤ δ) :
    fourierCoeff (smoothedCuspCircle p δ hp hδ) 0 =
      (((1 / (2 * Real.pi)) *
        ∫ θ : ℝ in (0)..2 * Real.pi,
          (δ + 1 - Real.cos θ) ^ p : ℝ) : ℂ) := by
  let g : ℝ → ℂ := fun θ ↦
    (((δ + 1 - Real.cos θ) ^ p : ℝ) : ℂ)
  have hchange := intervalIntegral.integral_comp_mul_left g
    (show 2 * Real.pi ≠ 0 by positivity)
    (a := (0 : ℝ)) (b := 1)
  norm_num only [mul_zero, mul_one, one_div] at hchange
  rw [fourierCoeff_eq_intervalIntegral
    (smoothedCuspCircle p δ hp hδ) 0 0]
  simp only [zero_add, one_div, inv_one, one_smul, neg_zero, fourier_zero]
  calc
    (∫ x : ℝ in (0)..1,
        smoothedCuspCircle p δ hp hδ
          (x : AddCircle (1 : ℝ))) =
        ∫ x : ℝ in (0)..1, g ((2 * Real.pi) * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change smoothedCuspCircle p δ hp hδ
          (x : AddCircle (1 : ℝ)) = g (2 * Real.pi * x)
      rw [smoothedCuspCircle_coe hp hδ]
    _ = (2 * Real.pi)⁻¹ •
        ∫ θ : ℝ in (0)..2 * Real.pi, g θ := hchange
    _ = _ := by
      dsimp [g]
      rw [intervalIntegral.integral_ofReal]
      push_cast
      rfl

/-- Scaling from a general nonnegative affine cosine profile to the
normalised smoothed cusp. -/
theorem affineCosine_rpow_eq_scaledCusp
    {p A B : ℝ} (_hp : 0 < p) (hB : 0 < B) (hAB : B ≤ A)
    (θ : ℝ) :
    (A - B * Real.cos θ) ^ p =
      B ^ p *
        (((A - B) / B) + 1 - Real.cos θ) ^ p := by
  have hδ : 0 ≤ (A - B) / B := div_nonneg (sub_nonneg.mpr hAB) hB.le
  have hbase :
      0 ≤ ((A - B) / B) + 1 - Real.cos θ := by
    nlinarith [Real.cos_le_one θ]
  have heq :
      A - B * Real.cos θ =
        B * (((A - B) / B) + 1 - Real.cos θ) := by
    field_simp [hB.ne']
  rw [heq, Real.mul_rpow hB.le hbase]

theorem affineCosine_sum_eq_scaledCusp
    {p A B φ : ℝ} (hp : 0 < p) (hB : 0 < B) (hAB : B ≤ A)
    (L : ℕ) :
    (∑ k ∈ Finset.range L,
        (A - B * Real.cos
          (φ + 2 * Real.pi * (k : ℝ) / (L : ℝ))) ^ p) =
      B ^ p *
        ∑ k ∈ Finset.range L,
          (((A - B) / B) + 1 - Real.cos
            (φ + 2 * Real.pi * (k : ℝ) / (L : ℝ))) ^ p := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact affineCosine_rpow_eq_scaledCusp hp hB hAB _

theorem affineCosine_integral_eq_scaledCusp
    {p A B : ℝ} (hp : 0 < p) (hB : 0 < B) (hAB : B ≤ A) :
    (∫ θ : ℝ in (0)..2 * Real.pi,
        (A - B * Real.cos θ) ^ p) =
      B ^ p *
        ∫ θ : ℝ in (0)..2 * Real.pi,
          (((A - B) / B) + 1 - Real.cos θ) ^ p := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  exact affineCosine_rpow_eq_scaledCusp hp hB hAB θ

/-- Equation (4.1): the constant is uniform in `A`, `B`, the number of
nodes, and the angular phase. -/
theorem exists_uniform_cusp_trapezoid_all
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {A B : ℝ},
      0 ≤ B → B ≤ A → ∀ (L : ℕ), 1 ≤ L → ∀ φ : ℝ,
      |(1 / (L : ℝ)) * ∑ k ∈ Finset.range L,
          (A - B * Real.cos
            (φ + 2 * Real.pi * (k : ℝ) / (L : ℝ))) ^ (α / 2)
        - (1 / (2 * Real.pi)) *
          ∫ θ : ℝ in (0)..2 * Real.pi,
            (A - B * Real.cos θ) ^ (α / 2)|
      ≤ C * B ^ (α / 2) * (L : ℝ) ^ (-1 - α) := by
  obtain ⟨K, hK, huniform⟩ :=
    exists_uniform_smoothedCusp_trapezoid hα0 hα2
  refine ⟨K, hK, ?_⟩
  intro A B hB hAB L hL φ
  by_cases hB0 : B = 0
  · subst B
    have hA : 0 ≤ A := by simpa using hAB
    have hL0 : (L : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.zero_lt_of_lt hL).ne'
    rw [Real.zero_rpow (by linarith : α / 2 ≠ 0)]
    simp only [zero_mul, sub_zero]
    have hsum :
        (∑ k ∈ Finset.range L, A ^ (α / 2)) =
          (L : ℝ) * A ^ (α / 2) := by
      rw [Finset.sum_const, Finset.card_range]
      norm_num [nsmul_eq_mul]
    rw [hsum]
    have hint :
        (∫ θ : ℝ in (0)..2 * Real.pi, A ^ (α / 2)) =
          (2 * Real.pi) * A ^ (α / 2) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    rw [hint]
    field_simp [hL0, Real.pi_ne_zero]
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    let δ : ℝ := (A - B) / B
    have hδ : 0 ≤ δ := by
      dsimp [δ]
      exact div_nonneg (sub_nonneg.mpr hAB) hBpos.le
    have hroot := huniform hδ L hL
      (φ / (2 * Real.pi) : AddCircle (1 : ℝ))
    rw [shiftedRootGridAverage_smoothed_eq
      (p := α / 2) (δ := δ) (φ := φ) (by linarith) hδ L hL,
      fourierCoeff_smoothedCuspCircle_zero_eq_interval
        (p := α / 2) (δ := δ) (by linarith) hδ] at hroot
    have hrootReal :
        |(1 / (L : ℝ)) *
            ∑ k ∈ Finset.range L,
              (δ + 1 - Real.cos
                (φ + 2 * Real.pi * (k : ℝ) / (L : ℝ))) ^ (α / 2) -
          (1 / (2 * Real.pi)) *
            ∫ θ : ℝ in (0)..2 * Real.pi,
              (δ + 1 - Real.cos θ) ^ (α / 2)| ≤
          K * (L : ℝ) ^ (-1 - α) := by
      simpa only [← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using hroot
    rw [affineCosine_sum_eq_scaledCusp
      (p := α / 2) (A := A) (B := B) (φ := φ)
      (by linarith) hBpos hAB L,
      affineCosine_integral_eq_scaledCusp
        (p := α / 2) (A := A) (B := B)
        (by linarith) hBpos hAB]
    dsimp [δ] at hrootReal ⊢
    have hBpow : 0 ≤ B ^ (α / 2) := Real.rpow_nonneg hBpos.le _
    rw [show
        1 / (L : ℝ) *
              (B ^ (α / 2) *
                ∑ k ∈ Finset.range L,
                  ((A - B) / B + 1 -
                    Real.cos
                      (φ + 2 * Real.pi * (k : ℝ) / (L : ℝ))) ^
                      (α / 2)) -
            1 / (2 * Real.pi) *
              (B ^ (α / 2) *
                ∫ θ : ℝ in (0)..2 * Real.pi,
                  ((A - B) / B + 1 - Real.cos θ) ^ (α / 2)) =
          B ^ (α / 2) *
            ((1 / (L : ℝ)) *
                ∑ k ∈ Finset.range L,
                  ((A - B) / B + 1 -
                    Real.cos
                      (φ + 2 * Real.pi * (k : ℝ) / (L : ℝ))) ^
                      (α / 2) -
              (1 / (2 * Real.pi)) *
                ∫ θ : ℝ in (0)..2 * Real.pi,
                  ((A - B) / B + 1 - Real.cos θ) ^ (α / 2)) by ring,
      abs_mul, abs_of_nonneg hBpow]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hrootReal hBpow)

/-- Equation (4.1), in the blueprint's coefficient-specialised interface. -/
theorem uniform_cusp_trapezoid
    {α A B : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hB : 0 ≤ B) (hAB : B ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ), 1 ≤ L → ∀ φ : ℝ,
      |(1 / (L : ℝ)) * ∑ k ∈ Finset.range L,
          (A - B * Real.cos
            (φ + 2 * Real.pi * (k : ℝ) / (L : ℝ))) ^ (α / 2)
        - (1 / (2 * Real.pi)) *
          ∫ θ : ℝ in (0)..2 * Real.pi,
            (A - B * Real.cos θ) ^ (α / 2)|
      ≤ C * B ^ (α / 2) * (L : ℝ) ^ (-1 - α) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_cusp_trapezoid_all hα0 hα2
  exact ⟨C, hC, hbound hB hAB⟩

end CuspTrapezoid

end BEMOC
