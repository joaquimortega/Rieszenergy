# Comparable intermediate closure

The polar derivative bound and local height chain give a uniform order-four chord singularity. The C4 angular integral, inverse-power model bound, mixed Taylor estimate, and scalar conversion then prove the unconditional comparable block estimate for every nonendpoint gap between two labels and twice the first population.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.ComparableIntermediateIntegralBound
import BEMOCFormalization.ComparableIntermediateScaling
import BEMOCFormalization.ComparableHeightChainBounds

open Set MeasureTheory
namespace BEMOC.Definitive

/-- A uniform pointwise angular fourth-derivative estimate on intermediate
rectangles. The polar chain provides this input in the final assembly. -/
def IntermediatePointwiseBound (α C : ℝ) : Prop :=
  ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
    j.val ≠ 0 → j.val + 1 ≠ 2 * bandParameter N - 1 →
    k.val ≠ 0 → k.val + 1 ≠ 2 * bandParameter N - 1 →
    Comparable N (j.val + 1) (k.val + 1) →
    2 ≤ |(j.val : ℤ) - k.val| →
    |(j.val : ℝ) - k.val| ≤ 2 * population N (j.val + 1) →
    ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      |mixedFourth (fun q : ℝ × ℝ =>
        latitudeProfile α q.1 q.2 θ) p.1 p.2| ≤
        C * (((population N (j.val + 1) : ℝ) /
          bandParameter N) / 240) ^ (-4 : ℝ) *
          (2 - 2 * p.1 * p.2 -
            2 * Real.sqrt (1 - p.1 ^ 2) *
              Real.sqrt (1 - p.2 ^ 2) * Real.cos θ) ^ ((α - 4) / 2)

/-- The proved polar derivative table supplies a single pointwise constant
for every nonendpoint intermediate rectangle. -/
theorem intermediate_pointwise_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ IntermediatePointwiseBound α C := by
  obtain ⟨C₀, hC₀, hderiv⟩ := polar_derivative_bound hα0 hα2
  let T : ℝ := 16384
  let C : ℝ := C₀ * (1 + 2 * T + T ^ 2)
  have hC : 0 < C := by dsimp [C, T]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN j k hjfirst hjlast hkfirst hklast hcomp hjk hnear p hp θ hθ
  let M : ℝ := bandParameter N
  let R : ℝ := (population N (j.val + 1) : ℝ) / M
  let ρ : ℝ := R / 240
  let U : ℝ := 2 - 2 * p.1 * p.2 -
    2 * Real.sqrt (1 - p.1 ^ 2) *
      Real.sqrt (1 - p.2 ^ 2) * Real.cos θ
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (16 : ℕ))
      (bandParameter_ge_sixteen_of_ge_1024 hN))
  have hr : (0 : ℝ) < population N (j.val + 1) := by
    exact_mod_cast population_pos (by omega : 4 ≤ N) (by omega)
      (by have := j.isLt; omega)
  have hR : 0 < R := div_pos hr hM
  have hρ : 0 < ρ := div_pos hR (by norm_num)
  have hprof := intermediate_comparable_profile hN j k hjfirst hjlast
    hkfirst hklast hcomp hjk hp.1 hp.2
  have ha : ρ ≤ Real.sqrt (1 - p.1 ^ 2) := by
    have hρR : ρ ≤ R / 30 := by dsimp [ρ]; nlinarith [hR.le]
    exact hρR.trans hprof.1
  have hb : ρ ≤ Real.sqrt (1 - p.2 ^ 2) := by
    have h := hprof.2.2.1
    dsimp [ρ]
    nlinarith
  have hs : p.1 ∈ Ioo (-1 : ℝ) 1 :=
    nonpolar_band_height_interior hN j (by omega) hjlast hp.1
  have ht : p.2 ∈ Ioo (-1 : ℝ) 1 :=
    nonpolar_band_height_interior hN k (by omega) hklast hp.2
  have hgeo := intermediate_comparable_chord_bounds hN j k
    hjfirst hjlast hkfirst hklast hcomp hjk hnear hp.1 hp.2 hθ
  have hU : 0 < U := by
    have hℓ : 0 < |(j.val : ℝ) - k.val| := by
      have hℓ2 : 2 ≤ |(j.val : ℝ) - k.val| := by exact_mod_cast hjk
      linarith
    have hd : 0 < |(j.val : ℝ) - k.val| / M := div_pos hℓ hM
    have hδ : 0 < (|(j.val : ℝ) - k.val| / M) ^ 2 / 3600 :=
      div_pos (sq_pos_of_pos hd) (by norm_num)
    have hθterm : 0 ≤ R ^ 2 * θ ^ 2 / 30000 := by positivity
    dsimp [U]
    linarith [hgeo.1]
  have hUmax : U ≤ (T * ρ) ^ 2 := by
    have hupper := hgeo.2
    have hsq : 0 ≤ R ^ 2 := sq_nonneg R
    dsimp [U, T, ρ]
    nlinarith
  have hsclosed : p.1 ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have htclosed : p.2 ∈ Icc (-1 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hpolar : polarChordSquare (Real.arccos p.1) (Real.arccos p.2) θ = U :=
    polarChordSquare_arccos hsclosed htclosed
  have hU' : 0 < 2 - 2 * (Real.cos (Real.arccos p.1) *
      Real.cos (Real.arccos p.2) +
      Real.sin (Real.arccos p.1) * Real.sin (Real.arccos p.2) * Real.cos θ) := by
    change 0 < polarChordSquare (Real.arccos p.1) (Real.arccos p.2) θ
    rwa [hpolar]
  have hUmax' : 2 - 2 * (Real.cos (Real.arccos p.1) *
      Real.cos (Real.arccos p.2) +
      Real.sin (Real.arccos p.1) * Real.sin (Real.arccos p.2) * Real.cos θ) ≤
      (T * ρ) ^ 2 := by
    change polarChordSquare (Real.arccos p.1) (Real.arccos p.2) θ ≤ _
    rwa [hpolar]
  have hraw := abs_latitudeProfile_mixedFourth_le_of_positive
    (α := α) (θ := θ) (s := p.1) (t := p.2) (ρ := ρ) (L := T)
    hs ht hρ (by dsimp [T]; norm_num : 1 ≤ T) ha hb
    C₀ hC₀ hderiv hU' hUmax'
  have hpow : ρ ^ (-4 : ℝ) = (ρ ^ 4)⁻¹ := by
    rw [Real.rpow_neg hρ.le]
    norm_cast
  change |mixedFourth (fun q : ℝ × ℝ =>
    latitudeProfile α q.1 q.2 θ) p.1 p.2| ≤
      C * ρ ^ (-4 : ℝ) * U ^ ((α - 4) / 2)
  rw [hpow]
  change |mixedFourth (fun q : ℝ × ℝ =>
      latitudeProfile α q.1 q.2 θ) p.1 p.2| ≤
      C₀ * (1 + 2 * T + T ^ 2) *
        (polarChordSquare (Real.arccos p.1) (Real.arccos p.2) θ) ^
          ((α - 4) / 2) / ρ ^ 4 at hraw
  rw [hpolar] at hraw
  convert hraw using 1 <;> dsimp [C, T] <;> ring

/-- The pointwise polar-chain estimate, once available, closes every
nonendpoint intermediate comparable block at the exact manuscript scale. -/
theorem intermediate_comparable_block_bound_of_pointwise
    {α C : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hC : 0 < C) (hpoint : IntermediatePointwiseBound α C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
      j.val ≠ 0 → j.val + 1 ≠ 2 * bandParameter N - 1 →
      k.val ≠ 0 → k.val + 1 ≠ 2 * bandParameter N - 1 →
      Comparable N (j.val + 1) (k.val + 1) →
      2 ≤ |(j.val : ℤ) - k.val| →
      |(j.val : ℝ) - k.val| ≤
        2 * population N (j.val + 1) →
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        C' * population N (j.val + 1) / (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
  let C' : ℝ := C * (4096 * 180 * 240 ^ 4 * 60 ^ (3 - α)) *
    (1 + 1 / (3 - α))
  have hβ : 0 < 3 - α := by linarith
  have hC' : 0 < C' := by dsimp [C']; positivity
  refine ⟨C', hC', ?_⟩
  intro N hN j k hjfirst hjlast hkfirst hklast hcomp hjk hnear
  let M : ℝ := bandParameter N
  let r : ℝ := population N (j.val + 1)
  let r' : ℝ := population N (k.val + 1)
  let ℓ : ℝ := |(j.val : ℝ) - k.val|
  let R : ℝ := r / M
  let d : ℝ := ℓ / M
  let K : ℝ := C * (R / 240) ^ (-4 : ℝ)
  let L : ℝ := K * ((1 + 1 / (3 - α)) *
    (d / 60) ^ (α - 3) / (R / 180))
  have hM : 16 ≤ M := by
    dsimp [M]
    exact_mod_cast bandParameter_ge_sixteen_of_ge_1024 hN
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast population_pos (by omega : 4 ≤ N) (by omega)
      (by have := j.isLt; omega)
  have hr' : 0 ≤ r' := by positivity
  have hr'le : r' ≤ 8 * r := hcomp.2
  have hℓ : 2 ≤ ℓ := by dsimp [ℓ]; exact_mod_cast hjk
  have hR : 0 < R := div_pos hr (by linarith)
  have hd : 0 < d := div_pos (by linarith) (by linarith)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let W := integralParameterDomain nearTailSmoothDomain 0 Real.pi
  let G : ℝ × ℝ → ℝ := fun q => (1 / Real.pi) *
    ∫ θ in (0 : ℝ)..Real.pi, latitudeProfile α q.1 q.2 θ
  have hsm := intermediate_profile_smooth_extension hα0 hN j k
    hjfirst hjlast hkfirst hklast hcomp hjk hnear
  have hfourth : ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
      |mixedFourth G p.1 p.2| ≤ L := by
    intro p hp
    have hraw := intermediate_mixedFourth_integral_bound_of_pointwise
      hα0 hα2 hN j k hjfirst hjlast hkfirst hklast hcomp hjk hnear
      hp hK (hpoint N hN j k hjfirst hjlast hkfirst hklast hcomp
        hjk hnear p hp)
    have hEq := intermediate_mixedFourth_eq_integral hα0 hN j k
      hjfirst hjlast hkfirst hklast hcomp hjk hnear hp
    rw [hEq]
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    have hπ1 : (1 : ℝ) / Real.pi ≤ 1 := by
      apply (div_le_iff₀ hπ).2
      nlinarith [Real.pi_gt_three]
    have hnon : 0 ≤ |∫ θ in (0 : ℝ)..Real.pi,
      mixedFourth (fun q : ℝ × ℝ =>
        latitudeProfile α q.1 q.2 θ) p.1 p.2| := abs_nonneg _
    calc
      |(1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi,
          mixedFourth (fun q : ℝ × ℝ =>
            latitudeProfile α q.1 q.2 θ) p.1 p.2| =
          (1 / Real.pi) * |∫ θ in (0 : ℝ)..Real.pi,
            mixedFourth (fun q : ℝ × ℝ =>
              latitudeProfile α q.1 q.2 θ) p.1 p.2| := by
        rw [abs_mul, abs_of_pos (div_pos zero_lt_one hπ)]
      _ ≤ |∫ θ in (0 : ℝ)..Real.pi,
            mixedFourth (fun q : ℝ × ℝ =>
              latitudeProfile α q.1 q.2 θ) p.1 p.2| := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hπ1 hnon
      _ ≤ L := by simpa [L, K, R, d, r, ℓ, M] using hraw
  have hTaylor := kernelBlock_le_of_smooth_extension
    (by omega : 4 ≤ N) j k α G W hsm.1 hsm.2.1 hsm.2.2.1
    hsm.2.2.2 L hL hfourth
  have hscale := comparable_intermediate_full_scaling hα0 hα2 hM
    hr hr' hr'le hℓ
  calc
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        r ^ 3 * r' ^ 3 / M ^ 8 * L := hTaylor
    _ = C * (1 + 1 / (3 - α)) *
        (r ^ 3 * r' ^ 3 / M ^ 8 * (R / 240) ^ (-4 : ℝ) *
          ((d / 60) ^ (α - 3) / (R / 180))) := by dsimp [L, K]; ring
    _ ≤ C * (1 + 1 / (3 - α)) *
        ((4096 * 180 * 240 ^ 4 * 60 ^ (3 - α)) *
          (r / M ^ α) * (1 + ℓ) ^ (α - 3)) := by
      gcongr
    _ = C' * (r / M ^ α) * (1 + ℓ) ^ (α - 3) := by dsimp [C']; ring
    _ = _ := by dsimp [r, M, ℓ]; ring

/-- All nonendpoint comparable blocks with two or more labels of separation
and gap at most twice the first population satisfy the sharp bound. -/
theorem intermediate_comparable_block_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
      j.val ≠ 0 → j.val + 1 ≠ 2 * bandParameter N - 1 →
      k.val ≠ 0 → k.val + 1 ≠ 2 * bandParameter N - 1 →
      Comparable N (j.val + 1) (k.val + 1) →
      2 ≤ |(j.val : ℤ) - k.val| →
      |(j.val : ℝ) - k.val| ≤
        2 * population N (j.val + 1) →
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        C * population N (j.val + 1) / (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
  obtain ⟨C, hC, hpoint⟩ := intermediate_pointwise_bound hα0 hα2
  exact intermediate_comparable_block_bound_of_pointwise hα0 hα2 hC hpoint

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
