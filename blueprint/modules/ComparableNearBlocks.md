# Comparable near blocks

`BEMOCFormalization.ComparableNearBlocks` isolates comparable nonpolar latitude
bands whose zero-based indices differ by at most two. The intended manuscript
estimate is the `r_j M^{-α}` scale, multiplied by the harmless factor
`(1+|j-k|)^{α-3}`. Here `M = bandParameter N`, `r_j = population N (j+1)`,
`0 < α < 2`, and the global construction hypothesis is `1024 ≤ N`.

The completed reduction splits the half-turn angular average at `1/r_j`.
`latitudeKernel_eq_half_profile_integral` uses reflection around π and the
periodic latitude profile. `latitudeKernel_eq_near_split` and
`kernelBlock_eq_near_low_add_tail` give the exact sum of the small-arc and
tail contributions. The proof uses continuity and interval integrability
of the two kernels, so it does not presume unrestricted additivity of a
Bochner integral on arbitrary functions.

The low arc is complete. `near_band_small_arc_chord_upper` combines the
angular chord comparison with the near-band polar-angle gap and both radius
bounds, proving `0 ≤ D² ≤ 2100/M²` whenever `0 ≤ θ ≤ 1/r_j`. The pointwise
profile is therefore at most `2100^(α/2)/M^α`; integration over an interval
of length `1/r_j` gives `nearLowAngleBound`. The signed band block then has
variation at most `4 r_j r_k`, and comparability gives `r_k ≤ 8r_j`.

The same geometric APIs yield `near_band_chord_lower`, a lower bound
`D² ≥ (r_j/M)² θ² / 28800` for positive angles on the full half-turn.
Consequently the tail is smooth on an open neighborhood of the closed band
rectangle: its angular interval begins at `1/r_j > 0`, and continuity plus
compactness preserve strict positivity of `D²` locally. The standalone
`polarKernel_contDiffAt_of_chord_pos` proves the required polar C4 regularity
at each positive chord without assuming an integer exponent. This local
regularity is essential because `α < 2` and the distance power is not C4
at coincident points.

The open-domain construction is now formalized as
`nearTailPhysicalRegularSet r`. Its chord-positivity component is open by
`IsCompact.eventually_forall_of_forall_eventually` applied to the compact
interval `[r⁻¹,π]`, and its coordinate component is the open physical
strip `(-1,1)²`. `nonpolar_band_height_interior` uses the radius lower
bound to exclude the polar endpoints. The theorem
`near_band_rectangle_subset_tail_regular` puts the entire closed near
rectangle inside this domain, while `near_band_tail_chord_pos` supplies
the strict pointwise positivity from the lower chord estimate.

`iteratedDeriv_two_comp_arccos` proves the exact two-derivative height chain
rule. `iteratedDeriv_two_const_linear_comp_arccos` packages a linear
combination of two such chains, and `mixedFourth_arccos_chain` applies it
twice. Its factored four-term identity has denominator powers `a²b²`,
`a³b²`, `a²b³`, and `a³b³`, with `a=sqrt(1-s²)` and `b=sqrt(1-t²)`.
The theorem allows the vertical slice to be C2 merely on a polar-angle
neighborhood rather than globally, which is what the positive-chord tail
actually supplies. To instantiate it from pair-valued C4, use Taylor's
`partialSecond`, `partialSecondTwice`,
`iteratedDeriv_two_slice_second_eq_partialSecondTwice`, and
`deriv_slice_second_eq_partialSecond`; the derivative profiles are locally
equal to the C2 partial fields. The compiled
`contDiffAt_vertical_second_profile` and
`contDiffAt_vertical_first_profile` package these two regularity facts.
The open set can be the preimage of the positive-chord domain under
`u ↦ (u, arccos t)`.

The analytic contract `NearTailDerivativeBound α` is now discharged by
`ComparableNearTailClosure.near_tail_derivative_bound`, using the positive-chord
open set above. Its fourth derivative estimate follows from
`ComparableHeightChainBounds.near_tail_profile_chord_bound` and
`NearTailIntegralCalculus.mixedFourth_nearTailKernel_eq_integral`. The quantitative
radius common to both bands is `ρ = r_j/(240M)`, not `r_j/(30M)`; the latter
only lower-bounds the source band and would fail for a target band with
population as small as `r_j/8`. The combined polar chain estimate uses the
orders `(2,2)`, `(2,1)`, `(1,2)`, `(1,1)` and the common power
`D^{α-4}`. The chord lower bound yields the pointwise majorant
`C_α (r_j/M)^{α-8} θ^{α-4}`. The scalar angular integral is at most
`r_j^{3-α}/(3-α)`, so the exact identity in
`ComparableNearTailScaling` gives `M⁸/(r_j⁵ M^α)`. This domination applies
at `α=1` without a logarithmic case split.

`near_comparable_scale_of_analytic_bounds` consumes the low-angle and
tail contracts and proves `|kernelBlock| ≤ C r_j/M^α`. Its tail application
is the already proved `mixedTaylorBound`, which gives the width factor
`r_j³ r_k³/M⁸`. `near_comparable_block_bound_of_tail` adds the displayed
manuscript decay factor: for index gap at most two and `0<α<2`, the factor
is bounded below by `1/27`. This intermediate theorem keeps
`NearTailDerivativeBound` explicit; `ComparableNearTailClosure.near_tail_derivative_bound`
proves that contract and closes the near comparable regime downstream.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.ComparableBlockEstimates
import BEMOCFormalization.AngularDistance

open MeasureTheory Set
open scoped Interval
namespace BEMOC.Definitive

/-- The angular profile is symmetric around π. -/
theorem latitudeProfile_two_pi_sub (α s t θ : ℝ) :
    latitudeProfile α s t (2 * Real.pi - θ) = latitudeProfile α s t θ := by
  simp only [latitudeProfile, Real.cos_two_pi_sub]

/-- The complete-turn latitude average equals the half-turn average. -/
theorem latitudeKernel_eq_half_profile_integral {α : ℝ} (hα : 0 < α)
    (s t : ℝ) :
    latitudeKernel α s t =
      (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, latitudeProfile α s t θ := by
  let f : ℝ → ℝ := latitudeProfile α s t
  have hf : Continuous f :=
    (continuous_latitudeProfile hα).comp
      ((continuous_const.prodMk continuous_const).prodMk continuous_id)
  have hfirst : IntervalIntegrable f volume 0 Real.pi :=
    hf.intervalIntegrable _ _
  have hsecond : IntervalIntegrable f volume Real.pi (2 * Real.pi) :=
    hf.intervalIntegrable _ _
  have hreflect : (∫ θ in Real.pi..2 * Real.pi, f θ) =
      ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    calc
      _ = ∫ θ in Real.pi..2 * Real.pi, f (2 * Real.pi - θ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        exact (latitudeProfile_two_pi_sub α s t θ).symm
      _ = ∫ θ in (0 : ℝ)..Real.pi, f θ := by
        rw [intervalIntegral.integral_comp_sub_left]
        congr 1 <;> ring
  have hfull : (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) =
      2 * (∫ θ in (0 : ℝ)..Real.pi, f θ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hfirst hsecond,
      hreflect]
    ring
  rw [latitudeKernel_eq_profile_integral, hfull]
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- Average over the small angular arc where the height kernel may have a cusp. -/
noncomputable def nearLowKernel (α r : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 / Real.pi) * ∫ θ in (0 : ℝ)..r⁻¹,
    latitudeProfile α p.1 p.2 θ

/-- Average over the smooth angular tail, away from zero angle. -/
noncomputable def nearTailKernel (α r : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 / Real.pi) * ∫ θ in r⁻¹..Real.pi,
    latitudeProfile α p.1 p.2 θ

/-- Exact split at inverse population; the positive population is supplied by callers. -/
theorem latitudeKernel_eq_near_split {α : ℝ} (hα : 0 < α)
    (s t r : ℝ) :
    latitudeKernel α s t =
      nearLowKernel α r (s, t) + nearTailKernel α r (s, t) := by
  rw [latitudeKernel_eq_half_profile_integral hα]
  have hf : Continuous (latitudeProfile α s t) :=
    (continuous_latitudeProfile hα).comp
      ((continuous_const.prodMk continuous_const).prodMk continuous_id)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (0 : ℝ) r⁻¹)
    (hf.intervalIntegrable r⁻¹ Real.pi)]
  simp only [nearLowKernel, nearTailKernel]
  ring

/-- The fixed-angle truncated averages remain continuous for positive exponents. -/
theorem continuous_nearLowKernel {α : ℝ} (hα : 0 < α) (r : ℝ) :
    Continuous (nearLowKernel α r) := by
  unfold nearLowKernel
  apply continuous_const.mul
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (continuous_latitudeProfile hα) _ _

theorem continuous_nearTailKernel {α : ℝ} (hα : 0 < α) (r : ℝ) :
    Continuous (nearTailKernel α r) := by
  unfold nearTailKernel
  apply continuous_const.mul
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (continuous_latitudeProfile hα) _ _

/-- A continuous kernel has a continuous signed-band average in the free height. -/
theorem continuous_bandError_slice (N k : ℕ)
    {G : ℝ × ℝ → ℝ} (hG : Continuous G) :
    Continuous (fun s => bandError N k (fun t => G (s, t))) := by
  unfold bandError
  apply Continuous.sub
  · apply continuous_const.mul
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun s t => G (s, t)) hG _ _
  · apply continuous_const.mul
    exact hG.comp (continuous_id.prodMk continuous_const)

/-- Tensor band integration distributes over continuous kernels. -/
theorem bandBlock_add_of_continuous (N j k : ℕ)
    {F G : ℝ × ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) :
    bandBlock N j k (fun p => F p + G p) =
      bandBlock N j k F + bandBlock N j k G := by
  have hinner (s : ℝ) :
      bandError N k (fun t => F (s, t) + G (s, t)) =
        bandError N k (fun t => F (s, t)) +
          bandError N k (fun t => G (s, t)) := by
    apply bandError_add_of_integrable
    · exact (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    · exact (hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have houterF : IntervalIntegrable
      (fun s => bandError N k (fun t => F (s, t))) volume
      (boundary N j) (boundary N (j - 1)) :=
    (continuous_bandError_slice N k hF).intervalIntegrable _ _
  have houterG : IntervalIntegrable
      (fun s => bandError N k (fun t => G (s, t))) volume
      (boundary N j) (boundary N (j - 1)) :=
    (continuous_bandError_slice N k hG).intervalIntegrable _ _
  unfold bandBlock
  simp_rw [hinner]
  exact bandError_add_of_integrable N j _ _ houterF houterG

/-- The kernel band tensor is exactly the sum of its low-angle and smooth-tail tensors. -/
theorem kernelBlock_eq_near_low_add_tail {α : ℝ} (hα : 0 < α)
    (N j k : ℕ) (r : ℝ) :
    kernelBlock α N j k =
      bandBlock N j k (nearLowKernel α r) +
        bandBlock N j k (nearTailKernel α r) := by
  unfold kernelBlock
  rw [show (fun p : ℝ × ℝ => latitudeKernel α p.1 p.2) =
      fun p => nearLowKernel α r p + nearTailKernel α r p by
        funext p
        exact latitudeKernel_eq_near_split hα p.1 p.2 r]
  exact bandBlock_add_of_continuous N j k
    (continuous_nearLowKernel hα r) (continuous_nearTailKernel hα r)

/-- An angular pointwise bound gives the small-arc average bound without smoothness. -/
theorem abs_nearLowKernel_le_of_profile_bound
    {α r s t P : ℝ} (hr : 0 < r) (hP : 0 ≤ P)
    (hprofile : ∀ θ ∈ Icc (0 : ℝ) r⁻¹,
      |latitudeProfile α s t θ| ≤ P) :
    |nearLowKernel α r (s, t)| ≤ P / (Real.pi * r) := by
  have hcut : (0 : ℝ) ≤ r⁻¹ := le_of_lt (inv_pos.mpr hr)
  have hint : |∫ θ in (0 : ℝ)..r⁻¹, latitudeProfile α s t θ| ≤
      P * r⁻¹ := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := r⁻¹) (C := P)
      (f := latitudeProfile α s t) (by
        intro θ hθ
        rw [Real.norm_eq_abs]
        exact hprofile θ (by
          rw [uIoc_of_le hcut] at hθ
          exact ⟨hθ.1.le, hθ.2⟩))
    simpa [Real.norm_eq_abs, abs_of_nonneg hcut] using h
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [nearLowKernel, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.pi)]
  have hmul := mul_le_mul_of_nonneg_left hint (by positivity : 0 ≤ 1 / Real.pi)
  convert hmul using 1 <;> field_simp

theorem div_sq_rpow_half {C M α : ℝ}
    (hC : 0 ≤ C) (hM : 0 < M) :
    (C / M ^ 2) ^ (α / 2) = C ^ (α / 2) / M ^ α := by
  rw [Real.div_rpow hC (sq_nonneg _) (α / 2)]
  have hpow := Real.rpow_mul hM.le (2 : ℝ) (α / 2)
  rw [show (2 : ℝ) * (α / 2) = α by ring] at hpow
  rw [hpow]

  exact congrArg (fun x : ℝ => C ^ (α / 2) / x ^ (α / 2))
    (Real.rpow_natCast M 2).symm
/-- A near nonpolar rectangle has squared distance O(M⁻²) below angle 1/r_j. -/
theorem near_band_small_arc_chord_upper
    {N : ℕ} (hN : 1024 ≤ N) (j k : RingIndex N)
    (hjfirst : j.val + 1 ≠ 1)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val + 1 ≠ 1)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    (hnear : |(j.val : ℝ) - k.val| ≤ 2)
    {s t θ : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1))
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ (population N (j.val + 1) : ℝ)⁻¹) :
    0 ≤ 2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ ∧
    2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ ≤
      2100 / (bandParameter N : ℝ) ^ 2 := by
  let rj : ℝ := population N (j.val + 1)
  let rk : ℝ := population N (k.val + 1)
  let M : ℝ := bandParameter N
  have hN4 : 4 ≤ N := by omega
  have hM16 := bandParameter_ge_sixteen_of_ge_1024 hN
  have hMr : 0 < M := by dsimp [M]; exact_mod_cast (by omega : 0 < bandParameter N)
  have hjindex : j.val + 1 < 2 * bandParameter N := by
    have hv := j.isLt
    omega
  have hkindex : k.val + 1 < 2 * bandParameter N := by
    have hv := k.isLt
    omega
  have hrj : 0 < rj := by
    dsimp [rj]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hrj1 : 1 ≤ rj := by
    dsimp [rj]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hrk : 0 < rk := by
    dsimp [rk]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ k.val + 1) hkindex
  have hrk8 : rk ≤ 8 * rj := hcomp.2
  have hsunit : s ∈ Icc (-1 : ℝ) 1 := ⟨
    (boundary_ge_neg_one hN4 hjindex).trans hs.1,
    hs.2.trans (boundary_le_one hN4 (by omega))⟩
  have htunit : t ∈ Icc (-1 : ℝ) 1 := ⟨
    (boundary_ge_neg_one hN4 hkindex).trans ht.1,
    ht.2.trans (boundary_le_one hN4 (by omega))⟩
  have hnearZ : |(j.val : ℤ) - k.val| ≤ 2 := by
    exact_mod_cast hnear
  have hgap := near_band_arccos_gap hN4 hM16 j k hnearZ hs ht
  have hradS := (band_radius_comparison hN4 hM16 j
    (by omega) hjlast hs).2
  have hradT := (band_radius_comparison hN4 hM16 k
    (by omega) hklast ht).2
  have hθπ : |θ| ≤ Real.pi := by
    rw [abs_of_nonneg hθ0]
    have hinv : rj⁻¹ ≤ 1 := (inv_le_one₀ hrj).2 hrj1
    linarith [Real.one_le_pi_div_two, hθ1]
  have hchord := heightChordSquare_comparison hsunit htunit hθπ
  have hangleSq : (Real.arccos s - Real.arccos t) ^ 2 ≤
      (45 / M) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hgap 2
    simpa only [sq_abs] using h
  have hsinS0 : 0 ≤ Real.sqrt (1 - s ^ 2) := Real.sqrt_nonneg _
  have hsinT0 : 0 ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
  have hsinprod : Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
      (rj / M) * (rk / M) := by
    exact mul_le_mul hradS hradT hsinT0 (by positivity)
  have hθSq : θ ^ 2 ≤ rj⁻¹ ^ 2 := by gcongr
  have hlong : Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * θ ^ 2 ≤
      8 / M ^ 2 := by
    calc
      _ ≤ (rj / M) * (rk / M) * θ ^ 2 := by gcongr
      _ ≤ (rj / M) * (rk / M) * rj⁻¹ ^ 2 := by gcongr
      _ ≤ (rj / M) * (8 * rj / M) * rj⁻¹ ^ 2 := by gcongr
      _ = 8 / M ^ 2 := by field_simp; ring
  have hlat : (45 / M) ^ 2 = 2025 / M ^ 2 := by ring
  have hmodel0 : 0 ≤ (Real.arccos s - Real.arccos t) ^ 2 +
      Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * θ ^ 2 := by positivity
  constructor
  · linarith [hchord.1]
  · change 2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
        Real.sqrt (1 - t ^ 2) * Real.cos θ ≤ 2100 / M ^ 2
    calc
      _ ≤ (Real.arccos s - Real.arccos t) ^ 2 +
          Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * θ ^ 2 :=
        hchord.2
      _ ≤ (45 / M) ^ 2 + 8 / M ^ 2 :=
        add_le_add (by simpa [hlat] using hangleSq) hlong
      _ = 2033 / M ^ 2 := by ring
      _ ≤ 2100 / M ^ 2 := by gcongr; norm_num

/-- Uniform small-arc bound needed only on the literal near-comparable rectangles. -/
def NearLowAngleBound (α : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
    j.val + 1 ≠ 1 → j.val + 1 ≠ 2 * bandParameter N - 1 →
    k.val + 1 ≠ 1 → k.val + 1 ≠ 2 * bandParameter N - 1 →
    Comparable N (j.val + 1) (k.val + 1) →
    |(j.val : ℝ) - k.val| ≤ 2 →
    ∀ s ∈ band N (j.val + 1), ∀ t ∈ band N (k.val + 1),
      |nearLowKernel α (population N (j.val + 1)) (s, t)| ≤
        A / ((population N (j.val + 1) : ℝ) *
          (bandParameter N : ℝ) ^ α)

/-- The low-angle contribution has the required TV-compatible pointwise size. -/
theorem nearLowAngleBound {α : ℝ} (hα : 0 < α) : NearLowAngleBound α := by
  let A : ℝ := (2100 : ℝ) ^ (α / 2) / Real.pi
  have hA : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro N hN j k hjfirst hjlast hkfirst hklast hcomp hnear s hs t ht
  let rj : ℝ := population N (j.val + 1)
  let M : ℝ := bandParameter N
  have hN4 : 4 ≤ N := by omega
  have hjindex : j.val + 1 < 2 * bandParameter N := by
    have hv := j.isLt
    omega
  have hrj : 0 < rj := by
    dsimp [rj]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hMr : 0 < M := by
    dsimp [M]
    exact_mod_cast bandParameter_pos hN4
  have hMα : 0 < M ^ α := Real.rpow_pos_of_pos hMr _
  have hP : 0 ≤ (2100 : ℝ) ^ (α / 2) / M ^ α := by positivity
  have hprofile : ∀ θ ∈ Icc (0 : ℝ) rj⁻¹,
      |latitudeProfile α s t θ| ≤ (2100 : ℝ) ^ (α / 2) / M ^ α := by
    intro θ hθ
    have hchord := near_band_small_arc_chord_upper hN j k
      hjfirst hjlast hkfirst hklast hcomp hnear hs ht hθ.1 hθ.2
    have hαhalf : 0 ≤ α / 2 := by linarith
    unfold latitudeProfile
    rw [abs_of_nonneg (Real.rpow_nonneg hchord.1 _)]
    calc
      _ ≤ (2100 / M ^ 2) ^ (α / 2) :=
        Real.rpow_le_rpow hchord.1 hchord.2 hαhalf
      _ = (2100 : ℝ) ^ (α / 2) / M ^ α :=
        div_sq_rpow_half (by norm_num) hMr
  have hlow := abs_nearLowKernel_le_of_profile_bound hrj hP hprofile
  change |nearLowKernel α rj (s, t)| ≤ A / (rj * M ^ α)
  calc
    _ ≤ ((2100 : ℝ) ^ (α / 2) / M ^ α) / (Real.pi * rj) := hlow
    _ = A / (rj * M ^ α) := by
      dsimp [A]
      field_simp
      ring

/-- The second height derivative of the polar coordinate map in the open unit interval. -/
theorem iteratedDeriv_two_arccos {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    iteratedDeriv 2 Real.arccos s =
      -s / (Real.sqrt (1 - s ^ 2)) ^ 3 := by
  have hbase : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hsqrt : 0 < Real.sqrt (1 - s ^ 2) := Real.sqrt_pos.2 hbase
  have hbaseDeriv : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * s) s := by
    convert (hasDerivAt_const s (1 : ℝ)).sub
      ((hasDerivAt_id s).pow 2) using 1 <;> simp [id] <;> ring
  have hroot : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
      ((1 / (2 * Real.sqrt (1 - s ^ 2))) * (-2 * s)) s :=
    by simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt (x := 1 - s ^ 2) hbase.ne').comp s hbaseDeriv
  have hfirst : HasDerivAt
      (fun x : ℝ => -(1 / Real.sqrt (1 - x ^ 2)))
      (-s / (Real.sqrt (1 - s ^ 2)) ^ 3) s := by
    have hinv := hroot.inv hsqrt.ne'
    convert hinv.neg using 1 <;> dsimp
    field_simp
    ring
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_arccos]
  exact hfirst.deriv

/-- A two-derivative height-to-polar chain rule at a nonpolar height. -/
theorem iteratedDeriv_two_comp_arccos
    {g : ℝ → ℝ} {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1)
    (hg : ContDiffAt ℝ 2 g (Real.arccos s)) :
    iteratedDeriv 2 (fun x => g (Real.arccos x)) s =
      iteratedDeriv 2 g (Real.arccos s) /
        (Real.sqrt (1 - s ^ 2)) ^ 2 -
      s * deriv g (Real.arccos s) /
        (Real.sqrt (1 - s ^ 2)) ^ 3 := by
  have hroot : 0 < Real.sqrt (1 - s ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [hs.1, hs.2]
  have harc : ContDiffAt ℝ 2 Real.arccos s :=
    Real.contDiffAt_arccos (by linarith [hs.1]) (by linarith [hs.2])
  have hchain := iteratedDeriv_comp_two hg harc
  change iteratedDeriv 2 (fun x => g (Real.arccos x)) s = _ at hchain
  rw [Real.deriv_arccos, iteratedDeriv_two_arccos hs] at hchain
  rw [hchain]
  field_simp
  ring

/-- Polar distance powers are smooth at every nonzero chord, even when the
exponent is below four.  This is the local regularity used in the smooth
angular tail. -/
theorem polarKernel_contDiffAt_of_chord_pos {α θ φ ψ : ℝ}
    (hD : 0 < 2 - 2 * (Real.cos φ * Real.cos ψ +
      Real.sin φ * Real.sin ψ * Real.cos θ)) :
    ContDiffAt ℝ 4
      (fun p : ℝ × ℝ => polarKernel α θ p.1 p.2) (φ, ψ) := by
  let D : ℝ × ℝ → ℝ := fun p =>
    2 - 2 * (Real.cos p.1 * Real.cos p.2 +
      Real.sin p.1 * Real.sin p.2 * Real.cos θ)
  have hDdiff : ContDiffAt ℝ 4 D (φ, ψ) := by
    have hcφ : ContDiffAt ℝ 4 (fun p : ℝ × ℝ => Real.cos p.1) (φ, ψ) :=
      Real.contDiff_cos.contDiffAt.comp (φ, ψ) contDiffAt_fst
    have hcψ : ContDiffAt ℝ 4 (fun p : ℝ × ℝ => Real.cos p.2) (φ, ψ) :=
      Real.contDiff_cos.contDiffAt.comp (φ, ψ) contDiffAt_snd
    have hsφ : ContDiffAt ℝ 4 (fun p : ℝ × ℝ => Real.sin p.1) (φ, ψ) :=
      Real.contDiff_sin.contDiffAt.comp (φ, ψ) contDiffAt_fst
    have hsψ : ContDiffAt ℝ 4 (fun p : ℝ × ℝ => Real.sin p.2) (φ, ψ) :=
      Real.contDiff_sin.contDiffAt.comp (φ, ψ) contDiffAt_snd
    dsimp [D]
    exact contDiffAt_const.sub (contDiffAt_const.mul
      ((hcφ.mul hcψ).add ((hsφ.mul hsψ).mul contDiffAt_const)))
  have hpow : ContDiffAt ℝ 4 (fun x : ℝ => x ^ (α / 2)) (D (φ, ψ)) :=
    Real.contDiffAt_rpow_const_of_ne hD.ne'
  simpa only [polarKernel, D, Function.comp_def] using hpow.comp (φ, ψ) hDdiff

/-- On two comparable nonpolar bands, the angular term alone controls the
chord throughout the positive half-turn. -/
theorem near_band_chord_lower
    {N : ℕ} (hN : 1024 ≤ N) (j k : RingIndex N)
    (hjfirst : j.val + 1 ≠ 1)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val + 1 ≠ 1)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    {s t θ : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1))
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    ((population N (j.val + 1) : ℝ) /
      bandParameter N) ^ 2 * θ ^ 2 / 28800 ≤
      2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
        Real.sqrt (1 - t ^ 2) * Real.cos θ := by
  let rj : ℝ := population N (j.val + 1)
  let rk : ℝ := population N (k.val + 1)
  let M : ℝ := bandParameter N
  have hN4 : 4 ≤ N := by omega
  have hM16 := bandParameter_ge_sixteen_of_ge_1024 hN
  have hMr : 0 < M := by dsimp [M]; exact_mod_cast (by omega : 0 < bandParameter N)
  have hjindex : j.val + 1 < 2 * bandParameter N := by
    have hv := j.isLt
    omega
  have hkindex : k.val + 1 < 2 * bandParameter N := by
    have hv := k.isLt
    omega
  have hrj : 0 < rj := by
    dsimp [rj]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hrk : 0 < rk := by
    dsimp [rk]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ k.val + 1) hkindex
  have hsunit : s ∈ Icc (-1 : ℝ) 1 := ⟨
    (boundary_ge_neg_one hN4 hjindex).trans hs.1,
    hs.2.trans (boundary_le_one hN4 (by omega))⟩
  have htunit : t ∈ Icc (-1 : ℝ) 1 := ⟨
    (boundary_ge_neg_one hN4 hkindex).trans ht.1,
    ht.2.trans (boundary_le_one hN4 (by omega))⟩
  have hradS := (band_radius_comparison hN4 hM16 j
    (by omega) hjlast hs).1
  have hradT := (band_radius_comparison hN4 hM16 k
    (by omega) hklast ht).1
  have hradS0 : 0 ≤ Real.sqrt (1 - s ^ 2) := Real.sqrt_nonneg _
  have hradT0 : 0 ≤ Real.sqrt (1 - t ^ 2) := Real.sqrt_nonneg _
  have hθsq : 0 ≤ θ ^ 2 := sq_nonneg _
  have hcomp' : rj / 8 ≤ rk := hcomp.1
  have hradProd : (rj / (30 * M)) * (rj / (240 * M)) ≤
      Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) := by
    have hradS' : rj / (30 * M) ≤ Real.sqrt (1 - s ^ 2) := by
      convert hradS using 1 <;> ring
    have hradT' : rj / (240 * M) ≤ Real.sqrt (1 - t ^ 2) := by
      calc
        _ ≤ rk / (30 * M) := by
          apply (div_le_div_iff₀ (by positivity : 0 < 240 * M)
            (by positivity : 0 < 30 * M)).2
          nlinarith [mul_nonneg (sub_nonneg.mpr hcomp')
            (show 0 ≤ M by positivity)]
        _ = (1 / 30 : ℝ) * rk / M := by ring
        _ ≤ Real.sqrt (1 - t ^ 2) := hradT
    exact mul_le_mul hradS' hradT' (by positivity) hradS0
  have hmodel := (heightChordSquare_comparison hsunit htunit
    (by rwa [abs_of_nonneg hθ0])).1
  have hangleNonneg : 0 ≤ (Real.arccos s - Real.arccos t) ^ 2 := sq_nonneg _
  change (rj / M) ^ 2 * θ ^ 2 / 28800 ≤ _
  calc
    _ = (1 / 4 : ℝ) * ((rj / (30 * M)) *
      (rj / (240 * M)) * θ ^ 2) := by field_simp; ring
    _ ≤ (1 / 4 : ℝ) *
      ((Real.arccos s - Real.arccos t) ^ 2 +
        Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * θ ^ 2) := by
      gcongr
      nlinarith [hmodel, hradProd, hangleNonneg]
    _ ≤ _ := hmodel

/-- The height-coordinate squared chord used on the truncated angular interval. -/
noncomputable def nearTailChord (p : ℝ × ℝ) (θ : ℝ) : ℝ :=
  2 - 2 * p.1 * p.2 - 2 * Real.sqrt (1 - p.1 ^ 2) *
    Real.sqrt (1 - p.2 ^ 2) * Real.cos θ

/-- The tail cutoff removes the collision even for identical or adjacent
bands, uniformly on the closed height rectangle. -/
theorem near_band_tail_chord_pos
    {N : ℕ} (hN : 1024 ≤ N) (j k : RingIndex N)
    (hjfirst : j.val + 1 ≠ 1)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val + 1 ≠ 1)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    {s t θ : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1))
    (hθ : θ ∈ Icc ((population N (j.val + 1) : ℝ)⁻¹) Real.pi) :
    0 < 2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ := by
  have hN4 : 4 ≤ N := by omega
  have hjindex : j.val + 1 < 2 * bandParameter N := by
    have hv := j.isLt
    omega
  have hrj : 0 < (population N (j.val + 1) : ℝ) := by
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hθ0 : 0 < θ := lt_of_lt_of_le (inv_pos.mpr hrj) hθ.1
  have hM : 0 < (bandParameter N : ℝ) := by
    exact_mod_cast bandParameter_pos hN4
  have hlower := near_band_chord_lower hN j k hjfirst hjlast hkfirst hklast
    hcomp hs ht hθ0.le hθ.2
  have hfactor : 0 <
      ((population N (j.val + 1) : ℝ) / bandParameter N)^2 *
        θ^2 / 28800 := by positivity
  exact lt_of_lt_of_le hfactor hlower

/-- The squared chord stays on the population angular scale throughout the
half-turn for labels separated by at most two. -/
theorem near_band_chord_upper_full
    {N : ℕ} (hN : 1024 ≤ N) (j k : RingIndex N)
    (hjfirst : j.val + 1 ≠ 1)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val + 1 ≠ 1)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    (hnear : |(j.val : ℝ) - k.val| ≤ 2)
    {s t θ : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1))
    (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    nearTailChord (s,t) θ ≤
      (50 * (population N (j.val + 1) : ℝ) / bandParameter N)^2 := by
  let rj : ℝ := population N (j.val + 1)
  let rk : ℝ := population N (k.val + 1)
  let M : ℝ := bandParameter N
  have hN4 : 4 ≤ N := by omega
  have hM16 := bandParameter_ge_sixteen_of_ge_1024 hN
  have hMr : 0 < M := by dsimp [M]; exact_mod_cast bandParameter_pos hN4
  have hjindex : j.val + 1 < 2 * bandParameter N := by
    have hv := j.isLt
    omega
  have hkindex : k.val + 1 < 2 * bandParameter N := by
    have hv := k.isLt
    omega
  have hrj : 0 < rj := by
    dsimp [rj]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hrj1 : 1 ≤ rj := by
    dsimp [rj]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hsunit : s ∈ Icc (-1 : ℝ) 1 := ⟨
    (boundary_ge_neg_one hN4 hjindex).trans hs.1,
    hs.2.trans (boundary_le_one hN4 (by omega))⟩
  have htunit : t ∈ Icc (-1 : ℝ) 1 := ⟨
    (boundary_ge_neg_one hN4 hkindex).trans ht.1,
    ht.2.trans (boundary_le_one hN4 (by omega))⟩
  have hnearZ : |(j.val : ℤ) - k.val| ≤ 2 := by
    exact_mod_cast hnear
  have hgap := near_band_arccos_gap hN4 hM16 j k hnearZ hs ht
  have hradS := (band_radius_comparison hN4 hM16 j
    (by omega) hjlast hs).2
  have hradT := (band_radius_comparison hN4 hM16 k
    (by omega) hklast ht).2
  have hθabs : |θ| ≤ Real.pi := by
    rw [abs_of_nonneg hθ.1]
    exact hθ.2
  have hchord := (heightChordSquare_comparison hsunit htunit hθabs).2
  have hangleSq : (Real.arccos s - Real.arccos t)^2 ≤ (45/M)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hgap 2
    simpa only [sq_abs] using h
  have hπ4 : θ ≤ 4 := le_trans hθ.2 Real.pi_le_four
  have hθsq : θ^2 ≤ 16 := by
    have h := pow_le_pow_left₀ hθ.1 hπ4 2
    norm_num at h
    exact h
  have hsinS0 : 0 ≤ Real.sqrt (1 - s^2) := Real.sqrt_nonneg _
  have hsinT0 : 0 ≤ Real.sqrt (1 - t^2) := Real.sqrt_nonneg _
  have hsinprod : Real.sqrt (1-s^2) * Real.sqrt (1-t^2) ≤
      (rj/M)*(rk/M) :=
    mul_le_mul hradS hradT hsinT0 (by positivity)
  have hlong : Real.sqrt (1-s^2) * Real.sqrt (1-t^2) * θ^2 ≤
      128*rj^2/M^2 := by
    calc
      _ ≤ (rj/M)*(rk/M)*θ^2 := by gcongr
      _ ≤ (rj/M)*(8*rj/M)*16 := by gcongr; exact hcomp.2
      _ = 128*rj^2/M^2 := by field_simp; ring
  have hlat : (Real.arccos s-Real.arccos t)^2 ≤
      2025*rj^2/M^2 := by
    calc
      _ ≤ (45/M)^2 := hangleSq
      _ = 2025/M^2 := by ring
      _ ≤ 2025*rj^2/M^2 := by
        gcongr
        nlinarith [hrj1]
  change 2 - 2*s*t - 2*Real.sqrt (1-s^2) *
    Real.sqrt (1-t^2)*Real.cos θ ≤ _
  calc
    _ ≤ (Real.arccos s-Real.arccos t)^2 +
      Real.sqrt (1-s^2)*Real.sqrt (1-t^2)*θ^2 := hchord
    _ ≤ 2025*rj^2/M^2 + 128*rj^2/M^2 :=
      add_le_add hlat hlong
    _ = 2153*rj^2/M^2 := by ring
    _ ≤ 2500*rj^2/M^2 := by gcongr; norm_num
    _ = (50*rj/M)^2 := by ring

/-- A linear combination of two polar profiles obeys the second height chain rule. -/
theorem iteratedDeriv_two_const_linear_comp_arccos
    {A B : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1)
    (hA : ContDiffAt ℝ 2 A (Real.arccos s))
    (hB : ContDiffAt ℝ 2 B (Real.arccos s))
    (c d : ℝ) :
    iteratedDeriv 2 (fun x => c * A (Real.arccos x) - d * B (Real.arccos x)) s =
      c * (iteratedDeriv 2 A (Real.arccos s) / (Real.sqrt (1-s^2))^2 -
        s * deriv A (Real.arccos s) / (Real.sqrt (1-s^2))^3) -
      d * (iteratedDeriv 2 B (Real.arccos s) / (Real.sqrt (1-s^2))^2 -
        s * deriv B (Real.arccos s) / (Real.sqrt (1-s^2))^3) := by
  have harc : ContDiffAt ℝ 2 Real.arccos s :=
    Real.contDiffAt_arccos (by linarith [hs.1]) (by linarith [hs.2])
  have hAc : ContDiffAt ℝ 2 (fun x => A (Real.arccos x)) s := hA.comp s harc
  have hBc : ContDiffAt ℝ 2 (fun x => B (Real.arccos x)) s := hB.comp s harc
  change iteratedDeriv 2 ((fun x => c * A (Real.arccos x)) -
    (fun x => d * B (Real.arccos x))) s = _
  rw [iteratedDeriv_sub (contDiffAt_const.mul hAc) (contDiffAt_const.mul hBc),
    iteratedDeriv_const_mul hAc, iteratedDeriv_const_mul hBc,
    iteratedDeriv_two_comp_arccos hs hA,
    iteratedDeriv_two_comp_arccos hs hB]


/-- A local two-by-two chain rule for height variables.  The vertical slice
needs only local regularity near the polar angle `arccos s`; this matters
for a positive-angle kernel that becomes singular elsewhere on the sphere. -/
theorem mixedFourth_arccos_chain
    {P : ℝ → ℝ → ℝ} {s t : ℝ} {V : Set ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hV : IsOpen V) (hφV : Real.arccos s ∈ V)
    (hvertical : ∀ u ∈ V, ContDiffAt ℝ 2 (P u) (Real.arccos t))
    (hA : ContDiffAt ℝ 2
      (fun u => iteratedDeriv 2 (P u) (Real.arccos t))
      (Real.arccos s))
    (hB : ContDiffAt ℝ 2
      (fun u => deriv (P u) (Real.arccos t))
      (Real.arccos s)) :
    mixedFourth
      (fun p : ℝ × ℝ => P (Real.arccos p.1) (Real.arccos p.2)) s t =
      (1 / (Real.sqrt (1-t^2))^2) *
        ((iteratedDeriv 2
        (fun u => iteratedDeriv 2 (P u) (Real.arccos t))
        (Real.arccos s)) / (Real.sqrt (1-s^2))^2 -
      s * (deriv
        (fun u => iteratedDeriv 2 (P u) (Real.arccos t))
        (Real.arccos s)) / (Real.sqrt (1-s^2))^3) -
      (t / (Real.sqrt (1-t^2))^3) *
        ((iteratedDeriv 2
        (fun u => deriv (P u) (Real.arccos t))
        (Real.arccos s)) / (Real.sqrt (1-s^2))^2 -
      s * (deriv
        (fun u => deriv (P u) (Real.arccos t))
        (Real.arccos s)) / (Real.sqrt (1-s^2))^3) := by
  let a : ℝ := Real.sqrt (1-s^2)
  let b : ℝ := Real.sqrt (1-t^2)
  let A : ℝ → ℝ := fun u => iteratedDeriv 2 (P u) (Real.arccos t)
  let B : ℝ → ℝ := fun u => deriv (P u) (Real.arccos t)
  have ha : 0 < a := by
    dsimp [a]
    apply Real.sqrt_pos.2
    nlinarith [hs.1, hs.2]
  have hb : 0 < b := by
    dsimp [b]
    apply Real.sqrt_pos.2
    nlinarith [ht.1, ht.2]
  have harc : ContDiffAt ℝ 2 Real.arccos s :=
    Real.contDiffAt_arccos (by linarith [hs.1]) (by linarith [hs.2])
  have hevent : ∀ᶠ x in nhds s, x ∈ Ioo (-1 : ℝ) 1 ∧
      Real.arccos x ∈ V := by
    filter_upwards [isOpen_Ioo.mem_nhds hs,
      harc.continuousAt.eventually (hV.mem_nhds hφV)] with x hx hVx
    exact ⟨hx, hVx⟩
  have hEq : (fun x => iteratedDeriv 2
      (fun y => P (Real.arccos x) (Real.arccos y)) t) =ᶠ[nhds s]
      (fun x => (1 / b^2) * A (Real.arccos x) -
        (t / b^3) * B (Real.arccos x)) := by
    filter_upwards [hevent] with x hx
    have hchain := iteratedDeriv_two_comp_arccos ht
      (hvertical (Real.arccos x) hx.2)
    dsimp [A, B, b]
    convert hchain using 1 <;> ring
  have hfirst : mixedFourth
      (fun p : ℝ × ℝ => P (Real.arccos p.1) (Real.arccos p.2)) s t =
      iteratedDeriv 2 (fun x => (1 / b^2) * A (Real.arccos x) -
        (t / b^3) * B (Real.arccos x)) s := by
    exact Filter.EventuallyEq.iteratedDeriv_eq 2 hEq
  have hsecond := iteratedDeriv_two_const_linear_comp_arccos
    hs hA hB (1 / b^2) (t / b^3)
  exact hfirst.trans (by simpa only [A, B, b] using hsecond)


/-- C4 regularity supplies C2 horizontal dependence of the second vertical derivative. -/
theorem contDiffAt_vertical_second_profile
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)} {φ ψ : ℝ}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (hp : (φ, ψ) ∈ W) :
    ContDiffAt ℝ 2
      (fun u => iteratedDeriv 2 (fun v => G (u,v)) ψ) φ := by
  let V : Set ℝ := {u | (u, ψ) ∈ W}
  have hVo : IsOpen V := hW.preimage (by fun_prop : Continuous (fun u : ℝ => (u, ψ)))
  have hpart : ContDiffAt ℝ 2 (fun u => partialSecondTwice G (u, ψ)) φ := by
    have hmap : ContDiffAt ℝ 2 (fun u : ℝ => (u, ψ)) φ := by fun_prop
    exact ((contDiffOn_partialSecondTwice hW hG).contDiffAt
      (hW.mem_nhds hp)).comp φ hmap
  have hEq : (fun u => iteratedDeriv 2 (fun v => G (u, v)) ψ) =ᶠ[nhds φ]
      (fun u => partialSecondTwice G (u, ψ)) := by
    filter_upwards [hVo.mem_nhds hp] with u hu
    exact iteratedDeriv_two_slice_second_eq_partialSecondTwice hW hG u ψ hu
  exact hpart.congr_of_eventuallyEq hEq

/-- The first vertical derivative profile is likewise C2 horizontally. -/
theorem contDiffAt_vertical_first_profile
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)} {φ ψ : ℝ}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (hp : (φ, ψ) ∈ W) :
    ContDiffAt ℝ 2
      (fun u => deriv (fun v => G (u,v)) ψ) φ := by
  let V : Set ℝ := {u | (u, ψ) ∈ W}
  have hVo : IsOpen V := hW.preimage (by fun_prop : Continuous (fun u : ℝ => (u, ψ)))
  have hpart : ContDiffAt ℝ 2 (fun u => partialSecond G (u, ψ)) φ := by
    have hmap : ContDiffAt ℝ 2 (fun u : ℝ => (u, ψ)) φ := by fun_prop
    exact (((contDiffOn_partialSecond hW hG).of_le (by decide)).contDiffAt
      (hW.mem_nhds hp)).comp φ hmap
  have hEq : (fun u => deriv (fun v => G (u, v)) ψ) =ᶠ[nhds φ]
      (fun u => partialSecond G (u, ψ)) := by
    filter_upwards [hVo.mem_nhds hp] with u hu
    exact deriv_slice_second_eq_partialSecond hW hG u ψ hu
  exact hpart.congr_of_eventuallyEq hEq


/-- Continuity of the squared chord in both heights and angle. -/
theorem continuous_nearTailChord :
    Continuous (fun q : (ℝ × ℝ) × ℝ => nearTailChord q.1 q.2) := by
  unfold nearTailChord
  fun_prop

/-- Heights whose entire angular tail has positive chord. -/
def nearTailRegularSet (r : ℝ) : Set (ℝ × ℝ) :=
  {p | ∀ θ ∈ Icc r⁻¹ Real.pi, 0 < nearTailChord p θ}

/-- Compactness of the angular interval makes tail regularity an open condition. -/
theorem isOpen_nearTailRegularSet (r : ℝ) : IsOpen (nearTailRegularSet r) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hcompact : IsCompact (Icc r⁻¹ Real.pi) := isCompact_Icc
  have hpoint : ∀ θ ∈ Icc r⁻¹ Real.pi,
      ∀ᶠ q : (ℝ × ℝ) × ℝ in nhds (p, θ), 0 < nearTailChord q.1 q.2 := by
    intro θ hθ
    exact (isOpen_Ioi.preimage continuous_nearTailChord).mem_nhds (hp θ hθ)
  exact hcompact.eventually_forall_of_forall_eventually hpoint

/-- Every height in a nonpolar band is strictly between the poles. -/
theorem nonpolar_band_height_interior
    {N : ℕ} (hN : 1024 ≤ N) (j : RingIndex N)
    (hjfirst : j.val + 1 ≠ 1)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    {s : ℝ} (hs : s ∈ band N (j.val + 1)) :
    s ∈ Ioo (-1 : ℝ) 1 := by
  have hN4 : 4 ≤ N := by omega
  have hM16 := bandParameter_ge_sixteen_of_ge_1024 hN
  have hM : 0 < (bandParameter N : ℝ) := by
    exact_mod_cast bandParameter_pos hN4
  have hjindex : j.val + 1 < 2 * bandParameter N := by
    have hv := j.isLt
    omega
  have hrj : 0 < (population N (j.val + 1) : ℝ) := by
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hrad := (band_radius_comparison hN4 hM16 j
    (by omega) hjlast hs).1
  have hradPos : 0 < Real.sqrt (1 - s^2) := by
    have : 0 < (1 / 30 : ℝ) * population N (j.val + 1) /
      bandParameter N := by positivity
    exact lt_of_lt_of_le this hrad
  have hbase : 0 < 1 - s^2 := Real.sqrt_pos.mp hradPos
  constructor <;> nlinarith [sq_nonneg (s + 1), sq_nonneg (s - 1)]

/-- A convenient open domain for truncated-tail calculus. -/
def nearTailPhysicalRegularSet (r : ℝ) : Set (ℝ × ℝ) :=
  nearTailRegularSet r ∩
    (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1)

theorem isOpen_nearTailPhysicalRegularSet (r : ℝ) :
    IsOpen (nearTailPhysicalRegularSet r) :=
  (isOpen_nearTailRegularSet r).inter (isOpen_Ioo.prod isOpen_Ioo)

/-- The closed near rectangle lies in the common open tail domain. -/
theorem near_band_rectangle_subset_tail_regular
    {N : ℕ} (hN : 1024 ≤ N) (j k : RingIndex N)
    (hjfirst : j.val + 1 ≠ 1)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val + 1 ≠ 1)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1)) :
    band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆
      nearTailPhysicalRegularSet (population N (j.val + 1)) := by
  intro p hp
  constructor
  · intro θ hθ
    exact near_band_tail_chord_pos hN j k hjfirst hjlast hkfirst hklast
      hcomp hp.1 hp.2 hθ
  · exact ⟨nonpolar_band_height_interior hN j hjfirst hjlast hp.1,
      nonpolar_band_height_interior hN k hkfirst hklast hp.2⟩


/-- A scale-free four-term estimate for the height-to-polar chain. -/
theorem abs_four_term_chain_le
    {a b ρ C L E s t X22 X12 X21 X11 : ℝ}
    (hρ : 0 < ρ) (ha : ρ ≤ a) (hb : ρ ≤ b)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hE : 0 ≤ E)
    (hs : |s| ≤ 1) (ht : |t| ≤ 1)
    (h22 : |X22| ≤ C * E)
    (h12 : |X12| ≤ C * L * ρ * E)
    (h21 : |X21| ≤ C * L * ρ * E)
    (h11 : |X11| ≤ C * L ^ 2 * ρ ^ 2 * E) :
    |(1/b^2)*(X22/a^2-s*X12/a^3) -
      (t/b^3)*(X21/a^2-s*X11/a^3)| ≤
      C * (1+2*L+L^2) * E / ρ^4 := by
  have ha0 : 0 < a := lt_of_lt_of_le hρ ha
  have hb0 : 0 < b := lt_of_lt_of_le hρ hb
  have hρ2 : ρ^2 ≤ a^2 := by gcongr
  have hρ3 : ρ^3 ≤ a^3 := by gcongr
  have hρb2 : ρ^2 ≤ b^2 := by gcongr
  have hρb3 : ρ^3 ≤ b^3 := by gcongr
  have hden22 : ρ^4 ≤ a^2*b^2 := by
    calc
      ρ^4 = ρ^2*ρ^2 := by ring
      _ ≤ a^2*b^2 := mul_le_mul hρ2 hρb2 (by positivity) (by positivity)
  have hden12 : ρ^3*ρ^2 ≤ a^3*b^2 :=
    mul_le_mul hρ3 hρb2 (by positivity) (by positivity)
  have hden21 : ρ^2*ρ^3 ≤ a^2*b^3 :=
    mul_le_mul hρ2 hρb3 (by positivity) (by positivity)
  have hden11 : ρ^3*ρ^3 ≤ a^3*b^3 :=
    mul_le_mul hρ3 hρb3 (by positivity) (by positivity)
  have h22' : |X22| / (a^2*b^2) ≤ C*E/ρ^4 := by
    calc
      _ ≤ C*E/(a^2*b^2) := by gcongr
      _ ≤ C*E/ρ^4 := by gcongr
  have h12' : |s| * |X12| / (a^3*b^2) ≤ C*L*E/ρ^4 := by
    calc
      _ ≤ |X12| / (a^3*b^2) := by
        gcongr
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (abs_nonneg X12)
      _ ≤ C*L*ρ*E/(ρ^3*ρ^2) := by gcongr
      _ = C*L*E/ρ^4 := by field_simp; ring
  have h21' : |t| * |X21| / (a^2*b^3) ≤ C*L*E/ρ^4 := by
    calc
      _ ≤ |X21| / (a^2*b^3) := by
        gcongr
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ht (abs_nonneg X21)
      _ ≤ C*L*ρ*E/(ρ^2*ρ^3) := by gcongr
      _ = C*L*E/ρ^4 := by field_simp; ring
  have h11' : |s| * |t| * |X11| / (a^3*b^3) ≤ C*L^2*E/ρ^4 := by
    calc
      _ ≤ |X11| / (a^3*b^3) := by
        gcongr
        have hst : |s| * |t| ≤ (1 : ℝ) := by
          calc
            _ ≤ 1 * |t| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
            _ ≤ 1 * 1 := by gcongr
            _ = 1 := by ring
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hst (abs_nonneg X11)
      _ ≤ C*L^2*ρ^2*E/(ρ^3*ρ^3) := by gcongr
      _ = C*L^2*E/ρ^4 := by field_simp; ring
  have hdecomp :
      (1/b^2)*(X22/a^2-s*X12/a^3) -
      (t/b^3)*(X21/a^2-s*X11/a^3) =
      X22/(a^2*b^2) - s*X12/(a^3*b^2) -
      t*X21/(a^2*b^3) + s*t*X11/(a^3*b^3) := by
    field_simp
    ring
  have htri : |(1/b^2)*(X22/a^2-s*X12/a^3) -
      (t/b^3)*(X21/a^2-s*X11/a^3)| ≤
      |X22|/(a^2*b^2) + |s| * |X12|/(a^3*b^2) +
      |t| * |X21|/(a^2*b^3) + |s| * |t| * |X11|/(a^3*b^3) := by
    rw [hdecomp]
    have h1 := abs_add_le
      (X22/(a^2*b^2) - s*X12/(a^3*b^2) - t*X21/(a^2*b^3))
      (s*t*X11/(a^3*b^3))
    have h2 := abs_sub_le
      (X22/(a^2*b^2) - s*X12/(a^3*b^2)) 0
      (t*X21/(a^2*b^3))
    have h3 := abs_sub_le (X22/(a^2*b^2)) 0
      (s*X12/(a^3*b^2))
    have hsum :
      |X22/(a^2*b^2) - s*X12/(a^3*b^2) -
        t*X21/(a^2*b^3) + s*t*X11/(a^3*b^3)| ≤
      |X22/(a^2*b^2)| + |s*X12/(a^3*b^2)| +
        |t*X21/(a^2*b^3)| + |s*t*X11/(a^3*b^3)| := by
      simp only [sub_zero, zero_sub, abs_neg] at h2 h3
      linarith
    convert hsum using 1 <;>
      simp only [abs_div, abs_mul, abs_pow, abs_of_pos ha0,
        abs_of_pos hb0, abs_of_pos hρ] <;> ring

  calc
    _ ≤ |X22| / (a^2*b^2) + |s| * |X12| / (a^3*b^2) +
      |t| * |X21| / (a^2*b^3) + |s| * |t| * |X11| / (a^3*b^3) := htri
    _ ≤ C*E/ρ^4 + C*L*E/ρ^4 + C*L*E/ρ^4 + C*L^2*E/ρ^4 := by
      gcongr
    _ = C * (1+2*L+L^2) * E / ρ^4 := by ring


/-- First and second power shifts used in the polar derivative table. -/
theorem polar_power_step_one
    {α U ρ L : ℝ} (hU : 0 < U) (hρ : 0 < ρ)
    (hL : 0 ≤ L) (hUL : U ≤ (L*ρ)^2) :
    U ^ ((α-3)/2) ≤ (L*ρ) * U ^ ((α-4)/2) := by
  have hsqrt : Real.sqrt U ≤ L*ρ :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hUL⟩
  have hE : 0 ≤ U ^ ((α-4)/2) := Real.rpow_nonneg hU.le _
  have hsplit : U ^ ((α-3)/2) = U ^ ((α-4)/2) * Real.sqrt U := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hU]
    congr 1
    ring
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hsqrt hE]

theorem polar_power_step_two
    {α U ρ L : ℝ} (hU : 0 < U) (hρ : 0 < ρ)
    (hL : 0 ≤ L) (hUL : U ≤ (L*ρ)^2) :
    U ^ ((α-2)/2) ≤ (L*ρ)^2 * U ^ ((α-4)/2) := by
  have hE : 0 ≤ U ^ ((α-4)/2) := Real.rpow_nonneg hU.le _
  have hsplit : U ^ ((α-2)/2) = U ^ ((α-4)/2) * U := by
    have := Real.rpow_add hU ((α-4)/2) 1
    rw [Real.rpow_one] at this
    convert this using 1 <;> ring
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hUL hE]


/-- Smooth-tail C⁴ bound after excluding the angular cusp by θ ≥ 1/r_j. -/
def NearTailDerivativeBound (α : ℝ) : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
    j.val + 1 ≠ 1 → j.val + 1 ≠ 2 * bandParameter N - 1 →
    k.val + 1 ≠ 1 → k.val + 1 ≠ 2 * bandParameter N - 1 →
    Comparable N (j.val + 1) (k.val + 1) →
    |(j.val : ℝ) - k.val| ≤ 2 →
    ∃ W : Set (ℝ × ℝ), IsOpen W ∧
      band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ W ∧
      ContDiffOn ℝ 4
        (nearTailKernel α (population N (j.val + 1))) W ∧
      ∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
        |mixedFourth
          (nearTailKernel α (population N (j.val + 1))) p.1 p.2| ≤
          B * (bandParameter N : ℝ) ^ 8 /
            ((population N (j.val + 1) : ℝ) ^ 5 *
              (bandParameter N : ℝ) ^ α)

/-- The small-arc TV bound and smooth-tail Taylor bound imply the near-block scale. -/
theorem near_comparable_scale_of_analytic_bounds
    {α : ℝ} (hα : 0 < α)
    (hlow : NearLowAngleBound α) (htail : NearTailDerivativeBound α) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
      j.val + 1 ≠ 1 → j.val + 1 ≠ 2 * bandParameter N - 1 →
      k.val + 1 ≠ 1 → k.val + 1 ≠ 2 * bandParameter N - 1 →
      Comparable N (j.val + 1) (k.val + 1) →
      |(j.val : ℝ) - k.val| ≤ 2 →
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        C * (population N (j.val + 1) : ℝ) /
          (bandParameter N : ℝ) ^ α := by
  obtain ⟨A, hA, hlow⟩ := hlow
  obtain ⟨B, hB, htail⟩ := htail
  refine ⟨32 * A + 512 * B, by positivity, ?_⟩
  intro N hN j k hjfirst hjlast hkfirst hklast hcomp hnear
  let rj : ℝ := population N (j.val + 1)
  let rk : ℝ := population N (k.val + 1)
  let M : ℝ := bandParameter N
  have hN4 : 4 ≤ N := by omega
  have hjindex : j.val + 1 < 2 * bandParameter N := by
    have hv := j.isLt
    omega
  have hkindex : k.val + 1 < 2 * bandParameter N := by
    have hv := k.isLt
    omega
  have hrj : 0 < rj := by
    dsimp [rj]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hrk : 0 < rk := by
    dsimp [rk]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ k.val + 1) hkindex
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast bandParameter_pos hN4
  have hMα : 0 < M ^ α := Real.rpow_pos_of_pos hM _
  have hrk8 : rk ≤ 8 * rj := hcomp.2
  have hlowpoint := hlow N hN j k hjfirst hjlast hkfirst hklast hcomp hnear
  have hlowblock :
      |bandBlock N (j.val + 1) (k.val + 1)
        (nearLowKernel α rj)| ≤ 4 * rj * rk * (A / (rj * M ^ α)) :=
    abs_bandBlock_le_of_rectangle_bound hN4 (by omega) hjindex
      (by omega) hkindex _ (by positivity) hlowpoint
  obtain ⟨W, hW, hrect, hsmooth, hderiv⟩ :=
    htail N hN j k hjfirst hjlast hkfirst hklast hcomp hnear
  have htailblock :
      |bandBlock N (j.val + 1) (k.val + 1)
        (nearTailKernel α rj)| ≤
        rj ^ 3 * rk ^ 3 / M ^ 8 * (B * M ^ 8 / (rj ^ 5 * M ^ α)) :=
    mixedTaylorBound N hN4 j k (nearTailKernel α rj) W hW hrect
      hsmooth _ (by positivity) hderiv
  have hlowfinal :
      4 * rj * rk * (A / (rj * M ^ α)) ≤ 32 * A * rj / M ^ α := by
    have hrkpow : rk ≤ 8 * rj := hrk8
    calc
      _ ≤ 4 * rj * (8 * rj) * (A / (rj * M ^ α)) := by gcongr
      _ = 32 * A * rj / M ^ α := by field_simp; ring
  have htailfinal :
      rj ^ 3 * rk ^ 3 / M ^ 8 * (B * M ^ 8 / (rj ^ 5 * M ^ α)) ≤
        512 * B * rj / M ^ α := by
    calc
      _ ≤ rj ^ 3 * (8 * rj) ^ 3 / M ^ 8 *
        (B * M ^ 8 / (rj ^ 5 * M ^ α)) := by gcongr
      _ = 512 * B * rj / M ^ α := by field_simp; ring
  rw [kernelBlock_eq_near_low_add_tail hα N (j.val + 1) (k.val + 1) rj]
  calc
    |bandBlock N (j.val + 1) (k.val + 1) (nearLowKernel α rj) +
      bandBlock N (j.val + 1) (k.val + 1) (nearTailKernel α rj)| ≤
        |bandBlock N (j.val + 1) (k.val + 1) (nearLowKernel α rj)| +
        |bandBlock N (j.val + 1) (k.val + 1) (nearTailKernel α rj)| := abs_add_le _ _
    _ ≤ 32 * A * rj / M ^ α + 512 * B * rj / M ^ α :=
      add_le_add (hlowblock.trans hlowfinal) (htailblock.trans htailfinal)
    _ = (32 * A + 512 * B) * rj / M ^ α := by ring

/-- Near comparable rectangles have the manuscript's displayed decay factor. -/
theorem near_comparable_block_bound_of_analytic_bounds
    {α : ℝ} (hα : 0 < α) (hα2 : α < 2)
    (hlow : NearLowAngleBound α) (htail : NearTailDerivativeBound α) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
      j.val + 1 ≠ 1 → j.val + 1 ≠ 2 * bandParameter N - 1 →
      k.val + 1 ≠ 1 → k.val + 1 ≠ 2 * bandParameter N - 1 →
      Comparable N (j.val + 1) (k.val + 1) →
      |(j.val : ℝ) - k.val| ≤ 2 →
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        C * population N (j.val + 1) / (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
  obtain ⟨C, hC, hscale⟩ :=
    near_comparable_scale_of_analytic_bounds hα hlow htail
  refine ⟨27 * C, by positivity, ?_⟩
  intro N hN j k hjfirst hjlast hkfirst hklast hcomp hnear
  have hbase : 0 < 1 + |(j.val : ℝ) - k.val| := by positivity
  have hupper : 1 + |(j.val : ℝ) - k.val| ≤ 3 := by linarith
  have hexp : α - 3 ≤ 0 := by linarith
  have hpow₁ : (3 : ℝ) ^ (-3 : ℝ) ≤ (3 : ℝ) ^ (α - 3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hpow₂ : (3 : ℝ) ^ (α - 3) ≤
      (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) :=
    Real.rpow_le_rpow_of_nonpos hbase hupper hexp
  have hpow : (1 / 27 : ℝ) ≤
      (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
    calc
      _ = (3 : ℝ) ^ (-3 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ (α - 3) := hpow₁
      _ ≤ _ := hpow₂
  have hr : 0 ≤ (population N (j.val + 1) : ℝ) := by positivity
  have hM : 0 < (bandParameter N : ℝ) := by
    exact_mod_cast bandParameter_pos (by omega : 4 ≤ N)
  have hMα : 0 < (bandParameter N : ℝ) ^ α := Real.rpow_pos_of_pos hM _
  have hscale' := hscale N hN j k hjfirst hjlast hkfirst hklast hcomp hnear
  calc
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        C * (population N (j.val + 1) : ℝ) /
          (bandParameter N : ℝ) ^ α := hscale'
    _ ≤ 27 * C * (population N (j.val + 1) : ℝ) /
          (bandParameter N : ℝ) ^ α *
            (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
      have h := mul_le_mul_of_nonneg_left hpow
        (show 0 ≤ 27 * C * (population N (j.val + 1) : ℝ) /
          (bandParameter N : ℝ) ^ α by positivity)
      convert h using 1 <;> ring

/-- Near comparable block estimate with the low arc already discharged; the
remaining input is exactly the smooth-tail mixed derivative estimate. -/
theorem near_comparable_block_bound_of_tail
    {α : ℝ} (hα : 0 < α) (hα2 : α < 2)
    (htail : NearTailDerivativeBound α) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
      j.val + 1 ≠ 1 → j.val + 1 ≠ 2 * bandParameter N - 1 →
      k.val + 1 ≠ 1 → k.val + 1 ≠ 2 * bandParameter N - 1 →
      Comparable N (j.val + 1) (k.val + 1) →
      |(j.val : ℝ) - k.val| ≤ 2 →
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        C * population N (j.val + 1) / (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) :=
  near_comparable_block_bound_of_analytic_bounds hα hα2
    (nearLowAngleBound hα) htail

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
