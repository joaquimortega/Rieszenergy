import BEMOCFormalization.ComparableHeightChainBounds
import BEMOCFormalization.NearTailIntegralCalculus
import BEMOCFormalization.AngularPowerIntegrals
import BEMOCFormalization.ComparableNearTailScaling

open MeasureTheory Set
open scoped Interval
namespace BEMOC.Definitive

/-- Near-band polar-jet control after the lower chord inequality. -/
theorem near_tail_profile_theta_bound
    {α : ℝ} (C : ℝ) (hC : 0 < C)
    (hderiv : ∀ m n : ℕ, m + n ≤ 4 → ∀ θ φ ψ : ℝ,
      0 < 2 - 2 * (Real.cos φ * Real.cos ψ +
        Real.sin φ * Real.sin ψ * Real.cos θ) →
      |iteratedDeriv m (fun u => iteratedDeriv n
        (fun v => polarKernel α θ u v) ψ) φ| ≤
        C * (2 - 2 * (Real.cos φ * Real.cos ψ +
          Real.sin φ * Real.sin ψ * Real.cos θ)) ^ ((α-m-n)/2))
    (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 1024 ≤ N) (j k : RingIndex N)
    (hjfirst : j.val + 1 ≠ 1)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val + 1 ≠ 1)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    (hnear : |(j.val : ℝ) - k.val| ≤ 2)
    {s t θ : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1))
    (hθ : θ ∈ Icc ((population N (j.val + 1) : ℝ)⁻¹) Real.pi) :
    |mixedFourth (fun p : ℝ × ℝ => latitudeProfile α p.1 p.2 θ) s t| ≤
      C * (1+2*(12000:ℝ)+12000^2) *
        (28800:ℝ)^2 *
        (((population N (j.val + 1) : ℝ)/bandParameter N)*θ)^(α-4) /
          ((population N (j.val + 1) : ℝ)/(240*bandParameter N))^4 := by
  let rj : ℝ := population N (j.val + 1)
  let M : ℝ := bandParameter N
  let D : ℝ := (rj/M)*θ
  have hN4 : 4 ≤ N := by omega
  have hjindex : j.val + 1 < 2 * bandParameter N := by
    have hv := j.isLt
    omega
  have hrj : 0 < rj := by
    dsimp [rj]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast bandParameter_pos hN4
  have hθpos : 0 < θ := lt_of_lt_of_le (inv_pos.mpr hrj) hθ.1
  have hD : 0 < D := by dsimp [D]; positivity
  have hU : 0 < nearTailChord (s,t) θ :=
    near_band_tail_chord_pos hN j k hjfirst hjlast hkfirst hklast
      hcomp hs ht hθ
  have hmodel : D^2 / 28800 ≤ nearTailChord (s,t) θ := by
    have h := near_band_chord_lower hN j k hjfirst hjlast
      hkfirst hklast hcomp hs ht hθpos.le hθ.2
    convert h using 1 <;> dsimp [D, nearTailChord] <;> ring
  have hpower := inverse_chord_power_le hα0 hα2 hU hD hmodel
  have hpoint := near_tail_profile_chord_bound C hC hderiv hN j k
    hjfirst hjlast hkfirst hklast hcomp hnear hs ht hθ
  calc
    _ ≤ C * (1+2*(12000:ℝ)+12000^2) *
      (nearTailChord (s,t) θ)^((α-4)/2) /
        (rj/(240*M))^4 := hpoint
    _ ≤ C * (1+2*(12000:ℝ)+12000^2) * (28800:ℝ)^2 *
      D^(α-4) / (rj/(240*M))^4 := by
      have hcoef : 0 ≤ C * (1+2*(12000:ℝ)+12000^2) /
          (rj/(240*M))^4 := by positivity
      calc
        _ = (C * (1+2*(12000:ℝ)+12000^2) /
          (rj/(240*M))^4) * (nearTailChord (s,t) θ)^((α-4)/2) := by ring
        _ ≤ (C * (1+2*(12000:ℝ)+12000^2) /
          (rj/(240*M))^4) * ((28800:ℝ)^2 * D^(α-4)) :=
          mul_le_mul_of_nonneg_left hpower hcoef
        _ = _ := by ring
    _ = _ := by rfl


theorem tail_integral_le_power_majorant
    {α r A : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hr : 1 ≤ r) (hA : 0 ≤ A) (f : ℝ → ℝ)
    (hpoint : ∀ θ ∈ Icc r⁻¹ Real.pi,
      |f θ| ≤ A * θ^(α-4)) :
    |∫ θ in r⁻¹..Real.pi, f θ| ≤
      A * ((1/(3-α))*r^(3-α)) := by
  have hrpos : 0 < r := by linarith
  have hri : 0 < r⁻¹ := inv_pos.mpr hrpos
  have hle : r⁻¹ ≤ Real.pi := by
    have hri1 : r⁻¹ ≤ 1 := (inv_le_one₀ hrpos).2 hr
    linarith [Real.pi_gt_three]
  have hmajorant : ∀ᵐ θ ∂volume.restrict (Ι r⁻¹ Real.pi),
      ‖f θ‖ ≤ A * θ^(α-4) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc)] with θ hθ
    have hθI : θ ∈ Icc r⁻¹ Real.pi := by
      rw [Set.uIoc_of_le hle] at hθ
      exact ⟨hθ.1.le, hθ.2⟩
    simpa only [Real.norm_eq_abs] using hpoint θ hθI
  have hint : IntervalIntegrable (fun θ : ℝ => A * θ^(α-4))
      volume r⁻¹ Real.pi := by
    exact (intervalIntegral.intervalIntegrable_rpow (Or.inr (by
      rw [Set.uIcc_of_le hle]
      intro h
      have hh := h.1
      linarith))).const_mul A
  have hbase := intervalIntegral.norm_integral_le_of_norm_le hmajorant hint
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hbase
  have hpowerNonneg := truncated_angular_power_integral_nonneg hα0 hα2 hr
  have hpowerBound := truncated_angular_power_integral_bound hα0 hα2 hr
  have hscalarNonneg : 0 ≤ A * (∫ θ in r⁻¹..Real.pi, θ^(α-4)) :=
    mul_nonneg hA hpowerNonneg
  rw [abs_of_nonneg hscalarNonneg] at hbase
  calc
    _ ≤ A * (∫ θ in r⁻¹..Real.pi, θ^(α-4)) := hbase
    _ ≤ A * ((1/(3-α))*r^(3-α)) :=
      mul_le_mul_of_nonneg_left hpowerBound hA


/-- The smooth angular tail obeys the required fourth derivative scale. -/
theorem near_tail_derivative_bound {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    NearTailDerivativeBound α := by
  obtain ⟨C, hC, hpolar⟩ := polar_derivative_bound hα0 hα2
  let K : ℝ := C * (1 + 2 * (12000:ℝ) + 12000^2) * (28800:ℝ)^2
  let B : ℝ := K * 240^4 / (Real.pi * (3-α))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB : 0 < B := by
    have hden : 0 < 3 - α := by linarith
    dsimp [B, K]
    positivity
  refine ⟨B, hB, ?_⟩
  intro N hN j k hjfirst hjlast hkfirst hklast hcomp hnear
  let r : ℝ := population N (j.val + 1)
  let M : ℝ := bandParameter N
  let W : Set (ℝ × ℝ) := nearTailPhysicalRegularSet r
  have hN4 : 4 ≤ N := by omega
  have hjindex : j.val + 1 < 2 * bandParameter N := by
    have hv := j.isLt
    omega
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hr1 : 1 ≤ r := by
    dsimp [r]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast bandParameter_pos hN4
  have hπ : r⁻¹ ≤ Real.pi := by
    have hri : r⁻¹ ≤ 1 := (inv_le_one₀ hr).2 hr1
    linarith [Real.pi_gt_three]
  have hW : IsOpen W := isOpen_nearTailPhysicalRegularSet r
  have hrect : band N (j.val+1) ×ˢ band N (k.val+1) ⊆ W :=
    near_band_rectangle_subset_tail_regular hN j k hjfirst hjlast
      hkfirst hklast hcomp
  have hphysical : W ⊆ Ioo (-1:ℝ) 1 ×ˢ Ioo (-1:ℝ) 1 := fun p hp => hp.2
  have hchord : ∀ p ∈ W, ∀ θ ∈ Icc r⁻¹ Real.pi,
      0 < 2 - 2*p.1*p.2 - 2*Real.sqrt (1-p.1^2)*
        Real.sqrt (1-p.2^2)*Real.cos θ := by
    intro p hp θ hθ
    exact hp.1 θ hθ
  refine ⟨W, hW, hrect,
    nearTailKernel_contDiffOn_of_chord_pos hr hπ hW hphysical hchord, ?_⟩
  intro p hp
  have hpW : p ∈ W := hrect hp
  have hident := mixedFourth_nearTailKernel_eq_integral (α := α) hr hπ hW
    hphysical hchord hpW
  let A : ℝ := K * 240^4 * (r/M)^(α-8)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint : ∀ θ ∈ Icc r⁻¹ Real.pi,
      |mixedFourth (fun q : ℝ × ℝ => latitudeProfile α q.1 q.2 θ)
        p.1 p.2| ≤ A * θ^(α-4) := by
    intro θ hθ
    have hθpos : 0 < θ := lt_of_lt_of_le (inv_pos.mpr hr) hθ.1
    have hraw := near_tail_profile_theta_bound C hC hpolar hα0 hα2
      hN j k hjfirst hjlast hkfirst hklast hcomp hnear hp.1 hp.2 hθ
    calc
      _ ≤ K * (((r/M)*θ)^(α-4) / (r/(240*M))^4) := by
        convert hraw using 1 <;> dsimp [K, r, M] <;> ring
      _ = A * θ^(α-4) := by
        rw [near_tail_radius_denominator,
          near_tail_pointwise_power_identity (div_pos hr hM) hθpos]
        dsimp [A]
        ring
  have hint := tail_integral_le_power_majorant hα0 hα2 hr1 hA
    (fun θ => mixedFourth (fun q : ℝ × ℝ =>
      latitudeProfile α q.1 q.2 θ) p.1 p.2) hpoint
  rw [hident, abs_mul, abs_of_pos (div_pos (by norm_num : (0:ℝ)<1) Real.pi_pos)]
  have hscale := near_tail_integrated_power_identity (α := α) hr hM
  calc
    _ ≤ (1/Real.pi) * (A * ((1/(3-α))*r^(3-α))) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = B * (r^(3-α) * (r/M)^(α-8)) := by
      dsimp [A, B]
      have hden : 3 - α ≠ 0 := by linarith
      field_simp [ne_of_gt Real.pi_pos, hden]
      ring
    _ = B * M^8 / (r^5 * M^α) := by rw [hscale]; ring
    _ = _ := by rfl

/-- The complete regular near comparable estimate, including the small arc. -/
theorem near_comparable_block_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
      j.val + 1 ≠ 1 → j.val + 1 ≠ 2 * bandParameter N - 1 →
      k.val + 1 ≠ 1 → k.val + 1 ≠ 2 * bandParameter N - 1 →
      Comparable N (j.val + 1) (k.val + 1) →
      |(j.val : ℝ) - k.val| ≤ 2 →
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        C * population N (j.val + 1) / (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) :=
  near_comparable_block_bound_of_tail hα0 hα2
    (near_tail_derivative_bound hα0 hα2)

end BEMOC.Definitive
