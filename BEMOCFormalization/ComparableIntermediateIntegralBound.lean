import BEMOCFormalization.ComparableIntermediateBlocks
import BEMOCFormalization.ComparableIntermediateIntegrability

open Set MeasureTheory
namespace BEMOC.Definitive

/-- A pointwise fourth-derivative bound integrates to the exact intermediate
comparable model. The pointwise estimate is supplied by the polar chain. -/
theorem intermediate_mixedFourth_integral_bound_of_pointwise
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 1024 ≤ N) (j k : RingIndex N)
    (hjfirst : j.val ≠ 0)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val ≠ 0)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    (hjk : 2 ≤ |(j.val : ℤ) - k.val|)
    (hnear : |(j.val : ℝ) - k.val| ≤
      2 * population N (j.val + 1))
    {p : ℝ × ℝ}
    (hp : p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1))
    {K : ℝ} (hK : 0 ≤ K)
    (hpoint : ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      |mixedFourth (fun q : ℝ × ℝ =>
        latitudeProfile α q.1 q.2 θ) p.1 p.2| ≤
        K * (2 - 2 * p.1 * p.2 -
          2 * Real.sqrt (1 - p.1 ^ 2) *
            Real.sqrt (1 - p.2 ^ 2) * Real.cos θ) ^ ((α - 4) / 2)) :
    |∫ θ in (0 : ℝ)..Real.pi,
      mixedFourth (fun q : ℝ × ℝ =>
        latitudeProfile α q.1 q.2 θ) p.1 p.2| ≤
      K * ((1 + 1 / (3 - α)) *
        (|(j.val : ℝ) - k.val| / bandParameter N / 60) ^ (α - 3) /
        ((population N (j.val + 1) : ℝ) / bandParameter N / 180)) := by
  let A : ℝ → ℝ := fun θ => 2 - 2 * p.1 * p.2 -
    2 * Real.sqrt (1 - p.1 ^ 2) *
      Real.sqrt (1 - p.2 ^ 2) * Real.cos θ
  let f : ℝ → ℝ := fun θ => mixedFourth (fun q : ℝ × ℝ =>
    latitudeProfile α q.1 q.2 θ) p.1 p.2
  let W := integralParameterDomain nearTailSmoothDomain 0 Real.pi
  let F : (ℝ × ℝ) × ℝ → ℝ :=
    fun z => latitudeProfile α z.1.1 z.1.2 z.2
  have hsm := intermediate_profile_smooth_extension hα0 hN j k
    hjfirst hjlast hkfirst hklast hcomp hjk hnear
  have hpW : p ∈ W := hsm.2.1 hp
  have hfint : IntervalIntegrable f volume 0 Real.pi :=
    intervalIntegrable_latitudeProfile_mixedFourth α Real.pi_nonneg hpW
  have hApos (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) : 0 < A θ := by
    have hgeo := intermediate_comparable_chord_bounds hN j k
      hjfirst hjlast hkfirst hklast hcomp hjk hnear hp.1 hp.2 hθ
    have hM : (0 : ℝ) < bandParameter N := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (16 : ℕ))
        (bandParameter_ge_sixteen_of_ge_1024 hN))
    have hd : 0 < |(j.val : ℝ) - k.val| / bandParameter N := by
      apply div_pos _ hM
      have hℓ : 2 ≤ |(j.val : ℝ) - k.val| := by exact_mod_cast hjk
      linarith
    have hδ : 0 < (|(j.val : ℝ) - k.val| /
        (bandParameter N : ℝ)) ^ 2 / 3600 :=
      div_pos (sq_pos_of_pos hd) (by norm_num)
    have hθterm : 0 ≤ ((population N (j.val + 1) : ℝ) /
      bandParameter N) ^ 2 * θ ^ 2 / 30000 := by positivity
    dsimp [A]
    linarith [hgeo.1]
  have hAcont : Continuous A := by dsimp [A]; fun_prop
  have hAint : IntervalIntegrable
      (fun θ => A θ ^ ((α - 4) / 2)) volume 0 Real.pi := by
    apply ContinuousOn.intervalIntegrable_of_Icc Real.pi_nonneg
    apply ContinuousOn.rpow_const hAcont.continuousOn
    intro θ hθ
    exact Or.inl (hApos θ hθ).ne'
  have hgint : IntervalIntegrable
      (fun θ => K * A θ ^ ((α - 4) / 2)) volume 0 Real.pi :=
    hAint.const_mul K
  have hmono : (∫ θ in (0 : ℝ)..Real.pi, |f θ|) ≤
      ∫ θ in (0 : ℝ)..Real.pi, K * A θ ^ ((α - 4) / 2) :=
    intervalIntegral.integral_mono_on Real.pi_nonneg hfint.abs hgint
      (by intro θ hθ; exact hpoint θ hθ)
  have hangular := intermediate_inverse_chord_integral_bound hα0 hα2 hN j k
    hjfirst hjlast hkfirst hklast hcomp hjk hnear hp.1 hp.2
  calc
    |∫ θ in (0 : ℝ)..Real.pi, f θ| ≤
        ∫ θ in (0 : ℝ)..Real.pi, |f θ| :=
      intervalIntegral.abs_integral_le_integral_abs Real.pi_nonneg
    _ ≤ ∫ θ in (0 : ℝ)..Real.pi,
        K * A θ ^ ((α - 4) / 2) := hmono
    _ = K * ∫ θ in (0 : ℝ)..Real.pi,
        A θ ^ ((α - 4) / 2) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ K * ((1 + 1 / (3 - α)) *
        (|(j.val : ℝ) - k.val| / bandParameter N / 60) ^ (α - 3) /
        ((population N (j.val + 1) : ℝ) / bandParameter N / 180)) :=
      mul_le_mul_of_nonneg_left hangular hK

end BEMOC.Definitive
