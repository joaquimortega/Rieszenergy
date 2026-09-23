import BEMOCFormalization.ComparableSeparatedBlocks
import BEMOCFormalization.AngularPowerIntegrals
import BEMOCFormalization.NearTailIntegralCalculus

open Set MeasureTheory
namespace BEMOC.Definitive

/-- Uniform radius and angular-gap comparisons on a nonendpoint comparable
rectangle with at least two labels of separation. -/
theorem intermediate_comparable_profile {N : ℕ} (hN : 1024 ≤ N)
    (j k : RingIndex N)
    (hjfirst : j.val ≠ 0)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val ≠ 0)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    (hjk : 2 ≤ |(j.val : ℤ) - k.val|)
    {s t : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1)) :
    let R : ℝ := (population N (j.val + 1) : ℝ) / bandParameter N
    let d : ℝ := |(j.val : ℝ) - k.val| / bandParameter N
    R / 30 ≤ Real.sqrt (1 - s ^ 2) ∧
      Real.sqrt (1 - s ^ 2) ≤ R ∧
      R / 240 ≤ Real.sqrt (1 - t ^ 2) ∧
      Real.sqrt (1 - t ^ 2) ≤ 8 * R ∧
      d / 30 ≤ |Real.arccos s - Real.arccos t| ∧
      |Real.arccos s - Real.arccos t| ≤ 30 * d := by
  let M : ℝ := bandParameter N
  let r : ℝ := population N (j.val + 1)
  let r' : ℝ := population N (k.val + 1)
  let R : ℝ := r / M
  let d : ℝ := |(j.val : ℝ) - k.val| / M
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (16 : ℕ))
      (bandParameter_ge_sixteen_of_ge_1024 hN))
  have hRj := band_radius_comparison (by omega : 4 ≤ N)
    (bandParameter_ge_sixteen_of_ge_1024 hN) j hjfirst hjlast hs
  have hRk := band_radius_comparison (by omega : 4 ≤ N)
    (bandParameter_ge_sixteen_of_ge_1024 hN) k hkfirst hklast ht
  have hcompLo : r / 8 ≤ r' := hcomp.1
  have hcompHi : r' ≤ 8 * r := hcomp.2
  have hdivLo : R / 8 ≤ r' / M := by
    have h := div_le_div_of_nonneg_right hcompLo hM.le
    simpa [R, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hdivHi : r' / M ≤ 8 * R := by
    have h := div_le_div_of_nonneg_right hcompHi hM.le
    simpa [R, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hd := separated_band_arccos_gap (by omega : 4 ≤ N)
    (bandParameter_ge_sixteen_of_ge_1024 hN) j k hjk hs ht
  change R / 30 ≤ Real.sqrt (1 - s ^ 2) ∧
    Real.sqrt (1 - s ^ 2) ≤ R ∧
    R / 240 ≤ Real.sqrt (1 - t ^ 2) ∧
    Real.sqrt (1 - t ^ 2) ≤ 8 * R ∧
    d / 30 ≤ |Real.arccos s - Real.arccos t| ∧
    |Real.arccos s - Real.arccos t| ≤ 30 * d
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [R, M, r, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using hRj.1
  · exact hRj.2
  · calc
      R / 240 = (R / 8) / 30 := by ring
      _ ≤ (r' / M) / 30 := by gcongr
      _ ≤ Real.sqrt (1 - t ^ 2) := by
        simpa [r', M, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          using hRk.1
  · exact hRk.2.trans hdivHi
  · simpa [d, M, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using hd.1
  · simpa [d, M, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using hd.2

/-- In the intermediate comparable range, the chord has the model lower
bound needed for the scaled angular integral and a uniform radius upper bound. -/
theorem intermediate_comparable_chord_bounds {N : ℕ} (hN : 1024 ≤ N)
    (j k : RingIndex N)
    (hjfirst : j.val ≠ 0)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val ≠ 0)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    (hjk : 2 ≤ |(j.val : ℤ) - k.val|)
    (hnear : |(j.val : ℝ) - k.val| ≤
      2 * population N (j.val + 1))
    {s t θ : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1))
    (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    let R : ℝ := (population N (j.val + 1) : ℝ) / bandParameter N
    let d : ℝ := |(j.val : ℝ) - k.val| / bandParameter N
    d ^ 2 / 3600 + R ^ 2 * θ ^ 2 / 30000 ≤
      2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
        Real.sqrt (1 - t ^ 2) * Real.cos θ ∧
    2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ ≤ 4096 * R ^ 2 := by
  let M : ℝ := bandParameter N
  let R : ℝ := (population N (j.val + 1) : ℝ) / M
  let d : ℝ := |(j.val : ℝ) - k.val| / M
  let a : ℝ := Real.sqrt (1 - s ^ 2)
  let b : ℝ := Real.sqrt (1 - t ^ 2)
  let δ : ℝ := |Real.arccos s - Real.arccos t|
  let D : ℝ := 2 - 2 * s * t - 2 * a * b * Real.cos θ
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (16 : ℕ))
      (bandParameter_ge_sixteen_of_ge_1024 hN))
  have hR : 0 ≤ R := by positivity
  have hd : 0 ≤ d := by positivity
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hδ : 0 ≤ δ := abs_nonneg _
  have hp := intermediate_comparable_profile hN j k hjfirst hjlast
    hkfirst hklast hcomp hjk hs ht
  have haLo : R / 30 ≤ a := hp.1
  have haHi : a ≤ R := hp.2.1
  have hbLo : R / 240 ≤ b := hp.2.2.1
  have hbHi : b ≤ 8 * R := hp.2.2.2.1
  have hδLo : d / 30 ≤ δ := hp.2.2.2.2.1
  have hδHi : δ ≤ 30 * d := hp.2.2.2.2.2
  have hdR : d ≤ 2 * R := by
    have h := div_le_div_of_nonneg_right hnear hM.le
    simpa [d, R, M, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using h
  have hδHiR : δ ≤ 60 * R := by linarith only [hδHi, hdR]
  have hsI : s ∈ Icc (-1 : ℝ) 1 := by
    have hlo := boundary_ge_neg_one (by omega : 4 ≤ N)
      (by have := j.isLt; omega : j.val + 1 < 2 * bandParameter N)
    have hhi := boundary_le_one (by omega : 4 ≤ N)
      (by have := j.isLt; omega : j.val < 2 * bandParameter N)
    exact ⟨hlo.trans hs.1, hs.2.trans hhi⟩
  have htI : t ∈ Icc (-1 : ℝ) 1 := by
    have hlo := boundary_ge_neg_one (by omega : 4 ≤ N)
      (by have := k.isLt; omega : k.val + 1 < 2 * bandParameter N)
    have hhi := boundary_le_one (by omega : 4 ≤ N)
      (by have := k.isLt; omega : k.val < 2 * bandParameter N)
    exact ⟨hlo.trans ht.1, ht.2.trans hhi⟩
  have hθabs : |θ| ≤ Real.pi := by rw [abs_of_nonneg hθ.1]; exact hθ.2
  have hchord := heightChordSquare_comparison hsI htI hθabs
  have hchord' : (1 / 4 : ℝ) * (δ ^ 2 + a * b * θ ^ 2) ≤ D ∧
      D ≤ δ ^ 2 + a * b * θ ^ 2 := by
    simpa [δ, D, a, b, sq_abs] using hchord
  have hδSqLo : d ^ 2 / 900 ≤ δ ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hδLo)
      (add_nonneg hδ (by positivity : 0 ≤ d / 30))
    nlinarith only [h]
  have habLo : R ^ 2 / 7200 ≤ a * b := by
    have h1 := mul_nonneg (sub_nonneg.mpr haLo) hb
    have h2 := mul_nonneg (sub_nonneg.mpr hbLo)
      (by positivity : 0 ≤ R / 30)
    nlinarith only [h1, h2]
  have habθLo : R ^ 2 / 7200 * θ ^ 2 ≤ a * b * θ ^ 2 :=
    mul_le_mul_of_nonneg_right habLo (sq_nonneg θ)
  have hδSqHi : δ ^ 2 ≤ 3600 * R ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hδHiR)
      (add_nonneg (by positivity : 0 ≤ 60 * R) hδ)
    nlinarith only [h]
  have habHi : a * b ≤ 8 * R ^ 2 := by
    have h1 := mul_nonneg (sub_nonneg.mpr haHi) hb
    have h2 := mul_nonneg (sub_nonneg.mpr hbHi) hR
    nlinarith only [h1, h2]
  have hθHi : θ ≤ 4 := hθ.2.trans Real.pi_le_four
  have hθSqHi : θ ^ 2 ≤ 16 := by nlinarith only [hθ.1, hθHi, sq_nonneg (θ - 4)]
  have habθHi : a * b * θ ^ 2 ≤ 128 * R ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right habHi (sq_nonneg θ)
    have h2 := mul_le_mul_of_nonneg_left hθSqHi (by positivity : 0 ≤ 8 * R ^ 2)
    nlinarith only [h1, h2]
  change d ^ 2 / 3600 + R ^ 2 * θ ^ 2 / 30000 ≤ D ∧
    D ≤ 4096 * R ^ 2
  constructor
  · nlinarith only [hchord'.1, hδSqLo, habθLo, sq_nonneg R,
      sq_nonneg θ]
  · nlinarith only [hchord'.2, hδSqHi, habθHi, sq_nonneg R]

/-- Pointwise reduction of the singular order-four angular power to the
one-dimensional model treated by `angular_inverse_power_integral_bound`. -/
theorem intermediate_inverse_chord_le {α : ℝ}
    (hα2 : α < 2) {N : ℕ} (hN : 1024 ≤ N)
    (j k : RingIndex N)
    (hjfirst : j.val ≠ 0)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val ≠ 0)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    (hjk : 2 ≤ |(j.val : ℤ) - k.val|)
    (hnear : |(j.val : ℝ) - k.val| ≤
      2 * population N (j.val + 1))
    {s t θ : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1))
    (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    (2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ) ^ ((α - 4) / 2) ≤
    (((|(j.val : ℝ) - k.val| / (bandParameter N : ℝ)) / 60) ^ 2 +
      (((population N (j.val + 1) : ℝ) /
        (bandParameter N : ℝ) / 180) * θ) ^ 2) ^ ((α - 4) / 2) := by
  let R : ℝ := (population N (j.val + 1) : ℝ) / bandParameter N
  let d : ℝ := |(j.val : ℝ) - k.val| / bandParameter N
  let A : ℝ := 2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
    Real.sqrt (1 - t ^ 2) * Real.cos θ
  let B : ℝ := (d / 60) ^ 2 + ((R / 180) * θ) ^ 2
  have hM : (0 : ℝ) < bandParameter N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (16 : ℕ))
      (bandParameter_ge_sixteen_of_ge_1024 hN))
  have hd : 0 < d := by
    dsimp [d]
    apply div_pos _ hM
    have hℓ : 2 ≤ |(j.val : ℝ) - k.val| := by exact_mod_cast hjk
    linarith
  have hB : 0 < B := by
    dsimp [B]
    have hδ : 0 < (d / 60) ^ 2 := sq_pos_of_pos (div_pos hd (by norm_num))
    nlinarith [sq_nonneg ((R / 180) * θ)]
  have hgeo := intermediate_comparable_chord_bounds hN j k
    hjfirst hjlast hkfirst hklast hcomp hjk hnear hs ht hθ
  have hBA : B ≤ A := by
    have hRθ : 0 ≤ R ^ 2 * θ ^ 2 := by positivity
    dsimp [B, A]
    dsimp [R, d] at hgeo
    nlinarith [hgeo.1, hRθ]
  have hexp : (α - 4) / 2 ≤ 0 := by linarith
  exact Real.rpow_le_rpow_of_nonpos hB hBA hexp

/-- The singular angular power has the exact scaled integral bound needed
for the regular intermediate comparable case. -/
theorem intermediate_inverse_chord_integral_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) {N : ℕ} (hN : 1024 ≤ N)
    (j k : RingIndex N)
    (hjfirst : j.val ≠ 0)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val ≠ 0)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    (hjk : 2 ≤ |(j.val : ℤ) - k.val|)
    (hnear : |(j.val : ℝ) - k.val| ≤
      2 * population N (j.val + 1))
    {s t : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1)) :
    let R : ℝ := (population N (j.val + 1) : ℝ) / bandParameter N
    let d : ℝ := |(j.val : ℝ) - k.val| / bandParameter N
    (∫ θ in (0 : ℝ)..Real.pi,
      (2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
        Real.sqrt (1 - t ^ 2) * Real.cos θ) ^ ((α - 4) / 2)) ≤
      (1 + 1 / (3 - α)) * (d / 60) ^ (α - 3) / (R / 180) := by
  let R : ℝ := (population N (j.val + 1) : ℝ) / bandParameter N
  let d : ℝ := |(j.val : ℝ) - k.val| / bandParameter N
  let a : ℝ := Real.sqrt (1 - s ^ 2)
  let b : ℝ := Real.sqrt (1 - t ^ 2)
  let A : ℝ → ℝ := fun θ => 2 - 2 * s * t - 2 * a * b * Real.cos θ
  let B : ℝ → ℝ := fun θ => (d / 60) ^ 2 + ((R / 180) * θ) ^ 2
  have hM : (0 : ℝ) < bandParameter N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (16 : ℕ))
      (bandParameter_ge_sixteen_of_ge_1024 hN))
  have hd : 0 < d := by
    dsimp [d]
    apply div_pos _ hM
    have hℓ : 2 ≤ |(j.val : ℝ) - k.val| := by exact_mod_cast hjk
    linarith
  have hR : 0 < R := by
    dsimp [R]
    apply div_pos _ hM
    exact_mod_cast population_pos (by omega : 4 ≤ N) (by omega)
      (by have := j.isLt; omega)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hgeo0 := intermediate_comparable_chord_bounds hN j k
    hjfirst hjlast hkfirst hklast hcomp hjk hnear hs ht
    (show (0 : ℝ) ∈ Icc 0 Real.pi by exact ⟨le_refl _, Real.pi_nonneg⟩)
  have hA0 : 0 < 2 - 2 * s * t - 2 * a * b := by
    have hδ : 0 < d ^ 2 / 3600 := div_pos (sq_pos_of_pos hd) (by norm_num)
    have hmin : d ^ 2 / 3600 ≤ 2 - 2 * s * t - 2 * a * b := by
      simpa [d, R, a, b, Real.cos_zero] using hgeo0.1
    exact hδ.trans_le hmin
  have hApos (θ : ℝ) : 0 < A θ := by
    have hc : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hv : 0 ≤ 2 * a * b := by positivity
    have hm := mul_nonneg hv (sub_nonneg.mpr hc)
    dsimp [A]
    nlinarith only [hA0, hm]
  have hBpos (θ : ℝ) : 0 < B θ := by
    dsimp [B]
    have hδ : 0 < (d / 60) ^ 2 := sq_pos_of_pos (div_pos hd (by norm_num))
    nlinarith [sq_nonneg ((R / 180) * θ)]
  have hAcont : Continuous A := by dsimp [A]; fun_prop
  have hBcont : Continuous B := by dsimp [B]; fun_prop
  have hAint : IntervalIntegrable (fun θ => A θ ^ ((α - 4) / 2))
      volume 0 Real.pi :=
    (hAcont.rpow_const (fun θ => Or.inl (hApos θ).ne')).intervalIntegrable _ _
  have hBint : IntervalIntegrable (fun θ => B θ ^ ((α - 4) / 2))
      volume 0 Real.pi :=
    (hBcont.rpow_const (fun θ => Or.inl (hBpos θ).ne')).intervalIntegrable _ _
  have hmono : (∫ θ in (0 : ℝ)..Real.pi, A θ ^ ((α - 4) / 2)) ≤
      ∫ θ in (0 : ℝ)..Real.pi, B θ ^ ((α - 4) / 2) :=
    intervalIntegral.integral_mono_on Real.pi_nonneg hAint hBint (by
      intro θ hθ
      exact intermediate_inverse_chord_le hα2 hN j k hjfirst hjlast
        hkfirst hklast hcomp hjk hnear hs ht hθ)
  have hscalar := angular_inverse_power_integral_bound hα0 hα2
    (div_pos hd (by norm_num : (0 : ℝ) < 60))
    (div_pos hR (by norm_num : (0 : ℝ) < 180))
  exact hmono.trans hscalar

/-- The full half-turn angular average is a genuine C⁴ extension of the
latitude kernel on every regular intermediate comparable rectangle. -/
theorem intermediate_profile_smooth_extension {α : ℝ} (hα0 : 0 < α)
    {N : ℕ} (hN : 1024 ≤ N) (j k : RingIndex N)
    (hjfirst : j.val ≠ 0)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    (hkfirst : k.val ≠ 0)
    (hklast : k.val + 1 ≠ 2 * bandParameter N - 1)
    (hcomp : Comparable N (j.val + 1) (k.val + 1))
    (hjk : 2 ≤ |(j.val : ℤ) - k.val|)
    (hnear : |(j.val : ℝ) - k.val| ≤
      2 * population N (j.val + 1)) :
    let W := integralParameterDomain nearTailSmoothDomain 0 Real.pi
    let G : ℝ × ℝ → ℝ := fun p => (1 / Real.pi) *
      ∫ θ in (0 : ℝ)..Real.pi, latitudeProfile α p.1 p.2 θ
    IsOpen W ∧
      band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ W ∧
      ContDiffOn ℝ 4 G W ∧
      ∀ s ∈ band N (j.val + 1), ∀ t ∈ band N (k.val + 1),
        G (s, t) = latitudeKernel α s t := by
  let W := integralParameterDomain nearTailSmoothDomain 0 Real.pi
  let F : (ℝ × ℝ) × ℝ → ℝ :=
    fun z => latitudeProfile α z.1.1 z.1.2 z.2
  let I : ℝ × ℝ → ℝ := fun p => ∫ θ in (0 : ℝ)..Real.pi, F (p, θ)
  let G : ℝ × ℝ → ℝ := fun p => (1 / Real.pi) * I p
  have hW : IsOpen W := isOpen_integralParameterDomain
    isOpen_nearTailSmoothDomain 0 Real.pi
  have hF : ContDiffOn ℝ 4 F nearTailSmoothDomain :=
    latitudeProfile_joint_contDiffOn α
  have hrect : band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ W := by
    intro p hp θ hθ
    have hprof := intermediate_comparable_profile hN j k
      hjfirst hjlast hkfirst hklast hcomp hjk hp.1 hp.2
    have hM : (0 : ℝ) < bandParameter N := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (16 : ℕ))
        (bandParameter_ge_sixteen_of_ge_1024 hN))
    have hR : 0 < (population N (j.val + 1) : ℝ) /
        bandParameter N := by
      apply div_pos _ hM
      exact_mod_cast population_pos (by omega : 4 ≤ N) (by omega)
        (by have := j.isLt; omega)
    have hsrad : 0 < Real.sqrt (1 - p.1 ^ 2) :=
      (div_pos hR (by norm_num)).trans_le hprof.1
    have htrad : 0 < Real.sqrt (1 - p.2 ^ 2) :=
      (div_pos hR (by norm_num)).trans_le hprof.2.2.1
    have hsclosed : p.1 ∈ Icc (-1 : ℝ) 1 := by
      have hlo := boundary_ge_neg_one (by omega : 4 ≤ N)
        (by have := j.isLt; omega : j.val + 1 < 2 * bandParameter N)
      have hhi := boundary_le_one (by omega : 4 ≤ N)
        (by have := j.isLt; omega : j.val < 2 * bandParameter N)
      exact ⟨hlo.trans hp.1.1, hp.1.2.trans hhi⟩
    have htclosed : p.2 ∈ Icc (-1 : ℝ) 1 := by
      have hlo := boundary_ge_neg_one (by omega : 4 ≤ N)
        (by have := k.isLt; omega : k.val + 1 < 2 * bandParameter N)
      have hhi := boundary_le_one (by omega : 4 ≤ N)
        (by have := k.isLt; omega : k.val < 2 * bandParameter N)
      exact ⟨hlo.trans hp.2.1, hp.2.2.trans hhi⟩
    have hsopen : p.1 ∈ Ioo (-1 : ℝ) 1 := by
      have hsq := Real.sqrt_pos.1 hsrad
      constructor <;> nlinarith [hsclosed.1, hsclosed.2]
    have htopen : p.2 ∈ Ioo (-1 : ℝ) 1 := by
      have hsq := Real.sqrt_pos.1 htrad
      constructor <;> nlinarith [htclosed.1, htclosed.2]
    have hgeo := intermediate_comparable_chord_bounds hN j k
      hjfirst hjlast hkfirst hklast hcomp hjk hnear hp.1 hp.2 hθ
    have hd : 0 < |(j.val : ℝ) - k.val| /
        bandParameter N := by
      apply div_pos _ hM
      have hℓ : 2 ≤ |(j.val : ℝ) - k.val| := by exact_mod_cast hjk
      linarith
    have hchord : 0 < 2 - 2 * p.1 * p.2 -
        2 * Real.sqrt (1 - p.1 ^ 2) *
          Real.sqrt (1 - p.2 ^ 2) * Real.cos θ := by
      have hδ : 0 <
          (|(j.val : ℝ) - k.val| / (bandParameter N : ℝ)) ^ 2 / 3600 :=
        div_pos (sq_pos_of_pos hd) (by norm_num)
      have hθterm : 0 ≤
          ((population N (j.val + 1) : ℝ) /
            bandParameter N) ^ 2 * θ ^ 2 / 30000 := by positivity
      linarith [hgeo.1]
    exact ⟨hsopen, htopen, hchord⟩
  have hI : ContDiffOn ℝ 4 I W :=
    contDiffOn_intervalIntegral_param_of_contDiffOn 4
      isOpen_nearTailSmoothDomain hF Real.pi_nonneg
  have hG : ContDiffOn ℝ 4 G W := contDiffOn_const.mul hI
  refine ⟨hW, hrect, hG, ?_⟩
  intro s hs t ht
  exact (latitudeKernel_eq_half_profile_integral hα0 s t).symm

/-- The fourth mixed height derivative of the actual smooth angular average
passes under the full half-turn integral on intermediate rectangles. -/
theorem intermediate_mixedFourth_eq_integral {α : ℝ} (hα0 : 0 < α)
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
    (hp : p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1)) :
    mixedFourth
      (fun q : ℝ × ℝ => (1 / Real.pi) *
        ∫ θ in (0 : ℝ)..Real.pi, latitudeProfile α q.1 q.2 θ)
      p.1 p.2 =
      (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi,
        mixedFourth (fun q : ℝ × ℝ =>
          latitudeProfile α q.1 q.2 θ) p.1 p.2 := by
  let W := integralParameterDomain nearTailSmoothDomain 0 Real.pi
  let F : (ℝ × ℝ) × ℝ → ℝ :=
    fun z => latitudeProfile α z.1.1 z.1.2 z.2
  let I : ℝ × ℝ → ℝ := fun q => ∫ θ in (0 : ℝ)..Real.pi, F (q, θ)
  have hsm := intermediate_profile_smooth_extension hα0 hN j k
    hjfirst hjlast hkfirst hklast hcomp hjk hnear
  have hpW : p ∈ W := hsm.2.1 hp
  have hW : IsOpen W := isOpen_integralParameterDomain
    isOpen_nearTailSmoothDomain 0 Real.pi
  have hF : ContDiffOn ℝ 4 F nearTailSmoothDomain :=
    latitudeProfile_joint_contDiffOn α
  have hI : ContDiffOn ℝ 4 I W :=
    contDiffOn_intervalIntegral_param_of_contDiffOn 4
      isOpen_nearTailSmoothDomain hF Real.pi_nonneg
  have hconst := mixedFourth_const_mul_of_C4 hW hI
    (1 / Real.pi) hpW
  have hpass := mixedFourth_intervalIntegral_eq
    isOpen_nearTailSmoothDomain hF Real.pi_nonneg hpW
  calc
    mixedFourth (fun q : ℝ × ℝ => (1 / Real.pi) * I q) p.1 p.2 =
        (1 / Real.pi) * mixedFourth I p.1 p.2 := hconst
    _ = (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi,
          mixedFourth (fun q : ℝ × ℝ =>
            latitudeProfile α q.1 q.2 θ) p.1 p.2 := by
      rw [hpass]

end BEMOC.Definitive
