import BEMOCFormalization.ComparableNearBlocks
import BEMOCFormalization.PolarDerivatives

open Set
namespace BEMOC.Definitive

def polarPositiveSet (θ : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < polarChordSquare p.1 p.2 θ}

theorem isOpen_polarPositiveSet (θ : ℝ) : IsOpen (polarPositiveSet θ) := by
  unfold polarPositiveSet
  have hc : Continuous (fun p : ℝ × ℝ => polarChordSquare p.1 p.2 θ) := by
    unfold polarChordSquare
    fun_prop
  exact isOpen_Ioi.preimage hc

theorem polarKernel_contDiffOn_positive (α θ : ℝ) :
    ContDiffOn ℝ 4 (fun p : ℝ × ℝ => polarKernel α θ p.1 p.2)
      (polarPositiveSet θ) := by
  intro p hp
  exact (polarKernel_contDiffAt_of_chord_pos hp).contDiffWithinAt


/-- Local polar C4 regularity supplies every profile hypothesis of the height chain. -/
theorem polar_height_chain_regular
    {α θ s t : ℝ}
    (hU : 0 < polarChordSquare (Real.arccos s) (Real.arccos t) θ) :
    ∃ V : Set ℝ, IsOpen V ∧ Real.arccos s ∈ V ∧
      (∀ u∈V, ContDiffAt ℝ 2
        (fun v => polarKernel α θ u v) (Real.arccos t)) ∧
      ContDiffAt ℝ 2
        (fun u => iteratedDeriv 2 (fun v => polarKernel α θ u v)
          (Real.arccos t)) (Real.arccos s) ∧
      ContDiffAt ℝ 2
        (fun u => deriv (fun v => polarKernel α θ u v)
          (Real.arccos t)) (Real.arccos s) := by
  let φ := Real.arccos s
  let ψ := Real.arccos t
  let W := polarPositiveSet θ
  let V : Set ℝ := {u | (u,ψ)∈W}
  have hW : IsOpen W := isOpen_polarPositiveSet θ
  have hp : (φ,ψ)∈W := hU
  have hVo : IsOpen V := hW.preimage (by fun_prop : Continuous (fun u : ℝ => (u,ψ)))
  have hG : ContDiffOn ℝ 4
      (fun p : ℝ×ℝ => polarKernel α θ p.1 p.2) W :=
    polarKernel_contDiffOn_positive α θ
  refine ⟨V, hVo, hp, ?_, ?_, ?_⟩
  · intro u hu
    have hmap : ContDiffAt ℝ 4 (fun v : ℝ => (u,v)) ψ := by fun_prop
    have h4 : ContDiffAt ℝ 4 (fun v => polarKernel α θ u v) ψ :=
      (hG.contDiffAt (hW.mem_nhds hu)).comp ψ hmap
    exact h4.of_le (by decide)
  · simpa only using (contDiffAt_vertical_second_profile hW hG hp)
  · simpa only using (contDiffAt_vertical_first_profile hW hG hp)


theorem abs_polar_height_mixedFourth_le
    {α θ s t ρ L : ℝ} {V : Set ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hρ : 0 < ρ) (hL : 1 ≤ L)
    (ha : ρ ≤ Real.sqrt (1-s^2))
    (hb : ρ ≤ Real.sqrt (1-t^2))
    (hV : IsOpen V) (hφV : Real.arccos s ∈ V)
    (hvertical : ∀ u ∈ V,
      ContDiffAt ℝ 2 (fun v => polarKernel α θ u v) (Real.arccos t))
    (hA : ContDiffAt ℝ 2
      (fun u => iteratedDeriv 2 (fun v => polarKernel α θ u v) (Real.arccos t))
      (Real.arccos s))
    (hB : ContDiffAt ℝ 2
      (fun u => deriv (fun v => polarKernel α θ u v) (Real.arccos t))
      (Real.arccos s))
    (C : ℝ) (hC : 0 < C)
    (hderiv : ∀ m n : ℕ, m + n ≤ 4 → ∀ θ φ ψ : ℝ,
      0 < 2 - 2 * (Real.cos φ * Real.cos ψ +
        Real.sin φ * Real.sin ψ * Real.cos θ) →
      |iteratedDeriv m (fun u => iteratedDeriv n
        (fun v => polarKernel α θ u v) ψ) φ| ≤
        C * (2 - 2 * (Real.cos φ * Real.cos ψ +
          Real.sin φ * Real.sin ψ * Real.cos θ)) ^ ((α-m-n)/2))
    (hU : 0 < 2 - 2 * (Real.cos (Real.arccos s) * Real.cos (Real.arccos t) +
      Real.sin (Real.arccos s) * Real.sin (Real.arccos t) * Real.cos θ))
    (hUmax : 2 - 2 * (Real.cos (Real.arccos s) * Real.cos (Real.arccos t) +
      Real.sin (Real.arccos s) * Real.sin (Real.arccos t) * Real.cos θ) ≤
      (L*ρ)^2) :
    |mixedFourth (fun p : ℝ × ℝ => polarKernel α θ
        (Real.arccos p.1) (Real.arccos p.2)) s t| ≤
      C * (1+2*L+L^2) *
        (2 - 2 * (Real.cos (Real.arccos s) * Real.cos (Real.arccos t) +
          Real.sin (Real.arccos s) * Real.sin (Real.arccos t) * Real.cos θ)) ^
          ((α-4)/2) / ρ^4 := by
  let φ := Real.arccos s
  let ψ := Real.arccos t
  let U := 2 - 2 * (Real.cos φ * Real.cos ψ +
    Real.sin φ * Real.sin ψ * Real.cos θ)
  let E := U ^ ((α-4)/2)
  let P : ℝ → ℝ → ℝ := fun u v => polarKernel α θ u v
  let X22 := iteratedDeriv 2 (fun u => iteratedDeriv 2 (P u) ψ) φ
  let X12 := deriv (fun u => iteratedDeriv 2 (P u) ψ) φ
  let X21 := iteratedDeriv 2 (fun u => deriv (P u) ψ) φ
  let X11 := deriv (fun u => deriv (P u) ψ) φ
  have hE : 0 ≤ E := Real.rpow_nonneg hU.le _
  have hsabs : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have htabs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h22 : |X22| ≤ C*E := by
    have h := hderiv 2 2 (by norm_num) θ φ ψ hU
    have heq : (α - (2:ℝ) - 2) / 2 = (α-4)/2 := by ring
    change |X22| ≤ C * U ^ ((α - (2:ℝ) - 2) / 2) at h
    rw [heq] at h
    exact h
  have h12 : |X12| ≤ C*L*ρ*E := by
    have h := hderiv 1 2 (by norm_num) θ φ ψ hU
    have hstep := polar_power_step_one (α:=α) hU hρ (by linarith : 0 ≤ L) hUmax
    simp only [iteratedDeriv_one] at h
    norm_num at h
    have h' : |X12| ≤ C * U ^ ((α-3)/2) := by
      have heq : (α - (1:ℝ) - 2) / 2 = (α-3)/2 := by ring
      change |X12| ≤ C * U ^ ((α - (1:ℝ) - 2) / 2) at h
      rw [heq] at h
      exact h
    calc
      _ ≤ C * U ^ ((α-3)/2) := h'
      _ ≤ C * ((L*ρ)*E) := by gcongr
      _ = C*L*ρ*E := by ring
  have h21 : |X21| ≤ C*L*ρ*E := by
    have h := hderiv 2 1 (by norm_num) θ φ ψ hU
    have hstep := polar_power_step_one (α:=α) hU hρ (by linarith : 0 ≤ L) hUmax
    simp only [iteratedDeriv_one] at h
    norm_num at h
    have h' : |X21| ≤ C * U ^ ((α-3)/2) := by
      have heq : (α - (2:ℝ) - 1) / 2 = (α-3)/2 := by ring
      change |X21| ≤ C * U ^ ((α - (2:ℝ) - 1) / 2) at h
      rw [heq] at h
      exact h
    calc
      _ ≤ C * U ^ ((α-3)/2) := h'
      _ ≤ C * ((L*ρ)*E) := by gcongr
      _ = C*L*ρ*E := by ring
  have h11 : |X11| ≤ C*L^2*ρ^2*E := by
    have h := hderiv 1 1 (by norm_num) θ φ ψ hU
    have hstep := polar_power_step_two (α:=α) hU hρ (by linarith : 0 ≤ L) hUmax
    simp only [iteratedDeriv_one] at h
    norm_num at h
    have h' : |X11| ≤ C * U ^ ((α-2)/2) := by
      have heq : (α - (1:ℝ) - 1) / 2 = (α-2)/2 := by ring
      change |X11| ≤ C * U ^ ((α - (1:ℝ) - 1) / 2) at h
      rw [heq] at h
      exact h
    calc
      _ ≤ C * U ^ ((α-2)/2) := h'
      _ ≤ C * ((L*ρ)^2*E) := by gcongr
      _ = C*L^2*ρ^2*E := by ring
  have hchain := mixedFourth_arccos_chain hs ht hV hφV hvertical hA hB
  rw [hchain]
  have hnum := abs_four_term_chain_le hρ ha hb hC.le hL hE
    hsabs htabs h22 h12 h21 h11
  simpa only [P, X22, X12, X21, X11, E, U, φ, ψ] using hnum

/-- The quantitative height derivative bound with local regularity discharged by positive chord. -/
theorem abs_polar_height_mixedFourth_le_of_positive
    {α θ s t ρ L : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hρ : 0 < ρ) (hL : 1 ≤ L)
    (ha : ρ ≤ Real.sqrt (1-s^2))
    (hb : ρ ≤ Real.sqrt (1-t^2))
    (C : ℝ) (hC : 0 < C)
    (hderiv : ∀ m n : ℕ, m + n ≤ 4 → ∀ θ φ ψ : ℝ,
      0 < 2 - 2 * (Real.cos φ * Real.cos ψ +
        Real.sin φ * Real.sin ψ * Real.cos θ) →
      |iteratedDeriv m (fun u => iteratedDeriv n
        (fun v => polarKernel α θ u v) ψ) φ| ≤
        C * (2 - 2 * (Real.cos φ * Real.cos ψ +
          Real.sin φ * Real.sin ψ * Real.cos θ)) ^ ((α-m-n)/2))
    (hU : 0 < 2 - 2 * (Real.cos (Real.arccos s) * Real.cos (Real.arccos t) +
      Real.sin (Real.arccos s) * Real.sin (Real.arccos t) * Real.cos θ))
    (hUmax : 2 - 2 * (Real.cos (Real.arccos s) * Real.cos (Real.arccos t) +
      Real.sin (Real.arccos s) * Real.sin (Real.arccos t) * Real.cos θ) ≤
      (L*ρ)^2) :
    |mixedFourth (fun p : ℝ × ℝ => polarKernel α θ
        (Real.arccos p.1) (Real.arccos p.2)) s t| ≤
      C * (1+2*L+L^2) *
        (2 - 2 * (Real.cos (Real.arccos s) * Real.cos (Real.arccos t) +
          Real.sin (Real.arccos s) * Real.sin (Real.arccos t) * Real.cos θ)) ^
          ((α-4)/2) / ρ^4 := by
  have hU' : 0 < polarChordSquare (Real.arccos s) (Real.arccos t) θ := hU
  obtain ⟨V, hV, hφV, hvertical, hA, hB⟩ :=
    polar_height_chain_regular (α:=α) hU'
  exact abs_polar_height_mixedFourth_le hs ht hρ hL ha hb hV hφV
    hvertical hA hB C hC hderiv hU hUmax


/-- Local equality transfers the mixed derivative between height kernels. -/
theorem mixedFourth_congr_of_rect_eqOn
    {F G : ℝ × ℝ → ℝ} {U V : Set ℝ} {s t : ℝ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hs : s ∈ U) (ht : t ∈ V)
    (hEq : ∀ u ∈ U, ∀ v ∈ V, F (u,v) = G (u,v)) :
    mixedFourth F s t = mixedFourth G s t := by
  have hinner : ∀ u ∈ U,
      iteratedDeriv 2 (fun v => F (u,v)) t =
        iteratedDeriv 2 (fun v => G (u,v)) t := by
    intro u hu
    apply Filter.EventuallyEq.iteratedDeriv_eq 2
    filter_upwards [hV.mem_nhds ht] with v hv
    exact hEq u hu v hv
  apply Filter.EventuallyEq.iteratedDeriv_eq 2
  filter_upwards [hU.mem_nhds hs] with u hu
  exact hinner u hu

theorem latitudeProfile_eq_polarKernel_arccos
    (α θ : ℝ) {s t : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    latitudeProfile α s t θ =
      polarKernel α θ (Real.arccos s) (Real.arccos t) := by
  unfold latitudeProfile polarKernel
  rw [Real.cos_arccos hs.1 hs.2, Real.cos_arccos ht.1 ht.2,
    Real.sin_arccos, Real.sin_arccos]
  ring

theorem mixedFourth_latitudeProfile_eq_polar
    (α θ : ℝ) {s t : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1) :
    mixedFourth (fun p : ℝ × ℝ => latitudeProfile α p.1 p.2 θ) s t =
      mixedFourth (fun p : ℝ × ℝ => polarKernel α θ
        (Real.arccos p.1) (Real.arccos p.2)) s t := by
  apply mixedFourth_congr_of_rect_eqOn isOpen_Ioo isOpen_Ioo hs ht
  intro u hu v hv
  exact latitudeProfile_eq_polarKernel_arccos α θ
    ⟨hu.1.le, hu.2.le⟩ ⟨hv.1.le, hv.2.le⟩


/-- Physical height kernel fourth derivative bounded by the polar jet table. -/
theorem abs_latitudeProfile_mixedFourth_le_of_positive
    {α θ s t ρ L : ℝ}
    (hs : s ∈ Ioo (-1 : ℝ) 1) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hρ : 0 < ρ) (hL : 1 ≤ L)
    (ha : ρ ≤ Real.sqrt (1-s^2))
    (hb : ρ ≤ Real.sqrt (1-t^2))
    (C : ℝ) (hC : 0 < C)
    (hderiv : ∀ m n : ℕ, m + n ≤ 4 → ∀ θ φ ψ : ℝ,
      0 < 2 - 2 * (Real.cos φ * Real.cos ψ +
        Real.sin φ * Real.sin ψ * Real.cos θ) →
      |iteratedDeriv m (fun u => iteratedDeriv n
        (fun v => polarKernel α θ u v) ψ) φ| ≤
        C * (2 - 2 * (Real.cos φ * Real.cos ψ +
          Real.sin φ * Real.sin ψ * Real.cos θ)) ^ ((α-m-n)/2))
    (hU : 0 < 2 - 2 * (Real.cos (Real.arccos s) * Real.cos (Real.arccos t) +
      Real.sin (Real.arccos s) * Real.sin (Real.arccos t) * Real.cos θ))
    (hUmax : 2 - 2 * (Real.cos (Real.arccos s) * Real.cos (Real.arccos t) +
      Real.sin (Real.arccos s) * Real.sin (Real.arccos t) * Real.cos θ) ≤
      (L*ρ)^2) :
    |mixedFourth (fun p : ℝ × ℝ => latitudeProfile α p.1 p.2 θ) s t| ≤
      C * (1+2*L+L^2) *
        (2 - 2 * (Real.cos (Real.arccos s) * Real.cos (Real.arccos t) +
          Real.sin (Real.arccos s) * Real.sin (Real.arccos t) * Real.cos θ)) ^
          ((α-4)/2) / ρ^4 := by
  rw [mixedFourth_latitudeProfile_eq_polar α θ hs ht]
  exact abs_polar_height_mixedFourth_le_of_positive hs ht hρ hL ha hb
    C hC hderiv hU hUmax


/-- Near-band pointwise fourth derivative in terms of the positive squared chord. -/
theorem near_tail_profile_chord_bound
    {α : ℝ} (C : ℝ) (hC : 0 < C)
    (hderiv : ∀ m n : ℕ, m + n ≤ 4 → ∀ θ φ ψ : ℝ,
      0 < 2 - 2 * (Real.cos φ * Real.cos ψ +
        Real.sin φ * Real.sin ψ * Real.cos θ) →
      |iteratedDeriv m (fun u => iteratedDeriv n
        (fun v => polarKernel α θ u v) ψ) φ| ≤
        C * (2 - 2 * (Real.cos φ * Real.cos ψ +
          Real.sin φ * Real.sin ψ * Real.cos θ)) ^ ((α-m-n)/2))
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
        (nearTailChord (s,t) θ)^((α-4)/2) /
          ((population N (j.val + 1) : ℝ)/(240*bandParameter N))^4 := by
  let rj : ℝ := population N (j.val + 1)
  let M : ℝ := bandParameter N
  let ρ : ℝ := rj/(240*M)
  have hN4 : 4 ≤ N := by omega
  have hM16 := bandParameter_ge_sixteen_of_ge_1024 hN
  have hjindex : j.val + 1 < 2 * bandParameter N := by
    have hv := j.isLt
    omega
  have hkindex : k.val + 1 < 2 * bandParameter N := by
    have hv := k.isLt
    omega
  have hrj : 0 < rj := by
    dsimp [rj]
    exact_mod_cast population_pos hN4 (by omega : 1 ≤ j.val + 1) hjindex
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast bandParameter_pos hN4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hsint := nonpolar_band_height_interior hN j hjfirst hjlast hs
  have htint := nonpolar_band_height_interior hN k hkfirst hklast ht
  have ha : ρ ≤ Real.sqrt (1-s^2) := by
    have hrad := (band_radius_comparison hN4 hM16 j
      (by omega) hjlast hs).1
    calc
      ρ ≤ (1/30:ℝ)*rj/M := by
        have hnon : 0 ≤ (1/30:ℝ)*rj/M := by positivity
        calc
          ρ = (1/8:ℝ)*((1/30)*rj/M) := by dsimp [ρ]; ring
          _ ≤ 1*((1/30)*rj/M) :=
            mul_le_mul_of_nonneg_right (by norm_num) hnon
          _ = (1/30)*rj/M := by ring
      _ ≤ Real.sqrt (1-s^2) := hrad
  have hb : ρ ≤ Real.sqrt (1-t^2) := by
    have hrad := (band_radius_comparison hN4 hM16 k
      (by omega) hklast ht).1
    have hcomp' : rj/8 ≤ (population N (k.val + 1) : ℝ) := hcomp.1
    calc
      ρ = (rj/8)/(30*M) := by dsimp [ρ]; ring
      _ ≤ (population N (k.val+1):ℝ)/(30*M) := by gcongr
      _ = (1/30:ℝ) * population N (k.val+1) / M := by ring
      _ ≤ Real.sqrt (1-t^2) := hrad
  have hsunit : s∈Icc (-1:ℝ) 1 := ⟨hsint.1.le,hsint.2.le⟩
  have htunit : t∈Icc (-1:ℝ) 1 := ⟨htint.1.le,htint.2.le⟩
  have hchordEq := polarChordSquare_arccos (θ:=θ) hsunit htunit
  have hU : 0 < 2 - 2 * (Real.cos (Real.arccos s) * Real.cos (Real.arccos t) +
      Real.sin (Real.arccos s) * Real.sin (Real.arccos t) * Real.cos θ) := by
    rw [← polarChordSquare]
    rw [hchordEq]
    exact near_band_tail_chord_pos hN j k hjfirst hjlast hkfirst hklast
      hcomp hs ht hθ
  have hUupper := near_band_chord_upper_full hN j k hjfirst hjlast
    hkfirst hklast hcomp hnear hs ht ⟨(inv_pos.mpr hrj).le.trans hθ.1, hθ.2⟩
  have hUmax : 2 - 2 * (Real.cos (Real.arccos s) * Real.cos (Real.arccos t) +
      Real.sin (Real.arccos s) * Real.sin (Real.arccos t) * Real.cos θ) ≤
      ((12000:ℝ)*ρ)^2 := by
    rw [← polarChordSquare, hchordEq]
    calc
      _ ≤ (50*rj/M)^2 := hUupper
      _ = ((12000:ℝ)*ρ)^2 := by dsimp [ρ]; ring
  have hbound := abs_latitudeProfile_mixedFourth_le_of_positive
    hsint htint hρ (by norm_num : (1:ℝ)≤12000) ha hb
    C hC hderiv hU hUmax
  have hUeq : 2 - 2 * (Real.cos (Real.arccos s) * Real.cos (Real.arccos t) +
      Real.sin (Real.arccos s) * Real.sin (Real.arccos t) * Real.cos θ) =
      nearTailChord (s,t) θ := by
    simpa only [polarChordSquare, nearTailChord] using hchordEq
  rw [hUeq] at hbound
  exact hbound


/-- Negative power of a positive chord controlled by a quadratic model. -/
theorem inverse_chord_power_le
    {α U D : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hU : 0 < U) (hD : 0 < D)
    (hlower : D^2 / 28800 ≤ U) :
    U ^ ((α-4)/2) ≤ (28800:ℝ)^2 * D^(α-4) := by
  have he : (α-4)/2 ≤ 0 := by linarith
  have hbase : 0 < D^2 / 28800 := by positivity
  have hpow := Real.rpow_le_rpow_of_nonpos hbase hlower he
  have hsplit : (D^2 / (28800:ℝ)) ^ ((α-4)/2) =
      D^(α-4) * (28800:ℝ)^((4-α)/2) := by
    rw [Real.div_rpow (sq_nonneg _) (by norm_num : (0:ℝ)≤28800),
      ← Real.rpow_natCast D 2]
    rw [← Real.rpow_mul (by positivity : 0 ≤ D)]
    have hmul : (2:ℝ) * ((α-4)/2) = α-4 := by ring
    rw [show (↑(2:ℕ):ℝ) = 2 by norm_num, hmul,
      div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0:ℝ)≤28800)]
    congr 1
    ring
  have hconst' : (28800:ℝ)^((4-α)/2) ≤ (28800:ℝ)^(2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (x := (28800:ℝ))
      (y := (4-α)/2) (z := 2) (by norm_num) (by linarith)
  have hconst : (28800:ℝ)^((4-α)/2) ≤ (28800:ℝ)^2 := by
    simpa only [show (28800:ℝ) ^ (2:ℝ) = (28800:ℝ)^2 by
      simpa using (Real.rpow_natCast (28800:ℝ) 2)] using hconst'
  calc
    _ ≤ (D^2/(28800:ℝ))^((α-4)/2) := hpow
    _ = D^(α-4) * (28800:ℝ)^((4-α)/2) := hsplit
    _ ≤ D^(α-4) * (28800:ℝ)^2 :=
      mul_le_mul_of_nonneg_left hconst (Real.rpow_nonneg hD.le _)
    _ = (28800:ℝ)^2 * D^(α-4) := by ring


end BEMOC.Definitive
