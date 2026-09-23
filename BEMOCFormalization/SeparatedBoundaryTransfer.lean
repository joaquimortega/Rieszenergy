import BEMOCFormalization.SeparatedSmoothExtension

open Filter Set
open scoped Topology
namespace BEMOC.Definitive

/-- The mixed fourth derivative of a `C⁴` extension is continuous on its open domain. -/
theorem continuousOn_mixedFourth_of_contDiffOn
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W) :
    ContinuousOn (fun p : ℝ × ℝ => mixedFourth G p.1 p.2) W := by
  have hsecond : ContDiffOn ℝ 2 (partialSecondTwice G) W :=
    contDiffOn_partialSecondTwice hW hG
  have hthird : ContDiffOn ℝ 1 (partialFirst (partialSecondTwice G)) W :=
    contDiffOn_partialFirst_of_succ hW hsecond (by decide)
  have hfourth : ContDiffOn ℝ 0
      (partialFirst (partialFirst (partialSecondTwice G))) W :=
    contDiffOn_partialFirst_of_succ hW hthird (by decide)
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => partialFirstTwice (partialSecondTwice G) p) W := by
    simpa only [partialFirstTwice] using hfourth.continuousOn
  apply hcont.congr
  intro p hp
  simpa only [Prod.mk.eta] using
    (mixedFourth_eq_partialFirstTwice_partialSecondTwice
      hW hG p.1 p.2 hp)

/-- Radial contraction keeps a physical height strictly inside the polar interval. -/
private theorem contracted_height_mem_open (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    (1 - 1 / ((n : ℝ) + 1)) * x ∈ Ioo (-1 : ℝ) 1 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hd0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hd1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ hn).2
    norm_num
  have hc0 : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by linarith
  have hc1 : 1 - 1 / ((n : ℝ) + 1) < 1 := by linarith
  have hlo := mul_nonneg hc0 (show 0 ≤ x + 1 by linarith [hx.1])
  have hhi := mul_nonneg hc0 (show 0 ≤ 1 - x by linarith [hx.2])
  constructor <;> nlinarith

private theorem tendsto_contracted_height (x : ℝ) :
    Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 1)) * x)
      atTop (𝓝 x) := by
  have hc : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat)
  simpa only [one_mul] using hc.mul_const x

private theorem continuousAt_separatedRatio_of_mem_open
    {p : ℝ × ℝ} (hp : p ∈ separatedOpen) :
    ContinuousAt (fun x : ℝ × ℝ => separatedRatio x.1 x.2) p := by
  have hnum : ContinuousAt (fun x : ℝ × ℝ =>
      4 * (1 - x.1 ^ 2) * (1 - x.2 ^ 2)) p := by fun_prop
  have hden : ContinuousAt (fun x : ℝ × ℝ =>
      (2 - 2 * x.1 * x.2) ^ 2) p := by fun_prop
  change ContinuousAt (fun x : ℝ × ℝ =>
    4 * (1 - x.1 ^ 2) * (1 - x.2 ^ 2) /
      (2 - 2 * x.1 * x.2) ^ 2) p
  exact hnum.div hden (pow_ne_zero 2 hp.1.ne')

/-- An interior mixed-fourth estimate extends to the polar boundary with ratio slack. -/
theorem separatedSmoothExtension_boundary_transfer
    {α q q' C : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hqq' : q < q')
    (hinterior : ∀ s ∈ Ioo (-1 : ℝ) 1, ∀ t ∈ Ioo (-1 : ℝ) 1,
      (s, t) ∈ separatedOpen → separatedRatio s t ≤ q' →
      |mixedFourth (separatedSmoothExtension α) s t| ≤
        C * (2 - 2 * s * t) ^ (α / 2 - 4))
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hp : (s, t) ∈ separatedOpen)
    (hq : separatedRatio s t ≤ q) :
    |mixedFourth (separatedSmoothExtension α) s t| ≤
      C * (2 - 2 * s * t) ^ (α / 2 - 4) := by
  let c : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  let p : ℕ → ℝ × ℝ := fun n => (c n * s, c n * t)
  have hptend : Tendsto p atTop (𝓝 (s, t)) := by
    exact (tendsto_contracted_height s).prodMk_nhds
      (tendsto_contracted_height t)
  have hopen : ∀ᶠ n : ℕ in atTop, p n ∈ separatedOpen :=
    hptend.eventually (isOpen_separatedOpen.mem_nhds hp)
  have hratlim : Tendsto (fun n => separatedRatio (p n).1 (p n).2)
      atTop (𝓝 (separatedRatio s t)) :=
    (continuousAt_separatedRatio_of_mem_open hp).tendsto.comp hptend
  have hq' : separatedRatio s t < q' := lt_of_le_of_lt hq hqq'
  have hratio : ∀ᶠ n : ℕ in atTop,
      separatedRatio (p n).1 (p n).2 ≤ q' :=
    (hratlim.eventually (Iio_mem_nhds hq')).mono (fun _ hn => hn.le)
  have hle : ∀ᶠ n : ℕ in atTop,
      |mixedFourth (separatedSmoothExtension α) (p n).1 (p n).2| ≤
        C * (2 - 2 * (p n).1 * (p n).2) ^ (α / 2 - 4) := by
    filter_upwards [hopen, hratio] with n hnopen hnratio
    exact hinterior (p n).1
      (contracted_height_mem_open n hs)
      (p n).2 (contracted_height_mem_open n ht)
      hnopen hnratio
  have hG : ContDiffOn ℝ 4 (separatedSmoothExtension α) separatedOpen :=
    separatedSmoothExtension_contDiffOn hα0 hα2
  have hfourthCont : ContinuousAt
      (fun x : ℝ × ℝ =>
        |mixedFourth (separatedSmoothExtension α) x.1 x.2|) (s, t) :=
    (continuousOn_mixedFourth_of_contDiffOn isOpen_separatedOpen hG).continuousAt
      (isOpen_separatedOpen.mem_nhds hp) |>.abs
  have hUcont : ContinuousAt
      (fun x : ℝ × ℝ => 2 - 2 * x.1 * x.2) (s, t) := by fun_prop
  have hUne : 2 - 2 * s * t ≠ 0 := by
    simpa only [angularKernelA] using hp.1.ne'
  have hpowCont : ContinuousAt
      (fun x : ℝ × ℝ => (2 - 2 * x.1 * x.2) ^ (α / 2 - 4)) (s, t) :=
    (Real.continuousAt_rpow_const (2 - 2 * s * t) (α / 2 - 4)
      (Or.inl hUne)).comp_of_eq hUcont rfl
  have hrightCont : ContinuousAt
      (fun x : ℝ × ℝ => C * (2 - 2 * x.1 * x.2) ^ (α / 2 - 4))
      (s, t) := continuousAt_const.mul hpowCont
  exact le_of_tendsto_of_tendsto
    (hfourthCont.tendsto.comp hptend)
    (hrightCont.tendsto.comp hptend) hle

/-- The physical angular ratio bound controls the polynomial even-series ratio. -/
theorem separatedRatio_le_of_angular_gap {s t : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hU : 0 < 2 - 2 * s * t)
    (hV : 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) ≤
      (1 - (1 / 256 : ℝ)) * (2 - 2 * s * t)) :
    separatedRatio s t ≤ (255 / 256 : ℝ) ^ 2 := by
  have has : 0 ≤ 1 - s ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2)
      (show 0 ≤ 1 + s by linarith [hs.1])]
  have hat : 0 ≤ 1 - t ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2)
      (show 0 ≤ 1 + t by linarith [ht.1])]
  have hV0 : 0 ≤ 2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) := by
    positivity
  have hV2 :
      (2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 =
        4 * (1 - s ^ 2) * (1 - t ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt has, Real.sq_sqrt hat]
    ring
  have hsq : 4 * (1 - s ^ 2) * (1 - t ^ 2) ≤
      (255 / 256 : ℝ) ^ 2 * (2 - 2 * s * t) ^ 2 := by
    rw [← hV2]
    nlinarith [hV]
  unfold separatedRatio
  exact (div_le_iff₀ (sq_pos_of_pos hU)).2 hsq

end BEMOC.Definitive
