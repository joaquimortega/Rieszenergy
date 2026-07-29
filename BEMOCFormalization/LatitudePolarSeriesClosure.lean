import BEMOCFormalization.LatitudeExceptionalSeriesClosure
import BEMOCFormalization.LatitudePolarBlocks

/-!
# Endpoint-safe even-series closure for polar latitude blocks

The angular even-power expansion is polynomial in the squared radii.
Consequently its differentiated stages extend continuously to a polar
endpoint even though the square-root height chart itself does not.  This
file supplies the one-sided Peano bridge needed to use that expansion on
literal endpoint bands, then packages the polar comparable and oriented
unequal cases for the global pointwise assembly.
-/

open scoped Topology
open MeasureTheory Set

namespace BEMOC

/-- A degree-one Taylor bound whose derivative chain is stated within the
closed interval.  This endpoint version is the form needed for polar bands. -/
theorem abs_sub_linear_le_of_hasDerivWithinAt_chain
    {f f₁ f₂ : ℝ → ℝ} {a b C x : ℝ}
    (_hab : a ≤ b) (hx : x ∈ Icc a b) (hC : 0 ≤ C)
    (hf : ∀ y ∈ Icc a b, HasDerivWithinAt f (f₁ y) (Icc a b) y)
    (hf₁ : ∀ y ∈ Icc a b, HasDerivWithinAt f₁ (f₂ y) (Icc a b) y)
    (hf₂ : ∀ y ∈ Icc a b, |f₂ y| ≤ C) :
    |f x - f a - (x - a) * f₁ a| ≤ C * (b - a) ^ 2 := by
  rcases eq_or_lt_of_le hx.1 with hxa | hax
  · subst x
    simp
    positivity
  have hxb : x ≤ b := hx.2
  have hI : Icc a x ⊆ Icc a b := by
    intro y hy
    exact ⟨hy.1, hy.2.trans hxb⟩
  have hdiff : DifferentiableOn ℝ f (Icc a x) := by
    intro y hy
    exact (hf y (hI hy)).differentiableWithinAt.mono hI
  have hderiv : ∀ y ∈ Icc a x, derivWithin f (Icc a x) y = f₁ y := by
    intro y hy
    exact ((hf y (hI hy)).mono hI).derivWithin
      ((uniqueDiffOn_Icc hax) y hy)
  have hcont₁ : ContinuousOn f₁ (Icc a x) := by
    intro y hy
    exact (hf₁ y (hI hy)).continuousWithinAt.mono hI
  have hcontDeriv :
      ContinuousOn (derivWithin f (Icc a x)) (Icc a x) :=
    hcont₁.congr fun y hy ↦ hderiv y hy
  have hfC1 : ContDiffOn ℝ 1 f (Icc a x) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hax)]
    refine ⟨hdiff, ?_, ?_⟩
    · simp
    · rwa [contDiffOn_zero]
  have hiter₁ : ∀ y ∈ Icc a x,
      iteratedDerivWithin 1 f (Icc a x) y = f₁ y := by
    intro y hy
    rw [show (1 : ℕ) = 0 + 1 by norm_num,
      iteratedDerivWithin_succ, iteratedDerivWithin_zero]
    exact hderiv y hy
  have hdiff₁ : DifferentiableOn ℝ f₁ (Ioo a x) := by
    intro y hy
    exact (hf₁ y (hI ⟨hy.1.le, hy.2.le⟩)).differentiableWithinAt.mono
      (fun z hz ↦ hI ⟨hz.1.le, hz.2.le⟩)
  have hiterDiff :
      DifferentiableOn ℝ
        (iteratedDerivWithin 1 f (Icc a x)) (Ioo a x) := by
    apply hdiff₁.congr
    intro y hy
    exact hiter₁ y ⟨hy.1.le, hy.2.le⟩
  obtain ⟨y, hy, hrem⟩ :=
    taylor_mean_remainder_lagrange (n := 1) hax hfC1 hiterDiff
  have hyI : y ∈ Icc a x := ⟨hy.1.le, hy.2.le⟩
  have hiter₂ :
      iteratedDerivWithin 2 f (Icc a x) y = f₂ y := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDerivWithin_succ]
    have heq : Set.EqOn
        (iteratedDerivWithin 1 f (Icc a x)) f₁ (Icc a x) :=
      fun z hz ↦ hiter₁ z hz
    rw [derivWithin_congr heq (heq hyI)]
    exact ((hf₁ y (hI hyI)).mono hI).derivWithin
      ((uniqueDiffOn_Icc hax) y hyI)
  have hTaylor :
      taylorWithinEval f 1 (Icc a x) a x =
        f a + (x - a) * f₁ a := by
    rw [show taylorWithinEval f 1 (Icc a x) a x =
      f a + (x - a) * derivWithin f (Icc a x) a by
        simp [taylorWithinEval_succ]]
    rw [hderiv a ⟨le_rfl, hax.le⟩]
  have hyB : |f₂ y| ≤ C := hf₂ y (hI hyI)
  rw [hTaylor, hiter₂] at hrem
  have hwidth : 0 ≤ x - a := sub_nonneg.mpr hax.le
  have hwidthB : x - a ≤ b - a := by linarith
  rw [show f x - f a - (x - a) * f₁ a =
      f x - (f a + (x - a) * f₁ a) by ring,
    hrem, abs_div, abs_mul, abs_pow, abs_of_nonneg hwidth]
  norm_num
  calc
    |f₂ y| * (x - a) ^ 2 / 2 ≤ C * (x - a) ^ 2 := by
      nlinarith [sq_nonneg (x - a)]
    _ ≤ C * (b - a) ^ 2 := by
      gcongr

/-- A derivative chain on the open interval extends to one-sided
derivatives on the closed interval when both stages extend continuously. -/
theorem hasDerivWithinAt_Icc_of_continuous_derivative_extension
    {f f₁ : ℝ → ℝ} {a b x : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b)
    (hf : ContinuousOn f (Icc a b))
    (hf₁ : ContinuousOn f₁ (Icc a b))
    (hderiv : ∀ y ∈ Ioo a b, HasDerivAt f (f₁ y) y) :
    HasDerivWithinAt f (f₁ x) (Icc a b) x := by
  rcases lt_or_eq_of_le hx.1 with hax | hxa
  · rcases lt_or_eq_of_le hx.2 with hxb | hxb
    · exact (hderiv x ⟨hax, hxb⟩).hasDerivWithinAt
    · subst x
      have hdiff : DifferentiableOn ℝ f (Ioo a b) := by
        intro y hy
        exact (hderiv y hy).differentiableAt.differentiableWithinAt
      have hfilter : 𝓝[Iio b] b ≤ 𝓝[Icc a b] b := by
        apply nhdsWithin_le_iff.mpr
        exact Filter.mem_of_superset (Ioo_mem_nhdsLT hab) Ioo_subset_Icc_self
      have htend₁ : Filter.Tendsto f₁ (𝓝[Iio b] b) (𝓝 (f₁ b)) :=
        (hf₁ b ⟨hab.le, le_rfl⟩).tendsto.mono_left hfilter
      have htend :
          Filter.Tendsto (fun y ↦ deriv f y) (𝓝[Iio b] b) (𝓝 (f₁ b)) := by
        apply htend₁.congr'
        filter_upwards [Ioo_mem_nhdsLT hab] with y hy
        exact (hderiv y hy).deriv.symm
      have hleft := hasDerivWithinAt_Iic_of_tendsto_deriv
        hdiff
        ((hf b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self)
        (Ioo_mem_nhdsLT hab) htend
      exact hleft.mono Icc_subset_Iic_self
  · subst x
    have hdiff : DifferentiableOn ℝ f (Ioo a b) := by
      intro y hy
      exact (hderiv y hy).differentiableAt.differentiableWithinAt
    have hfilter : 𝓝[Ioi a] a ≤ 𝓝[Icc a b] a := by
      apply nhdsWithin_le_iff.mpr
      exact Filter.mem_of_superset (Ioo_mem_nhdsGT hab) Ioo_subset_Icc_self
    have htend₁ : Filter.Tendsto f₁ (𝓝[Ioi a] a) (𝓝 (f₁ a)) :=
      (hf₁ a ⟨le_rfl, hab.le⟩).tendsto.mono_left hfilter
    have htend :
        Filter.Tendsto (fun y ↦ deriv f y) (𝓝[Ioi a] a) (𝓝 (f₁ a)) := by
      apply htend₁.congr'
      filter_upwards [Ioo_mem_nhdsGT hab] with y hy
      exact (hderiv y hy).deriv.symm
    have hright := hasDerivWithinAt_Ici_of_tendsto_deriv
      hdiff
      ((hf a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsGT hab) htend
    exact hright.mono Icc_subset_Ici_self

/-! ## The two cross stages of the endpoint tensor expansion -/

/-- Coefficient-weighted mixed `(1,1)` term of the even-power expansion. -/
noncomputable def latitudeEvenPowerDSTSeriesTerm
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  (Ring.choose (α / 2) (2 * m) *
    normalizedCosineMoment (2 * m)) *
    latitudeEvenPowerSummandDST α m s t

/-- The mixed `(1,2)` derivative of one polynomial even-power summand. -/
noncomputable def latitudeEvenPowerSummandDSTT
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  let e := α / 2 - 2 * (m : ℝ)
  let Y :=
    unequalAPowS e s t * unequalRadiusPower m s +
      unequalAPow e s t * unequalRadiusPowerD1 m s
  let YT :=
    unequalAPowST e s t * unequalRadiusPower m s +
      unequalAPowT e s t * unequalRadiusPowerD1 m s
  let YTT :=
    unequalAPowSTT e s t * unequalRadiusPower m s +
      unequalAPowTT e s t * unequalRadiusPowerD1 m s
  (4 : ℝ) ^ m *
    (YTT * unequalRadiusPower m t +
      2 * YT * unequalRadiusPowerD1 m t +
      Y * unequalRadiusPowerD2 m t)

/-- Coefficient-weighted mixed `(1,2)` term. -/
noncomputable def latitudeEvenPowerDSTTSeriesTerm
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  (Ring.choose (α / 2) (2 * m) *
    normalizedCosineMoment (2 * m)) *
    latitudeEvenPowerSummandDSTT α m s t

theorem hasDerivAt_latitudeEvenPowerSummandDS_right_cross
    {α : ℝ} {m : ℕ} {s t : ℝ}
    (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ latitudeEvenPowerSummandDS α m s y)
      (latitudeEvenPowerSummandDST α m s t) t := by
  let e := α / 2 - 2 * (m : ℝ)
  have hps := hasDerivAt_unequalAPowS_right (e := e) hA
  have hp := hasDerivAt_unequalAPow_right (e := e) hA
  have hv := hasDerivAt_unequalRadiusPower m t
  let U := unequalRadiusPower m s
  let U1 := unequalRadiusPowerD1 m s
  have hY :
      HasDerivAt
        (fun y ↦ unequalAPowS e s y * U + unequalAPow e s y * U1)
        (unequalAPowST e s t * U + unequalAPowT e s t * U1) t := by
    exact (hps.mul_const U).add (hp.mul_const U1)
  unfold latitudeEvenPowerSummandDS latitudeEvenPowerSummandDST
  dsimp only
  convert ((hY.mul hv).const_mul ((4 : ℝ) ^ m)) using 1
  funext y
  dsimp [e, U, U1]
  ring

theorem hasDerivAt_latitudeEvenPowerSummandDST_right
    {α : ℝ} {m : ℕ} {s t : ℝ}
    (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ latitudeEvenPowerSummandDST α m s y)
      (latitudeEvenPowerSummandDSTT α m s t) t := by
  let e := α / 2 - 2 * (m : ℝ)
  have hst := hasDerivAt_unequalAPowST_right (e := e) hA
  have ht := hasDerivAt_unequalAPowT_right (e := e) hA
  have hs := hasDerivAt_unequalAPowS_right (e := e) hA
  have h0 := hasDerivAt_unequalAPow_right (e := e) hA
  have hv := hasDerivAt_unequalRadiusPower m t
  have hv1 := hasDerivAt_unequalRadiusPowerD1 m t
  let U := unequalRadiusPower m s
  let U1 := unequalRadiusPowerD1 m s
  have hYT :
      HasDerivAt
        (fun y ↦ unequalAPowST e s y * U + unequalAPowT e s y * U1)
        (unequalAPowSTT e s t * U + unequalAPowTT e s t * U1) t :=
    (hst.mul_const U).add (ht.mul_const U1)
  have hY :
      HasDerivAt
        (fun y ↦ unequalAPowS e s y * U + unequalAPow e s y * U1)
        (unequalAPowST e s t * U + unequalAPowT e s t * U1) t :=
    (hs.mul_const U).add (h0.mul_const U1)
  unfold latitudeEvenPowerSummandDST latitudeEvenPowerSummandDSTT
  dsimp only
  convert
    (((hYT.mul hv).add (hY.mul hv1)).const_mul ((4 : ℝ) ^ m))
      using 1 ; dsimp [e, U, U1] ; ring

/-- Equality of mixed partials for the polynomial even-power summand. -/
theorem latitudeEvenPowerSummandDSTT_eq_DSST_swap
    (α : ℝ) (m : ℕ) (s t : ℝ) :
    latitudeEvenPowerSummandDSTT α m s t =
      latitudeEvenPowerSummandDSST α m t s := by
  unfold latitudeEvenPowerSummandDSTT latitudeEvenPowerSummandDSST
    unequalAPow unequalAPowS unequalAPowT unequalAPowSS
    unequalAPowST unequalAPowTT unequalAPowSST unequalAPowSTT
    unequalRadiusPower unequalRadiusPowerD1 unequalRadiusPowerD2
    angularKernelA
  dsimp only
  ring_nf

/-- The base geometry is invariant under transposition of its rectangle. -/
theorem LatitudeEvenPowerSeriesBaseGeometry.swap
    {N : ℕ} {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L) :
    LatitudeEvenPowerSeriesBaseGeometry N k j L where
  base_pos := hgeo.base_pos
  base_le t ht s hs := by
    have h := hgeo.base_le s hs t ht
    convert h using 1 ; unfold angularKernelA ; ring
  ratio_le t ht s hs := by
    have h := hgeo.ratio_le s hs t ht
    convert h using 1 ; unfold unequalAngularRatio angularKernelA ; ring

/-- Both cross tails are normally summable with the same majorant as the
already constructed lower derivative stages. -/
theorem summable_shifted_latitudeEvenPower_crossSeriesTerms
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    Summable (fun r : ℕ ↦
      latitudeEvenPowerDSTSeriesTerm α (r + 2) s t) ∧
    Summable (fun r : ℕ ↦
      latitudeEvenPowerDSTTSeriesTerm α (r + 2) s t) := by
  let c : ℕ → ℝ := fun m ↦
    Ring.choose (α / 2) (2 * m) * normalizedCosineMoment (2 * m)
  let E : ℕ → ℝ := fun r ↦
    4194304 * angularKernelA s t ^ (α / 2 - 4) *
      (evenAngularDerivativeCoefficient α (r + 2) *
        ((15 : ℝ) / 16) ^ r)
  have hcoef :=
    summable_shifted_evenAngularDerivativeCoefficient_mul_pow
      α (q := (15 : ℝ) / 16) (by norm_num) (by norm_num)
  have hE : Summable E :=
    hcoef.mul_left (4194304 * angularKernelA s t ^ (α / 2 - 4))
  have hbound (F : ℕ → ℝ)
      (hF : ∀ r : ℕ,
        |F r| ≤
          4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
            angularKernelA s t ^ (α / 2 - 4) *
            ((15 : ℝ) / 16) ^ r) :
      Summable (fun r : ℕ ↦ c (r + 2) * F r) := by
    apply hE.of_norm_bounded
    intro r
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |c (r + 2)| * |F r| ≤
          |c (r + 2)| *
            (4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
              angularKernelA s t ^ (α / 2 - 4) *
              ((15 : ℝ) / 16) ^ r) := by
        exact mul_le_mul_of_nonneg_left (hF r) (abs_nonneg _)
      _ = E r := by
        dsimp [c, E, evenAngularDerivativeCoefficient]
        rw [abs_mul]
        ring
  have hdst : Summable (fun r : ℕ ↦
      c (r + 2) * latitudeEvenPowerSummandDST α (r + 2) s t) := by
    apply hbound
    intro r
    have h :=
      (abs_latitudeEvenPower_lowerDerivatives_le_on_leftSmall_rectangle
        hα0 hα2 hN hgeo hs ht (m := r + 2) (by omega)).2.2.2
    simpa [show r + 2 - 2 = r by omega] using h
  have hdstt : Summable (fun r : ℕ ↦
      c (r + 2) * latitudeEvenPowerSummandDSTT α (r + 2) s t) := by
    apply hbound
    intro r
    rw [latitudeEvenPowerSummandDSTT_eq_DSST_swap]
    have h :=
      (abs_latitudeEvenPower_lowerDerivatives_le_on_leftSmall_rectangle
        hα0 hα2 hN hgeo.swap ht hs (m := r + 2) (by omega)).2.2.1
    have hA :
        angularKernelA t s = angularKernelA s t := by
      unfold angularKernelA
      ring
    simpa [show r + 2 - 2 = r by omega, hA] using h
  exact
    ⟨by simpa [latitudeEvenPowerDSTSeriesTerm, c] using hdst,
      by simpa [latitudeEvenPowerDSTTSeriesTerm, c] using hdstt⟩

noncomputable def latitudeEvenPowerDSTSeriesSum
    (α s t : ℝ) : ℝ :=
  latitudeEvenPowerDSTSeriesTerm α 0 s t +
    latitudeEvenPowerDSTSeriesTerm α 1 s t +
    ∑' r : ℕ, latitudeEvenPowerDSTSeriesTerm α (r + 2) s t

noncomputable def latitudeEvenPowerDSTTSeriesSum
    (α s t : ℝ) : ℝ :=
  latitudeEvenPowerDSTTSeriesTerm α 0 s t +
    latitudeEvenPowerDSTTSeriesTerm α 1 s t +
    ∑' r : ℕ, latitudeEvenPowerDSTTSeriesTerm α (r + 2) s t

theorem norm_latitudeEvenPower_crossTailStages_le_majorant
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (r : ℕ) :
    ‖latitudeEvenPowerDSTSeriesTerm α (r + 2) s t‖ ≤
        leftSmallLatitudeTailMajorant α L r ∧
    ‖latitudeEvenPowerDSTTSeriesTerm α (r + 2) s t‖ ≤
        leftSmallLatitudeTailMajorant α L r := by
  have hLA : L ≤ angularKernelA s t := hgeo.base_le s hs t ht
  have hγ : α / 2 - 4 ≤ 0 := by linarith
  have hpow :
      angularKernelA s t ^ (α / 2 - 4) ≤ L ^ (α / 2 - 4) :=
    Real.rpow_le_rpow_of_nonpos hgeo.base_pos hLA hγ
  have hdst :=
    (abs_latitudeEvenPower_lowerDerivatives_le_on_leftSmall_rectangle
      hα0 hα2 hN hgeo hs ht (m := r + 2) (by omega)).2.2.2
  have hdstt :=
    (abs_latitudeEvenPower_lowerDerivatives_le_on_leftSmall_rectangle
      hα0 hα2 hN hgeo.swap ht hs (m := r + 2) (by omega)).2.2.1
  rw [show r + 2 - 2 = r by omega] at hdst hdstt
  let c : ℝ :=
    Ring.choose (α / 2) (2 * (r + 2)) *
      normalizedCosineMoment (2 * (r + 2))
  have hstage (F : ℝ)
      (hF : |F| ≤
        4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
          angularKernelA s t ^ (α / 2 - 4) *
          ((15 : ℝ) / 16) ^ r) :
      ‖c * F‖ ≤ leftSmallLatitudeTailMajorant α L r := by
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |c| * |F| ≤
          |c| *
            (4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
              angularKernelA s t ^ (α / 2 - 4) *
              ((15 : ℝ) / 16) ^ r) :=
        mul_le_mul_of_nonneg_left hF (abs_nonneg _)
      _ ≤ |c| *
            (4194304 * (((r + 2 : ℕ) : ℝ) + 1) ^ (4 : ℕ) *
              L ^ (α / 2 - 4) *
              ((15 : ℝ) / 16) ^ r) := by
        gcongr
      _ = leftSmallLatitudeTailMajorant α L r := by
        dsimp [c, leftSmallLatitudeTailMajorant,
          evenAngularDerivativeCoefficient]
        rw [abs_mul]
        ring
  constructor
  · simpa [latitudeEvenPowerDSTSeriesTerm, c] using hstage _ hdst
  · rw [latitudeEvenPowerDSTTSeriesTerm,
      latitudeEvenPowerSummandDSTT_eq_DSST_swap]
    have hA : angularKernelA t s = angularKernelA s t := by
      unfold angularKernelA
      ring
    exact hstage _ (by simpa [hA] using hdstt)

/-- The shifted first cross series differentiates normally on the open
right-band interior. -/
theorem hasDerivAt_shifted_latitudeEvenPowerDSSeries_right_cross
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivAt
      (fun y ↦ ∑' r : ℕ,
        latitudeEvenPowerDSSeriesTerm α (r + 2) s y)
      (∑' r : ℕ,
        latitudeEvenPowerDSTSeriesTerm α (r + 2) s t) t := by
  apply hasDerivAt_tsum_of_isPreconnected
    (u := leftSmallLatitudeTailMajorant α L)
    (t := Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (g := fun r y ↦ latitudeEvenPowerDSSeriesTerm α (r + 2) s y)
    (g' := fun r y ↦ latitudeEvenPowerDSTSeriesTerm α (r + 2) s y)
    (y₀ := t)
  · exact summable_leftSmallLatitudeTailMajorant α L
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro r y hy
    have hy' := show y ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k) from ⟨hy.1.le, hy.2.le⟩
    have hA : 0 < angularKernelA s y :=
      hgeo.base_pos.trans_le (hgeo.base_le s hs y hy')
    simpa [latitudeEvenPowerDSSeriesTerm,
      latitudeEvenPowerDSTSeriesTerm] using
      (hasDerivAt_latitudeEvenPowerSummandDS_right_cross
        (α := α) (m := r + 2) hA).const_mul
          (Ring.choose (α / 2) (2 * (r + 2)) *
            normalizedCosineMoment (2 * (r + 2)))
  · intro r y hy
    exact (norm_latitudeEvenPower_crossTailStages_le_majorant
      hα0 hα2 hN hgeo hs ⟨hy.1.le, hy.2.le⟩ r).1
  · exact ht
  · exact
      (summable_shifted_latitudeEvenPower_lowerSeriesTerms
        hα0 hα2 hN hgeo hs ⟨ht.1.le, ht.2.le⟩).1
  · exact ht

theorem hasDerivAt_shifted_latitudeEvenPowerDSTSeries_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivAt
      (fun y ↦ ∑' r : ℕ,
        latitudeEvenPowerDSTSeriesTerm α (r + 2) s y)
      (∑' r : ℕ,
        latitudeEvenPowerDSTTSeriesTerm α (r + 2) s t) t := by
  apply hasDerivAt_tsum_of_isPreconnected
    (u := leftSmallLatitudeTailMajorant α L)
    (t := Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (g := fun r y ↦ latitudeEvenPowerDSTSeriesTerm α (r + 2) s y)
    (g' := fun r y ↦ latitudeEvenPowerDSTTSeriesTerm α (r + 2) s y)
    (y₀ := t)
  · exact summable_leftSmallLatitudeTailMajorant α L
  · exact isOpen_Ioo
  · exact isPreconnected_Ioo
  · intro r y hy
    have hy' := show y ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k) from ⟨hy.1.le, hy.2.le⟩
    have hA : 0 < angularKernelA s y :=
      hgeo.base_pos.trans_le (hgeo.base_le s hs y hy')
    simpa [latitudeEvenPowerDSTSeriesTerm,
      latitudeEvenPowerDSTTSeriesTerm] using
      (hasDerivAt_latitudeEvenPowerSummandDST_right
        (α := α) (m := r + 2) hA).const_mul
          (Ring.choose (α / 2) (2 * (r + 2)) *
            normalizedCosineMoment (2 * (r + 2)))
  · intro r y hy
    exact (norm_latitudeEvenPower_crossTailStages_le_majorant
      hα0 hα2 hN hgeo hs ⟨hy.1.le, hy.2.le⟩ r).2
  · exact ht
  · exact
      (summable_shifted_latitudeEvenPower_crossSeriesTerms
        hα0 hα2 hN hgeo hs ⟨ht.1.le, ht.2.le⟩).1
  · exact ht

end BEMOC
