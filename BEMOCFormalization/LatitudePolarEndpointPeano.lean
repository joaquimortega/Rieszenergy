import BEMOCFormalization.LatitudePolarSeriesClosure

/-!
# Endpoint Peano transfer for the polar even-power series

This module keeps the already audited series construction frozen and
builds the closed-rectangle Taylor remainder from its public derivative
stages.
-/

open scoped Topology
open MeasureTheory Set

namespace BEMOC

theorem hasDerivAt_latitudeEvenPowerDSSeriesSum_right_cross
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivAt (fun y ↦ latitudeEvenPowerDSSeriesSum α s y)
      (latitudeEvenPowerDSTSeriesSum α s t) t := by
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le
      (hgeo.base_le s hs t ⟨ht.1.le, ht.2.le⟩)
  have h0 :=
    (hasDerivAt_latitudeEvenPowerSummandDS_right_cross
      (α := α) (m := 0) hA).const_mul
        (Ring.choose (α / 2) 0 * normalizedCosineMoment 0)
  have h1 :=
    (hasDerivAt_latitudeEvenPowerSummandDS_right_cross
      (α := α) (m := 1) hA).const_mul
        (Ring.choose (α / 2) 2 * normalizedCosineMoment 2)
  have htail :=
    hasDerivAt_shifted_latitudeEvenPowerDSSeries_right_cross
      hα0 hα2 hN hgeo hs ht
  simpa [latitudeEvenPowerDSSeriesSum, latitudeEvenPowerDSTSeriesSum,
    latitudeEvenPowerDSSeriesTerm, latitudeEvenPowerDSTSeriesTerm] using
      (h0.add h1).add htail

theorem hasDerivAt_latitudeEvenPowerDSTSeriesSum_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Ioo (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivAt (fun y ↦ latitudeEvenPowerDSTSeriesSum α s y)
      (latitudeEvenPowerDSTTSeriesSum α s t) t := by
  have hA : 0 < angularKernelA s t :=
    hgeo.base_pos.trans_le
      (hgeo.base_le s hs t ⟨ht.1.le, ht.2.le⟩)
  have h0 :=
    (hasDerivAt_latitudeEvenPowerSummandDST_right
      (α := α) (m := 0) hA).const_mul
        (Ring.choose (α / 2) 0 * normalizedCosineMoment 0)
  have h1 :=
    (hasDerivAt_latitudeEvenPowerSummandDST_right
      (α := α) (m := 1) hA).const_mul
        (Ring.choose (α / 2) 2 * normalizedCosineMoment 2)
  have htail :=
    hasDerivAt_shifted_latitudeEvenPowerDSTSeries_right
      hα0 hα2 hN hgeo hs ht
  simpa [latitudeEvenPowerDSTSeriesSum, latitudeEvenPowerDSTTSeriesSum,
    latitudeEvenPowerDSTSeriesTerm, latitudeEvenPowerDSTTSeriesTerm] using
      (h0.add h1).add htail

/-- The `(1,2)` full series is the transposed `(2,1)` full series. -/
theorem latitudeEvenPowerDSTTSeriesSum_eq_DSSTSeriesSum_swap
    (α s t : ℝ) :
    latitudeEvenPowerDSTTSeriesSum α s t =
      latitudeEvenPowerDSSTSeriesSum α t s := by
  unfold latitudeEvenPowerDSTTSeriesSum latitudeEvenPowerDSSTSeriesSum
    latitudeEvenPowerDSTTSeriesTerm latitudeEvenPowerDSSTSeriesTerm
  simp_rw [latitudeEvenPowerSummandDSTT_eq_DSST_swap]

theorem latitudeEvenPowerSeriesSum_comm (α s t : ℝ) :
    latitudeEvenPowerSeriesSum α s t =
      latitudeEvenPowerSeriesSum α t s := by
  have hterm (m : ℕ) :
      latitudeEvenPowerSeriesTerm α m s t =
        latitudeEvenPowerSeriesTerm α m t s := by
    unfold latitudeEvenPowerSeriesTerm latitudeEvenPowerSummand
    have hA : angularKernelA s t = angularKernelA t s := by
      unfold angularKernelA
      ring
    rw [hA]
    ring
  unfold latitudeEvenPowerSeriesSum
  rw [hterm 0, hterm 1]
  congr 2
  funext r
  exact hterm (r + 2)

theorem continuousOn_latitudeEvenPower_crossSeriesSums_uncurry
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L) :
    let S :=
      Icc (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k)
    ContinuousOn
        (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSTSeriesSum α p.1 p.2) S ∧
      ContinuousOn
        (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSTTSeriesSum α p.1 p.2) S := by
  dsimp only
  let S :=
    Icc (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) ×ˢ
      Icc (bandBoundaryHeight N (k + 1)) (bandBoundaryHeight N k)
  have hterm (m : ℕ) :
      ContinuousOn
          (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSTSeriesTerm α m p.1 p.2) S := by
    intro p hp
    have hA : 0 < angularKernelA p.1 p.2 :=
      hgeo.base_pos.trans_le (hgeo.base_le p.1 hp.1 p.2 hp.2)
    have hAc :
        ContinuousAt (fun q : ℝ × ℝ ↦ angularKernelA q.1 q.2) p := by
      unfold angularKernelA
      fun_prop
    have hpow (z : ℝ) :
        ContinuousAt (fun q : ℝ × ℝ ↦ angularKernelA q.1 q.2 ^ z) p :=
      hAc.rpow_const (Or.inl hA.ne')
    unfold latitudeEvenPowerDSTSeriesTerm latitudeEvenPowerSummandDST
      unequalAPow unequalAPowS unequalAPowT unequalAPowST
      unequalRadiusPower unequalRadiusPowerD1
    dsimp only
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have htail :
      ContinuousOn
        (fun p : ℝ × ℝ ↦ ∑' r : ℕ,
          latitudeEvenPowerDSTSeriesTerm α (r + 2) p.1 p.2) S := by
    apply continuousOn_tsum
      (fun r ↦ hterm (r + 2))
      (summable_leftSmallLatitudeTailMajorant α L)
    intro r p hp
    exact (norm_latitudeEvenPower_crossTailStages_le_majorant
      hα0 hα2 hN hgeo hp.1 hp.2 r).1
  have hdst : ContinuousOn
      (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSTSeriesSum α p.1 p.2) S := by
    unfold latitudeEvenPowerDSTSeriesSum
    exact ((hterm 0).add (hterm 1)).add htail
  have hterm2 (m : ℕ) :
      ContinuousOn
          (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSTTSeriesTerm α m p.1 p.2) S := by
    intro p hp
    have hA : 0 < angularKernelA p.1 p.2 :=
      hgeo.base_pos.trans_le (hgeo.base_le p.1 hp.1 p.2 hp.2)
    have hAc :
        ContinuousAt (fun q : ℝ × ℝ ↦ angularKernelA q.1 q.2) p := by
      unfold angularKernelA
      fun_prop
    have hpow (z : ℝ) :
        ContinuousAt (fun q : ℝ × ℝ ↦ angularKernelA q.1 q.2 ^ z) p :=
      hAc.rpow_const (Or.inl hA.ne')
    unfold latitudeEvenPowerDSTTSeriesTerm latitudeEvenPowerSummandDSTT
      unequalAPow unequalAPowS unequalAPowT unequalAPowST
      unequalAPowTT unequalAPowSTT
      unequalRadiusPower unequalRadiusPowerD1 unequalRadiusPowerD2
    dsimp only
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have htail2 :
      ContinuousOn
        (fun p : ℝ × ℝ ↦ ∑' r : ℕ,
          latitudeEvenPowerDSTTSeriesTerm α (r + 2) p.1 p.2) S := by
    apply continuousOn_tsum
      (fun r ↦ hterm2 (r + 2))
      (summable_leftSmallLatitudeTailMajorant α L)
    intro r p hp
    exact (norm_latitudeEvenPower_crossTailStages_le_majorant
      hα0 hα2 hN hgeo hp.1 hp.2 r).2
  have hdstt : ContinuousOn
      (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSTTSeriesSum α p.1 p.2) S := by
    unfold latitudeEvenPowerDSTTSeriesSum
    exact ((hterm2 0).add (hterm2 1)).add htail2
  exact ⟨hdst, hdstt⟩

theorem hasDerivWithinAt_latitudeEvenPowerSeriesSum_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivWithinAt (fun y ↦ latitudeEvenPowerSeriesSum α s y)
      (latitudeEvenPowerDSSeriesSum α t s)
      (Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)) t := by
  let Is := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  have hklt :
      bandBoundaryHeight N (k + 1) < bandBoundaryHeight N k := by
    have hw : 0 < bandWidth N k := by
      rw [bandWidth_eq_population]
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hkpopNat : 0 < finiteBandPopulation N k := by
        have h := three_mul_latitudeBandScale_le_population hM k
        have hd := latitudeBandScale_pos N k
        omega
      have hkpop : (0 : ℝ) < finiteBandPopulation N k := by
        exact_mod_cast hkpopNat
      positivity
    unfold bandWidth at hw
    linarith
  have hlo :=
    continuousOn_latitudeEvenPower_lowerSeriesSums_uncurry
      hα0 hα2 hN hgeo
  have hK : ContinuousOn
      (fun y ↦ latitudeEvenPowerSeriesSum α s y) It := by
    simpa [Is, It, Function.comp_def] using
      hlo.1.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy ↦ ⟨hs, hy⟩)
  have hDs : ContinuousOn
      (fun y ↦ latitudeEvenPowerDSSeriesSum α y s) It := by
    have hswap :=
      continuousOn_latitudeEvenPower_lowerSeriesSums_uncurry
        hα0 hα2 hN hgeo.swap
    simpa [Is, It, Function.comp_def] using
      hswap.2.1.comp (continuousOn_id.prodMk continuousOn_const)
        (fun y hy ↦ ⟨hy, hs⟩)
  apply hasDerivWithinAt_Icc_of_continuous_derivative_extension
    hklt ht hK hDs
  intro y hy
  have h :=
    hasDerivAt_latitudeEvenPowerSeriesSum_left
      hα0 hα2 hN hgeo.swap hy hs
  convert h using 1
  funext z
  exact latitudeEvenPowerSeriesSum_comm α s z

theorem hasDerivWithinAt_latitudeEvenPowerDSSeriesSum_right_cross
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivWithinAt (fun y ↦ latitudeEvenPowerDSSeriesSum α s y)
      (latitudeEvenPowerDSTSeriesSum α s t)
      (Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)) t := by
  let Is := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  have hklt :
      bandBoundaryHeight N (k + 1) < bandBoundaryHeight N k := by
    have hw : 0 < bandWidth N k := by
      rw [bandWidth_eq_population]
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hkpopNat : 0 < finiteBandPopulation N k := by
        have h := three_mul_latitudeBandScale_le_population hM k
        have hd := latitudeBandScale_pos N k
        omega
      have hkpop : (0 : ℝ) < finiteBandPopulation N k := by
        exact_mod_cast hkpopNat
      positivity
    unfold bandWidth at hw
    linarith
  have hlo :=
    continuousOn_latitudeEvenPower_lowerSeriesSums_uncurry
      hα0 hα2 hN hgeo
  have hcross :=
    continuousOn_latitudeEvenPower_crossSeriesSums_uncurry
      hα0 hα2 hN hgeo
  have hDs : ContinuousOn
      (fun y ↦ latitudeEvenPowerDSSeriesSum α s y) It := by
    simpa [Is, It, Function.comp_def] using
      hlo.2.1.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy ↦ ⟨hs, hy⟩)
  have hDst : ContinuousOn
      (fun y ↦ latitudeEvenPowerDSTSeriesSum α s y) It := by
    simpa [Is, It, Function.comp_def] using
      hcross.1.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy ↦ ⟨hs, hy⟩)
  apply hasDerivWithinAt_Icc_of_continuous_derivative_extension
    hklt ht hDs hDst
  intro y hy
  exact hasDerivAt_latitudeEvenPowerDSSeriesSum_right_cross
    hα0 hα2 hN hgeo hs hy

theorem hasDerivWithinAt_latitudeEvenPowerDSTSeriesSum_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivWithinAt (fun y ↦ latitudeEvenPowerDSTSeriesSum α s y)
      (latitudeEvenPowerDSTTSeriesSum α s t)
      (Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)) t := by
  let Is := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  have hklt :
      bandBoundaryHeight N (k + 1) < bandBoundaryHeight N k := by
    have hw : 0 < bandWidth N k := by
      rw [bandWidth_eq_population]
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hkpopNat : 0 < finiteBandPopulation N k := by
        have h := three_mul_latitudeBandScale_le_population hM k
        have hd := latitudeBandScale_pos N k
        omega
      have hkpop : (0 : ℝ) < finiteBandPopulation N k := by
        exact_mod_cast hkpopNat
      positivity
    unfold bandWidth at hw
    linarith
  have hcross :=
    continuousOn_latitudeEvenPower_crossSeriesSums_uncurry
      hα0 hα2 hN hgeo
  have hDst : ContinuousOn
      (fun y ↦ latitudeEvenPowerDSTSeriesSum α s y) It := by
    simpa [Is, It, Function.comp_def] using
      hcross.1.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy ↦ ⟨hs, hy⟩)
  have hDstt : ContinuousOn
      (fun y ↦ latitudeEvenPowerDSTTSeriesSum α s y) It := by
    simpa [Is, It, Function.comp_def] using
      hcross.2.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy ↦ ⟨hs, hy⟩)
  apply hasDerivWithinAt_Icc_of_continuous_derivative_extension
    hklt ht hDst hDstt
  intro y hy
  exact hasDerivAt_latitudeEvenPowerDSTSeriesSum_right
    hα0 hα2 hN hgeo hs hy

noncomputable def polarSeriesFirstTaylorError
    (α a s t : ℝ) : ℝ :=
  latitudeEvenPowerSeriesSum α s t -
    latitudeEvenPowerSeriesSum α a t -
      (s - a) * latitudeEvenPowerDSSeriesSum α a t

noncomputable def polarSeriesFirstTaylorErrorDt
    (α a s t : ℝ) : ℝ :=
  latitudeEvenPowerDSSeriesSum α t s -
    latitudeEvenPowerDSSeriesSum α t a -
      (s - a) * latitudeEvenPowerDSTSeriesSum α a t

noncomputable def polarSeriesFirstTaylorErrorDtt
    (α a s t : ℝ) : ℝ :=
  latitudeEvenPowerDSSSeriesSum α t s -
    latitudeEvenPowerDSSSeriesSum α t a -
      (s - a) * latitudeEvenPowerDSTTSeriesSum α a t

noncomputable def polarSeriesExplicitMixedRemainder
    (α a c s t : ℝ) : ℝ :=
  polarSeriesFirstTaylorError α a s t -
    polarSeriesFirstTaylorError α a s c -
      (t - c) * polarSeriesFirstTaylorErrorDt α a s c

theorem polarSeriesExplicitMixedRemainder_decomposition
    (α a c s t : ℝ) :
    latitudeEvenPowerSeriesSum α s t =
      polarSeriesExplicitMixedRemainder α a c s t +
        (polarSeriesFirstTaylorErrorDt α a s c * t +
          (polarSeriesFirstTaylorError α a s c -
            c * polarSeriesFirstTaylorErrorDt α a s c)) +
        (latitudeEvenPowerDSSeriesSum α a t * s +
          (latitudeEvenPowerSeriesSum α a t -
            a * latitudeEvenPowerDSSeriesSum α a t)) := by
  unfold polarSeriesExplicitMixedRemainder polarSeriesFirstTaylorError
  ring

theorem hasDerivWithinAt_latitudeEvenPowerDSSeriesSum_left
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivWithinAt (fun y ↦ latitudeEvenPowerDSSeriesSum α y t)
      (latitudeEvenPowerDSSSeriesSum α s t)
      (Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j)) s := by
  let Is := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  have hjlt :
      bandBoundaryHeight N (j + 1) < bandBoundaryHeight N j := by
    have hjpopNat : 0 < finiteBandPopulation N j := by
      have h := three_mul_latitudeBandScale_le_population hM j
      have hd := latitudeBandScale_pos N j
      omega
    have hw : 0 < bandWidth N j := by
      rw [bandWidth_eq_population]
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hjpop : (0 : ℝ) < finiteBandPopulation N j := by
        exact_mod_cast hjpopNat
      positivity
    unfold bandWidth at hw
    linarith
  have hlo :=
    continuousOn_latitudeEvenPower_lowerSeriesSums_uncurry
      hα0 hα2 hN hgeo
  have hDs : ContinuousOn
      (fun y ↦ latitudeEvenPowerDSSeriesSum α y t) Is := by
    simpa [Is, It, Function.comp_def] using
      hlo.2.1.comp (continuousOn_id.prodMk continuousOn_const)
        (fun y hy ↦ ⟨hy, ht⟩)
  have hDss : ContinuousOn
      (fun y ↦ latitudeEvenPowerDSSSeriesSum α y t) Is := by
    simpa [Is, It, Function.comp_def] using
      hlo.2.2.1.comp (continuousOn_id.prodMk continuousOn_const)
        (fun y hy ↦ ⟨hy, ht⟩)
  apply hasDerivWithinAt_Icc_of_continuous_derivative_extension
    hjlt hs hDs hDss
  intro y hy
  exact hasDerivAt_latitudeEvenPowerDSSeriesSum_left
    hα0 hα2 hN hgeo hy ht

theorem hasDerivWithinAt_latitudeEvenPowerDSSSeriesSum_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivWithinAt (fun y ↦ latitudeEvenPowerDSSSeriesSum α s y)
      (latitudeEvenPowerDSSTSeriesSum α s t)
      (Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)) t := by
  let Is := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  have hklt :
      bandBoundaryHeight N (k + 1) < bandBoundaryHeight N k := by
    have hkpopNat : 0 < finiteBandPopulation N k := by
      have h := three_mul_latitudeBandScale_le_population hM k
      have hd := latitudeBandScale_pos N k
      omega
    have hw : 0 < bandWidth N k := by
      rw [bandWidth_eq_population]
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hkpop : (0 : ℝ) < finiteBandPopulation N k := by
        exact_mod_cast hkpopNat
      positivity
    unfold bandWidth at hw
    linarith
  have hlo :=
    continuousOn_latitudeEvenPower_lowerSeriesSums_uncurry
      hα0 hα2 hN hgeo
  have hDss : ContinuousOn
      (fun y ↦ latitudeEvenPowerDSSSeriesSum α s y) It := by
    simpa [Is, It, Function.comp_def] using
      hlo.2.2.1.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy ↦ ⟨hs, hy⟩)
  have hDsst : ContinuousOn
      (fun y ↦ latitudeEvenPowerDSSTSeriesSum α s y) It := by
    simpa [Is, It, Function.comp_def] using
      hlo.2.2.2.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy ↦ ⟨hs, hy⟩)
  apply hasDerivWithinAt_Icc_of_continuous_derivative_extension
    hklt ht hDss hDsst
  intro y hy
  exact hasDerivAt_latitudeEvenPowerDSSSeriesSum_right
    hα0 hα2 hN hgeo hs hy

theorem hasDerivWithinAt_latitudeEvenPowerDSSTSeriesSum_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivWithinAt (fun y ↦ latitudeEvenPowerDSSTSeriesSum α s y)
      (latitudeEvenPowerDSSTTSeriesSum α s t)
      (Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)) t := by
  let Is := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  have hklt :
      bandBoundaryHeight N (k + 1) < bandBoundaryHeight N k := by
    have hkpopNat : 0 < finiteBandPopulation N k := by
      have h := three_mul_latitudeBandScale_le_population hM k
      have hd := latitudeBandScale_pos N k
      omega
    have hw : 0 < bandWidth N k := by
      rw [bandWidth_eq_population]
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hkpop : (0 : ℝ) < finiteBandPopulation N k := by
        exact_mod_cast hkpopNat
      positivity
    unfold bandWidth at hw
    linarith
  have hlo :=
    continuousOn_latitudeEvenPower_lowerSeriesSums_uncurry
      hα0 hα2 hN hgeo
  have hfour :=
    continuousOn_latitudeEvenPowerDSSTTSeriesSum_uncurry
      hα0 hα2 hN hgeo
  have hDsst : ContinuousOn
      (fun y ↦ latitudeEvenPowerDSSTSeriesSum α s y) It := by
    simpa [Is, It, Function.comp_def] using
      hlo.2.2.2.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy ↦ ⟨hs, hy⟩)
  have hDsstt : ContinuousOn
      (fun y ↦ latitudeEvenPowerDSSTTSeriesSum α s y) It := by
    simpa [Is, It, Function.comp_def] using
      hfour.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y hy ↦ ⟨hs, hy⟩)
  apply hasDerivWithinAt_Icc_of_continuous_derivative_extension
    hklt ht hDsst hDsstt
  intro y hy
  exact hasDerivAt_latitudeEvenPowerDSSTSeriesSum_right
    hα0 hα2 hN hgeo hs hy

theorem hasDerivWithinAt_polarSeriesFirstTaylorError_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {a s t : ℝ}
    (ha : a ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivWithinAt
      (fun y ↦ polarSeriesFirstTaylorError α a s y)
      (polarSeriesFirstTaylorErrorDt α a s t)
      (Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)) t := by
  have hK :=
    hasDerivWithinAt_latitudeEvenPowerSeriesSum_right
      hα0 hα2 hN hM hgeo hs ht
  have hKa :=
    hasDerivWithinAt_latitudeEvenPowerSeriesSum_right
      hα0 hα2 hN hM hgeo ha ht
  have hDs :=
    hasDerivWithinAt_latitudeEvenPowerDSSeriesSum_right_cross
      hα0 hα2 hN hM hgeo ha ht
  unfold polarSeriesFirstTaylorError polarSeriesFirstTaylorErrorDt
  convert (hK.sub hKa).sub
    (hDs.const_mul (s - a)) using 1

theorem hasDerivWithinAt_polarSeriesFirstTaylorErrorDt_right
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    {a s t : ℝ}
    (ha : a ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    HasDerivWithinAt
      (fun y ↦ polarSeriesFirstTaylorErrorDt α a s y)
      (polarSeriesFirstTaylorErrorDtt α a s t)
      (Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)) t := by
  have hDss :=
    hasDerivWithinAt_latitudeEvenPowerDSSeriesSum_left
      hα0 hα2 hN hM hgeo.swap ht hs
  have hDssa :=
    hasDerivWithinAt_latitudeEvenPowerDSSeriesSum_left
      hα0 hα2 hN hM hgeo.swap ht ha
  have hDst :=
    hasDerivWithinAt_latitudeEvenPowerDSTSeriesSum_right
      hα0 hα2 hN hM hgeo ha ht
  unfold polarSeriesFirstTaylorErrorDt polarSeriesFirstTaylorErrorDtt
  convert (hDss.sub hDssa).sub
    (hDst.const_mul (s - a)) using 1

/-- Endpoint-safe tensor Taylor bound for the complete even-power series. -/
theorem abs_polarSeriesExplicitMixedRemainder_le
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)} {L C : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    (hC : 0 ≤ C)
    (hmixed : ∀ x ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ y ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
      |latitudeEvenPowerDSSTTSeriesSum α y x| ≤ C)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |polarSeriesExplicitMixedRemainder α
        (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N (k + 1)) s t| ≤
      C * bandWidth N j ^ 2 * bandWidth N k ^ 2 := by
  let a := bandBoundaryHeight N (j + 1)
  let b := bandBoundaryHeight N j
  let c := bandBoundaryHeight N (k + 1)
  let d := bandBoundaryHeight N k
  have hab : a ≤ b := bandBoundaryHeight_succ_le j
  have hcd : c ≤ d := bandBoundaryHeight_succ_le k
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hc : c ∈ Icc c d := ⟨le_rfl, hcd⟩
  have hinner (y : ℝ) (hy : y ∈ Icc c d) :
      |polarSeriesFirstTaylorErrorDtt α a s y| ≤
        C * (b - a) ^ 2 := by
    have hchain := abs_sub_linear_le_of_hasDerivWithinAt_chain
      (f := fun x ↦ latitudeEvenPowerDSSSeriesSum α y x)
      (f₁ := fun x ↦ latitudeEvenPowerDSSTSeriesSum α y x)
      (f₂ := fun x ↦ latitudeEvenPowerDSSTTSeriesSum α y x)
      hab hs hC
      (fun x hx ↦
        hasDerivWithinAt_latitudeEvenPowerDSSSeriesSum_right
          hα0 hα2 hN hM hgeo.swap hy hx)
      (fun x hx ↦
        hasDerivWithinAt_latitudeEvenPowerDSSTSeriesSum_right
          hα0 hα2 hN hM hgeo.swap hy hx)
      (fun x hx ↦ hmixed x hx y hy)
    unfold polarSeriesFirstTaylorErrorDtt
    rw [latitudeEvenPowerDSTTSeriesSum_eq_DSSTSeriesSum_swap]
    exact hchain
  have houter := abs_sub_linear_le_of_hasDerivWithinAt_chain
    (f := fun y ↦ polarSeriesFirstTaylorError α a s y)
    (f₁ := fun y ↦ polarSeriesFirstTaylorErrorDt α a s y)
    (f₂ := fun y ↦ polarSeriesFirstTaylorErrorDtt α a s y)
    hcd ht (mul_nonneg hC (sq_nonneg _))
    (fun y hy ↦
      hasDerivWithinAt_polarSeriesFirstTaylorError_right
        hα0 hα2 hN hM hgeo ha hs hy)
    (fun y hy ↦
      hasDerivWithinAt_polarSeriesFirstTaylorErrorDt_right
        hα0 hα2 hN hM hgeo ha hs hy)
    hinner
  dsimp [a, b, c, d] at houter ⊢
  simpa [bandWidth] using houter

set_option maxHeartbeats 800000 in
theorem continuousOn_polarSeriesExplicitMixedRemainder
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)} {L : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦
        polarSeriesExplicitMixedRemainder α
          (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N (k + 1)) p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
  let Is := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  let a := bandBoundaryHeight N (j + 1)
  let c := bandBoundaryHeight N (k + 1)
  have ha : a ∈ Is := ⟨le_rfl, bandBoundaryHeight_succ_le j⟩
  have hc : c ∈ It := ⟨le_rfl, bandBoundaryHeight_succ_le k⟩
  have hlo :=
    continuousOn_latitudeEvenPower_lowerSeriesSums_uncurry
      hα0 hα2 hN hgeo
  have hK := hlo.1
  have hDs := hlo.2.1
  have hKst : ContinuousOn
      (fun p : ℝ × ℝ ↦ latitudeEvenPowerSeriesSum α p.1 p.2)
      (Is ×ˢ It) := by simpa [Is, It] using hK
  have hmapAT : ContinuousOn (fun p : ℝ × ℝ ↦ (a, p.2))
      (Is ×ˢ It) := continuousOn_const.prodMk continuousOn_snd
  have hmapSC : ContinuousOn (fun p : ℝ × ℝ ↦ (p.1, c))
      (Is ×ˢ It) := continuousOn_fst.prodMk continuousOn_const
  have hmapCS : ContinuousOn (fun p : ℝ × ℝ ↦ (c, p.1))
      (Is ×ˢ It) := continuousOn_const.prodMk continuousOn_fst
  have hKat : ContinuousOn
      (fun p : ℝ × ℝ ↦ latitudeEvenPowerSeriesSum α a p.2)
      (Is ×ˢ It) := by
    simpa [Is, It, Function.comp_def] using
      hK.comp hmapAT
        (fun (p : ℝ × ℝ) hp ↦ ⟨ha, hp.2⟩)
  have hKsc : ContinuousOn
      (fun p : ℝ × ℝ ↦ latitudeEvenPowerSeriesSum α p.1 c)
      (Is ×ˢ It) := by
    simpa [Is, It, Function.comp_def] using
      hK.comp hmapSC
        (fun (p : ℝ × ℝ) hp ↦ ⟨hp.1, hc⟩)
  have hDsat : ContinuousOn
      (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSSeriesSum α a p.2)
      (Is ×ˢ It) := by
    simpa [Is, It, Function.comp_def] using
      hDs.comp hmapAT
        (fun (p : ℝ × ℝ) hp ↦ ⟨ha, hp.2⟩)
  have hDscs : ContinuousOn
      (fun p : ℝ × ℝ ↦ latitudeEvenPowerDSSeriesSum α c p.1)
      (Is ×ˢ It) := by
    have hswap :=
      continuousOn_latitudeEvenPower_lowerSeriesSums_uncurry
        hα0 hα2 hN hgeo.swap
    simpa [Is, It, Function.comp_def] using
      hswap.2.1.comp hmapCS
        (fun (p : ℝ × ℝ) hp ↦ ⟨hc, hp.1⟩)
  unfold polarSeriesExplicitMixedRemainder
    polarSeriesFirstTaylorError polarSeriesFirstTaylorErrorDt
  dsimp [a, c] at *
  fun_prop

set_option maxHeartbeats 800000 in
/-- Concrete polar endpoint Peano transfer.  The only analytic premise is
the endpoint-safe `(2,2)` even-series bound on the transposed rectangle. -/
theorem abs_latitudeKernel_bandPairError_le_of_evenSeriesDsstt
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1)) {L C : ℝ}
    (hgeo : LatitudeEvenPowerSeriesBaseGeometry N j k L)
    (hC : 0 ≤ C)
    (hmixed : ∀ x ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ y ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
      |latitudeEvenPowerDSSTTSeriesSum α y x| ≤ C) :
    |bandPairError N j k (latitudeKernel α)| ≤
      64 * C * (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  let Is := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  let a := bandBoundaryHeight N (j + 1)
  let c := bandBoundaryHeight N (k + 1)
  let R : ℝ → ℝ → ℝ := fun s t ↦
    polarSeriesExplicitMixedRemainder α a c s t
  have hcontR : ContinuousOn (fun p : ℝ × ℝ ↦ R p.1 p.2)
      (Is ×ˢ It) := by
    simpa [Is, It, a, c, R] using
      continuousOn_polarSeriesExplicitMixedRemainder
        hα0 hα2 hN hgeo
  let fR : C(Is ×ˢ It, ℝ) :=
    ⟨fun p ↦ R p.1.1 p.1.2,
      continuousOn_iff_continuous_restrict.mp hcontR⟩
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq
    (isClosed_Icc.prod isClosed_Icc) fR
  have hGeq : ∀ p ∈ Is ×ˢ It, G p = R p.1 p.2 := by
    intro p hp
    exact DFunLike.congr_fun hG (⟨p, hp⟩ : Is ×ˢ It)
  let uRight : ℝ → ℝ := fun s ↦
    polarSeriesFirstTaylorErrorDt α a s c
  let vRight : ℝ → ℝ := fun s ↦
    polarSeriesFirstTaylorError α a s c -
      c * polarSeriesFirstTaylorErrorDt α a s c
  let uLeft : ℝ → ℝ := fun t ↦
    latitudeEvenPowerDSSeriesSum α a t
  let vLeft : ℝ → ℝ := fun t ↦
    latitudeEvenPowerSeriesSum α a t -
      a * latitudeEvenPowerDSSeriesSum α a t
  let Kext : ℝ → ℝ → ℝ := fun s t ↦
    G (s, t) + (uRight s * t + vRight s) +
      (uLeft t * s + vLeft t)
  have hpair :
      bandPairError N j k (latitudeKernel α) =
        bandPairError N j k Kext := by
    apply bandPairError_congr_on_literalRectangle j k
    intro s hs t ht
    rw [latitudeKernel_eq_latitudeEvenPowerSeriesSum hN hgeo hs ht]
    rw [polarSeriesExplicitMixedRemainder_decomposition]
    have hGR : G (s, t) = R s t := hGeq (s, t) ⟨hs, ht⟩
    dsimp [Kext, uRight, vRight, uLeft, vLeft, R]
    rw [hGR]
  rw [hpair]
  apply abs_bandPairError_le_of_biaffine_mixed_remainder hN j k
    Kext (fun s t ↦ G (s, t)) uRight vRight uLeft vLeft C hC
  · intro s
    exact (G.continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (continuous_bandError_right k G.continuous).intervalIntegrable _ _
  · have hlo :=
      continuousOn_latitudeEvenPower_lowerSeriesSums_uncurry
        hα0 hα2 hN hgeo
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (bandBoundaryHeight_succ_le k)]
    have hU : ContinuousOn
        (fun t ↦ latitudeEvenPowerDSSeriesSum α
          (bandBoundaryHeight N (j + 1)) t)
        (Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
      simpa only [Function.comp_apply] using
        hlo.2.1.comp (continuousOn_const.prodMk continuousOn_id)
          (fun t ht ↦
            ⟨⟨le_rfl, bandBoundaryHeight_succ_le j⟩, ht⟩)
    exact hU
  · have hlo :=
      continuousOn_latitudeEvenPower_lowerSeriesSums_uncurry
        hα0 hα2 hN hgeo
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (bandBoundaryHeight_succ_le k)]
    have hK : ContinuousOn
        (fun t ↦ latitudeEvenPowerSeriesSum α
          (bandBoundaryHeight N (j + 1)) t)
        (Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
      simpa only [Function.comp_apply] using
        hlo.1.comp (continuousOn_const.prodMk continuousOn_id)
          (fun t ht ↦
            ⟨⟨le_rfl, bandBoundaryHeight_succ_le j⟩, ht⟩)
    have hDs : ContinuousOn
        (fun t ↦ latitudeEvenPowerDSSeriesSum α
          (bandBoundaryHeight N (j + 1)) t)
        (Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
      simpa only [Function.comp_apply] using
        hlo.2.1.comp (continuousOn_const.prodMk continuousOn_id)
          (fun t ht ↦
            ⟨⟨le_rfl, bandBoundaryHeight_succ_le j⟩, ht⟩)
    exact hK.sub (continuousOn_const.mul hDs)
  · intro s t
    rfl
  · intro s hs t ht
    have hGR : G (s, t) = R s t := hGeq (s, t) ⟨hs, ht⟩
    rw [hGR]
    exact abs_polarSeriesExplicitMixedRemainder_le
      hα0 hα2 hN hM hgeo hC hmixed hs ht

end BEMOC
