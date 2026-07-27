import BEMOCFormalization.LatitudeUnequalGeometry
import BEMOCFormalization.LatitudeUnequalSeries

/-!
# Individual even-power summands on unequal latitude rectangles

This file applies the endpoint-safe monomial majorant to the actual
summands in (5.6).  It also records the required smoothness of each
individual summand on the open region `A>0`.
-/

open Set

namespace BEMOC

/-- The `m`th even-power summand before the binomial and angular-moment
coefficients are inserted. -/
noncomputable def latitudeEvenPowerSummand
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  angularKernelA s t ^ (α / 2 - 2 * (m : ℝ)) *
    (4 : ℝ) ^ m * (1 - s ^ 2) ^ m * (1 - t ^ 2) ^ m

/-- Each individual summand is four-times differentiable in the first
height variable wherever `A>0`. -/
theorem contDiffAt_latitudeEvenPowerSummand_left
    {α : ℝ} {m : ℕ} {s t : ℝ}
    (hA : 0 < angularKernelA s t) :
    ContDiffAt ℝ 4 (fun y ↦ latitudeEvenPowerSummand α m y t) s := by
  have hAfun :
      ContDiffAt ℝ 4 (fun y : ℝ ↦ angularKernelA y t) s := by
    unfold angularKernelA
    fun_prop
  have hApow :
      ContDiffAt ℝ 4
        (fun y : ℝ ↦ angularKernelA y t ^
          (α / 2 - 2 * (m : ℝ))) s :=
    by
      simpa only [Function.comp_apply] using
        (Real.contDiffAt_rpow_const_of_ne (n := 4) hA.ne').comp s hAfun
  have hu :
      ContDiffAt ℝ 4 (fun y : ℝ ↦ (1 - y ^ 2) ^ m) s := by
    fun_prop
  have hc4 : ContDiffAt ℝ 4 (fun _ : ℝ ↦ (4 : ℝ) ^ m) s :=
    contDiffAt_const
  have hct : ContDiffAt ℝ 4 (fun _ : ℝ ↦ (1 - t ^ 2) ^ m) s :=
    contDiffAt_const
  unfold latitudeEvenPowerSummand
  exact (((hApow.mul hc4).mul hu).mul hct)

/-- The symmetric four-times differentiability statement in the second
height variable. -/
theorem contDiffAt_latitudeEvenPowerSummand_right
    {α : ℝ} {m : ℕ} {s t : ℝ}
    (hA : 0 < angularKernelA s t) :
    ContDiffAt ℝ 4 (fun y ↦ latitudeEvenPowerSummand α m s y) t := by
  have hAfun :
      ContDiffAt ℝ 4 (fun y : ℝ ↦ angularKernelA s y) t := by
    unfold angularKernelA
    fun_prop
  have hApow :
      ContDiffAt ℝ 4
        (fun y : ℝ ↦ angularKernelA s y ^
          (α / 2 - 2 * (m : ℝ))) t :=
    by
      simpa only [Function.comp_apply] using
        (Real.contDiffAt_rpow_const_of_ne (n := 4) hA.ne').comp t hAfun
  have hv :
      ContDiffAt ℝ 4 (fun y : ℝ ↦ (1 - y ^ 2) ^ m) t := by
    fun_prop
  have hc : ContDiffAt ℝ 4
      (fun _ : ℝ ↦ (4 : ℝ) ^ m * (1 - s ^ 2) ^ m) t :=
    contDiffAt_const
  unfold latitudeEvenPowerSummand
  convert (hApow.mul hc).mul hv using 1 <;> ring

/-- In particular every summand is `C²` in each variable, as required
before taking the mixed `(2,2)` derivative. -/
theorem contDiffAt_two_latitudeEvenPowerSummand
    {α : ℝ} {m : ℕ} {s t : ℝ}
    (hA : 0 < angularKernelA s t) :
    ContDiffAt ℝ 2 (fun y ↦ latitudeEvenPowerSummand α m y t) s ∧
      ContDiffAt ℝ 2 (fun y ↦ latitudeEvenPowerSummand α m s y) t := by
  have h24 : (2 : WithTop ℕ∞) ≤ 4 := by decide
  exact
    ⟨(contDiffAt_latitudeEvenPowerSummand_left hA).of_le h24,
      (contDiffAt_latitudeEvenPowerSummand_right hA).of_le h24⟩

/-- The actual mixed `(2,2)` partial derivative, expressed using mathlib's
iterated one-variable derivative. -/
noncomputable def latitudeEvenPowerSummandMixed22
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  iteratedDeriv 2
    (fun y ↦ iteratedDeriv 2
      (fun x ↦ latitudeEvenPowerSummand α m x y) s) t

/-! ## Explicit finite Leibniz expansion -/

noncomputable def unequalRadiusPower (m : ℕ) (s : ℝ) : ℝ :=
  (1 - s ^ 2) ^ m

noncomputable def unequalRadiusPowerD1 (m : ℕ) (s : ℝ) : ℝ :=
  (m : ℝ) * (1 - s ^ 2) ^ (m - 1) * (-2 * s)

noncomputable def unequalRadiusPowerD2 (m : ℕ) (s : ℝ) : ℝ :=
  (m : ℝ) * ((m : ℝ) - 1) * (1 - s ^ 2) ^ (m - 2) * (-2 * s) ^ 2 +
    (m : ℝ) * (1 - s ^ 2) ^ (m - 1) * (-2)

noncomputable def unequalAPow (e s t : ℝ) : ℝ :=
  angularKernelA s t ^ e

noncomputable def unequalAPowS (e s t : ℝ) : ℝ :=
  e * angularKernelA s t ^ (e - 1) * (-2 * t)

noncomputable def unequalAPowT (e s t : ℝ) : ℝ :=
  e * angularKernelA s t ^ (e - 1) * (-2 * s)

noncomputable def unequalAPowSS (e s t : ℝ) : ℝ :=
  e * (e - 1) * angularKernelA s t ^ (e - 2) * (-2 * t) ^ 2

noncomputable def unequalAPowST (e s t : ℝ) : ℝ :=
  e * (e - 1) * angularKernelA s t ^ (e - 2) *
      (-2 * s) * (-2 * t) +
    e * angularKernelA s t ^ (e - 1) * (-2)

noncomputable def unequalAPowTT (e s t : ℝ) : ℝ :=
  e * (e - 1) * angularKernelA s t ^ (e - 2) * (-2 * s) ^ 2

noncomputable def unequalAPowSST (e s t : ℝ) : ℝ :=
  e * (e - 1) * (e - 2) * angularKernelA s t ^ (e - 3) *
      (-2 * s) * (-2 * t) ^ 2 +
    2 * e * (e - 1) * angularKernelA s t ^ (e - 2) *
      (-2 * t) * (-2)

noncomputable def unequalAPowSTT (e s t : ℝ) : ℝ :=
  e * (e - 1) * (e - 2) * angularKernelA s t ^ (e - 3) *
      (-2 * t) * (-2 * s) ^ 2 +
    2 * e * (e - 1) * angularKernelA s t ^ (e - 2) *
      (-2 * s) * (-2)

noncomputable def unequalAPowSSTT (e s t : ℝ) : ℝ :=
  e * (e - 1) * (e - 2) * (e - 3) *
      angularKernelA s t ^ (e - 4) * (-2 * s) ^ 2 * (-2 * t) ^ 2 +
    4 * e * (e - 1) * (e - 2) *
      angularKernelA s t ^ (e - 3) * (-2 * s) * (-2 * t) * (-2) +
    2 * e * (e - 1) * angularKernelA s t ^ (e - 2) * (-2) ^ 2

noncomputable def latitudeEvenPowerSummandDSS
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  let e := α / 2 - 2 * (m : ℝ)
  (4 : ℝ) ^ m *
    (unequalAPowSS e s t * unequalRadiusPower m s +
      2 * unequalAPowS e s t * unequalRadiusPowerD1 m s +
      unequalAPow e s t * unequalRadiusPowerD2 m s) *
    unequalRadiusPower m t

noncomputable def latitudeEvenPowerSummandDSST
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  let e := α / 2 - 2 * (m : ℝ)
  let X :=
    unequalAPowSS e s t * unequalRadiusPower m s +
      2 * unequalAPowS e s t * unequalRadiusPowerD1 m s +
      unequalAPow e s t * unequalRadiusPowerD2 m s
  let XT :=
    unequalAPowSST e s t * unequalRadiusPower m s +
      2 * unequalAPowST e s t * unequalRadiusPowerD1 m s +
      unequalAPowT e s t * unequalRadiusPowerD2 m s
  (4 : ℝ) ^ m *
    (XT * unequalRadiusPower m t + X * unequalRadiusPowerD1 m t)

noncomputable def latitudeEvenPowerSummandDSSTT
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  let e := α / 2 - 2 * (m : ℝ)
  let X :=
    unequalAPowSS e s t * unequalRadiusPower m s +
      2 * unequalAPowS e s t * unequalRadiusPowerD1 m s +
      unequalAPow e s t * unequalRadiusPowerD2 m s
  let XT :=
    unequalAPowSST e s t * unequalRadiusPower m s +
      2 * unequalAPowST e s t * unequalRadiusPowerD1 m s +
      unequalAPowT e s t * unequalRadiusPowerD2 m s
  let XTT :=
    unequalAPowSSTT e s t * unequalRadiusPower m s +
      2 * unequalAPowSTT e s t * unequalRadiusPowerD1 m s +
      unequalAPowTT e s t * unequalRadiusPowerD2 m s
  (4 : ℝ) ^ m *
    (XTT * unequalRadiusPower m t +
      2 * XT * unequalRadiusPowerD1 m t +
      X * unequalRadiusPowerD2 m t)

/-- The endpoint-safe monomial bound specialized to an actual unequal
latitude rectangle.  It is valid when the smaller squared radius is zero. -/
theorem unequalDerivativeMonomial_le_on_leftSmall_rectangle
    {α : ℝ} {N : ℕ} (hN : 0 < N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : LeftSmallSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    {m a b c : ℕ}
    (hb : b ≤ 2) (hc : c ≤ 2)
    (habc : a + b + c = 4) (hm : 2 ≤ m) :
    unequalDerivativeMonomial (α / 2)
        (angularKernelA s t) (1 - s ^ 2) (1 - t ^ 2)
        m a b c ≤
      16 * angularKernelA s t ^ (α / 2 - 4) *
        ((15 : ℝ) / 16) ^ (m - 2) := by
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hA :=
    (leftSmallSame_rectangle_angularKernelA_bounds hN j k hjk hs ht).1
  have hu0 : 0 ≤ 1 - s ^ 2 := by nlinarith [hsSphere.1, hsSphere.2]
  have hv0 : 0 ≤ 1 - t ^ 2 := by nlinarith [htSphere.1, htSphere.2]
  have huA : 1 - s ^ 2 ≤ angularKernelA s t := by
    rw [angularKernelA_eq_radiusSq_add]
    nlinarith [hv0, sq_nonneg (s - t)]
  have hvA : 1 - t ^ 2 ≤ angularKernelA s t := by
    rw [angularKernelA_eq_radiusSq_add]
    nlinarith [hu0, sq_nonneg (s - t)]
  have hmono := unequalDerivativeMonomial_le (β := α / 2)
    hA hu0 hv0 huA hvA hb hc habc hm
  have hQ0 := unequalAngularRatio_nonneg hsSphere htSphere
  have hQ := leftSmallSame_rectangle_unequalAngularRatio_le
    hN j k hjk hs ht
  have hpow :
      unequalAngularRatio s t ^ (m - 2) ≤
        ((15 : ℝ) / 16) ^ (m - 2) := by
    exact pow_le_pow_left₀ hQ0 hQ _
  rw [show 4 * (1 - s ^ 2) * (1 - t ^ 2) /
      angularKernelA s t ^ 2 = unequalAngularRatio s t by rfl] at hmono
  exact hmono.trans (by
    have hcoef :
        0 ≤ 16 * angularKernelA s t ^ (α / 2 - 4) := by positivity
    exact mul_le_mul_of_nonneg_left hpow hcoef)

/-- The degree-four polynomial/geometric majorant which dominates the sum
of all finitely many Leibniz terms of a mixed `(2,2)` derivative. -/
noncomputable def latitudeEvenPowerMixed22Majorant
    (α A : ℝ) (m : ℕ) : ℝ :=
  256 * ((m : ℝ) + 1) ^ (4 : ℕ) *
    A ^ (α / 2 - 4) * ((15 : ℝ) / 16) ^ (m - 2)

/-- The mixed-derivative majorant is normally summable in `m` for every
fixed positive angular scale. -/
theorem summable_latitudeEvenPowerMixed22Majorant
    {α A : ℝ} (hA : 0 < A) :
    Summable (fun r : ℕ ↦
      latitudeEvenPowerMixed22Majorant α A (r + 2)) := by
  have hgeo :=
    summable_natPolynomial_mul_geometric_shift_two 4
      (q := (15 : ℝ) / 16) (by norm_num) (by norm_num)
  have hscaled := hgeo.mul_left
    (256 * A ^ (α / 2 - 4))
  convert hscaled using 1
  funext r
  unfold latitudeEvenPowerMixed22Majorant
  rw [show r + 2 - 2 = r by omega]
  norm_num [Nat.cast_add, Nat.cast_ofNat]
  ring

end BEMOC
