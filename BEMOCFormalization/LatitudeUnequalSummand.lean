import BEMOCFormalization.LatitudeUnequalGeometry
import BEMOCFormalization.LatitudeUnequalSeries

/-!
# Individual even-power summands on unequal latitude rectangles

This file applies the endpoint-safe monomial majorant to the actual
summands in (5.6).  It also records the required smoothness of each
individual summand on the open region `A>0`.
-/

open Filter Set
open scoped Topology

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

/-! ## Verification of the explicit derivative -/

noncomputable def latitudeEvenPowerSummandDS
    (α : ℝ) (m : ℕ) (s t : ℝ) : ℝ :=
  let e := α / 2 - 2 * (m : ℝ)
  (4 : ℝ) ^ m *
    (unequalAPowS e s t * unequalRadiusPower m s +
      unequalAPow e s t * unequalRadiusPowerD1 m s) *
    unequalRadiusPower m t

theorem hasDerivAt_unequalRadiusPower (m : ℕ) (s : ℝ) :
    HasDerivAt (unequalRadiusPower m) (unequalRadiusPowerD1 m s) s := by
  unfold unequalRadiusPower unequalRadiusPowerD1
  convert
    (((hasDerivAt_const s 1).sub (hasDerivAt_pow 2 s)).pow m) using 1 <;>
    ring

theorem hasDerivAt_unequalRadiusPowerD1 (m : ℕ) (s : ℝ) :
    HasDerivAt (unequalRadiusPowerD1 m) (unequalRadiusPowerD2 m s) s := by
  cases m with
  | zero =>
      have hfun : unequalRadiusPowerD1 0 = fun _ : ℝ ↦ 0 := by
        funext y
        simp [unequalRadiusPowerD1]
      have hval : unequalRadiusPowerD2 0 s = 0 := by
        simp [unequalRadiusPowerD2]
      rw [hfun, hval]
      exact hasDerivAt_const s 0
  | succ m =>
      have hbase :
          HasDerivAt (fun y : ℝ ↦ 1 - y ^ 2) (-2 * s) s := by
        convert (hasDerivAt_const s 1).sub (hasDerivAt_pow 2 s) using 1 <;> ring
      have hlin : HasDerivAt (fun y : ℝ ↦ -2 * y) (-2) s := by
        convert (hasDerivAt_const s (-2)).mul (hasDerivAt_id s) using 1 <;> ring
      unfold unequalRadiusPowerD1 unequalRadiusPowerD2
      have hm : m + 1 - 2 = m - 1 := by omega
      convert
        ((hbase.pow m).const_mul ((m + 1 : ℕ) : ℝ)).mul hlin using 1 <;>
        norm_num [Nat.cast_add]
      rw [hm]
      ring

private theorem hasDerivAt_angularKernelA_left (s t : ℝ) :
    HasDerivAt (fun y ↦ angularKernelA y t) (-2 * t) s := by
  unfold angularKernelA
  convert (hasDerivAt_const s 2).sub
    ((hasDerivAt_id s).mul_const (2 * t)) using 1
  · funext y
    simp only [id_eq]
    ring
  · ring

private theorem hasDerivAt_angularKernelA_right (s t : ℝ) :
    HasDerivAt (fun y ↦ angularKernelA s y) (-2 * s) t := by
  unfold angularKernelA
  convert (hasDerivAt_const t 2).sub
    ((hasDerivAt_id t).mul_const (2 * s)) using 1
  · funext y
    simp only [id_eq]
    ring
  · ring

theorem hasDerivAt_unequalAPow_left
    {e s t : ℝ} (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ unequalAPow e y t) (unequalAPowS e s t) s := by
  unfold unequalAPow unequalAPowS
  convert
    (Real.hasDerivAt_rpow_const (x := angularKernelA s t)
      (p := e) (Or.inl hA.ne')).comp s
        (hasDerivAt_angularKernelA_left s t) using 1 <;>
    simp only [Function.comp_apply] <;> ring

theorem hasDerivAt_unequalAPowS_left
    {e s t : ℝ} (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ unequalAPowS e y t) (unequalAPowSS e s t) s := by
  unfold unequalAPowS unequalAPowSS
  convert
    ((Real.hasDerivAt_rpow_const (x := angularKernelA s t)
      (p := e - 1) (Or.inl hA.ne')).comp s
        (hasDerivAt_angularKernelA_left s t)).const_mul (e * (-2 * t))
      using 1
  · funext y
    simp only [Function.comp_apply]
    ring
  · ring

theorem hasDerivAt_unequalAPow_right
    {e s t : ℝ} (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ unequalAPow e s y) (unequalAPowT e s t) t := by
  unfold unequalAPow unequalAPowT
  convert
    (Real.hasDerivAt_rpow_const (x := angularKernelA s t)
      (p := e) (Or.inl hA.ne')).comp t
        (hasDerivAt_angularKernelA_right s t) using 1 <;>
    simp only [Function.comp_apply] <;> ring

theorem hasDerivAt_unequalAPowT_right
    {e s t : ℝ} (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ unequalAPowT e s y) (unequalAPowTT e s t) t := by
  unfold unequalAPowT unequalAPowTT
  convert
    ((Real.hasDerivAt_rpow_const (x := angularKernelA s t)
      (p := e - 1) (Or.inl hA.ne')).comp t
        (hasDerivAt_angularKernelA_right s t)).const_mul (e * (-2 * s))
      using 1
  · funext y
    simp only [Function.comp_apply]
    ring
  · ring

theorem hasDerivAt_unequalAPowS_right
    {e s t : ℝ} (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ unequalAPowS e s y) (unequalAPowST e s t) t := by
  unfold unequalAPowS unequalAPowST
  have hp :=
    (Real.hasDerivAt_rpow_const (x := angularKernelA s t)
      (p := e - 1) (Or.inl hA.ne')).comp t
        (hasDerivAt_angularKernelA_right s t)
  have hlin : HasDerivAt (fun y : ℝ ↦ -2 * y) (-2) t := by
    convert (hasDerivAt_const t (-2)).mul (hasDerivAt_id t) using 1 <;> ring
  convert (hp.mul hlin).const_mul e using 1
  · funext y
    simp only [Function.comp_apply, id_eq]
    ring
  · simp only [Function.comp_apply]
    ring

theorem hasDerivAt_unequalAPowSS_right
    {e s t : ℝ} (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ unequalAPowSS e s y) (unequalAPowSST e s t) t := by
  unfold unequalAPowSS unequalAPowSST
  have hp :=
    (Real.hasDerivAt_rpow_const (x := angularKernelA s t)
      (p := e - 2) (Or.inl hA.ne')).comp t
        (hasDerivAt_angularKernelA_right s t)
  have hsq : HasDerivAt (fun y : ℝ ↦ (-2 * y) ^ 2)
      (2 * (-2 * t) * (-2)) t := by
    convert
      (((hasDerivAt_const t (-2)).mul (hasDerivAt_id t)).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  convert (hp.mul hsq).const_mul (e * (e - 1)) using 1
  · funext y
    simp only [Function.comp_apply, id_eq]
    ring
  · simp only [Function.comp_apply]
    ring

theorem hasDerivAt_unequalAPowST_right
    {e s t : ℝ} (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ unequalAPowST e s y) (unequalAPowSTT e s t) t := by
  unfold unequalAPowST unequalAPowSTT
  have hp2 :=
    (Real.hasDerivAt_rpow_const (x := angularKernelA s t)
      (p := e - 2) (Or.inl hA.ne')).comp t
        (hasDerivAt_angularKernelA_right s t)
  have hp1 :=
    (Real.hasDerivAt_rpow_const (x := angularKernelA s t)
      (p := e - 1) (Or.inl hA.ne')).comp t
        (hasDerivAt_angularKernelA_right s t)
  have hlin : HasDerivAt (fun y : ℝ ↦ -2 * y) (-2) t := by
    convert (hasDerivAt_const t (-2)).mul (hasDerivAt_id t) using 1 <;> ring
  convert
    (((hp2.mul hlin).const_mul (e * (e - 1) * (-2 * s))).add
      (hp1.const_mul (e * (-2)))) using 1
  · funext y
    simp only [Function.comp_apply, id_eq]
    ring
  · simp only [Function.comp_apply]
    ring

theorem hasDerivAt_unequalAPowSST_right
    {e s t : ℝ} (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ unequalAPowSST e s y)
      (unequalAPowSSTT e s t) t := by
  unfold unequalAPowSST unequalAPowSSTT
  have hp3 :=
    (Real.hasDerivAt_rpow_const (x := angularKernelA s t)
      (p := e - 3) (Or.inl hA.ne')).comp t
        (hasDerivAt_angularKernelA_right s t)
  have hp2 :=
    (Real.hasDerivAt_rpow_const (x := angularKernelA s t)
      (p := e - 2) (Or.inl hA.ne')).comp t
        (hasDerivAt_angularKernelA_right s t)
  have hsq : HasDerivAt (fun y : ℝ ↦ (-2 * y) ^ 2)
      (2 * (-2 * t) * (-2)) t := by
    convert
      (((hasDerivAt_const t (-2)).mul (hasDerivAt_id t)).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hlin : HasDerivAt (fun y : ℝ ↦ -2 * y) (-2) t := by
    convert (hasDerivAt_const t (-2)).mul (hasDerivAt_id t) using 1 <;> ring
  convert
    (((hp3.mul hsq).const_mul
        (e * (e - 1) * (e - 2) * (-2 * s))).add
      ((hp2.mul hlin).const_mul
        (2 * e * (e - 1) * (-2)))) using 1
  · funext y
    simp only [Function.comp_apply, id_eq]
    ring
  · simp only [Function.comp_apply]
    ring

theorem hasDerivAt_latitudeEvenPowerSummand_left
    {α : ℝ} {m : ℕ} {s t : ℝ}
    (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ latitudeEvenPowerSummand α m y t)
      (latitudeEvenPowerSummandDS α m s t) s := by
  let e := α / 2 - 2 * (m : ℝ)
  have hp := hasDerivAt_unequalAPow_left (e := e) hA
  have hu := hasDerivAt_unequalRadiusPower m s
  unfold latitudeEvenPowerSummand latitudeEvenPowerSummandDS
  dsimp only
  convert ((hp.mul hu).const_mul ((4 : ℝ) ^ m)).mul_const
    (unequalRadiusPower m t) using 1
  · funext y
    dsimp [e, unequalAPow, unequalRadiusPower]
    ring

theorem hasDerivAt_latitudeEvenPowerSummandDS_left
    {α : ℝ} {m : ℕ} {s t : ℝ}
    (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ latitudeEvenPowerSummandDS α m y t)
      (latitudeEvenPowerSummandDSS α m s t) s := by
  let e := α / 2 - 2 * (m : ℝ)
  have hp := hasDerivAt_unequalAPow_left (e := e) hA
  have hps := hasDerivAt_unequalAPowS_left (e := e) hA
  have hu := hasDerivAt_unequalRadiusPower m s
  have hu1 := hasDerivAt_unequalRadiusPowerD1 m s
  unfold latitudeEvenPowerSummandDS latitudeEvenPowerSummandDSS
  dsimp only
  convert
    ((((hps.mul hu).add (hp.mul hu1)).const_mul ((4 : ℝ) ^ m)).mul_const
      (unequalRadiusPower m t)) using 1
  dsimp [e]
  ring

theorem hasDerivAt_latitudeEvenPowerSummandDSS_right
    {α : ℝ} {m : ℕ} {s t : ℝ}
    (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ latitudeEvenPowerSummandDSS α m s y)
      (latitudeEvenPowerSummandDSST α m s t) t := by
  let e := α / 2 - 2 * (m : ℝ)
  have hss := hasDerivAt_unequalAPowSS_right (e := e) hA
  have hs := hasDerivAt_unequalAPowS_right (e := e) hA
  have h0 := hasDerivAt_unequalAPow_right (e := e) hA
  have hv := hasDerivAt_unequalRadiusPower m t
  let U := unequalRadiusPower m s
  let U1 := unequalRadiusPowerD1 m s
  let U2 := unequalRadiusPowerD2 m s
  have hX :
      HasDerivAt
        (fun y ↦ unequalAPowSS e s y * U +
          2 * unequalAPowS e s y * U1 +
          unequalAPow e s y * U2)
        (unequalAPowSST e s t * U +
          2 * unequalAPowST e s t * U1 +
          unequalAPowT e s t * U2) t := by
    convert
      (((hss.mul_const U).add ((hs.mul_const U1).const_mul 2)).add
        (h0.mul_const U2)) using 1
    · funext y
      ring
    · ring
  unfold latitudeEvenPowerSummandDSS latitudeEvenPowerSummandDSST
  dsimp only
  convert (hX.mul hv).const_mul ((4 : ℝ) ^ m) using 1
  · funext y
    ring

theorem hasDerivAt_latitudeEvenPowerSummandDSST_right
    {α : ℝ} {m : ℕ} {s t : ℝ}
    (hA : 0 < angularKernelA s t) :
    HasDerivAt (fun y ↦ latitudeEvenPowerSummandDSST α m s y)
      (latitudeEvenPowerSummandDSSTT α m s t) t := by
  let e := α / 2 - 2 * (m : ℝ)
  have hsst := hasDerivAt_unequalAPowSST_right (e := e) hA
  have hst := hasDerivAt_unequalAPowST_right (e := e) hA
  have ht := hasDerivAt_unequalAPowT_right (e := e) hA
  have hss := hasDerivAt_unequalAPowSS_right (e := e) hA
  have hs := hasDerivAt_unequalAPowS_right (e := e) hA
  have h0 := hasDerivAt_unequalAPow_right (e := e) hA
  have hv := hasDerivAt_unequalRadiusPower m t
  have hv1 := hasDerivAt_unequalRadiusPowerD1 m t
  let U := unequalRadiusPower m s
  let U1 := unequalRadiusPowerD1 m s
  let U2 := unequalRadiusPowerD2 m s
  have hXT :
      HasDerivAt
        (fun y ↦ unequalAPowSST e s y * U +
          2 * unequalAPowST e s y * U1 +
          unequalAPowT e s y * U2)
        (unequalAPowSSTT e s t * U +
          2 * unequalAPowSTT e s t * U1 +
          unequalAPowTT e s t * U2) t := by
    convert
      (((hsst.mul_const U).add ((hst.mul_const U1).const_mul 2)).add
        (ht.mul_const U2)) using 1
    · funext y
      ring
    · ring
  have hX :
      HasDerivAt
        (fun y ↦ unequalAPowSS e s y * U +
          2 * unequalAPowS e s y * U1 +
          unequalAPow e s y * U2)
        (unequalAPowSST e s t * U +
          2 * unequalAPowST e s t * U1 +
          unequalAPowT e s t * U2) t := by
    convert
      (((hss.mul_const U).add ((hs.mul_const U1).const_mul 2)).add
        (h0.mul_const U2)) using 1
    · funext y
      ring
    · ring
  unfold latitudeEvenPowerSummandDSST latitudeEvenPowerSummandDSSTT
  dsimp only
  convert
    ((hXT.mul hv).add (hX.mul hv1)).const_mul ((4 : ℝ) ^ m) using 1
  dsimp [e, U, U1, U2]
  ring

theorem iteratedDeriv_two_latitudeEvenPowerSummand_left
    {α : ℝ} {m : ℕ} {s t : ℝ}
    (hA : 0 < angularKernelA s t) :
    iteratedDeriv 2 (fun y ↦ latitudeEvenPowerSummand α m y t) s =
      latitudeEvenPowerSummandDSS α m s t := by
  have hcont : ContinuousAt (fun y : ℝ ↦ angularKernelA y t) s := by
    unfold angularKernelA
    fun_prop
  have hpos : ∀ᶠ y in 𝓝 s, 0 < angularKernelA y t :=
    hcont.eventually (Ioi_mem_nhds hA)
  have heq :
      deriv (fun y ↦ latitudeEvenPowerSummand α m y t) =ᶠ[𝓝 s]
        fun y ↦ latitudeEvenPowerSummandDS α m y t := by
    filter_upwards [hpos] with y hy
    exact (hasDerivAt_latitudeEvenPowerSummand_left hy).deriv
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ]
  rw [show iteratedDeriv 1
      (fun y ↦ latitudeEvenPowerSummand α m y t) =
        deriv (fun y ↦ latitudeEvenPowerSummand α m y t) by
      rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_zero]]
  rw [heq.deriv_eq]
  exact (hasDerivAt_latitudeEvenPowerSummandDS_left hA).deriv

/-- The finite Leibniz formula above is exactly mathlib's mixed `(2,2)`
iterated derivative, not merely a formal expression. -/
theorem latitudeEvenPowerSummandMixed22_eq_DSSTT
    {α : ℝ} {m : ℕ} {s t : ℝ}
    (hA : 0 < angularKernelA s t) :
    latitudeEvenPowerSummandMixed22 α m s t =
      latitudeEvenPowerSummandDSSTT α m s t := by
  let G : ℝ → ℝ := fun y ↦
    iteratedDeriv 2 (fun x ↦ latitudeEvenPowerSummand α m x y) s
  have hcont : ContinuousAt (fun y : ℝ ↦ angularKernelA s y) t := by
    unfold angularKernelA
    fun_prop
  have hpos : ∀ᶠ y in 𝓝 t, 0 < angularKernelA s y :=
    hcont.eventually (Ioi_mem_nhds hA)
  have hG :
      G =ᶠ[𝓝 t] fun y ↦ latitudeEvenPowerSummandDSS α m s y := by
    filter_upwards [hpos] with y hy
    exact iteratedDeriv_two_latitudeEvenPowerSummand_left hy
  have hDSS :
      deriv (fun y ↦ latitudeEvenPowerSummandDSS α m s y) =ᶠ[𝓝 t]
        fun y ↦ latitudeEvenPowerSummandDSST α m s y := by
    filter_upwards [hpos] with y hy
    exact (hasDerivAt_latitudeEvenPowerSummandDSS_right hy).deriv
  unfold latitudeEvenPowerSummandMixed22
  change iteratedDeriv 2 G t = _
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ]
  rw [show iteratedDeriv 1 G = deriv G by
      rw [show 1 = 0 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_zero]]
  rw [hG.deriv.deriv_eq, hDSS.deriv_eq]
  exact (hasDerivAt_latitudeEvenPowerSummandDSST_right hA).deriv

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
