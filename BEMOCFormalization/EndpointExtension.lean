import BEMOCFormalization.CircleEndpoint

open scoped Topology
open Filter Set

namespace BEMOC.CircleGeneral.EndpointExtension

/-- Extend a function on `[0,1]` by the quadratic Taylor polynomials determined
by its endpoint two-jets. -/
noncomputable def quadraticJetExtension
    (f f' f'' : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then
    f 0 + f' 0 * x + f'' 0 / 2 * x ^ 2
  else if x ≤ 1 then f x
  else
    f 1 + f' 1 * (x - 1) + f'' 1 / 2 * (x - 1) ^ 2

/-- The intended first derivative of `quadraticJetExtension`. -/
noncomputable def quadraticJetExtensionDeriv
    (f' f'' : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then f' 0 + f'' 0 * x
  else if x ≤ 1 then f' x
  else f' 1 + f'' 1 * (x - 1)

/-- The intended second derivative of `quadraticJetExtension`. -/
noncomputable def quadraticJetExtensionSecond
    (f'' : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then f'' 0
  else if x ≤ 1 then f'' x
  else f'' 1

theorem quadraticJetExtension_eq
    (f f' f'' : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    quadraticJetExtension f f' f'' x = f x := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hx0.eq_or_lt with rfl | hx0
  · simp [quadraticJetExtension]
  · simp [quadraticJetExtension, hx0.not_le, hx1]

theorem quadraticJetExtensionDeriv_eq
    (f' f'' : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    quadraticJetExtensionDeriv f' f'' x = f' x := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hx0.eq_or_lt with rfl | hx0
  · simp [quadraticJetExtensionDeriv]
  · simp [quadraticJetExtensionDeriv, hx0.not_le, hx1]

theorem quadraticJetExtensionSecond_eq
    (f'' : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    quadraticJetExtensionSecond f'' x = f'' x := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hx0.eq_or_lt with rfl | hx0
  · simp [quadraticJetExtensionSecond]
  · simp [quadraticJetExtensionSecond, hx0.not_le, hx1]

private theorem hasDerivAt_leftQuadratic
    (f f' f'' : ℝ → ℝ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => f 0 + f' 0 * y + f'' 0 / 2 * y ^ 2)
      (f' 0 + f'' 0 * x) x := by
  convert
    ((hasDerivAt_const x (f 0)).add
      ((hasDerivAt_id x).const_mul (f' 0))).add
      (((hasDerivAt_pow 2 x).const_mul (f'' 0 / 2))) using 1 <;> ring

private theorem hasDerivAt_rightQuadratic
    (f f' f'' : ℝ → ℝ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        f 1 + f' 1 * (y - 1) + f'' 1 / 2 * (y - 1) ^ 2)
      (f' 1 + f'' 1 * (x - 1)) x := by
  have hsub : HasDerivAt (fun y : ℝ => y - 1) 1 x :=
    (hasDerivAt_id x).sub_const 1
  convert
    ((hasDerivAt_const x (f 1)).add (hsub.const_mul (f' 1))).add
      (((hsub.pow 2).const_mul (f'' 1 / 2))) using 1 <;> ring

private theorem hasDerivAt_leftLinear
    (f' f'' : ℝ → ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => f' 0 + f'' 0 * y) (f'' 0) x := by
  convert (hasDerivAt_const x (f' 0)).add
    ((hasDerivAt_id x).const_mul (f'' 0)) using 1 <;> ring

private theorem hasDerivAt_rightLinear
    (f' f'' : ℝ → ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => f' 1 + f'' 1 * (y - 1)) (f'' 1) x := by
  convert (hasDerivAt_const x (f' 1)).add
    (((hasDerivAt_id x).sub_const 1).const_mul (f'' 1)) using 1 <;> ring

theorem quadraticJetExtension_hasDerivAt
    (f f' f'' : ℝ → ℝ)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf0 : HasDerivWithinAt f (f' 0) (Ici (0 : ℝ)) 0)
    (hf1 : HasDerivWithinAt f (f' 1) (Iic (1 : ℝ)) 1) :
    ∀ x, HasDerivAt (quadraticJetExtension f f' f'')
      (quadraticJetExtensionDeriv f' f'' x) x := by
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hext : quadraticJetExtension f f' f'' =ᶠ[𝓝 x]
        (fun y : ℝ => f 0 + f' 0 * y + f'' 0 / 2 * y ^ 2) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp [quadraticJetExtension, hy.le]
    have hder : quadraticJetExtensionDeriv f' f'' x = f' 0 + f'' 0 * x := by
      simp [quadraticJetExtensionDeriv, hx.le]
    rw [hder]
    exact (hasDerivAt_leftQuadratic f f' f'' x).congr_of_eventuallyEq hext
  · have hleft : HasDerivWithinAt (quadraticJetExtension f f' f'')
        (f' 0) (Iic (0 : ℝ)) 0 := by
      have hp : HasDerivAt
          (fun y : ℝ => f 0 + f' 0 * y + f'' 0 / 2 * y ^ 2) (f' 0) 0 := by
        simpa using hasDerivAt_leftQuadratic f f' f'' 0
      apply hp.hasDerivWithinAt.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : y ≤ 0 := hy
        simp [quadraticJetExtension, hy']
      · simp [quadraticJetExtension]
    have hright : HasDerivWithinAt (quadraticJetExtension f f' f'')
        (f' 0) (Ici (0 : ℝ)) 0 := by
      apply hf0.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin,
          (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left]
          with y hy0 hy1
        have hy0' : 0 ≤ y := hy0
        rcases eq_or_lt_of_le hy0' with rfl | hy0
        · simp [quadraticJetExtension]
        · simp [quadraticJetExtension, hy0.not_le, hy1.le]
      · simp [quadraticJetExtension]
    have h := hleft.union hright
    simpa [quadraticJetExtensionDeriv] using h
  · rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · have hext : quadraticJetExtension f f' f'' =ᶠ[𝓝 x] f := by
        filter_upwards [eventually_gt_nhds hx, eventually_lt_nhds hx1] with y hy0 hy1
        simp [quadraticJetExtension, hy0.not_le, hy1.le]
      have hder : quadraticJetExtensionDeriv f' f'' x = f' x := by
        simp [quadraticJetExtensionDeriv, hx.not_le, hx1.le]
      rw [hder]
      exact (hf x ⟨hx, hx1⟩).congr_of_eventuallyEq hext
    · have hleft : HasDerivWithinAt (quadraticJetExtension f f' f'')
          (f' 1) (Iic (1 : ℝ)) 1 := by
        apply hf1.congr_of_eventuallyEq
        · filter_upwards [self_mem_nhdsWithin,
            (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left]
            with y hy1 hy0
          have hy1' : y ≤ 1 := hy1
          rcases eq_or_lt_of_le hy1' with rfl | hy1
          · simp [quadraticJetExtension]
          · simp [quadraticJetExtension, hy0.not_le, hy1.le]
        · simp [quadraticJetExtension]
      have hright : HasDerivWithinAt (quadraticJetExtension f f' f'')
          (f' 1) (Ici (1 : ℝ)) 1 := by
        have hp : HasDerivAt
            (fun y : ℝ => f 1 + f' 1 * (y - 1) + f'' 1 / 2 * (y - 1) ^ 2)
            (f' 1) 1 := by
          simpa using hasDerivAt_rightQuadratic f f' f'' 1
        apply hp.hasDerivWithinAt.congr_of_eventuallyEq
        · filter_upwards [self_mem_nhdsWithin] with y hy
          have hy' : 1 ≤ y := hy
          rcases hy'.eq_or_lt with rfl | hy
          · simp [quadraticJetExtension]
          · simp [quadraticJetExtension, hy.not_le, show ¬ y ≤ 0 by linarith]
        · simp [quadraticJetExtension]
      have h := hleft.union hright
      norm_num [quadraticJetExtensionDeriv]
      have huniv : Iic (1 : ℝ) ∪ Ici 1 = univ := Iic_union_Ici
      rw [huniv] at h
      exact hasDerivWithinAt_univ.mp h
    · have hext : quadraticJetExtension f f' f'' =ᶠ[𝓝 x]
          (fun y : ℝ => f 1 + f' 1 * (y - 1) + f'' 1 / 2 * (y - 1) ^ 2) := by
        filter_upwards [eventually_gt_nhds hx1] with y hy
        simp [quadraticJetExtension, hy.not_le, show ¬ y ≤ 0 by linarith]
      have hder : quadraticJetExtensionDeriv f' f'' x = f' 1 + f'' 1 * (x - 1) := by
        simp [quadraticJetExtensionDeriv, hx1.not_le, show ¬ x ≤ 0 by linarith]
      rw [hder]
      exact (hasDerivAt_rightQuadratic f f' f'' x).congr_of_eventuallyEq hext

theorem quadraticJetExtensionDeriv_hasDerivAt
    (f' f'' : ℝ → ℝ)
    (hf' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f' (f'' x) x)
    (hf'0 : HasDerivWithinAt f' (f'' 0) (Ici (0 : ℝ)) 0)
    (hf'1 : HasDerivWithinAt f' (f'' 1) (Iic (1 : ℝ)) 1) :
    ∀ x, HasDerivAt (quadraticJetExtensionDeriv f' f'')
      (quadraticJetExtensionSecond f'' x) x := by
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hext : quadraticJetExtensionDeriv f' f'' =ᶠ[𝓝 x]
        (fun y : ℝ => f' 0 + f'' 0 * y) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp [quadraticJetExtensionDeriv, hy.le]
    have hval : quadraticJetExtensionSecond f'' x = f'' 0 := by
      simp [quadraticJetExtensionSecond, hx.le]
    rw [hval]
    exact (hasDerivAt_leftLinear f' f'' x).congr_of_eventuallyEq hext
  · have hleft : HasDerivWithinAt (quadraticJetExtensionDeriv f' f'')
        (f'' 0) (Iic (0 : ℝ)) 0 := by
      apply (hasDerivAt_leftLinear f' f'' 0).hasDerivWithinAt.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : y ≤ 0 := hy
        simp [quadraticJetExtensionDeriv, hy']
      · simp [quadraticJetExtensionDeriv]
    have hright : HasDerivWithinAt (quadraticJetExtensionDeriv f' f'')
        (f'' 0) (Ici (0 : ℝ)) 0 := by
      apply hf'0.congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin,
          (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left]
          with y hy0 hy1
        have hy0' : 0 ≤ y := hy0
        rcases eq_or_lt_of_le hy0' with rfl | hy0
        · simp [quadraticJetExtensionDeriv]
        · simp [quadraticJetExtensionDeriv, hy0.not_le, hy1.le]
      · simp [quadraticJetExtensionDeriv]
    have h := hleft.union hright
    simpa [quadraticJetExtensionSecond] using h
  · rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · have hext : quadraticJetExtensionDeriv f' f'' =ᶠ[𝓝 x] f' := by
        filter_upwards [eventually_gt_nhds hx, eventually_lt_nhds hx1] with y hy0 hy1
        simp [quadraticJetExtensionDeriv, hy0.not_le, hy1.le]
      have hval : quadraticJetExtensionSecond f'' x = f'' x := by
        simp [quadraticJetExtensionSecond, hx.not_le, hx1.le]
      rw [hval]
      exact (hf' x ⟨hx, hx1⟩).congr_of_eventuallyEq hext
    · have hleft : HasDerivWithinAt (quadraticJetExtensionDeriv f' f'')
          (f'' 1) (Iic (1 : ℝ)) 1 := by
        apply hf'1.congr_of_eventuallyEq
        · filter_upwards [self_mem_nhdsWithin,
            (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left]
            with y hy1 hy0
          have hy1' : y ≤ 1 := hy1
          rcases eq_or_lt_of_le hy1' with rfl | hy1
          · simp [quadraticJetExtensionDeriv]
          · simp [quadraticJetExtensionDeriv, hy0.not_le, hy1.le]
        · simp [quadraticJetExtensionDeriv]
      have hright : HasDerivWithinAt (quadraticJetExtensionDeriv f' f'')
          (f'' 1) (Ici (1 : ℝ)) 1 := by
        apply (hasDerivAt_rightLinear f' f'' 1).hasDerivWithinAt.congr_of_eventuallyEq
        · filter_upwards [self_mem_nhdsWithin] with y hy
          have hy' : 1 ≤ y := hy
          rcases hy'.eq_or_lt with rfl | hy
          · simp [quadraticJetExtensionDeriv]
          · simp [quadraticJetExtensionDeriv, hy.not_le, show ¬ y ≤ 0 by linarith]
        · simp [quadraticJetExtensionDeriv]
      have h := hleft.union hright
      norm_num [quadraticJetExtensionSecond]
      have huniv : Iic (1 : ℝ) ∪ Ici 1 = univ := Iic_union_Ici
      rw [huniv] at h
      exact hasDerivWithinAt_univ.mp h
    · have hext : quadraticJetExtensionDeriv f' f'' =ᶠ[𝓝 x]
          (fun y : ℝ => f' 1 + f'' 1 * (y - 1)) := by
        filter_upwards [eventually_gt_nhds hx1] with y hy
        simp [quadraticJetExtensionDeriv, hy.not_le, show ¬ y ≤ 0 by linarith]
      have hval : quadraticJetExtensionSecond f'' x = f'' 1 := by
        simp [quadraticJetExtensionSecond, hx1.not_le, show ¬ x ≤ 0 by linarith]
      rw [hval]
      exact (hasDerivAt_rightLinear f' f'' x).congr_of_eventuallyEq hext

theorem quadraticJetExtensionSecond_continuousOn
    (f'' : ℝ → ℝ) (hf'' : ContinuousOn f'' (Icc (0 : ℝ) 1)) :
    ContinuousOn (quadraticJetExtensionSecond f'') (Icc (0 : ℝ) 1) := by
  intro x hx
  apply (hf'' x hx).congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact quadraticJetExtensionSecond_eq f'' hy
  · exact quadraticJetExtensionSecond_eq f'' hx

/-- Package local two-jet data on `[0,1]` into the global extension fields
required by `EndpointResidualData`.  Thus an application only needs one-sided
endpoint derivatives, not a separately constructed global `C²` function. -/
noncomputable def endpointResidualDataOfLocalTwoJet
    (α : ℝ) (f f' f'' f''' : ℝ → ℝ)
    (heq : ∀ x ∈ Icc (0 : ℝ) 1, f x = circleEndpointResidual α x)
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf0 : HasDerivWithinAt f (f' 0) (Ici (0 : ℝ)) 0)
    (hf1 : HasDerivWithinAt f (f' 1) (Iic (1 : ℝ)) 1)
    (hf' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f' (f'' x) x)
    (hf'0 : HasDerivWithinAt f' (f'' 0) (Ici (0 : ℝ)) 0)
    (hf'1 : HasDerivWithinAt f' (f'' 1) (Iic (1 : ℝ)) 1)
    (hf''cont : ContinuousOn f'' (Icc (0 : ℝ) 1))
    (hf'' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f'' (f''' x) x)
    (hf'''int : IntervalIntegrable f''' MeasureTheory.volume (0 : ℝ) 1)
    (hend : f' 1 = f' 0) : EndpointResidualData α where
  g := quadraticJetExtension f f' f''
  deriv1 := quadraticJetExtensionDeriv f' f''
  deriv2 := quadraticJetExtensionSecond f''
  deriv3 := f'''
  eqOn x hx := (quadraticJetExtension_eq f f' f'' hx).trans (heq x hx)
  hasDeriv := quadraticJetExtension_hasDerivAt f f' f'' hf hf0 hf1
  hasDeriv' := quadraticJetExtensionDeriv_hasDerivAt f' f'' hf' hf'0 hf'1
  continuousOn_second := quadraticJetExtensionSecond_continuousOn f'' hf''cont
  hasDeriv_second := by
    intro x hx
    have hext : quadraticJetExtensionSecond f'' =ᶠ[𝓝 x] f'' := by
      filter_upwards [eventually_gt_nhds hx.1, eventually_lt_nhds hx.2] with y hy0 hy1
      exact quadraticJetExtensionSecond_eq f'' ⟨hy0.le, hy1.le⟩
    exact (hf'' x hx).congr_of_eventuallyEq hext
  third_integrable := hf'''int
  deriv_endpoints := by
    rw [quadraticJetExtensionDeriv_eq f' f''
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num),
      quadraticJetExtensionDeriv_eq f' f''
        (show (0 : ℝ) ∈ Icc 0 1 by norm_num)]
    exact hend

end BEMOC.CircleGeneral.EndpointExtension
