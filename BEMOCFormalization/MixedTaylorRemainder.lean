import BEMOCFormalization.LatitudeSmoothOppositeBlocks
import Mathlib.Analysis.Calculus.Taylor

/-!
# Tensor Taylor remainders on a rectangle

This module supplies the missing analytic bridge between a uniform mixed
`(2,2)` derivative bound and the biaffine remainder interfaces used by the
latitude block estimates.

We first remove the degree-one Taylor polynomial in the first variable.
From that error we remove its degree-one Taylor polynomial in the second
variable.  The resulting tensor remainder is invisible to neither
two-moment rule, while both discarded terms are affine in one variable.
Two applications of `taylor_mean_remainder_bound` give the product of the
squared side lengths.

The sole commutation hypothesis says that differentiating the first Taylor
error twice in the second variable gives the first Taylor error of
`K_{tt}`.  It is deliberately stated as an equality of
`iteratedDerivWithin`: concrete smooth kernels discharge it from their
explicit derivative chains, without requiring a new multivariable calculus
framework.
-/

open MeasureTheory Set

namespace BEMOC

/-- The error after removing the degree-one Taylor polynomial in `s`,
anchored at the left endpoint `a`. -/
noncomputable def firstTaylorError
    (K : ℝ → ℝ → ℝ) (I : Set ℝ) (a s t : ℝ) : ℝ :=
  K s t - taylorWithinEval (fun x ↦ K x t) 1 I a s

/-- The tensor `(1,1)` Taylor remainder: first remove the affine Taylor
polynomial in `s`, then remove the affine Taylor polynomial in `t` from the
resulting error. -/
noncomputable def mixedTaylorRemainder
    (K : ℝ → ℝ → ℝ) (Is It : Set ℝ) (a c s t : ℝ) : ℝ :=
  firstTaylorError K Is a s t -
    taylorWithinEval (firstTaylorError K Is a s) 1 It c t

/-- Coefficient of `t` in the second Taylor polynomial. -/
noncomputable def mixedTaylorRightSlope
    (K : ℝ → ℝ → ℝ) (Is It : Set ℝ) (a c s : ℝ) : ℝ :=
  derivWithin (firstTaylorError K Is a s) It c

/-- Constant coefficient in the second Taylor polynomial. -/
noncomputable def mixedTaylorRightIntercept
    (K : ℝ → ℝ → ℝ) (Is It : Set ℝ) (a c s : ℝ) : ℝ :=
  firstTaylorError K Is a s c -
    c * mixedTaylorRightSlope K Is It a c s

/-- Coefficient of `s` in the first Taylor polynomial. -/
noncomputable def mixedTaylorLeftSlope
    (K : ℝ → ℝ → ℝ) (Is : Set ℝ) (a t : ℝ) : ℝ :=
  derivWithin (fun x ↦ K x t) Is a

/-- Constant coefficient in the first Taylor polynomial. -/
noncomputable def mixedTaylorLeftIntercept
    (K : ℝ → ℝ → ℝ) (Is : Set ℝ) (a t : ℝ) : ℝ :=
  K a t - a * mixedTaylorLeftSlope K Is a t

/-- Exact biaffine decomposition associated with the tensor Taylor
remainder.  No differentiability is needed for this algebraic identity. -/
theorem mixedTaylor_decomposition
    (K : ℝ → ℝ → ℝ) (Is It : Set ℝ) (a c s t : ℝ) :
    K s t =
      mixedTaylorRemainder K Is It a c s t +
        (mixedTaylorRightSlope K Is It a c s * t +
          mixedTaylorRightIntercept K Is It a c s) +
        (mixedTaylorLeftSlope K Is a t * s +
          mixedTaylorLeftIntercept K Is a t) := by
  have hs :
      taylorWithinEval (fun x ↦ K x t) 1 Is a s =
        K a t + (s - a) * derivWithin (fun x ↦ K x t) Is a := by
    simpa using taylorWithinEval_succ (fun x ↦ K x t) 0 Is a s
  have ht :
      taylorWithinEval (firstTaylorError K Is a s) 1 It c t =
        firstTaylorError K Is a s c +
          (t - c) * derivWithin (firstTaylorError K Is a s) It c := by
    simpa using
      taylorWithinEval_succ (firstTaylorError K Is a s) 0 It c t
  unfold mixedTaylorRemainder
  rw [ht]
  unfold mixedTaylorRightIntercept mixedTaylorRightSlope
    mixedTaylorLeftIntercept mixedTaylorLeftSlope
  unfold firstTaylorError
  rw [hs]
  ring

/-- A uniform `(2,2)` bound gives a product-side-length bound for the
tensor Taylor remainder.

`Ktt` denotes the second derivative in the second variable.  `hcommute`
is the concrete derivative-chain fact that the second `t` derivative of
the first `s` Taylor error is the first `s` Taylor error of `Ktt`. -/
theorem abs_mixedTaylorRemainder_le
    (K Ktt : ℝ → ℝ → ℝ)
    {a b c d C : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hC : 0 ≤ C)
    (hKtt : ∀ t ∈ Icc c d,
      ContDiffOn ℝ 2 (fun s ↦ Ktt s t) (Icc a b))
    (hmixed : ∀ t ∈ Icc c d, ∀ s ∈ Icc a b,
      ‖iteratedDerivWithin 2 (fun x ↦ Ktt x t) (Icc a b) s‖ ≤ C)
    (herror : ∀ s ∈ Icc a b,
      ContDiffOn ℝ 2 (firstTaylorError K (Icc a b) a s) (Icc c d))
    (hcommute : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d,
      iteratedDerivWithin 2
          (firstTaylorError K (Icc a b) a s) (Icc c d) t =
        Ktt s t -
          taylorWithinEval (fun x ↦ Ktt x t) 1 (Icc a b) a s)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc c d) :
    |mixedTaylorRemainder K (Icc a b) (Icc c d) a c s t| ≤
      C * (b - a) ^ 2 * (d - c) ^ 2 := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hdc : 0 ≤ d - c := sub_nonneg.mpr hcd
  have hs_sub : 0 ≤ s - a := sub_nonneg.mpr hs.1
  have hs_width : s - a ≤ b - a := by linarith [hs.2]
  have ht_sub : 0 ≤ t - c := sub_nonneg.mpr ht.1
  have ht_width : t - c ≤ d - c := by linarith [ht.2]
  have hsecond : ∀ y ∈ Icc c d,
      ‖iteratedDerivWithin 2
          (firstTaylorError K (Icc a b) a s) (Icc c d) y‖ ≤
        C * (b - a) ^ 2 := by
    intro y hy
    rw [hcommute s hs y hy]
    have hTaylor := taylor_mean_remainder_bound
      (f := fun x ↦ Ktt x y) (n := 1)
      hab (hKtt y hy) hs (hmixed y hy)
    have hformula :
        taylorWithinEval (fun x ↦ Ktt x y) 1 (Icc a b) a s =
          Ktt a y + (s - a) *
            derivWithin (fun x ↦ Ktt x y) (Icc a b) a := by
      simpa using
        taylorWithinEval_succ (fun x ↦ Ktt x y) 0 (Icc a b) a s
    rw [show (1 : ℕ) + 1 = 2 by norm_num] at hTaylor
    norm_num at hTaylor
    calc
      ‖Ktt s y -
          taylorWithinEval (fun x ↦ Ktt x y) 1 (Icc a b) a s‖ =
          |Ktt s y -
            taylorWithinEval (fun x ↦ Ktt x y) 1 (Icc a b) a s| := by
              rw [Real.norm_eq_abs]
      _ ≤ C * (s - a) ^ 2 := by
        rw [hformula]
        exact hTaylor
      _ ≤ C * (b - a) ^ 2 := by
        gcongr
  have houter := taylor_mean_remainder_bound
    (f := firstTaylorError K (Icc a b) a s) (n := 1)
    hcd (herror s hs) ht hsecond
  rw [show (1 : ℕ) + 1 = 2 by norm_num] at houter
  norm_num at houter
  have hformula :
      taylorWithinEval (firstTaylorError K (Icc a b) a s)
          1 (Icc c d) c t =
        firstTaylorError K (Icc a b) a s c +
          (t - c) * derivWithin
            (firstTaylorError K (Icc a b) a s) (Icc c d) c := by
    simpa using taylorWithinEval_succ
      (firstTaylorError K (Icc a b) a s) 0 (Icc c d) c t
  unfold mixedTaylorRemainder
  calc
    |firstTaylorError K (Icc a b) a s t -
        taylorWithinEval (firstTaylorError K (Icc a b) a s)
          1 (Icc c d) c t| =
        ‖firstTaylorError K (Icc a b) a s t -
          taylorWithinEval (firstTaylorError K (Icc a b) a s)
            1 (Icc c d) c t‖ := by
              rw [Real.norm_eq_abs]
    _ ≤ (C * (b - a) ^ 2) * (t - c) ^ 2 := by
      rw [hformula]
      exact houter
    _ ≤ C * (b - a) ^ 2 * (d - c) ^ 2 := by
      gcongr

/-- Right-variable-first version of `firstTaylorError`.  This orientation
matches the latitude derivative chain, which first forms `K_{ss}` and then
differentiates twice in `t`. -/
noncomputable def firstRightTaylorError
    (K : ℝ → ℝ → ℝ) (It : Set ℝ) (c s t : ℝ) : ℝ :=
  K s t - taylorWithinEval (K s) 1 It c t

/-- Right-variable-first tensor Taylor remainder. -/
noncomputable def mixedTaylorRemainderRightFirst
    (K : ℝ → ℝ → ℝ) (Is It : Set ℝ) (a c s t : ℝ) : ℝ :=
  mixedTaylorRemainder (fun y x ↦ K x y) It Is c a t s

theorem firstRightTaylorError_eq_transpose
    (K : ℝ → ℝ → ℝ) (It : Set ℝ) (c s t : ℝ) :
    firstRightTaylorError K It c s t =
      firstTaylorError (fun y x ↦ K x y) It c t s := by
  rfl

/-- The tensor bound in the orientation used by the actual latitude
kernel: `Kss` is the second `s` derivative, and `hmixed` bounds its second
`t` derivative. -/
theorem abs_mixedTaylorRemainderRightFirst_le
    (K Kss : ℝ → ℝ → ℝ)
    {a b c d C : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hC : 0 ≤ C)
    (hKss : ∀ s ∈ Icc a b,
      ContDiffOn ℝ 2 (Kss s) (Icc c d))
    (hmixed : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d,
      ‖iteratedDerivWithin 2 (Kss s) (Icc c d) t‖ ≤ C)
    (herror : ∀ t ∈ Icc c d,
      ContDiffOn ℝ 2
        (fun s ↦ firstRightTaylorError K (Icc c d) c s t)
        (Icc a b))
    (hcommute : ∀ t ∈ Icc c d, ∀ s ∈ Icc a b,
      iteratedDerivWithin 2
          (fun x ↦ firstRightTaylorError K (Icc c d) c x t)
          (Icc a b) s =
        Kss s t -
          taylorWithinEval (Kss s) 1 (Icc c d) c t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc c d) :
    |mixedTaylorRemainderRightFirst K
        (Icc a b) (Icc c d) a c s t| ≤
      C * (b - a) ^ 2 * (d - c) ^ 2 := by
  have hmain := abs_mixedTaylorRemainder_le
    (fun y x ↦ K x y) (fun y x ↦ Kss x y)
    hcd hab hC
    (fun x hx ↦ hKss x hx)
    (fun x hx y hy ↦ hmixed x hx y hy)
    (fun y hy ↦ by
      simpa only [firstRightTaylorError_eq_transpose] using herror y hy)
    (fun y hy x hx ↦ by
      simpa only [firstRightTaylorError_eq_transpose] using
        hcommute y hy x hx)
    ht hs
  unfold mixedTaylorRemainderRightFirst
  calc
    |mixedTaylorRemainder (fun y x ↦ K x y)
        (Icc c d) (Icc a b) c a t s| ≤
      C * (d - c) ^ 2 * (b - a) ^ 2 := hmain
    _ = C * (b - a) ^ 2 * (d - c) ^ 2 := by ring

/-- Abstract paired-rule consequence of the tensor Taylor construction. -/
theorem TwoMomentFunctional.abs_pairEval_le_of_mixedDerivative
    (L₁ L₂ : TwoMomentFunctional) (K Ktt : ℝ → ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hKtt : ∀ t ∈ Icc L₂.a L₂.b,
      ContDiffOn ℝ 2 (fun s ↦ Ktt s t) (Icc L₁.a L₁.b))
    (hmixed : ∀ t ∈ Icc L₂.a L₂.b, ∀ s ∈ Icc L₁.a L₁.b,
      ‖iteratedDerivWithin 2 (fun x ↦ Ktt x t)
          (Icc L₁.a L₁.b) s‖ ≤ C)
    (herror : ∀ s ∈ Icc L₁.a L₁.b,
      ContDiffOn ℝ 2
        (firstTaylorError K (Icc L₁.a L₁.b) L₁.a s)
        (Icc L₂.a L₂.b))
    (hcommute : ∀ s ∈ Icc L₁.a L₁.b, ∀ t ∈ Icc L₂.a L₂.b,
      iteratedDerivWithin 2
          (firstTaylorError K (Icc L₁.a L₁.b) L₁.a s)
          (Icc L₂.a L₂.b) t =
        Ktt s t -
          taylorWithinEval (fun x ↦ Ktt x t) 1
            (Icc L₁.a L₁.b) L₁.a s) :
    |L₁.pairEval L₂ K| ≤
      L₁.variation * L₂.variation * C *
        L₁.width ^ 2 * L₂.width ^ 2 := by
  apply L₁.abs_pairEval_le_of_biaffine_mixedRemainder L₂ K
    (fun s t ↦ mixedTaylorRemainder K
      (Icc L₁.a L₁.b) (Icc L₂.a L₂.b) L₁.a L₂.a s t)
    (mixedTaylorRightSlope K (Icc L₁.a L₁.b)
      (Icc L₂.a L₂.b) L₁.a L₂.a)
    (mixedTaylorRightIntercept K (Icc L₁.a L₁.b)
      (Icc L₂.a L₂.b) L₁.a L₂.a)
    (mixedTaylorLeftSlope K (Icc L₁.a L₁.b) L₁.a)
    (mixedTaylorLeftIntercept K (Icc L₁.a L₁.b) L₁.a)
    C hC
  · intro s t
    exact mixedTaylor_decomposition K
      (Icc L₁.a L₁.b) (Icc L₂.a L₂.b) L₁.a L₂.a s t
  · intro s hs t ht
    exact abs_mixedTaylorRemainder_le K Ktt
      L₁.a_le_b L₂.a_le_b hC hKtt hmixed herror hcommute hs ht

/-- Concrete BEMOC-band consequence.  The derivative hypotheses now
produce the full biaffine remainder and its sharp
`bandWidth² * bandWidth²` bound; only the standard interval-integrability
facts for the explicit Taylor terms are requested from the application. -/
theorem abs_bandPairError_le_of_mixedDerivative
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (K Ktt : ℝ → ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hKtt : ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
      ContDiffOn ℝ 2 (fun s ↦ Ktt s t)
        (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j)))
    (hmixed : ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ‖iteratedDerivWithin 2 (fun x ↦ Ktt x t)
          (Icc (bandBoundaryHeight N (j + 1))
            (bandBoundaryHeight N j)) s‖ ≤ C)
    (herror : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ContDiffOn ℝ 2
        (firstTaylorError K
          (Icc (bandBoundaryHeight N (j + 1))
            (bandBoundaryHeight N j))
          (bandBoundaryHeight N (j + 1)) s)
        (Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)))
    (hcommute : ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j),
      ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k),
      iteratedDerivWithin 2
          (firstTaylorError K
            (Icc (bandBoundaryHeight N (j + 1))
              (bandBoundaryHeight N j))
            (bandBoundaryHeight N (j + 1)) s)
          (Icc (bandBoundaryHeight N (k + 1))
            (bandBoundaryHeight N k)) t =
        Ktt s t -
          taylorWithinEval (fun x ↦ Ktt x t) 1
            (Icc (bandBoundaryHeight N (j + 1))
              (bandBoundaryHeight N j))
            (bandBoundaryHeight N (j + 1)) s)
    (hR : ∀ s, IntervalIntegrable
      (fun t ↦ mixedTaylorRemainder K
        (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j))
        (Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k))
        (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N (k + 1)) s t)
      volume (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k))
    (hOuterR : IntervalIntegrable
      (fun s ↦ bandError N k (fun t ↦ mixedTaylorRemainder K
        (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j))
        (Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k))
        (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N (k + 1)) s t))
      volume (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j))
    (huLeft : IntervalIntegrable
      (mixedTaylorLeftSlope K
        (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j))
        (bandBoundaryHeight N (j + 1)))
      volume (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k))
    (hvLeft : IntervalIntegrable
      (mixedTaylorLeftIntercept K
        (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j))
        (bandBoundaryHeight N (j + 1)))
      volume (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)) :
    |bandPairError N j k K| ≤
      64 * C * (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  let Is : Set ℝ := Icc (bandBoundaryHeight N (j + 1))
    (bandBoundaryHeight N j)
  let It : Set ℝ := Icc (bandBoundaryHeight N (k + 1))
    (bandBoundaryHeight N k)
  let a : ℝ := bandBoundaryHeight N (j + 1)
  let c : ℝ := bandBoundaryHeight N (k + 1)
  let R : ℝ → ℝ → ℝ := fun s t ↦
    mixedTaylorRemainder K Is It a c s t
  apply abs_bandPairError_le_of_biaffine_mixed_remainder hN j k K R
    (mixedTaylorRightSlope K Is It a c)
    (mixedTaylorRightIntercept K Is It a c)
    (mixedTaylorLeftSlope K Is a)
    (mixedTaylorLeftIntercept K Is a)
    C hC
  · exact hR
  · exact hOuterR
  · exact huLeft
  · exact hvLeft
  · intro s t
    exact mixedTaylor_decomposition K Is It a c s t
  · intro s hs t ht
    change |mixedTaylorRemainder K Is It a c s t| ≤
      C * bandWidth N j ^ 2 * bandWidth N k ^ 2
    have hmain := abs_mixedTaylorRemainder_le K Ktt
      (bandBoundaryHeight_succ_le j)
      (bandBoundaryHeight_succ_le k) hC
      hKtt hmixed herror hcommute hs ht
    simpa [Is, It, a, c, bandWidth] using hmain

end BEMOC
