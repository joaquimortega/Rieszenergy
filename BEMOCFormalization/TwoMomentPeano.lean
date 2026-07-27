import Mathlib.Analysis.Calculus.Taylor

/-!
# Abstract two-moment Peano estimates

This file is deliberately independent of the BEMOC construction.  It
packages the only properties of a one-dimensional quadrature error used in
the latitude argument: linearity, annihilation of affine functions, and a
total-variation bound on a support interval.  The resulting theorems can be
instantiated by a signed atomic-minus-continuous band measure.

The one-variable theorem is a direct application of mathlib's Taylor bound.
The two-variable theorem is its fixed-rectangle counterpart: it accepts the
mixed fourth-order remainder after the affine-in-each-variable terms have
been removed.  This is the form which remains useful on a diagonal cusp,
where a pointwise fourth derivative need not be bounded.
-/

open Set

namespace BEMOC

/-- An abstract signed quadrature functional with zero zeroth and first
moments.  `variation` is a total-variation-style bound on the interval
`[a,b]`. -/
structure TwoMomentFunctional where
  a : ℝ
  b : ℝ
  a_le_b : a ≤ b
  eval : (ℝ → ℝ) → ℝ
  map_add : ∀ (f g : ℝ → ℝ), eval (fun x ↦ f x + g x) = eval f + eval g
  map_smul : ∀ (c : ℝ) (f : ℝ → ℝ), eval (fun x ↦ c * f x) = c * eval f
  const_zero : ∀ c : ℝ, eval (fun _ ↦ c) = 0
  id_zero : eval id = 0
  variation : ℝ
  variation_nonneg : 0 ≤ variation
  abs_eval_le : ∀ (f : ℝ → ℝ) (C : ℝ), 0 ≤ C →
    (∀ (x : ℝ), x ∈ Icc a b → |f x| ≤ C) → |eval f| ≤ variation * C

namespace TwoMomentFunctional

/-- Width of the support interval of an abstract rule. -/
noncomputable def width (L : TwoMomentFunctional) : ℝ := L.b - L.a

theorem width_nonneg (L : TwoMomentFunctional) : 0 ≤ L.width := by
  exact sub_nonneg.mpr L.a_le_b

theorem eval_sub (L : TwoMomentFunctional) (f g : ℝ → ℝ) :
    L.eval (fun x ↦ f x - g x) = L.eval f - L.eval g := by
  rw [show (fun x ↦ f x - g x) = fun x ↦ f x + (-1 : ℝ) * g x by
    funext x; ring, L.map_add, L.map_smul]
  ring

/-- Every affine function is killed by a two-moment rule. -/
theorem affine_zero (L : TwoMomentFunctional) (a b : ℝ) :
    L.eval (fun x ↦ a * x + b) = 0 := by
  rw [show (fun x ↦ a * x + b) = fun x ↦ a * id x + (fun _ ↦ b) x by rfl,
    L.map_add, L.map_smul, L.id_zero, L.const_zero]
  ring

/-- The degree-one Taylor polynomial is affine, hence is invisible to the
rule. -/
theorem taylor_one_zero (L : TwoMomentFunctional) (f : ℝ → ℝ) :
    L.eval (fun x ↦ taylorWithinEval f 1 (Icc L.a L.b) L.a x) = 0 := by
  have hformula : ∀ x : ℝ,
      taylorWithinEval f 1 (Icc L.a L.b) L.a x =
        f L.a + (x - L.a) * derivWithin f (Icc L.a L.b) L.a := by
    intro x
    simpa using taylorWithinEval_succ f 0 (Icc L.a L.b) L.a x
  rw [show (fun x ↦ taylorWithinEval f 1 (Icc L.a L.b) L.a x) =
      fun x ↦ f L.a + (x - L.a) * derivWithin f (Icc L.a L.b) L.a by
        funext x; exact hformula x]
  let d : ℝ := derivWithin f (Icc L.a L.b) L.a
  change L.eval (fun x ↦ f L.a + (x - L.a) * d) = 0
  rw [show (fun x ↦ f L.a + (x - L.a) * d) =
      fun x ↦ d * x + (f L.a - d * L.a) by
        funext x; ring]
  exact L.affine_zero d (f L.a - d * L.a)

/-- A two-moment rule gains two powers of the support width from a bounded
second derivative.  This is the abstract one-band Peano estimate. -/
theorem abs_eval_le_of_secondDerivative
    (L : TwoMomentFunctional) (f : ℝ → ℝ) (C : ℝ)
    (hf : ContDiffOn ℝ 2 f (Icc L.a L.b))
    (hC : 0 ≤ C)
    (hderiv : ∀ x ∈ Icc L.a L.b,
      ‖iteratedDerivWithin 2 f (Icc L.a L.b) x‖ ≤ C) :
    |L.eval f| ≤ L.variation * C * L.width ^ 2 := by
  let T : ℝ → ℝ := fun x ↦ taylorWithinEval f 1 (Icc L.a L.b) L.a x
  let R : ℝ → ℝ := fun x ↦ f x - T x
  have hT : L.eval T = 0 := by
    exact L.taylor_one_zero f
  have hR_eval : L.eval R = L.eval f := by
    rw [show R = fun x ↦ f x - T x by rfl, L.eval_sub, hT, sub_zero]
  have hwidthsq : 0 ≤ L.width ^ 2 := sq_nonneg _
  have hformula : ∀ x : ℝ,
      taylorWithinEval f 1 (Icc L.a L.b) L.a x =
        f L.a + (x - L.a) * derivWithin f (Icc L.a L.b) L.a := by
    intro x
    simpa using taylorWithinEval_succ f 0 (Icc L.a L.b) L.a x
  have hbound : ∀ x ∈ Icc L.a L.b, |R x| ≤ C * L.width ^ 2 := by
    intro x hx
    have hTaylor := taylor_mean_remainder_bound (f := f) (n := 1)
      L.a_le_b hf hx hderiv
    have hxa : 0 ≤ x - L.a := sub_nonneg.mpr hx.1
    have hxab : x - L.a ≤ L.width := by
      dsimp [width]
      linarith [hx.2]
    rw [show (1 : ℕ) + 1 = 2 by norm_num] at hTaylor
    norm_num at hTaylor
    dsimp [R, T]
    rw [hformula x]
    calc
      _ ≤ C * (x - L.a) ^ 2 := hTaylor
      _ ≤ C * L.width ^ 2 := by
        gcongr
  have hmain := L.abs_eval_le R (C * L.width ^ 2)
    (mul_nonneg hC hwidthsq) hbound
  rw [hR_eval] at hmain
  nlinarith

/-- Public one-band name for the abstract second-derivative Peano estimate. -/
theorem bandError_le_of_secondDerivative
    (L : TwoMomentFunctional) (f : ℝ → ℝ) (C : ℝ)
    (hf : ContDiffOn ℝ 2 f (Icc L.a L.b))
    (hC : 0 ≤ C)
    (hderiv : ∀ x ∈ Icc L.a L.b,
      ‖iteratedDerivWithin 2 f (Icc L.a L.b) x‖ ≤ C) :
    |L.eval f| ≤ L.variation * C * L.width ^ 2 :=
  abs_eval_le_of_secondDerivative L f C hf hC hderiv

/-- The product of two two-moment rules, written in the nesting convention
used by `bandPairError`. -/
noncomputable def pairEval (L₁ L₂ : TwoMomentFunctional) (K : ℝ → ℝ → ℝ) : ℝ :=
  L₁.eval (fun s ↦ L₂.eval (fun t ↦ K s t))

theorem pairEval_add (L₁ L₂ : TwoMomentFunctional)
    (K R : ℝ → ℝ → ℝ) :
    pairEval L₁ L₂ (fun s t ↦ K s t + R s t) =
      pairEval L₁ L₂ K + pairEval L₁ L₂ R := by
  unfold pairEval
  rw [show (fun s ↦ L₂.eval (fun t ↦ K s t + R s t)) =
      fun s ↦ L₂.eval (K s) + L₂.eval (R s) by
        funext s
        exact L₂.map_add (K s) (R s)]
  exact L₁.map_add _ _

/-- A kernel affine in the second variable is killed by the paired rule.
The coefficients may vary arbitrarily in the first variable. -/
theorem pairEval_affine_right (L₁ L₂ : TwoMomentFunctional)
    (u v : ℝ → ℝ) :
    pairEval L₁ L₂ (fun s t ↦ u s * t + v s) = 0 := by
  unfold pairEval
  have hinner : (fun s ↦ L₂.eval (fun t ↦ u s * t + v s)) = fun _ ↦ 0 := by
    funext s
    exact L₂.affine_zero (u s) (v s)
  rw [hinner, L₁.const_zero]

/-- A kernel affine in the first variable is killed as well; its
coefficients may vary arbitrarily in the second variable. -/
theorem pairEval_affine_left (L₁ L₂ : TwoMomentFunctional)
    (u v : ℝ → ℝ) :
    pairEval L₁ L₂ (fun s t ↦ u t * s + v t) = 0 := by
  unfold pairEval
  have hinner :
      (fun s ↦ L₂.eval (fun t ↦ u t * s + v t)) =
        fun s ↦ (L₂.eval u) * s + L₂.eval v := by
    funext s
    rw [show (fun t ↦ u t * s + v t) =
        fun t ↦ s * u t + v t by funext t; ring,
      L₂.map_add, L₂.map_smul]
    ring_nf
  rw [hinner]
  exact L₁.affine_zero (L₂.eval u) (L₂.eval v)

/-- Fixed-rectangle mixed Peano estimate.  The hypothesis supplies the
mixed fourth-order remainder `R`; the discarded part is affine in `t` and
therefore vanishes under the inner two-moment rule.  The conclusion is
exactly the `width_s² width_t²` gain needed for rescaled cusp rectangles. -/
theorem abs_pairEval_le_of_mixedFourthRemainder
    (L₁ L₂ : TwoMomentFunctional) (K R : ℝ → ℝ → ℝ)
    (u v : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hdecomp : ∀ s t, K s t = R s t + (u s * t + v s))
    (hbound : ∀ s ∈ Icc L₁.a L₁.b, ∀ t ∈ Icc L₂.a L₂.b,
      |R s t| ≤ C * L₁.width ^ 2 * L₂.width ^ 2) :
    |pairEval L₁ L₂ K| ≤
      L₁.variation * L₂.variation * C * L₁.width ^ 2 * L₂.width ^ 2 := by
  have hsq₁ : 0 ≤ L₁.width ^ 2 := sq_nonneg _
  have hsq₂ : 0 ≤ L₂.width ^ 2 := sq_nonneg _
  have hD : 0 ≤ L₂.variation * C * L₁.width ^ 2 * L₂.width ^ 2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg L₂.variation_nonneg hC) hsq₁) hsq₂
  -- Restrict the preceding inner estimate to the outer support, where its
  -- hypothesis is available, and use the two variation estimates in turn.
  have hinnerOn : ∀ s ∈ Icc L₁.a L₁.b,
      |L₂.eval (fun t ↦ R s t)| ≤
        L₂.variation * C * L₁.width ^ 2 * L₂.width ^ 2 := by
    intro s hs
    have hb : ∀ t ∈ Icc L₂.a L₂.b,
        |R s t| ≤ C * L₁.width ^ 2 * L₂.width ^ 2 := fun t ht ↦ hbound s hs t ht
    have := L₂.abs_eval_le (fun t ↦ R s t)
      (C * L₁.width ^ 2 * L₂.width ^ 2) (by positivity) hb
    nlinarith
  have houter := L₁.abs_eval_le (fun s ↦ L₂.eval (fun t ↦ R s t))
    (L₂.variation * C * L₁.width ^ 2 * L₂.width ^ 2) hD hinnerOn
  have heq : pairEval L₁ L₂ K = pairEval L₁ L₂ R := by
    unfold pairEval
    congr 1
    funext s
    rw [show (fun t ↦ K s t) = fun t ↦ R s t + (u s * t + v s) by
      funext t; exact hdecomp s t,
      L₂.map_add, L₂.affine_zero]
    ring
  rw [heq]
  calc
    _ ≤ L₁.variation * (L₂.variation * C * L₁.width ^ 2 * L₂.width ^ 2) := houter
    _ = _ := by ring

/-- Bilinear Taylor form of the mixed Peano estimate.  In addition to a
remainder, one may discard a term affine in the second variable and a term
affine in the first variable.  This is the full nullspace needed to obtain
both width gains from a mixed `(2,2)` Taylor expansion. -/
theorem abs_pairEval_le_of_biaffine_mixedRemainder
    (L₁ L₂ : TwoMomentFunctional) (K R : ℝ → ℝ → ℝ)
    (uRight vRight uLeft vLeft : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hdecomp : ∀ s t, K s t =
      R s t + (uRight s * t + vRight s) +
        (uLeft t * s + vLeft t))
    (hbound : ∀ s ∈ Icc L₁.a L₁.b, ∀ t ∈ Icc L₂.a L₂.b,
      |R s t| ≤ C * L₁.width ^ 2 * L₂.width ^ 2) :
    |pairEval L₁ L₂ K| ≤
      L₁.variation * L₂.variation * C *
        L₁.width ^ 2 * L₂.width ^ 2 := by
  have hpair :
      pairEval L₁ L₂ K = pairEval L₁ L₂ R := by
    rw [show K = fun s t ↦
        (R s t + (uRight s * t + vRight s)) +
          (uLeft t * s + vLeft t) by
      funext s t
      exact hdecomp s t]
    rw [pairEval_add, pairEval_add,
      pairEval_affine_right, pairEval_affine_left]
    ring
  rw [hpair]
  have hzeroRight : ∀ s t, R s t =
      R s t + ((0 : ℝ) * t + 0) := by
    intro s t
    ring
  exact abs_pairEval_le_of_mixedFourthRemainder
    L₁ L₂ R R (fun _ ↦ 0) (fun _ ↦ 0) C
      hC hzeroRight hbound

/-- Public two-band name for the fixed-rectangle mixed Peano estimate.
Applications discharge `hdecomp` using a mixed fourth-derivative Taylor
formula off the diagonal, or directly by a scaled cusp remainder bound. -/
theorem bandPairError_le_of_mixedFourthDerivative
    (L₁ L₂ : TwoMomentFunctional) (K R : ℝ → ℝ → ℝ)
    (u v : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hdecomp : ∀ s t, K s t = R s t + (u s * t + v s))
    (hbound : ∀ s ∈ Icc L₁.a L₁.b, ∀ t ∈ Icc L₂.a L₂.b,
      |R s t| ≤ C * L₁.width ^ 2 * L₂.width ^ 2) :
    |pairEval L₁ L₂ K| ≤
      L₁.variation * L₂.variation * C * L₁.width ^ 2 * L₂.width ^ 2 :=
  abs_pairEval_le_of_mixedFourthRemainder L₁ L₂ K R u v C hC hdecomp hbound

end TwoMomentFunctional
end BEMOC
