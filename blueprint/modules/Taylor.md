# Taylor: two-moment cancellation on a closed rectangle

`Taylor.lean` isolates Appendix 2's `eq:one-variable-taylor` and `eq:two-variable-taylor`. The analytic input is elementary but its hypotheses matter: a function `G` must be `C⁴` on an open neighborhood `W` of the entire closed product `B_j×B_k`, and its fourth mixed height derivative must be bounded there on the rectangle. The `MixedTaylorBound` contract states exactly the estimate later consumed by the separated and truncated-kernel cases. Do not apply it to the full latitude kernel on equal or adjacent bands, where the angular cusp invalidates the needed regularity. At a polar boundary, differentiating the raw square-root formula also fails; a smooth extension supplied by the separated-series argument is required.

Start with a one-variable lemma for a linear functional `L` that annihilates `1` and `id`. For any basepoint `x₀` in an interval of length `a`, Taylor's integral remainder gives `f(x)=f(x₀)+f'(x₀)(x−x₀)+R(x)` and `|R(x)|≤(a²/2) sup_I|f''|`. Applying `bandError` kills the affine part and leaves an absolute bound `≤(r_j a²) sup|f''|`, because its underlying signed measure has total variation at most `2r_j`. An equivalent direct calculation avoids signed measures: bound the continuous integral of `R` by `r_j sup|R|` and the atomic term by `r_j sup|R|`. Choose a basepoint inside the interval; `h_j` is convenient and reduces some interval-width constants, though the manuscript uses any point.

The exact band width is `a_j=2r_j/N`. From `4M²≤N`, `a_j≤r_j/(2M²)≤r_j/M²`. Applying the one-variable lemma first in `t` and then in `s` yields a coefficient at most `(r_j³r_k³)/(M⁸)`; the manuscript uses the somewhat loose factor at each stage. Keep an explicit denominator positivity proof for `M≥1`. For `j,k : RingIndex N`, `4≤N` implies `M≥1`; `ConstructionFacts` already contains this. Because `bandBlock` applies `k` inside `j`, a clean proof fixes `s`, estimates the `t` error, then differentiates the resulting function twice in `s`. The derivative and finite-interval integral commute under `ContDiffOn ℝ 4 G W`; prove the resulting mixed derivative equals `mixedFourth G`, or switch the application order to match `mixedFourth`'s exact nesting. The `C⁴` assumption gives equality of the mixed partial orders. Check the Lean `iteratedDeriv 2` convention at both levels and use `ContinuousLinearMap` or standard one-dimensional differentiation-under-integral lemmas rather than rewriting derivatives formally.

The contract uses `W` and `Set.prod` explicitly. The band rectangles are compact; all desired derivatives are continuous and bounded there. A reusable bridge should take a locally `C⁴` family of extensions whose values agree with the physical kernel and produce one rectangle-level witness, so that callers do not repeat gluing. If this proves awkward, state and prove a version of the Taylor lemma for `ContDiffOn` on an open set containing just the rectangle and define a canonical separated-series extension on that set. In either approach, prevent a pointwise `∃G` from being mistaken for a global `G`.

Legacy candidate: `legacy/BEMOCFormalization/MixedTaylorRemainder.lean`, especially `TwoMomentFunctional.abs_pairEval_le_of_mixedDerivative` and `abs_bandPairError_le_of_mixedDerivative`. It may offer an efficient abstract proof, but the old functional types and band normalization differ. `LatitudeBands.lean` supplies the moment cancellation used by those lemmas. This module's immediate dependency is `BandErrors`; downstream analytic blocks should cite this theorem rather than re-prove Taylor estimates.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.BandErrors
import Mathlib.Analysis.Calculus.Taylor

open MeasureTheory Set Filter
open scoped Topology
namespace BEMOC.Definitive

/-- A quadrature error supported on an interval, with vanishing zeroth and
first moments. This abstracts the band error without committing to signed
measures or to the details of the Diamond populations. -/
structure TwoMomentRule where
  left : ℝ
  right : ℝ
  left_le_right : left ≤ right
  apply : (ℝ → ℝ) → ℝ
  map_add : ∀ f g, apply (fun x => f x + g x) = apply f + apply g
  map_smul : ∀ c f, apply (fun x => c * f x) = c * apply f
  const_zero : ∀ c, apply (fun _ => c) = 0
  id_zero : apply id = 0
  variation : ℝ
  variation_nonneg : 0 ≤ variation
  abs_apply_le : ∀ f C, 0 ≤ C →
    (∀ x ∈ Icc left right, |f x| ≤ C) → |apply f| ≤ variation * C

namespace TwoMomentRule

def width (L : TwoMomentRule) : ℝ := L.right - L.left

theorem width_nonneg (L : TwoMomentRule) : 0 ≤ L.width :=
  sub_nonneg.mpr L.left_le_right

theorem apply_sub (L : TwoMomentRule) (f g : ℝ → ℝ) :
    L.apply (fun x => f x - g x) = L.apply f - L.apply g := by
  rw [show (fun x => f x - g x) = fun x => f x + (-1 : ℝ) * g x by
    funext x; ring, L.map_add, L.map_smul]
  ring

theorem affine_zero (L : TwoMomentRule) (a b : ℝ) :
    L.apply (fun x => a * x + b) = 0 := by
  rw [show (fun x => a * x + b) = fun x => a * id x + (fun _ => b) x by rfl,
    L.map_add, L.map_smul, L.id_zero, L.const_zero]
  ring

/-- One-variable Peano estimate. The deliberately loose constant matches the
manuscript and avoids a factorial in later bookkeeping. -/
theorem abs_apply_le_of_second_derivative
    (L : TwoMomentRule) (f : ℝ → ℝ) (C : ℝ)
    (hf : ContDiffOn ℝ 2 f (Icc L.left L.right))
    (hC : 0 ≤ C)
    (hderiv : ∀ x ∈ Icc L.left L.right,
      ‖iteratedDerivWithin 2 f (Icc L.left L.right) x‖ ≤ C) :
    |L.apply f| ≤ L.variation * C * L.width ^ 2 := by
  let T : ℝ → ℝ := fun x =>
    taylorWithinEval f 1 (Icc L.left L.right) L.left x
  let R : ℝ → ℝ := fun x => f x - T x
  have hformula : ∀ x : ℝ,
      T x = f L.left + (x - L.left) *
        derivWithin f (Icc L.left L.right) L.left := by
    intro x
    simp [T, taylorWithinEval_succ]
  have hT : L.apply T = 0 := by
    let d := derivWithin f (Icc L.left L.right) L.left
    have heq : T = fun x => d * x + (f L.left - d * L.left) := by
      funext x
      rw [hformula]
      dsimp [d]
      ring
    rw [heq]
    exact L.affine_zero d (f L.left - d * L.left)
  have hR : L.apply R = L.apply f := by
    rw [show R = fun x => f x - T x by rfl, L.apply_sub, hT, sub_zero]
  have hbound : ∀ x ∈ Icc L.left L.right,
      |R x| ≤ C * L.width ^ 2 := by
    intro x hx
    have hTaylor := taylor_mean_remainder_bound (f := f) (n := 1)
      L.left_le_right hf hx hderiv
    rw [show (1 : ℕ) + 1 = 2 by norm_num] at hTaylor
    norm_num at hTaylor
    have hxa : 0 ≤ x - L.left := sub_nonneg.mpr hx.1
    have hxab : x - L.left ≤ L.width := by
      dsimp [width]
      linarith [hx.2]
    dsimp [R]
    rw [hformula x]
    calc
      _ ≤ C * (x - L.left) ^ 2 := hTaylor
      _ ≤ C * L.width ^ 2 := by gcongr
  have hmain := L.abs_apply_le R (C * L.width ^ 2)
    (mul_nonneg hC (sq_nonneg _)) hbound
  rw [hR] at hmain
  nlinarith

/-- Nested two-moment evaluation, with the outer rule acting on the first
coordinate. -/
def pairApply (L₁ L₂ : TwoMomentRule) (G : ℝ → ℝ → ℝ) : ℝ :=
  L₁.apply (fun s => L₂.apply (G s))

/-- A bounded tensor remainder is the only part surviving both moment
cancellations. This theorem is useful even when a cusp prevents a fourth
derivative estimate. -/
theorem abs_pairApply_le_of_biaffine_remainder
    (L₁ L₂ : TwoMomentRule) (G R : ℝ → ℝ → ℝ)
    (uRight vRight uLeft vLeft : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hdecomp : ∀ s t, G s t = R s t +
      (uRight s * t + vRight s) + (uLeft t * s + vLeft t))
    (hbound : ∀ s ∈ Icc L₁.left L₁.right,
      ∀ t ∈ Icc L₂.left L₂.right,
        |R s t| ≤ C * L₁.width ^ 2 * L₂.width ^ 2) :
    |L₁.pairApply L₂ G| ≤
      L₁.variation * L₂.variation * C *
        L₁.width ^ 2 * L₂.width ^ 2 := by
  have hpair : L₁.pairApply L₂ G = L₁.pairApply L₂ R := by
    unfold pairApply
    have hinner : ∀ s,
        L₂.apply (G s) =
          L₂.apply (R s) +
            L₂.apply uLeft * s + L₂.apply vLeft := by
      intro s
      rw [show G s = fun t => R s t +
        (uRight s * t + vRight s) +
          (uLeft t * s + vLeft t) by
          funext t; exact hdecomp s t,
        L₂.map_add, L₂.map_add, L₂.affine_zero]
      rw [show (fun t => uLeft t * s + vLeft t) =
        fun t => s * uLeft t + vLeft t by funext t; ring,
        L₂.map_add, L₂.map_smul]
      ring
    rw [show (fun s => L₂.apply (G s)) =
      fun s => L₂.apply (R s) +
        (L₂.apply uLeft * s + L₂.apply vLeft) by
        funext s; convert hinner s using 1 <;> ring,
      L₁.map_add, L₁.affine_zero]
    ring
  rw [hpair]
  have hinner : ∀ s ∈ Icc L₁.left L₁.right,
      |L₂.apply (R s)| ≤
        L₂.variation * (C * L₁.width ^ 2 * L₂.width ^ 2) := by
    intro s hs
    exact L₂.abs_apply_le (R s)
      (C * L₁.width ^ 2 * L₂.width ^ 2)
      (by positivity) (fun t ht => hbound s hs t ht)
  have houter := L₁.abs_apply_le (fun s => L₂.apply (R s))
    (L₂.variation * (C * L₁.width ^ 2 * L₂.width ^ 2))
    (mul_nonneg L₂.variation_nonneg (by positivity)) hinner
  calc
    |L₁.pairApply L₂ R| ≤
        L₁.variation *
          (L₂.variation * (C * L₁.width ^ 2 * L₂.width ^ 2)) := houter
    _ = _ := by ring

/-- The error after removing the affine Taylor polynomial in the first
coordinate at the left endpoint. -/
noncomputable def firstTaylorError (G : ℝ → ℝ → ℝ)
    (I : Set ℝ) (a s t : ℝ) : ℝ :=
  G s t - taylorWithinEval (fun x => G x t) 1 I a s

/-- The tensor remainder obtained by Taylor subtraction in both variables. -/
noncomputable def tensorTaylorRemainder (G : ℝ → ℝ → ℝ)
    (Is It : Set ℝ) (a c s t : ℝ) : ℝ :=
  firstTaylorError G Is a s t -
    taylorWithinEval (firstTaylorError G Is a s) 1 It c t

/-- The tensor remainder differs from the kernel only by terms affine in
one of the two variables. -/
theorem tensorTaylor_decomposition (G : ℝ → ℝ → ℝ)
    (Is It : Set ℝ) (a c s t : ℝ) :
    G s t = tensorTaylorRemainder G Is It a c s t +
      (derivWithin (firstTaylorError G Is a s) It c * t +
        (firstTaylorError G Is a s c -
          c * derivWithin (firstTaylorError G Is a s) It c)) +
      (derivWithin (fun x => G x t) Is a * s +
        (G a t - a * derivWithin (fun x => G x t) Is a)) := by
  have hs : taylorWithinEval (fun x => G x t) 1 Is a s =
      G a t + (s - a) * derivWithin (fun x => G x t) Is a := by
    simp [taylorWithinEval_succ]
  have ht : taylorWithinEval (firstTaylorError G Is a s) 1 It c t =
      firstTaylorError G Is a s c +
        (t - c) * derivWithin (firstTaylorError G Is a s) It c := by
    simp [taylorWithinEval_succ]
  unfold tensorTaylorRemainder
  rw [ht]
  unfold firstTaylorError
  rw [hs]
  ring

/-- Two Taylor remainders give the product of squared interval widths. The
commutation hypothesis is the derivative identity that a C⁴ kernel supplies;
it is stated explicitly so this lemma also applies to other regularity APIs. -/
theorem abs_tensorTaylorRemainder_le
    (G Gtt : ℝ → ℝ → ℝ)
    {a b c d C : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hC : 0 ≤ C)
    (hGtt : ∀ t ∈ Icc c d,
      ContDiffOn ℝ 2 (fun s => Gtt s t) (Icc a b))
    (hmixed : ∀ t ∈ Icc c d, ∀ s ∈ Icc a b,
      ‖iteratedDerivWithin 2 (fun x => Gtt x t) (Icc a b) s‖ ≤ C)
    (herror : ∀ s ∈ Icc a b,
      ContDiffOn ℝ 2 (firstTaylorError G (Icc a b) a s) (Icc c d))
    (hcommute : ∀ s ∈ Icc a b, ∀ t ∈ Icc c d,
      iteratedDerivWithin 2
          (firstTaylorError G (Icc a b) a s) (Icc c d) t =
        Gtt s t -
          taylorWithinEval (fun x => Gtt x t) 1 (Icc a b) a s)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc c d) :
    |tensorTaylorRemainder G (Icc a b) (Icc c d) a c s t| ≤
      C * (b - a) ^ 2 * (d - c) ^ 2 := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hdc : 0 ≤ d - c := sub_nonneg.mpr hcd
  have hs_sub : 0 ≤ s - a := sub_nonneg.mpr hs.1
  have hs_width : s - a ≤ b - a := by linarith [hs.2]
  have ht_sub : 0 ≤ t - c := sub_nonneg.mpr ht.1
  have ht_width : t - c ≤ d - c := by linarith [ht.2]
  have hsecond : ∀ y ∈ Icc c d,
      ‖iteratedDerivWithin 2
          (firstTaylorError G (Icc a b) a s) (Icc c d) y‖ ≤
        C * (b - a) ^ 2 := by
    intro y hy
    rw [hcommute s hs y hy]
    have hTaylor := taylor_mean_remainder_bound
      (f := fun x => Gtt x y) (n := 1)
      hab (hGtt y hy) hs (hmixed y hy)
    have hformula :
        taylorWithinEval (fun x => Gtt x y) 1 (Icc a b) a s =
          Gtt a y + (s - a) *
            derivWithin (fun x => Gtt x y) (Icc a b) a := by
      simp [taylorWithinEval_succ]
    rw [show (1 : ℕ) + 1 = 2 by norm_num] at hTaylor
    norm_num at hTaylor
    calc
      ‖Gtt s y -
          taylorWithinEval (fun x => Gtt x y) 1 (Icc a b) a s‖ =
          |Gtt s y -
            taylorWithinEval (fun x => Gtt x y) 1 (Icc a b) a s| := by
              rw [Real.norm_eq_abs]
      _ ≤ C * (s - a) ^ 2 := by
        rw [hformula]
        exact hTaylor
      _ ≤ C * (b - a) ^ 2 := by gcongr
  have houter := taylor_mean_remainder_bound
    (f := firstTaylorError G (Icc a b) a s) (n := 1)
    hcd (herror s hs) ht hsecond
  rw [show (1 : ℕ) + 1 = 2 by norm_num] at houter
  norm_num at houter
  have hformula :
      taylorWithinEval (firstTaylorError G (Icc a b) a s)
          1 (Icc c d) c t =
        firstTaylorError G (Icc a b) a s c +
          (t - c) * derivWithin
            (firstTaylorError G (Icc a b) a s) (Icc c d) c := by
    simp [taylorWithinEval_succ]
  unfold tensorTaylorRemainder
  calc
    |firstTaylorError G (Icc a b) a s t -
        taylorWithinEval (firstTaylorError G (Icc a b) a s)
          1 (Icc c d) c t| =
        ‖firstTaylorError G (Icc a b) a s t -
          taylorWithinEval (firstTaylorError G (Icc a b) a s)
            1 (Icc c d) c t‖ := by rw [Real.norm_eq_abs]
    _ ≤ (C * (b - a) ^ 2) * (t - c) ^ 2 := by
      rw [hformula]
      exact houter
    _ ≤ C * (b - a) ^ 2 * (d - c) ^ 2 := by gcongr

/-- Complete abstract two-moment consequence of a mixed derivative chain. -/
theorem abs_pairApply_le_of_mixed_derivative
    (L₁ L₂ : TwoMomentRule) (G Gtt : ℝ → ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hGtt : ∀ t ∈ Icc L₂.left L₂.right,
      ContDiffOn ℝ 2 (fun s => Gtt s t) (Icc L₁.left L₁.right))
    (hmixed : ∀ t ∈ Icc L₂.left L₂.right,
      ∀ s ∈ Icc L₁.left L₁.right,
      ‖iteratedDerivWithin 2 (fun x => Gtt x t)
        (Icc L₁.left L₁.right) s‖ ≤ C)
    (herror : ∀ s ∈ Icc L₁.left L₁.right,
      ContDiffOn ℝ 2
        (firstTaylorError G (Icc L₁.left L₁.right) L₁.left s)
        (Icc L₂.left L₂.right))
    (hcommute : ∀ s ∈ Icc L₁.left L₁.right,
      ∀ t ∈ Icc L₂.left L₂.right,
      iteratedDerivWithin 2
        (firstTaylorError G (Icc L₁.left L₁.right) L₁.left s)
        (Icc L₂.left L₂.right) t =
          Gtt s t -
            taylorWithinEval (fun x => Gtt x t) 1
              (Icc L₁.left L₁.right) L₁.left s) :
    |L₁.pairApply L₂ G| ≤
      L₁.variation * L₂.variation * C *
        L₁.width ^ 2 * L₂.width ^ 2 := by
  apply L₁.abs_pairApply_le_of_biaffine_remainder L₂ G
    (fun s t => tensorTaylorRemainder G
      (Icc L₁.left L₁.right) (Icc L₂.left L₂.right)
      L₁.left L₂.left s t)
    (fun s => derivWithin (firstTaylorError G
      (Icc L₁.left L₁.right) L₁.left s)
      (Icc L₂.left L₂.right) L₂.left)
    (fun s => firstTaylorError G
      (Icc L₁.left L₁.right) L₁.left s L₂.left -
      L₂.left * derivWithin (firstTaylorError G
        (Icc L₁.left L₁.right) L₁.left s)
        (Icc L₂.left L₂.right) L₂.left)
    (fun t => derivWithin (fun x => G x t)
      (Icc L₁.left L₁.right) L₁.left)
    (fun t => G L₁.left t - L₁.left *
      derivWithin (fun x => G x t)
        (Icc L₁.left L₁.right) L₁.left)
    C hC
  · intro s t
    exact tensorTaylor_decomposition G
      (Icc L₁.left L₁.right) (Icc L₂.left L₂.right)
      L₁.left L₂.left s t
  · intro s hs t ht
    exact abs_tensorTaylorRemainder_le G Gtt
      L₁.left_le_right L₂.left_le_right hC
      hGtt hmixed herror hcommute hs ht

end TwoMomentRule

/-- Two derivatives in each height variable, in a fixed order. -/
noncomputable def mixedFourth (G : ℝ × ℝ → ℝ) (s t : ℝ) : ℝ :=
  iteratedDeriv 2 (fun u => iteratedDeriv 2 (fun v => G (u, v)) t) s

/-- The concrete band error is additive on interval-integrable functions.
This restriction is essential: the real interval integral is totalized on
arbitrary functions, but its unrestricted additivity is unavailable. -/
theorem bandError_add_of_integrable (N j : ℕ) (f g : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (boundary N j) (boundary N (j - 1)))
    (hg : IntervalIntegrable g volume (boundary N j) (boundary N (j - 1))) :
    bandError N j (fun t => f t + g t) =
      bandError N j f + bandError N j g := by
  unfold bandError
  change (N : ℝ) / 2 *
      (∫ t in boundary N j..boundary N (j - 1), f t + g t) -
      (population N j : ℝ) * (f (height N j) + g (height N j)) = _
  have hint :
      (∫ t in boundary N j..boundary N (j - 1), f t + g t) =
        (∫ t in boundary N j..boundary N (j - 1), f t) +
          (∫ t in boundary N j..boundary N (j - 1), g t) :=
    intervalIntegral.integral_add hf hg
  rw [hint]
  ring

theorem bandError_const_mul (N j : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    bandError N j (fun t => c * f t) = c * bandError N j f := by
  unfold bandError
  rw [intervalIntegral.integral_const_mul]
  ring

theorem bandError_affine_of_moments (N j : ℕ)
    (hone : bandError N j (fun _ => 1) = 0)
    (hid : bandError N j id = 0) (a b : ℝ) :
    bandError N j (fun t => a * t + b) = 0 := by
  have hintId : IntervalIntegrable id volume
      (boundary N j) (boundary N (j - 1)) :=
    continuous_id.intervalIntegrable _ _
  have hintConst : IntervalIntegrable (fun _ : ℝ => b) volume
      (boundary N j) (boundary N (j - 1)) :=
    continuous_const.intervalIntegrable _ _
  rw [show (fun t : ℝ => a * t + b) =
      fun t => a * id t + (fun _ : ℝ => b) t by rfl,
    bandError_add_of_integrable N j _ _ (hintId.const_mul a) hintConst,
    bandError_const_mul,
    show (fun _ : ℝ => b) = fun t => b * (fun _ : ℝ => 1) t by
      funext t; ring,
    bandError_const_mul, hone, hid]
  ring

/-- Total variation estimate for the explicit midpoint band rule. The width
and midpoint conditions are isolated so this lemma does not wait for the
construction module's arithmetic theorems. -/
theorem abs_bandError_le_of_bound (N j : ℕ) (f : ℝ → ℝ) (C : ℝ)
    (hN : 0 < N) (_hC : 0 ≤ C)
    (hwidth : boundary N (j - 1) - boundary N j =
      2 * (population N j : ℝ) / N)
    (hmid : height N j ∈ band N j)
    (hbound : ∀ t ∈ band N j, |f t| ≤ C) :
    |bandError N j f| ≤ 2 * (population N j : ℝ) * C := by
  let a := boundary N j
  let b := boundary N (j - 1)
  let r : ℝ := population N j
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNreal
  have hba : a ≤ b := by
    apply sub_nonneg.mp
    rw [hwidth]
    positivity
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := f) (C := C)
    (fun t ht => by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le hba] at ht
      exact hbound t ⟨ht.1.le, ht.2⟩)
  rw [Real.norm_eq_abs] at hint
  have hm : |f (height N j)| ≤ C := hbound _ hmid
  have hscale : 0 ≤ (N : ℝ) / 2 := by positivity
  unfold bandError
  calc
    |(N : ℝ) / 2 * (∫ t in a..b, f t) - r * f (height N j)| ≤
        |(N : ℝ) / 2 * (∫ t in a..b, f t)| +
          |r * f (height N j)| := by
            calc
              _ = |(N : ℝ) / 2 * (∫ t in a..b, f t) +
                  -(r * f (height N j))| := by ring
              _ ≤ |(N : ℝ) / 2 * (∫ t in a..b, f t)| +
                  |-(r * f (height N j))| := abs_add_le _ _
              _ = _ := by rw [abs_neg]
    _ ≤ (N : ℝ) / 2 * (C * (b - a)) + r * C := by
      rw [abs_mul, abs_mul, abs_of_nonneg hscale,
        abs_of_nonneg (show 0 ≤ r by positivity)]
      have habs : |b - a| = b - a := abs_of_nonneg (sub_nonneg.mpr hba)
      rw [habs] at hint
      gcongr
    _ = 2 * r * C := by
      dsimp [a, b, r]
      rw [hwidth]
      field_simp
      ring

/-- The actual midpoint band rule gains two powers of its width when its
first two moments vanish. The smoothness and derivative bound are only
required on the closed band. -/
theorem abs_bandError_le_of_second_derivative
    (N j : ℕ) (f : ℝ → ℝ) (C : ℝ)
    (hN : 0 < N) (hC : 0 ≤ C)
    (hwidth : boundary N (j - 1) - boundary N j =
      2 * (population N j : ℝ) / N)
    (hmid : height N j ∈ band N j)
    (hone : bandError N j (fun _ => 1) = 0)
    (hid : bandError N j id = 0)
    (hf : ContDiffOn ℝ 2 f (band N j))
    (hderiv : ∀ x ∈ band N j,
      ‖iteratedDerivWithin 2 f (band N j) x‖ ≤ C) :
    |bandError N j f| ≤
      2 * (population N j : ℝ) * C *
        (boundary N (j - 1) - boundary N j) ^ 2 := by
  let a := boundary N j
  let b := boundary N (j - 1)
  have hab : a ≤ b := by
    apply sub_nonneg.mp
    rw [hwidth]
    positivity
  let T : ℝ → ℝ := fun x =>
    taylorWithinEval f 1 (Icc a b) a x
  let R : ℝ → ℝ := fun x => f x - T x
  have hformula : ∀ x : ℝ,
      T x = f a + (x - a) *
        derivWithin f (Icc a b) a := by
    intro x
    simp [T, taylorWithinEval_succ]
  have hTzero : bandError N j T = 0 := by
    have heq : T = fun x =>
        derivWithin f (Icc a b) a * x +
          (f a - derivWithin f (Icc a b) a * a) := by
      funext x
      rw [hformula]
      ring
    rw [heq]
    exact bandError_affine_of_moments N j hone hid _ _
  have hTint : IntervalIntegrable T volume a b := by
    apply Continuous.intervalIntegrable
    rw [show T = fun x => f a + (x - a) *
      derivWithin f (Icc a b) a by funext x; exact hformula x]
    fun_prop
  have hfint : IntervalIntegrable f volume a b := by
    exact ContinuousOn.intervalIntegrable_of_Icc hab hf.continuousOn
  have hRint : IntervalIntegrable R volume a b := hfint.sub hTint
  have hReq : bandError N j R = bandError N j f := by
    have hadd := bandError_add_of_integrable N j R T hRint hTint
    have hfun : (fun x => R x + T x) = f := by
      funext x
      dsimp [R]
      ring
    rw [hfun, hTzero] at hadd
    linarith
  have hbound : ∀ x ∈ band N j,
      |R x| ≤ C * (b - a) ^ 2 := by
    intro x hx
    have hTaylor := taylor_mean_remainder_bound (f := f) (n := 1)
      hab hf hx hderiv
    rw [show (1 : ℕ) + 1 = 2 by norm_num] at hTaylor
    norm_num at hTaylor
    have hxa : 0 ≤ x - a := sub_nonneg.mpr hx.1
    have hxab : x - a ≤ b - a := by linarith [hx.2]
    dsimp [R]
    rw [hformula x]
    calc
      _ ≤ C * (x - a) ^ 2 := hTaylor
      _ ≤ C * (b - a) ^ 2 := by gcongr
  have hmain := abs_bandError_le_of_bound N j R
    (C * (b - a) ^ 2) hN (by positivity)
    hwidth hmid hbound
  rw [hReq] at hmain
  convert hmain using 1 <;> ring

/-- The midpoint lies in its closed band as soon as the boundary width is
nonnegative. -/
theorem height_mem_band_of_width (N j : ℕ) (hN : 0 < N)
    (hwidth : boundary N (j - 1) - boundary N j =
      2 * (population N j : ℝ) / N) :
    height N j ∈ band N j := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : boundary N j ≤ boundary N (j - 1) := by
    apply sub_nonneg.mp
    rw [hwidth]
    positivity
  change boundary N j ≤
      (boundary N (j - 1) + boundary N j) / 2 ∧
      (boundary N (j - 1) + boundary N j) / 2 ≤
        boundary N (j - 1)
  constructor <;> linarith

/-- Exact boundary widths are at most half the population divided by `M²`.
This spare factor of two absorbs the two variation constants in the double
Taylor estimate. -/
theorem boundary_width_le_scaled {N : ℕ} (hN : 4 ≤ N)
    (j : RingIndex N) :
    boundary N j.val - boundary N (j.val + 1) ≤
      (population N (j.val + 1) : ℝ) /
        (2 * (bandParameter N : ℝ) ^ 2) := by
  have hj : 1 ≤ j.val + 1 := by omega
  have hw : boundary N j.val - boundary N (j.val + 1) =
      2 * (population N (j.val + 1) : ℝ) / N := by
    simpa only [Nat.add_sub_cancel_left] using (boundary_width hN hj)
  rw [hw]
  have hM : (0 : ℝ) < bandParameter N := by
    exact_mod_cast bandParameter_pos hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hBig : 4 * (bandParameter N : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hr : (0 : ℝ) ≤ population N (j.val + 1) := by positivity
  apply (div_le_div_iff₀ hNr (by positivity : 0 < 2 * (bandParameter N : ℝ) ^ 2)).2
  nlinarith [mul_nonneg hr (sub_nonneg.mpr hBig)]

/-- A directly usable band variation estimate for occupied indices. -/
theorem abs_bandError_le_of_bound_indexed
    {N : ℕ} (hN : 4 ≤ N) (j : RingIndex N)
    (f : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ band N (j.val + 1), |f t| ≤ C) :
    |bandError N (j.val + 1) f| ≤
      2 * (population N (j.val + 1) : ℝ) * C := by
  have hj : 1 ≤ j.val + 1 := by omega
  have hw := boundary_width hN hj
  have hNpos : 0 < N := by omega
  exact abs_bandError_le_of_bound N (j.val + 1) f C
    hNpos hC hw (height_mem_band_of_width N _ hNpos hw) hbound

/-- A directly usable one-band Peano estimate, conditional only on the
moment contract and the second derivative bound. -/
theorem abs_bandError_le_of_second_derivative_indexed
    {N : ℕ} (hN : 4 ≤ N) (hmom : BandMoments)
    (j : RingIndex N) (f : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ContDiffOn ℝ 2 f (band N (j.val + 1)))
    (hderiv : ∀ x ∈ band N (j.val + 1),
      ‖iteratedDerivWithin 2 f (band N (j.val + 1)) x‖ ≤ C) :
    |bandError N (j.val + 1) f| ≤
      2 * (population N (j.val + 1) : ℝ) * C *
        (boundary N j.val - boundary N (j.val + 1)) ^ 2 := by
  have hj : 1 ≤ j.val + 1 := by omega
  have hw := boundary_width hN hj
  have hNpos : 0 < N := by omega
  obtain ⟨hone, hid⟩ := hmom N hN j
  exact abs_bandError_le_of_second_derivative N (j.val + 1) f C
    hNpos hC hw (height_mem_band_of_width N _ hNpos hw)
    hone hid hf hderiv

/-- Concrete double variation estimate on a rectangle. It is independent
of differentiability, so it can also bound the low-angle cusp contribution. -/
theorem abs_bandBlock_le_of_bound (N j k : ℕ) (G : ℝ × ℝ → ℝ) (C : ℝ)
    (hN : 0 < N) (hC : 0 ≤ C)
    (hwj : boundary N (j - 1) - boundary N j =
      2 * (population N j : ℝ) / N)
    (hwk : boundary N (k - 1) - boundary N k =
      2 * (population N k : ℝ) / N)
    (hmj : height N j ∈ band N j)
    (hmk : height N k ∈ band N k)
    (hbound : ∀ s ∈ band N j, ∀ t ∈ band N k,
      |G (s, t)| ≤ C) :
    |bandBlock N j k G| ≤
      4 * (population N j : ℝ) * (population N k : ℝ) * C := by
  have hinner : ∀ s ∈ band N j,
      |bandError N k (fun t => G (s, t))| ≤
        2 * (population N k : ℝ) * C := by
    intro s hs
    exact abs_bandError_le_of_bound N k (fun t => G (s, t)) C
      hN hC hwk hmk (fun t ht => hbound s hs t ht)
  unfold bandBlock
  have hD : 0 ≤ 2 * (population N k : ℝ) * C := by positivity
  have houter := abs_bandError_le_of_bound N j
    (fun s => bandError N k (fun t => G (s, t)))
    (2 * (population N k : ℝ) * C)
    hN hD hwj hmj hinner
  calc
    _ ≤ 2 * (population N j : ℝ) *
      (2 * (population N k : ℝ) * C) := houter
    _ = _ := by ring

/-- If affine cancellation has reduced a block to a bounded tensor
remainder, the explicit midpoint rules obey the same product-width bound
as abstract two-moment rules. -/
theorem abs_bandBlock_le_of_remainder (N j k : ℕ)
    (G R : ℝ × ℝ → ℝ) (L : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L)
    (hwj : boundary N (j - 1) - boundary N j =
      2 * (population N j : ℝ) / N)
    (hwk : boundary N (k - 1) - boundary N k =
      2 * (population N k : ℝ) / N)
    (hmj : height N j ∈ band N j)
    (hmk : height N k ∈ band N k)
    (heq : bandBlock N j k G = bandBlock N j k R)
    (hbound : ∀ s ∈ band N j, ∀ t ∈ band N k,
      |R (s, t)| ≤ L *
        (boundary N (j - 1) - boundary N j) ^ 2 *
        (boundary N (k - 1) - boundary N k) ^ 2) :
    |bandBlock N j k G| ≤
      4 * (population N j : ℝ) * (population N k : ℝ) *
        L * (boundary N (j - 1) - boundary N j) ^ 2 *
          (boundary N (k - 1) - boundary N k) ^ 2 := by
  rw [heq]
  have hC : 0 ≤ L *
      (boundary N (j - 1) - boundary N j) ^ 2 *
        (boundary N (k - 1) - boundary N k) ^ 2 := by positivity
  have hmain := abs_bandBlock_le_of_bound N j k R _
    hN hC hwj hwk hmj hmk hbound
  convert hmain using 1 <;> ring

/-- Concrete two-band Taylor estimate from an explicit derivative chain.
The assumptions `hcommute` and `hinner` are precisely the calculus facts a
`C⁴` neighborhood supplies; keeping them visible prevents accidental use
on diagonal cusp blocks. -/
theorem abs_bandBlock_le_of_mixed_derivative
    {N : ℕ} (hN : 4 ≤ N) (hmom : BandMoments)
    (j k : RingIndex N) (G : ℝ × ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (houter : ContDiffOn ℝ 2
      (fun s => bandError N (k.val + 1) (fun t => G (s, t)))
      (band N (j.val + 1)))
    (hcommute : ∀ s ∈ band N (j.val + 1),
      iteratedDerivWithin 2
        (fun u => bandError N (k.val + 1) (fun t => G (u, t)))
        (band N (j.val + 1)) s =
      bandError N (k.val + 1)
        (fun t => iteratedDerivWithin 2
          (fun u => G (u, t)) (band N (j.val + 1)) s))
    (hinner : ∀ s ∈ band N (j.val + 1),
      ContDiffOn ℝ 2
        (fun t => iteratedDerivWithin 2
          (fun u => G (u, t)) (band N (j.val + 1)) s)
        (band N (k.val + 1)))
    (hbound : ∀ s ∈ band N (j.val + 1),
      ∀ t ∈ band N (k.val + 1),
      ‖iteratedDerivWithin 2
        (fun v => iteratedDerivWithin 2
          (fun u => G (u, v)) (band N (j.val + 1)) s)
        (band N (k.val + 1)) t‖ ≤ L) :
    |bandBlock N (j.val + 1) (k.val + 1) G| ≤
      4 * (population N (j.val + 1) : ℝ) *
        (population N (k.val + 1) : ℝ) * L *
        (boundary N j.val - boundary N (j.val + 1)) ^ 2 *
        (boundary N k.val - boundary N (k.val + 1)) ^ 2 := by
  have hboundOuter : ∀ s ∈ band N (j.val + 1),
      ‖iteratedDerivWithin 2
        (fun u => bandError N (k.val + 1) (fun t => G (u, t)))
        (band N (j.val + 1)) s‖ ≤
      2 * (population N (k.val + 1) : ℝ) * L *
        (boundary N k.val - boundary N (k.val + 1)) ^ 2 := by
    intro s hs
    rw [hcommute s hs, Real.norm_eq_abs]
    exact abs_bandError_le_of_second_derivative_indexed
      hN hmom k _ L hL (hinner s hs) (fun t ht => hbound s hs t ht)
  have hmain := abs_bandError_le_of_second_derivative_indexed
    hN hmom j
    (fun s => bandError N (k.val + 1) (fun t => G (s, t)))
    (2 * (population N (k.val + 1) : ℝ) * L *
      (boundary N k.val - boundary N (k.val + 1)) ^ 2)
    (by positivity) houter hboundOuter
  unfold bandBlock
  convert hmain using 1 <;> ring

/-- The derivative-chain estimate in the precise `M⁻⁸` normalization used
by `MixedTaylorBound`. -/
theorem abs_bandBlock_le_of_mixed_derivative_scaled
    {N : ℕ} (hN : 4 ≤ N) (hmom : BandMoments)
    (j k : RingIndex N) (G : ℝ × ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (houter : ContDiffOn ℝ 2
      (fun s => bandError N (k.val + 1) (fun t => G (s, t)))
      (band N (j.val + 1)))
    (hcommute : ∀ s ∈ band N (j.val + 1),
      iteratedDerivWithin 2
        (fun u => bandError N (k.val + 1) (fun t => G (u, t)))
        (band N (j.val + 1)) s =
      bandError N (k.val + 1)
        (fun t => iteratedDerivWithin 2
          (fun u => G (u, t)) (band N (j.val + 1)) s))
    (hinner : ∀ s ∈ band N (j.val + 1),
      ContDiffOn ℝ 2
        (fun t => iteratedDerivWithin 2
          (fun u => G (u, t)) (band N (j.val + 1)) s)
        (band N (k.val + 1)))
    (hbound : ∀ s ∈ band N (j.val + 1),
      ∀ t ∈ band N (k.val + 1),
      ‖iteratedDerivWithin 2
        (fun v => iteratedDerivWithin 2
          (fun u => G (u, v)) (band N (j.val + 1)) s)
        (band N (k.val + 1)) t‖ ≤ L) :
    |bandBlock N (j.val + 1) (k.val + 1) G| ≤
      (population N (j.val + 1) : ℝ) ^ 3 *
        (population N (k.val + 1) : ℝ) ^ 3 /
          (bandParameter N : ℝ) ^ 8 * L := by
  let M : ℝ := bandParameter N
  let rj : ℝ := population N (j.val + 1)
  let rk : ℝ := population N (k.val + 1)
  let wj : ℝ := boundary N j.val - boundary N (j.val + 1)
  let wk : ℝ := boundary N k.val - boundary N (k.val + 1)
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast bandParameter_pos hN
  have hrj : 0 ≤ rj := by positivity
  have hrk : 0 ≤ rk := by positivity
  have hwj : 0 ≤ wj := by
    dsimp [wj]
    have hj : 1 ≤ j.val + 1 := by omega
    have hw := boundary_width hN hj
    have hw' : boundary N j.val - boundary N (j.val + 1) =
        2 * (population N (j.val + 1) : ℝ) / N := by
      simpa only [Nat.add_sub_cancel_left] using hw
    rw [hw']
    positivity
  have hwk : 0 ≤ wk := by
    dsimp [wk]
    have hk : 1 ≤ k.val + 1 := by omega
    have hw := boundary_width hN hk
    have hw' : boundary N k.val - boundary N (k.val + 1) =
        2 * (population N (k.val + 1) : ℝ) / N := by
      simpa only [Nat.add_sub_cancel_left] using hw
    rw [hw']
    positivity
  have hlej : wj ≤ rj / (2 * M ^ 2) := boundary_width_le_scaled hN j
  have hlek : wk ≤ rk / (2 * M ^ 2) := boundary_width_le_scaled hN k
  have hbase := abs_bandBlock_le_of_mixed_derivative hN hmom j k G L
    hL houter hcommute hinner hbound
  change |bandBlock N (j.val + 1) (k.val + 1) G| ≤
    rj ^ 3 * rk ^ 3 / M ^ 8 * L
  calc
    _ ≤ 4 * rj * rk * L * wj ^ 2 * wk ^ 2 := hbase
    _ ≤ 4 * rj * rk * L *
        (rj / (2 * M ^ 2)) ^ 2 *
        (rk / (2 * M ^ 2)) ^ 2 := by gcongr
    _ = rj ^ 3 * rk ^ 3 / M ^ 8 * L / 4 := by
      field_simp
      ring
    _ ≤ rj ^ 3 * rk ^ 3 / M ^ 8 * L := by
      have hpos : 0 ≤ rj ^ 3 * rk ^ 3 / M ^ 8 * L := by positivity
      linarith

/-- The two-moment estimate for a C⁴ extension around a closed rectangle. -/
def MixedTaylorBound : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ j k : RingIndex N,
    ∀ G : ℝ × ℝ → ℝ, ∀ W : Set (ℝ × ℝ), IsOpen W →
      (band N (j.val + 1) ×ˢ band N (k.val + 1)) ⊆ W →
      ContDiffOn ℝ 4 G W → ∀ L : ℝ, 0 ≤ L →
      (∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
        |mixedFourth G p.1 p.2| ≤ L) →
      |bandBlock N (j.val + 1) (k.val + 1) G| ≤
        (population N (j.val + 1) : ℝ) ^ 3 *
          (population N (k.val + 1) : ℝ) ^ 3 / (bandParameter N : ℝ) ^ 8 * L

/-- The remaining calculus interface: a `C⁴` kernel on an open neighborhood
has the expected regularity and differentiation-under-integral identity for
the concrete band rules. This is deliberately a separate unproved target;
all measure and arithmetic portions of mixed Taylor are proved above. -/
def MixedTaylorCalculusBridge : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ j k : RingIndex N,
    ∀ G : ℝ × ℝ → ℝ, ∀ W : Set (ℝ × ℝ), IsOpen W →
      (band N (j.val + 1) ×ˢ band N (k.val + 1)) ⊆ W →
      ContDiffOn ℝ 4 G W →
      ContDiffOn ℝ 2
        (fun s => bandError N (k.val + 1) (fun t => G (s, t)))
        (band N (j.val + 1)) ∧
      (∀ s ∈ band N (j.val + 1),
        iteratedDerivWithin 2
          (fun u => bandError N (k.val + 1) (fun t => G (u, t)))
          (band N (j.val + 1)) s =
        bandError N (k.val + 1)
          (fun t => iteratedDerivWithin 2
            (fun u => G (u, t)) (band N (j.val + 1)) s)) ∧
      (∀ s ∈ band N (j.val + 1),
        ContDiffOn ℝ 2
          (fun t => iteratedDerivWithin 2
            (fun u => G (u, t)) (band N (j.val + 1)) s)
          (band N (k.val + 1))) ∧
      (∀ s ∈ band N (j.val + 1), ∀ t ∈ band N (k.val + 1),
        iteratedDerivWithin 2
          (fun v => iteratedDerivWithin 2
            (fun u => G (u, v)) (band N (j.val + 1)) s)
          (band N (k.val + 1)) t = mixedFourth G s t)

/-- Restriction of a neighborhood-smooth kernel to any horizontal slice. -/
theorem contDiffOn_band_slice_first
    {N j k : ℕ} {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : (band N j ×ˢ band N k) ⊆ W)
    (hG : ContDiffOn ℝ 4 G W)
    (t : ℝ) (ht : t ∈ band N k) :
    ContDiffOn ℝ 4 (fun s => G (s, t)) (band N j) := by
  have hmap : Set.MapsTo (fun s : ℝ => (s, t)) (band N j) W := by
    intro s hs
    exact hW ⟨hs, ht⟩
  have hsmooth : ContDiffOn ℝ 4 (fun s : ℝ => (s, t)) (band N j) := by
    fun_prop
  exact hG.comp hsmooth hmap

/-- Restriction to vertical slices, including the closed polar endpoints. -/
theorem contDiffOn_band_slice_second
    {N j k : ℕ} {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : (band N j ×ˢ band N k) ⊆ W)
    (hG : ContDiffOn ℝ 4 G W)
    (s : ℝ) (hs : s ∈ band N j) :
    ContDiffOn ℝ 4 (fun t => G (s, t)) (band N k) := by
  have hmap : Set.MapsTo (fun t : ℝ => (s, t)) (band N k) W := by
    intro t ht
    exact hW ⟨hs, ht⟩
  have hsmooth : ContDiffOn ℝ 4 (fun t : ℝ => (s, t)) (band N k) := by
    fun_prop
  exact hG.comp hsmooth hmap

/-- The ambient first height derivative, expressed as a Fréchet derivative
in the first coordinate. -/
noncomputable def partialFirst (G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ G p (1, 0)

/-- The ambient second derivative in the first height coordinate. -/
noncomputable def partialFirstTwice (G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (partialFirst G) p (1, 0)

theorem contDiffOn_partialFirst
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W) :
    ContDiffOn ℝ 3 (partialFirst G) W := by
  have hfd : ContDiffOn ℝ 3 (fderiv ℝ G) W :=
    hG.fderiv_of_isOpen hW (by norm_num)
  have hconst : ContDiffOn ℝ 3
      (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) W := contDiffOn_const
  exact hfd.clm_apply hconst

theorem contDiffOn_partialFirstTwice
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W) :
    ContDiffOn ℝ 2 (partialFirstTwice G) W := by
  have hfd : ContDiffOn ℝ 2 (fderiv ℝ (partialFirst G)) W :=
    (contDiffOn_partialFirst hW hG).fderiv_of_isOpen hW (by norm_num)
  have hconst : ContDiffOn ℝ 2
      (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) W := contDiffOn_const
  exact hfd.clm_apply hconst

theorem deriv_slice_first_eq_partialFirst
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (s t : ℝ) (hp : (s, t) ∈ W) :
    deriv (fun u => G (u, t)) s = partialFirst G (s, t) := by
  have hdiff : DifferentiableAt ℝ G (s, t) :=
    (hG.contDiffAt (hW.mem_nhds hp)).differentiableAt (by norm_num)
  have hcomp := hdiff.hasFDerivAt.comp s
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) s t)
  have hscalar := hcomp.hasDerivAt.deriv
  simpa [partialFirst] using hscalar

theorem deriv_slice_partialFirst_eq_partialFirstTwice
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (s t : ℝ) (hp : (s, t) ∈ W) :
    deriv (fun u => partialFirst G (u, t)) s =
      partialFirstTwice G (s, t) := by
  have hdiff : DifferentiableAt ℝ (partialFirst G) (s, t) :=
    ((contDiffOn_partialFirst hW hG).contDiffAt
      (hW.mem_nhds hp)).differentiableAt (by norm_num)
  have hcomp := hdiff.hasFDerivAt.comp s
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) s t)
  have hscalar := hcomp.hasDerivAt.deriv
  simpa [partialFirstTwice] using hscalar

theorem iteratedDeriv_two_slice_first_eq_partialFirstTwice
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (s t : ℝ) (hp : (s, t) ∈ W) :
    iteratedDeriv 2 (fun u => G (u, t)) s =
      partialFirstTwice G (s, t) := by
  have hslice : Continuous (fun u : ℝ => (u, t)) := by fun_prop
  have hpre : IsOpen {u : ℝ | (u, t) ∈ W} := hW.preimage hslice
  have hmem : ∀ᶠ u in 𝓝 s, (u, t) ∈ W := hpre.mem_nhds hp
  have hev : (fun u => deriv (fun v => G (v, t)) u) =ᶠ[𝓝 s]
      (fun u => partialFirst G (u, t)) :=
    hmem.mono (fun u hu =>
      deriv_slice_first_eq_partialFirst hW hG u t hu)
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    iteratedDeriv_succ, iteratedDeriv_one]
  rw [hev.deriv_eq]
  exact deriv_slice_partialFirst_eq_partialFirstTwice hW hG s t hp

/-- At a point of a nondegenerate closed interval, derivatives taken within
that interval agree with the ordinary derivatives of a smooth extension,
including at its endpoints. -/
theorem iteratedDerivWithin_two_eq_iteratedDeriv
    {f : ℝ → ℝ} {a b x : ℝ} (hab : a < b)
    (hx : x ∈ Icc a b) (hf : ContDiffAt ℝ 2 f x) :
    iteratedDerivWithin 2 f (Icc a b) x = iteratedDeriv 2 f x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedDeriv_eq_iteratedFDeriv]
  rw [iteratedFDerivWithin_eq_iteratedFDeriv
    (uniqueDiffOn_Icc hab) hf hx]

theorem mixedTaylorBound_of_calculus_bridge
    (hmom : BandMoments) (hbridge : MixedTaylorCalculusBridge) :
    MixedTaylorBound := by
  intro N hN j k G W hW hopen hG L hL hbound
  obtain ⟨houter, hcommute, hinner, hfourth⟩ :=
    hbridge N hN j k G W hW hopen hG
  apply abs_bandBlock_le_of_mixed_derivative_scaled
    hN hmom j k G L hL houter hcommute hinner
  intro s hs t ht
  rw [hfourth s hs t ht, Real.norm_eq_abs]
  exact hbound (s, t) ⟨hs, ht⟩

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
