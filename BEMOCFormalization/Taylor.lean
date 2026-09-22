import BEMOCFormalization.BandErrors
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

open MeasureTheory Set Filter
open scoped Topology Interval
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

/-- The calculus interface: a `C⁴` kernel on an open neighborhood has the
expected regularity and differentiation-under-integral identity for the
concrete band rules. Its proof below uses compactness of the closed band. -/
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

theorem contDiffAt_slice_first
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (s t : ℝ) (hp : (s, t) ∈ W) :
    ContDiffAt ℝ 4 (fun u => G (u, t)) s := by
  have hpt : ContDiffAt ℝ 4 (fun u : ℝ => (u, t)) s := by fun_prop
  exact (hG.contDiffAt (hW.mem_nhds hp)).comp s hpt

theorem iteratedDerivWithin_two_slice_first_eq_partialFirstTwice
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    {a b s t : ℝ} (hab : a < b) (hs : s ∈ Icc a b)
    (hp : (s, t) ∈ W) :
    iteratedDerivWithin 2 (fun u => G (u, t)) (Icc a b) s =
      partialFirstTwice G (s, t) := by
  rw [iteratedDerivWithin_two_eq_iteratedDeriv hab hs
    ((contDiffAt_slice_first hW hG s t hp).of_le (by decide))]
  exact iteratedDeriv_two_slice_first_eq_partialFirstTwice hW hG s t hp

theorem contDiffOn_inner_partial
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    {a b c d s : ℝ} (hab : a < b) (hs : s ∈ Icc a b)
    (hrect : (Icc a b ×ˢ Icc c d) ⊆ W) :
    ContDiffOn ℝ 2
      (fun t => iteratedDerivWithin 2
        (fun u => G (u, t)) (Icc a b) s) (Icc c d) := by
  have hmap : Set.MapsTo (fun t : ℝ => (s, t)) (Icc c d) W := by
    intro t ht
    exact hrect ⟨hs, ht⟩
  have hsmooth : ContDiffOn ℝ 2 (fun t : ℝ => (s, t)) (Icc c d) := by
    fun_prop
  have hpart : ContDiffOn ℝ 2
      (fun t => partialFirstTwice G (s, t)) (Icc c d) :=
    (contDiffOn_partialFirstTwice hW hG).comp hsmooth hmap
  apply hpart.congr
  intro t ht
  exact iteratedDerivWithin_two_slice_first_eq_partialFirstTwice
    hW hG hab hs (hrect ⟨hs, ht⟩)

noncomputable def partialSecond (G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ G p (0, 1)

noncomputable def partialSecondTwice (G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (partialSecond G) p (0, 1)

theorem contDiffOn_partialSecond
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W) :
    ContDiffOn ℝ 3 (partialSecond G) W := by
  have hfd : ContDiffOn ℝ 3 (fderiv ℝ G) W :=
    hG.fderiv_of_isOpen hW (by norm_num)
  have hconst : ContDiffOn ℝ 3
      (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) W := contDiffOn_const
  exact hfd.clm_apply hconst

theorem contDiffOn_partialSecondTwice
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W) :
    ContDiffOn ℝ 2 (partialSecondTwice G) W := by
  have hfd : ContDiffOn ℝ 2 (fderiv ℝ (partialSecond G)) W :=
    (contDiffOn_partialSecond hW hG).fderiv_of_isOpen hW (by norm_num)
  have hconst : ContDiffOn ℝ 2
      (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) W := contDiffOn_const
  exact hfd.clm_apply hconst

theorem contDiffOn_second_height_partial_horizontal
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    {a b c d t : ℝ} (ht : t ∈ Icc c d)
    (hrect : (Icc a b ×ˢ Icc c d) ⊆ W) :
    ContDiffOn ℝ 2 (fun s => partialSecondTwice G (s, t)) (Icc a b) := by
  have hmap : Set.MapsTo (fun s : ℝ => (s, t)) (Icc a b) W := by
    intro s hs
    exact hrect ⟨hs, ht⟩
  have hsmooth : ContDiffOn ℝ 2 (fun s : ℝ => (s, t)) (Icc a b) := by
    fun_prop
  exact (contDiffOn_partialSecondTwice hW hG).comp hsmooth hmap

theorem deriv_slice_second_eq_partialSecond
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (s t : ℝ) (hp : (s, t) ∈ W) :
    deriv (fun v => G (s, v)) t = partialSecond G (s, t) := by
  have hdiff : DifferentiableAt ℝ G (s, t) :=
    (hG.contDiffAt (hW.mem_nhds hp)).differentiableAt (by norm_num)
  have hcomp := hdiff.hasFDerivAt.comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) s t)
  have hscalar := hcomp.hasDerivAt.deriv
  simpa [partialSecond] using hscalar

theorem deriv_slice_partialSecond_eq_partialSecondTwice
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (s t : ℝ) (hp : (s, t) ∈ W) :
    deriv (fun v => partialSecond G (s, v)) t =
      partialSecondTwice G (s, t) := by
  have hdiff : DifferentiableAt ℝ (partialSecond G) (s, t) :=
    ((contDiffOn_partialSecond hW hG).contDiffAt
      (hW.mem_nhds hp)).differentiableAt (by norm_num)
  have hcomp := hdiff.hasFDerivAt.comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) s t)
  have hscalar := hcomp.hasDerivAt.deriv
  simpa [partialSecondTwice] using hscalar

theorem iteratedDeriv_two_slice_second_eq_partialSecondTwice
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (s t : ℝ) (hp : (s, t) ∈ W) :
    iteratedDeriv 2 (fun v => G (s, v)) t =
      partialSecondTwice G (s, t) := by
  have hslice : Continuous (fun v : ℝ => (s, v)) := by fun_prop
  have hpre : IsOpen {v : ℝ | (s, v) ∈ W} := hW.preimage hslice
  have hmem : ∀ᶠ v in 𝓝 t, (s, v) ∈ W := hpre.mem_nhds hp
  have hev : (fun v => deriv (fun w => G (s, w)) v) =ᶠ[𝓝 t]
      (fun v => partialSecond G (s, v)) :=
    hmem.mono (fun v hv =>
      deriv_slice_second_eq_partialSecond hW hG s v hv)
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    iteratedDeriv_succ, iteratedDeriv_one]
  rw [hev.deriv_eq]
  exact deriv_slice_partialSecond_eq_partialSecondTwice hW hG s t hp

theorem partialFirst_partialSecond_commute
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)} {n : WithTop ℕ∞}
    (hW : IsOpen W) (hG : ContDiffOn ℝ n G W)
    (hn : (2 : WithTop ℕ∞) ≤ n)
    (p : ℝ × ℝ) (hp : p ∈ W) :
    partialFirst (partialSecond G) p =
      partialSecond (partialFirst G) p := by
  have hdiffF : DifferentiableAt ℝ (fderiv ℝ G) p :=
    ((hG.fderiv_of_isOpen hW
      (by simpa using hn : (1 : WithTop ℕ∞) + 1 ≤ n)).contDiffAt
      (hW.mem_nhds hp)).differentiableAt (by decide)
  have hfirst :
      fderiv ℝ (partialFirst G) p ((0, 1) : ℝ × ℝ) =
        fderiv ℝ (fderiv ℝ G) p (0, 1) (1, 0) := by
    have hraw := fderiv_clm_apply hdiffF
      (differentiableAt_const (c := ((1, 0) : ℝ × ℝ)))
    have happ := congrArg
      (fun (L : (ℝ × ℝ) →L[ℝ] ℝ) => L (0, 1)) hraw
    simpa [partialFirst] using happ
  have hsecond :
      fderiv ℝ (partialSecond G) p ((1, 0) : ℝ × ℝ) =
        fderiv ℝ (fderiv ℝ G) p (1, 0) (0, 1) := by
    have hraw := fderiv_clm_apply hdiffF
      (differentiableAt_const (c := ((0, 1) : ℝ × ℝ)))
    have happ := congrArg
      (fun (L : (ℝ × ℝ) →L[ℝ] ℝ) => L (1, 0)) hraw
    simpa [partialSecond] using happ
  have hsymm := (hG.contDiffAt (hW.mem_nhds hp)).isSymmSndFDerivAt
    (by simpa using hn)
  dsimp [partialFirst, partialSecond]
  rw [hsecond, hfirst]
  exact hsymm ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)

theorem partialFirst_congr_on_open
    {F H : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hEq : Set.EqOn F H W)
    (p : ℝ × ℝ) (hp : p ∈ W) :
    partialFirst F p = partialFirst H p := by
  have hmem : ∀ᶠ q in 𝓝 p, q ∈ W := hW.mem_nhds hp
  have hev : F =ᶠ[𝓝 p] H := hmem.mono (fun q hq => hEq hq)
  rw [partialFirst, partialFirst, hev.fderiv_eq]

theorem partialSecond_congr_on_open
    {F H : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hEq : Set.EqOn F H W)
    (p : ℝ × ℝ) (hp : p ∈ W) :
    partialSecond F p = partialSecond H p := by
  have hmem : ∀ᶠ q in 𝓝 p, q ∈ W := hW.mem_nhds hp
  have hev : F =ᶠ[𝓝 p] H := hmem.mono (fun q hq => hEq hq)
  rw [partialSecond, partialSecond, hev.fderiv_eq]

theorem contDiffOn_partialFirst_of_succ
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    {m n : WithTop ℕ∞}
    (hW : IsOpen W) (hG : ContDiffOn ℝ n G W)
    (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (partialFirst G) W := by
  have hfd : ContDiffOn ℝ m (fderiv ℝ G) W :=
    hG.fderiv_of_isOpen hW hmn
  have hconst : ContDiffOn ℝ m
      (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) W := contDiffOn_const
  exact hfd.clm_apply hconst

theorem contDiffOn_partialSecond_of_succ
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    {m n : WithTop ℕ∞}
    (hW : IsOpen W) (hG : ContDiffOn ℝ n G W)
    (hmn : m + 1 ≤ n) :
    ContDiffOn ℝ m (partialSecond G) W := by
  have hfd : ContDiffOn ℝ m (fderiv ℝ G) W :=
    hG.fderiv_of_isOpen hW hmn
  have hconst : ContDiffOn ℝ m
      (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) W := contDiffOn_const
  exact hfd.clm_apply hconst

theorem partialFirstTwice_partialSecondTwice_commute
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (p : ℝ × ℝ) (hp : p ∈ W) :
    partialFirstTwice (partialSecondTwice G) p =
      partialSecondTwice (partialFirstTwice G) p := by
  have hTG : ContDiffOn ℝ 3 (partialSecond G) W :=
    contDiffOn_partialSecond_of_succ hW hG (by norm_num)
  have hSG : ContDiffOn ℝ 3 (partialFirst G) W :=
    contDiffOn_partialFirst_of_succ hW hG (by norm_num)
  have hSTG : ContDiffOn ℝ 2 (partialFirst (partialSecond G)) W :=
    contDiffOn_partialFirst_of_succ hW hTG (by norm_num)
  have hGcomm : Set.EqOn (partialFirst (partialSecond G))
      (partialSecond (partialFirst G)) W := by
    intro q hq
    exact partialFirst_partialSecond_commute hW hG (by decide) q hq
  have hTGcomm : Set.EqOn (partialFirst (partialSecond (partialSecond G)))
      (partialSecond (partialFirst (partialSecond G))) W := by
    intro q hq
    exact partialFirst_partialSecond_commute hW hTG (by decide) q hq
  have hSTGcomm : Set.EqOn
      (partialFirst (partialSecond (partialFirst (partialSecond G))))
      (partialSecond (partialFirst (partialFirst (partialSecond G)))) W := by
    intro q hq
    exact partialFirst_partialSecond_commute hW hSTG (by decide) q hq
  have hSGcomm : Set.EqOn
      (partialFirst (partialSecond (partialFirst G)))
      (partialSecond (partialFirst (partialFirst G))) W := by
    intro q hq
    exact partialFirst_partialSecond_commute hW hSG (by decide) q hq
  calc
    partialFirstTwice (partialSecondTwice G) p
        = partialFirst (partialFirst (partialSecond (partialSecond G))) p := rfl
    _ = partialFirst (partialSecond (partialFirst (partialSecond G))) p :=
      partialFirst_congr_on_open hW hTGcomm p hp
    _ = partialSecond (partialFirst (partialFirst (partialSecond G))) p :=
      hSTGcomm hp
    _ = partialSecond (partialFirst (partialSecond (partialFirst G))) p := by
      apply partialSecond_congr_on_open hW _ p hp
      intro q hq
      exact partialFirst_congr_on_open hW hGcomm q hq
    _ = partialSecond (partialSecond (partialFirst (partialFirst G))) p := by
      apply partialSecond_congr_on_open hW _ p hp
      intro q hq
      exact hSGcomm hq
    _ = partialSecondTwice (partialFirstTwice G) p := rfl

theorem iteratedDeriv_two_slice_first_eq_partialFirstTwice_of_C2
    {F : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 2 F W)
    (s t : ℝ) (hp : (s, t) ∈ W) :
    iteratedDeriv 2 (fun u => F (u, t)) s =
      partialFirstTwice F (s, t) := by
  have hpre : IsOpen {u : ℝ | (u, t) ∈ W} :=
    hW.preimage (by fun_prop : Continuous (fun u : ℝ => (u, t)))
  have hmem : ∀ᶠ u in 𝓝 s, (u, t) ∈ W := hpre.mem_nhds hp
  have hfirst : ∀ u, (u, t) ∈ W →
      deriv (fun v => F (v, t)) u = partialFirst F (u, t) := by
    intro u hu
    have hdiff : DifferentiableAt ℝ F (u, t) :=
      (hF.contDiffAt (hW.mem_nhds hu)).differentiableAt (by decide)
    have hc := hdiff.hasFDerivAt.comp u
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) u t)
    simpa [partialFirst] using hc.hasDerivAt.deriv
  have hsecond : deriv (fun u => partialFirst F (u, t)) s =
      partialFirstTwice F (s, t) := by
    have hpart : ContDiffOn ℝ 1 (partialFirst F) W :=
      contDiffOn_partialFirst_of_succ hW hF (by decide)
    have hdiff : DifferentiableAt ℝ (partialFirst F) (s, t) :=
      (hpart.contDiffAt (hW.mem_nhds hp)).differentiableAt (by decide)
    have hc := hdiff.hasFDerivAt.comp s
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) s t)
    simpa [partialFirstTwice] using hc.hasDerivAt.deriv
  have hev : (fun u => deriv (fun v => F (v, t)) u) =ᶠ[𝓝 s]
      (fun u => partialFirst F (u, t)) :=
    hmem.mono (fun u hu => hfirst u hu)
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
  exact hsecond

theorem mixedFourth_eq_partialFirstTwice_partialSecondTwice
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (s t : ℝ) (hp : (s, t) ∈ W) :
    mixedFourth G s t = partialFirstTwice (partialSecondTwice G) (s, t) := by
  have hpre : IsOpen {u : ℝ | (u, t) ∈ W} :=
    hW.preimage (by fun_prop : Continuous (fun u : ℝ => (u, t)))
  have hev : (fun u => iteratedDeriv 2 (fun v => G (u, v)) t) =ᶠ[𝓝 s]
      (fun u => partialSecondTwice G (u, t)) :=
    (show ∀ᶠ u in 𝓝 s, (u, t) ∈ W from hpre.mem_nhds hp).mono
      (fun u hu =>
        iteratedDeriv_two_slice_second_eq_partialSecondTwice hW hG u t hu)
  rw [mixedFourth, hev.iteratedDeriv_eq 2]
  exact iteratedDeriv_two_slice_first_eq_partialFirstTwice_of_C2
    hW (contDiffOn_partialSecondTwice hW hG) s t hp

theorem iteratedDeriv_two_slice_second_eq_partialSecondTwice_of_C2
    {F : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 2 F W)
    (s t : ℝ) (hp : (s, t) ∈ W) :
    iteratedDeriv 2 (fun v => F (s, v)) t =
      partialSecondTwice F (s, t) := by
  have hpre : IsOpen {v : ℝ | (s, v) ∈ W} :=
    hW.preimage (by fun_prop : Continuous (fun v : ℝ => (s, v)))
  have hmem : ∀ᶠ v in 𝓝 t, (s, v) ∈ W := hpre.mem_nhds hp
  have hfirst : ∀ v, (s, v) ∈ W →
      deriv (fun w => F (s, w)) v = partialSecond F (s, v) := by
    intro v hv
    have hdiff : DifferentiableAt ℝ F (s, v) :=
      (hF.contDiffAt (hW.mem_nhds hv)).differentiableAt (by decide)
    have hc := hdiff.hasFDerivAt.comp v
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) s v)
    simpa [partialSecond] using hc.hasDerivAt.deriv
  have hsecond : deriv (fun v => partialSecond F (s, v)) t =
      partialSecondTwice F (s, t) := by
    have hpart : ContDiffOn ℝ 1 (partialSecond F) W :=
      contDiffOn_partialSecond_of_succ hW hF (by decide)
    have hdiff : DifferentiableAt ℝ (partialSecond F) (s, t) :=
      (hpart.contDiffAt (hW.mem_nhds hp)).differentiableAt (by decide)
    have hc := hdiff.hasFDerivAt.comp t
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) s t)
    simpa [partialSecondTwice] using hc.hasDerivAt.deriv
  have hev : (fun v => deriv (fun w => F (s, w)) v) =ᶠ[𝓝 t]
      (fun v => partialSecond F (s, v)) :=
    hmem.mono (fun v hv => hfirst v hv)
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
  exact hsecond

theorem mixedFourth_eq_reversed_partial
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    (s t : ℝ) (hp : (s, t) ∈ W) :
    mixedFourth G s t = partialSecondTwice (partialFirstTwice G) (s, t) := by
  rw [mixedFourth_eq_partialFirstTwice_partialSecondTwice hW hG s t hp,
    partialFirstTwice_partialSecondTwice_commute hW hG (s, t) hp]

theorem iteratedDerivWithin_two_slice_second_eq_partialSecondTwice_of_C2
    {F : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 2 F W)
    {c d s t : ℝ} (hcd : c < d) (ht : t ∈ Icc c d)
    (hp : (s, t) ∈ W) :
    iteratedDerivWithin 2 (fun v => F (s, v)) (Icc c d) t =
      partialSecondTwice F (s, t) := by
  have hpt : ContDiffAt ℝ 2 (fun v : ℝ => F (s, v)) t :=
    (hF.contDiffAt (hW.mem_nhds hp)).comp t (by fun_prop)
  rw [iteratedDerivWithin_two_eq_iteratedDeriv hcd ht hpt]
  exact iteratedDeriv_two_slice_second_eq_partialSecondTwice_of_C2 hW hF s t hp

theorem mixed_within_fourth_eq_mixedFourth
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W)
    {a b c d s t : ℝ} (hab : a < b) (hcd : c < d)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc c d)
    (hrect : (Icc a b ×ˢ Icc c d) ⊆ W) :
    iteratedDerivWithin 2
        (fun v => iteratedDerivWithin 2
          (fun u => G (u, v)) (Icc a b) s)
        (Icc c d) t = mixedFourth G s t := by
  have heq : Set.EqOn
      (fun v => iteratedDerivWithin 2 (fun u => G (u, v)) (Icc a b) s)
      (fun v => partialFirstTwice G (s, v)) (Icc c d) := by
    intro v hv
    exact iteratedDerivWithin_two_slice_first_eq_partialFirstTwice
      hW hG hab hs (hrect ⟨hs, hv⟩)
  rw [(iteratedDerivWithin_congr heq) ht]
  rw [iteratedDerivWithin_two_slice_second_eq_partialSecondTwice_of_C2
    hW (contDiffOn_partialFirstTwice hW hG) hcd ht (hrect ⟨hs, ht⟩)]
  exact (mixedFourth_eq_reversed_partial hW hG s t (hrect ⟨hs, ht⟩)).symm

theorem exists_closedBall_slice_subset
    {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    {s c d : ℝ} (hrect : ∀ t ∈ Icc c d, (s, t) ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.closedBall s ε ×ˢ Icc c d ⊆ W := by
  have hprod : W ∈ 𝓝 s ×ˢ 𝓝ˢ (Icc c d) :=
    isCompact_Icc.mem_prod_nhdsSet_of_forall (by
      intro t ht
      rw [← nhds_prod_eq]
      exact hW.mem_nhds (hrect t ht))
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp hprod
  have hs : s ∈ u := mem_of_mem_nhds hu
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨ε / 2, by positivity, ?_⟩
  have hclosed : Metric.closedBall s (ε / 2) ⊆ u :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεsub
  exact (Set.prod_mono hclosed (subset_of_mem_nhdsSet hv)).trans huv

set_option maxHeartbeats 600000 in
theorem hasDerivAt_intervalIntegral_slice_of_C1
    {F : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W)
    {s c d : ℝ} (hcd : c ≤ d)
    (hrect : ∀ t ∈ Icc c d, (s, t) ∈ W) :
    HasDerivAt
      (fun x => ∫ t in c..d, F (x, t))
      (∫ t in c..d, partialFirst F (s, t)) s := by
  obtain ⟨ε, hε, hεsub⟩ := exists_closedBall_slice_subset hW hrect
  have hK : IsCompact (Metric.closedBall s ε ×ˢ Icc c d) :=
    (isCompact_closedBall s ε).prod isCompact_Icc
  have hpart : ContinuousOn (partialFirst F) W :=
    (contDiffOn_partialFirst_of_succ (m := 0) hW hF (by decide)).continuousOn
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hpart.norm.mono hεsub)
  have hbound : ∀ x ∈ Metric.closedBall s ε, ∀ t ∈ Icc c d,
      ‖partialFirst F (x, t)‖ ≤ M := by
    intro x hx t ht
    exact hM (mem_image_of_mem _ ⟨hx, ht⟩)
  have hcont : ∀ x ∈ Metric.closedBall s ε,
      ContinuousOn (fun t => F (x, t)) (Icc c d) := by
    intro x hx
    apply hF.continuousOn.comp (by fun_prop)
    intro t ht
    exact hεsub ⟨hx, ht⟩
  have hcont' : ∀ x ∈ Metric.closedBall s ε,
      ContinuousOn (fun t => partialFirst F (x, t)) (Icc c d) := by
    intro x hx
    apply hpart.comp (by fun_prop)
    intro t ht
    exact hεsub ⟨hx, ht⟩
  have hsball : s ∈ Metric.closedBall s ε := Metric.mem_closedBall_self (by positivity)
  have hmeas : ∀ᶠ x in 𝓝 s,
      AEStronglyMeasurable (fun t => F (x, t)) (volume.restrict (Ι c d)) := by
    filter_upwards [Metric.ball_mem_nhds s hε] with x hx
    have hxc : x ∈ Metric.closedBall s ε := Metric.ball_subset_closedBall hx
    exact ((hcont x hxc).mono (by
      simpa [uIoc_of_le hcd] using Ioc_subset_Icc_self : Ι c d ⊆ Icc c d)).aestronglyMeasurable
      measurableSet_uIoc
  have hint : IntervalIntegrable (fun t => F (s, t)) volume c d :=
    (hcont s hsball).intervalIntegrable_of_Icc hcd
  have hmeas' : AEStronglyMeasurable
      (fun t => partialFirst F (s, t)) (volume.restrict (Ι c d)) :=
    ((hcont' s hsball).mono (by
      simpa [uIoc_of_le hcd] using Ioc_subset_Icc_self : Ι c d ⊆ Icc c d)).aestronglyMeasurable
      measurableSet_uIoc
  have hbound' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι c d →
      ∀ x ∈ Metric.ball s ε, ‖partialFirst F (x, t)‖ ≤ M := by
    filter_upwards [] with t
    intro ht x hx
    exact hbound x (Metric.ball_subset_closedBall hx) t
      ((by simpa [uIoc_of_le hcd] using Ioc_subset_Icc_self : Ι c d ⊆ Icc c d) ht)
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι c d →
      ∀ x ∈ Metric.ball s ε,
        HasDerivAt (fun y => F (y, t)) (partialFirst F (x, t)) x := by
    filter_upwards [] with t
    intro ht x hx
    have hxt : (x, t) ∈ W := hεsub ⟨Metric.ball_subset_closedBall hx,
      ((by simpa [uIoc_of_le hcd] using Ioc_subset_Icc_self : Ι c d ⊆ Icc c d) ht)⟩
    have hdiffF : DifferentiableAt ℝ F (x, t) :=
      (hF.contDiffAt (hW.mem_nhds hxt)).differentiableAt (by decide)
    have hc := hdiffF.hasFDerivAt.comp x
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
    simpa [partialFirst] using hc.hasDerivAt
  have hconstint : IntervalIntegrable (fun _ : ℝ => M) volume c d :=
    intervalIntegrable_const
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t => F (x, t))
    (F' := fun x t => partialFirst F (x, t))
    (bound := fun _ => M) (μ := volume) (a := c) (b := d)
    (x₀ := s) (ε := ε)
    hε hmeas hint hmeas' hbound' hconstint hdiff).2

theorem hasDerivAt_bandError_slice_of_C1
    {N : ℕ} (hN : 4 ≤ N) (k : RingIndex N)
    {F : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 1 F W)
    {s : ℝ}
    (hrect : ∀ t ∈ band N (k.val + 1), (s, t) ∈ W) :
    HasDerivAt
      (fun x => bandError N (k.val + 1) (fun t => F (x, t)))
      (bandError N (k.val + 1) (fun t => partialFirst F (s, t))) s := by
  have hk : k.val + 1 < 2 * bandParameter N := by
    have hv := k.isLt
    omega
  have hstrict := boundary_strict hN (j := k.val + 1) (by omega) hk
  have hheight : height N (k.val + 1) ∈ band N (k.val + 1) := by
    have h := height_inside_band hN (j := k.val + 1) (by omega) hk
    exact ⟨h.1.le, h.2.le⟩
  have hint := hasDerivAt_intervalIntegral_slice_of_C1 hW hF hstrict.le
    (by simpa only [band, Nat.add_sub_cancel_left] using hrect)
  have hsample : HasDerivAt
      (fun x => F (x, height N (k.val + 1)))
      (partialFirst F (s, height N (k.val + 1))) s := by
    have hdiff : DifferentiableAt ℝ F (s, height N (k.val + 1)) :=
      (hF.contDiffAt (hW.mem_nhds (hrect _ hheight))).differentiableAt (by decide)
    have hc := hdiff.hasFDerivAt.comp s
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) s (height N (k.val + 1)))
    simpa [partialFirst] using hc.hasDerivAt
  have h := (hint.const_mul ((N : ℝ) / 2)).sub
    (hsample.const_mul (population N (k.val + 1) : ℝ))
  simpa only [bandError] using h

def bandSliceDomain (N k : ℕ) (W : Set (ℝ × ℝ)) : Set ℝ :=
  {s | ∀ t ∈ band N k, (s, t) ∈ W}

theorem isOpen_bandSliceDomain
    {N k : ℕ} {W : Set (ℝ × ℝ)} (hW : IsOpen W) :
    IsOpen (bandSliceDomain N k W) := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  obtain ⟨ε, hε, hεsub⟩ := exists_closedBall_slice_subset hW
    (show ∀ t ∈ Icc (boundary N k) (boundary N (k - 1)),
      (s, t) ∈ W from hs)
  apply Filter.mem_of_superset (Metric.ball_mem_nhds s hε)
  intro x hx t ht
  exact hεsub ⟨Metric.ball_subset_closedBall hx, ht⟩

theorem bandSliceDomain_contains_outer
    {N j k : ℕ} {W : Set (ℝ × ℝ)}
    (hrect : band N j ×ˢ band N k ⊆ W) :
    band N j ⊆ bandSliceDomain N k W := by
  intro s hs t ht
  exact hrect ⟨hs, ht⟩

theorem contDiffOn_bandError_slice_C2
    {N : ℕ} (hN : 4 ≤ N) (k : RingIndex N)
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ 4 G W) :
    ContDiffOn ℝ 2
      (fun s => bandError N (k.val + 1) (fun t => G (s, t)))
      (bandSliceDomain N (k.val + 1) W) := by
  let U := bandSliceDomain N (k.val + 1) W
  let H₀ : ℝ → ℝ := fun s => bandError N (k.val + 1) (fun t => G (s, t))
  let H₁ : ℝ → ℝ := fun s => bandError N (k.val + 1) (fun t => partialFirst G (s, t))
  let H₂ : ℝ → ℝ := fun s => bandError N (k.val + 1) (fun t => partialFirstTwice G (s, t))
  have hU : IsOpen U := isOpen_bandSliceDomain hW
  have hG₁ : ContDiffOn ℝ 1 (partialFirst G) W :=
    (contDiffOn_partialFirst hW hG).of_le (by decide)
  have hG₂ : ContDiffOn ℝ 1 (partialFirstTwice G) W :=
    (contDiffOn_partialFirstTwice hW hG).of_le (by decide)
  have hd₀ : ∀ s ∈ U, HasDerivAt H₀ (H₁ s) s := by
    intro s hs
    exact hasDerivAt_bandError_slice_of_C1 hN k hW
      (hG.of_le (by decide)) hs
  have hd₁ : ∀ s ∈ U, HasDerivAt H₁ (H₂ s) s := by
    intro s hs
    exact hasDerivAt_bandError_slice_of_C1 hN k hW hG₁ hs
  have hd₂ : ∀ s ∈ U,
      DifferentiableAt ℝ H₂ s := by
    intro s hs
    exact (hasDerivAt_bandError_slice_of_C1 hN k hW hG₂ hs).differentiableAt
  have hH₀diff : DifferentiableOn ℝ H₀ U :=
    fun s hs => (hd₀ s hs).differentiableAt.differentiableWithinAt
  have hH₁diff : DifferentiableOn ℝ H₁ U :=
    fun s hs => (hd₁ s hs).differentiableAt.differentiableWithinAt
  have hH₂cont : ContinuousOn H₂ U :=
    (fun s hs => (hd₂ s hs).continuousAt.continuousWithinAt)
  have hH₁C1 : ContDiffOn ℝ 1 H₁ U := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_deriv_of_isOpen hU]
    refine ⟨hH₁diff, by simp, ?_⟩
    apply (contDiffOn_zero.mpr hH₂cont).congr
    intro s hs
    exact (hd₁ s hs).deriv
  change ContDiffOn ℝ 2 H₀ U
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨hH₀diff, by simp, ?_⟩
  apply hH₁C1.congr
  intro s hs
  exact (hd₀ s hs).deriv

theorem bandError_congr_on_band
    {N : ℕ} (hN : 4 ≤ N) (k : RingIndex N)
    {f g : ℝ → ℝ}
    (hfg : Set.EqOn f g (band N (k.val + 1))) :
    bandError N (k.val + 1) f = bandError N (k.val + 1) g := by
  have hk : k.val + 1 < 2 * bandParameter N := by
    have hv := k.isLt
    omega
  have hstrict := boundary_strict hN (j := k.val + 1) (by omega) hk
  have hheight : height N (k.val + 1) ∈ band N (k.val + 1) := by
    have h := height_inside_band hN (j := k.val + 1) (by omega) hk
    exact ⟨h.1.le, h.2.le⟩
  have hint : (∫ t in boundary N (k.val + 1)..boundary N (k.val + 1 - 1), f t) =
      (∫ t in boundary N (k.val + 1)..boundary N (k.val + 1 - 1), g t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply hfg
    simpa only [band, uIcc_of_le hstrict.le] using ht
  simp only [bandError, hint, hfg hheight]

theorem iteratedDerivWithin_bandError_eq
    {N : ℕ} (hN : 4 ≤ N) (j k : RingIndex N)
    {G : ℝ × ℝ → ℝ} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W)
    (hrect : band N (j.val + 1) ×ˢ band N (k.val + 1) ⊆ W)
    (hG : ContDiffOn ℝ 4 G W)
    {s : ℝ} (hs : s ∈ band N (j.val + 1)) :
    iteratedDerivWithin 2
      (fun u => bandError N (k.val + 1) (fun t => G (u, t)))
      (band N (j.val + 1)) s =
    bandError N (k.val + 1)
      (fun t => iteratedDerivWithin 2
        (fun u => G (u, t)) (band N (j.val + 1)) s) := by
  let U := bandSliceDomain N (k.val + 1) W
  let H₀ : ℝ → ℝ := fun u => bandError N (k.val + 1) (fun t => G (u, t))
  let H₁ : ℝ → ℝ := fun u => bandError N (k.val + 1) (fun t => partialFirst G (u, t))
  let H₂ : ℝ → ℝ := fun u => bandError N (k.val + 1) (fun t => partialFirstTwice G (u, t))
  have hU : IsOpen U := isOpen_bandSliceDomain hW
  have houter : band N (j.val + 1) ⊆ U :=
    bandSliceDomain_contains_outer hrect
  have hsU : s ∈ U := houter hs
  have hj : j.val + 1 < 2 * bandParameter N := by
    have hv := j.isLt
    omega
  have hjstrict := boundary_strict hN (j := j.val + 1) (by omega) hj
  have hC2 : ContDiffAt ℝ 2 H₀ s :=
    (contDiffOn_bandError_slice_C2 hN k hW hG).contDiffAt (hU.mem_nhds hsU)
  change iteratedDerivWithin 2 H₀
      (Icc (boundary N (j.val + 1)) (boundary N (j.val + 1 - 1))) s = _
  rw [iteratedDerivWithin_two_eq_iteratedDeriv hjstrict hs hC2]
  have hderiv₀ : Set.EqOn (deriv H₀) H₁ U := by
    intro u hu
    exact (hasDerivAt_bandError_slice_of_C1 hN k hW
      (hG.of_le (by decide)) hu).deriv
  have hpre : ∀ᶠ u in 𝓝 s, u ∈ U := hU.mem_nhds hsU
  have hev : deriv H₀ =ᶠ[𝓝 s] H₁ := hpre.mono (fun u hu => hderiv₀ hu)
  have hderiv₁ : deriv H₁ s = H₂ s :=
    (hasDerivAt_bandError_slice_of_C1 hN k hW
      ((contDiffOn_partialFirst hW hG).of_le (by decide)) hsU).deriv
  have hiter : iteratedDeriv 2 H₀ s = H₂ s := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num,
      iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
    exact hderiv₁
  rw [hiter]
  apply bandError_congr_on_band hN k
  intro t ht
  exact (iteratedDerivWithin_two_slice_first_eq_partialFirstTwice
    hW hG hjstrict hs (hrect ⟨hs, ht⟩)).symm

theorem mixedTaylorCalculusBridge : MixedTaylorCalculusBridge := by
  intro N hN j k G W hW hrect hG
  have hj : j.val + 1 < 2 * bandParameter N := by
    have hv := j.isLt
    omega
  have hk : k.val + 1 < 2 * bandParameter N := by
    have hv := k.isLt
    omega
  have hjstrict := boundary_strict hN (j := j.val + 1) (by omega) hj
  have hkstrict := boundary_strict hN (j := k.val + 1) (by omega) hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (contDiffOn_bandError_slice_C2 hN k hW hG).mono
      (bandSliceDomain_contains_outer hrect)
  · intro s hs
    exact iteratedDerivWithin_bandError_eq hN j k hW hrect hG hs
  · intro s hs
    exact contDiffOn_inner_partial hW hG hjstrict hs hrect
  · intro s hs t ht
    exact mixed_within_fourth_eq_mixedFourth hW hG hjstrict hkstrict hs ht hrect

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

/-- The concrete two-moment Taylor estimate from the actual Diamond band
moments and the proved C⁴ calculus bridge. -/
theorem mixedTaylorBound : MixedTaylorBound :=
  mixedTaylorBound_of_calculus_bridge bandMoments mixedTaylorCalculusBridge

end BEMOC.Definitive
