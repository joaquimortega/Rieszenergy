import BEMOCFormalization.ReducedCuspQuadratic
import BEMOCFormalization.TwoMomentPeano
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Fixed-square estimates for diagonal latitude cusps

Neighboring comparable latitude bands meet the diagonal, so a pointwise
fourth-derivative estimate is not available on their product rectangle.
After the common band scale is removed, however, the nonanalytic terms are
the fixed-square kernels

`|z + u - v|^(1+α)` and, at `α = 1`,
`(z + u - v)^2 log |z + u - v|`.

This file proves their uniform paired two-moment bounds.  The resonant
scaling identity produces an additional quadratic polynomial.  We prove
that polynomial lies in the biaffine nullspace of the product rule, so no
`log a` loss survives.
-/

open Set

namespace BEMOC

namespace TwoMomentFunctional

/-- Pair evaluation is linear under multiplication of the kernel by a
constant. -/
theorem pairEval_const_mul (L₁ L₂ : TwoMomentFunctional)
    (c : ℝ) (K : ℝ → ℝ → ℝ) :
    pairEval L₁ L₂ (fun s t ↦ c * K s t) =
      c * pairEval L₁ L₂ K := by
  unfold pairEval
  rw [show (fun s ↦ L₂.eval (fun t ↦ c * K s t)) =
      fun s ↦ c * L₂.eval (K s) by
        funext s
        exact L₂.map_smul c (K s)]
  exact L₁.map_smul c _

/-- Fixed-rectangle counterpart of the mixed Peano estimate.  Once the
biaffine nullspace has been discarded, boundedness of the rescaled
remainder is enough; its support widths are already normalized constants. -/
theorem abs_pairEval_le_of_biaffine_boundedRemainder
    (L₁ L₂ : TwoMomentFunctional) (K R : ℝ → ℝ → ℝ)
    (uRight vRight uLeft vLeft : ℝ → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hdecomp : ∀ s t, K s t =
      R s t + (uRight s * t + vRight s) +
        (uLeft t * s + vLeft t))
    (hbound : ∀ s ∈ Icc L₁.a L₁.b, ∀ t ∈ Icc L₂.a L₂.b,
      |R s t| ≤ B) :
    |pairEval L₁ L₂ K| ≤ L₁.variation * L₂.variation * B := by
  have hpair : pairEval L₁ L₂ K = pairEval L₁ L₂ R := by
    rw [show K = fun s t ↦
        (R s t + (uRight s * t + vRight s)) +
          (uLeft t * s + vLeft t) by
      funext s t
      exact hdecomp s t]
    rw [pairEval_add, pairEval_add,
      pairEval_affine_right, pairEval_affine_left]
    ring
  have hinner : ∀ s ∈ Icc L₁.a L₁.b,
      |L₂.eval (R s)| ≤ L₂.variation * B := by
    intro s hs
    exact L₂.abs_eval_le (R s) B hB (fun t ht ↦ hbound s hs t ht)
  have houter := L₁.abs_eval_le
    (fun s ↦ L₂.eval (R s)) (L₂.variation * B)
    (mul_nonneg L₂.variation_nonneg hB) hinner
  rw [hpair]
  simpa [pairEval, mul_assoc] using houter

/-- The translated diagonal quadratic is in the biaffine nullspace of any
product of two two-moment rules. -/
theorem pairEval_translated_sub_sq (L₁ L₂ : TwoMomentFunctional) (z : ℝ) :
    pairEval L₁ L₂ (fun u v ↦ (z + u - v) ^ 2) = 0 := by
  rw [show (fun u v : ℝ ↦ (z + u - v) ^ 2) =
      fun u v ↦
        ((-2 * (z + u)) * v + (z + u) ^ 2) +
          ((0 : ℝ) * u + v ^ 2) by
    funext u v
    ring]
  rw [pairEval_add, pairEval_affine_right, pairEval_affine_left]
  ring

end TwoMomentFunctional

/-- Translated fixed-square nonresonant cusp kernel.  The translation `z`
records the bounded separation of the centers of neighboring blocks. -/
noncomputable def fixedSquarePowerCusp
    (α z u v : ℝ) : ℝ :=
  latitudePowerBranch α (z + u - v)

/-- Translated fixed-square resonant cusp kernel. -/
noncomputable def fixedSquareResonantCusp
    (z u v : ℝ) : ℝ :=
  resonantLatitudeBranch (z + u - v)

/-- The nonanalytic power of the reduced quadratic variable `x = c w²`. -/
noncomputable def quadraticReducedPowerBranch
    (α c w : ℝ) : ℝ :=
  (c * w ^ 2) ^ ((1 + α) / 2)

/-- The resonant reduced-variable branch `x log x` after `x = c w²`. -/
noncomputable def quadraticReducedResonantBranch
    (c w : ℝ) : ℝ :=
  (c * w ^ 2) * Real.log (c * w ^ 2)

/-- Exact positive-scale homogeneity of the nonresonant branch. -/
theorem latitudePowerBranch_mul
    {α a x : ℝ} (ha : 0 ≤ a) :
    latitudePowerBranch α (a * x) =
      a ^ (1 + α) * latitudePowerBranch α x := by
  unfold latitudePowerBranch
  rw [abs_mul, abs_of_nonneg ha, Real.mul_rpow ha (abs_nonneg x)]

/-- Exact scaling identity at resonance.  The second summand is the
quadratic term which disappears under paired two-moment evaluation. -/
theorem resonantLatitudeBranch_mul
    {a x : ℝ} (ha : 0 < a) :
    resonantLatitudeBranch (a * x) =
      a ^ 2 * resonantLatitudeBranch x +
        a ^ 2 * Real.log a * x ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [resonantLatitudeBranch]
  · unfold resonantLatitudeBranch
    rw [Real.log_mul ha.ne' hx]
    ring

/-- Passing a nonresonant reduced-variable power through a positive
quadratic gap gives precisely the physical branch `|w|^(1+α)`. -/
theorem quadraticReducedPowerBranch_eq
    {α c w : ℝ} (hc : 0 ≤ c) :
    quadraticReducedPowerBranch α c w =
      c ^ ((1 + α) / 2) * latitudePowerBranch α w := by
  unfold quadraticReducedPowerBranch latitudePowerBranch
  rw [Real.mul_rpow hc (sq_nonneg w)]
  congr 1
  rw [show w ^ 2 = |w| ^ 2 by
    rw [sq_abs]]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (abs_nonneg w)]
  congr 1
  ring

/-- At resonance, the reduced branch `x log x` becomes twice the physical
`w² log |w|` branch, plus a quadratic polynomial. -/
theorem quadraticReducedResonantBranch_eq
    {c w : ℝ} (hc : 0 < c) :
    quadraticReducedResonantBranch c w =
      c * Real.log c * w ^ 2 + 2 * c * resonantLatitudeBranch w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [quadraticReducedResonantBranch, resonantLatitudeBranch]
  · unfold quadraticReducedResonantBranch resonantLatitudeBranch
    rw [Real.log_mul hc.ne' (pow_ne_zero 2 hw), Real.log_pow]
    norm_num
    ring

/-- The nonresonant cusp is continuous across the diagonal for the project
range `0 < α`. -/
theorem continuous_latitudePowerBranch
    {α : ℝ} (hα : -1 ≤ α) :
    Continuous (latitudePowerBranch α) := by
  unfold latitudePowerBranch
  exact continuous_abs.rpow_const (fun _ ↦ Or.inr (by linarith))

/-- The resonant `w² log |w|` branch is continuous at the diagonal. -/
theorem continuous_resonantLatitudeBranch :
    Continuous resonantLatitudeBranch := by
  rw [show resonantLatitudeBranch =
      fun w : ℝ ↦ w * (w * Real.log w) by
    funext w
    unfold resonantLatitudeBranch
    ring]
  exact continuous_id.mul Real.continuous_mul_log

/-- Every fixed interval has a finite uniform bound for the resonant
branch.  This includes the diagonal point, where the continuous extension
has value zero. -/
theorem exists_resonantLatitudeBranch_bound (D : ℝ) (hD : 0 ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : ℝ, |x| ≤ D → |resonantLatitudeBranch x| ≤ B := by
  have hzero : (0 : ℝ) ∈ Icc (-D) D := by
    constructor <;> linarith
  obtain ⟨x, hx, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn
      ⟨0, hzero⟩ continuous_resonantLatitudeBranch.abs.continuousOn
  refine ⟨|resonantLatitudeBranch x|, abs_nonneg _, ?_⟩
  intro y hy
  apply hmax
  exact (abs_le.mp hy)

/-- Uniform fixed-square estimate for the nonresonant cusp. -/
theorem abs_pairEval_fixedSquarePowerCusp_le
    (L₁ L₂ : TwoMomentFunctional) {α z D : ℝ}
    (hα : -1 ≤ α) (hD : 0 ≤ D)
    (hgap : ∀ u ∈ Icc L₁.a L₁.b, ∀ v ∈ Icc L₂.a L₂.b,
      |z + u - v| ≤ D) :
    |L₁.pairEval L₂ (fixedSquarePowerCusp α z)| ≤
      L₁.variation * L₂.variation * D ^ (1 + α) := by
  apply L₁.abs_pairEval_le_of_biaffine_boundedRemainder L₂
    (fixedSquarePowerCusp α z) (fixedSquarePowerCusp α z)
    (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0)
    (D ^ (1 + α))
  · exact Real.rpow_nonneg hD _
  · intro u v
    ring
  · intro u hu v hv
    unfold fixedSquarePowerCusp latitudePowerBranch
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hgap u hu v hv) (by linarith [hα])

/-- Uniform fixed-square estimate for the resonant cusp.  The constant
depends only on the fixed gap bound `D`, not on the original band scale. -/
theorem exists_abs_pairEval_fixedSquareResonantCusp_le
    (L₁ L₂ : TwoMomentFunctional) {z D : ℝ} (hD : 0 ≤ D)
    (hgap : ∀ u ∈ Icc L₁.a L₁.b, ∀ v ∈ Icc L₂.a L₂.b,
      |z + u - v| ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧
      |L₁.pairEval L₂ (fixedSquareResonantCusp z)| ≤
        L₁.variation * L₂.variation * B := by
  obtain ⟨B, hB, hbranch⟩ := exists_resonantLatitudeBranch_bound D hD
  refine ⟨B, hB, ?_⟩
  apply L₁.abs_pairEval_le_of_biaffine_boundedRemainder L₂
    (fixedSquareResonantCusp z) (fixedSquareResonantCusp z)
    (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) B hB
  · intro u v
    ring
  · intro u hu v hv
    exact hbranch _ (hgap u hu v hv)

/-- Exact product-rule reduction of a fixed-square nonresonant branch in
the quadratic reduced variable. -/
theorem pairEval_fixedSquareQuadraticReducedPower
    (L₁ L₂ : TwoMomentFunctional) {α c z : ℝ} (hc : 0 ≤ c) :
    L₁.pairEval L₂
        (fun u v ↦ quadraticReducedPowerBranch α c (z + u - v)) =
      c ^ ((1 + α) / 2) *
        L₁.pairEval L₂ (fixedSquarePowerCusp α z) := by
  rw [show
      (fun u v ↦ quadraticReducedPowerBranch α c (z + u - v)) =
        fun u v ↦
          c ^ ((1 + α) / 2) * fixedSquarePowerCusp α z u v by
    funext u v
    exact quadraticReducedPowerBranch_eq hc]
  exact L₁.pairEval_const_mul L₂ _ _

/-- Exact resonant reduction in the quadratic reduced variable.  The
`c log c` term vanishes because it multiplies a translated square. -/
theorem pairEval_fixedSquareQuadraticReducedResonant
    (L₁ L₂ : TwoMomentFunctional) {c z : ℝ} (hc : 0 < c) :
    L₁.pairEval L₂
        (fun u v ↦ quadraticReducedResonantBranch c (z + u - v)) =
      2 * c * L₁.pairEval L₂ (fixedSquareResonantCusp z) := by
  rw [show
      (fun u v ↦ quadraticReducedResonantBranch c (z + u - v)) =
        fun u v ↦
          (c * Real.log c) * (z + u - v) ^ 2 +
            (2 * c) * fixedSquareResonantCusp z u v by
    funext u v
    exact quadraticReducedResonantBranch_eq hc]
  rw [TwoMomentFunctional.pairEval_add,
    L₁.pairEval_const_mul L₂,
    L₁.pairEval_const_mul L₂,
    L₁.pairEval_translated_sub_sq L₂]
  ring

/-- Fixed-square remainder bound for a nonresonant reduced cusp composed
with the quadratic diagonal gap. -/
theorem abs_pairEval_fixedSquareQuadraticReducedPower_le
    (L₁ L₂ : TwoMomentFunctional) {α c z D : ℝ}
    (hα : -1 ≤ α) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (hgap : ∀ u ∈ Icc L₁.a L₁.b, ∀ v ∈ Icc L₂.a L₂.b,
      |z + u - v| ≤ D) :
    |L₁.pairEval L₂
        (fun u v ↦ quadraticReducedPowerBranch α c (z + u - v))| ≤
      L₁.variation * L₂.variation *
        (c ^ ((1 + α) / 2) * D ^ (1 + α)) := by
  rw [pairEval_fixedSquareQuadraticReducedPower L₁ L₂ hc,
    abs_mul, abs_of_nonneg (Real.rpow_nonneg hc _)]
  have hfixed :=
    abs_pairEval_fixedSquarePowerCusp_le L₁ L₂ hα hD hgap
  have hcPow : 0 ≤ c ^ ((1 + α) / 2) := Real.rpow_nonneg hc _
  calc
    c ^ ((1 + α) / 2) *
        |L₁.pairEval L₂ (fixedSquarePowerCusp α z)| ≤
      c ^ ((1 + α) / 2) *
        (L₁.variation * L₂.variation * D ^ (1 + α)) :=
      mul_le_mul_of_nonneg_left hfixed hcPow
    _ = _ := by ring

/-- Fixed-square remainder bound for the resonant reduced branch
`x log x` composed with a quadratic gap.  The bound has no `log c` term. -/
theorem exists_abs_pairEval_fixedSquareQuadraticReducedResonant_le
    (L₁ L₂ : TwoMomentFunctional) {c z D : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D)
    (hgap : ∀ u ∈ Icc L₁.a L₁.b, ∀ v ∈ Icc L₂.a L₂.b,
      |z + u - v| ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧
      |L₁.pairEval L₂
          (fun u v ↦ quadraticReducedResonantBranch c (z + u - v))| ≤
        L₁.variation * L₂.variation * (2 * c * B) := by
  obtain ⟨B, hB, hfixed⟩ :=
    exists_abs_pairEval_fixedSquareResonantCusp_le L₁ L₂ hD hgap
  refine ⟨B, hB, ?_⟩
  rw [pairEval_fixedSquareQuadraticReducedResonant L₁ L₂ hc,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * c)]
  calc
    (2 * c) * |L₁.pairEval L₂ (fixedSquareResonantCusp z)| ≤
      (2 * c) * (L₁.variation * L₂.variation * B) :=
      mul_le_mul_of_nonneg_left hfixed (by positivity)
    _ = _ := by ring

/-- Scaling a neighboring nonresonant cusp extracts exactly
`a^(1+α)` from the paired two-moment error. -/
theorem pairEval_scaled_fixedSquarePowerCusp
    (L₁ L₂ : TwoMomentFunctional) {α z a : ℝ} (ha : 0 ≤ a) :
    L₁.pairEval L₂
        (fun u v ↦ latitudePowerBranch α (a * (z + u - v))) =
      a ^ (1 + α) *
        L₁.pairEval L₂ (fixedSquarePowerCusp α z) := by
  rw [show (fun u v ↦ latitudePowerBranch α (a * (z + u - v))) =
      fun u v ↦ a ^ (1 + α) * fixedSquarePowerCusp α z u v by
    funext u v
    exact latitudePowerBranch_mul ha]
  exact L₁.pairEval_const_mul L₂ _ _

/-- Quantitative scaled fixed-square bound for the nonresonant cusp. -/
theorem abs_pairEval_scaled_fixedSquarePowerCusp_le
    (L₁ L₂ : TwoMomentFunctional) {α z a D : ℝ}
    (hα : -1 ≤ α) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hgap : ∀ u ∈ Icc L₁.a L₁.b, ∀ v ∈ Icc L₂.a L₂.b,
      |z + u - v| ≤ D) :
    |L₁.pairEval L₂
        (fun u v ↦ latitudePowerBranch α (a * (z + u - v)))| ≤
      L₁.variation * L₂.variation *
        (a ^ (1 + α) * D ^ (1 + α)) := by
  rw [pairEval_scaled_fixedSquarePowerCusp L₁ L₂ ha, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ha _)]
  have hfixed :=
    abs_pairEval_fixedSquarePowerCusp_le L₁ L₂ hα hD hgap
  have hscale : 0 ≤ a ^ (1 + α) := Real.rpow_nonneg ha _
  calc
    a ^ (1 + α) *
        |L₁.pairEval L₂ (fixedSquarePowerCusp α z)| ≤
      a ^ (1 + α) *
        (L₁.variation * L₂.variation * D ^ (1 + α)) :=
      mul_le_mul_of_nonneg_left hfixed hscale
    _ = _ := by ring

/-- At resonance, the `a² log a` correction is a translated quadratic and
is killed exactly by the biaffine nullspace.  Thus only the clean `a²`
factor remains. -/
theorem pairEval_scaled_fixedSquareResonantCusp
    (L₁ L₂ : TwoMomentFunctional) {z a : ℝ} (ha : 0 < a) :
    L₁.pairEval L₂
        (fun u v ↦ resonantLatitudeBranch (a * (z + u - v))) =
      a ^ 2 * L₁.pairEval L₂ (fixedSquareResonantCusp z) := by
  rw [show (fun u v ↦ resonantLatitudeBranch (a * (z + u - v))) =
      fun u v ↦
        a ^ 2 * fixedSquareResonantCusp z u v +
          (a ^ 2 * Real.log a) * (z + u - v) ^ 2 by
    funext u v
    exact resonantLatitudeBranch_mul ha]
  rw [TwoMomentFunctional.pairEval_add,
    L₁.pairEval_const_mul L₂,
    L₁.pairEval_const_mul L₂,
    L₁.pairEval_translated_sub_sq L₂]
  ring

/-- Quantitative resonant fixed-square estimate after restoring the common
band scale.  In particular, no logarithm of that scale occurs. -/
theorem exists_abs_pairEval_scaled_fixedSquareResonantCusp_le
    (L₁ L₂ : TwoMomentFunctional) {z a D : ℝ}
    (ha : 0 < a) (hD : 0 ≤ D)
    (hgap : ∀ u ∈ Icc L₁.a L₁.b, ∀ v ∈ Icc L₂.a L₂.b,
      |z + u - v| ≤ D) :
    ∃ B : ℝ, 0 ≤ B ∧
      |L₁.pairEval L₂
          (fun u v ↦ resonantLatitudeBranch (a * (z + u - v)))| ≤
        L₁.variation * L₂.variation * (a ^ 2 * B) := by
  obtain ⟨B, hB, hfixed⟩ :=
    exists_abs_pairEval_fixedSquareResonantCusp_le L₁ L₂ hD hgap
  refine ⟨B, hB, ?_⟩
  rw [pairEval_scaled_fixedSquareResonantCusp L₁ L₂ ha,
    abs_mul, abs_of_nonneg (sq_nonneg a)]
  calc
    a ^ 2 * |L₁.pairEval L₂ (fixedSquareResonantCusp z)| ≤
      a ^ 2 * (L₁.variation * L₂.variation * B) :=
      mul_le_mul_of_nonneg_left hfixed (sq_nonneg a)
    _ = _ := by ring

end BEMOC
