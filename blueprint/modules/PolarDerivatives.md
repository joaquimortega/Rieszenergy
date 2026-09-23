# Polar derivatives of the chordal power

Source: `definitive.tex`, Lemma `derivative-bounds`, especially equation
`polar-derivatives`. The statement to prove is `PolarDerivativeBound α` from
`BEMOCFormalization/KernelDerivatives.lean`, with `0 < α < 2`. This is a
pointwise estimate on the open set where the squared chordal distance is
positive. The coefficient may depend on α, but it must be uniform in θ, φ,
ψ and in all fifteen pairs `(m,n)` with `m+n≤4`. The definition permits θ,
φ,ψ to be arbitrary real numbers, not only their geometric ranges.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.KernelDerivatives

namespace BEMOC.Definitive

/-- Squared chordal distance in the polar variables. -/
private noncomputable def polarChordSq (θ φ ψ : ℝ) : ℝ :=
  2 - 2 * (Real.cos φ * Real.cos ψ + Real.sin φ * Real.sin ψ * Real.cos θ)

private lemma polarChordSq_eq_sum_sq (θ φ ψ : ℝ) :
    polarChordSq θ φ ψ =
      (Real.sin φ * Real.cos θ - Real.sin ψ) ^ 2 +
      (Real.sin φ * Real.sin θ) ^ 2 +
      (Real.cos φ - Real.cos ψ) ^ 2 := by
  unfold polarChordSq
  nlinarith [Real.sin_sq_add_cos_sq φ, Real.sin_sq_add_cos_sq ψ,
    Real.sin_sq_add_cos_sq θ]

private lemma polarChordSq_nonneg (θ φ ψ : ℝ) : 0 ≤ polarChordSq θ φ ψ := by
  rw [polarChordSq_eq_sum_sq]
  positivity

private lemma polarChordSq_le_six (θ φ ψ : ℝ) : polarChordSq θ φ ψ ≤ 6 := by
  have hc : |Real.cos φ * Real.cos ψ| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _)
  have hs : |Real.sin φ * Real.sin ψ * Real.cos θ| ≤ 1 := by
    rw [abs_mul, abs_mul]
    exact mul_le_one₀
      (mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_sin_le_one _))
      (abs_nonneg _) (Real.abs_cos_le_one _)
  unfold polarChordSq
  have hc' := (abs_le.mp hc).1
  have hs' := (abs_le.mp hs).1
  linarith

private lemma hasDerivAt_polarChordSq_phi (θ φ ψ : ℝ) :
    HasDerivAt (fun u => polarChordSq θ u ψ)
      (2 * (Real.sin φ * Real.cos ψ - Real.cos φ * Real.sin ψ * Real.cos θ)) φ := by
  unfold polarChordSq
  convert (((Real.hasDerivAt_cos φ).mul_const (Real.cos ψ)).add
    (((Real.hasDerivAt_sin φ).mul_const (Real.sin ψ)).mul_const (Real.cos θ))
    |>.const_mul 2 |>.const_sub 2) using 1
  ring

private lemma hasDerivAt_polarChordSq_psi (θ φ ψ : ℝ) :
    HasDerivAt (fun v => polarChordSq θ φ v)
      (2 * (Real.cos φ * Real.sin ψ - Real.sin φ * Real.cos ψ * Real.cos θ)) ψ := by
  unfold polarChordSq
  convert (((Real.hasDerivAt_cos ψ).const_mul (Real.cos φ)).add
    (((Real.hasDerivAt_sin ψ).const_mul (Real.sin φ)).mul_const (Real.cos θ))
    |>.const_mul 2 |>.const_sub 2) using 1
  ring

private lemma hasDerivAt_polarKernel_phi (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt (fun u => polarKernel α θ u ψ)
      ((α / 2) * (polarChordSq θ φ ψ) ^ (α / 2 - 1) *
        (2 * (Real.sin φ * Real.cos ψ - Real.cos φ * Real.sin ψ * Real.cos θ))) φ := by
  change HasDerivAt (fun u => (polarChordSq θ u ψ) ^ (α / 2)) _ φ
  convert (Real.hasDerivAt_rpow_const (p := α / 2) (Or.inl hA.ne')).comp φ
    (hasDerivAt_polarChordSq_phi θ φ ψ) using 1

private lemma three_square_cauchy (a b c d e f : ℝ) :
    (a * d + b * e + c * f) ^ 2 ≤
      (a ^ 2 + b ^ 2 + c ^ 2) * (d ^ 2 + e ^ 2 + f ^ 2) := by
  nlinarith [sq_nonneg (a * e - b * d), sq_nonneg (a * f - c * d),
    sq_nonneg (b * f - c * e)]

private lemma polarChordSq_le_four (θ φ ψ : ℝ) : polarChordSq θ φ ψ ≤ 4 := by
  have hx : (Real.sin φ * Real.cos θ) ^ 2 +
      (Real.sin φ * Real.sin θ) ^ 2 + (Real.cos φ) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]
  have hy : (Real.sin ψ) ^ 2 + (0 : ℝ) ^ 2 + (Real.cos ψ) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq ψ]
  have hc := three_square_cauchy
    (Real.sin φ * Real.cos θ) (Real.sin φ * Real.sin θ) (Real.cos φ)
    (Real.sin ψ) 0 (Real.cos ψ)
  rw [hx, hy, one_mul] at hc
  have hdot : Real.sin φ * Real.cos θ * Real.sin ψ +
      Real.sin φ * Real.sin θ * 0 + Real.cos φ * Real.cos ψ =
      Real.cos φ * Real.cos ψ + Real.sin φ * Real.sin ψ * Real.cos θ := by ring
  rw [hdot] at hc
  unfold polarChordSq
  nlinarith

private lemma abs_polarChordSq_cross_le_two (θ φ ψ : ℝ) :
    |2 * (Real.sin φ * Real.sin ψ +
      Real.cos φ * Real.cos ψ * Real.cos θ)| ≤ 2 := by
  have hx : (Real.sin φ) ^ 2 + (Real.cos φ * Real.cos θ) ^ 2 +
      (Real.cos φ * Real.sin θ) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]
  have hy : (Real.sin ψ) ^ 2 + (Real.cos ψ) ^ 2 + (0 : ℝ) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq ψ]
  have hc := three_square_cauchy (Real.sin φ) (Real.cos φ * Real.cos θ)
    (Real.cos φ * Real.sin θ) (Real.sin ψ) (Real.cos ψ) 0
  rw [hx, hy, one_mul] at hc
  have hdot : Real.sin φ * Real.sin ψ + Real.cos φ * Real.cos θ * Real.cos ψ +
      Real.cos φ * Real.sin θ * 0 =
      Real.sin φ * Real.sin ψ + Real.cos φ * Real.cos ψ * Real.cos θ := by ring
  rw [hdot] at hc
  have hbound : |Real.sin φ * Real.sin ψ +
      Real.cos φ * Real.cos ψ * Real.cos θ| ≤ 1 := by
    nlinarith [sq_abs (Real.sin φ * Real.sin ψ +
      Real.cos φ * Real.cos ψ * Real.cos θ)]
  simpa [abs_mul] using (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2))

private noncomputable def polarChordPhi (θ φ ψ : ℝ) : ℝ :=
  2 * (Real.sin φ * Real.cos ψ - Real.cos φ * Real.sin ψ * Real.cos θ)

private noncomputable def polarChordPsi (θ φ ψ : ℝ) : ℝ :=
  2 * (Real.cos φ * Real.sin ψ - Real.sin φ * Real.cos ψ * Real.cos θ)

private noncomputable def polarChordCross (θ φ ψ : ℝ) : ℝ :=
  -2 * (Real.sin φ * Real.sin ψ + Real.cos φ * Real.cos ψ * Real.cos θ)

private lemma abs_polarChordCross_le_two (θ φ ψ : ℝ) :
    |polarChordCross θ φ ψ| ≤ 2 := by
  simpa [polarChordCross, abs_neg] using abs_polarChordSq_cross_le_two θ φ ψ

private lemma hasDerivAt_polarChordPhi_phi (θ φ ψ : ℝ) :
    HasDerivAt (fun u => polarChordPhi θ u ψ) (2 - polarChordSq θ φ ψ) φ := by
  unfold polarChordPhi polarChordSq
  convert (((Real.hasDerivAt_sin φ).mul_const (Real.cos ψ)).sub
    (((Real.hasDerivAt_cos φ).mul_const (Real.sin ψ)).mul_const (Real.cos θ))
    |>.const_mul 2) using 1
  ring

private lemma hasDerivAt_polarChordPhi_psi (θ φ ψ : ℝ) :
    HasDerivAt (fun v => polarChordPhi θ φ v) (polarChordCross θ φ ψ) ψ := by
  unfold polarChordPhi polarChordCross
  convert (((Real.hasDerivAt_cos ψ).const_mul (Real.sin φ)).sub
    (((Real.hasDerivAt_sin ψ).const_mul (Real.cos φ)).mul_const (Real.cos θ))
    |>.const_mul 2) using 1
  ring

private lemma hasDerivAt_polarChordPsi_phi (θ φ ψ : ℝ) :
    HasDerivAt (fun u => polarChordPsi θ u ψ) (polarChordCross θ φ ψ) φ := by
  unfold polarChordPsi polarChordCross
  convert (((Real.hasDerivAt_cos φ).mul_const (Real.sin ψ)).sub
    (((Real.hasDerivAt_sin φ).mul_const (Real.cos ψ)).mul_const (Real.cos θ))
    |>.const_mul 2) using 1
  ring

private lemma hasDerivAt_polarChordPsi_psi (θ φ ψ : ℝ) :
    HasDerivAt (fun v => polarChordPsi θ φ v) (2 - polarChordSq θ φ ψ) ψ := by
  unfold polarChordPsi polarChordSq
  convert (((Real.hasDerivAt_sin ψ).const_mul (Real.cos φ)).sub
    (((Real.hasDerivAt_cos ψ).const_mul (Real.sin φ)).mul_const (Real.cos θ))
    |>.const_mul 2) using 1
  ring

private lemma hasDerivAt_polarChordCross_phi (θ φ ψ : ℝ) :
    HasDerivAt (fun u => polarChordCross θ u ψ) (-polarChordPsi θ φ ψ) φ := by
  unfold polarChordCross polarChordPsi
  convert (((Real.hasDerivAt_sin φ).mul_const (Real.sin ψ)).add
    (((Real.hasDerivAt_cos φ).mul_const (Real.cos ψ)).mul_const (Real.cos θ))
    |>.const_mul (-2)) using 1
  ring

private lemma hasDerivAt_polarChordCross_psi (θ φ ψ : ℝ) :
    HasDerivAt (fun v => polarChordCross θ φ v) (-polarChordPhi θ φ ψ) ψ := by
  unfold polarChordCross polarChordPhi
  convert (((Real.hasDerivAt_sin ψ).const_mul (Real.sin φ)).add
    (((Real.hasDerivAt_cos ψ).const_mul (Real.cos φ)).mul_const (Real.cos θ))
    |>.const_mul (-2)) using 1
  ring

private lemma hasDerivAt_polarChordSq_rpow_phi (q θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt (fun u => polarChordSq θ u ψ ^ q)
      (q * polarChordSq θ φ ψ ^ (q - 1) * polarChordPhi θ φ ψ) φ := by
  convert (Real.hasDerivAt_rpow_const (p := q) (Or.inl hA.ne')).comp φ
    (hasDerivAt_polarChordSq_phi θ φ ψ) using 1

private lemma hasDerivAt_polarChordSq_rpow_psi (q θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt (fun v => polarChordSq θ φ v ^ q)
      (q * polarChordSq θ φ ψ ^ (q - 1) * polarChordPsi θ φ ψ) ψ := by
  convert (Real.hasDerivAt_rpow_const (p := q) (Or.inl hA.ne')).comp ψ
    (hasDerivAt_polarChordSq_psi θ φ ψ) using 1

private lemma abs_two_sub_polarChordSq_le (θ φ ψ : ℝ) :
    |2 - polarChordSq θ φ ψ| ≤ 2 := by
  have h₀ := polarChordSq_nonneg θ φ ψ
  have h₄ := polarChordSq_le_four θ φ ψ
  rw [abs_le]
  constructor <;> linarith

private lemma polarChordSq_symm (θ φ ψ : ℝ) :
    polarChordSq θ φ ψ = polarChordSq θ ψ φ := by
  unfold polarChordSq
  ring

private lemma polarKernel_symm (α θ φ ψ : ℝ) :
    polarKernel α θ φ ψ = polarKernel α θ ψ φ := by
  unfold polarKernel
  ring

private lemma polarChordSq_phi_sq_le (θ φ ψ : ℝ) :
    (Real.sin φ * Real.cos ψ - Real.cos φ * Real.sin ψ * Real.cos θ) ^ 2 ≤
      polarChordSq θ φ ψ := by
  let a := Real.sin φ * Real.cos θ - Real.sin ψ
  let b := Real.sin φ * Real.sin θ
  let c := Real.cos φ - Real.cos ψ
  let d := Real.cos φ * Real.cos θ
  let e := Real.cos φ * Real.sin θ
  let f := -Real.sin φ
  have hz : a ^ 2 + b ^ 2 + c ^ 2 = polarChordSq θ φ ψ := by
    simpa [a, b, c] using (polarChordSq_eq_sum_sq θ φ ψ).symm
  have hw : d ^ 2 + e ^ 2 + f ^ 2 = 1 := by
    dsimp [d, e, f]
    nlinarith [Real.sin_sq_add_cos_sq φ, Real.sin_sq_add_cos_sq θ]
  have hdot : a * d + b * e + c * f =
      Real.sin φ * Real.cos ψ - Real.cos φ * Real.sin ψ * Real.cos θ := by
    dsimp [a, b, c, d, e, f]
    nlinarith [congrArg (fun x : ℝ => Real.sin φ * Real.cos φ * x)
      (Real.sin_sq_add_cos_sq θ)]
  have h := three_square_cauchy a b c d e f
  rw [hz, hw, mul_one, hdot] at h
  exact h

private lemma abs_polarChordPhi_le (θ φ ψ : ℝ) :
    |polarChordPhi θ φ ψ| ≤ 2 * Real.sqrt (polarChordSq θ φ ψ) := by
  rw [polarChordPhi, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left
    (Real.abs_le_sqrt (polarChordSq_phi_sq_le θ φ ψ)) (by norm_num)

private lemma polarChordSq_psi_sq_le (θ φ ψ : ℝ) :
    (Real.cos φ * Real.sin ψ - Real.sin φ * Real.cos ψ * Real.cos θ) ^ 2 ≤
      polarChordSq θ φ ψ := by
  let a := Real.sin φ * Real.cos θ - Real.sin ψ
  let b := Real.sin φ * Real.sin θ
  let c := Real.cos φ - Real.cos ψ
  let d := -Real.cos ψ
  let e := (0 : ℝ)
  let f := Real.sin ψ
  have hz : a ^ 2 + b ^ 2 + c ^ 2 = polarChordSq θ φ ψ := by
    simpa [a, b, c] using (polarChordSq_eq_sum_sq θ φ ψ).symm
  have hw : d ^ 2 + e ^ 2 + f ^ 2 = 1 := by
    dsimp [d, e, f]
    nlinarith [Real.sin_sq_add_cos_sq ψ]
  have hdot : a * d + b * e + c * f =
      Real.cos φ * Real.sin ψ - Real.sin φ * Real.cos ψ * Real.cos θ := by
    dsimp [a, b, c, d, e, f]
    ring
  have h := three_square_cauchy a b c d e f
  rw [hz, hw, mul_one, hdot] at h
  exact h

private lemma abs_polarChordPsi_le (θ φ ψ : ℝ) :
    |polarChordPsi θ φ ψ| ≤ 2 * Real.sqrt (polarChordSq θ φ ψ) := by
  rw [polarChordPsi, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left
    (Real.abs_le_sqrt (polarChordSq_psi_sq_le θ φ ψ)) (by norm_num)

private lemma hasDerivAt_polarKernel_psi (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt (fun v => polarKernel α θ φ v)
      ((α / 2) * (polarChordSq θ φ ψ) ^ (α / 2 - 1) *
        (2 * (Real.cos φ * Real.sin ψ - Real.sin φ * Real.cos ψ * Real.cos θ))) ψ := by
  change HasDerivAt (fun v => (polarChordSq θ φ v) ^ (α / 2)) _ ψ
  convert (Real.hasDerivAt_rpow_const (p := α / 2) (Or.inl hA.ne')).comp ψ
    (hasDerivAt_polarChordSq_psi θ φ ψ) using 1

private lemma abs_deriv_polarKernel_phi_le (α θ φ ψ : ℝ) (hα : 0 ≤ α)
    (hA : 0 < polarChordSq θ φ ψ) :
    |deriv (fun u => polarKernel α θ u ψ) φ| ≤
      α * (polarChordSq θ φ ψ) ^ ((α - 1) / 2) := by
  let A := polarChordSq θ φ ψ
  let E := Real.sin φ * Real.cos ψ - Real.cos φ * Real.sin ψ * Real.cos θ
  have hE : |E| ≤ Real.sqrt A := Real.abs_le_sqrt (polarChordSq_phi_sq_le θ φ ψ)
  have hApow : 0 ≤ A ^ (α / 2 - 1) := (Real.rpow_pos_of_pos hA _).le
  have hsqrt : A ^ (α / 2 - 1) * Real.sqrt A = A ^ ((α - 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hA]
    congr 1
    ring
  rw [(hasDerivAt_polarKernel_phi α θ φ ψ hA).deriv]
  dsimp [A, E] at *
  have hα2 : 0 ≤ α / 2 := by positivity
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hα2, abs_of_nonneg hApow,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  calc
    α / 2 * polarChordSq θ φ ψ ^ (α / 2 - 1) * (2 * |E|) =
        α * (polarChordSq θ φ ψ ^ (α / 2 - 1) * |E|) := by ring
    _ ≤ α * (polarChordSq θ φ ψ ^ (α / 2 - 1) * Real.sqrt (polarChordSq θ φ ψ)) := by
      gcongr
    _ = _ := by rw [hsqrt]

private lemma abs_deriv_polarKernel_psi_le (α θ φ ψ : ℝ) (hα : 0 ≤ α)
    (hA : 0 < polarChordSq θ φ ψ) :
    |deriv (fun v => polarKernel α θ φ v) ψ| ≤
      α * (polarChordSq θ φ ψ) ^ ((α - 1) / 2) := by
  let A := polarChordSq θ φ ψ
  let E := Real.cos φ * Real.sin ψ - Real.sin φ * Real.cos ψ * Real.cos θ
  have hE : |E| ≤ Real.sqrt A := Real.abs_le_sqrt (polarChordSq_psi_sq_le θ φ ψ)
  have hApow : 0 ≤ A ^ (α / 2 - 1) := (Real.rpow_pos_of_pos hA _).le
  have hsqrt : A ^ (α / 2 - 1) * Real.sqrt A = A ^ ((α - 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hA]
    congr 1
    ring
  rw [(hasDerivAt_polarKernel_psi α θ φ ψ hA).deriv]
  dsimp [A, E] at *
  have hα2 : 0 ≤ α / 2 := by positivity
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hα2, abs_of_nonneg hApow,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  calc
    α / 2 * polarChordSq θ φ ψ ^ (α / 2 - 1) * (2 * |E|) =
        α * (polarChordSq θ φ ψ ^ (α / 2 - 1) * |E|) := by ring
    _ ≤ α * (polarChordSq θ φ ψ ^ (α / 2 - 1) * Real.sqrt (polarChordSq θ φ ψ)) := by
      gcongr
    _ = _ := by rw [hsqrt]

/-- The zeroth- and first-order cases of the polar derivative estimate. -/
theorem polar_derivative_bound_one {α : ℝ} (hα : 0 ≤ α) :
    ∀ m n : ℕ, m + n ≤ 1 → ∀ θ φ ψ : ℝ,
      0 < 2 - 2 * (Real.cos φ * Real.cos ψ +
        Real.sin φ * Real.sin ψ * Real.cos θ) →
      |iteratedDeriv m
        (fun u => iteratedDeriv n (fun v => polarKernel α θ u v) ψ) φ| ≤
        (α + 1) *
        (2 - 2 * (Real.cos φ * Real.cos ψ +
          Real.sin φ * Real.sin ψ * Real.cos θ)) ^ ((α - m - n) / 2) := by
  intro m n hmn θ φ ψ hA
  have hm : m ≤ 1 := by omega
  have hn : n ≤ 1 := by omega
  interval_cases m <;> interval_cases n
  · simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, polarKernel]
    have hpow : 0 <
        (2 - 2 * (Real.cos φ * Real.cos ψ +
          Real.sin φ * Real.sin ψ * Real.cos θ)) ^ (α / 2) :=
      Real.rpow_pos_of_pos hA _
    rw [abs_of_pos hpow]
    nlinarith
  · simpa only [iteratedDeriv_zero, iteratedDeriv_one, Nat.cast_zero, Nat.cast_one,
      sub_zero, polarChordSq] using
      (abs_deriv_polarKernel_psi_le α θ φ ψ hα hA).trans
        (by
          apply mul_le_mul_of_nonneg_right
          · linarith
          · positivity)
  · simpa only [iteratedDeriv_zero, iteratedDeriv_one, Nat.cast_zero, Nat.cast_one,
      sub_zero, polarChordSq] using
      (abs_deriv_polarKernel_phi_le α θ φ ψ hα hA).trans
        (by
          apply mul_le_mul_of_nonneg_right
          · linarith
          · positivity)
  · omega

private def rpowFalling (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (p - n) * rpowFalling p n

private lemma iteratedDeriv_rpow_of_pos (p : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (fun y : ℝ => y ^ p) x =
      rpowFalling p n * x ^ (p - n) := by
  induction n generalizing x with
  | zero => simp [iteratedDeriv_zero, rpowFalling]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n (fun y : ℝ => y ^ p) =ᶠ[nhds x]
          fun y => rpowFalling p n * y ^ (p - n) := by
        filter_upwards [eventually_gt_nhds hx] with y hy
        exact ih hy
      rw [heq.deriv_eq]
      rw [((Real.hasDerivAt_rpow_const
        (p := p - n) (Or.inl hx.ne')).const_mul (rpowFalling p n)).deriv]
      simp only [rpowFalling]
      push_cast
      ring

private lemma abs_iteratedDeriv_rpow_le (p : ℝ) (n : ℕ) {x : ℝ}
    (hx : 0 < x) (hn : n ≤ 4) :
    |iteratedDeriv n (fun y : ℝ => y ^ p) x| ≤
      (∑ k ∈ Finset.range 5, |rpowFalling p k|) * x ^ (p - n) := by
  rw [iteratedDeriv_rpow_of_pos p n hx, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hx _)]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun k _ => abs_nonneg (rpowFalling p k))
      (Finset.mem_range.mpr (by omega)))
    (Real.rpow_pos_of_pos hx _).le

private noncomputable def polarJet20 (p θ φ ψ : ℝ) : ℝ :=
  p * (p - 1) * polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ ^ 2 +
    p * polarChordSq θ φ ψ ^ (p - 1) * (2 - polarChordSq θ φ ψ)

private lemma hasDerivAt_polarJet10_phi (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt
      (fun u => p * polarChordSq θ u ψ ^ (p - 1) * polarChordPhi θ u ψ)
      (polarJet20 p θ φ ψ) φ := by
  have hpow : HasDerivAt (fun u => polarChordSq θ u ψ ^ (p - 1))
      ((p - 1) * polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ) φ := by
    convert (Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hA.ne')).comp φ
      (hasDerivAt_polarChordSq_phi θ φ ψ) using 1
    simp only [polarChordPhi]
    ring
  convert ((hpow.const_mul p).mul (hasDerivAt_polarChordPhi_phi θ φ ψ)) using 1
  unfold polarJet20
  ring

private lemma iteratedDeriv_two_polarKernel_phi_eq (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    iteratedDeriv 2 (fun u => polarKernel α θ u ψ) φ =
      polarJet20 (α / 2) θ φ ψ := by
  have hpos : ∀ᶠ u in nhds φ, 0 < polarChordSq θ u ψ :=
    (hasDerivAt_polarChordSq_phi θ φ ψ).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hA)
  have heq : (fun u => deriv (fun v => polarKernel α θ v ψ) u) =ᶠ[nhds φ]
      fun u => (α / 2) * polarChordSq θ u ψ ^ (α / 2 - 1) *
        polarChordPhi θ u ψ := by
    filter_upwards [hpos] with u hu
    rw [(hasDerivAt_polarKernel_phi α θ u ψ hu).deriv]
    simp [polarChordPhi]
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [heq.deriv_eq]
  exact (hasDerivAt_polarJet10_phi (α / 2) θ φ ψ hA).deriv

private noncomputable def polarJet11 (p θ φ ψ : ℝ) : ℝ :=
  p * (p - 1) * polarChordSq θ φ ψ ^ (p - 2) *
      polarChordPhi θ φ ψ * polarChordPsi θ φ ψ +
    p * polarChordSq θ φ ψ ^ (p - 1) * polarChordCross θ φ ψ

private lemma hasDerivAt_polarJet01_phi (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt
      (fun u => p * polarChordSq θ u ψ ^ (p - 1) * polarChordPsi θ u ψ)
      (polarJet11 p θ φ ψ) φ := by
  have hpow : HasDerivAt (fun u => polarChordSq θ u ψ ^ (p - 1))
      ((p - 1) * polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ) φ := by
    convert (Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hA.ne')).comp φ
      (hasDerivAt_polarChordSq_phi θ φ ψ) using 1
    simp only [polarChordPhi]
    ring
  convert ((hpow.const_mul p).mul (hasDerivAt_polarChordPsi_phi θ φ ψ)) using 1
  unfold polarJet11
  ring

private lemma iteratedDeriv_one_one_polarKernel_eq (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    iteratedDeriv 1
      (fun u => iteratedDeriv 1 (fun v => polarKernel α θ u v) ψ) φ =
      polarJet11 (α / 2) θ φ ψ := by
  have hpos : ∀ᶠ u in nhds φ, 0 < polarChordSq θ u ψ :=
    (hasDerivAt_polarChordSq_phi θ φ ψ).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hA)
  have heq : (fun u => iteratedDeriv 1 (fun v => polarKernel α θ u v) ψ) =ᶠ[nhds φ]
      fun u => (α / 2) * polarChordSq θ u ψ ^ (α / 2 - 1) *
        polarChordPsi θ u ψ := by
    filter_upwards [hpos] with u hu
    rw [iteratedDeriv_one, (hasDerivAt_polarKernel_psi α θ u ψ hu).deriv]
    simp [polarChordPsi]
  rw [iteratedDeriv_one, heq.deriv_eq]
  exact (hasDerivAt_polarJet01_phi (α / 2) θ φ ψ hA).deriv

private noncomputable def polarJet30 (p θ φ ψ : ℝ) : ℝ :=
  p * (p - 1) * (p - 2) * polarChordSq θ φ ψ ^ (p - 3) *
      polarChordPhi θ φ ψ ^ 3 +
    3 * p * (p - 1) * polarChordSq θ φ ψ ^ (p - 2) *
      polarChordPhi θ φ ψ * (2 - polarChordSq θ φ ψ) -
    p * polarChordSq θ φ ψ ^ (p - 1) * polarChordPhi θ φ ψ

private lemma hasDerivAt_polarJet20_phi (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt (fun u => polarJet20 p θ u ψ) (polarJet30 p θ φ ψ) φ := by
  let a := polarChordSq θ φ ψ
  let x := polarChordPhi θ φ ψ
  let b := 2 - a
  have ha := hasDerivAt_polarChordSq_phi θ φ ψ
  have ha' : HasDerivAt (fun u => polarChordSq θ u ψ) x φ := by
    simpa [x, polarChordPhi] using ha
  have hx := hasDerivAt_polarChordPhi_phi θ φ ψ
  have hp2 := hasDerivAt_polarChordSq_rpow_phi (p - 2) θ φ ψ hA
  have hp1 := hasDerivAt_polarChordSq_rpow_phi (p - 1) θ φ ψ hA
  have hterm1 := ((hp2.mul (hx.pow 2)).const_mul (p * (p - 1)))
  have hterm2 := (((hp1.const_mul p).mul (ha'.const_sub 2)))
  have hsum := hterm1.add hterm2
  convert hsum using 1
  · ext u
    simp only [polarJet20]
    ring
  · unfold polarJet30
    dsimp [a, x, b] at *
    ring

private lemma iteratedDeriv_three_polarKernel_phi_eq (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    iteratedDeriv 3 (fun u => polarKernel α θ u ψ) φ =
      polarJet30 (α / 2) θ φ ψ := by
  have hpos : ∀ᶠ u in nhds φ, 0 < polarChordSq θ u ψ :=
    (hasDerivAt_polarChordSq_phi θ φ ψ).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hA)
  have heq : (fun u => iteratedDeriv 2 (fun v => polarKernel α θ v ψ) u) =ᶠ[nhds φ]
      fun u => polarJet20 (α / 2) θ u ψ := by
    filter_upwards [hpos] with u hu
    exact iteratedDeriv_two_polarKernel_phi_eq α θ u ψ hu
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ, heq.deriv_eq]
  exact (hasDerivAt_polarJet20_phi (α / 2) θ φ ψ hA).deriv

private lemma iteratedDeriv_two_polarKernel_psi_eq (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    iteratedDeriv 2 (fun v => polarKernel α θ φ v) ψ =
      polarJet20 (α / 2) θ ψ φ := by
  have hfun : (fun v => polarKernel α θ φ v) =
      (fun v => polarKernel α θ v φ) := by
    funext v
    exact polarKernel_symm α θ φ v
  rw [hfun]
  exact iteratedDeriv_two_polarKernel_phi_eq α θ ψ φ
    (by rwa [← polarChordSq_symm θ φ ψ])

private lemma iteratedDeriv_three_polarKernel_psi_eq (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    iteratedDeriv 3 (fun v => polarKernel α θ φ v) ψ =
      polarJet30 (α / 2) θ ψ φ := by
  have hfun : (fun v => polarKernel α θ φ v) =
      (fun v => polarKernel α θ v φ) := by
    funext v
    exact polarKernel_symm α θ φ v
  rw [hfun]
  exact iteratedDeriv_three_polarKernel_phi_eq α θ ψ φ
    (by rwa [← polarChordSq_symm θ φ ψ])

private noncomputable def polarJet21 (p θ φ ψ : ℝ) : ℝ :=
  p * (p - 1) * (p - 2) * polarChordSq θ φ ψ ^ (p - 3) *
      polarChordPhi θ φ ψ ^ 2 * polarChordPsi θ φ ψ +
    p * (p - 1) * polarChordSq θ φ ψ ^ (p - 2) *
      (2 * polarChordPhi θ φ ψ * polarChordCross θ φ ψ +
        polarChordPsi θ φ ψ * (2 - polarChordSq θ φ ψ)) -
    p * polarChordSq θ φ ψ ^ (p - 1) * polarChordPsi θ φ ψ

private lemma hasDerivAt_polarJet11_phi (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt (fun u => polarJet11 p θ u ψ) (polarJet21 p θ φ ψ) φ := by
  have hp2 := hasDerivAt_polarChordSq_rpow_phi (p - 2) θ φ ψ hA
  have hp1 := hasDerivAt_polarChordSq_rpow_phi (p - 1) θ φ ψ hA
  have hx := hasDerivAt_polarChordPhi_phi θ φ ψ
  have hy := hasDerivAt_polarChordPsi_phi θ φ ψ
  have hz := hasDerivAt_polarChordCross_phi θ φ ψ
  have hterm1 := (((hp2.mul hx).mul hy).const_mul (p * (p - 1)))
  have hterm2 := ((hp1.mul hz).const_mul p)
  have hsum := hterm1.add hterm2
  convert hsum using 1
  · ext u
    simp only [polarJet11]
    ring
  · unfold polarJet21
    ring

private lemma iteratedDeriv_two_one_polarKernel_eq (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    iteratedDeriv 2
      (fun u => iteratedDeriv 1 (fun v => polarKernel α θ u v) ψ) φ =
      polarJet21 (α / 2) θ φ ψ := by
  have hpos : ∀ᶠ u in nhds φ, 0 < polarChordSq θ u ψ :=
    (hasDerivAt_polarChordSq_phi θ φ ψ).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hA)
  have heq : (fun u => iteratedDeriv 1
      (fun w => iteratedDeriv 1 (fun v => polarKernel α θ w v) ψ) u) =ᶠ[nhds φ]
      fun u => polarJet11 (α / 2) θ u ψ := by
    filter_upwards [hpos] with u hu
    exact iteratedDeriv_one_one_polarKernel_eq α θ u ψ hu
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, heq.deriv_eq]
  exact (hasDerivAt_polarJet11_phi (α / 2) θ φ ψ hA).deriv

private noncomputable def polarJet40 (p θ φ ψ : ℝ) : ℝ :=
  p * (p - 1) * (p - 2) * (p - 3) *
      polarChordSq θ φ ψ ^ (p - 4) * polarChordPhi θ φ ψ ^ 4 +
    6 * p * (p - 1) * (p - 2) *
      polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 2 *
        (2 - polarChordSq θ φ ψ) +
    3 * p * (p - 1) * polarChordSq θ φ ψ ^ (p - 2) *
      (2 - polarChordSq θ φ ψ) ^ 2 -
    4 * p * (p - 1) * polarChordSq θ φ ψ ^ (p - 2) *
      polarChordPhi θ φ ψ ^ 2 -
    p * polarChordSq θ φ ψ ^ (p - 1) * (2 - polarChordSq θ φ ψ)

private lemma hasDerivAt_polarJet30_phi (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt (fun u => polarJet30 p θ u ψ) (polarJet40 p θ φ ψ) φ := by
  have ha : HasDerivAt (fun u => polarChordSq θ u ψ) (polarChordPhi θ φ ψ) φ := by
    simpa [polarChordPhi] using hasDerivAt_polarChordSq_phi θ φ ψ
  have hx := hasDerivAt_polarChordPhi_phi θ φ ψ
  have hp3 := hasDerivAt_polarChordSq_rpow_phi (p - 3) θ φ ψ hA
  have hp2 := hasDerivAt_polarChordSq_rpow_phi (p - 2) θ φ ψ hA
  have hp1 := hasDerivAt_polarChordSq_rpow_phi (p - 1) θ φ ψ hA
  have ht1 := ((hp3.mul (hx.pow 3)).const_mul (p * (p - 1) * (p - 2)))
  have ht2 := (((hp2.mul hx).mul (ha.const_sub 2)).const_mul (3 * p * (p - 1)))
  have ht3 := ((hp1.mul hx).const_mul p)
  have hsum := (ht1.add ht2).sub ht3
  convert hsum using 1
  · ext u
    simp only [polarJet30]
    ring
  · unfold polarJet40
    ring

private lemma iteratedDeriv_four_polarKernel_phi_eq (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    iteratedDeriv 4 (fun u => polarKernel α θ u ψ) φ =
      polarJet40 (α / 2) θ φ ψ := by
  have hpos : ∀ᶠ u in nhds φ, 0 < polarChordSq θ u ψ :=
    (hasDerivAt_polarChordSq_phi θ φ ψ).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hA)
  have heq : (fun u => iteratedDeriv 3 (fun v => polarKernel α θ v ψ) u) =ᶠ[nhds φ]
      fun u => polarJet30 (α / 2) θ u ψ := by
    filter_upwards [hpos] with u hu
    exact iteratedDeriv_three_polarKernel_phi_eq α θ u ψ hu
  rw [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ, heq.deriv_eq]
  exact (hasDerivAt_polarJet30_phi (α / 2) θ φ ψ hA).deriv

private lemma iteratedDeriv_four_polarKernel_psi_eq (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    iteratedDeriv 4 (fun v => polarKernel α θ φ v) ψ =
      polarJet40 (α / 2) θ ψ φ := by
  have hfun : (fun v => polarKernel α θ φ v) =
      (fun v => polarKernel α θ v φ) := by
    funext v
    exact polarKernel_symm α θ φ v
  rw [hfun]
  exact iteratedDeriv_four_polarKernel_phi_eq α θ ψ φ
    (by rwa [← polarChordSq_symm θ φ ψ])

private lemma hasDerivAt_polarJet20_psi (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt (fun v => polarJet20 p θ φ v) (polarJet21 p θ φ ψ) ψ := by
  have ha : HasDerivAt (fun v => polarChordSq θ φ v) (polarChordPsi θ φ ψ) ψ := by
    simpa [polarChordPsi] using hasDerivAt_polarChordSq_psi θ φ ψ
  have hx := hasDerivAt_polarChordPhi_psi θ φ ψ
  have hp2 := hasDerivAt_polarChordSq_rpow_psi (p - 2) θ φ ψ hA
  have hp1 := hasDerivAt_polarChordSq_rpow_psi (p - 1) θ φ ψ hA
  have ht1 := ((hp2.mul (hx.pow 2)).const_mul (p * (p - 1)))
  have ht2 := ((hp1.const_mul p).mul (ha.const_sub 2))
  have hsum := ht1.add ht2
  convert hsum using 1
  · ext v
    simp only [polarJet20]
    ring
  · unfold polarJet21
    ring

private lemma iteratedDeriv_one_two_polarKernel_eq (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    iteratedDeriv 1
      (fun u => iteratedDeriv 2 (fun v => polarKernel α θ u v) ψ) φ =
      polarJet21 (α / 2) θ ψ φ := by
  have hpos : ∀ᶠ u in nhds φ, 0 < polarChordSq θ u ψ :=
    (hasDerivAt_polarChordSq_phi θ φ ψ).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hA)
  have heq : (fun u => iteratedDeriv 2 (fun v => polarKernel α θ u v) ψ) =ᶠ[nhds φ]
      fun u => polarJet20 (α / 2) θ ψ u := by
    filter_upwards [hpos] with u hu
    exact iteratedDeriv_two_polarKernel_psi_eq α θ u ψ hu
  rw [iteratedDeriv_one, heq.deriv_eq]
  exact (hasDerivAt_polarJet20_psi (α / 2) θ ψ φ
    (by rwa [← polarChordSq_symm θ φ ψ])).deriv

private noncomputable def polarJet31 (p θ φ ψ : ℝ) : ℝ :=
  p * (p - 1) * (p - 2) * (p - 3) * polarChordSq θ φ ψ ^ (p - 4) *
      polarChordPhi θ φ ψ ^ 3 * polarChordPsi θ φ ψ +
    3 * p * (p - 1) * (p - 2) * polarChordSq θ φ ψ ^ (p - 3) *
      (polarChordPhi θ φ ψ ^ 2 * polarChordCross θ φ ψ +
        polarChordPhi θ φ ψ * polarChordPsi θ φ ψ *
          (2 - polarChordSq θ φ ψ)) +
    p * (p - 1) * polarChordSq θ φ ψ ^ (p - 2) *
      (3 * polarChordCross θ φ ψ * (2 - polarChordSq θ φ ψ) -
        4 * polarChordPhi θ φ ψ * polarChordPsi θ φ ψ) -
    p * polarChordSq θ φ ψ ^ (p - 1) * polarChordCross θ φ ψ

private noncomputable def polarJet22 (p θ φ ψ : ℝ) : ℝ :=
  p * (p - 1) * (p - 2) * (p - 3) * polarChordSq θ φ ψ ^ (p - 4) *
      polarChordPhi θ φ ψ ^ 2 * polarChordPsi θ φ ψ ^ 2 +
    p * (p - 1) * (p - 2) * polarChordSq θ φ ψ ^ (p - 3) *
      ((2 - polarChordSq θ φ ψ) *
          (polarChordPhi θ φ ψ ^ 2 + polarChordPsi θ φ ψ ^ 2) +
        4 * polarChordPhi θ φ ψ * polarChordPsi θ φ ψ *
          polarChordCross θ φ ψ) +
    p * (p - 1) * polarChordSq θ φ ψ ^ (p - 2) *
      (2 * polarChordCross θ φ ψ ^ 2 +
        (2 - polarChordSq θ φ ψ) ^ 2 -
        2 * (polarChordPhi θ φ ψ ^ 2 + polarChordPsi θ φ ψ ^ 2)) -
    p * polarChordSq θ φ ψ ^ (p - 1) * (2 - polarChordSq θ φ ψ)

private lemma hasDerivAt_polarJet30_psi (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt (fun v => polarJet30 p θ φ v) (polarJet31 p θ φ ψ) ψ := by
  have ha : HasDerivAt (fun v => polarChordSq θ φ v) (polarChordPsi θ φ ψ) ψ := by
    simpa [polarChordPsi] using hasDerivAt_polarChordSq_psi θ φ ψ
  have hx := hasDerivAt_polarChordPhi_psi θ φ ψ
  have hp3 := hasDerivAt_polarChordSq_rpow_psi (p - 3) θ φ ψ hA
  have hp2 := hasDerivAt_polarChordSq_rpow_psi (p - 2) θ φ ψ hA
  have hp1 := hasDerivAt_polarChordSq_rpow_psi (p - 1) θ φ ψ hA
  have ht1 := ((hp3.mul (hx.pow 3)).const_mul (p * (p - 1) * (p - 2)))
  have ht2 := (((hp2.mul hx).mul (ha.const_sub 2)).const_mul (3 * p * (p - 1)))
  have ht3 := ((hp1.mul hx).const_mul p)
  have hsum := (ht1.add ht2).sub ht3
  convert hsum using 1
  · ext v
    simp only [polarJet30]
    ring
  · unfold polarJet31
    ring

private lemma hasDerivAt_polarJet21_phi (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt (fun u => polarJet21 p θ u ψ) (polarJet31 p θ φ ψ) φ := by
  have ha : HasDerivAt (fun u => polarChordSq θ u ψ) (polarChordPhi θ φ ψ) φ := by
    simpa [polarChordPhi] using hasDerivAt_polarChordSq_phi θ φ ψ
  have hx := hasDerivAt_polarChordPhi_phi θ φ ψ
  have hy := hasDerivAt_polarChordPsi_phi θ φ ψ
  have hz := hasDerivAt_polarChordCross_phi θ φ ψ
  have hp3 := hasDerivAt_polarChordSq_rpow_phi (p - 3) θ φ ψ hA
  have hp2 := hasDerivAt_polarChordSq_rpow_phi (p - 2) θ φ ψ hA
  have hp1 := hasDerivAt_polarChordSq_rpow_phi (p - 1) θ φ ψ hA
  have ht1 := (((hp3.mul (hx.pow 2)).mul hy).const_mul (p * (p - 1) * (p - 2)))
  have ht2 := ((hp2.mul (((hx.mul hz).const_mul 2).add
    (hy.mul (ha.const_sub 2)))).const_mul (p * (p - 1)))
  have ht3 := ((hp1.mul hy).const_mul p)
  have hsum := (ht1.add ht2).sub ht3
  convert hsum using 1
  · ext u
    simp only [polarJet21]
    ring
  · unfold polarJet31
    ring

private lemma hasDerivAt_polarJet21_psi (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    HasDerivAt (fun v => polarJet21 p θ φ v) (polarJet22 p θ φ ψ) ψ := by
  have ha : HasDerivAt (fun v => polarChordSq θ φ v) (polarChordPsi θ φ ψ) ψ := by
    simpa [polarChordPsi] using hasDerivAt_polarChordSq_psi θ φ ψ
  have hx := hasDerivAt_polarChordPhi_psi θ φ ψ
  have hy := hasDerivAt_polarChordPsi_psi θ φ ψ
  have hz := hasDerivAt_polarChordCross_psi θ φ ψ
  have hp3 := hasDerivAt_polarChordSq_rpow_psi (p - 3) θ φ ψ hA
  have hp2 := hasDerivAt_polarChordSq_rpow_psi (p - 2) θ φ ψ hA
  have hp1 := hasDerivAt_polarChordSq_rpow_psi (p - 1) θ φ ψ hA
  have ht1 := (((hp3.mul (hx.pow 2)).mul hy).const_mul (p * (p - 1) * (p - 2)))
  have ht2 := ((hp2.mul (((hx.mul hz).const_mul 2).add
    (hy.mul (ha.const_sub 2)))).const_mul (p * (p - 1)))
  have ht3 := ((hp1.mul hy).const_mul p)
  have hsum := (ht1.add ht2).sub ht3
  convert hsum using 1
  · ext v
    simp only [polarJet21]
    ring
  · unfold polarJet22
    ring

private lemma iteratedDeriv_three_one_polarKernel_eq (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    iteratedDeriv 3
      (fun u => iteratedDeriv 1 (fun v => polarKernel α θ u v) ψ) φ =
      polarJet31 (α / 2) θ φ ψ := by
  have hpos : ∀ᶠ u in nhds φ, 0 < polarChordSq θ u ψ :=
    (hasDerivAt_polarChordSq_phi θ φ ψ).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hA)
  have heq : (fun u => iteratedDeriv 2
      (fun w => iteratedDeriv 1 (fun v => polarKernel α θ w v) ψ) u) =ᶠ[nhds φ]
      fun u => polarJet21 (α / 2) θ u ψ := by
    filter_upwards [hpos] with u hu
    exact iteratedDeriv_two_one_polarKernel_eq α θ u ψ hu
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ, heq.deriv_eq]
  exact (hasDerivAt_polarJet21_phi (α / 2) θ φ ψ hA).deriv

private lemma iteratedDeriv_one_three_polarKernel_eq (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    iteratedDeriv 1
      (fun u => iteratedDeriv 3 (fun v => polarKernel α θ u v) ψ) φ =
      polarJet31 (α / 2) θ ψ φ := by
  have hpos : ∀ᶠ u in nhds φ, 0 < polarChordSq θ u ψ :=
    (hasDerivAt_polarChordSq_phi θ φ ψ).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hA)
  have heq : (fun u => iteratedDeriv 3 (fun v => polarKernel α θ u v) ψ) =ᶠ[nhds φ]
      fun u => polarJet30 (α / 2) θ ψ u := by
    filter_upwards [hpos] with u hu
    exact iteratedDeriv_three_polarKernel_psi_eq α θ u ψ hu
  rw [iteratedDeriv_one, heq.deriv_eq]
  exact (hasDerivAt_polarJet30_psi (α / 2) θ ψ φ
    (by rwa [← polarChordSq_symm θ φ ψ])).deriv

private lemma iteratedDeriv_two_two_polarKernel_eq (α θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    iteratedDeriv 2
      (fun u => iteratedDeriv 2 (fun v => polarKernel α θ u v) ψ) φ =
      polarJet22 (α / 2) θ ψ φ := by
  have hpos : ∀ᶠ u in nhds φ, 0 < polarChordSq θ u ψ :=
    (hasDerivAt_polarChordSq_phi θ φ ψ).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hA)
  have heq : (fun u => iteratedDeriv 1
      (fun w => iteratedDeriv 2 (fun v => polarKernel α θ w v) ψ) u) =ᶠ[nhds φ]
      fun u => polarJet21 (α / 2) θ ψ u := by
    filter_upwards [hpos] with u hu
    exact iteratedDeriv_one_two_polarKernel_eq α θ u ψ hu
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, heq.deriv_eq]
  exact (hasDerivAt_polarJet21_psi (α / 2) θ ψ φ
    (by rwa [← polarChordSq_symm θ φ ψ])).deriv

private lemma abs_pow_le_chord_rpow {a x : ℝ} (ha : 0 < a)
    (hx : |x| ≤ 2 * Real.sqrt a) (i : ℕ) :
    |x| ^ i ≤ 2 ^ i * a ^ ((i : ℝ) / 2) := by
  have h := pow_le_pow_left₀ (abs_nonneg x) hx i
  convert h using 1
  rw [mul_pow, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast (a ^ (1 / 2 : ℝ)) i,
    ← Real.rpow_mul ha.le]
  congr 1
  push_cast
  ring

private lemma abs_chord_monomial_le {a x y : ℝ} (ha : 0 < a) (ha4 : a ≤ 4)
    (hx : |x| ≤ 2 * Real.sqrt a) (hy : |y| ≤ 2 * Real.sqrt a)
    (p d : ℝ) (k r i j : ℕ) (hd0 : 0 ≤ d)
    (hbalance : p - (k : ℝ) + (i : ℝ) / 2 + (j : ℝ) / 2 =
      p - (r : ℝ) / 2 + d) :
    |a ^ (p - k) * x ^ i * y ^ j| ≤
      2 ^ (i + j) * 4 ^ d * a ^ (p - (r : ℝ) / 2) := by
  have hx' := abs_pow_le_chord_rpow ha hx i
  have hy' := abs_pow_le_chord_rpow ha hy j
  have hpow : 0 ≤ a ^ (p - k) := (Real.rpow_pos_of_pos ha _).le
  have had : a ^ d ≤ (4 : ℝ) ^ d :=
    Real.rpow_le_rpow ha.le ha4 hd0
  have hpower : a ^ (p - k) * a ^ ((i : ℝ) / 2) * a ^ ((j : ℝ) / 2) =
      a ^ (p - (r : ℝ) / 2) * a ^ d := by
    rw [← Real.rpow_add ha (p - k) ((i : ℝ) / 2),
      ← Real.rpow_add ha (p - k + (i : ℝ) / 2) ((j : ℝ) / 2),
      ← Real.rpow_add ha (p - (r : ℝ) / 2) d]
    rw [hbalance]
  rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha _), abs_pow, abs_pow]
  calc
    a ^ (p - k) * |x| ^ i * |y| ^ j ≤
        a ^ (p - k) * (2 ^ i * a ^ ((i : ℝ) / 2)) *
          (2 ^ j * a ^ ((j : ℝ) / 2)) := by gcongr
    _ = 2 ^ (i + j) * a ^ (p - (r : ℝ) / 2) * a ^ d := by
      rw [pow_add]
      calc
        a ^ (p - k) * (2 ^ i * a ^ ((i : ℝ) / 2)) *
            (2 ^ j * a ^ ((j : ℝ) / 2)) =
            (2 ^ i * 2 ^ j) *
              (a ^ (p - k) * a ^ ((i : ℝ) / 2) * a ^ ((j : ℝ) / 2)) := by ring
        _ = _ := by rw [hpower]; ring
    _ ≤ 2 ^ (i + j) * 4 ^ d * a ^ (p - (r : ℝ) / 2) := by
      have hmult : 0 ≤ 2 ^ (i + j) * a ^ (p - (r : ℝ) / 2) := by positivity
      have h := mul_le_mul_of_nonneg_left had hmult
      nlinarith

private lemma abs_chord_monomial_full_le {a x y z b : ℝ}
    (ha : 0 < a) (ha4 : a ≤ 4)
    (hx : |x| ≤ 2 * Real.sqrt a) (hy : |y| ≤ 2 * Real.sqrt a)
    (hz : |z| ≤ 2) (hb : |b| ≤ 2)
    (p d : ℝ) (k r i j l t : ℕ) (hd0 : 0 ≤ d)
    (hbalance : p - (k : ℝ) + (i : ℝ) / 2 + (j : ℝ) / 2 =
      p - (r : ℝ) / 2 + d) :
    |a ^ (p - k) * x ^ i * y ^ j * z ^ l * b ^ t| ≤
      2 ^ (i + j + l + t) * 4 ^ d * a ^ (p - (r : ℝ) / 2) := by
  have hbase := abs_chord_monomial_le ha ha4 hx hy p d k r i j hd0 hbalance
  have hz' : |z| ^ l ≤ (2 : ℝ) ^ l :=
    pow_le_pow_left₀ (abs_nonneg z) hz l
  have hb' : |b| ^ t ≤ (2 : ℝ) ^ t :=
    pow_le_pow_left₀ (abs_nonneg b) hb t
  rw [abs_mul, abs_mul, abs_pow, abs_pow]
  calc
    |a ^ (p - k) * x ^ i * y ^ j| * |z| ^ l * |b| ^ t ≤
        (2 ^ (i + j) * 4 ^ d * a ^ (p - (r : ℝ) / 2)) * 2 ^ l * 2 ^ t := by
      gcongr
    _ = _ := by rw [pow_add, pow_add]; ring

private lemma abs_chord_monomial_le_64 {a x y z b : ℝ}
    (ha : 0 < a) (ha4 : a ≤ 4)
    (hx : |x| ≤ 2 * Real.sqrt a) (hy : |y| ≤ 2 * Real.sqrt a)
    (hz : |z| ≤ 2) (hb : |b| ≤ 2)
    (p d : ℝ) (k r i j l t : ℕ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hdeg : i + j + l + t ≤ 4)
    (hbalance : p - (k : ℝ) + (i : ℝ) / 2 + (j : ℝ) / 2 =
      p - (r : ℝ) / 2 + d) :
    |a ^ (p - k) * x ^ i * y ^ j * z ^ l * b ^ t| ≤
      64 * a ^ (p - (r : ℝ) / 2) := by
  have h := abs_chord_monomial_full_le ha ha4 hx hy hz hb p d k r i j l t
    hd0 hbalance
  have h2 : (2 : ℝ) ^ (i + j + l + t) ≤ 16 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdeg
    norm_num at h
    exact h
  have h4 : (4 : ℝ) ^ d ≤ 4 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hd1
  have hc : (2 : ℝ) ^ (i + j + l + t) * 4 ^ d ≤ 64 := by
    have hmul : (2 : ℝ) ^ (i + j + l + t) * 4 ^ d ≤ 16 * 4 :=
      mul_le_mul h2 h4 (by positivity) (by positivity)
    nlinarith
  have hR : 0 ≤ a ^ (p - (r : ℝ) / 2) := (Real.rpow_pos_of_pos ha _).le
  exact h.trans (by
    have h' := mul_le_mul_of_nonneg_right hc hR
    nlinarith)

private noncomputable def polarCoeffBudget (p : ℝ) : ℝ :=
  1 + |p| + |p * (p - 1)| + |p * (p - 1) * (p - 2)| +
    |p * (p - 1) * (p - 2) * (p - 3)|

private lemma polarCoeffBudget_pos (p : ℝ) : 0 < polarCoeffBudget p := by
  unfold polarCoeffBudget
  positivity

private lemma polarCoeffBudget_bounds (p : ℝ) :
    |p| ≤ polarCoeffBudget p ∧
    |p * (p - 1)| ≤ polarCoeffBudget p ∧
    |p * (p - 1) * (p - 2)| ≤ polarCoeffBudget p ∧
    |p * (p - 1) * (p - 2) * (p - 3)| ≤ polarCoeffBudget p := by
  unfold polarCoeffBudget
  constructor
  · nlinarith [abs_nonneg (p * (p - 1)),
      abs_nonneg (p * (p - 1) * (p - 2)),
      abs_nonneg (p * (p - 1) * (p - 2) * (p - 3))]
  constructor
  · nlinarith [abs_nonneg p,
      abs_nonneg (p * (p - 1) * (p - 2)),
      abs_nonneg (p * (p - 1) * (p - 2) * (p - 3))]
  constructor
  · nlinarith [abs_nonneg p, abs_nonneg (p * (p - 1)),
      abs_nonneg (p * (p - 1) * (p - 2) * (p - 3))]
  · nlinarith [abs_nonneg p, abs_nonneg (p * (p - 1)),
      abs_nonneg (p * (p - 1) * (p - 2))]

private lemma abs_polar_monomial_le_64 (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ)
    (d : ℝ) (k r i j l t : ℕ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hdeg : i + j + l + t ≤ 4)
    (hbalance : p - (k : ℝ) + (i : ℝ) / 2 + (j : ℝ) / 2 =
      p - (r : ℝ) / 2 + d) :
    |polarChordSq θ φ ψ ^ (p - k) * polarChordPhi θ φ ψ ^ i *
      polarChordPsi θ φ ψ ^ j * polarChordCross θ φ ψ ^ l *
      (2 - polarChordSq θ φ ψ) ^ t| ≤
      64 * polarChordSq θ φ ψ ^ (p - (r : ℝ) / 2) :=
  abs_chord_monomial_le_64 hA (polarChordSq_le_four θ φ ψ)
    (abs_polarChordPhi_le θ φ ψ) (abs_polarChordPsi_le θ φ ψ)
    (abs_polarChordCross_le_two θ φ ψ) (abs_two_sub_polarChordSq_le θ φ ψ)
    p d k r i j l t hd0 hd1 hdeg hbalance

private lemma abs_coeff_mul_le {c t M K R : ℝ}
    (hc : |c| ≤ M) (ht : |t| ≤ K * R)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R) :
    |c * t| ≤ M * K * R := by
  rw [abs_mul]
  calc
    |c| * |t| ≤ M * (K * R) := by gcongr
    _ = M * K * R := by ring

private lemma abs_scaled_coeff_mul_le {c t M R : ℝ} (n : ℕ)
    (hc : |c| ≤ M) (ht : |t| ≤ 64 * R)
    (hM : 0 ≤ M) (hR : 0 ≤ R) :
    |((n : ℝ) * c) * t| ≤ (n : ℝ) * 64 * M * R := by
  have hcoeff : |(n : ℝ) * c| ≤ (n : ℝ) * M := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    exact mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
  have h := abs_coeff_mul_le hcoeff ht
    (mul_nonneg (Nat.cast_nonneg n) hM) (by norm_num : (0 : ℝ) ≤ 64) hR
  nlinarith

private lemma abs_sum_five_le (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le (a + b + c + d) e
  have h2 := abs_add_le (a + b + c) d
  have h3 := abs_add_le (a + b) c
  have h4 := abs_add_le a b
  linarith

private lemma abs_sum_six_le (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤
      |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 := abs_add_le (a + b + c + d + e) f
  have h2 := abs_sum_five_le a b c d e
  linarith

private lemma abs_sum_nine_le (a b c d e f g h i : ℝ) :
    |a + b + c + d + e + f + g + h + i| ≤
      |a| + |b| + |c| + |d| + |e| + |f| + |g| + |h| + |i| := by
  have h1 := abs_add_le (a + b + c + d + e + f + g + h) i
  have h2 := abs_add_le (a + b + c + d + e + f + g) h
  have h3 := abs_add_le (a + b + c + d + e + f) g
  have h4 := abs_sum_six_le a b c d e f
  linarith

private lemma abs_add_sub_le (a b c : ℝ) :
    |a + b - c| ≤ |a| + |b| + |c| := by
  have h1 : |a + b - c| ≤ |a + b| + |c| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (a + b) (-c)
  have h2 := abs_add_le a b
  linarith

private lemma abs_add_add_sub_le (a b c d : ℝ) :
    |a + b + c - d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_sub_le (a + b) c d
  have h2 := abs_add_le a b
  linarith

private lemma abs_polarJet20_le (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    |polarJet20 p θ φ ψ| ≤
      8 * polarCoeffBudget p * polarChordSq θ φ ψ ^ (p - 1) := by
  let a := polarChordSq θ φ ψ
  let x := polarChordPhi θ φ ψ
  let y := polarChordPsi θ φ ψ
  let z := polarChordCross θ φ ψ
  let b := 2 - a
  let M := polarCoeffBudget p
  let R := a ^ (p - 1)
  have ha4 : a ≤ 4 := polarChordSq_le_four θ φ ψ
  have hx : |x| ≤ 2 * Real.sqrt a := abs_polarChordPhi_le θ φ ψ
  have hy : |y| ≤ 2 * Real.sqrt a := abs_polarChordPsi_le θ φ ψ
  have hz : |z| ≤ 2 := abs_polarChordCross_le_two θ φ ψ
  have hb : |b| ≤ 2 := abs_two_sub_polarChordSq_le θ φ ψ
  have hM : 0 ≤ M := (polarCoeffBudget_pos p).le
  have hR : 0 ≤ R := (Real.rpow_pos_of_pos hA _).le
  have hc1 : |p * (p - 1)| ≤ M := by
    dsimp [M, polarCoeffBudget]
    nlinarith [abs_nonneg p, abs_nonneg (p * (p - 1) * (p - 2)),
      abs_nonneg (p * (p - 1) * (p - 2) * (p - 3))]
  have hc2 : |p| ≤ M := by
    dsimp [M, polarCoeffBudget]
    nlinarith [abs_nonneg (p * (p - 1)),
      abs_nonneg (p * (p - 1) * (p - 2)),
      abs_nonneg (p * (p - 1) * (p - 2) * (p - 3))]
  have ht1 : |a ^ (p - 2) * x ^ 2| ≤ 4 * R := by
    have h := abs_chord_monomial_full_le hA ha4 hx hy hz hb p 0 2 2 2 0 0 0
      (by norm_num) (by ring)
    norm_num at h
    simpa [R, a] using h
  have ht2 : |a ^ (p - 1) * b| ≤ 2 * R := by
    have h := abs_chord_monomial_full_le hA ha4 hx hy hz hb p 0 1 2 0 0 0 1
      (by norm_num) (by ring)
    norm_num at h
    simpa [R, a] using h
  have h1 := abs_coeff_mul_le hc1 ht1 hM (by norm_num : (0 : ℝ) ≤ 4) hR
  have h2 := abs_coeff_mul_le hc2 ht2 hM (by norm_num : (0 : ℝ) ≤ 2) hR
  have hform : polarJet20 p θ φ ψ =
      (p * (p - 1)) * (a ^ (p - 2) * x ^ 2) + p * (a ^ (p - 1) * b) := by
    unfold polarJet20
    ring
  rw [hform]
  exact (abs_add_le _ _).trans (by dsimp [M, R, a] at *; nlinarith [h1, h2])

private lemma abs_polarJet11_le (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    |polarJet11 p θ φ ψ| ≤
      128 * polarCoeffBudget p * polarChordSq θ φ ψ ^ (p - 1) := by
  let M := polarCoeffBudget p
  let R := polarChordSq θ φ ψ ^ (p - 1)
  obtain ⟨hc1, hc2, _, _⟩ := polarCoeffBudget_bounds p
  have hM : 0 ≤ M := (polarCoeffBudget_pos p).le
  have hR : 0 ≤ R := (Real.rpow_pos_of_pos hA _).le
  have ht1 : |polarChordSq θ φ ψ ^ (p - 2) *
      polarChordPhi θ φ ψ * polarChordPsi θ φ ψ| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 2 2 1 1 0 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht2 : |polarChordSq θ φ ψ ^ (p - 1) * polarChordCross θ φ ψ| ≤
      64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 1 2 0 0 1 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R] using h
  have h1 := abs_coeff_mul_le hc2 ht1 hM (by norm_num : (0 : ℝ) ≤ 64) hR
  have h2 := abs_coeff_mul_le hc1 ht2 hM (by norm_num : (0 : ℝ) ≤ 64) hR
  have hform : polarJet11 p θ φ ψ =
      (p * (p - 1)) * (polarChordSq θ φ ψ ^ (p - 2) *
        polarChordPhi θ φ ψ * polarChordPsi θ φ ψ) +
      p * (polarChordSq θ φ ψ ^ (p - 1) * polarChordCross θ φ ψ) := by
    unfold polarJet11
    ring
  rw [hform]
  exact (abs_add_le _ _).trans (by dsimp [M, R] at *; nlinarith [h1, h2])

private lemma abs_polarJet30_le (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    |polarJet30 p θ φ ψ| ≤
      512 * polarCoeffBudget p * polarChordSq θ φ ψ ^ (p - 3 / 2) := by
  let M := polarCoeffBudget p
  let R := polarChordSq θ φ ψ ^ (p - 3 / 2)
  obtain ⟨hc1, hc2, hc3, _⟩ := polarCoeffBudget_bounds p
  have hM : 0 ≤ M := (polarCoeffBudget_pos p).le
  have hR : 0 ≤ R := (Real.rpow_pos_of_pos hA _).le
  have ht1 : |polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 3| ≤
      64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 3 3 3 0 0 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R] using h
  have ht2 : |polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ *
      (2 - polarChordSq θ φ ψ)| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 2 3 1 0 0 1
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht3 : |polarChordSq θ φ ψ ^ (p - 1) * polarChordPhi θ φ ψ| ≤
      64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 1 1 3 1 0 0 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R] using h
  have h1 := abs_coeff_mul_le hc3 ht1 hM (by norm_num : (0 : ℝ) ≤ 64) hR
  have hc2' : |3 * (p * (p - 1))| ≤ 3 * M := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    gcongr
  have h2 := abs_coeff_mul_le hc2' ht2
    (by positivity : 0 ≤ 3 * M) (by norm_num : (0 : ℝ) ≤ 64) hR
  have h3 := abs_coeff_mul_le hc1 ht3 hM (by norm_num : (0 : ℝ) ≤ 64) hR
  have hform : polarJet30 p θ φ ψ =
      (p * (p - 1) * (p - 2)) *
        (polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 3) +
      (3 * (p * (p - 1))) *
        (polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ *
          (2 - polarChordSq θ φ ψ)) -
      p * (polarChordSq θ φ ψ ^ (p - 1) * polarChordPhi θ φ ψ) := by
    unfold polarJet30
    ring
  rw [hform]
  exact (abs_add_sub_le _ _ _).trans (by dsimp [M, R] at *; nlinarith [h1, h2, h3])

private lemma abs_polarJet21_le (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    |polarJet21 p θ φ ψ| ≤
      512 * polarCoeffBudget p * polarChordSq θ φ ψ ^ (p - 3 / 2) := by
  let M := polarCoeffBudget p
  let R := polarChordSq θ φ ψ ^ (p - 3 / 2)
  obtain ⟨hc1, hc2, hc3, _⟩ := polarCoeffBudget_bounds p
  have hM : 0 ≤ M := (polarCoeffBudget_pos p).le
  have hR : 0 ≤ R := (Real.rpow_pos_of_pos hA _).le
  have ht1 : |polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 2 *
      polarChordPsi θ φ ψ| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 3 3 2 1 0 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R] using h
  have ht2 : |polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ *
      polarChordCross θ φ ψ| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 2 3 1 0 1 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht3 : |polarChordSq θ φ ψ ^ (p - 2) * polarChordPsi θ φ ψ *
      (2 - polarChordSq θ φ ψ)| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 2 3 0 1 0 1
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht4 : |polarChordSq θ φ ψ ^ (p - 1) * polarChordPsi θ φ ψ| ≤
      64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 1 1 3 0 1 0 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R] using h
  have hc2' : |2 * (p * (p - 1))| ≤ 2 * M := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
  have h1 := abs_coeff_mul_le hc3 ht1 hM (by norm_num : (0 : ℝ) ≤ 64) hR
  have h2 := abs_coeff_mul_le hc2' ht2
    (by positivity : 0 ≤ 2 * M) (by norm_num : (0 : ℝ) ≤ 64) hR
  have h3 := abs_coeff_mul_le hc2 ht3 hM (by norm_num : (0 : ℝ) ≤ 64) hR
  have h4 := abs_coeff_mul_le hc1 ht4 hM (by norm_num : (0 : ℝ) ≤ 64) hR
  have hform : polarJet21 p θ φ ψ =
      (p * (p - 1) * (p - 2)) *
        (polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 2 *
          polarChordPsi θ φ ψ) +
      (2 * (p * (p - 1))) *
        (polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ *
          polarChordCross θ φ ψ) +
      (p * (p - 1)) *
        (polarChordSq θ φ ψ ^ (p - 2) * polarChordPsi θ φ ψ *
          (2 - polarChordSq θ φ ψ)) -
      p * (polarChordSq θ φ ψ ^ (p - 1) * polarChordPsi θ φ ψ) := by
    unfold polarJet21
    ring
  rw [hform]
  exact (abs_add_add_sub_le _ _ _ _).trans
    (by dsimp [M, R] at *; nlinarith [h1, h2, h3, h4])

private lemma abs_polarJet40_le (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    |polarJet40 p θ φ ψ| ≤
      2048 * polarCoeffBudget p * polarChordSq θ φ ψ ^ (p - 2) := by
  let M := polarCoeffBudget p
  let R := polarChordSq θ φ ψ ^ (p - 2)
  obtain ⟨hc1, hc2, hc3, hc4⟩ := polarCoeffBudget_bounds p
  have hM : 0 ≤ M := (polarCoeffBudget_pos p).le
  have hR : 0 ≤ R := (Real.rpow_pos_of_pos hA _).le
  have hMR : 0 ≤ M * R := mul_nonneg hM hR
  have ht1 : |polarChordSq θ φ ψ ^ (p - 4) * polarChordPhi θ φ ψ ^ 4| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 4 4 4 0 0 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R] using h
  have ht2 : |polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 2 *
      (2 - polarChordSq θ φ ψ)| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 3 4 2 0 0 1
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R] using h
  have ht3 : |polarChordSq θ φ ψ ^ (p - 2) *
      (2 - polarChordSq θ φ ψ) ^ 2| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 2 4 0 0 0 2
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R] using h
  have ht4 : |polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ ^ 2| ≤
      64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 1 2 4 2 0 0 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R] using h
  have ht5 : |polarChordSq θ φ ψ ^ (p - 1) *
      (2 - polarChordSq θ φ ψ)| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 1 1 4 0 0 0 1
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R] using h
  have h1 := abs_scaled_coeff_mul_le 1 hc4 ht1 hM hR
  have h2 := abs_scaled_coeff_mul_le 6 hc3 ht2 hM hR
  have h3 := abs_scaled_coeff_mul_le 3 hc2 ht3 hM hR
  have h4 := abs_scaled_coeff_mul_le 4 hc2 ht4 hM hR
  have h5 := abs_scaled_coeff_mul_le 1 hc1 ht5 hM hR
  have hform : polarJet40 p θ φ ψ =
      ((1 : ℝ) * (p * (p - 1) * (p - 2) * (p - 3))) *
        (polarChordSq θ φ ψ ^ (p - 4) * polarChordPhi θ φ ψ ^ 4) +
      (6 * (p * (p - 1) * (p - 2))) *
        (polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 2 *
          (2 - polarChordSq θ φ ψ)) +
      (3 * (p * (p - 1))) *
        (polarChordSq θ φ ψ ^ (p - 2) * (2 - polarChordSq θ φ ψ) ^ 2) +
      -(4 * (p * (p - 1)) *
        (polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ ^ 2)) +
      -((1 : ℝ) * p *
        (polarChordSq θ φ ψ ^ (p - 1) * (2 - polarChordSq θ φ ψ))) := by
    unfold polarJet40
    ring
  rw [hform]
  have htri := abs_sum_five_le
    ((1 : ℝ) * (p * (p - 1) * (p - 2) * (p - 3)) *
      (polarChordSq θ φ ψ ^ (p - 4) * polarChordPhi θ φ ψ ^ 4))
    (6 * (p * (p - 1) * (p - 2)) *
      (polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 2 *
        (2 - polarChordSq θ φ ψ)))
    (3 * (p * (p - 1)) *
      (polarChordSq θ φ ψ ^ (p - 2) * (2 - polarChordSq θ φ ψ) ^ 2))
    (-(4 * (p * (p - 1)) *
      (polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ ^ 2)))
    (-((1 : ℝ) * p *
      (polarChordSq θ φ ψ ^ (p - 1) * (2 - polarChordSq θ φ ψ))))
  simp only [abs_neg] at htri
  refine htri.trans ?_
  calc
    _ ≤ 960 * M * R := by
      have hs := add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5
      norm_num only [Nat.cast_ofNat, one_mul] at hs
      convert hs using 1 <;> ring
    _ ≤ 2048 * polarCoeffBudget p * polarChordSq θ φ ψ ^ (p - 2) := by
      dsimp [M, R] at *
      nlinarith [hMR]


set_option maxHeartbeats 1000000 in
private lemma abs_polarJet31_le (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    |polarJet31 p θ φ ψ| ≤
      2048 * polarCoeffBudget p * polarChordSq θ φ ψ ^ (p - 2) := by
  let M := polarCoeffBudget p
  let R := polarChordSq θ φ ψ ^ (p - 2)
  obtain ⟨hc1, hc2, hc3, hc4⟩ := polarCoeffBudget_bounds p
  have hM : 0 ≤ M := (polarCoeffBudget_pos p).le
  have hR : 0 ≤ R := (Real.rpow_pos_of_pos hA _).le
  have hMR : 0 ≤ M * R := mul_nonneg hM hR
  have ht1 : |polarChordSq θ φ ψ ^ (p - 4) * polarChordPhi θ φ ψ ^ 3 * polarChordPsi θ φ ψ| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 4 4 3 1 0 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht2 : |polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 2 * polarChordCross θ φ ψ| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 3 4 2 0 1 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht3 : |polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ * polarChordPsi θ φ ψ * (2 - polarChordSq θ φ ψ)| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 3 4 1 1 0 1
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht4 : |polarChordSq θ φ ψ ^ (p - 2) * polarChordCross θ φ ψ * (2 - polarChordSq θ φ ψ)| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 2 4 0 0 1 1
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht5 : |polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ * polarChordPsi θ φ ψ| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 1 2 4 1 1 0 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht6 : |polarChordSq θ φ ψ ^ (p - 1) * polarChordCross θ φ ψ| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 1 1 4 0 0 1 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have h1 := abs_scaled_coeff_mul_le 1 hc4 ht1 hM hR
  have h2 := abs_scaled_coeff_mul_le 3 hc3 ht2 hM hR
  have h3 := abs_scaled_coeff_mul_le 3 hc3 ht3 hM hR
  have h4 := abs_scaled_coeff_mul_le 3 hc2 ht4 hM hR
  have h5 := abs_scaled_coeff_mul_le 4 hc2 ht5 hM hR
  have h6 := abs_scaled_coeff_mul_le 1 hc1 ht6 hM hR
  have hform : polarJet31 p θ φ ψ =
    (1 * (p * (p - 1) * (p - 2) * (p - 3))) * (polarChordSq θ φ ψ ^ (p - 4) * polarChordPhi θ φ ψ ^ 3 * polarChordPsi θ φ ψ) +
    (3 * (p * (p - 1) * (p - 2))) * (polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 2 * polarChordCross θ φ ψ) +
    (3 * (p * (p - 1) * (p - 2))) * (polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ * polarChordPsi θ φ ψ * (2 - polarChordSq θ φ ψ)) +
    (3 * (p * (p - 1))) * (polarChordSq θ φ ψ ^ (p - 2) * polarChordCross θ φ ψ * (2 - polarChordSq θ φ ψ)) +
    (-((4 * (p * (p - 1))) * (polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ * polarChordPsi θ φ ψ))) +
    (-((1 * p) * (polarChordSq θ φ ψ ^ (p - 1) * polarChordCross θ φ ψ))) := by
    unfold polarJet31
    ring
  rw [hform]
  have htri := abs_sum_six_le
    ((1 * (p * (p - 1) * (p - 2) * (p - 3))) * (polarChordSq θ φ ψ ^ (p - 4) * polarChordPhi θ φ ψ ^ 3 * polarChordPsi θ φ ψ))
    ((3 * (p * (p - 1) * (p - 2))) * (polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 2 * polarChordCross θ φ ψ))
    ((3 * (p * (p - 1) * (p - 2))) * (polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ * polarChordPsi θ φ ψ * (2 - polarChordSq θ φ ψ)))
    ((3 * (p * (p - 1))) * (polarChordSq θ φ ψ ^ (p - 2) * polarChordCross θ φ ψ * (2 - polarChordSq θ φ ψ)))
    ((-((4 * (p * (p - 1))) * (polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ * polarChordPsi θ φ ψ))))
    ((-((1 * p) * (polarChordSq θ φ ψ ^ (p - 1) * polarChordCross θ φ ψ))))
  simp only [abs_neg] at htri
  refine htri.trans ?_
  calc
    _ ≤ 960 * M * R := by
      have hs := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) h6)
      norm_num only [Nat.cast_ofNat, one_mul] at hs
      convert hs using 1 <;> ring
    _ ≤ 2048 * polarCoeffBudget p * polarChordSq θ φ ψ ^ (p - 2) := by
      dsimp [M, R] at *
      nlinarith [hMR]

set_option maxHeartbeats 1000000 in
private lemma abs_polarJet22_le (p θ φ ψ : ℝ)
    (hA : 0 < polarChordSq θ φ ψ) :
    |polarJet22 p θ φ ψ| ≤
      2048 * polarCoeffBudget p * polarChordSq θ φ ψ ^ (p - 2) := by
  let M := polarCoeffBudget p
  let R := polarChordSq θ φ ψ ^ (p - 2)
  obtain ⟨hc1, hc2, hc3, hc4⟩ := polarCoeffBudget_bounds p
  have hM : 0 ≤ M := (polarCoeffBudget_pos p).le
  have hR : 0 ≤ R := (Real.rpow_pos_of_pos hA _).le
  have hMR : 0 ≤ M * R := mul_nonneg hM hR
  have ht1 : |polarChordSq θ φ ψ ^ (p - 4) * polarChordPhi θ φ ψ ^ 2 * polarChordPsi θ φ ψ ^ 2| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 4 4 2 2 0 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht2 : |polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 2 * (2 - polarChordSq θ φ ψ)| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 3 4 2 0 0 1
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht3 : |polarChordSq θ φ ψ ^ (p - 3) * polarChordPsi θ φ ψ ^ 2 * (2 - polarChordSq θ φ ψ)| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 3 4 0 2 0 1
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht4 : |polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ * polarChordPsi θ φ ψ * polarChordCross θ φ ψ| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 3 4 1 1 1 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht5 : |polarChordSq θ φ ψ ^ (p - 2) * polarChordCross θ φ ψ ^ 2| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 2 4 0 0 2 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht6 : |polarChordSq θ φ ψ ^ (p - 2) * (2 - polarChordSq θ φ ψ) ^ 2| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 0 2 4 0 0 0 2
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht7 : |polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ ^ 2| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 1 2 4 2 0 0 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht8 : |polarChordSq θ φ ψ ^ (p - 2) * polarChordPsi θ φ ψ ^ 2| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 1 2 4 0 2 0 0
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have ht9 : |polarChordSq θ φ ψ ^ (p - 1) * (2 - polarChordSq θ φ ψ)| ≤ 64 * R := by
    have h := abs_polar_monomial_le_64 p θ φ ψ hA 1 1 4 0 0 0 1
      (by norm_num) (by norm_num) (by norm_num) (by ring)
    norm_num at h
    simpa [R, mul_assoc] using h
  have h1 := abs_scaled_coeff_mul_le 1 hc4 ht1 hM hR
  have h2 := abs_scaled_coeff_mul_le 1 hc3 ht2 hM hR
  have h3 := abs_scaled_coeff_mul_le 1 hc3 ht3 hM hR
  have h4 := abs_scaled_coeff_mul_le 4 hc3 ht4 hM hR
  have h5 := abs_scaled_coeff_mul_le 2 hc2 ht5 hM hR
  have h6 := abs_scaled_coeff_mul_le 1 hc2 ht6 hM hR
  have h7 := abs_scaled_coeff_mul_le 2 hc2 ht7 hM hR
  have h8 := abs_scaled_coeff_mul_le 2 hc2 ht8 hM hR
  have h9 := abs_scaled_coeff_mul_le 1 hc1 ht9 hM hR
  have hform : polarJet22 p θ φ ψ =
    (1 * (p * (p - 1) * (p - 2) * (p - 3))) * (polarChordSq θ φ ψ ^ (p - 4) * polarChordPhi θ φ ψ ^ 2 * polarChordPsi θ φ ψ ^ 2) +
    (1 * (p * (p - 1) * (p - 2))) * (polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 2 * (2 - polarChordSq θ φ ψ)) +
    (1 * (p * (p - 1) * (p - 2))) * (polarChordSq θ φ ψ ^ (p - 3) * polarChordPsi θ φ ψ ^ 2 * (2 - polarChordSq θ φ ψ)) +
    (4 * (p * (p - 1) * (p - 2))) * (polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ * polarChordPsi θ φ ψ * polarChordCross θ φ ψ) +
    (2 * (p * (p - 1))) * (polarChordSq θ φ ψ ^ (p - 2) * polarChordCross θ φ ψ ^ 2) +
    (1 * (p * (p - 1))) * (polarChordSq θ φ ψ ^ (p - 2) * (2 - polarChordSq θ φ ψ) ^ 2) +
    (-((2 * (p * (p - 1))) * (polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ ^ 2))) +
    (-((2 * (p * (p - 1))) * (polarChordSq θ φ ψ ^ (p - 2) * polarChordPsi θ φ ψ ^ 2))) +
    (-((1 * p) * (polarChordSq θ φ ψ ^ (p - 1) * (2 - polarChordSq θ φ ψ)))) := by
    unfold polarJet22
    ring
  rw [hform]
  have htri := abs_sum_nine_le
    ((1 * (p * (p - 1) * (p - 2) * (p - 3))) * (polarChordSq θ φ ψ ^ (p - 4) * polarChordPhi θ φ ψ ^ 2 * polarChordPsi θ φ ψ ^ 2))
    ((1 * (p * (p - 1) * (p - 2))) * (polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ ^ 2 * (2 - polarChordSq θ φ ψ)))
    ((1 * (p * (p - 1) * (p - 2))) * (polarChordSq θ φ ψ ^ (p - 3) * polarChordPsi θ φ ψ ^ 2 * (2 - polarChordSq θ φ ψ)))
    ((4 * (p * (p - 1) * (p - 2))) * (polarChordSq θ φ ψ ^ (p - 3) * polarChordPhi θ φ ψ * polarChordPsi θ φ ψ * polarChordCross θ φ ψ))
    ((2 * (p * (p - 1))) * (polarChordSq θ φ ψ ^ (p - 2) * polarChordCross θ φ ψ ^ 2))
    ((1 * (p * (p - 1))) * (polarChordSq θ φ ψ ^ (p - 2) * (2 - polarChordSq θ φ ψ) ^ 2))
    ((-((2 * (p * (p - 1))) * (polarChordSq θ φ ψ ^ (p - 2) * polarChordPhi θ φ ψ ^ 2))))
    ((-((2 * (p * (p - 1))) * (polarChordSq θ φ ψ ^ (p - 2) * polarChordPsi θ φ ψ ^ 2))))
    ((-((1 * p) * (polarChordSq θ φ ψ ^ (p - 1) * (2 - polarChordSq θ φ ψ)))))
  simp only [abs_neg] at htri
  refine htri.trans ?_
  calc
    _ ≤ 960 * M * R := by
      have hs := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) h6) h7) h8) h9)
      norm_num only [Nat.cast_ofNat, one_mul] at hs
      convert hs using 1 <;> ring
    _ ≤ 2048 * polarCoeffBudget p * polarChordSq θ φ ψ ^ (p - 2) := by
      dsimp [M, R] at *
      nlinarith [hMR]


set_option maxHeartbeats 2000000
set_option maxHeartbeats 2000000
/-- Uniform polar derivative estimates through total order four, away from coincident points. -/
theorem polar_derivative_bound {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    PolarDerivativeBound α := by
  let M := polarCoeffBudget (α / 2)
  let C := 4096 * M + α + 1
  have hM : 0 < M := polarCoeffBudget_pos _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m n hmn θ φ ψ hA
  let A := 2 - 2 * (Real.cos φ * Real.cos ψ +
    Real.sin φ * Real.sin ψ * Real.cos θ)
  have hA' : 0 < A := hA
  have hR : 0 < A ^ ((α - (m : ℝ) - (n : ℝ)) / 2) :=
    Real.rpow_pos_of_pos hA' _
  have hsmall : ∀ k l : ℕ, k + l ≤ 1 →
      |iteratedDeriv k
        (fun u => iteratedDeriv l (fun v => polarKernel α θ u v) ψ) φ| ≤
        C * A ^ ((α - k - l) / 2) := by
    intro k l hkl
    have h := polar_derivative_bound_one hα0.le k l hkl θ φ ψ hA
    calc
      _ ≤ (α + 1) * A ^ ((α - k - l) / 2) := h
      _ ≤ C * A ^ ((α - k - l) / 2) := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [C]; nlinarith [hM]
        · exact (Real.rpow_pos_of_pos hA' _).le
  have hCdom (K : ℝ) (hK : K ≤ 4096) : K * M ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) hM.le]
  have hm : m ≤ 4 := by omega
  have hn : n ≤ 4 := by omega
  interval_cases m <;> interval_cases n
  · exact hsmall 0 0 (by omega)
  · exact hsmall 0 1 (by omega)
  · have hpos : 0 < polarChordSq θ ψ φ := by
      rwa [← polarChordSq_symm θ φ ψ]
    have hj := abs_polarJet20_le (α / 2) θ ψ φ hpos
    have heq := iteratedDeriv_two_polarKernel_psi_eq α θ φ ψ hA
    have hcalc : |iteratedDeriv 0 (fun u => iteratedDeriv 2 (fun v => polarKernel α θ u v) ψ) φ| ≤ C * A ^ ((α - (0 : ℝ) - (2 : ℝ)) / 2) := by
      calc
        _ = |polarJet20 (α / 2) θ ψ φ| := by
          simpa only [iteratedDeriv_zero] using congrArg abs heq
        _ ≤ 8 * M * A ^ ((α - (0 : ℝ) - (2 : ℝ)) / 2) := by
          have hpow : polarChordSq θ ψ φ = A := by
            change polarChordSq θ ψ φ = polarChordSq θ φ ψ; exact polarChordSq_symm θ ψ φ
          have hexp : ((α - (0 : ℝ) - (2 : ℝ)) / 2) = α / 2 - 1 := by ring
          rw [hexp]
          simpa only [hpow, M] using hj
        _ ≤ C * A ^ ((α - (0 : ℝ) - (2 : ℝ)) / 2) := by
          exact mul_le_mul_of_nonneg_right (hCdom 8 (by norm_num))
            (Real.rpow_pos_of_pos hA' _).le
    convert hcalc using 1 <;> simp only [A, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · have hpos : 0 < polarChordSq θ ψ φ := by
      rwa [← polarChordSq_symm θ φ ψ]
    have hj := abs_polarJet30_le (α / 2) θ ψ φ hpos
    have heq := iteratedDeriv_three_polarKernel_psi_eq α θ φ ψ hA
    have hcalc : |iteratedDeriv 0 (fun u => iteratedDeriv 3 (fun v => polarKernel α θ u v) ψ) φ| ≤ C * A ^ ((α - (0 : ℝ) - (3 : ℝ)) / 2) := by
      calc
        _ = |polarJet30 (α / 2) θ ψ φ| := by
          simpa only [iteratedDeriv_zero] using congrArg abs heq
        _ ≤ 512 * M * A ^ ((α - (0 : ℝ) - (3 : ℝ)) / 2) := by
          have hpow : polarChordSq θ ψ φ = A := by
            change polarChordSq θ ψ φ = polarChordSq θ φ ψ; exact polarChordSq_symm θ ψ φ
          have hexp : ((α - (0 : ℝ) - (3 : ℝ)) / 2) = α / 2 - 3 / 2 := by ring
          rw [hexp]
          simpa only [hpow, M] using hj
        _ ≤ C * A ^ ((α - (0 : ℝ) - (3 : ℝ)) / 2) := by
          exact mul_le_mul_of_nonneg_right (hCdom 512 (by norm_num))
            (Real.rpow_pos_of_pos hA' _).le
    convert hcalc using 1 <;> simp only [A, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · have hpos : 0 < polarChordSq θ ψ φ := by
      rwa [← polarChordSq_symm θ φ ψ]
    have hj := abs_polarJet40_le (α / 2) θ ψ φ hpos
    have heq := iteratedDeriv_four_polarKernel_psi_eq α θ φ ψ hA
    have hcalc : |iteratedDeriv 0 (fun u => iteratedDeriv 4 (fun v => polarKernel α θ u v) ψ) φ| ≤ C * A ^ ((α - (0 : ℝ) - (4 : ℝ)) / 2) := by
      calc
        _ = |polarJet40 (α / 2) θ ψ φ| := by
          simpa only [iteratedDeriv_zero] using congrArg abs heq
        _ ≤ 2048 * M * A ^ ((α - (0 : ℝ) - (4 : ℝ)) / 2) := by
          have hpow : polarChordSq θ ψ φ = A := by
            change polarChordSq θ ψ φ = polarChordSq θ φ ψ; exact polarChordSq_symm θ ψ φ
          have hexp : ((α - (0 : ℝ) - (4 : ℝ)) / 2) = α / 2 - 2 := by ring
          rw [hexp]
          simpa only [hpow, M] using hj
        _ ≤ C * A ^ ((α - (0 : ℝ) - (4 : ℝ)) / 2) := by
          exact mul_le_mul_of_nonneg_right (hCdom 2048 (by norm_num))
            (Real.rpow_pos_of_pos hA' _).le
    convert hcalc using 1 <;> simp only [A, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · exact hsmall 1 0 (by omega)
  · have hpos : 0 < polarChordSq θ φ ψ := by
      exact hA
    have hj := abs_polarJet11_le (α / 2) θ φ ψ hpos
    have heq := iteratedDeriv_one_one_polarKernel_eq α θ φ ψ hA
    have hcalc : |iteratedDeriv 1 (fun u => iteratedDeriv 1 (fun v => polarKernel α θ u v) ψ) φ| ≤ C * A ^ ((α - (1 : ℝ) - (1 : ℝ)) / 2) := by
      calc
        _ = |polarJet11 (α / 2) θ φ ψ| := by
          exact congrArg abs heq
        _ ≤ 128 * M * A ^ ((α - (1 : ℝ) - (1 : ℝ)) / 2) := by
          have hpow : polarChordSq θ φ ψ = A := by
            rfl
          have hexp : ((α - (1 : ℝ) - (1 : ℝ)) / 2) = α / 2 - 1 := by ring
          rw [hexp]
          simpa only [hpow, M] using hj
        _ ≤ C * A ^ ((α - (1 : ℝ) - (1 : ℝ)) / 2) := by
          exact mul_le_mul_of_nonneg_right (hCdom 128 (by norm_num))
            (Real.rpow_pos_of_pos hA' _).le
    convert hcalc using 1 <;> simp only [A, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · have hpos : 0 < polarChordSq θ ψ φ := by
      rwa [← polarChordSq_symm θ φ ψ]
    have hj := abs_polarJet21_le (α / 2) θ ψ φ hpos
    have heq := iteratedDeriv_one_two_polarKernel_eq α θ φ ψ hA
    have hcalc : |iteratedDeriv 1 (fun u => iteratedDeriv 2 (fun v => polarKernel α θ u v) ψ) φ| ≤ C * A ^ ((α - (1 : ℝ) - (2 : ℝ)) / 2) := by
      calc
        _ = |polarJet21 (α / 2) θ ψ φ| := by
          exact congrArg abs heq
        _ ≤ 512 * M * A ^ ((α - (1 : ℝ) - (2 : ℝ)) / 2) := by
          have hpow : polarChordSq θ ψ φ = A := by
            change polarChordSq θ ψ φ = polarChordSq θ φ ψ; exact polarChordSq_symm θ ψ φ
          have hexp : ((α - (1 : ℝ) - (2 : ℝ)) / 2) = α / 2 - 3 / 2 := by ring
          rw [hexp]
          simpa only [hpow, M] using hj
        _ ≤ C * A ^ ((α - (1 : ℝ) - (2 : ℝ)) / 2) := by
          exact mul_le_mul_of_nonneg_right (hCdom 512 (by norm_num))
            (Real.rpow_pos_of_pos hA' _).le
    convert hcalc using 1 <;> simp only [A, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · have hpos : 0 < polarChordSq θ ψ φ := by
      rwa [← polarChordSq_symm θ φ ψ]
    have hj := abs_polarJet31_le (α / 2) θ ψ φ hpos
    have heq := iteratedDeriv_one_three_polarKernel_eq α θ φ ψ hA
    have hcalc : |iteratedDeriv 1 (fun u => iteratedDeriv 3 (fun v => polarKernel α θ u v) ψ) φ| ≤ C * A ^ ((α - (1 : ℝ) - (3 : ℝ)) / 2) := by
      calc
        _ = |polarJet31 (α / 2) θ ψ φ| := by
          exact congrArg abs heq
        _ ≤ 2048 * M * A ^ ((α - (1 : ℝ) - (3 : ℝ)) / 2) := by
          have hpow : polarChordSq θ ψ φ = A := by
            change polarChordSq θ ψ φ = polarChordSq θ φ ψ; exact polarChordSq_symm θ ψ φ
          have hexp : ((α - (1 : ℝ) - (3 : ℝ)) / 2) = α / 2 - 2 := by ring
          rw [hexp]
          simpa only [hpow, M] using hj
        _ ≤ C * A ^ ((α - (1 : ℝ) - (3 : ℝ)) / 2) := by
          exact mul_le_mul_of_nonneg_right (hCdom 2048 (by norm_num))
            (Real.rpow_pos_of_pos hA' _).le
    convert hcalc using 1 <;> simp only [A, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · omega
  · have hpos : 0 < polarChordSq θ φ ψ := by
      exact hA
    have hj := abs_polarJet20_le (α / 2) θ φ ψ hpos
    have heq := iteratedDeriv_two_polarKernel_phi_eq α θ φ ψ hA
    have hcalc : |iteratedDeriv 2 (fun u => iteratedDeriv 0 (fun v => polarKernel α θ u v) ψ) φ| ≤ C * A ^ ((α - (2 : ℝ) - (0 : ℝ)) / 2) := by
      calc
        _ = |polarJet20 (α / 2) θ φ ψ| := by
          simpa only [iteratedDeriv_zero] using congrArg abs heq
        _ ≤ 8 * M * A ^ ((α - (2 : ℝ) - (0 : ℝ)) / 2) := by
          have hpow : polarChordSq θ φ ψ = A := by
            rfl
          have hexp : ((α - (2 : ℝ) - (0 : ℝ)) / 2) = α / 2 - 1 := by ring
          rw [hexp]
          simpa only [hpow, M] using hj
        _ ≤ C * A ^ ((α - (2 : ℝ) - (0 : ℝ)) / 2) := by
          exact mul_le_mul_of_nonneg_right (hCdom 8 (by norm_num))
            (Real.rpow_pos_of_pos hA' _).le
    convert hcalc using 1 <;> simp only [A, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · have hpos : 0 < polarChordSq θ φ ψ := by
      exact hA
    have hj := abs_polarJet21_le (α / 2) θ φ ψ hpos
    have heq := iteratedDeriv_two_one_polarKernel_eq α θ φ ψ hA
    have hcalc : |iteratedDeriv 2 (fun u => iteratedDeriv 1 (fun v => polarKernel α θ u v) ψ) φ| ≤ C * A ^ ((α - (2 : ℝ) - (1 : ℝ)) / 2) := by
      calc
        _ = |polarJet21 (α / 2) θ φ ψ| := by
          exact congrArg abs heq
        _ ≤ 512 * M * A ^ ((α - (2 : ℝ) - (1 : ℝ)) / 2) := by
          have hpow : polarChordSq θ φ ψ = A := by
            rfl
          have hexp : ((α - (2 : ℝ) - (1 : ℝ)) / 2) = α / 2 - 3 / 2 := by ring
          rw [hexp]
          simpa only [hpow, M] using hj
        _ ≤ C * A ^ ((α - (2 : ℝ) - (1 : ℝ)) / 2) := by
          exact mul_le_mul_of_nonneg_right (hCdom 512 (by norm_num))
            (Real.rpow_pos_of_pos hA' _).le
    convert hcalc using 1 <;> simp only [A, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · have hpos : 0 < polarChordSq θ ψ φ := by
      rwa [← polarChordSq_symm θ φ ψ]
    have hj := abs_polarJet22_le (α / 2) θ ψ φ hpos
    have heq := iteratedDeriv_two_two_polarKernel_eq α θ φ ψ hA
    have hcalc : |iteratedDeriv 2 (fun u => iteratedDeriv 2 (fun v => polarKernel α θ u v) ψ) φ| ≤ C * A ^ ((α - (2 : ℝ) - (2 : ℝ)) / 2) := by
      calc
        _ = |polarJet22 (α / 2) θ ψ φ| := by
          exact congrArg abs heq
        _ ≤ 2048 * M * A ^ ((α - (2 : ℝ) - (2 : ℝ)) / 2) := by
          have hpow : polarChordSq θ ψ φ = A := by
            change polarChordSq θ ψ φ = polarChordSq θ φ ψ; exact polarChordSq_symm θ ψ φ
          have hexp : ((α - (2 : ℝ) - (2 : ℝ)) / 2) = α / 2 - 2 := by ring
          rw [hexp]
          simpa only [hpow, M] using hj
        _ ≤ C * A ^ ((α - (2 : ℝ) - (2 : ℝ)) / 2) := by
          exact mul_le_mul_of_nonneg_right (hCdom 2048 (by norm_num))
            (Real.rpow_pos_of_pos hA' _).le
    convert hcalc using 1 <;> simp only [A, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · omega
  · omega
  · have hpos : 0 < polarChordSq θ φ ψ := by
      exact hA
    have hj := abs_polarJet30_le (α / 2) θ φ ψ hpos
    have heq := iteratedDeriv_three_polarKernel_phi_eq α θ φ ψ hA
    have hcalc : |iteratedDeriv 3 (fun u => iteratedDeriv 0 (fun v => polarKernel α θ u v) ψ) φ| ≤ C * A ^ ((α - (3 : ℝ) - (0 : ℝ)) / 2) := by
      calc
        _ = |polarJet30 (α / 2) θ φ ψ| := by
          simpa only [iteratedDeriv_zero] using congrArg abs heq
        _ ≤ 512 * M * A ^ ((α - (3 : ℝ) - (0 : ℝ)) / 2) := by
          have hpow : polarChordSq θ φ ψ = A := by
            rfl
          have hexp : ((α - (3 : ℝ) - (0 : ℝ)) / 2) = α / 2 - 3 / 2 := by ring
          rw [hexp]
          simpa only [hpow, M] using hj
        _ ≤ C * A ^ ((α - (3 : ℝ) - (0 : ℝ)) / 2) := by
          exact mul_le_mul_of_nonneg_right (hCdom 512 (by norm_num))
            (Real.rpow_pos_of_pos hA' _).le
    convert hcalc using 1 <;> simp only [A, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · have hpos : 0 < polarChordSq θ φ ψ := by
      exact hA
    have hj := abs_polarJet31_le (α / 2) θ φ ψ hpos
    have heq := iteratedDeriv_three_one_polarKernel_eq α θ φ ψ hA
    have hcalc : |iteratedDeriv 3 (fun u => iteratedDeriv 1 (fun v => polarKernel α θ u v) ψ) φ| ≤ C * A ^ ((α - (3 : ℝ) - (1 : ℝ)) / 2) := by
      calc
        _ = |polarJet31 (α / 2) θ φ ψ| := by
          exact congrArg abs heq
        _ ≤ 2048 * M * A ^ ((α - (3 : ℝ) - (1 : ℝ)) / 2) := by
          have hpow : polarChordSq θ φ ψ = A := by
            rfl
          have hexp : ((α - (3 : ℝ) - (1 : ℝ)) / 2) = α / 2 - 2 := by ring
          rw [hexp]
          simpa only [hpow, M] using hj
        _ ≤ C * A ^ ((α - (3 : ℝ) - (1 : ℝ)) / 2) := by
          exact mul_le_mul_of_nonneg_right (hCdom 2048 (by norm_num))
            (Real.rpow_pos_of_pos hA' _).le
    convert hcalc using 1 <;> simp only [A, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · omega
  · omega
  · omega
  · have hpos : 0 < polarChordSq θ φ ψ := by
      exact hA
    have hj := abs_polarJet40_le (α / 2) θ φ ψ hpos
    have heq := iteratedDeriv_four_polarKernel_phi_eq α θ φ ψ hA
    have hcalc : |iteratedDeriv 4 (fun u => iteratedDeriv 0 (fun v => polarKernel α θ u v) ψ) φ| ≤ C * A ^ ((α - (4 : ℝ) - (0 : ℝ)) / 2) := by
      calc
        _ = |polarJet40 (α / 2) θ φ ψ| := by
          simpa only [iteratedDeriv_zero] using congrArg abs heq
        _ ≤ 2048 * M * A ^ ((α - (4 : ℝ) - (0 : ℝ)) / 2) := by
          have hpow : polarChordSq θ φ ψ = A := by
            rfl
          have hexp : ((α - (4 : ℝ) - (0 : ℝ)) / 2) = α / 2 - 2 := by ring
          rw [hexp]
          simpa only [hpow, M] using hj
        _ ≤ C * A ^ ((α - (4 : ℝ) - (0 : ℝ)) / 2) := by
          exact mul_le_mul_of_nonneg_right (hCdom 2048 (by norm_num))
            (Real.rpow_pos_of_pos hA' _).le
    convert hcalc using 1 <;> simp only [A, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  · omega
  · omega
  · omega
  · omega

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->

## Checked proof and dependencies

`polar_derivative_bound` now proves the complete `PolarDerivativeBound α` contract for `0<α<2`. The module imports only `KernelDerivatives`, and the checked theorem returns one constant for all fifteen pairs `(m,n)` with `m+n≤4` and all real `θ,φ,ψ` at positive chord square. It does not impose a phase or angle range. The selected constant is `4096 * polarCoeffBudget (α/2) + α + 1`; it is positive because the budget is a sum of absolute values plus one. The first two orders use the earlier exact first-order estimate, and the higher orders use explicit finite jet formulas. No unproved local regularity or derivative interchange is used in this module.

Write `A=polarChordSq`, `X=∂φA`, `Y=∂ψA`, `Z=∂φ∂ψA`, and `B=2−A`. The proof first identifies `A` with the squared norm of the difference of two unit vectors on the sphere, so `0≤A≤4`. A three-coordinate Cauchy estimate gives `|X|,|Y|≤2√A`; it also gives `|Z|≤2`, while `|B|≤2` follows from the range of `A`. The exact derivative table closes on these four quantities:

`∂φA=X`, `∂ψA=Y`, `∂φX=∂ψY=B`, `∂ψX=∂φY=Z`, `∂φZ=−Y`, and `∂ψZ=−X`.

Repeated one-variable `HasDerivAt` rules produce jets for the distinct derivative patterns `(2,0)`, `(1,1)`, `(3,0)`, `(2,1)`, `(4,0)`, `(3,1)`, and `(2,2)`. Symmetry in `φ,ψ` supplies the other patterns. The termwise estimate `abs_polar_monomial_le_64` uses the first-derivative square-root gain and `A≤4`: after factoring `A^(p-r/2)`, each eligible monomial is at most 64 times that power. The coefficient budget bounds all falling products of `p=α/2` through degree four. Finite triangle inequalities then give constants 8, 128, 512, or 2048 times the budget for the relevant jets. The final case split checks the exact nested `iteratedDeriv` order in the contract, including the mixed `(2,2)` case. It uses positive distance to justify every real-power differentiation and every possibly negative exponent.

This module supplies pointwise derivatives only. The near and intermediate comparable-block modules must separately establish local `C^4` regularity of their height-coordinate compositions, justify differentiation under angular integration where needed, and combine the polar estimates with chordal lower bounds. The positive-chord hypothesis is essential: coincident points are outside the contract. The proof is actually uniform for all real `α>0` in its finite estimates; the public theorem retains `α<2` to match the manuscript range and downstream use.
