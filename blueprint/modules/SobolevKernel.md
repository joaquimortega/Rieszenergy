# `BEMOCFormalization.SobolevKernel` proof guide

This module works with the independently defined spectral Sobolev norm and
worst-case quadrature error in `Sobolev.lean`. It imports `HarmonicBasis` and
`SobolevBasic`. All declarations in the exact source block below have been
checked by Lean 4.19 against pinned mathlib. The comparison theorem in this module takes the genuine distance-kernel pointwise expansion `DistancePointwiseExpansion Y s` as an explicit hypothesis. `HarmonicAdditionLegendre` and `DistanceScalarBridge` now discharge that hypothesis downstream; it is never an axiom or substitute definition.

## Spectral and kernel normalization

`harmonicQuadratureCoefficient Y X ℓ k` is exactly the quadrature error of the
basis harmonic `Y.function ℓ k`. The canonical spectral quadrature term uses
`(1+ℓ(ℓ+1))^(-s)`. Degree zero vanishes because every degree-zero harmonic is
constant. For `1<s<2`, put `α=2s−2`. The coefficient of the degree-`ℓ`
addition kernel, for `ℓ≥1`, is BSSW's positive coefficient

```text
a_ℓ = I_α · (s−1)/(s+1) · ∏_{j=0}^{ℓ−2} (j+2−s)/(j+2+s).
```

It multiplies `Σ_k Y_(ℓ,k)(x)Y_(ℓ,k)(y)` without another dimension factor:
normalized area measure makes that addition kernel equal to
`(2ℓ+1)P_ℓ(x·y)`. The required pointwise hypothesis is precisely

```text
Σ_{ℓ≥1} a_ℓ Σ_k Y_(ℓ,k)(x)Y_(ℓ,k)(y)
  = I_α − |x−y|^α,
```

with summability for every `x,y`. `DistanceScalarBridge` now checks the
Legendre coefficients and scalar series equality. The genuine addition
theorem is supplied downstream by `harmonic_addition_legendre` for this comparison route.

## Checked coefficient estimate

`distanceHarmonicCoefficient_succ_succ` proves the exact coefficient ratio.
For `t=ℓ+1−s>0`, Bernoulli's inequality yields
`(1+1/t)^(2s)≥1+2s/t`. Consequently
`a_(ℓ+1)(ℓ+2−s)^(2s)≥a_ℓ(ℓ+1−s)^(2s)`, so the product is bounded below
by the positive initial value `a_1(2−s)^(2s)`. Since
`(ℓ+1−s)^2≤1+ℓ(ℓ+1)`, the theorem
`distanceCoefficientComparison_of_range` obtains a fixed `A>0` with

```text
(1+ℓ(ℓ+1))^(−s) ≤ A a_ℓ,       ℓ≥1.
```

This holds throughout `1<s<2` without Gamma asymptotics. A second exact
identity telescopes the dimension-weighted coefficients:
`(2ℓ+1)a_ℓ = b_ℓ−b_(ℓ+1)` for
`b_ℓ=ℓ(ℓ+s)a_ℓ/(s−1)`. The module proves
`Σ_{ℓ≥1}(2ℓ+1)a_ℓ ≤ I_(2s−2)` and summability. This is the
positive majorant needed for uniform absolute convergence after an addition
bound is supplied.

## Checked reconstruction and transfer

`distanceSpectralIdentity_of_pointwise` sums the pointwise identity over all
ordered node pairs, justifies each finite/infinite exchange, and gives
`Σ distanceErrorTerm = I_α−energy(X,α)/n²`. The diagonal identity at `x=y`
and positivity of the distance terms give a uniform upper bound for the
canonical evaluation diagonal. From it, finite weighted Cauchy–Schwarz makes
the harmonic partial sums Cauchy in the sup norm. Continuity of each Fourier
coefficient and `HarmonicBasis.complete` identify the uniform limit with the
original Sobolev function. Thus `harmonicQuadratureReconstruction_of_pointwise`
and `sobolevEmbedding_of_pointwise` are both checked consequences of the one
pointwise kernel premise.

`spectralWCEBound_of_pointwise` applies finite weighted Cauchy–Schwarz to the
real quadrature functional, passes to its limit, and bounds the **actual**
supremum over the canonical Sobolev unit ball. Finally,
`sobolevEnergyComparison_of_pointwise` combines that bound, the exact energy
identity, and the proved coefficient comparison. It is the complete
comparison proof conditional only on the pointwise distance expansion and
an arbitrary genuine `HarmonicBasis`.

Primary source for the coefficient and kernel expansion:
[Brauchart–Saff–Sloan–Womersley, §5, equations (37)–(42)](https://arxiv.org/pdf/1208.3267).

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.HarmonicBasis
import BEMOCFormalization.SobolevBasic

/-! Spectral bookkeeping for the Sobolev worst-case error.  The equal-weight
quadrature functional and the harmonic coefficients here are the independently
defined objects of `Sobolev`, rather than a distance-kernel surrogate. -/

open scoped BigOperators
open MeasureTheory

namespace BEMOC.Definitive

/-- The quadrature error of one genuine spherical harmonic. -/
noncomputable def harmonicQuadratureCoefficient {ι : Type} [Fintype ι]
    (Y : HarmonicBasis) (X : ι → Sphere) (ℓ : ℕ)
    (k : Fin (2 * ℓ + 1)) : ℝ :=
  quadratureError X (Y.function ℓ k)

/-- The spectral contribution of degree `ℓ` to squared quadrature error. -/
noncomputable def spectralErrorTerm {ι : Type} [Fintype ι]
    (Y : HarmonicBasis) (s : ℝ) (X : ι → Sphere) (ℓ : ℕ) : ℝ :=
  (1 + (ℓ : ℝ) * (ℓ + 1)) ^ (-s) *
    ∑ k, harmonicQuadratureCoefficient Y X ℓ k ^ 2

theorem spectralErrorTerm_nonneg {ι : Type} [Fintype ι]
    (Y : HarmonicBasis) (s : ℝ) (X : ι → Sphere) (ℓ : ℕ) :
    0 ≤ spectralErrorTerm Y s X ℓ := by
  unfold spectralErrorTerm
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Finset.sum_nonneg
    (fun _ _ => sq_nonneg _))

/-- BSSW's degree coefficient for the centered chordal-power kernel on `S²`.
The product is its Pochhammer quotient, with the first negative factor removed. -/
noncomputable def distanceHarmonicCoefficient (s : ℝ) (ℓ : ℕ) : ℝ :=
  continuousEnergy (2 * s - 2) * ((s - 1) / (s + 1)) *
    ∏ j ∈ Finset.range (ℓ - 1), ((j : ℝ) + 2 - s) / ((j : ℝ) + 2 + s)

/-- The centered generalized-distance kernel's formal degree contribution. -/
noncomputable def distanceErrorTerm {ι : Type} [Fintype ι]
    (Y : HarmonicBasis) (s : ℝ) (X : ι → Sphere) (ℓ : ℕ) : ℝ :=
  distanceHarmonicCoefficient s (ℓ + 1) *
    ∑ k, harmonicQuadratureCoefficient Y X (ℓ + 1) k ^ 2

/-- The centered chordal-power kernel whose finite quadratic average is the
energy deficit. -/
noncomputable def centeredDistanceKernel (α : ℝ) (x y : Sphere) : ℝ :=
  continuousEnergy α - dist x y ^ α

theorem centeredDistanceKernel_average {n : ℕ} (hn : 0 < n)
    (X : Fin n → Sphere) (α : ℝ) :
    (∑ i, ∑ j, centeredDistanceKernel α (X i) (X j)) / (n : ℝ) ^ 2 =
      continuousEnergy α - energy X α / (n : ℝ) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [centeredDistanceKernel, Finset.sum_sub_distrib, Finset.sum_const_zero,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  unfold energy
  field_simp
  ring

private theorem finite_basis_quadratic_identity {ι κ : Type}
    [Fintype ι] [Fintype κ] (F : κ → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, F k i * F k j) =
      ∑ k, (∑ i, F k i) ^ 2 := by
  calc
    (∑ i, ∑ j, ∑ k, F k i * F k j) =
        ∑ i, ∑ k, ∑ j, F k i * F k j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, F k i * F k j := by
      rw [Finset.sum_comm]
    _ = ∑ k, (∑ i, F k i) ^ 2 := by
      congr 1
      ext k
      simp only [pow_two, Finset.sum_mul_sum]

/-- One degree of the pointwise harmonic distance expansion. -/
noncomputable def distanceKernelDegree (Y : HarmonicBasis) (s : ℝ)
    (ℓ : ℕ) (x y : Sphere) : ℝ :=
  distanceHarmonicCoefficient s (ℓ + 1) *
    ∑ k, Y.function (ℓ + 1) k x * Y.function (ℓ + 1) k y

theorem distanceHarmonicCoefficient_pos {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (ℓ : ℕ) : 0 < distanceHarmonicCoefficient s ℓ := by
  unfold distanceHarmonicCoefficient
  have hα : 0 < 2 * s - 2 := by linarith
  have hI : 0 < continuousEnergy (2 * s - 2) := by
    unfold continuousEnergy
    exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)
  apply mul_pos (mul_pos hI (div_pos (by linarith) (by linarith)))
  apply Finset.prod_pos
  intro j hj
  apply div_pos
  · have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  · have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith

theorem distanceErrorTerm_nonneg {ι : Type} [Fintype ι]
    (Y : HarmonicBasis) (X : ι → Sphere) {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) (ℓ : ℕ) :
    0 ≤ distanceErrorTerm Y s X ℓ := by
  unfold distanceErrorTerm
  exact mul_nonneg (distanceHarmonicCoefficient_pos hs1 hs2 _).le
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Successive positive distance-kernel coefficients have an elementary ratio. -/
theorem distanceHarmonicCoefficient_succ_succ (s : ℝ) (ℓ : ℕ) :
    distanceHarmonicCoefficient s (ℓ + 2) =
      distanceHarmonicCoefficient s (ℓ + 1) *
        (((ℓ : ℝ) + 2 - s) / ((ℓ : ℝ) + 2 + s)) := by
  simp only [distanceHarmonicCoefficient,
    show ℓ + 2 - 1 = ℓ + 1 by omega,
    show ℓ + 1 - 1 = ℓ by omega,
    Finset.prod_range_succ]
  ring

/-- A telescoping primitive for the dimension-weighted kernel coefficients. -/
noncomputable def distanceCoefficientTail (s : ℝ) (ℓ : ℕ) : ℝ :=
  (ℓ : ℝ) * ((ℓ : ℝ) + s) / (s - 1) * distanceHarmonicCoefficient s ℓ

theorem distanceCoefficient_weighted_telescopes {s : ℝ} (hs1 : 1 < s)
    (ℓ : ℕ) :
    (2 * (ℓ : ℝ) + 3) * distanceHarmonicCoefficient s (ℓ + 1) =
      distanceCoefficientTail s (ℓ + 1) -
        distanceCoefficientTail s (ℓ + 2) := by
  unfold distanceCoefficientTail
  rw [distanceHarmonicCoefficient_succ_succ]
  have hd1 : s - 1 ≠ 0 := ne_of_gt (by linarith)
  have hd2 : (ℓ : ℝ) + 2 + s ≠ 0 := ne_of_gt (by
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith)
  push_cast
  field_simp [hd1, hd2]
  ring

theorem distanceCoefficient_weighted_partial_sum {s : ℝ} (hs1 : 1 < s)
    (N : ℕ) :
    (∑ ℓ ∈ Finset.range N,
      (2 * (ℓ : ℝ) + 3) * distanceHarmonicCoefficient s (ℓ + 1)) =
      distanceCoefficientTail s 1 - distanceCoefficientTail s (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, distanceCoefficient_weighted_telescopes hs1 N]
      ring

theorem distanceCoefficientTail_nonneg {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) (ℓ : ℕ) :
    0 ≤ distanceCoefficientTail s ℓ := by
  unfold distanceCoefficientTail
  exact mul_nonneg (div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (by
      have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
      linarith)) (by linarith))
    (distanceHarmonicCoefficient_pos hs1 hs2 ℓ).le

theorem distanceCoefficientTail_one {s : ℝ} (hs1 : 1 < s) :
    distanceCoefficientTail s 1 = continuousEnergy (2 * s - 2) := by
  have hs0 : s - 1 ≠ 0 := ne_of_gt (by linarith)
  have hs2 : s + 1 ≠ 0 := ne_of_gt (by linarith)
  simp only [distanceCoefficientTail, distanceHarmonicCoefficient,
    show 1 - 1 = 0 by omega, Finset.prod_empty]
  field_simp [hs0, hs2]
  ring

/-- Dimension-weighted distance coefficients form a summable positive
majorant, with total mass at most the continuous energy. -/
theorem distanceCoefficient_weighted_summable {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) :
    Summable (fun ℓ : ℕ =>
      (2 * (ℓ : ℝ) + 3) * distanceHarmonicCoefficient s (ℓ + 1)) := by
  have hnonneg (ℓ : ℕ) :
      0 ≤ (2 * (ℓ : ℝ) + 3) * distanceHarmonicCoefficient s (ℓ + 1) :=
    mul_nonneg (by positivity) (distanceHarmonicCoefficient_pos hs1 hs2 _).le
  apply summable_of_sum_range_le hnonneg
  intro N
  rw [distanceCoefficient_weighted_partial_sum hs1 N]
  exact sub_le_self _ (distanceCoefficientTail_nonneg hs1 hs2 _)

theorem distanceCoefficient_weighted_tsum_le_energy {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) :
    (∑' ℓ : ℕ,
      (2 * (ℓ : ℝ) + 3) * distanceHarmonicCoefficient s (ℓ + 1)) ≤
      continuousEnergy (2 * s - 2) := by
  have hnonneg (ℓ : ℕ) :
      0 ≤ (2 * (ℓ : ℝ) + 3) * distanceHarmonicCoefficient s (ℓ + 1) :=
    mul_nonneg (by positivity) (distanceHarmonicCoefficient_pos hs1 hs2 _).le
  apply Real.tsum_le_of_sum_range_le hnonneg
  intro N
  rw [distanceCoefficient_weighted_partial_sum hs1 N, distanceCoefficientTail_one hs1]
  exact sub_le_self _ (distanceCoefficientTail_nonneg hs1 hs2 _)

/-- Bernoulli's inequality supplies the sharp power-law comparison for one
step of the Pochhammer quotient. -/
private theorem distance_ratio_power_step {s t : ℝ}
    (hs : 1 < s) (ht : 0 < t) :
    t ^ (2 * s) ≤ (t / (t + 2 * s)) * (t + 1) ^ (2 * s) := by
  have hden : 0 < t + 2 * s := by linarith
  have hbern := one_add_mul_self_le_rpow_one_add
    (s := 1 / t) (p := 2 * s) (by
      have h : 0 ≤ 1 / t := by positivity
      linarith)
    (by linarith)
  have hbern' : t + 2 * s ≤ t * (1 + 1 / t) ^ (2 * s) := by
    have h := mul_le_mul_of_nonneg_left hbern ht.le
    convert h using 1 <;> field_simp
  have hfactor : (t + 1) ^ (2 * s) =
      t ^ (2 * s) * (1 + 1 / t) ^ (2 * s) := by
    have heq : t + 1 = t * (1 + 1 / t) := by field_simp
    rw [heq, Real.mul_rpow ht.le (by positivity)]
  rw [hfactor]
  have hpow : (t + 2 * s) * t ^ (2 * s) ≤
      t * (t ^ (2 * s) * (1 + 1 / t) ^ (2 * s)) := by
    nlinarith [mul_le_mul_of_nonneg_left hbern' (Real.rpow_nonneg ht.le (2 * s))]
  calc
    t ^ (2 * s) ≤ (t * (t ^ (2 * s) * (1 + 1 / t) ^ (2 * s))) /
        (t + 2 * s) := (le_div_iff₀ hden).2 (by nlinarith [hpow])
    _ = t / (t + 2 * s) * (t ^ (2 * s) * (1 + 1 / t) ^ (2 * s)) := by ring

/-- The Pochhammer coefficient has a quantitative `ℓ^(-2s)` lower bound.
The shifted variable avoids a Gamma-function asymptotic. -/
theorem distanceHarmonicCoefficient_scaled_lower {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) (ℓ : ℕ) :
    distanceHarmonicCoefficient s 1 * (2 - s) ^ (2 * s) ≤
      distanceHarmonicCoefficient s (ℓ + 1) *
        ((ℓ : ℝ) + 2 - s) ^ (2 * s) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have ht : 0 < (ℓ : ℝ) + 2 - s := by
      have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
      linarith
    have hstep := distance_ratio_power_step hs1 ht
    have hcoef := (distanceHarmonicCoefficient_pos hs1 hs2 (ℓ + 1)).le
    have hmono :
        distanceHarmonicCoefficient s (ℓ + 1) *
            ((ℓ : ℝ) + 2 - s) ^ (2 * s) ≤
          distanceHarmonicCoefficient s (ℓ + 2) *
            ((ℓ : ℝ) + 3 - s) ^ (2 * s) := by
      rw [distanceHarmonicCoefficient_succ_succ]
      have h := mul_le_mul_of_nonneg_left hstep hcoef
      convert h using 1 <;> ring
    convert ih.trans hmono using 1 <;> push_cast <;> ring

/-- Uniform comparison of the canonical spectral weights with the
Pochhammer coefficients of the centered distance kernel. -/
def DistanceCoefficientComparison (s : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ ℓ : ℕ,
    (1 + ((ℓ + 1 : ℕ) : ℝ) * ((ℓ + 1 : ℕ) + 1)) ^ (-s) ≤
      A * distanceHarmonicCoefficient s (ℓ + 1)

/-- Uniform comparison of canonical Sobolev weights with the generalized
distance coefficients, obtained without Gamma asymptotics. -/
theorem distanceCoefficientComparison_of_range {s : ℝ}
    (hs1 : 1 < s) (hs2 : s < 2) : DistanceCoefficientComparison s := by
  let C : ℝ := distanceHarmonicCoefficient s 1 * (2 - s) ^ (2 * s)
  have hC : 0 < C := mul_pos (distanceHarmonicCoefficient_pos hs1 hs2 1)
    (Real.rpow_pos_of_pos (by linarith) _)
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro ℓ
  let u : ℝ := (ℓ : ℝ) + 2 - s
  let B : ℝ := 1 + ((ℓ + 1 : ℕ) : ℝ) * ((ℓ + 1 : ℕ) + 1)
  let a : ℝ := distanceHarmonicCoefficient s (ℓ + 1)
  have hu : 0 < u := by
    dsimp [u]
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have huB : u ^ 2 ≤ B := by
    dsimp [u, B]
    have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    push_cast
    nlinarith [sq_nonneg (ℓ : ℝ)]
  have hpow : u ^ (2 * s) ≤ B ^ s := by
    have h := Real.rpow_le_rpow (sq_nonneg u) huB (by linarith : 0 ≤ s)
    simpa [Real.rpow_mul hu.le, Real.rpow_natCast] using h
  have hb : B ^ (-s) ≤ (u ^ (2 * s))⁻¹ := by
    have h1 := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hu _) hpow
    simpa [Real.rpow_neg hB.le, one_div, Real.rpow_neg hu.le] using h1
  have hscaled : C ≤ a * u ^ (2 * s) :=
    distanceHarmonicCoefficient_scaled_lower hs1 hs2 ℓ
  have hapos : 0 < a := distanceHarmonicCoefficient_pos hs1 hs2 _
  have hup : 0 < u ^ (2 * s) := Real.rpow_pos_of_pos hu _
  have haux : B ^ (-s) * C ≤ a := by
    calc
      B ^ (-s) * C ≤ (u ^ (2 * s))⁻¹ * C :=
        mul_le_mul_of_nonneg_right hb hC.le
      _ = C / u ^ (2 * s) := by ring
      _ ≤ a := (div_le_iff₀ hup).2 (by nlinarith [hscaled])
  dsimp [B, a] at haux ⊢
  calc
    _ = (1 + ↑(ℓ + 1) * (↑(ℓ + 1) + 1)) ^ (-s) * (C * C⁻¹) := by
      rw [mul_inv_cancel₀ hC.ne', mul_one]
    _ = (1 + ↑(ℓ + 1) * (↑(ℓ + 1) + 1)) ^ (-s) * C * C⁻¹ := by ring
    _ ≤ distanceHarmonicCoefficient s (ℓ + 1) * C⁻¹ :=
      mul_le_mul_of_nonneg_right haux (le_of_lt (inv_pos.mpr hC))
    _ = C⁻¹ * distanceHarmonicCoefficient s (ℓ + 1) := by ring

theorem harmonicCoefficient_basis (Y : HarmonicBasis)
    (ℓ m : ℕ) (k : Fin (2 * ℓ + 1)) (j : Fin (2 * m + 1)) :
    harmonicCoefficient Y (Y.function ℓ k) m j =
      if ℓ = m ∧ k.val = j.val then 1 else 0 := by
  exact Y.orthonormal ℓ m k j

theorem harmonicCoefficient_add (Y : HarmonicBasis) (f g : C(Sphere, ℝ))
    (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    harmonicCoefficient Y (f + g) ℓ k =
      harmonicCoefficient Y f ℓ k + harmonicCoefficient Y g ℓ k := by
  have hf : Integrable (fun x : Sphere => f x * Y.function ℓ k x) sigma :=
    (f.continuous.mul (Y.function ℓ k).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (fun x : Sphere => g x * Y.function ℓ k x) sigma :=
    (g.continuous.mul (Y.function ℓ k).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [harmonicCoefficient, ContinuousMap.add_apply, add_mul,
    integral_add hf hg]

theorem harmonicCoefficient_smul (Y : HarmonicBasis) (c : ℝ)
    (f : C(Sphere, ℝ)) (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    harmonicCoefficient Y (c • f) ℓ k = c * harmonicCoefficient Y f ℓ k := by
  simp only [harmonicCoefficient, ContinuousMap.smul_apply, smul_eq_mul, mul_assoc,
    integral_const_mul]

/-- Fourier extraction as a real linear functional on continuous functions. -/
noncomputable def harmonicCoefficientLinearMap (Y : HarmonicBasis)
    (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) : C(Sphere, ℝ) →ₗ[ℝ] ℝ where
  toFun f := harmonicCoefficient Y f ℓ k
  map_add' := fun f g => harmonicCoefficient_add Y f g ℓ k
  map_smul' := fun c f => by
    simp [harmonicCoefficient_smul]

theorem harmonicCoefficientLinearMap_continuous (Y : HarmonicBasis)
    (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    Continuous (harmonicCoefficientLinearMap Y ℓ k) := by
  have hbound (f : C(Sphere, ℝ)) :
      ‖harmonicCoefficientLinearMap Y ℓ k f‖ ≤
        ‖Y.function ℓ k‖ * ‖f‖ := by
    change ‖∫ x : Sphere, f x * Y.function ℓ k x ∂sigma‖ ≤ _
    have hpoint (x : Sphere) :
        ‖f x * Y.function ℓ k x‖ ≤ ‖Y.function ℓ k‖ * ‖f‖ := by
      rw [norm_mul]
      exact mul_le_mul (f.norm_coe_le_norm x)
        ((Y.function ℓ k).norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)
        |>.trans_eq (mul_comm _ _)
    have h := norm_integral_le_of_norm_le_const
      (μ := sigma) (f := fun x : Sphere => f x * Y.function ℓ k x)
      (Filter.Eventually.of_forall hpoint)
    simpa using h
  exact (harmonicCoefficientLinearMap Y ℓ k).mkContinuous
    ‖Y.function ℓ k‖ hbound |>.continuous

/-- The full degree-`ℓ` orthogonal projection of a continuous function. -/
noncomputable def harmonicDegreeProjection (Y : HarmonicBasis)
    (f : C(Sphere, ℝ)) (ℓ : ℕ) : C(Sphere, ℝ) :=
  ∑ k : Fin (2 * ℓ + 1), harmonicCoefficient Y f ℓ k • Y.function ℓ k

theorem harmonicCoefficient_degreeProjection (Y : HarmonicBasis)
    (f : C(Sphere, ℝ)) (ℓ m : ℕ) (j : Fin (2 * m + 1)) :
    harmonicCoefficient Y (harmonicDegreeProjection Y f ℓ) m j =
      if ℓ = m then harmonicCoefficient Y f m j else 0 := by
  classical
  simp only [harmonicDegreeProjection,
    show harmonicCoefficient Y (∑ k : Fin (2 * ℓ + 1),
        harmonicCoefficient Y f ℓ k • Y.function ℓ k) m j =
      (harmonicCoefficientLinearMap Y m j)
        (∑ k : Fin (2 * ℓ + 1), harmonicCoefficient Y f ℓ k • Y.function ℓ k) from rfl,
    map_sum, map_smul, harmonicCoefficientLinearMap, harmonicCoefficient_basis]
  by_cases h : ℓ = m
  · subst m
    simp [harmonicCoefficient_basis, Finset.sum_ite_eq', Fin.val_inj]
  · simp [harmonicCoefficient_basis, h]

/-- Projection onto all harmonic degrees strictly below `L`. -/
noncomputable def harmonicPartialSum (Y : HarmonicBasis)
    (f : C(Sphere, ℝ)) (L : ℕ) : C(Sphere, ℝ) :=
  ∑ ℓ ∈ Finset.range L, harmonicDegreeProjection Y f ℓ

theorem harmonicPartialSum_apply (Y : HarmonicBasis) (f : C(Sphere, ℝ))
    (L : ℕ) (x : Sphere) :
    harmonicPartialSum Y f L x =
      ∑ ℓ ∈ Finset.range L, ∑ k : Fin (2 * ℓ + 1),
        harmonicCoefficient Y f ℓ k * Y.function ℓ k x := by
  simp [harmonicPartialSum, harmonicDegreeProjection, smul_eq_mul]

theorem harmonicCoefficient_partialSum (Y : HarmonicBasis)
    (f : C(Sphere, ℝ)) (L m : ℕ) (j : Fin (2 * m + 1)) :
    harmonicCoefficient Y (harmonicPartialSum Y f L) m j =
      if m < L then harmonicCoefficient Y f m j else 0 := by
  classical
  change (harmonicCoefficientLinearMap Y m j)
      (∑ ℓ ∈ Finset.range L, harmonicDegreeProjection Y f ℓ) = _
  rw [map_sum]
  simp_rw [show ∀ ℓ, (harmonicCoefficientLinearMap Y m j)
      (harmonicDegreeProjection Y f ℓ) =
        if ℓ = m then harmonicCoefficient Y f m j else 0 from
    fun ℓ => harmonicCoefficient_degreeProjection Y f ℓ m j]
  by_cases hm : m < L
  · simp [hm, eq_comm]
  · simp [hm, eq_comm]

theorem harmonicCoefficient_partialRemainder (Y : HarmonicBasis)
    (f : C(Sphere, ℝ)) (L m : ℕ) (j : Fin (2 * m + 1)) :
    harmonicCoefficient Y (f - harmonicPartialSum Y f L) m j =
      if m < L then 0 else harmonicCoefficient Y f m j := by
  change (harmonicCoefficientLinearMap Y m j) (f - harmonicPartialSum Y f L) = _
  rw [map_sub]
  change harmonicCoefficient Y f m j -
      harmonicCoefficient Y (harmonicPartialSum Y f L) m j = _
  rw [harmonicCoefficient_partialSum]
  split_ifs <;> ring

theorem sobolevNormTerm_partialRemainder (Y : HarmonicBasis) (s : ℝ)
    (f : C(Sphere, ℝ)) (L m : ℕ) :
    sobolevNormTerm Y s (f - harmonicPartialSum Y f L) m =
      if m < L then 0 else sobolevNormTerm Y s f m := by
  by_cases hm : m < L
  · simp [sobolevNormTerm, harmonicCoefficient_partialRemainder, hm]
  · simp [sobolevNormTerm, harmonicCoefficient_partialRemainder, hm]

theorem sobolevNormTerm_nonneg (Y : HarmonicBasis) (s : ℝ)
    (f : C(Sphere, ℝ)) (ℓ : ℕ) :
    0 ≤ sobolevNormTerm Y s f ℓ := by
  unfold sobolevNormTerm
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem sobolevNormTerm_smul (Y : HarmonicBasis) (s c : ℝ)
    (f : C(Sphere, ℝ)) (ℓ : ℕ) :
    sobolevNormTerm Y s (c • f) ℓ = c ^ 2 * sobolevNormTerm Y s f ℓ := by
  simp only [sobolevNormTerm, harmonicCoefficient_smul, mul_pow,
    ← Finset.mul_sum]
  ring

theorem summable_sobolevNormTerm_partialRemainder (Y : HarmonicBasis)
    (s : ℝ) (f : C(Sphere, ℝ))
    (hf : Summable (sobolevNormTerm Y s f)) (L : ℕ) :
    Summable (sobolevNormTerm Y s (f - harmonicPartialSum Y f L)) := by
  apply hf.congr_cofinite
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop L] with m hm
  rw [sobolevNormTerm_partialRemainder]
  simp [not_lt.mpr hm]

private theorem spectralWeight_half_mul (b s : ℝ) (hb : 0 < b) :
    b ^ (s / 2) * b ^ (-s / 2) = 1 := by
  rw [← Real.rpow_add hb]
  have : s / 2 + -s / 2 = 0 := by ring
  simp [this]

private theorem spectralWeight_half_sq (b s : ℝ) (hb : 0 < b) :
    (b ^ (s / 2)) ^ 2 = b ^ s := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hb.le]
  congr 1
  ring

private theorem spectralWeight_half_neg_sq (b s : ℝ) (hb : 0 < b) :
    (b ^ (-s / 2)) ^ 2 = b ^ (-s) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hb.le]
  congr 1
  ring

/-- Finite weighted Cauchy–Schwarz, with the same `b^s`/`b^(-s)` weights
as the Sobolev norm and canonical quadrature spectrum. -/
private theorem finite_weighted_cauchy {κ : Type} (S : Finset κ)
    (w a b : κ → ℝ) (s : ℝ) (hw : ∀ i ∈ S, 0 < w i) :
    (∑ i ∈ S, a i * b i) ^ 2 ≤
      (∑ i ∈ S, (w i) ^ s * (a i) ^ 2) *
        (∑ i ∈ S, (w i) ^ (-s) * (b i) ^ 2) := by
  let u : κ → ℝ := fun i => (w i) ^ (s / 2) * a i
  let v : κ → ℝ := fun i => (w i) ^ (-s / 2) * b i
  have hprod : (∑ i ∈ S, u i * v i) = ∑ i ∈ S, a i * b i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [u, v]
    have h := spectralWeight_half_mul (w i) s (hw i hi)
    calc
      (w i) ^ (s / 2) * a i * ((w i) ^ (-s / 2) * b i) =
          ((w i) ^ (s / 2) * (w i) ^ (-s / 2)) * (a i * b i) := by ring
      _ = a i * b i := by rw [h, one_mul]
  have hu : (∑ i ∈ S, u i ^ 2) =
      ∑ i ∈ S, (w i) ^ s * (a i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [u, mul_pow, spectralWeight_half_sq (w i) s (hw i hi)]
  have hv : (∑ i ∈ S, v i ^ 2) =
      ∑ i ∈ S, (w i) ^ (-s) * (b i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [v, mul_pow, spectralWeight_half_neg_sq (w i) s (hw i hi)]
  rw [← hprod, ← hu, ← hv]
  exact Finset.sum_mul_sq_le_sq_mul_sq S u v

theorem finite_spectral_cauchy {ι : Type} [Fintype ι]
    (Y : HarmonicBasis) (s : ℝ) (X : ι → Sphere)
    (f : C(Sphere, ℝ)) (L : ℕ) :
    (∑ ℓ ∈ Finset.range L, ∑ k : Fin (2 * ℓ + 1),
      harmonicCoefficient Y f ℓ k * harmonicQuadratureCoefficient Y X ℓ k) ^ 2 ≤
      (∑ ℓ ∈ Finset.range L, sobolevNormTerm Y s f ℓ) *
        (∑ ℓ ∈ Finset.range L, spectralErrorTerm Y s X ℓ) := by
  let S : Finset (Σ ℓ : ℕ, Fin (2 * ℓ + 1)) :=
    (Finset.range L).sigma (fun _ => Finset.univ)
  let w : (Σ ℓ : ℕ, Fin (2 * ℓ + 1)) → ℝ :=
    fun i => 1 + (i.1 : ℝ) * (i.1 + 1)
  let a : (Σ ℓ : ℕ, Fin (2 * ℓ + 1)) → ℝ :=
    fun i => harmonicCoefficient Y f i.1 i.2
  let b : (Σ ℓ : ℕ, Fin (2 * ℓ + 1)) → ℝ :=
    fun i => harmonicQuadratureCoefficient Y X i.1 i.2
  have hw : ∀ i ∈ S, 0 < w i := by
    intro i hi
    dsimp [w]
    positivity
  have h := finite_weighted_cauchy S w a b s hw
  simpa only [S, w, a, b, Finset.sum_sigma, sobolevNormTerm,
    spectralErrorTerm, ← Finset.mul_sum] using h

/-- Diagonal term including degree zero, for point-evaluation estimates. -/
noncomputable def spectralEvalTerm (Y : HarmonicBasis) (s : ℝ)
    (x : Sphere) (ℓ : ℕ) : ℝ :=
  (1 + (ℓ : ℝ) * (ℓ + 1)) ^ (-s) *
    ∑ k, Y.function ℓ k x ^ 2

theorem spectralEvalTerm_nonneg (Y : HarmonicBasis) (s : ℝ)
    (x : Sphere) (ℓ : ℕ) : 0 ≤ spectralEvalTerm Y s x ℓ := by
  unfold spectralEvalTerm
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem finite_spectral_eval_cauchy (Y : HarmonicBasis) (s : ℝ)
    (f : C(Sphere, ℝ)) (x : Sphere) (L : ℕ) :
    (∑ ℓ ∈ Finset.range L, ∑ k : Fin (2 * ℓ + 1),
      harmonicCoefficient Y f ℓ k * Y.function ℓ k x) ^ 2 ≤
      (∑ ℓ ∈ Finset.range L, sobolevNormTerm Y s f ℓ) *
        (∑ ℓ ∈ Finset.range L, spectralEvalTerm Y s x ℓ) := by
  let S : Finset (Σ ℓ : ℕ, Fin (2 * ℓ + 1)) :=
    (Finset.range L).sigma (fun _ => Finset.univ)
  let w : (Σ ℓ : ℕ, Fin (2 * ℓ + 1)) → ℝ :=
    fun i => 1 + (i.1 : ℝ) * (i.1 + 1)
  let a : (Σ ℓ : ℕ, Fin (2 * ℓ + 1)) → ℝ :=
    fun i => harmonicCoefficient Y f i.1 i.2
  let b : (Σ ℓ : ℕ, Fin (2 * ℓ + 1)) → ℝ :=
    fun i => Y.function i.1 i.2 x
  have hw : ∀ i ∈ S, 0 < w i := by
    intro i hi
    dsimp [w]
    positivity
  have h := finite_weighted_cauchy S w a b s hw
  simpa only [S, w, a, b, Finset.sum_sigma, sobolevNormTerm,
    spectralEvalTerm, ← Finset.mul_sum] using h

theorem finite_spectral_eval_cauchy_finset (Y : HarmonicBasis) (s : ℝ)
    (f : C(Sphere, ℝ)) (x : Sphere) (D : Finset ℕ) :
    (∑ ℓ ∈ D, ∑ k : Fin (2 * ℓ + 1),
      harmonicCoefficient Y f ℓ k * Y.function ℓ k x) ^ 2 ≤
      (∑ ℓ ∈ D, sobolevNormTerm Y s f ℓ) *
        (∑ ℓ ∈ D, spectralEvalTerm Y s x ℓ) := by
  let S : Finset (Σ ℓ : ℕ, Fin (2 * ℓ + 1)) :=
    D.sigma (fun _ => Finset.univ)
  let w : (Σ ℓ : ℕ, Fin (2 * ℓ + 1)) → ℝ :=
    fun i => 1 + (i.1 : ℝ) * (i.1 + 1)
  let a : (Σ ℓ : ℕ, Fin (2 * ℓ + 1)) → ℝ :=
    fun i => harmonicCoefficient Y f i.1 i.2
  let b : (Σ ℓ : ℕ, Fin (2 * ℓ + 1)) → ℝ :=
    fun i => Y.function i.1 i.2 x
  have hw : ∀ i ∈ S, 0 < w i := by
    intro i hi
    dsimp [w]
    positivity
  have h := finite_weighted_cauchy S w a b s hw
  simpa only [S, w, a, b, Finset.sum_sigma, sobolevNormTerm,
    spectralEvalTerm, ← Finset.mul_sum] using h

theorem harmonicPartialSum_difference_sq_le (Y : HarmonicBasis) (s : ℝ)
    (f : C(Sphere, ℝ)) (x : Sphere) {L M : ℕ} (hLM : L ≤ M) :
    (harmonicPartialSum Y f M x - harmonicPartialSum Y f L x) ^ 2 ≤
      (∑ ℓ ∈ Finset.Ico L M, sobolevNormTerm Y s f ℓ) *
        (∑ ℓ ∈ Finset.Ico L M, spectralEvalTerm Y s x ℓ) := by
  rw [harmonicPartialSum_apply, harmonicPartialSum_apply]
  rw [← Finset.sum_Ico_eq_sub _ hLM]
  exact finite_spectral_eval_cauchy_finset Y s f x (Finset.Ico L M)

/-- A degree-zero member of any harmonic basis is a constant function. -/
theorem harmonicBasis_zero_constant (Y : HarmonicBasis) (k : Fin 1) :
    ∃ c : ℝ, ∀ x : Sphere, Y.function 0 k x = c := by
  obtain ⟨p, hp, -, heval⟩ := Y.harmonic 0 k
  refine ⟨MvPolynomial.coeff 0 p, ?_⟩
  intro x
  rw [heval x, homogeneous_zero_eq_constant hp]
  simp

/-- Every nonconstant harmonic degree has zero surface mean. -/
theorem harmonicBasis_positive_degree_mean_zero (Y : HarmonicBasis)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (k : Fin (2 * ℓ + 1)) :
    (∫ x : Sphere, Y.function ℓ k x ∂sigma) = 0 := by
  obtain ⟨c, hc⟩ := harmonicBasis_zero_constant Y 0
  have hc2 : c * c = 1 := by
    have h := Y.orthonormal 0 0 (0 : Fin 1) (0 : Fin 1)
    simp only [ite_true, and_self] at h
    simpa only [hc, integral_const, smul_eq_mul, Measure.real, measure_univ,
      ENNReal.toReal_one, one_mul] using h
  have hcne : c ≠ 0 := by
    intro h
    simp [h] at hc2
  have horth := Y.orthonormal ℓ 0 k (0 : Fin 1)
  have hne : ℓ ≠ 0 := Nat.ne_of_gt hℓ
  simp only [hne, false_and, ite_false] at horth
  have hz : (∫ x : Sphere, Y.function ℓ k x ∂sigma) * c = 0 := by
    simpa only [hc, integral_mul_const, smul_eq_mul] using horth
  exact (mul_eq_zero.mp hz).resolve_right hcne

theorem harmonicBasis_zero_sq_one (Y : HarmonicBasis) (x : Sphere) :
    Y.function 0 (0 : Fin 1) x ^ 2 = 1 := by
  obtain ⟨c, hc⟩ := harmonicBasis_zero_constant Y 0
  have h := Y.orthonormal 0 0 (0 : Fin 1) (0 : Fin 1)
  simp only [ite_true, and_self] at h
  have hc2 : c * c = 1 := by
    simpa only [hc, integral_const, smul_eq_mul, Measure.real, measure_univ,
      ENNReal.toReal_one, one_mul] using h
  simpa [hc, pow_two] using hc2

theorem spectralEvalTerm_zero (Y : HarmonicBasis) (s : ℝ) (x : Sphere) :
    spectralEvalTerm Y s x 0 = 1 := by
  simp [spectralEvalTerm, harmonicBasis_zero_sq_one Y x]

/-- Every degree-zero harmonic integrates exactly under equal weights. -/
theorem harmonicQuadratureCoefficient_zero {ι : Type} [Fintype ι] [Nonempty ι]
    (Y : HarmonicBasis) (X : ι → Sphere) (k : Fin 1) :
    harmonicQuadratureCoefficient Y X 0 k = 0 := by
  obtain ⟨c, hc⟩ := harmonicBasis_zero_constant Y k
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι).ne'
  unfold harmonicQuadratureCoefficient quadratureError
  simp [hc, hcard]

theorem harmonicQuadratureCoefficient_pos_degree {ι : Type} [Fintype ι]
    (Y : HarmonicBasis) (X : ι → Sphere) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (k : Fin (2 * ℓ + 1)) :
    harmonicQuadratureCoefficient Y X ℓ k =
      (∑ i, Y.function ℓ k (X i)) / Fintype.card ι := by
  simp [harmonicQuadratureCoefficient, quadratureError,
    harmonicBasis_positive_degree_mean_zero Y ℓ hℓ k]

theorem distanceKernelDegree_average {n : ℕ} (hn : 0 < n)
    (Y : HarmonicBasis) (s : ℝ) (X : Fin n → Sphere) (ℓ : ℕ) :
    (∑ i, ∑ j, distanceKernelDegree Y s ℓ (X i) (X j)) / (n : ℝ) ^ 2 =
      distanceErrorTerm Y s X ℓ := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsum :
      (∑ i, ∑ j, distanceKernelDegree Y s ℓ (X i) (X j)) =
        distanceHarmonicCoefficient s (ℓ + 1) *
          ∑ k, (∑ i, Y.function (ℓ + 1) k (X i)) ^ 2 := by
    simp only [distanceKernelDegree]
    simp_rw [← Finset.mul_sum]
    rw [finite_basis_quadratic_identity]
  rw [hsum]
  unfold distanceErrorTerm
  simp_rw [harmonicQuadratureCoefficient_pos_degree Y X (ℓ + 1) (Nat.zero_lt_succ ℓ)]
  simp only [div_pow]
  rw [← Finset.sum_div]
  field_simp

theorem spectralErrorTerm_zero {ι : Type} [Fintype ι] [Nonempty ι]
    (Y : HarmonicBasis) (s : ℝ) (X : ι → Sphere) :
    spectralErrorTerm Y s X 0 = 0 := by
  simp [spectralErrorTerm, harmonicQuadratureCoefficient_zero Y X]

/-- The spectral norm of a single normalized harmonic occupies exactly one degree. -/
theorem sobolevNormTerm_basis (Y : HarmonicBasis) (s : ℝ)
    (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) (m : ℕ) :
    sobolevNormTerm Y s (Y.function ℓ k) m =
      if ℓ = m then (1 + (ℓ : ℝ) * (ℓ + 1)) ^ s else 0 := by
  classical
  by_cases h : ℓ = m
  · subst m
    have hcard : ({x : Fin (2 * ℓ + 1) | k.val = x.val} : Finset _).card = 1 := by
      have heq : ({x : Fin (2 * ℓ + 1) | k.val = x.val} : Finset _) = {k} := by
        ext x
        simp [Fin.ext_iff, eq_comm]
      rw [heq]
      simp
    simp [sobolevNormTerm, harmonicCoefficient_basis, Finset.sum_ite_eq', hcard]
  · simp [sobolevNormTerm, harmonicCoefficient_basis, h]

theorem summable_sobolevNormTerm_basis (Y : HarmonicBasis) (s : ℝ)
    (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
    Summable (sobolevNormTerm Y s (Y.function ℓ k)) := by
  rw [show sobolevNormTerm Y s (Y.function ℓ k) =
      fun m => if ℓ = m then (1 + (ℓ : ℝ) * (ℓ + 1)) ^ s else 0 from
    funext (sobolevNormTerm_basis Y s ℓ k)]
  exact summable_of_ne_finset_zero (s := {ℓ}) (by
    intro m hm
    simp only [Finset.mem_singleton] at hm
    simp [Ne.symm hm])

theorem quadratureError_add {ι : Type} [Fintype ι]
    (X : ι → Sphere) (f g : C(Sphere, ℝ)) :
    quadratureError X (f + g) = quadratureError X f + quadratureError X g := by
  have hf : Integrable (fun x : Sphere => f x) sigma :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (fun x : Sphere => g x) sigma :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [quadratureError, ContinuousMap.add_apply, Finset.sum_add_distrib,
    integral_add hf hg]
  ring

theorem quadratureError_smul {ι : Type} [Fintype ι]
    (X : ι → Sphere) (c : ℝ) (f : C(Sphere, ℝ)) :
    quadratureError X (c • f) = c * quadratureError X f := by
  simp only [quadratureError, ContinuousMap.smul_apply, smul_eq_mul,
    ← Finset.mul_sum, integral_const_mul]
  ring

noncomputable def quadratureErrorLinearMap {ι : Type} [Fintype ι]
    (X : ι → Sphere) : C(Sphere, ℝ) →ₗ[ℝ] ℝ where
  toFun := quadratureError X
  map_add' := quadratureError_add X
  map_smul' := quadratureError_smul X

theorem quadratureError_partialSum {ι : Type} [Fintype ι]
    (Y : HarmonicBasis) (X : ι → Sphere) (f : C(Sphere, ℝ)) (L : ℕ) :
    quadratureError X (harmonicPartialSum Y f L) =
      ∑ ℓ ∈ Finset.range L, ∑ k : Fin (2 * ℓ + 1),
        harmonicCoefficient Y f ℓ k * harmonicQuadratureCoefficient Y X ℓ k := by
  change (quadratureErrorLinearMap X) (harmonicPartialSum Y f L) = _
  simp only [harmonicPartialSum, harmonicDegreeProjection, map_sum, map_smul,
    quadratureErrorLinearMap, harmonicQuadratureCoefficient, smul_eq_mul]
  rfl

/-- The analytic Parseval inequality needed to evaluate the actual spectral
worst-case error.  Its proof requires uniform harmonic reconstruction. -/
def SpectralWCEBound (Y : HarmonicBasis) (s : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ X : Fin n → Sphere,
    Summable (fun ℓ => spectralErrorTerm Y s X (ℓ + 1)) ∧
      sobolevWCE Y s X ^ 2 ≤
        ∑' ℓ, spectralErrorTerm Y s X (ℓ + 1)

/-- Reconstruction only at quadrature functionals. It follows from uniform
convergence of the finite harmonic projections on the Sobolev unit ball. -/
def HarmonicQuadratureReconstruction (Y : HarmonicBasis) (s : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ X : Fin n → Sphere,
    ∀ f : C(Sphere, ℝ), SobolevUnitBall Y s f →
      Filter.Tendsto (fun L => quadratureError X (harmonicPartialSum Y f L))
        Filter.atTop (nhds (quadratureError X f))

/-- The distance-kernel harmonic identity, including convergence and the
geometric normalization of the continuous energy. -/
def DistanceSpectralIdentity (Y : HarmonicBasis) (s : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ X : Fin n → Sphere,
    Summable (distanceErrorTerm Y s X) ∧
      (∑' ℓ, distanceErrorTerm Y s X ℓ) =
        continuousEnergy (2 * s - 2) - energy X (2 * s - 2) / (n : ℝ) ^ 2

/-- The exact pointwise Legendre/addition expansion of the centered distance
kernel, with convergence recorded for each pair of points. -/
def DistancePointwiseExpansion (Y : HarmonicBasis) (s : ℝ) : Prop :=
  ∀ x y : Sphere, Summable (fun ℓ => distanceKernelDegree Y s ℓ x y) ∧
    (∑' ℓ, distanceKernelDegree Y s ℓ x y) =
      centeredDistanceKernel (2 * s - 2) x y

/-- Partial sums of the distance-kernel diagonal, viewed as continuous
functions of the evaluation point. -/
noncomputable def distanceDiagonalPartial (Y : HarmonicBasis)
    (s : ℝ) (L : ℕ) (x : Sphere) : ℝ :=
  ∑ ℓ ∈ Finset.range L, distanceKernelDegree Y s ℓ x x

theorem distanceKernelDegree_diag_nonneg (Y : HarmonicBasis)
    {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (ℓ : ℕ) (x : Sphere) : 0 ≤ distanceKernelDegree Y s ℓ x x := by
  unfold distanceKernelDegree
  exact mul_nonneg (distanceHarmonicCoefficient_pos hs1 hs2 _).le
    (Finset.sum_nonneg (fun k _ => by simpa [pow_two] using
      (sq_nonneg (Y.function (ℓ + 1) k x))))

theorem distanceDiagonalPartial_tendstoUniformly (Y : HarmonicBasis)
    {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hpoint : DistancePointwiseExpansion Y s) :
    TendstoUniformly (distanceDiagonalPartial Y s)
      (fun _ : Sphere => continuousEnergy (2 * s - 2)) Filter.atTop := by
  have hcont (L : ℕ) : Continuous (distanceDiagonalPartial Y s L) := by
    unfold distanceDiagonalPartial distanceKernelDegree
    fun_prop
  have hmono : Monotone (distanceDiagonalPartial Y s) := by
    intro L M hLM x
    unfold distanceDiagonalPartial
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hLM)
      (fun ℓ _ _ => distanceKernelDegree_diag_nonneg Y hs1 hs2 ℓ x)
  have hlimit (x : Sphere) :
      Filter.Tendsto (fun L => distanceDiagonalPartial Y s L x) Filter.atTop
        (nhds (continuousEnergy (2 * s - 2))) := by
    have h := (hpoint x x).1.tendsto_sum_tsum_nat
    have hα : 0 < 2 * s - 2 := by linarith
    simpa [distanceDiagonalPartial, (hpoint x x).2,
      centeredDistanceKernel, Real.zero_rpow hα.ne'] using h
  exact Monotone.tendstoUniformly_of_forall_tendsto hcont hmono
    continuous_const hlimit

/-- The canonical spectral reproducing kernel's diagonal term in positive
degrees. -/
noncomputable def canonicalDiagonalTerm (Y : HarmonicBasis) (s : ℝ)
    (x : Sphere) (ℓ : ℕ) : ℝ :=
  (1 + ((ℓ + 1 : ℕ) : ℝ) * ((ℓ + 1 : ℕ) + 1)) ^ (-s) *
    ∑ k, Y.function (ℓ + 1) k x ^ 2

theorem canonicalDiagonalTerm_nonneg (Y : HarmonicBasis) (s : ℝ)
    (x : Sphere) (ℓ : ℕ) : 0 ≤ canonicalDiagonalTerm Y s x ℓ := by
  unfold canonicalDiagonalTerm
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- The exact distance expansion and the checked coefficient comparison
bound the canonical spectral kernel diagonally by a constant independent of
the evaluation point. -/
theorem canonicalDiagonal_bound_of_distanceExpansion (Y : HarmonicBasis)
    {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hpoint : DistancePointwiseExpansion Y s) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : Sphere,
      Summable (canonicalDiagonalTerm Y s x) ∧
        (∑' ℓ, canonicalDiagonalTerm Y s x ℓ) ≤
          A * continuousEnergy (2 * s - 2) := by
  obtain ⟨A, hA, hcoef⟩ := distanceCoefficientComparison_of_range hs1 hs2
  refine ⟨A, hA, ?_⟩
  intro x
  have hdiag (ℓ : ℕ) :
      canonicalDiagonalTerm Y s x ℓ ≤ A * distanceKernelDegree Y s ℓ x x := by
    unfold canonicalDiagonalTerm distanceKernelDegree
    simp only [← sq]
    have hs : 0 ≤ ∑ k : Fin (2 * (ℓ + 1) + 1),
        Y.function (ℓ + 1) k x ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    convert mul_le_mul_of_nonneg_right (hcoef ℓ) hs using 1; ring
  have hsum : Summable (canonicalDiagonalTerm Y s x) :=
    Summable.of_nonneg_of_le (canonicalDiagonalTerm_nonneg Y s x)
      hdiag ((hpoint x x).1.mul_left A)
  have hbound := hsum.tsum_le_tsum hdiag ((hpoint x x).1.mul_left A)
  rw [((hpoint x x).1).tsum_mul_left] at hbound
  have hα : 0 < 2 * s - 2 := by linarith
  have hcenter : centeredDistanceKernel (2 * s - 2) x x =
      continuousEnergy (2 * s - 2) := by
    simp [centeredDistanceKernel, Real.zero_rpow hα.ne']
  rw [(hpoint x x).2, hcenter] at hbound
  exact ⟨hsum, hbound⟩

theorem spectralEvalTerm_uniform_bound_of_distanceExpansion (Y : HarmonicBasis)
    {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hpoint : DistancePointwiseExpansion Y s) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : Sphere,
      Summable (spectralEvalTerm Y s x) ∧
        (∑' ℓ, spectralEvalTerm Y s x ℓ) ≤ K := by
  obtain ⟨A, hA, hdiag⟩ :=
    canonicalDiagonal_bound_of_distanceExpansion Y hs1 hs2 hpoint
  have hI : 0 < continuousEnergy (2 * s - 2) := by
    unfold continuousEnergy
    exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)
  refine ⟨1 + A * continuousEnergy (2 * s - 2), by positivity, ?_⟩
  intro x
  obtain ⟨hsum, hbound⟩ := hdiag x
  have hshift : Summable (fun ℓ => spectralEvalTerm Y s x (ℓ + 1)) := by
    convert hsum using 1
  have hfull : Summable (spectralEvalTerm Y s x) :=
    (summable_nat_add_iff 1).mp hshift
  refine ⟨hfull, ?_⟩
  rw [hfull.tsum_eq_zero_add, spectralEvalTerm_zero]
  simpa only [spectralEvalTerm, canonicalDiagonalTerm,
    Nat.cast_add, Nat.cast_one] using add_le_add_left hbound 1

/-- Uniform diagonal control turns every summable Sobolev Fourier sequence
into a uniformly Cauchy sequence of continuous harmonic partial sums. -/
theorem harmonicPartialSum_cauchy_of_evalBound (Y : HarmonicBasis) (s : ℝ)
    (f : C(Sphere, ℝ)) (hf : Summable (sobolevNormTerm Y s f))
    (K : ℝ) (hK : 0 < K)
    (hEval : ∀ x : Sphere, Summable (spectralEvalTerm Y s x) ∧
      (∑' ℓ, spectralEvalTerm Y s x ℓ) ≤ K) :
    CauchySeq (harmonicPartialSum Y f) := by
  let T : ℝ := ∑' ℓ, sobolevNormTerm Y s f ℓ
  have htail : Filter.Tendsto (fun L => T -
      ∑ ℓ ∈ Finset.range L, sobolevNormTerm Y s f ℓ)
      Filter.atTop (nhds 0) := by
    have hTconst : Filter.Tendsto (fun _ : ℕ => T) Filter.atTop (nhds T) :=
      tendsto_const_nhds
    simpa [T] using hTconst.sub hf.tendsto_sum_tsum_nat
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hδ : 0 < ε ^ 2 / (2 * K) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (htail.eventually (eventually_lt_nhds hδ))
  refine ⟨N, ?_⟩
  have hordered (L M : ℕ) (hLM : L ≤ M) (hLN : N ≤ L) :
      dist (harmonicPartialSum Y f M) (harmonicPartialSum Y f L) < ε := by
    rw [dist_eq_norm]
    apply ((harmonicPartialSum Y f M - harmonicPartialSum Y f L).norm_lt_iff hε).2
    intro x
    have hNormIco : (∑ ℓ ∈ Finset.Ico L M, sobolevNormTerm Y s f ℓ) <
        ε ^ 2 / (2 * K) := by
      rw [Finset.sum_Ico_eq_sub _ hLM]
      have hM := hf.sum_le_tsum (Finset.range M)
        (fun ℓ _ => sobolevNormTerm_nonneg Y s f ℓ)
      have hL := hN L hLN
      dsimp [T] at hL
      linarith
    have hNormNonneg : 0 ≤ ∑ ℓ ∈ Finset.Ico L M,
        sobolevNormTerm Y s f ℓ :=
      Finset.sum_nonneg (fun ℓ _ => sobolevNormTerm_nonneg Y s f ℓ)
    have hEvalIco : (∑ ℓ ∈ Finset.Ico L M, spectralEvalTerm Y s x ℓ) ≤ K :=
      ((hEval x).1.sum_le_tsum _
        (fun ℓ _ => spectralEvalTerm_nonneg Y s x ℓ)).trans (hEval x).2
    have hsq := harmonicPartialSum_difference_sq_le Y s f x hLM
    have hprod :
        (∑ ℓ ∈ Finset.Ico L M, sobolevNormTerm Y s f ℓ) *
          (∑ ℓ ∈ Finset.Ico L M, spectralEvalTerm Y s x ℓ) < ε ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hEvalIco hNormNonneg
      have h2 := mul_lt_mul_of_pos_right hNormIco hK
      have hKK : K ≠ 0 := hK.ne'
      have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
      nlinarith [div_mul_cancel₀ (ε ^ 2) (show 2 * K ≠ 0 by positivity)]
    have hreal : |harmonicPartialSum Y f M x - harmonicPartialSum Y f L x| < ε := by
      nlinarith [sq_abs (harmonicPartialSum Y f M x - harmonicPartialSum Y f L x),
        abs_nonneg (harmonicPartialSum Y f M x - harmonicPartialSum Y f L x)]
    simpa [Real.norm_eq_abs] using hreal
  intro m hm n hn
  by_cases hnm : n ≤ m
  · exact hordered n m hnm hn
  · rw [dist_comm]
    exact hordered m n (le_of_not_ge hnm) hm

/-- The uniform limit of the genuine harmonic projections is the original
continuous function, by continuity of Fourier extraction and completeness of
the basis. -/
theorem harmonicPartialSum_tendsto_of_evalBound (Y : HarmonicBasis) (s : ℝ)
    (f : C(Sphere, ℝ)) (hf : Summable (sobolevNormTerm Y s f))
    (K : ℝ) (hK : 0 < K)
    (hEval : ∀ x : Sphere, Summable (spectralEvalTerm Y s x) ∧
      (∑' ℓ, spectralEvalTerm Y s x ℓ) ≤ K) :
    Filter.Tendsto (harmonicPartialSum Y f) Filter.atTop (nhds f) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete
    (harmonicPartialSum_cauchy_of_evalBound Y s f hf K hK hEval)
  have hcoeff (ℓ : ℕ) (k : Fin (2 * ℓ + 1)) :
      harmonicCoefficient Y g ℓ k = harmonicCoefficient Y f ℓ k := by
    have hlim : Filter.Tendsto
        (fun L => harmonicCoefficient Y (harmonicPartialSum Y f L) ℓ k)
        Filter.atTop (nhds (harmonicCoefficient Y g ℓ k)) := by
      exact ((harmonicCoefficientLinearMap_continuous Y ℓ k).tendsto g).comp hg
    have hconst : Filter.Tendsto
        (fun L => harmonicCoefficient Y (harmonicPartialSum Y f L) ℓ k)
        Filter.atTop (nhds (harmonicCoefficient Y f ℓ k)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop (ℓ + 1)] with L hL
      rw [harmonicCoefficient_partialSum]
      simp [show ℓ < L by omega]
    exact tendsto_nhds_unique hlim hconst
  have hzero : ∀ ℓ k, harmonicCoefficient Y (g - f) ℓ k = 0 := by
    intro ℓ k
    change (harmonicCoefficientLinearMap Y ℓ k) (g - f) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hcoeff ℓ k)
  have hgf : g = f := by
    have hz := Y.complete (g - f) hzero
    exact sub_eq_zero.mp hz
  rw [hgf] at hg
  exact hg

theorem quadratureErrorLinearMap_continuous {ι : Type} [Fintype ι]
    [Nonempty ι] (X : ι → Sphere) :
    Continuous (quadratureErrorLinearMap X) := by
  have hbound (f : C(Sphere, ℝ)) :
      ‖quadratureErrorLinearMap X f‖ ≤ 2 * ‖f‖ := by
    change |quadratureError X f| ≤ 2 * ‖f‖
    exact quadratureError_abs_le_two_mul X f ‖f‖
      (fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
  exact ((quadratureErrorLinearMap X).mkContinuous 2 hbound).continuous

/-- The distance-kernel diagonal supplies uniform harmonic reconstruction at
every quadrature functional. -/
theorem harmonicQuadratureReconstruction_of_pointwise
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hpoint : DistancePointwiseExpansion Y s) :
    HarmonicQuadratureReconstruction Y s := by
  obtain ⟨K, hK, hEval⟩ :=
    spectralEvalTerm_uniform_bound_of_distanceExpansion Y hs1 hs2 hpoint
  intro n hn X f hf
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ((quadratureErrorLinearMap_continuous X).tendsto f).comp
    (harmonicPartialSum_tendsto_of_evalBound Y s f hf.1 K hK hEval)

/-- The distance-kernel diagonal also gives the actual Sobolev embedding. -/
theorem sobolevEmbedding_of_pointwise
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hpoint : DistancePointwiseExpansion Y s) :
    SobolevEmbedding Y s := by
  obtain ⟨K, hK, hEval⟩ :=
    spectralEvalTerm_uniform_bound_of_distanceExpansion Y hs1 hs2 hpoint
  refine ⟨Real.sqrt K, Real.sqrt_pos.2 hK, ?_⟩
  intro f hf x
  have hfinite (L : ℕ) : (harmonicPartialSum Y f L x) ^ 2 ≤ K := by
    have hn : (∑ ℓ ∈ Finset.range L, sobolevNormTerm Y s f ℓ) ≤ 1 :=
      (hf.1.sum_le_tsum _ (fun ℓ _ => sobolevNormTerm_nonneg Y s f ℓ)).trans hf.2
    have he : (∑ ℓ ∈ Finset.range L, spectralEvalTerm Y s x ℓ) ≤ K :=
      ((hEval x).1.sum_le_tsum _
        (fun ℓ _ => spectralEvalTerm_nonneg Y s x ℓ)).trans (hEval x).2
    have he0 : 0 ≤ ∑ ℓ ∈ Finset.range L, spectralEvalTerm Y s x ℓ :=
      Finset.sum_nonneg (fun ℓ _ => spectralEvalTerm_nonneg Y s x ℓ)
    rw [harmonicPartialSum_apply]
    exact (finite_spectral_eval_cauchy Y s f x L).trans (by
      nlinarith [mul_le_mul_of_nonneg_right hn he0])
  have hlim : Filter.Tendsto (fun L => harmonicPartialSum Y f L x)
      Filter.atTop (nhds (f x)) :=
    (continuous_eval_const x).tendsto f |>.comp
      (harmonicPartialSum_tendsto_of_evalBound Y s f hf.1 K hK hEval)
  have hsq : (f x) ^ 2 ≤ K :=
    le_of_tendsto (hlim.pow 2) (Filter.Eventually.of_forall hfinite)
  exact (Real.le_sqrt (abs_nonneg _) hK.le).2 (by simpa only [sq_abs] using hsq)

theorem distanceSpectralIdentity_of_pointwise
    (Y : HarmonicBasis) (s : ℝ)
    (hpoint : DistancePointwiseExpansion Y s) :
    DistanceSpectralIdentity Y s := by
  intro n hn X
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsum : Summable (fun ℓ =>
      (∑ i, ∑ j, distanceKernelDegree Y s ℓ (X i) (X j))) := by
    apply summable_sum
    intro i _
    apply summable_sum
    intro j _
    exact (hpoint (X i) (X j)).1
  have hterm (ℓ : ℕ) : distanceErrorTerm Y s X ℓ =
      (∑ i, ∑ j, distanceKernelDegree Y s ℓ (X i) (X j)) / (n : ℝ) ^ 2 :=
    (distanceKernelDegree_average hn Y s X ℓ).symm
  have hdistSum : Summable (distanceErrorTerm Y s X) := by
    simpa only [funext hterm] using hsum.div_const ((n : ℝ) ^ 2)
  refine ⟨hdistSum, ?_⟩
  simp_rw [hterm]
  rw [tsum_div_const]
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => (hpoint (X i) (X j)).1))]
  simp_rw [Summable.tsum_finsetSum (fun j _ => (hpoint _ _).1)]
  simp_rw [(hpoint _ _).2]
  exact centeredDistanceKernel_average hn X (2 * s - 2)

/-- Finite Cauchy–Schwarz and actual harmonic reconstruction bound the
supremum in `sobolevWCE` by its canonical spectral quadrature series. -/
theorem spectralWCEBound_of_pointwise_reconstruction (Y : HarmonicBasis)
    {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hpoint : DistancePointwiseExpansion Y s)
    (hrec : HarmonicQuadratureReconstruction Y s) :
    SpectralWCEBound Y s := by
  obtain ⟨A, hA, hcoef⟩ := distanceCoefficientComparison_of_range hs1 hs2
  have hDistance := distanceSpectralIdentity_of_pointwise Y s hpoint
  intro n hn X
  have hterm (ℓ : ℕ) :
      spectralErrorTerm Y s X (ℓ + 1) ≤ A * distanceErrorTerm Y s X ℓ := by
    unfold spectralErrorTerm distanceErrorTerm
    have hs : 0 ≤ ∑ k : Fin (2 * (ℓ + 1) + 1),
        harmonicQuadratureCoefficient Y X (ℓ + 1) k ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    convert mul_le_mul_of_nonneg_right (hcoef ℓ) hs using 1; ring
  have hsum : Summable (fun ℓ => spectralErrorTerm Y s X (ℓ + 1)) :=
    Summable.of_nonneg_of_le (fun ℓ => spectralErrorTerm_nonneg Y s X _)
      hterm ((hDistance n hn X).1.mul_left A)
  refine ⟨hsum, ?_⟩
  let T : ℝ := ∑' ℓ, spectralErrorTerm Y s X (ℓ + 1)
  have hT : 0 ≤ T := tsum_nonneg (fun ℓ => spectralErrorTerm_nonneg Y s X _)
  have hpointBound (f : C(Sphere, ℝ)) (hf : SobolevUnitBall Y s f) :
      (quadratureError X f) ^ 2 ≤ T := by
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hfinite (L : ℕ) :
        (quadratureError X (harmonicPartialSum Y f L)) ^ 2 ≤ T := by
      have hnorm : (∑ ℓ ∈ Finset.range L, sobolevNormTerm Y s f ℓ) ≤ 1 :=
        (hf.1.sum_le_tsum _ (fun ℓ _ => sobolevNormTerm_nonneg Y s f ℓ)).trans hf.2
      have herr : (∑ ℓ ∈ Finset.range L, spectralErrorTerm Y s X ℓ) ≤ T := by
        cases L with
        | zero => simpa using hT
        | succ L =>
          rw [Finset.sum_range_succ', spectralErrorTerm_zero Y s X, add_zero]
          exact hsum.sum_le_tsum _
            (fun ℓ _ => spectralErrorTerm_nonneg Y s X (ℓ + 1))
      rw [quadratureError_partialSum]
      exact (finite_spectral_cauchy Y s X f L).trans (by
        have herr0 : 0 ≤ ∑ ℓ ∈ Finset.range L, spectralErrorTerm Y s X ℓ :=
          Finset.sum_nonneg (fun ℓ _ => spectralErrorTerm_nonneg Y s X ℓ)
        nlinarith [mul_le_mul_of_nonneg_right hnorm herr0])
    exact le_of_tendsto ((hrec n hn X f hf).pow 2)
      (Filter.Eventually.of_forall hfinite)
  have hBdd : BddAbove {e : ℝ | ∃ f : C(Sphere, ℝ),
      SobolevUnitBall Y s f ∧ e = |quadratureError X f|} := by
    refine ⟨Real.sqrt T, ?_⟩
    rintro e ⟨f, hf, rfl⟩
    exact (Real.le_sqrt (abs_nonneg _) hT).2 (by
      simpa only [sq_abs] using hpointBound f hf)
  have hWCE : sobolevWCE Y s X ≤ Real.sqrt T := by
    unfold sobolevWCE
    apply csSup_le (sobolev_error_set_nonempty Y s X)
    rintro e ⟨f, hf, rfl⟩
    exact (Real.le_sqrt (abs_nonneg _) hT).2 (by
      simpa only [sq_abs] using hpointBound f hf)
  have hWCE0 : 0 ≤ sobolevWCE Y s X := by
    unfold sobolevWCE
    exact le_csSup hBdd (show (0 : ℝ) ∈ _ from
      ⟨0, zero_mem_sobolev_unit_ball Y s, by simp [quadratureError_zero]⟩)
  calc
    sobolevWCE Y s X ^ 2 ≤ (Real.sqrt T) ^ 2 :=
      (sq_le_sq₀ hWCE0 (Real.sqrt_nonneg T)).2 hWCE
    _ = T := Real.sq_sqrt hT

/-- The three analytic kernel obligations together imply comparison for the
independently defined worst-case error and geometric energy. -/
theorem sobolevEnergyComparison_of_spectral
    (Y : HarmonicBasis) (s : ℝ)
    (hWCE : SpectralWCEBound Y s)
    (hDistance : DistanceSpectralIdentity Y s)
    (hCoeff : DistanceCoefficientComparison s) :
    SobolevEnergyComparison Y s := by
  obtain ⟨A, hA, hcoef⟩ := hCoeff
  refine ⟨A, hA, ?_⟩
  intro n hn X
  obtain ⟨hsum, hbound⟩ := hWCE n hn X
  obtain ⟨hdistSum, hdistEq⟩ := hDistance n hn X
  have hpoint (ℓ : ℕ) :
      spectralErrorTerm Y s X (ℓ + 1) ≤ A * distanceErrorTerm Y s X ℓ := by
    unfold spectralErrorTerm distanceErrorTerm
    have hs : 0 ≤ ∑ k : Fin (2 * (ℓ + 1) + 1),
        harmonicQuadratureCoefficient Y X (ℓ + 1) k ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    convert mul_le_mul_of_nonneg_right (hcoef ℓ) hs using 1; ring
  have hsumBound := hsum.tsum_le_tsum hpoint (hdistSum.mul_left A)
  rw [hdistSum.tsum_mul_left] at hsumBound
  exact hbound.trans (by simpa [hdistEq] using hsumBound)

/-- One exact distance-kernel harmonic expansion implies the independently
defined spectral WCE estimate, with no additional reconstruction hypothesis. -/
theorem spectralWCEBound_of_pointwise (Y : HarmonicBasis)
    {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hpoint : DistancePointwiseExpansion Y s) :
    SpectralWCEBound Y s :=
  spectralWCEBound_of_pointwise_reconstruction Y hs1 hs2 hpoint
    (harmonicQuadratureReconstruction_of_pointwise Y hs1 hs2 hpoint)

/-- The full geometric comparison follows from the genuine BSSW kernel
expansion; coefficient asymptotics, embedding, WCE reconstruction, and all
infinite-sum exchanges are proved in this module. -/
theorem sobolevEnergyComparison_of_pointwise (Y : HarmonicBasis)
    {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hpoint : DistancePointwiseExpansion Y s) :
    SobolevEnergyComparison Y s :=
  sobolevEnergyComparison_of_spectral Y s
    (spectralWCEBound_of_pointwise Y hs1 hs2 hpoint)
    (distanceSpectralIdentity_of_pointwise Y s hpoint)
    (distanceCoefficientComparison_of_range hs1 hs2)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
