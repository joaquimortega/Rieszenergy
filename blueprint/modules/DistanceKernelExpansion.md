# `BEMOCFormalization.DistanceKernelExpansion` proof guide

This module isolates the genuine all-degree harmonic expansion of the centered
chordal-power kernel. It imports `DistanceZonal` for Rodrigues-normalized
Legendre polynomials and `HarmonicAddition` for the basis addition kernel.
No new axiom or replacement definition of worst-case error is used.

For `1<s<2`, `SobolevKernel` proves by exact telescoping that the positive
series `Σ_{ℓ≥1}(2ℓ+1)a_ℓ` is summable and at most the continuous energy.
`harmonicAddition_abs_le_dim_of_diag` bounds the absolute value of each
basis addition kernel by `2ℓ+1` under its explicit diagonal hypothesis;
`harmonicAddition_abs_le_dim` supplies that bound unconditionally. Thus
`distanceKernelDegree_summable_of_addition_diag` proves absolute pointwise
convergence at every `x,y`, independently of the scalar series identity.

`HarmonicAdditionLegendre Y` states the exact addition theorem for the
Rodrigues polynomial `P_ℓ`, while `DistanceScalarExpansion s` states

```text
Σ_{ℓ≥1} a_ℓ(2ℓ+1)P_ℓ(t)
  = I_(2s−2) − (2−2t)^(s−1),   −1≤t≤1.
```

`sphere_distance_power_eq_inner` checks the unit-sphere geometry
`dist(x,y)^(2s−2)=(2−2⟨x,y⟩)^(s−1)`. Therefore the checked theorem
`distancePointwiseExpansion_of_legendre` combines the three explicit
obligations into `DistancePointwiseExpansion Y s`, with its summability
included. `sobolevEnergyComparison_of_legendre` then applies the complete
SobolevKernel transfer. `HarmonicAddition` proves the diagonal
unconditionally, and `DistanceScalarBridge` proves the scalar series given
addition. `harmonic_addition_legendre` now proves the exact all-degree addition theorem, and `Corollaries.sobolev_energy_comparison` applies the resulting pointwise expansion.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.DistanceZonal
import BEMOCFormalization.HarmonicAddition

/-! Convergence of the harmonic distance kernel from the addition diagonal. -/

open scoped BigOperators

namespace BEMOC.Definitive

/-- Once the harmonic addition diagonal is known, the centered distance-kernel
series converges absolutely at every pair of points. Its convergence does not
depend on the still-open scalar Legendre expansion identity. -/
theorem distanceKernelDegree_summable_of_addition_diag
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hdiag : HarmonicAdditionDiagonal Y) (x y : Sphere) :
    Summable (fun ℓ => distanceKernelDegree Y s ℓ x y) := by
  apply Summable.of_norm_bounded
    (fun ℓ : ℕ => (2 * (ℓ : ℝ) + 3) *
      distanceHarmonicCoefficient s (ℓ + 1))
    (distanceCoefficient_weighted_summable hs1 hs2)
  intro ℓ
  have hcoef := distanceHarmonicCoefficient_pos hs1 hs2 (ℓ + 1)
  have hkernel := harmonicAddition_abs_le_dim_of_diag Y hdiag (ℓ + 1) x y
  unfold distanceKernelDegree
  change ‖distanceHarmonicCoefficient s (ℓ + 1) *
    harmonicAdditionKernel Y (ℓ + 1) x y‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hcoef]
  have h := mul_le_mul_of_nonneg_left hkernel hcoef.le
  convert h using 1 <;> push_cast <;> ring

theorem distanceKernelDegree_summable
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (x y : Sphere) :
    Summable (fun ℓ => distanceKernelDegree Y s ℓ x y) :=
  distanceKernelDegree_summable_of_addition_diag Y hs1 hs2
    (harmonicAddition_diag Y) x y

/-- Exact addition formula with the Rodrigues-normalized Legendre polynomial. -/
def HarmonicAdditionLegendre (Y : HarmonicBasis) : Prop :=
  ∀ (ℓ : ℕ) (x y : Sphere),
    harmonicAdditionKernel Y ℓ x y =
      (2 * (ℓ : ℝ) + 1) *
        (legendrePolynomial ℓ).eval (sphereInnerKernel x y)

theorem sphereInnerKernel_northPole_parallel (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    sphereInnerKernel northPole (parallelPoint t 0 ht) = t := by
  simp [sphereInnerKernel, northPole, parallelPoint, parallelVector,
    Fin.sum_univ_succ]

/-- The addition formula and its diagonal normalization give the classical
uniform bound for the Legendre polynomials on `[-1,1]`. -/
theorem legendrePolynomial_eval_abs_le_one_of_addition
    (Y : HarmonicBasis) (hdiag : HarmonicAdditionDiagonal Y)
    (haddition : HarmonicAdditionLegendre Y)
    (ℓ : ℕ) (t : ℝ) (ht₁ : -1 ≤ t) (ht₂ : t ≤ 1) :
    |(legendrePolynomial ℓ).eval t| ≤ 1 := by
  let y : Sphere := parallelPoint t 0 ⟨ht₁, ht₂⟩
  have hinner : sphereInnerKernel northPole y = t :=
    sphereInnerKernel_northPole_parallel t ⟨ht₁, ht₂⟩
  have hbound := harmonicAddition_abs_le_dim_of_diag Y hdiag ℓ northPole y
  rw [haddition ℓ northPole y, hinner, abs_mul,
    abs_of_pos (by positivity : 0 < 2 * (ℓ : ℝ) + 1)] at hbound
  have h := (mul_le_mul_left (by positivity : 0 < 2 * (ℓ : ℝ) + 1)).mp
    (show (2 * (ℓ : ℝ) + 1) * |(legendrePolynomial ℓ).eval t| ≤
        (2 * (ℓ : ℝ) + 1) * 1 by simpa using hbound)
  simpa using h

/-- The scalar Legendre series is absolutely summable at every point of the
closed interval, using the proven coefficient majorant. -/
theorem distanceScalarSeries_summable_of_addition
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hdiag : HarmonicAdditionDiagonal Y)
    (haddition : HarmonicAdditionLegendre Y)
    (t : ℝ) (ht₁ : -1 ≤ t) (ht₂ : t ≤ 1) :
    Summable (fun ℓ : ℕ => distanceHarmonicCoefficient s (ℓ + 1) *
      (2 * (ℓ : ℝ) + 3) *
        (legendrePolynomial (ℓ + 1)).eval t) := by
  apply Summable.of_norm_bounded
    (fun ℓ : ℕ => (2 * (ℓ : ℝ) + 3) *
      distanceHarmonicCoefficient s (ℓ + 1))
    (distanceCoefficient_weighted_summable hs1 hs2)
  intro ℓ
  have hc := distanceHarmonicCoefficient_pos hs1 hs2 (ℓ + 1)
  have hp := legendrePolynomial_eval_abs_le_one_of_addition
    Y hdiag haddition (ℓ + 1) t ht₁ ht₂
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hc,
    abs_of_pos (by positivity : 0 < 2 * (ℓ : ℝ) + 3)]
  nlinarith [mul_le_mul_of_nonneg_left hp
    (show 0 ≤ distanceHarmonicCoefficient s (ℓ + 1) *
      (2 * (ℓ : ℝ) + 3) by positivity)]

theorem distanceScalarTerm_norm_le_of_addition
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hdiag : HarmonicAdditionDiagonal Y)
    (haddition : HarmonicAdditionLegendre Y)
    (ℓ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ‖distanceHarmonicCoefficient s (ℓ + 1) *
      (2 * (ℓ : ℝ) + 3) *
        (legendrePolynomial (ℓ + 1)).eval t‖ ≤
      (2 * (ℓ : ℝ) + 3) * distanceHarmonicCoefficient s (ℓ + 1) := by
  have hc := distanceHarmonicCoefficient_pos hs1 hs2 (ℓ + 1)
  have hp := legendrePolynomial_eval_abs_le_one_of_addition
    Y hdiag haddition (ℓ + 1) t ht.1 ht.2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hc,
    abs_of_pos (by positivity : 0 < 2 * (ℓ : ℝ) + 3)]
  nlinarith [mul_le_mul_of_nonneg_left hp
    (show 0 ≤ distanceHarmonicCoefficient s (ℓ + 1) *
      (2 * (ℓ : ℝ) + 3) by positivity)]

/-- Weierstrass convergence makes the scalar Legendre sum continuous on the
closed interval. -/
theorem distanceScalarSeries_continuousOn_of_addition
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hdiag : HarmonicAdditionDiagonal Y)
    (haddition : HarmonicAdditionLegendre Y) :
    ContinuousOn (fun t : ℝ => ∑' ℓ : ℕ,
      distanceHarmonicCoefficient s (ℓ + 1) *
        (2 * (ℓ : ℝ) + 3) *
          (legendrePolynomial (ℓ + 1)).eval t)
      (Set.Icc (-1 : ℝ) 1) := by
  apply continuousOn_tsum
  · intro ℓ
    fun_prop
  · exact distanceCoefficient_weighted_summable hs1 hs2
  · intro ℓ t ht
    exact distanceScalarTerm_norm_le_of_addition Y hs1 hs2 hdiag haddition ℓ t ht

theorem distanceScalarSeries_tendstoUniformlyOn_of_addition
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hdiag : HarmonicAdditionDiagonal Y)
    (haddition : HarmonicAdditionLegendre Y) :
    TendstoUniformlyOn
      (fun (N : ℕ) (t : ℝ) => ∑ ℓ ∈ Finset.range N,
        distanceHarmonicCoefficient s (ℓ + 1) *
          (2 * (ℓ : ℝ) + 3) *
            (legendrePolynomial (ℓ + 1)).eval t)
      (fun t : ℝ => ∑' ℓ : ℕ,
        distanceHarmonicCoefficient s (ℓ + 1) *
          (2 * (ℓ : ℝ) + 3) *
            (legendrePolynomial (ℓ + 1)).eval t)
      Filter.atTop (Set.Icc (-1 : ℝ) 1) := by
  apply tendstoUniformlyOn_tsum_nat (distanceCoefficient_weighted_summable hs1 hs2)
  intro ℓ t ht
  exact distanceScalarTerm_norm_le_of_addition Y hs1 hs2 hdiag haddition ℓ t ht

/-- The scalar Legendre series needed for the chordal-power kernel. -/
def DistanceScalarExpansion (s : ℝ) : Prop :=
  ∀ t : ℝ, -1 ≤ t → t ≤ 1 →
    Summable (fun ℓ : ℕ => distanceHarmonicCoefficient s (ℓ + 1) *
      (2 * (ℓ : ℝ) + 3) *
        (legendrePolynomial (ℓ + 1)).eval t) ∧
    (∑' ℓ : ℕ, distanceHarmonicCoefficient s (ℓ + 1) *
      (2 * (ℓ : ℝ) + 3) *
        (legendrePolynomial (ℓ + 1)).eval t) =
      continuousEnergy (2 * s - 2) - (2 - 2 * t) ^ (s - 1)

theorem sphere_distance_power_eq_inner (s : ℝ)
    (x y : Sphere) :
    dist x y ^ (2 * s - 2) =
      (2 - 2 * sphereInnerKernel x y) ^ (s - 1) := by
  have hd : 0 ≤ dist x y := dist_nonneg
  have hsq : dist x y ^ (2 : ℕ) = 2 - 2 * sphereInnerKernel x y := by
    simpa [sphereInnerKernel] using sphere_dist_sq_coordinates x y
  calc
    dist x y ^ (2 * s - 2) = dist x y ^ (2 * (s - 1)) := by ring
    _ = (dist x y ^ (2 : ℕ)) ^ (s - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
      ring
    _ = _ := by rw [hsq]

/-- The two exact analytic formulas combine to discharge the sole pointwise
premise of the Sobolev comparison theorem. -/
theorem distancePointwiseExpansion_of_legendre
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hdiag : HarmonicAdditionDiagonal Y)
    (haddition : HarmonicAdditionLegendre Y)
    (hscalar : DistanceScalarExpansion s) :
    DistancePointwiseExpansion Y s := by
  intro x y
  have ht := sphereInnerKernel_abs_le_one x y
  have hscalar' := hscalar (sphereInnerKernel x y) (abs_le.mp ht).1 (abs_le.mp ht).2
  have hterm (ℓ : ℕ) : distanceKernelDegree Y s ℓ x y =
      distanceHarmonicCoefficient s (ℓ + 1) *
        (2 * (ℓ : ℝ) + 3) *
          (legendrePolynomial (ℓ + 1)).eval (sphereInnerKernel x y) := by
    unfold distanceKernelDegree
    change distanceHarmonicCoefficient s (ℓ + 1) *
      harmonicAdditionKernel Y (ℓ + 1) x y = _
    rw [haddition]
    push_cast
    ring
  refine ⟨distanceKernelDegree_summable_of_addition_diag Y hs1 hs2 hdiag x y, ?_⟩
  simp_rw [hterm]
  rw [hscalar'.2]
  unfold centeredDistanceKernel
  rw [sphere_distance_power_eq_inner s x y]

/-- Concrete analytic obligations for the full comparison: the addition
diagonal, its Legendre identification, and one scalar Legendre series. -/
theorem sobolevEnergyComparison_of_legendre
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (hdiag : HarmonicAdditionDiagonal Y)
    (haddition : HarmonicAdditionLegendre Y)
    (hscalar : DistanceScalarExpansion s) :
    SobolevEnergyComparison Y s :=
  sobolevEnergyComparison_of_pointwise Y hs1 hs2
    (distancePointwiseExpansion_of_legendre Y hs1 hs2 hdiag haddition hscalar)

theorem distancePointwiseExpansion_of_legendre'
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (haddition : HarmonicAdditionLegendre Y)
    (hscalar : DistanceScalarExpansion s) :
    DistancePointwiseExpansion Y s :=
  distancePointwiseExpansion_of_legendre Y hs1 hs2
    (harmonicAddition_diag Y) haddition hscalar

theorem sobolevEnergyComparison_of_legendre'
    (Y : HarmonicBasis) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2)
    (haddition : HarmonicAdditionLegendre Y)
    (hscalar : DistanceScalarExpansion s) :
    SobolevEnergyComparison Y s :=
  sobolevEnergyComparison_of_legendre Y hs1 hs2
    (harmonicAddition_diag Y) haddition hscalar

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
