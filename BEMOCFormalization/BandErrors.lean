import BEMOCFormalization.Geometry
import BEMOCFormalization.EnergyDecomposition

open scoped BigOperators
open MeasureTheory Set
namespace BEMOC.Definitive

/-- Integration against λ_j−ν_j, implemented as a difference of ordinary integrals. -/
noncomputable def bandError (N j : ℕ) (f : ℝ → ℝ) : ℝ :=
  (N : ℝ) / 2 * (∫ t in boundary N j..boundary N (j - 1), f t) -
    (population N j : ℝ) * f (height N j)

/-- Ordered tensor of the two band error functionals: j acts on s, k on t. -/
noncomputable def bandBlock (N j k : ℕ) (G : ℝ × ℝ → ℝ) : ℝ :=
  bandError N j (fun s => bandError N k (fun t => G (s, t)))
/-- The actual latitude kernel block. -/
noncomputable def kernelBlock (α : ℝ) (N j k : ℕ) : ℝ :=
  bandBlock N j k (fun p => latitudeKernel α p.1 p.2)

/-- Exact two-moment cancellation, derived from the midpoint and mass formulas. -/
def BandMoments : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ j : RingIndex N,
    bandError N (j.val + 1) (fun _ => 1) = 0 ∧
    bandError N (j.val + 1) id = 0

/-- The signed band functional has zero mass and first moment on every occupied band. -/
theorem bandMoments : BandMoments := by
  intro N hN j
  let q := j.val + 1
  have hq : 1 ≤ q := by omega
  have hw := boundary_width hN hq
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmid : height N q =
      (boundary N (q - 1) + boundary N q) / 2 := rfl
  constructor
  · unfold bandError
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one]
    change (N : ℝ) / 2 * (boundary N (q - 1) - boundary N q) -
      (population N q : ℝ) = 0
    rw [hw]
    field_simp
    ring
  · unfold bandError
    change (N : ℝ) / 2 *
      (∫ t in boundary N q..boundary N (q - 1), t) -
      (population N q : ℝ) * height N q = 0
    rw [integral_id, hmid]
    have hmass : (population N q : ℝ) =
        (N : ℝ) / 2 * (boundary N (q - 1) - boundary N q) := by
      rw [hw]
      field_simp
      ring
    rw [hmass]
    ring

/-- Corrected variable binding for eq:latitude-decomposition. -/
def LatitudeIdentity (α : ℝ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → latitudeError α N =
    -∑ j : RingIndex N, ∑ k : RingIndex N, kernelBlock α N (j.val + 1) (k.val + 1)

/-- Exchange symmetry used when orienting unequal-scale ordered pairs. -/
def BlockSymmetry (α : ℝ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ j k : RingIndex N,
    kernelBlock α N (j.val + 1) (k.val + 1) =
      kernelBlock α N (k.val + 1) (j.val + 1)

/-- The angular average is continuous when its exponent is positive. -/
theorem continuous_latitudeKernel_bandErrors {α : ℝ} (hα : 0 < α) :
    Continuous (fun p : ℝ × ℝ => latitudeKernel α p.1 p.2) := by
  unfold latitudeKernel
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hp : 0 ≤ α / 2 := by linarith
  have hbase : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      2 - 2 * p.1.1 * p.1.2 -
        2 * Real.sqrt (1 - p.1.1 ^ 2) *
          Real.sqrt (1 - p.1.2 ^ 2) * Real.cos p.2) := by
    fun_prop
  exact (Real.continuous_rpow_const hp).comp hbase

/-- Swapping the two heights preserves the angular kernel. -/
theorem latitudeKernel_swap (α s t : ℝ) :
    latitudeKernel α s t = latitudeKernel α t s := by
  unfold latitudeKernel
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  ring

/-- Fubini for two oriented interval integrals on a compact rectangle. -/
theorem intervalIntegral_swap_of_continuous
    {K : ℝ → ℝ → ℝ} (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ s in a..b, ∫ t in c..d, K s t) =
      ∫ t in c..d, ∫ s in a..b, K s t := by
  have hrect : IntegrableOn (fun p : ℝ × ℝ => K p.1 p.2)
      (Icc a b ×ˢ Icc c d) :=
    hK.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hioc : IntegrableOn (fun p : ℝ × ℝ => K p.1 p.2)
      (Ioc a b ×ˢ Ioc c d) :=
    hrect.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hint : Integrable (Function.uncurry K)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact hioc
  simp_rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hcd]
  exact MeasureTheory.integral_integral_swap hint

/-- Integrating a jointly continuous kernel over a fixed interval preserves continuity. -/
theorem continuous_intervalIntegral_right
    {K : ℝ → ℝ → ℝ} (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (c d : ℝ) : Continuous (fun s => ∫ t in c..d, K s t) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hK

/-- The four terms obtained by expanding both signed band rules. -/
theorem bandBlock_eq_four_terms (N j k : ℕ) (K : ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2)) :
    bandBlock N j k (fun p => K p.1 p.2) =
      ((N : ℝ) / 2) ^ 2 *
          (∫ s in boundary N j..boundary N (j - 1),
            ∫ t in boundary N k..boundary N (k - 1), K s t) -
        (N : ℝ) / 2 * (population N k : ℝ) *
          (∫ s in boundary N j..boundary N (j - 1), K s (height N k)) -
        (population N j : ℝ) * (N : ℝ) / 2 *
          (∫ t in boundary N k..boundary N (k - 1), K (height N j) t) +
        (population N j : ℝ) * (population N k : ℝ) *
          K (height N j) (height N k) := by
  have hinner : IntervalIntegrable
      (fun s => ∫ t in boundary N k..boundary N (k - 1), K s t)
      volume (boundary N j) (boundary N (j - 1)) :=
    (continuous_intervalIntegral_right hK _ _).intervalIntegrable _ _
  have hatom : IntervalIntegrable
      (fun s => K s (height N k)) volume
      (boundary N j) (boundary N (j - 1)) :=
    (hK.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  unfold bandBlock bandError
  rw [intervalIntegral.integral_sub
    (hinner.const_mul ((N : ℝ) / 2))
    (hatom.const_mul (population N k : ℝ))]
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- Symmetry of two signed band rules on a continuous symmetric kernel. -/
theorem bandBlock_swap_of_continuous_of_symmetric
    (N j k : ℕ) (K : ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hsym : ∀ s t, K s t = K t s)
    (hj : boundary N j ≤ boundary N (j - 1))
    (hk : boundary N k ≤ boundary N (k - 1)) :
    bandBlock N j k (fun p => K p.1 p.2) =
      bandBlock N k j (fun p => K p.1 p.2) := by
  have hdouble :
      (∫ s in boundary N j..boundary N (j - 1),
        ∫ t in boundary N k..boundary N (k - 1), K s t) =
      (∫ s in boundary N k..boundary N (k - 1),
        ∫ t in boundary N j..boundary N (j - 1), K s t) := by
    calc
      _ = ∫ t in boundary N k..boundary N (k - 1),
            ∫ s in boundary N j..boundary N (j - 1), K s t :=
          intervalIntegral_swap_of_continuous hK hj hk
      _ = ∫ t in boundary N k..boundary N (k - 1),
            ∫ s in boundary N j..boundary N (j - 1), K t s := by
          simp_rw [hsym]
      _ = _ := rfl
  rw [bandBlock_eq_four_terms N j k K hK,
    bandBlock_eq_four_terms N k j K hK, hdouble]
  have hcrossj :
      (∫ s in boundary N j..boundary N (j - 1), K s (height N k)) =
      (∫ s in boundary N j..boundary N (j - 1), K (height N k) s) := by
    simp_rw [hsym]
  have hcrossk :
      (∫ s in boundary N k..boundary N (k - 1), K s (height N j)) =
      (∫ s in boundary N k..boundary N (k - 1), K (height N j) s) := by
    simp_rw [hsym]
  rw [hcrossj, hcrossk, hsym (height N j) (height N k)]
  ring

/-- The physical latitude-kernel blocks are symmetric for positive exponent. -/
theorem blockSymmetry_of_pos {α : ℝ} (hα : 0 < α) : BlockSymmetry α := by
  intro N hN j k
  have horder (i : RingIndex N) :
      boundary N (i.val + 1) ≤ boundary N (i.val + 1 - 1) := by
    have hpos : 0 < population N (i.val + 1) :=
      population_pos hN (by omega) (by have := i.isLt; omega)
    have hw := boundary_width hN (j := i.val + 1) (by omega)
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hpr : (0 : ℝ) ≤ population N (i.val + 1) := by exact_mod_cast hpos.le
    have hnonneg : 0 ≤ 2 * (population N (i.val + 1) : ℝ) / N :=
      div_nonneg (by positivity) hNr.le
    linarith
  exact bandBlock_swap_of_continuous_of_symmetric N (j.val + 1) (k.val + 1)
    (latitudeKernel α) (continuous_latitudeKernel_bandErrors hα)
    (latitudeKernel_swap α) (horder j) (horder k)

end BEMOC.Definitive
