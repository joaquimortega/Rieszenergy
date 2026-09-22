# `BEMOCFormalization.CapDiscrepancy` proof guide

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.EnergyDecomposition
import BEMOCFormalization.SurfaceMeasure
import BEMOCFormalization.SphereProjection
import BEMOCFormalization.SphereCapMeasure

open scoped BigOperators
open MeasureTheory
namespace BEMOC.Definitive

/-- Closed spherical cap, using the manuscript's chordal inner-product convention. -/
def cap (u : Sphere) (t : ℝ) : Set Sphere :=
  {x | t ≤ @Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)}

theorem measurableSet_cap (u : Sphere) (t : ℝ) : MeasurableSet (cap u t) := by
  unfold cap
  exact (continuous_const.inner
    (continuous_subtype_val : Continuous fun x : Sphere => (x : Ambient))).measurable
    measurableSet_Ici

/-- Joint incidence set for centers, heights, and test points. -/
def capIncidence : Set ((Sphere × ℝ) × Sphere) :=
  {p | p.1.2 ≤ @Inner.inner ℝ Ambient _ (p.1.1 : Ambient) (p.2 : Ambient)}

theorem measurableSet_capIncidence : MeasurableSet capIncidence := by
  unfold capIncidence
  apply measurableSet_le
  · fun_prop
  · fun_prop

/-- Cap area varies measurably with center and threshold. -/
theorem measurable_capArea :
    Measurable (fun p : Sphere × ℝ => (sigma (cap p.1 p.2)).toReal) := by
  have h := (measurable_measure_prodMk_left (ν := sigma)
    measurableSet_capIncidence).ennreal_toReal
  convert h using 1

/-- Empirical cap proportion minus normalized surface area. -/
noncomputable def capError {ι : Type} [Fintype ι] (X : ι → Sphere)
    (u : Sphere) (t : ℝ) : ℝ := by
  classical
  exact (∑ i, if X i ∈ cap u t then (1 : ℝ) else 0) / Fintype.card ι -
    (sigma (cap u t)).toReal

/-- The cap error is jointly measurable in center and threshold. -/
theorem measurable_capError {ι : Type} [Fintype ι] (X : ι → Sphere) :
    Measurable (fun p : Sphere × ℝ => capError X p.1 p.2) := by
  classical
  have heach (i : ι) : Measurable
      (fun p : Sphere × ℝ => if X i ∈ cap p.1 p.2 then (1 : ℝ) else 0) := by
    have hset : MeasurableSet {p : Sphere × ℝ | X i ∈ cap p.1 p.2} := by
      change MeasurableSet {p : Sphere × ℝ | p.2 ≤
        @Inner.inner ℝ Ambient _ (p.1 : Ambient) (X i : Ambient)}
      apply measurableSet_le
      · fun_prop
      · fun_prop
    exact Measurable.ite hset measurable_const measurable_const
  unfold capError
  exact ((Finset.measurable_sum Finset.univ (fun i _ => heach i)).div_const _).sub
    measurable_capArea

/-- Both terms in the empirical cap error are proportions. -/
theorem abs_capError_le_one {ι : Type} [Fintype ι] [Nonempty ι]
    (X : ι → Sphere) (u : Sphere) (t : ℝ) :
    |capError X u t| ≤ 1 := by
  classical
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hsumnonneg :
      0 ≤ (∑ i : ι, if X i ∈ cap u t then (1 : ℝ) else 0) := by
    positivity
  have hsumle : (∑ i : ι, if X i ∈ cap u t then (1 : ℝ) else 0) ≤
      (Fintype.card ι : ℝ) := by
    calc
      _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (by
        intro i hi
        split_ifs <;> norm_num)
      _ = _ := by simp
  have hsig0 : 0 ≤ (sigma (cap u t)).toReal := ENNReal.toReal_nonneg
  have hsig1 : (sigma (cap u t)).toReal ≤ 1 := by
    simpa [Measure.real_def] using
      (measureReal_le_one (μ := sigma) (s := cap u t))
  unfold capError
  rw [abs_le]
  constructor <;> nlinarith [div_nonneg hsumnonneg hcard.le,
    (div_le_one hcard).2 hsumle]

/-- The squared cap error is integrable on the product of the center sphere
and the unnormalized height interval. -/
theorem integrable_capError_sq {ι : Type} [Fintype ι] [Nonempty ι]
    (X : ι → Sphere) :
    Integrable (fun p : Sphere × ℝ => capError X p.1 p.2 ^ 2)
      (sigma.prod (volume.restrict (Set.Icc (-1 : ℝ) 1))) := by
  have hfinite :
      IsFiniteMeasure (sigma.prod (volume.restrict (Set.Icc (-1 : ℝ) 1))) := inferInstance
  refine Integrable.mono (integrable_const (1 : ℝ))
    ((measurable_capError X).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with p
  simp only [Real.norm_eq_abs, abs_pow]
  have h := abs_capError_le_one X p.1 p.2
  exact (pow_le_pow_left₀ (abs_nonneg _) h 2).trans (by norm_num)
/-- Actual integrated squared cap error; the height measure is dt, of total mass two. -/
noncomputable def capDiscrepancySq {ι : Type} [Fintype ι] (X : ι → Sphere) : ℝ :=
  ∫ t in Set.Icc (-1 : ℝ) 1, ∫ u, capError X u t ^ 2 ∂sigma
/-- Actual L² spherical cap discrepancy, defined independently of energy. -/
noncomputable def capDiscrepancy {ι : Type} [Fintype ι] (X : ι → Sphere) : ℝ :=
  Real.sqrt (capDiscrepancySq X)

/-- Stolarsky with ordinary dt; replacing dt by dt/2 would change the factor to eight. -/
def StolarskyIdentity : Prop :=
  ∀ n : ℕ, 0 < n → ∀ X : Fin n → Sphere,
    4 * capDiscrepancySq X = continuousEnergy 1 - energy X 1 / (n : ℝ) ^ 2

/-- Geometric nonnegativity before invoking the invariance principle. -/
theorem capDiscrepancySq_nonneg {ι : Type} [Fintype ι] (X : ι → Sphere) :
    0 ≤ capDiscrepancySq X := by
  unfold capDiscrepancySq
  exact integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))

/-- The exact interval integral of two cap-height indicators. The interval
uses ordinary Lebesgue measure, so its mass is two. -/
theorem integral_cap_indicators (a b : ℝ) (ha₀ : -1 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : -1 ≤ b) :
    (∫ t in Set.Icc (-1 : ℝ) 1,
      (if t ≤ a then (1 : ℝ) else 0) * (if t ≤ b then (1 : ℝ) else 0)) =
      1 + min a b := by
  have hm₀ : -1 ≤ min a b := le_min ha₀ hb₀
  have hm₁ : min a b ≤ 1 := (min_le_left a b).trans ha₁
  have hfun : ∀ t : ℝ,
      (if t ≤ a then (1 : ℝ) else 0) * (if t ≤ b then (1 : ℝ) else 0) =
      (Set.Iic (min a b)).indicator (fun _ => (1 : ℝ)) t := by
    intro t
    by_cases hta : t ≤ a <;> by_cases htb : t ≤ b <;>
      simp [hta, htb, Set.indicator, Set.mem_Iic, le_min_iff]
  simp_rw [hfun]
  rw [setIntegral_indicator measurableSet_Iic]
  have hs : Set.Icc (-1 : ℝ) 1 ∩ Set.Iic (min a b) =
      Set.Icc (-1) (min a b) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨htl, _⟩, htm⟩
      exact ⟨htl, htm⟩
    · intro h
      exact ⟨⟨h.1, h.2.trans hm₁⟩, h.2⟩
  rw [hs, setIntegral_const, Measure.real_def, Real.volume_Icc]
  simp [sub_neg_eq_add, ENNReal.toReal_ofReal (by linarith : 0 ≤ min a b + 1)]
  ring

/-- The absolute-value form of the height-indicator kernel used in the
Stolarsky expansion. -/
theorem min_eq_mean_sub_abs (a b : ℝ) :
    min a b = (a + b - |a - b|) / 2 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- The form that survives cancellation of the constant and linear terms
when the centered cap counts are expanded. -/
theorem integral_cap_indicators_abs (a b : ℝ) (ha₀ : -1 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : -1 ≤ b) :
    (∫ t in Set.Icc (-1 : ℝ) 1,
      (if t ≤ a then (1 : ℝ) else 0) * (if t ≤ b then (1 : ℝ) else 0)) =
      1 + (a + b - |a - b|) / 2 := by
  rw [integral_cap_indicators a b ha₀ ha₁ hb₀, min_eq_mean_sub_abs]

/-- Every inner product of two unit spherical points is a valid cap height. -/
theorem sphere_inner_bounds (u x : Sphere) :
    -1 ≤ @Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient) ∧
    @Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient) ≤ 1 := by
  have hu : ‖(u : Ambient)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using u.property
  have hx : ‖(x : Ambient)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using x.property
  have h := abs_real_inner_le_norm (u : Ambient) (x : Ambient)
  rw [hu, hx, mul_one] at h
  exact abs_le.mp h

attribute [local instance] Classical.propDecidable

/-- The cap-pair height integral is the scalar kernel entering Stolarsky's
invariance principle. -/
theorem integral_two_caps (u x y : Sphere) :
    (∫ t in Set.Icc (-1 : ℝ) 1,
      (if x ∈ cap u t then (1 : ℝ) else 0) *
        (if y ∈ cap u t then (1 : ℝ) else 0)) =
      1 + min (@Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient))
        (@Inner.inner ℝ Ambient _ (u : Ambient) (y : Ambient)) := by
  simpa only [cap, Set.mem_setOf_eq] using
    integral_cap_indicators _ _ (sphere_inner_bounds u x).1
      (sphere_inner_bounds u x).2 (sphere_inner_bounds u y).1

private noncomputable def capProjection (x u : Sphere) : ℝ :=
  @Inner.inner ℝ Ambient _ (u : Ambient) (x : Ambient)

/-- Spherical averaging of the `min` kernel leaves exactly a quarter of the
chordal distance, with negative sign. -/
theorem integral_min_sphere (x y : Sphere) :
    (∫ u : Sphere, min (capProjection x u) (capProjection y u) ∂sigma) =
      -dist x y / 4 := by
  have hfun : ∀ u : Sphere,
      min (capProjection x u) (capProjection y u) =
        (capProjection x u + capProjection y u -
          |@Inner.inner ℝ Ambient _ (u : Ambient)
            ((x : Ambient) - (y : Ambient))|) / 2 := by
    intro u
    rw [min_eq_mean_sub_abs]
    simp only [capProjection, inner_sub_right]
  simp_rw [hfun]
  have habs : Integrable (fun u : Sphere =>
      |@Inner.inner ℝ Ambient _ (u : Ambient)
        ((x : Ambient) - (y : Ambient))|) sigma := by
    have hc : Continuous (fun u : Sphere =>
        |@Inner.inner ℝ Ambient _ (u : Ambient)
          ((x : Ambient) - (y : Ambient))|) :=
      ((continuous_subtype_val : Continuous fun u : Sphere => (u : Ambient)).inner
        continuous_const).abs
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  have hint (v : Ambient) : Integrable (fun u : Sphere =>
      @Inner.inner ℝ Ambient _ (u : Ambient) v) sigma := by
    have hc : Continuous (fun u : Sphere =>
        @Inner.inner ℝ Ambient _ (u : Ambient) v) :=
      (continuous_subtype_val : Continuous fun u : Sphere => (u : Ambient)).inner
        continuous_const
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  have hx : Integrable (capProjection x) sigma := hint (x : Ambient)
  have hy : Integrable (capProjection y) sigma := hint (y : Ambient)
  have hsplit :
      (∫ u : Sphere, capProjection x u + capProjection y u -
        |@Inner.inner ℝ Ambient _ (u : Ambient)
          ((x : Ambient) - (y : Ambient))| ∂sigma) =
      (∫ u : Sphere, capProjection x u ∂sigma) +
      (∫ u : Sphere, capProjection y u ∂sigma) -
      (∫ u : Sphere, |@Inner.inner ℝ Ambient _ (u : Ambient)
        ((x : Ambient) - (y : Ambient))| ∂sigma) := by
    have h₁ := integral_sub (hx.add hy) habs
    have h₂ := integral_add hx hy
    simpa only [Pi.add_apply, Pi.sub_apply, h₂] using h₁
  rw [integral_div, hsplit]
  simp only [capProjection, sphere_projection_integral, sphere_projection_abs_integral]
  change (0 + 0 - ‖(x : Ambient) - (y : Ambient)‖ / 2) / 2 =
    -dist (x : Ambient) (y : Ambient) / 4
  rw [dist_eq_norm]
  ring

/-- Exact average overlap of two caps over all centers and thresholds. -/
theorem integral_two_caps_sphere (x y : Sphere) :
    (∫ u : Sphere, (∫ t in Set.Icc (-1 : ℝ) 1,
      (if x ∈ cap u t then (1 : ℝ) else 0) *
        (if y ∈ cap u t then (1 : ℝ) else 0)) ∂sigma) =
      1 - dist x y / 4 := by
  simp_rw [integral_two_caps]
  have hc : Continuous (fun u : Sphere =>
      min (capProjection x u) (capProjection y u)) := by
    exact (((continuous_subtype_val : Continuous fun u : Sphere => (u : Ambient)).inner
      continuous_const).min
      ((continuous_subtype_val : Continuous fun u : Sphere => (u : Ambient)).inner
      continuous_const))
  have hmin : Integrable (fun u : Sphere =>
      min (capProjection x u) (capProjection y u)) sigma := by
    simpa using hc.continuousOn.integrableOn_compact isCompact_univ
  change (∫ u : Sphere, (1 : ℝ) +
    min (capProjection x u) (capProjection y u) ∂sigma) = _
  have hsplit : (∫ u : Sphere, (1 : ℝ) +
      min (capProjection x u) (capProjection y u) ∂sigma) =
      (∫ _u : Sphere, (1 : ℝ) ∂sigma) +
      (∫ u : Sphere, min (capProjection x u) (capProjection y u) ∂sigma) := by
    simpa only [Pi.add_apply] using
      (integral_add (integrable_const (1 : ℝ)) hmin)
  rw [hsplit, integral_const, integral_min_sphere]
  simp [Measure.real_def, sigma_apply_univ]
  ring

private noncomputable def capFeature (x : Sphere) (p : ℝ × Sphere) : ℝ :=
  if x ∈ cap p.2 p.1 then 1 else 0

private theorem measurable_capFeature (x : Sphere) : Measurable (capFeature x) := by
  have hset : MeasurableSet {p : ℝ × Sphere | x ∈ cap p.2 p.1} := by
    change MeasurableSet {p : ℝ × Sphere | p.1 ≤
      @Inner.inner ℝ Ambient _ (p.2 : Ambient) (x : Ambient)}
    apply measurableSet_le
    · fun_prop
    · fun_prop
  exact Measurable.ite hset measurable_const measurable_const

private theorem integrable_capFeature_pair (x y : Sphere) :
    Integrable (fun p : ℝ × Sphere => capFeature x p * capFeature y p)
      ((volume.restrict (Set.Icc (-1 : ℝ) 1)).prod sigma) := by
  have hfinite : IsFiniteMeasure
      ((volume.restrict (Set.Icc (-1 : ℝ) 1)).prod sigma) := inferInstance
  refine Integrable.mono (integrable_const (1 : ℝ))
    ((measurable_capFeature x).mul (measurable_capFeature y)).aestronglyMeasurable ?_
  filter_upwards with p
  dsimp [capFeature]
  split_ifs <;> norm_num

/-- Fubini is valid for the actual bounded cap-pair indicator. -/
theorem integral_two_caps_swap (x y : Sphere) :
    (∫ t in Set.Icc (-1 : ℝ) 1, (∫ u : Sphere,
      (if x ∈ cap u t then (1 : ℝ) else 0) *
        (if y ∈ cap u t then (1 : ℝ) else 0) ∂sigma)) =
    (∫ u : Sphere, (∫ t in Set.Icc (-1 : ℝ) 1,
      (if x ∈ cap u t then (1 : ℝ) else 0) *
        (if y ∈ cap u t then (1 : ℝ) else 0)) ∂sigma) := by
  simpa only [capFeature] using (integral_integral_swap
    (μ := volume.restrict (Set.Icc (-1 : ℝ) 1)) (ν := sigma)
    (f := fun t u => capFeature x (t, u) * capFeature y (t, u))
    (integrable_capFeature_pair x y))

/-- The overlap kernel in the manuscript's original order of integration. -/
theorem integral_two_caps_manuscript_order (x y : Sphere) :
    (∫ t in Set.Icc (-1 : ℝ) 1, (∫ u : Sphere,
      (if x ∈ cap u t then (1 : ℝ) else 0) *
        (if y ∈ cap u t then (1 : ℝ) else 0) ∂sigma)) =
      1 - dist x y / 4 := by
  rw [integral_two_caps_swap, integral_two_caps_sphere]

/-- Cap incidence is symmetric in the center and test point. -/
theorem cap_indicator_centers_eq_indicator (x : Sphere) (t : ℝ) (u : Sphere) :
    (if x ∈ cap u t then (1 : ℝ) else 0) =
      (cap x t).indicator (fun _ => (1 : ℝ)) u := by
  have hmem : x ∈ cap u t ↔ u ∈ cap x t := by
    simp only [cap, Set.mem_setOf_eq]
    simpa only [real_inner_comm]
  simp [Set.indicator, hmem]

theorem integrable_cap_indicator_centers (x : Sphere) (t : ℝ) :
    Integrable (fun u : Sphere => if x ∈ cap u t then (1 : ℝ) else 0) sigma := by
  simp_rw [cap_indicator_centers_eq_indicator]
  exact (integrable_const (1 : ℝ)).indicator (measurableSet_cap x t)

/-- For a fixed point, integrating over cap centers gives that cap's area. -/
theorem integral_cap_indicator_centers (x : Sphere) (t : ℝ) :
    (∫ u : Sphere, if x ∈ cap u t then (1 : ℝ) else 0 ∂sigma) =
      (sigma (cap x t)).toReal := by
  simp_rw [cap_indicator_centers_eq_indicator]
  simpa [Measure.real_def] using
    (integral_indicator_one (μ := sigma) (measurableSet_cap x t))

/-- Empirical cap error is unchanged by an arbitrary finite relabeling. -/
theorem capError_comp_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (X : κ → Sphere) (u : Sphere) (t : ℝ) :
    capError (X ∘ e) u t = capError X u t := by
  classical
  have hsum : (∑ i : ι, if X (e i) ∈ cap u t then (1 : ℝ) else 0) =
      ∑ j : κ, if X j ∈ cap u t then (1 : ℝ) else 0 := by
    apply Fintype.sum_equiv e
    intro i
    rfl
  simp only [capError, Function.comp_apply, hsum, Fintype.card_congr e]

theorem capDiscrepancySq_comp_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (X : κ → Sphere) :
    capDiscrepancySq (X ∘ e) = capDiscrepancySq X := by
  simp only [capDiscrepancySq, capError_comp_equiv e X]

theorem capDiscrepancy_comp_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (X : κ → Sphere) :
    capDiscrepancy (X ∘ e) = capDiscrepancy X := by
  simp only [capDiscrepancy, capDiscrepancySq_comp_equiv e X]

/-- Relabeling/cardinality bridge for the concrete point-index type. -/
def DiamondStolarsky : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N,
    4 * (N : ℝ) ^ 2 * capDiscrepancySq (point N φ) = deficit 1 N φ

/-- The construction's population identity identifies its dependent point
labels with `Fin N`. -/
theorem pointIndex_card_of_constructionFacts
    (hcon : ConstructionFacts) (N : ℕ) (hN : 4 ≤ N) :
    Fintype.card (PointIndex N) = N := by
  obtain ⟨_, _, _, hpop, _, _⟩ := hcon N hN
  simpa [PointIndex, Fintype.card_sigma] using hpop

/-- Ordered-pair energy is invariant under finite relabeling. -/
theorem energy_comp_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (X : κ → Sphere) (α : ℝ) :
    energy (X ∘ e) α = energy X α := by
  classical
  simp only [energy, Function.comp_apply]
  apply Fintype.sum_equiv e
  intro i
  exact Fintype.sum_equiv e _ _ (by intro j; rfl)

/-- The concrete Stolarsky identity needs no additional analytic assumption
once the universal identity and point-count theorem are available. -/
theorem diamondStolarsky_of_stolarsky (hcon : ConstructionFacts)
    (hStol : StolarskyIdentity) : DiamondStolarsky := by
  intro N hN φ
  let e : PointIndex N ≃ Fin N :=
    Fintype.equivFinOfCardEq (pointIndex_card_of_constructionFacts hcon N hN)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have h := hStol N (by omega) (point N φ ∘ e.symm)
  rw [capDiscrepancySq_comp_equiv e.symm, energy_comp_equiv e.symm] at h
  unfold deficit diamondEnergy
  field_simp at h ⊢
  nlinarith

/-- Beck's external lower estimate for actual sets, with injectivity explicit. -/
def BeckLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ X : Fin n → Sphere,
    Function.Injective X → c * (n : ℝ) ^ (-(3 : ℝ) / 4) ≤ capDiscrepancy X

/-- Beck's universal lower bound applies to the concrete Diamond point set
after verifying its population count and distinctness. -/
theorem diamond_beck_lower_of (hcon : ConstructionFacts) (hbeck : BeckLowerBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N,
      c * (N : ℝ) ^ (-(3 : ℝ) / 4) ≤ capDiscrepancy (point N φ) := by
  obtain ⟨c, hc, hbeck⟩ := hbeck
  refine ⟨c, hc, ?_⟩
  intro N hN φ
  let e : PointIndex N ≃ Fin N :=
    Fintype.equivFinOfCardEq (pointIndex_card_of_constructionFacts hcon N hN)
  have hinj : Function.Injective (point N φ ∘ e.symm) := by
    exact (hcon N hN).2.2.2.2.2 φ |>.comp e.symm.injective
  have h := hbeck N (by omega) (point N φ ∘ e.symm) hinj
  rwa [capDiscrepancy_comp_equiv e.symm] at h

/-- Corollary main, stronger by its uniformity in arbitrary ring phases. -/
def CapDiscrepancyCorollary : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 4 ≤ N → ∀ φ : Phases N,
    c * (N : ℝ) ^ (-(3 : ℝ) / 4) ≤ capDiscrepancy (point N φ) ∧
    capDiscrepancy (point N φ) ≤ C * (N : ℝ) ^ (-(3 : ℝ) / 4)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->

**Status and source.** The module defines the cap observable, proves the elementary nonnegativity of its squared integral, and states four unproved `Prop` contracts: `StolarskyIdentity`, `DiamondStolarsky`, `BeckLowerBound`, and `CapDiscrepancyCorollary`. The source is `definitive.tex:64–84` for definition, identity, and lower bound, and `:139–147` for the corollary. Its direct code dependency is `EnergyDecomposition`, which imports `Construction`, `ContinuousEnergy`, and ultimately `Core`. Analytic sphere integration should reuse `ContinuousEnergy.SurfaceIntegration` once that proposition is proved; the cap theorem must not be reduced to an energy-defined discrepancy.

**Definition and normalization.** `cap u t` is the closed set of points with `t≤⟪u,x⟫`; this agrees with the manuscript's `u·x≥t`. `capError X u t` is an empirical *proportion* minus `sigma (cap u t)`, whose real measure is obtained through `.toReal`. To identify this with the manuscript's formula, establish `IsProbabilityMeasure sigma`, `sigma (cap u t)≠⊤`, and the cap's measurability. For `n>0`, prove `(Finset.univ.sum fun i => if X i∈cap u t then 1 else 0)/n` equals `# {i | ...}/n`. The squared discrepancy integrates first over center `u` against normalized surface measure, then over `t` against ordinary volume restricted to `Icc (-1) 1`. This is `dt` of mass 2. The reference integral has the opposite nesting, but Tonelli/Fubini for a bounded nonnegative measurable square gives equality. Bound `|capError|≤1` (or ≤2) for finite integrability. The boundary at `t=±1` is measure zero, so `Icc` versus open or half-open endpoints does not change the value.

**Proof of the universal identity.** For a clean Lean proof, first establish the scalar interval lemma

`∫ t in Icc (-1) 1, (if t≤a then 1 else 0)*(if t≤b then 1 else 0) = 1 + min a b`

when `a,b∈[-1,1]`. This follows because the product is the indicator of `Icc (-1) (min a b)`. Next use `min a b = (a+b-|a-b|)/2`. Expand the square in the integrated cap error. A finite signed-measure viewpoint is attractive: let `ν=(1/n)∑ᵢδ_{Xᵢ}-sigma`. It has total mass zero, and `capError` is its cap mass. After interchanging integrals, constant and linear terms in `a` and `b` vanish because `ν(Sphere)=0`; the remaining kernel is `-1/2 ∫_{Sphere}|⟪u,x-y⟫| dσ(u)`. Rotational invariance gives `∫|⟪u,v⟫|dσ(u)=‖v‖/2`. Consequently `D²=-1/4 ∬dist(x,y)dν(x)dν(y)`. Expand `ν`; use the constant distance potential `continuousEnergy 1=4/3`, yielding `4D²=4/3-energy X 1/n²`. A proof with direct finite sums and integrals is also possible and avoids signed measures, at the cost of more expansion lemmas. Verify `n=1` as a normalization check: `D²=1/3`.

`Core.energy` includes all ordered pairs. At exponent 1, `dist(x,x)^1=0`, so it equals the manuscript's off-diagonal convention. The factor is **4** with ordinary `dt`; if one accidentally inserts the probability measure `dt/2`, it becomes **8**. Keep this test close to the theorem. The universal `StolarskyIdentity` should be proved independently of `DiamondStolarsky`, thereby also supplying a useful theorem for arbitrary configurations.

**Concrete index bridge.** `point N φ` is indexed by `PointIndex N`, not `Fin N`. From `ConstructionFacts` derive `Fintype.card (PointIndex N)=N` using the population sum. Construct `e : PointIndex N ≃ Fin N` with `Fintype.equivFinOfCardEq`. Prove `capError (point N φ)` equals `capError (point N φ ∘ e.symm)` pointwise, using finite-sum reindexing and cardinality equality; hence the discrepancies are equal. Likewise prove `energy (point N φ) 1 = energy (point N φ ∘ e.symm) 1`. Apply `StolarskyIdentity` to the relabeled map and multiply by `N²`; unfold `deficit` and `diamondEnergy` to obtain `DiamondStolarsky`. This bridge should be an actual theorem rather than an additional assumption in the final exported result.

**Lower bound.** `BeckLowerBound` is the exact-kind external theorem needed for the manuscript's `cN^-3/4` lower estimate; its premise `Function.Injective X` makes explicit that Beck discusses `n`-element sets. A formal proof is a substantial harmonic/discrepancy argument, not an algebraic consequence of Stolarsky. One may instead prove a universal Wagner-type deficit lower bound `b n^(1/2)≤(4/3)n²-energy X 1` and use Stolarsky to derive Beck's numerical rate, checking whether the source bound permits repeated labels. In either route, prove `Function.Injective (point N φ)` from `ConstructionFacts` and transfer it under the index equivalence. Do not instantiate a distinct-set theorem with a possibly repeated labeling.

**Asymptotic assembly and checks.** `MainTheorem 1` gives `deficit 1 N φ≤C N^(1/2)` for every `N≥4` in the new scaffold. `DiamondStolarsky` gives `D²≤(C/4)N^(-3/2)`. From `capDiscrepancySq_nonneg` obtain `D=√D²≥0`; use positive `N`, `Real.sqrt_le_iff`, and `Real.rpow_mul` to derive `D≤(√C/2)N^-3/4`. Apply Beck for the other inequality. The constant must be independent of both `N` and `φ`, as `CapDiscrepancyCorollary` quantifies over arbitrary phases. The cap result depends on the main energy theorem, geometric cardinality/injectivity, Stolarsky, and Beck; none is supplied merely by importing this module. Build the module after each identity and audit for forbidden proof shortcuts.
