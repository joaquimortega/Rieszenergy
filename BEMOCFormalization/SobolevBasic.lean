import BEMOCFormalization.Sobolev
import BEMOCFormalization.SurfaceMeasure

open scoped BigOperators
open MeasureTheory
namespace BEMOC.Definitive

/-- The zero function satisfies the spectral summability guard and norm bound. -/
theorem zero_mem_sobolev_unit_ball (Y : HarmonicBasis) (s : ℝ) :
    SobolevUnitBall Y s (0 : C(Sphere, ℝ)) := by
  have hterm : sobolevNormTerm Y s (0 : C(Sphere, ℝ)) = 0 := by
    funext ℓ
    simp [sobolevNormTerm, harmonicCoefficient]
  constructor
  · simpa [hterm] using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
  · simp [hterm]

/-- The zero test function has zero quadrature error. -/
theorem quadratureError_zero {ι : Type} [Fintype ι] (X : ι → Sphere) :
    quadratureError X (0 : C(Sphere, ℝ)) = 0 := by
  simp [quadratureError]

/-- Zero belongs to the defining set of the spectral worst-case error. -/
theorem sobolev_error_set_nonempty {ι : Type} [Fintype ι]
    (Y : HarmonicBasis) (s : ℝ) (X : ι → Sphere) :
    Set.Nonempty {e : ℝ | ∃ f : C(Sphere, ℝ), SobolevUnitBall Y s f ∧
      e = |quadratureError X f|} := by
  refine ⟨0, (0 : C(Sphere, ℝ)), zero_mem_sobolev_unit_ball Y s, ?_⟩
  simp [quadratureError_zero]

/-- The embedding bound controls every quadrature error by twice its constant. -/
theorem quadratureError_abs_le_two_mul {ι : Type} [Fintype ι] [Nonempty ι]
    (X : ι → Sphere) (f : C(Sphere, ℝ)) (K : ℝ)
    (hK : ∀ x : Sphere, |f x| ≤ K) :
    |quadratureError X f| ≤ 2 * K := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsumUpper : (∑ i : ι, f (X i)) ≤ (Fintype.card ι : ℝ) * K := by
    calc
      _ ≤ ∑ _i : ι, K := Finset.sum_le_sum (fun i _ ↦ (abs_le.mp (hK (X i))).2)
      _ = (Fintype.card ι : ℝ) * K := by simp
  have hsumLower : -(Fintype.card ι : ℝ) * K ≤ (∑ i : ι, f (X i)) := by
    calc
      _ = ∑ _i : ι, -K := by simp
      _ ≤ ∑ i : ι, f (X i) := Finset.sum_le_sum (fun i _ ↦ (abs_le.mp (hK (X i))).1)
  have hmeanUpper : (∑ i : ι, f (X i)) / Fintype.card ι ≤ K := by
    apply (div_le_iff₀ hc).2
    linarith
  have hmeanLower : -K ≤ (∑ i : ι, f (X i)) / Fintype.card ι := by
    apply (le_div_iff₀ hc).2
    linarith
  have hint : Integrable (fun x : Sphere ↦ f x) sigma := by
    rw [← integrableOn_univ]
    apply Measure.integrableOn_of_bounded (measure_ne_top sigma Set.univ)
      f.continuous.aestronglyMeasurable
    filter_upwards with x
    simpa only [Real.norm_eq_abs] using hK x
  have hintUpper : (∫ x : Sphere, f x ∂sigma) ≤ K := by
    calc
      _ ≤ ∫ _x : Sphere, K ∂sigma := integral_mono hint (integrable_const K)
        (fun x ↦ (abs_le.mp (hK x)).2)
      _ = K := by simp
  have hintLower : -K ≤ (∫ x : Sphere, f x ∂sigma) := by
    calc
      _ = ∫ _x : Sphere, -K ∂sigma := by simp
      _ ≤ ∫ x : Sphere, f x ∂sigma := integral_mono (integrable_const (-K)) hint
        (fun x ↦ (abs_le.mp (hK x)).1)
  unfold quadratureError
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The defining error set is bounded above whenever the embedding contract holds. -/
theorem sobolev_error_set_bddAbove {ι : Type} [Fintype ι] [Nonempty ι]
    (Y : HarmonicBasis) (s : ℝ) (X : ι → Sphere)
    (hemb : SobolevEmbedding Y s) :
    BddAbove {e : ℝ | ∃ f : C(Sphere, ℝ), SobolevUnitBall Y s f ∧
      e = |quadratureError X f|} := by
  obtain ⟨K, _, hK⟩ := hemb
  refine ⟨2 * K, ?_⟩
  rintro e ⟨f, hf, rfl⟩
  exact quadratureError_abs_le_two_mul X f K (hK f hf)

/-- The spectral worst-case error is nonnegative under embedding. -/
theorem sobolevWCE_nonneg {ι : Type} [Fintype ι] [Nonempty ι]
    (Y : HarmonicBasis) (s : ℝ) (X : ι → Sphere)
    (hemb : SobolevEmbedding Y s) :
    0 ≤ sobolevWCE Y s X := by
  unfold sobolevWCE
  exact le_csSup (sobolev_error_set_bddAbove Y s X hemb)
    (show (0 : ℝ) ∈ {e : ℝ | ∃ f : C(Sphere, ℝ),
      SobolevUnitBall Y s f ∧ e = |quadratureError X f|} from
      ⟨0, zero_mem_sobolev_unit_ball Y s, by simp [quadratureError_zero]⟩)

/-- Every admissible test function's error lies below the actual supremum. -/
theorem quadratureError_abs_le_sobolevWCE {ι : Type} [Fintype ι] [Nonempty ι]
    (Y : HarmonicBasis) (s : ℝ) (X : ι → Sphere)
    (hemb : SobolevEmbedding Y s) (f : C(Sphere, ℝ))
    (hf : SobolevUnitBall Y s f) :
    |quadratureError X f| ≤ sobolevWCE Y s X := by
  unfold sobolevWCE
  exact le_csSup (sobolev_error_set_bddAbove Y s X hemb)
    ⟨f, hf, rfl⟩

/-- A uniform finite bound on the spectral worst-case error. -/
theorem sobolevWCE_le_two_mul {ι : Type} [Fintype ι] [Nonempty ι]
    (Y : HarmonicBasis) (s : ℝ) (X : ι → Sphere) (K : ℝ)
    (hK : ∀ f : C(Sphere, ℝ), SobolevUnitBall Y s f →
      ∀ x : Sphere, |f x| ≤ K) :
    sobolevWCE Y s X ≤ 2 * K := by
  unfold sobolevWCE
  apply csSup_le (sobolev_error_set_nonempty Y s X)
  rintro e ⟨f, hf, rfl⟩
  exact quadratureError_abs_le_two_mul X f K (hK f hf)

end BEMOC.Definitive
