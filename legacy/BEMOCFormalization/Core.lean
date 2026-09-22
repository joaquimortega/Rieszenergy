import BEMOCFormalization.EulerSmooth
import BEMOCFormalization.EulerPower
import BEMOCFormalization.CircleEndpoint
import BEMOCFormalization.PowerZeta
import BEMOCFormalization.PowerZetaContinuation
import BEMOCFormalization.EndpointRegularity
import BEMOCFormalization.EndpointResidualData
import BEMOCFormalization.CircleFourier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# BEMOC negative Riesz energies: formalization interface

This file formalizes the discrete parameters and the logical architecture of
the main theorem in `BEMOCRieszEnergies.tex`.  Deep analytic estimates are
isolated below as named structures, so no mathematical assumption is hidden.
-/

open scoped BigOperators Pointwise

namespace BEMOC

/-! ## Geometric energy -/

/-- The ambient Euclidean space containing the two-sphere. -/
abbrev Ambient := EuclideanSpace ℝ (Fin 3)

/-- The unit two-sphere as a metric-space subtype. -/
abbrev Sphere := Metric.sphere (0 : Ambient) 1

/-- A point of height `z` and azimuth `θ` before packaging it as an element
of the sphere. -/
noncomputable def parallelVector (z θ : ℝ) : Ambient :=
  !₂[Real.sqrt (1 - z ^ 2) * Real.cos θ,
     Real.sqrt (1 - z ^ 2) * Real.sin θ,
     z]

theorem parallelVector_mem_sphere {z θ : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    parallelVector z θ ∈ Metric.sphere (0 : Ambient) 1 := by
  rw [EuclideanSpace.sphere_zero_eq 1 (by positivity)]
  have hrad : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  simp [parallelVector, Fin.sum_univ_succ, Real.sq_sqrt hrad]
  ring_nf
  rw [Real.sq_sqrt hrad]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The standard parametrization of a spherical parallel. -/
noncomputable def parallelPoint (z θ : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) : Sphere :=
  ⟨parallelVector z θ, parallelVector_mem_sphere hz⟩

@[simp] theorem parallelPoint_height (z θ : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    (parallelPoint z θ hz : Ambient) 2 = z := by
  rfl

/-- An equally spaced polygon on the parallel of height `z`, with arbitrary
azimuthal phase `φ`. -/
noncomputable def parallelPolygon (w : ℕ) (z φ : ℝ)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) : Fin w → Sphere :=
  fun k ↦ parallelPoint z (φ + 2 * Real.pi * (k : ℝ) / w) hz

@[simp] theorem parallelPolygon_height (w : ℕ) (z φ : ℝ)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) (k : Fin w) :
    (parallelPolygon w z φ hz k : Ambient) 2 = z := by
  rfl

/-- Squared chordal distance between two points on spherical parallels. -/
theorem parallelPoint_dist_sq {s t θ φ : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    dist (parallelPoint s θ hs) (parallelPoint t φ ht) ^ 2 =
      2 - 2 * s * t -
        2 * Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * Real.cos (θ - φ) := by
  have hrs : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hrt : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  change dist (parallelVector s θ) (parallelVector t φ) ^ 2 = _
  rw [EuclideanSpace.dist_eq]
  have hsum : 0 ≤ ∑ i : Fin 3,
      dist (parallelVector s θ i) (parallelVector t φ i) ^ 2 := by positivity
  rw [Real.sq_sqrt hsum]
  simp [parallelPoint, parallelVector, Fin.sum_univ_succ, Real.dist_eq,
    sq_abs, Real.sq_sqrt hrs, Real.sq_sqrt hrt, Real.cos_sub]
  ring_nf
  rw [Real.sq_sqrt hrs, Real.sq_sqrt hrt]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]

theorem parallelPoint_same_height_dist_sq {z θ φ : ℝ}
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    dist (parallelPoint z θ hz) (parallelPoint z φ hz) ^ 2 =
      2 * (1 - z ^ 2) * (1 - Real.cos (θ - φ)) := by
  rw [parallelPoint_dist_sq hz hz]
  have hrad : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  ring_nf
  rw [Real.sq_sqrt hrad]
  ring

/-- Chord length on a parallel is its Euclidean radius times the unit-circle
chord at the angular difference. -/
theorem parallelPoint_same_height_dist_eq_radius_mul_abs_sin
    {z θ φ : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    dist (parallelPoint z θ hz) (parallelPoint z φ hz) =
      Real.sqrt (1 - z ^ 2) * |2 * Real.sin ((θ - φ) / 2)| := by
  have hrad : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hsq := parallelPoint_same_height_dist_sq (θ := θ) (φ := φ) hz
  have htrig : 2 * (1 - Real.cos (θ - φ)) =
      (2 * Real.sin ((θ - φ) / 2)) ^ 2 := by
    have hc : Real.cos (θ - φ) =
        2 * Real.cos ((θ - φ) / 2) ^ 2 - 1 := by
      calc
        Real.cos (θ - φ) = Real.cos (2 * ((θ - φ) / 2)) := by ring_nf
        _ = _ := Real.cos_two_mul _
    rw [hc]
    nlinarith [Real.sin_sq_add_cos_sq ((θ - φ) / 2)]
  have hsquares :
      dist (parallelPoint z θ hz) (parallelPoint z φ hz) ^ 2 =
        (Real.sqrt (1 - z ^ 2) * |2 * Real.sin ((θ - φ) / 2)|) ^ 2 := by
    rw [hsq, mul_pow, sq_abs, Real.sq_sqrt hrad]
    nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsquares) with h | h
  · exact h
  · have hl : 0 ≤ dist (parallelPoint z θ hz) (parallelPoint z φ hz) := dist_nonneg
    have hr : 0 ≤ Real.sqrt (1 - z ^ 2) *
        |2 * Real.sin ((θ - φ) / 2)| :=
      mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    linarith

/-! ### Circle scalar profile -/

/-- Chord length to the power `α`, in unit-period angular coordinates. -/
noncomputable def circleProfile (α x : ℝ) : ℝ :=
  (2 * Real.sin (Real.pi * x)) ^ α

/-- Chord-power sum from one vertex of a regular `w`-gon. -/
noncomputable def circleChordPowerSum (α : ℝ) (w : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 w, circleProfile α ((k : ℝ) / (w : ℝ))

/-- Ordered-pair negative Riesz energy of an `N`-point configuration. -/
noncomputable def rieszEnergy {N : ℕ} (X : Fin N → Sphere) (α : ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, dist (X i) (X j) ^ α

/-- Ordered-pair Riesz energy with an arbitrary finite label type. -/
noncomputable def finiteRieszEnergy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → Sphere) (α : ℝ) : ℝ :=
  ∑ i : ι, ∑ j ∈ Finset.univ.erase i, dist (X i) (X j) ^ α

theorem rieszEnergy_nonneg {N : ℕ} (X : Fin N → Sphere) (α : ℝ) :
    0 ≤ rieszEnergy X α := by
  unfold rieszEnergy
  positivity

theorem finiteRieszEnergy_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → Sphere) (α : ℝ) : 0 ≤ finiteRieszEnergy X α := by
  unfold finiteRieszEnergy
  positivity

/-- Ordered-pair energy is invariant under a relabeling equivalence. -/
theorem finiteRieszEnergy_comp_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (X : κ → Sphere) (α : ℝ) :
    finiteRieszEnergy (X ∘ e) α = finiteRieszEnergy X α := by
  classical
  unfold finiteRieszEnergy
  apply Fintype.sum_equiv e
  intro i
  apply Finset.sum_bij (fun j _ ↦ e j)
  · intro j hj
    exact Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_erase.mp hj).1 (e.injective h),
      Finset.mem_univ _⟩
  · intro a₁ ha₁ a₂ ha₂ h
    exact e.injective h
  · intro b hb
    refine ⟨e.symm b, ?_, by simp⟩
    exact Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_erase.mp hb).1
      (by simpa using congrArg e h), Finset.mem_univ _⟩
  · intro j hj
    rfl

@[simp] theorem rieszEnergy_empty (X : Fin 0 → Sphere) (α : ℝ) :
    rieszEnergy X α = 0 := by
  simp [rieszEnergy]

/-- A sequence of concrete spherical configurations. -/
structure ConfigurationSequence where
  points : ∀ N : ℕ, Fin N → Sphere

/-- The energy function associated with a configuration sequence. -/
noncomputable def ConfigurationSequence.energy
    (X : ConfigurationSequence) (α : ℝ) (N : ℕ) : ℝ :=
  rieszEnergy (X.points N) α

/-- Data for one occupied parallel. -/
structure OccupiedRing where
  population : ℕ
  height : ℝ
  height_mem : height ∈ Set.Icc (-1 : ℝ) 1
  phase : ℝ

/-- Euclidean radius of the parallel supporting an occupied ring. -/
noncomputable def OccupiedRing.radius (R : OccupiedRing) : ℝ :=
  Real.sqrt (1 - R.height ^ 2)

theorem OccupiedRing.radius_nonneg (R : OccupiedRing) :
    0 ≤ R.radius := Real.sqrt_nonneg _

/-- The polygon carried by an occupied ring. -/
noncomputable def OccupiedRing.point (R : OccupiedRing) : Fin R.population → Sphere :=
  parallelPolygon R.population R.height R.phase R.height_mem

/-- Labels for all points in a finite family of occupied rings. -/
abbrev RingPointIndex {κ : Type*} [Fintype κ] (R : κ → OccupiedRing) :=
  Σ k, Fin (R k).population

theorem card_ringPointIndex {κ : Type*} [Fintype κ] (R : κ → OccupiedRing) :
    Fintype.card (RingPointIndex R) = ∑ k, (R k).population := by
  simp [RingPointIndex, Fintype.card_sigma]

/-- Concrete point map of a finite family of occupied rings. -/
noncomputable def ringConfiguration {κ : Type*} [Fintype κ]
    (R : κ → OccupiedRing) : RingPointIndex R → Sphere :=
  fun x ↦ (R x.1).point x.2

/-- A ring configuration relabeled by `Fin N` once its population sum is
known to equal `N`. -/
noncomputable def finRingConfiguration {κ : Type*} [Fintype κ]
    (R : κ → OccupiedRing) (N : ℕ) (hN : ∑ k, (R k).population = N) :
    Fin N → Sphere :=
  let e : RingPointIndex R ≃ Fin N :=
    Fintype.equivFinOfCardEq ((card_ringPointIndex R).trans hN)
  fun i ↦ ringConfiguration R (e.symm i)

/-- Relabeling a ring family by `Fin N` preserves its ordered-pair energy. -/
theorem rieszEnergy_finRingConfiguration {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : κ → OccupiedRing) (N : ℕ) (hN : ∑ k, (R k).population = N)
    (α : ℝ) :
    rieszEnergy (finRingConfiguration R N hN) α =
      finiteRieszEnergy (ringConfiguration R) α := by
  classical
  let e : RingPointIndex R ≃ Fin N :=
    Fintype.equivFinOfCardEq ((card_ringPointIndex R).trans hN)
  change finiteRieszEnergy (ringConfiguration R ∘ e.symm) α =
    finiteRieszEnergy (ringConfiguration R) α
  exact finiteRieszEnergy_comp_equiv e.symm (ringConfiguration R) α

/-- A family of finite ring configurations with a certified total
population at every `N`. -/
structure RingConstructionSequence where
  ringCount : ℕ → ℕ
  rings : ∀ N, Fin (ringCount N) → OccupiedRing
  totalPopulation : ∀ N, ∑ k, (rings N k).population = N

/-- Forget the ring decomposition and retain the resulting `N` spherical
points. -/
noncomputable def RingConstructionSequence.toConfigurationSequence
    (R : RingConstructionSequence) : ConfigurationSequence where
  points N := finRingConfiguration (R.rings N) N (R.totalPopulation N)

@[simp] theorem ringConfiguration_height {κ : Type*} [Fintype κ]
    (R : κ → OccupiedRing) (x : RingPointIndex R) :
    (ringConfiguration R x : Ambient) 2 = (R x.1).height := by
  rfl

/-- Contribution of ordered pairs lying on the same occupied ring. -/
noncomputable def withinRingEnergy {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : κ → OccupiedRing) (α : ℝ) : ℝ :=
  ∑ x : RingPointIndex R, ∑ y ∈ Finset.univ.erase x,
    if x.1 = y.1 then dist (ringConfiguration R x) (ringConfiguration R y) ^ α else 0

/-- Ordered-pair energy internal to one occupied regular polygon. -/
noncomputable def singleRingDiscreteEnergy (R : OccupiedRing) (α : ℝ) : ℝ :=
  finiteRieszEnergy R.point α

/-- Contribution of ordered pairs lying on different occupied rings. -/
noncomputable def crossRingEnergy {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : κ → OccupiedRing) (α : ℝ) : ℝ :=
  ∑ x : RingPointIndex R, ∑ y ∈ Finset.univ.erase x,
    if x.1 ≠ y.1 then dist (ringConfiguration R x) (ringConfiguration R y) ^ α else 0

/-- The same-ring part of a ring configuration is the sum of the individual
regular-polygon energies. -/
theorem withinRingEnergy_eq_sum_single {κ : Type*} [Fintype κ]
    [DecidableEq κ] (R : κ → OccupiedRing) {α : ℝ} (hα : 0 < α) :
    withinRingEnergy R α = ∑ p, singleRingDiscreteEnergy (R p) α := by
  classical
  unfold withinRingEnergy singleRingDiscreteEnergy finiteRieszEnergy
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro i hi
  have hleft :
      (∑ y ∈ Finset.univ.erase (⟨p, i⟩ : RingPointIndex R),
        if p = y.1 then
          dist (ringConfiguration R ⟨p, i⟩) (ringConfiguration R y) ^ α else 0) =
      ∑ y : RingPointIndex R, if p = y.1 then
        dist (ringConfiguration R ⟨p, i⟩) (ringConfiguration R y) ^ α else 0 := by
    rw [← Finset.sum_erase_add _ _
      (Finset.mem_univ (⟨p, i⟩ : RingPointIndex R))]
    simp [Real.zero_rpow hα.ne']
  rw [hleft, Fintype.sum_sigma]
  have hright :
      (∑ j ∈ Finset.univ.erase i,
        dist ((R p).point i) ((R p).point j) ^ α) =
      ∑ j, dist ((R p).point i) ((R p).point j) ^ α := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp [Real.zero_rpow hα.ne']
  rw [hright]
  simp only [ringConfiguration]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q hq hqp
    have hpq : p ≠ q := fun h => hqp h.symm
    simp [hpq]
  · simp

/-! ### Exact discrete one-ring circle formula -/

/-- Chord length from vertex zero to vertex `k`, with the radius of the
parallel factored out. -/
theorem dist_ringPoint_zero_eq (R : OccupiedRing) {w : ℕ}
    (hw : 0 < w) (hpop : R.population = w) (k : Fin w) :
    dist
        (R.point (hpop ▸ (⟨0, hw⟩ : Fin w)))
        (R.point (hpop ▸ k)) =
      R.radius * (2 * Real.sin (Real.pi * (k : ℝ) / (w : ℝ))) := by
  subst w
  simp only [OccupiedRing.point, parallelPolygon, Nat.cast_zero,
    mul_zero, zero_div, add_zero]
  have hwR : 0 < (R.population : ℝ) := by exact_mod_cast hw
  have hk0 : 0 ≤ Real.pi * (k : ℝ) / (R.population : ℝ) := by positivity
  have hkle : Real.pi * (k : ℝ) / (R.population : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hwR]
    have hklt : (k : ℝ) < (R.population : ℝ) := by exact_mod_cast k.isLt
    nlinarith [Real.pi_pos]
  have hsin : 0 ≤ Real.sin
      (Real.pi * (k : ℝ) / (R.population : ℝ)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hk0 hkle
  rw [parallelPoint_same_height_dist_eq_radius_mul_abs_sin]
  rw [show (R.phase -
      (R.phase + 2 * Real.pi * (k : ℝ) / (R.population : ℝ))) / 2 =
      -(Real.pi * (k : ℝ) / (R.population : ℝ)) by ring,
    Real.sin_neg, mul_neg, abs_neg,
    abs_of_nonneg (mul_nonneg (by norm_num) hsin)]
  rfl

theorem dist_ringPoint_zero_rpow (R : OccupiedRing) {w : ℕ}
    (hw : 0 < w) (hpop : R.population = w) (k : Fin w) (α : ℝ) :
    dist
        (R.point (hpop ▸ (⟨0, hw⟩ : Fin w)))
        (R.point (hpop ▸ k)) ^ α =
      R.radius ^ α * circleProfile α ((k : ℝ) / (w : ℝ)) := by
  rw [dist_ringPoint_zero_eq R hw hpop k]
  have hwR : 0 < (w : ℝ) := by exact_mod_cast hw
  have hk0 : 0 ≤ Real.pi * (k : ℝ) / (w : ℝ) := by positivity
  have hkle : Real.pi * (k : ℝ) / (w : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hwR]
    have hklt : (k : ℝ) < (w : ℝ) := by exact_mod_cast k.isLt
    nlinarith [Real.pi_pos]
  have hchord : 0 ≤ 2 * Real.sin (Real.pi * (k : ℝ) / (w : ℝ)) :=
    mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_nonneg_of_le_pi hk0 hkle)
  rw [Real.mul_rpow R.radius_nonneg hchord]
  unfold circleProfile
  congr 2
  ring_nf

/-- The ordered energy seen from vertex zero is the radius-scaled circle
chord sum. -/
theorem ringPoint_zero_inner_energy (R : OccupiedRing) {α : ℝ}
    (hpop : 0 < R.population) :
    (∑ y ∈ Finset.univ.erase (⟨0, hpop⟩ : Fin R.population),
        dist (R.point (⟨0, hpop⟩ : Fin R.population)) (R.point y) ^ α) =
      R.radius ^ α * circleChordPowerSum α R.population := by
  classical
  rw [circleChordPowerSum, Finset.mul_sum]
  refine Finset.sum_bij
    (s := Finset.univ.erase (⟨0, hpop⟩ : Fin R.population))
    (t := Finset.Ico 1 R.population)
    (f := fun y : Fin R.population ↦
      dist (R.point (⟨0, hpop⟩ : Fin R.population)) (R.point y) ^ α)
    (g := fun i : ℕ ↦
      R.radius ^ α * circleProfile α ((i : ℝ) / (R.population : ℝ)))
    (fun y _ ↦ (y : ℕ)) ?_ ?_ ?_ ?_
  · intro y hy
    have hyne : y ≠ (⟨0, hpop⟩ : Fin R.population) :=
      (Finset.mem_erase.mp hy).1
    have hypos : 1 ≤ (y : ℕ) := by
      have : (y : ℕ) ≠ 0 := by
        intro hz
        apply hyne
        exact Fin.ext hz
      omega
    exact Finset.mem_Ico.mpr ⟨hypos, y.isLt⟩
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro k hk
    have hk' := Finset.mem_Ico.mp hk
    let y : Fin R.population := ⟨k, hk'.2⟩
    refine ⟨y, ?_, rfl⟩
    exact Finset.mem_erase.mpr ⟨by
      intro heq
      have : k = 0 := congrArg Fin.val heq
      omega, Finset.mem_univ y⟩
  · intro y hy
    simpa only using dist_ringPoint_zero_rpow R hpop rfl y α

/-- Cyclic translation of both polygon labels preserves their distance. -/
theorem dist_ringPoint_add_eq_dist_zero (R : OccupiedRing)
    (hpop : 0 < R.population) (i k : Fin R.population) :
    dist (R.point i) (R.point (i + k)) =
      dist (R.point (⟨0, hpop⟩ : Fin R.population)) (R.point k) := by
  have hwR : 0 < (R.population : ℝ) := by exact_mod_cast hpop
  have hcos :
      Real.cos
          ((R.phase + 2 * Real.pi * (i : ℝ) / (R.population : ℝ)) -
            (R.phase + 2 * Real.pi * ((i + k : Fin R.population) : ℝ) /
              (R.population : ℝ))) =
        Real.cos
          (R.phase -
            (R.phase + 2 * Real.pi * (k : ℝ) / (R.population : ℝ))) := by
    rw [Fin.val_add_eq_ite]
    split_ifs with hwrap
    · have hcast :
          (((i : ℕ) + (k : ℕ) - R.population : ℕ) : ℝ) =
            (i : ℝ) + (k : ℝ) - (R.population : ℝ) := by
        rw [Nat.cast_sub hwrap]
        push_cast
        rfl
      rw [hcast]
      have hleft :
          (R.phase + 2 * Real.pi * (i : ℝ) / (R.population : ℝ)) -
              (R.phase + 2 * Real.pi *
                ((i : ℝ) + (k : ℝ) - (R.population : ℝ)) /
                  (R.population : ℝ)) =
            2 * Real.pi -
              2 * Real.pi * (k : ℝ) / (R.population : ℝ) := by
        field_simp [hwR.ne']
        ring
      have hright :
          R.phase - (R.phase + 2 * Real.pi * (k : ℝ) /
            (R.population : ℝ)) =
            -(2 * Real.pi * (k : ℝ) / (R.population : ℝ)) := by ring
      rw [hleft, Real.cos_two_pi_sub, hright, Real.cos_neg]
    · have hcast : ((((i : ℕ) + (k : ℕ) : ℕ) : ℝ)) =
          (i : ℝ) + (k : ℝ) := by push_cast; rfl
      rw [hcast]
      have hleft :
          (R.phase + 2 * Real.pi * (i : ℝ) / (R.population : ℝ)) -
              (R.phase + 2 * Real.pi * ((i : ℝ) + (k : ℝ)) /
                (R.population : ℝ)) =
            -(2 * Real.pi * (k : ℝ) / (R.population : ℝ)) := by ring
      have hright :
          R.phase - (R.phase + 2 * Real.pi * (k : ℝ) /
            (R.population : ℝ)) =
            -(2 * Real.pi * (k : ℝ) / (R.population : ℝ)) := by ring
      rw [hleft, hright]
  have hsquare :
      dist (R.point i) (R.point (i + k)) ^ 2 =
        dist (R.point (⟨0, hpop⟩ : Fin R.population)) (R.point k) ^ 2 := by
    simp only [OccupiedRing.point, parallelPolygon]
    rw [parallelPoint_same_height_dist_sq,
      parallelPoint_same_height_dist_sq, hcos]
    simp
  have hdist₁ : 0 ≤ dist (R.point i) (R.point (i + k)) := dist_nonneg
  have hdist₂ : 0 ≤
      dist (R.point (⟨0, hpop⟩ : Fin R.population)) (R.point k) := dist_nonneg
  nlinarith

/-- Every vertex of the regular polygon sees the same radius-scaled circle
sum. -/
theorem ringPoint_inner_energy (R : OccupiedRing) {α : ℝ}
    (hpop : 0 < R.population) (i : Fin R.population) :
    (∑ y ∈ Finset.univ.erase i, dist (R.point i) (R.point y) ^ α) =
      R.radius ^ α * circleChordPowerSum α R.population := by
  letI : NeZero R.population := ⟨hpop.ne'⟩
  let e : Fin R.population ≃ Fin R.population := Equiv.addLeft i
  have htranslate :
      (∑ k ∈ Finset.univ.erase (⟨0, hpop⟩ : Fin R.population),
          dist (R.point (⟨0, hpop⟩ : Fin R.population)) (R.point k) ^ α) =
        ∑ y ∈ Finset.univ.erase i, dist (R.point i) (R.point y) ^ α := by
    classical
    refine Finset.sum_bij
      (s := Finset.univ.erase (⟨0, hpop⟩ : Fin R.population))
      (t := Finset.univ.erase i)
      (f := fun k ↦
        dist (R.point (⟨0, hpop⟩ : Fin R.population)) (R.point k) ^ α)
      (g := fun y ↦ dist (R.point i) (R.point y) ^ α)
      (fun k _ ↦ e k) ?_ ?_ ?_ ?_
    · intro k hk
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro heq
      have hkzero : k = (0 : Fin R.population) := by
        apply e.injective
        simpa [e] using heq
      exact (Finset.mem_erase.mp hk).1 hkzero
    · intro a ha b hb hab
      exact e.injective hab
    · intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro hzero
      have hyi : y = i := by
        rw [← e.apply_symm_apply y, hzero]
        simp [e]
      exact (Finset.mem_erase.mp hy).1 hyi
    · intro k hk
      have hdist := dist_ringPoint_add_eq_dist_zero R hpop i k
      simpa [e] using congrArg (fun x : ℝ ↦ x ^ α) hdist.symm
  rw [← htranslate]
  exact ringPoint_zero_inner_energy R hpop

/-- Exact discrete one-ring formula, including the empty population. -/
theorem singleRingDiscreteEnergy_eq_circle (R : OccupiedRing) (α : ℝ) :
    singleRingDiscreteEnergy R α =
      R.radius ^ α * R.population * circleChordPowerSum α R.population := by
  classical
  by_cases hpop : R.population = 0
  · have huniv : (Finset.univ : Finset (Fin R.population)) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro x hx
      have hxlt := x.isLt
      omega
    unfold singleRingDiscreteEnergy finiteRieszEnergy
    rw [huniv]
    simp [hpop]
  have hpoppos : 0 < R.population := Nat.pos_of_ne_zero hpop
  unfold singleRingDiscreteEnergy finiteRieszEnergy
  simp_rw [ringPoint_inner_energy R hpoppos]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring
theorem ring_energy_eq_within_add_cross {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : κ → OccupiedRing) (α : ℝ) :
    finiteRieszEnergy (ringConfiguration R) α =
      withinRingEnergy R α + crossRingEnergy R α := by
  classical
  unfold finiteRieszEnergy withinRingEnergy crossRingEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : x.1 = y.1 <;> simp [h]

/-- Pure algebra behind the exact three-term decomposition in the paper. -/
theorem insert_continuous_ring_energy
    (I pointEnergy ringEnergy selfContinuous selfDiscrete
      crossContinuous crossDiscrete : ℝ)
    (hPoint : pointEnergy = selfDiscrete + crossDiscrete)
    (hRing : ringEnergy = selfContinuous + crossContinuous) :
    I - pointEnergy =
      (I - ringEnergy) + (selfContinuous - selfDiscrete) +
        (crossContinuous - crossDiscrete) := by
  rw [hPoint, hRing]
  ring

/-! ### General endpoint Euler--Maclaurin statement -/

open Filter
open scoped Topology Interval

/-- The normalized angular moment `J_α` in Lemma 3.1. -/
noncomputable def circleAngularMoment (α : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, circleProfile α x

/-- Continuous-minus-discrete angular self-deficit of a regular `w`-gon
on the unit circle.  Multiplication by the supporting parallel's
`radius ^ α` gives the corresponding one-ring deficit. -/
noncomputable def circleSelfDeficit (α : ℝ) (w : ℕ) : ℝ :=
  (w : ℝ) ^ 2 * circleAngularMoment α -
    (w : ℝ) * circleChordPowerSum α w

/-- Real part of Mathlib's analytically continued Riemann zeta function. -/
noncomputable def realRiemannZeta (s : ℝ) : ℝ :=
  (riemannZeta (s : ℂ)).re

/-- Exact filter statement of equation (3.1) in `BEMOCRieszEnergies.tex`. -/
def HasCircleEulerMaclaurin (α : ℝ) : Prop :=
  Tendsto
    (fun w : ℕ =>
      (w : ℝ) ^ α *
        (circleChordPowerSum α w - (w : ℝ) * circleAngularMoment α))
    atTop
    (𝓝 (2 * (2 * Real.pi) ^ α * realRiemannZeta (-α)))

@[simp] theorem circleChordPowerSum_zero (α : ℝ) :
    circleChordPowerSum α 0 = 0 := by
  simp [circleChordPowerSum]

@[simp] theorem circleChordPowerSum_one (α : ℝ) :
    circleChordPowerSum α 1 = 0 := by
  simp [circleChordPowerSum]

/-! The functional equation below is the checked bridge from the absolutely
convergent zeta series at `1 + α` to the coefficient at `-α`. -/

theorem riemannZeta_neg_real_functional_equation {α : ℝ} (hα : 0 < α) :
    riemannZeta (-(α : ℂ)) =
      2 * (2 * (Real.pi : ℂ)) ^ (-((1 + α : ℝ) : ℂ)) *
        Complex.Gamma ((1 + α : ℝ) : ℂ) *
        Complex.cos ((Real.pi : ℂ) * ((1 + α : ℝ) : ℂ) / 2) *
        riemannZeta ((1 + α : ℝ) : ℂ) := by
  have hs (n : ℕ) : ((1 + α : ℝ) : ℂ) ≠ -(n : ℂ) := by
    intro hn
    have hr := congrArg Complex.re hn
    norm_num at hr
    linarith
  have hs1 : ((1 + α : ℝ) : ℂ) ≠ 1 := by
    intro hn
    have hr := congrArg Complex.re hn
    norm_num at hr
    linarith
  have harg : (1 : ℂ) - ((1 + α : ℝ) : ℂ) = -(α : ℂ) := by
    push_cast
    ring
  rw [← harg]
  exact riemannZeta_one_sub (s := ((1 + α : ℝ) : ℂ)) hs hs1

theorem riemannZeta_one_add_real_eq_ofReal_tsum {α : ℝ} (hα : 0 < α) :
    riemannZeta ((1 + α : ℝ) : ℂ) =
      ((∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + α)) : ℝ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow]
  · rw [Complex.ofReal_tsum]
    congr 1
    funext n
    rw [Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_cpow (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]
    norm_num
  · norm_num
    linarith

theorem riemannZeta_neg_real_eq_ofReal {α : ℝ} (hα : 0 < α) :
    riemannZeta (-(α : ℂ)) =
      ((2 * (2 * Real.pi) ^ (-(1 + α)) * Real.Gamma (1 + α) *
          Real.cos (Real.pi * (1 + α) / 2) *
          ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + α)) : ℝ) := by
  rw [riemannZeta_neg_real_functional_equation hα,
    riemannZeta_one_add_real_eq_ofReal_tsum hα]
  rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl]
  rw [show -((1 + α : ℝ) : ℂ) = ((-(1 + α) : ℝ) : ℂ) by push_cast; rfl]
  rw [show (Real.pi : ℂ) * ((1 + α : ℝ) : ℂ) / 2 =
      ((Real.pi * (1 + α) / 2 : ℝ) : ℂ) by push_cast; rfl]
  rw [← Complex.ofReal_cpow (by positivity : 0 ≤ 2 * Real.pi),
    Complex.Gamma_ofReal, ← Complex.ofReal_cos]
  norm_cast

theorem realRiemannZeta_neg_eq_functional_equation {α : ℝ} (hα : 0 < α) :
    realRiemannZeta (-α) =
      2 * (2 * Real.pi) ^ (-(1 + α)) * Real.Gamma (1 + α) *
        Real.cos (Real.pi * (1 + α) / 2) *
        ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + α) := by
  unfold realRiemannZeta
  rw [show (((-α : ℝ) : ℂ)) = -(α : ℂ) by push_cast; rfl,
    riemannZeta_neg_real_eq_ofReal hα]
  rfl

/-- The corrected power-sum constant has been proved to exist in
`EulerPower`.  This proposition isolates only its identification with the
standard analytic continuation of zeta. -/
def PowerSumZetaIdentification (α : ℝ) : Prop :=
  EulerPower.powerSumConstant α = realRiemannZeta (-α)

/-- The zeta identification is equivalently an equality between two explicit
absolutely convergent series. -/
theorem powerSumZetaIdentification_iff_explicit_series {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    PowerSumZetaIdentification α ↔
      -1 / (α + 1) + 1 / 2 - α / 12 +
          ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ α *
            EulerPower.localIncrement α (1 / ((n + 1 : ℕ) : ℝ)) =
      PowerZetaIdentification.zetaFunctionalCoefficient α := by
  unfold PowerSumZetaIdentification realRiemannZeta
  exact PowerZetaIdentification.powerSumConstant_eq_riemannZeta_re_iff hα0 hα2

/-- The corrected finite-part power-sum constant is the analytically
continued Riemann zeta value `ζ(-α)` for the full range in the paper. -/
theorem powerSumZetaIdentification {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    PowerSumZetaIdentification α := by
  unfold PowerSumZetaIdentification realRiemannZeta
  simpa only [Complex.ofReal_neg] using
    PowerZetaContinuation.powerSumConstant_eq_riemannZeta_re hα0 hα2

theorem tendsto_renormalizedPowerSum_to_zeta {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (hzeta : PowerSumZetaIdentification α) :
    Tendsto (EulerPower.renormalizedPowerSum α) atTop
      (𝓝 (realRiemannZeta (-α))) := by
  rw [PowerSumZetaIdentification] at hzeta
  simpa only [hzeta] using
    EulerPower.tendsto_renormalizedPowerSum hα0 hα2

theorem circleChordPowerSum_eq_circleGeneral (α : ℝ) (w : ℕ) :
    circleChordPowerSum α w = CircleGeneral.circleChordPowerSum α w := by
  unfold circleChordPowerSum circleProfile CircleGeneral.circleChordPowerSum
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  ring_nf

theorem circleAngularMoment_eq_circleGeneral (α : ℝ) :
    circleAngularMoment α = CircleGeneral.angularAverage α := by
  rfl

/-- Assembly of the general-`α` endpoint Euler--Maclaurin formula from the
residual-regularity package and identification of the corrected power-sum
constant.  The residual package is constructed unconditionally below. -/
theorem hasCircleEulerMaclaurin_of_endpointData_of_powerZeta
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hres : CircleGeneral.EndpointResidualData α)
    (hzeta : PowerSumZetaIdentification α) :
    HasCircleEulerMaclaurin α := by
  have hsmooth := CircleGeneral.smoothEndpointSubtraction_of_data
    hα0 hα2 hres
  have hpower :=
    (tendsto_renormalizedPowerSum_to_zeta hα0 hα2 hzeta).const_mul
      (2 * (2 * Real.pi) ^ α)
  have hadd := hsmooth.add hpower
  unfold HasCircleEulerMaclaurin
  convert hadd using 1
  · funext w
    rw [circleChordPowerSum_eq_circleGeneral,
      circleAngularMoment_eq_circleGeneral]
    ring
  · ring_nf

/-- The endpoint-regularity leaf of the general circle Euler--Maclaurin
argument is unconditional: the explicit residual has an integrable third
derivative, with endpoint singularity bounded by `O(x^(α-1))`. -/
theorem hasCircleEulerMaclaurin_of_powerZeta
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hzeta : PowerSumZetaIdentification α) :
    HasCircleEulerMaclaurin α :=
  hasCircleEulerMaclaurin_of_endpointData_of_powerZeta hα0 hα2
    (CircleGeneral.EndpointRegularity.endpointResidualData hα0) hzeta

/-- Unconditional endpoint Euler--Maclaurin formula for every exponent in
the range `0 < α < 2`. -/
theorem hasCircleEulerMaclaurin
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    HasCircleEulerMaclaurin α :=
  hasCircleEulerMaclaurin_of_powerZeta hα0 hα2
    (powerSumZetaIdentification hα0 hα2)

/-- Equation (3.2) before inserting a ring radius: the normalized
continuous-minus-discrete regular-polygon deficit has the negated endpoint
Euler--Maclaurin coefficient. -/
theorem tendsto_normalizedCircleSelfDeficit {α : ℝ}
    (hEM : HasCircleEulerMaclaurin α) :
    Tendsto
      (fun w : ℕ => (w : ℝ) ^ (α - 1) * circleSelfDeficit α w)
      atTop
      (𝓝 (-2 * (2 * Real.pi) ^ α * realRiemannZeta (-α))) := by
  have hneg := hEM.neg
  unfold HasCircleEulerMaclaurin at hneg
  convert hneg using 1
  · funext w
    by_cases hw : w = 0
    · simp [hw, circleSelfDeficit]
    have hwpos : 0 < (w : ℝ) := by positivity
    have hpow : (w : ℝ) ^ (α - 1) * (w : ℝ) = (w : ℝ) ^ α := by
      change Real.rpow (w : ℝ) (α - 1) * (w : ℝ) =
        Real.rpow (w : ℝ) α
      calc
        Real.rpow (w : ℝ) (α - 1) * (w : ℝ) =
            Real.rpow (w : ℝ) (α - 1) * Real.rpow (w : ℝ) 1 := by
          congr 1
          exact (Real.rpow_one _).symm
        _ = Real.rpow (w : ℝ) ((α - 1) + 1) :=
          (Real.rpow_add hwpos (α - 1) 1).symm
        _ = Real.rpow (w : ℝ) α := by ring_nf
    rw [circleSelfDeficit, ← hpow]
    ring
  · ring_nf

/-- The normalized one-ring correction is eventually uniformly bounded.
This is the domination extracted from endpoint Euler--Maclaurin that is
used when aggregating over all occupied rings. -/
theorem eventually_normalizedCircleSelfDeficit_le {α : ℝ}
    (hEM : HasCircleEulerMaclaurin α) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ w : ℕ in atTop,
      |(w : ℝ) ^ (α - 1) * circleSelfDeficit α w| ≤ C := by
  let L : ℝ := -2 * (2 * Real.pi) ^ α * realRiemannZeta (-α)
  refine ⟨|L| + 1, by positivity, ?_⟩
  have h := (tendsto_normalizedCircleSelfDeficit hEM).eventually
    (Metric.ball_mem_nhds L zero_lt_one)
  filter_upwards [h] with w hw
  rw [Real.dist_eq] at hw
  calc
    |(w : ℝ) ^ (α - 1) * circleSelfDeficit α w| =
        |((w : ℝ) ^ (α - 1) * circleSelfDeficit α w - L) + L| := by
      congr 1
      ring
    _ ≤ |(w : ℝ) ^ (α - 1) * circleSelfDeficit α w - L| + |L| :=
      abs_add _ _
    _ ≤ |L| + 1 := by linarith

/-- A convergent normalized circle error is bounded on the complete natural
sequence, so all finitely many small populations are absorbed as well. -/
theorem exists_uniform_normalized_circle_error_bound {α : ℝ}
    (hEM : HasCircleEulerMaclaurin α) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ,
      |(w : ℝ) ^ α *
        (circleChordPowerSum α w - (w : ℝ) * circleAngularMoment α)| ≤ C := by
  have hbounded : Bornology.IsBounded
      (Set.range (fun w : ℕ =>
        (w : ℝ) ^ α *
          (circleChordPowerSum α w - (w : ℝ) * circleAngularMoment α))) :=
    Metric.isBounded_range_of_tendsto _ hEM
  obtain ⟨C, hC, hbound⟩ := hbounded.exists_pos_norm_le
  refine ⟨C, hC, fun w ↦ ?_⟩
  simpa only [Real.norm_eq_abs] using hbound _ ⟨w, rfl⟩

/-- Uniform one-circle self-deficit estimate at its natural scale
`w^(1-α)`, valid also for empty and singleton populations. -/
theorem exists_uniform_circleSelfDeficit_bound {α : ℝ}
    (hEM : HasCircleEulerMaclaurin α) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ,
      |circleSelfDeficit α w| ≤ C * (w : ℝ) ^ (1 - α) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_normalized_circle_error_bound hEM
  refine ⟨C, hC, fun w ↦ ?_⟩
  by_cases hw : w = 0
  · subst w
    simp only [circleSelfDeficit, Nat.cast_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, sub_zero, abs_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg (le_refl 0) (1 - α))
  have hwR : 0 < (w : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hw)
  have hrpow :
      (w : ℝ) ^ (1 - α) * (w : ℝ) ^ α = (w : ℝ) := by
    calc
      (w : ℝ) ^ (1 - α) * (w : ℝ) ^ α =
          (w : ℝ) ^ ((1 - α) + α) := (Real.rpow_add hwR _ _).symm
      _ = (w : ℝ) ^ (1 : ℝ) := by congr 1 ; ring
      _ = (w : ℝ) := Real.rpow_one _
  have hfactor :
      circleSelfDeficit α w =
        -(w : ℝ) ^ (1 - α) *
          ((w : ℝ) ^ α *
            (circleChordPowerSum α w -
              (w : ℝ) * circleAngularMoment α)) := by
    unfold circleSelfDeficit
    calc
      (w : ℝ) ^ 2 * circleAngularMoment α -
          (w : ℝ) * circleChordPowerSum α w =
          -(w : ℝ) *
            (circleChordPowerSum α w -
              (w : ℝ) * circleAngularMoment α) := by ring
      _ = -((w : ℝ) ^ (1 - α) * (w : ℝ) ^ α) *
            (circleChordPowerSum α w -
              (w : ℝ) * circleAngularMoment α) := by rw [hrpow]
      _ = -(w : ℝ) ^ (1 - α) *
          ((w : ℝ) ^ α *
            (circleChordPowerSum α w -
              (w : ℝ) * circleAngularMoment α)) := by ring
  rw [hfactor, abs_mul, abs_neg,
    abs_of_nonneg (Real.rpow_nonneg hwR.le (1 - α))]
  calc
    (w : ℝ) ^ (1 - α) *
        |(w : ℝ) ^ α *
          (circleChordPowerSum α w -
            (w : ℝ) * circleAngularMoment α)|
        ≤ (w : ℝ) ^ (1 - α) * C :=
      mul_le_mul_of_nonneg_left (hbound w)
        (Real.rpow_nonneg hwR.le (1 - α))
    _ = C * (w : ℝ) ^ (1 - α) := by ring

theorem exists_uniform_circleSelfDeficit_bound_of_range {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ,
      |circleSelfDeficit α w| ≤ C * (w : ℝ) ^ (1 - α) :=
  exists_uniform_circleSelfDeficit_bound
    (hasCircleEulerMaclaurin hα0 hα2)

/-! ### Exact circle sum at `α = 1` -/

/-- Sum of unit-circle chord lengths from one vertex of a regular
`w`-gon to all other vertices. -/
noncomputable def circleChordSum (w : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (w - 1),
    2 * Real.sin (((i : ℝ) + 1) * (Real.pi / (w : ℝ)))

/-- The general chord-power sum specializes to the elementary chord sum at
`α = 1`. -/
theorem circleChordPowerSum_alpha_one (w : ℕ) :
    circleChordPowerSum 1 w = circleChordSum w := by
  unfold circleChordPowerSum circleProfile circleChordSum
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [Real.rpow_one]
  congr 2
  push_cast
  ring

/-- The continuous angular chord moment at `α = 1` is `4 / π`. -/
theorem circleAngularMoment_one :
    circleAngularMoment 1 = 4 / Real.pi := by
  have hchange := intervalIntegral.integral_comp_mul_right
    (a := (0 : ℝ)) (b := 1) Real.sin Real.pi_ne_zero
  have hsine :
      (∫ x in (0 : ℝ)..1, Real.sin (Real.pi * x)) = 2 / Real.pi := by
    calc
      (∫ x in (0 : ℝ)..1, Real.sin (Real.pi * x)) =
          Real.pi⁻¹ * ∫ y in (0 : ℝ)..Real.pi, Real.sin y := by
        simp only [smul_eq_mul] at hchange
        convert hchange using 1 <;> ring_nf
      _ = 2 / Real.pi := by
        rw [integral_sin, Real.cos_zero, Real.cos_pi]
        field_simp
        norm_num
  unfold circleAngularMoment circleProfile
  simp only [Real.rpow_one]
  rw [intervalIntegral.integral_const_mul, hsine]
  ring

/-- The special value needed to compare the general statement with the
independent cotangent proof. -/
theorem realRiemannZeta_neg_one :
    realRiemannZeta (-1) = -1 / 12 := by
  unfold realRiemannZeta
  rw [show (((-1 : ℝ) : ℂ)) = -(1 : ℕ) by norm_num,
    riemannZeta_neg_nat_eq_bernoulli' 1, bernoulli'_two]
  norm_num

theorem powerSumZetaIdentification_one : PowerSumZetaIdentification 1 := by
  rw [PowerSumZetaIdentification, EulerPower.powerSumConstant_one,
    realRiemannZeta_neg_one]

/-- Telescoping sine-sum identity underlying the exact `α = 1` computation. -/
theorem sin_half_mul_circleChordSum_aux (x : ℝ) (n : ℕ) :
    Real.sin (x / 2) *
        (∑ i ∈ Finset.range n, 2 * Real.sin ((i + 1) * x)) =
      Real.cos (x / 2) - Real.cos (((n : ℝ) + 1 / 2) * x) := by
  rw [Finset.mul_sum]
  calc
    (∑ i ∈ Finset.range n, Real.sin (x / 2) * (2 * Real.sin ((i + 1) * x))) =
        ∑ i ∈ Finset.range n,
          (Real.cos (((i : ℝ) + 1 / 2) * x) -
            Real.cos ((((i + 1 : ℕ) : ℝ) + 1 / 2) * x)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.cos_sub_cos]
      have hsum :
          ((((i : ℝ) + 1 / 2) * x + (((i + 1 : ℕ) : ℝ) + 1 / 2) * x) / 2) =
            ((i : ℝ) + 1) * x := by
        push_cast
        ring
      have hdiff :
          ((((i : ℝ) + 1 / 2) * x - (((i + 1 : ℕ) : ℝ) + 1 / 2) * x) / 2) =
            -(x / 2) := by
        push_cast
        ring
      rw [hsum, hdiff, Real.sin_neg]
      ring
    _ = Real.cos (x / 2) - Real.cos (((n : ℝ) + 1 / 2) * x) := by
      convert Finset.sum_range_sub'
        (fun i : ℕ ↦ Real.cos (((i : ℝ) + 1 / 2) * x)) n using 1 ;
        simp ; ring_nf

/-- Exact regular-polygon identity used in the manuscript's independent
check of the within-ring term at `α = 1`. -/
theorem circleChordSum_eq_two_cot (w : ℕ) (hw : 2 ≤ w) :
    circleChordSum w = 2 * Real.cot (Real.pi / (2 * w)) := by
  let x : ℝ := Real.pi / (w : ℝ)
  have hwpos : (0 : ℝ) < w := by positivity
  have hwone : 1 ≤ w := le_trans (by omega : 1 ≤ 2) hw
  have hcastsub : ((w - 1 : ℕ) : ℝ) = (w : ℝ) - 1 := by
    rw [Nat.cast_sub hwone]
    norm_num
  have hend : (((w - 1 : ℕ) : ℝ) + 1 / 2) * x = Real.pi - x / 2 := by
    dsimp [x]
    rw [hcastsub]
    field_simp
    ring
  have htel := sin_half_mul_circleChordSum_aux x (w - 1)
  rw [hend, Real.cos_pi_sub] at htel
  have hprod : Real.sin (x / 2) * circleChordSum w =
      2 * Real.cos (x / 2) := by
    simpa [circleChordSum, x, two_mul] using htel
  have hxhalf : x / 2 = Real.pi / (2 * (w : ℝ)) := by
    dsimp [x]
    ring
  have hden : (1 : ℝ) < 2 * w := by
    norm_num at hwpos ⊢
    linarith
  have hxpos : 0 < x / 2 := by
    rw [hxhalf]
    positivity
  have hxlt : x / 2 < Real.pi := by
    rw [hxhalf]
    exact div_lt_self Real.pi_pos hden
  have hsin : Real.sin (x / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hxpos hxlt).ne'
  rw [Real.cot_eq_cos_div_sin]
  have hquot : circleChordSum w =
      (2 * Real.cos (x / 2)) / Real.sin (x / 2) := by
    apply (eq_div_iff hsin).2
    nlinarith [hprod]
  rw [hquot, hxhalf]
  ring

/-- The continuous-minus-discrete self-deficit of a regular `w`-gon on a
unit circle at exponent `α = 1`, before multiplication by the ring radius.

The continuous angular chord average is `4 / π`; the second term is the
ordered discrete self-energy (one copy of `circleChordSum w` for every
vertex).  This is the scalar expression displayed after Lemma 3.2 of the
manuscript. -/
noncomputable def circleSelfDeficitOne (w : ℕ) : ℝ :=
  4 * (w : ℝ) ^ 2 / Real.pi - (w : ℝ) * circleChordSum w

/-- Exact cotangent form of the regular-polygon self-deficit at `α = 1`. -/
theorem circleSelfDeficitOne_eq_cot (w : ℕ) (hw : 2 ≤ w) :
    circleSelfDeficitOne w =
      (w : ℝ) * (4 * (w : ℝ) / Real.pi -
        2 * Real.cot (Real.pi / (2 * (w : ℝ)))) := by
  rw [circleSelfDeficitOne, circleChordSum_eq_two_cot w hw]
  ring

/-- At exponent `α = 1`, angular discretization on every nontrivial regular
polygon has strictly smaller self-energy than the corresponding uniform
circle.  This supplies the sign assertion in the elementary cotangent check
following Lemma 3.2. -/
theorem circleSelfDeficitOne_pos (w : ℕ) (hw : 2 ≤ w) :
    0 < circleSelfDeficitOne w := by
  rw [circleSelfDeficitOne_eq_cot w hw]
  let x : ℝ := Real.pi / (2 * (w : ℝ))
  have hwpos : (0 : ℝ) < w := by positivity
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hxlt : x < Real.pi / 2 := by
    dsimp [x]
    apply div_lt_div_of_pos_left Real.pi_pos (by positivity)
    norm_num at hwpos ⊢
    linarith
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxlt⟩
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hxpos (lt_trans hxlt (by linarith [Real.pi_pos]))
  have htan := Real.lt_tan hxpos hxlt
  rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos] at htan
  have hcot : Real.cot x < 1 / x := by
    rw [Real.cot_eq_cos_div_sin, div_lt_div_iff₀ hsin hxpos]
    simpa [mul_comm] using htan
  have hrecip : 1 / x = 2 * (w : ℝ) / Real.pi := by
    dsimp [x]
    field_simp
  have hparent :
      0 < 4 * (w : ℝ) / Real.pi - 2 * Real.cot x := by
    rw [hrecip] at hcot
    apply sub_pos.mpr
    calc
      2 * Real.cot x < 2 * (2 * (w : ℝ) / Real.pi) :=
        mul_lt_mul_of_pos_left hcot (by norm_num)
      _ = 4 * (w : ℝ) / Real.pi := by ring
  simpa [x] using mul_pos hwpos hparent

/-- The scalar self-deficit is nonnegative for every population, including
the empty and singleton edge cases used by the concrete BEMOC family. -/
theorem circleSelfDeficitOne_nonneg (w : ℕ) :
    0 ≤ circleSelfDeficitOne w := by
  rcases w with (_ | _ | w)
  · simp [circleSelfDeficitOne]
  · simp [circleSelfDeficitOne, circleChordSum]
    positivity
  · exact (circleSelfDeficitOne_pos (w + 2) (by omega)).le

/-- A population-uniform bound for the regular-polygon self-deficit at
`α = 1`.  The manuscript obtains the sharper limit `π / 3`; this elementary
bound already gives the required `O(1)` contribution per occupied ring. -/
theorem circleSelfDeficitOne_le (w : ℕ) (hw : 2 ≤ w) :
    circleSelfDeficitOne w ≤ Real.pi ^ 2 / 4 := by
  let x : ℝ := Real.pi / (2 * (w : ℝ))
  have hwpos : (0 : ℝ) < w := by positivity
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hxlt : x < Real.pi / 2 := by
    dsimp [x]
    apply div_lt_div_of_pos_left Real.pi_pos (by positivity)
    norm_num at hwpos ⊢
    linarith
  have hsinpos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hxpos (lt_trans hxlt (by linarith [Real.pi_pos]))
  have hsinlower : 2 / Real.pi * x ≤ Real.sin x :=
    Real.mul_le_sin hxpos.le hxlt.le
  have hsinupper : Real.sin x ≤ x := Real.sin_le hxpos.le
  have hcoslower : 1 - x ^ 2 / 2 ≤ Real.cos x :=
    Real.one_sub_sq_div_two_le_cos
  have hxcoslower : x * (1 - x ^ 2 / 2) ≤ x * Real.cos x :=
    mul_le_mul_of_nonneg_left hcoslower hxpos.le
  have hnum : Real.sin x - x * Real.cos x ≤ x ^ 3 / 2 := by
    calc
      Real.sin x - x * Real.cos x ≤ x - x * (1 - x ^ 2 / 2) :=
        sub_le_sub hsinupper hxcoslower
      _ = x ^ 3 / 2 := by ring
  have hfactor : 0 ≤ Real.pi * x / 4 * x := by positivity
  have hrhs : x ^ 3 / 2 ≤ Real.pi * x / 4 * (x * Real.sin x) := by
    calc
      x ^ 3 / 2 = (Real.pi * x / 4 * x) * (2 / Real.pi * x) := by
        field_simp [Real.pi_ne_zero]
        ring
      _ ≤ (Real.pi * x / 4 * x) * Real.sin x :=
        mul_le_mul_of_nonneg_left hsinlower hfactor
      _ = Real.pi * x / 4 * (x * Real.sin x) := by ring
  have hdiff : 1 / x - Real.cot x ≤ Real.pi * x / 4 := by
    rw [Real.cot_eq_cos_div_sin]
    have hid : 1 / x - Real.cos x / Real.sin x =
        (Real.sin x - x * Real.cos x) / (x * Real.sin x) := by
      field_simp [hxpos.ne', hsinpos.ne']
    rw [hid, div_le_iff₀ (mul_pos hxpos hsinpos)]
    exact hnum.trans hrhs
  have hrecip : 1 / x = 2 * (w : ℝ) / Real.pi := by
    dsimp [x]
    field_simp
  have hform : circleSelfDeficitOne w =
      2 * (w : ℝ) * (1 / x - Real.cot x) := by
    rw [circleSelfDeficitOne_eq_cot w hw, hrecip]
    ring
  have hbound := mul_le_mul_of_nonneg_left hdiff
    (show 0 ≤ 2 * (w : ℝ) by positivity)
  rw [← hform] at hbound
  calc
    circleSelfDeficitOne w ≤
        2 * (w : ℝ) * (Real.pi * x / 4) := hbound
    _ = Real.pi ^ 2 / 4 := by
      dsimp [x]
      field_simp
      ring

/-- A simple bound valid without a population side condition. -/
theorem circleSelfDeficitOne_le_four (w : ℕ) :
    circleSelfDeficitOne w ≤ 4 := by
  rcases w with (_ | _ | w)
  · simp [circleSelfDeficitOne]
  · simp [circleSelfDeficitOne, circleChordSum]
    have hpi : 0 < Real.pi := Real.pi_pos
    rw [div_le_iff₀ hpi]
    nlinarith [Real.two_le_pi]
  · refine (circleSelfDeficitOne_le (w + 2) (by omega)).trans ?_
    have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
    have hpisq : Real.pi ^ 2 ≤ (4 : ℝ) ^ 2 :=
      (sq_le_sq₀ hpi0 (by norm_num)).2 Real.pi_le_four
    nlinarith

/-! ### The sharp `α = 1` circle correction -/

open Filter Set
open scoped Topology

private theorem tendsto_sin_div_nhdsGT_zero :
    Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[>] 0) (𝓝 1) := by
  have h := (Real.hasDerivAt_sin 0).tendsto_slope_zero_right
  simpa [div_eq_mul_inv, mul_comm] using h

/-- The cubic cancellation in `sin x - x cos x`. -/
theorem tendsto_sin_sub_mul_cos_div_cube_nhdsGT_zero :
    Tendsto (fun x : ℝ => (Real.sin x - x * Real.cos x) / x ^ 3)
      (𝓝[>] 0) (𝓝 (1 / 3 : ℝ)) := by
  apply HasDerivAt.lhopital_zero_nhdsGT
  · filter_upwards with x
    convert (Real.hasDerivAt_sin x).sub
      ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1
  · filter_upwards with x
    convert (hasDerivAt_id x).pow 3 using 1
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    norm_num [hx0]
  · have h : Tendsto (fun x : ℝ => Real.sin x - x * Real.cos x) (𝓝 0) (𝓝 0) := by
      simpa using
        (Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)).tendsto 0
    exact h.mono_left inf_le_left
  · have h : Tendsto (fun x : ℝ => x ^ 3) (𝓝 0) (𝓝 0) := by
      simpa using
        (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).pow 3
    exact h.mono_left inf_le_left
  · have hratio :
        Tendsto (fun x : ℝ => (1 / 3 : ℝ) * (Real.sin x / x))
          (𝓝[>] 0) (𝓝 (1 / 3 : ℝ)) := by
      simpa using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (1 / 3 : ℝ))).mul
          tendsto_sin_div_nhdsGT_zero)
    refine hratio.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    field_simp [hx0]
    ring

/-- First nonzero term of the cotangent Laurent expansion, approached from
the right. -/
theorem tendsto_cot_remainder_nhdsGT_zero :
    Tendsto (fun x : ℝ => (1 / x - Real.cot x) / x)
      (𝓝[>] 0) (𝓝 (1 / 3 : ℝ)) := by
  have hquot := tendsto_sin_sub_mul_cos_div_cube_nhdsGT_zero.div
    tendsto_sin_div_nhdsGT_zero (by norm_num : (1 : ℝ) ≠ 0)
  have hquot' :
      Tendsto
        (fun x : ℝ =>
          ((Real.sin x - x * Real.cos x) / x ^ 3) / (Real.sin x / x))
        (𝓝[>] 0) (𝓝 (1 / 3 : ℝ)) := by
    simpa using hquot
  refine hquot'.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hsin : Real.sin x ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'
  rw [Real.cot_eq_cos_div_sin]
  field_simp
  ring

/-- The small positive angle sampled by a regular `w`-gon tends to zero. -/
theorem tendsto_pi_div_two_natCast_nhdsGT_zero :
    Tendsto (fun w : ℕ => Real.pi / (2 * (w : ℝ))) atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · convert tendsto_const_div_atTop_nhds_zero_nat (Real.pi / 2) using 1
    · funext w
      ring
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hw => hw⟩] with w hw
    exact div_pos Real.pi_pos (by positivity)

/-- The sharp `α = 1` cotangent correction for a regular polygon. -/
theorem tendsto_circle_cot_asymptotic :
    Tendsto
      (fun w : ℕ =>
        (w : ℝ) *
          (4 * (w : ℝ) / Real.pi -
            2 * Real.cot (Real.pi / (2 * (w : ℝ)))))
      atTop (𝓝 (Real.pi / 3)) := by
  let x : ℕ → ℝ := fun w => Real.pi / (2 * (w : ℝ))
  have hcore :
      Tendsto (fun w => (1 / x w - Real.cot (x w)) / x w)
        atTop (𝓝 (1 / 3 : ℝ)) :=
    tendsto_cot_remainder_nhdsGT_zero.comp tendsto_pi_div_two_natCast_nhdsGT_zero
  have hscaled :
      Tendsto
        (fun w => Real.pi * ((1 / x w - Real.cot (x w)) / x w))
        atTop (𝓝 (Real.pi * (1 / 3 : ℝ))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.pi) atTop (𝓝 Real.pi)).mul hcore
  convert hscaled using 1
  · funext w
    dsimp [x]
    by_cases hw : w = 0
    · simp [hw]
    field_simp [hw, Real.pi_ne_zero]
    ring
  · ring_nf

/-- Any circle sum eventually equal to the exact cotangent expression has
the same renormalized limit. -/
theorem tendsto_circle_sum_of_eventually_eq_two_cot (S : ℕ → ℝ)
    (hS : ∀ᶠ w in atTop,
      S w = 2 * Real.cot (Real.pi / (2 * (w : ℝ)))) :
    Tendsto
      (fun w : ℕ => (w : ℝ) * (4 * (w : ℝ) / Real.pi - S w))
      atTop (𝓝 (Real.pi / 3)) := by
  refine tendsto_circle_cot_asymptotic.congr' ?_
  filter_upwards [hS] with w hw
  rw [hw]

/-- The manuscript's independent `α = 1` check, including its sharp
`π / 3` limiting correction. -/
theorem tendsto_circleChordSum_alpha_one :
    Tendsto circleSelfDeficitOne atTop (𝓝 (Real.pi / 3)) := by
  have hcot : ∀ᶠ w in atTop,
      circleChordSum w = 2 * Real.cot (Real.pi / (2 * (w : ℝ))) := by
    filter_upwards [eventually_atTop.2 ⟨2, fun _ hw => hw⟩] with w hw
    exact circleChordSum_eq_two_cot w hw
  convert tendsto_circle_sum_of_eventually_eq_two_cot circleChordSum hcot using 1
  funext w
  unfold circleSelfDeficitOne
  ring

/-- Equation (3.1) at `α = 1`, written in remainder form:
`circleChordSum w = 4w/π - π/(3w) + o(1/w)`. -/
theorem tendsto_circleChordSum_remainder_alpha_one :
    Tendsto
      (fun w : ℕ =>
        (w : ℝ) * (circleChordSum w - 4 * (w : ℝ) / Real.pi))
      atTop (𝓝 (-Real.pi / 3)) := by
  convert tendsto_circleChordSum_alpha_one.neg using 1
  · funext w
    unfold circleSelfDeficitOne
    ring
  · ring_nf

/-- The general endpoint Euler--Maclaurin statement agrees with, and at
`α = 1` follows from, the independent exact cotangent computation. -/
theorem hasCircleEulerMaclaurin_one : HasCircleEulerMaclaurin 1 := by
  unfold HasCircleEulerMaclaurin
  convert tendsto_circleChordSum_remainder_alpha_one using 1
  · funext w
    rw [circleChordPowerSum_alpha_one, circleAngularMoment_one,
      Real.rpow_one]
    ring
  · rw [realRiemannZeta_neg_one, Real.rpow_one]
    ring_nf

namespace GridMultiplicity

/-- Multiplication by an integer, descended from `ℤ` to a cyclic additive
group.  The divisibility assumption makes the map well-defined modulo `n`. -/
def zmodScaleHom (n m : ℕ) (c : ℤ) (h : (m : ℤ) ∣ (n : ℤ) * c) :
    ZMod n →+ ZMod m :=
  ZMod.lift n ⟨
    { toFun := fun z ↦ (z : ZMod m) * (c : ZMod m)
      map_zero' := by simp
      map_add' := by
        intro x y
        push_cast
        ring },
    by
      change ((n : ℤ) * c : ZMod m) = 0
      simpa only [Int.cast_mul] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) * c) m).2 h ⟩

@[simp]
theorem zmodScaleHom_intCast (n m : ℕ) (c z : ℤ)
    (h : (m : ℤ) ∣ (n : ℤ) * c) :
    zmodScaleHom n m c h (z : ZMod n) = (z * c : ℤ) := by
  simp [zmodScaleHom]

/-- Difference of polygon angles, measured on their common grid. -/
def gridDifferenceHom (d a b : ℕ) :
    ZMod (d * a) × ZMod (d * b) →+ ZMod (d * a * b) :=
  (zmodScaleHom (d * a) (d * a * b) b (by
      simpa only [Nat.cast_mul] using
        (dvd_refl ((d : ℤ) * (a : ℤ) * (b : ℤ))))).comp (AddMonoidHom.fst _ _) -
    (zmodScaleHom (d * b) (d * a * b) a (by
      convert (dvd_refl ((d : ℤ) * (a : ℤ) * (b : ℤ))) using 1
      all_goals
        push_cast
        ring)).comp (AddMonoidHom.snd _ _)

@[simp]
theorem gridDifferenceHom_intCast (d a b : ℕ) (i j : ℤ) :
    gridDifferenceHom d a b (i, j) =
      (b : ZMod (d * a * b)) * i - (a : ZMod (d * a * b)) * j := by
  simp [gridDifferenceHom, zmodScaleHom_intCast]
  ring

/-- Bézout's identity makes the common-grid difference map onto when the
reduced populations are coprime. -/
theorem gridDifferenceHom_surjective {d a b : ℕ} (hab : a.Coprime b) :
    Function.Surjective (gridDifferenceHom d a b) := by
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  refine ⟨((b.gcdA a * z : ℤ), (-b.gcdB a * z : ℤ)), ?_⟩
  rw [gridDifferenceHom_intCast]
  have hbezout : (1 : ℤ) = b * b.gcdA a + a * b.gcdB a := by
    rw [← Nat.gcd_eq_gcd_ab]
    exact_mod_cast hab.symm.gcd_eq_one.symm
  calc
    (b : ZMod (d * a * b)) * (b.gcdA a * z : ℤ) -
        (a : ZMod (d * a * b)) * (-b.gcdB a * z : ℤ) =
        ((b * b.gcdA a + a * b.gcdB a) * z : ℤ) := by
          push_cast
          ring
    _ = (z : ZMod (d * a * b)) := by rw [← hbezout, one_mul]

/-- In a coprime factorization, the common modulus is the lcm. -/
theorem lcm_mul_coprime {d a b : ℕ} (hab : a.Coprime b) :
    Nat.lcm (d * a) (d * b) = d * a * b := by
  rw [Nat.lcm_mul_left, hab.lcm_eq_mul]
  ring

/-- In the same factorization, `d` is the gcd of the populations. -/
theorem gcd_mul_coprime {d a b : ℕ} (hab : a.Coprime b) :
    Nat.gcd (d * a) (d * b) = d := by
  rw [Nat.gcd_mul_left, hab.gcd_eq_one, mul_one]

/-- The population product is gcd times lcm. -/
theorem population_product_eq_gcd_mul_lcm {d a b : ℕ} (hab : a.Coprime b) :
    (d * a) * (d * b) = d * Nat.lcm (d * a) (d * b) := by
  rw [lcm_mul_coprime hab]
  ring

/-- Every point on the lcm grid occurs with multiplicity `d` among the
ordered pairs of polygon vertices. -/
theorem gridDifference_fiber_card {d a b : ℕ} [NeZero d] [NeZero a] [NeZero b]
    (hab : a.Coprime b) (k : ZMod (d * a * b)) :
    ((Finset.univ : Finset (ZMod (d * a) × ZMod (d * b))).filter
      (fun ij ↦ gridDifferenceHom d a b ij = k)).card = d := by
  classical
  let f := gridDifferenceHom d a b
  let c := ((Finset.univ : Finset (ZMod (d * a) × ZMod (d * b))).filter
    (fun ij ↦ f ij = k)).card
  have hsurj : Function.Surjective f := gridDifferenceHom_surjective hab
  have hfiber (y : ZMod (d * a * b)) :
      ((Finset.univ : Finset (ZMod (d * a) × ZMod (d * b))).filter
        (fun ij ↦ f ij = y)).card = c := by
    apply AddMonoidHom.card_fiber_eq_of_mem_range f
    · exact hsurj y
    · exact hsurj k
  have hcard : (d * a * b) * c = (d * a) * (d * b) := by
    calc
      (d * a * b) * c =
          ∑ y : ZMod (d * a * b),
            ((Finset.univ : Finset (ZMod (d * a) × ZMod (d * b))).filter
              (fun ij ↦ f ij = y)).card := by
                simp_rw [hfiber]
                rw [Finset.sum_const, Finset.card_univ, ZMod.card]
                norm_num [nsmul_eq_mul]
      _ = Fintype.card (ZMod (d * a) × ZMod (d * b)) := by
            symm
            simpa using
              (Finset.card_eq_sum_card_fiberwise
                (s := (Finset.univ : Finset (ZMod (d * a) × ZMod (d * b))))
                (t := (Finset.univ : Finset (ZMod (d * a * b))))
                (f := f) (by simp))
      _ = (d * a) * (d * b) := by simp [ZMod.card]
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  have hm : 0 < d * a * b := by positivity
  have hc : c = d := by
    apply Nat.eq_of_mul_eq_mul_left hm
    calc
      (d * a * b) * c = (d * a) * (d * b) := hcard
      _ = (d * a * b) * d := by ring
  exact hc

/-- Multiset form of `gridDifference_fiber_card`: summing a function over
all ordered vertex pairs is `d` times its sum over the common grid. -/
theorem sum_gridDifference_eq_gcd_mul_sum {d a b : ℕ}
    [NeZero d] [NeZero a] [NeZero b] (hab : a.Coprime b)
    {A : Type*} [AddCommMonoid A] (F : ZMod (d * a * b) → A) :
    ∑ ij : ZMod (d * a) × ZMod (d * b), F (gridDifferenceHom d a b ij) =
      d • ∑ k : ZMod (d * a * b), F k := by
  classical
  rw [← Finset.sum_fiberwise' Finset.univ
    (fun ij ↦ gridDifferenceHom d a b ij) F]
  simp_rw [Finset.sum_const, gridDifference_fiber_card hab]
  rw [Finset.sum_nsmul]

/-! #### Direct interface for arbitrary positive populations -/

/-- Positivity of both populations makes their lcm a valid `ZMod` modulus. -/
instance neZero_lcm (q r : ℕ) [NeZero q] [NeZero r] : NeZero (Nat.lcm q r) :=
  ⟨(Nat.lcm_pos (Nat.pos_of_neZero q) (Nat.pos_of_neZero r)).ne'⟩

/-- Angular difference for arbitrary populations, valued directly in their
`lcm` grid. -/
def generalGridDifferenceHom (q r : ℕ) :
    ZMod q × ZMod r →+ ZMod (Nat.lcm q r) :=
  (zmodScaleHom q (Nat.lcm q r) (Int.ofNat (Nat.lcm q r / q)) (by
      have hq : q * (Nat.lcm q r / q) = Nat.lcm q r :=
        Nat.mul_div_cancel_left' (Nat.dvd_lcm_left q r)
      have hqz : (q : ℤ) * Int.ofNat (Nat.lcm q r / q) = Nat.lcm q r := by
        calc
          (q : ℤ) * Int.ofNat (Nat.lcm q r / q) =
              Int.ofNat (q * (Nat.lcm q r / q)) := Int.ofNat_mul_out _ _
          _ = Int.ofNat (Nat.lcm q r) := congrArg Int.ofNat hq
      rw [hqz])).comp (AddMonoidHom.fst _ _) -
    (zmodScaleHom r (Nat.lcm q r) (Int.ofNat (Nat.lcm q r / r)) (by
      have hr : r * (Nat.lcm q r / r) = Nat.lcm q r :=
        Nat.mul_div_cancel_left' (Nat.dvd_lcm_right q r)
      have hrz : (r : ℤ) * Int.ofNat (Nat.lcm q r / r) = Nat.lcm q r := by
        calc
          (r : ℤ) * Int.ofNat (Nat.lcm q r / r) =
              Int.ofNat (r * (Nat.lcm q r / r)) := Int.ofNat_mul_out _ _
          _ = Int.ofNat (Nat.lcm q r) := congrArg Int.ofNat hr
      rw [hrz])).comp (AddMonoidHom.snd _ _)

@[simp]
theorem generalGridDifferenceHom_intCast (q r : ℕ) (i j : ℤ) :
    generalGridDifferenceHom q r (i, j) =
      ((Nat.lcm q r / q : ℕ) : ZMod (Nat.lcm q r)) * i -
        ((Nat.lcm q r / r : ℕ) : ZMod (Nat.lcm q r)) * j := by
  simp [generalGridDifferenceHom, zmodScaleHom_intCast]
  have hqcast :
      (((Nat.lcm q r : ℤ) / (q : ℤ) : ℤ) : ZMod (Nat.lcm q r)) =
        ((Nat.lcm q r / q : ℕ) : ZMod (Nat.lcm q r)) := by
    calc
      (((Nat.lcm q r : ℤ) / (q : ℤ) : ℤ) : ZMod (Nat.lcm q r)) =
          (((Nat.lcm q r / q : ℕ) : ℤ) : ZMod (Nat.lcm q r)) :=
        congrArg (fun z : ℤ ↦ (z : ZMod (Nat.lcm q r)))
          (Int.natCast_div (Nat.lcm q r) q).symm
      _ = ((Nat.lcm q r / q : ℕ) : ZMod (Nat.lcm q r)) := Int.cast_natCast _
  have hrcast :
      (((Nat.lcm q r : ℤ) / (r : ℤ) : ℤ) : ZMod (Nat.lcm q r)) =
        ((Nat.lcm q r / r : ℕ) : ZMod (Nat.lcm q r)) := by
    calc
      (((Nat.lcm q r : ℤ) / (r : ℤ) : ℤ) : ZMod (Nat.lcm q r)) =
          (((Nat.lcm q r / r : ℕ) : ℤ) : ZMod (Nat.lcm q r)) :=
        congrArg (fun z : ℤ ↦ (z : ZMod (Nat.lcm q r)))
          (Int.natCast_div (Nat.lcm q r) r).symm
      _ = ((Nat.lcm q r / r : ℕ) : ZMod (Nat.lcm q r)) := Int.cast_natCast _
  rw [hqcast, hrcast]
  ring

/-- Dividing positive populations by their gcd gives coprime factors. -/
theorem div_gcd_coprime {q r : ℕ} [NeZero q] :
    (q / Nat.gcd q r).Coprime (r / Nat.gcd q r) := by
  apply Nat.coprime_div_gcd_div_gcd
  exact Nat.gcd_pos_of_pos_left r (Nat.pos_of_neZero q)

theorem lcm_div_left_eq_div_gcd_right {q r : ℕ} [NeZero q] [NeZero r] :
    Nat.lcm q r / q = r / Nat.gcd q r := by
  let d := Nat.gcd q r
  let a := q / d
  let b := r / d
  change Nat.lcm q r / q = b
  have hd : 0 < d := Nat.gcd_pos_of_pos_left r (Nat.pos_of_neZero q)
  have hq : d * a = q := Nat.mul_div_cancel_left' (Nat.gcd_dvd_left q r)
  have hr : d * b = r := Nat.mul_div_cancel_left' (Nat.gcd_dvd_right q r)
  have ha : 0 < a := by
    have hqpos : 0 < q := Nat.pos_of_neZero q
    nlinarith
  have hab : a.Coprime b := div_gcd_coprime
  have hL : Nat.lcm q r = d * a * b := by
    calc
      Nat.lcm q r = Nat.lcm (d * a) (d * b) := by rw [hq, hr]
      _ = d * a * b := lcm_mul_coprime hab
  rw [hL, ← hq]
  exact Nat.mul_div_cancel_left b (Nat.mul_pos hd ha)

theorem lcm_div_right_eq_div_gcd_left {q r : ℕ} [NeZero q] [NeZero r] :
    Nat.lcm q r / r = q / Nat.gcd q r := by
  rw [Nat.lcm_comm, Nat.gcd_comm]
  exact lcm_div_left_eq_div_gcd_right (q := r) (r := q)

/-- The direct angular-difference map is onto. -/
theorem generalGridDifferenceHom_surjective {q r : ℕ} [NeZero q] [NeZero r] :
    Function.Surjective (generalGridDifferenceHom q r) := by
  let d := Nat.gcd q r
  let a := q / d
  let b := r / d
  have hab : a.Coprime b := div_gcd_coprime
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  refine ⟨((b.gcdA a * z : ℤ), (-b.gcdB a * z : ℤ)), ?_⟩
  rw [generalGridDifferenceHom_intCast,
    lcm_div_left_eq_div_gcd_right, lcm_div_right_eq_div_gcd_left]
  have hbezout : (1 : ℤ) = b * b.gcdA a + a * b.gcdB a := by
    rw [← Nat.gcd_eq_gcd_ab]
    exact_mod_cast hab.symm.gcd_eq_one.symm
  calc
    (b : ZMod (Nat.lcm q r)) * (b.gcdA a * z : ℤ) -
        (a : ZMod (Nat.lcm q r)) * (-b.gcdB a * z : ℤ) =
        ((b * b.gcdA a + a * b.gcdB a) * z : ℤ) := by
          push_cast
          ring
    _ = (z : ZMod (Nat.lcm q r)) := by rw [← hbezout, one_mul]

/-- Every lcm-grid point occurs exactly `gcd q r` times among the `q*r`
ordered pairs. -/
theorem generalGridDifference_fiber_card {q r : ℕ} [NeZero q] [NeZero r]
    (k : ZMod (Nat.lcm q r)) :
    ((Finset.univ : Finset (ZMod q × ZMod r)).filter
      (fun ij ↦ generalGridDifferenceHom q r ij = k)).card = Nat.gcd q r := by
  classical
  let f := generalGridDifferenceHom q r
  let c := ((Finset.univ : Finset (ZMod q × ZMod r)).filter
    (fun ij ↦ f ij = k)).card
  have hsurj : Function.Surjective f := generalGridDifferenceHom_surjective
  have hfiber (y : ZMod (Nat.lcm q r)) :
      ((Finset.univ : Finset (ZMod q × ZMod r)).filter
        (fun ij ↦ f ij = y)).card = c := by
    apply AddMonoidHom.card_fiber_eq_of_mem_range f
    · exact hsurj y
    · exact hsurj k
  have hcard : Nat.lcm q r * c = q * r := by
    calc
      Nat.lcm q r * c =
          ∑ y : ZMod (Nat.lcm q r),
            ((Finset.univ : Finset (ZMod q × ZMod r)).filter
              (fun ij ↦ f ij = y)).card := by
                simp_rw [hfiber]
                rw [Finset.sum_const, Finset.card_univ, ZMod.card]
                norm_num [nsmul_eq_mul]
      _ = Fintype.card (ZMod q × ZMod r) := by
            symm
            simpa using
              (Finset.card_eq_sum_card_fiberwise
                (s := (Finset.univ : Finset (ZMod q × ZMod r)))
                (t := (Finset.univ : Finset (ZMod (Nat.lcm q r))))
                (f := f) (by simp))
      _ = q * r := by simp [ZMod.card]
  have hL : 0 < Nat.lcm q r :=
    Nat.lcm_pos (Nat.pos_of_neZero q) (Nat.pos_of_neZero r)
  apply Nat.eq_of_mul_eq_mul_left hL
  calc
    Nat.lcm q r * c = q * r := hcard
    _ = Nat.lcm q r * Nat.gcd q r := by
      rw [← Nat.gcd_mul_lcm]
      ring

/-- Direct finite-sum form used in Section 4: the `q*r` angular differences
are the lcm grid, each with gcd multiplicity. -/
theorem sum_generalGridDifference_eq_gcd_mul_sum {q r : ℕ}
    [NeZero q] [NeZero r] {A : Type*} [AddCommMonoid A]
    (F : ZMod (Nat.lcm q r) → A) :
    ∑ ij : ZMod q × ZMod r, F (generalGridDifferenceHom q r ij) =
      Nat.gcd q r • ∑ k : ZMod (Nat.lcm q r), F k := by
  classical
  rw [← Finset.sum_fiberwise' Finset.univ (generalGridDifferenceHom q r) F]
  simp_rw [Finset.sum_const, generalGridDifference_fiber_card]
  rw [Finset.sum_nsmul]

end GridMultiplicity

/-! ## Discrete construction -/

/-- The number of latitude bands used in the BEMOC construction. -/
def bandCount (N : ℕ) : ℕ := Nat.sqrt (N / 4)

/-- The ordinary northern band population. -/
def ordinaryPopulation (j : ℕ) : ℕ := 4 * j - 1

/-- Sum of the first `m` ordinary populations, corresponding to indices
`1, ..., m`. -/
theorem sum_ordinaryPopulation (m : ℕ) :
    ∑ k ∈ Finset.range m, ordinaryPopulation (k + 1) = m * (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      have hop : ordinaryPopulation (m + 1) = 4 * m + 3 := by
        simp [ordinaryPopulation]
        omega
      rw [hop]
      ring

theorem sum_ordinaryPopulation_Ico (m : ℕ) :
    ∑ j ∈ Finset.Ico 1 (m + 1), ordinaryPopulation j = m * (2 * m + 1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simpa [add_comm] using sum_ordinaryPopulation m

/-- The exceptional central population before reflection. -/
def centralPopulation (N : ℕ) : ℕ :=
  N - 2 * ∑ j ∈ Finset.Ico 1 (bandCount N), ordinaryPopulation j

/-- Total population before inserting the central band: northern ordinary
bands plus their southern reflection. -/
def doubledOrdinaryTotal (N : ℕ) : ℕ :=
  2 * ∑ j ∈ Finset.Ico 1 (bandCount N), ordinaryPopulation j

/-- The total population after adjoining the central band. -/
def reflectedPopulationTotal (N : ℕ) : ℕ :=
  doubledOrdinaryTotal N + centralPopulation N

/-- Symmetric list of band populations, indexed by `1, ..., 2M-1`. -/
def bandPopulation (N j : ℕ) : ℕ :=
  let M := bandCount N
  if j < M then ordinaryPopulation j
  else if j = M then centralPopulation N
  else ordinaryPopulation (2 * M - j)

theorem bandCount_sq_le (N : ℕ) : bandCount N ^ 2 ≤ N / 4 := by
  simpa [bandCount] using Nat.sqrt_le' (N / 4)

theorem doubledOrdinaryTotal_closed (N : ℕ) (hM : 1 ≤ bandCount N) :
    doubledOrdinaryTotal N =
      2 * ((bandCount N - 1) * (2 * (bandCount N - 1) + 1)) := by
  unfold doubledOrdinaryTotal
  have htop : bandCount N - 1 + 1 = bandCount N := Nat.sub_add_cancel hM
  have hsum :
      ∑ j ∈ Finset.Ico 1 (bandCount N), ordinaryPopulation j =
        (bandCount N - 1) * (2 * (bandCount N - 1) + 1) := by
    calc
      _ = ∑ j ∈ Finset.Ico 1 (bandCount N - 1 + 1), ordinaryPopulation j := by
        rw [htop]
      _ = _ := sum_ordinaryPopulation_Ico (bandCount N - 1)
  rw [hsum]

theorem doubledOrdinaryTotal_le (N : ℕ) : doubledOrdinaryTotal N ≤ N := by
  by_cases hM : bandCount N = 0
  · simp [doubledOrdinaryTotal, hM]
  · have hM1 : 1 ≤ bandCount N := Nat.one_le_iff_ne_zero.mpr hM
    rw [doubledOrdinaryTotal_closed N hM1]
    have hsqrt := bandCount_sq_le N
    have hdiv : 4 * (N / 4) ≤ N := by omega
    have hscale : 4 * bandCount N ^ 2 ≤ N :=
      le_trans (Nat.mul_le_mul_left 4 hsqrt) hdiv
    have hpred : bandCount N = (bandCount N - 1) + 1 := by omega
    nlinarith

theorem centralPopulation_accounting (N : ℕ)
    (h : 2 * ∑ j ∈ Finset.Ico 1 (bandCount N), ordinaryPopulation j ≤ N) :
    centralPopulation N +
        2 * ∑ j ∈ Finset.Ico 1 (bandCount N), ordinaryPopulation j = N := by
  unfold centralPopulation
  omega

theorem reflectedPopulationTotal_eq (N : ℕ) : reflectedPopulationTotal N = N := by
  unfold reflectedPopulationTotal doubledOrdinaryTotal
  have h := centralPopulation_accounting N (doubledOrdinaryTotal_le N)
  omega

/-! ### A finite symmetric list of BEMOC bands

The list representation is useful for the geometric construction below: it
contains the northern ordinary populations, the exceptional central
population, and the reflected northern populations.  Unlike the formula
`bandPopulation`, the endpoints and the reflection are encoded directly in
the finite indexing type.
-/

/-- Northern ordinary populations `r₁, ..., r_{M-1}`. -/
def northernBandPopulations (N : ℕ) : List ℕ :=
  (List.range (bandCount N - 1)).map (fun k ↦ ordinaryPopulation (k + 1))

/-- All BEMOC band populations, including the central band and reflection. -/
def symmetricBandPopulations (N : ℕ) : List ℕ :=
  northernBandPopulations N ++
    centralPopulation N :: (northernBandPopulations N).reverse

@[simp] theorem length_northernBandPopulations (N : ℕ) :
    (northernBandPopulations N).length = bandCount N - 1 := by
  simp [northernBandPopulations]

theorem sum_northernBandPopulations (N : ℕ) :
    (northernBandPopulations N).sum =
      ∑ j ∈ Finset.Ico 1 (bandCount N), ordinaryPopulation j := by
  rw [northernBandPopulations,
    ← List.sum_toFinset (fun k ↦ ordinaryPopulation (k + 1)) List.nodup_range]
  have hrange :
      (List.range (bandCount N - 1)).toFinset =
        Finset.range (bandCount N - 1) := by
    ext k
    simp
  rw [hrange, Finset.sum_Ico_eq_sum_range]
  congr 1
  simp [add_comm]

@[simp] theorem length_symmetricBandPopulations (N : ℕ) :
    (symmetricBandPopulations N).length = 2 * (bandCount N - 1) + 1 := by
  simp [symmetricBandPopulations]
  omega

/-- The finite symmetric band family has exactly the requested population. -/
@[simp] theorem sum_symmetricBandPopulations (N : ℕ) :
    (symmetricBandPopulations N).sum = N := by
  rw [symmetricBandPopulations, List.sum_append, List.sum_cons,
    List.sum_reverse, sum_northernBandPopulations]
  have h := centralPopulation_accounting N (doubledOrdinaryTotal_le N)
  unfold doubledOrdinaryTotal at h
  omega

/-- The number of BEMOC bands, expressed without truncated subtraction when
`N ≥ 4` (and hence `M ≥ 1`). -/
theorem length_symmetricBandPopulations_of_four_le {N : ℕ} (hN : 4 ≤ N) :
    (symmetricBandPopulations N).length = 2 * bandCount N - 1 := by
  rw [length_symmetricBandPopulations]
  have hM : 1 ≤ bandCount N := by
    rw [bandCount]
    exact Nat.sqrt_pos.mpr (by omega)
  omega

/-- Height of the boundary following the first `j` bands.  Thus index zero
is the north pole and the final boundary is the south pole. -/
noncomputable def bandBoundaryHeight (N j : ℕ) : ℝ :=
  1 - 2 * ((symmetricBandPopulations N).take j).sum / N

theorem sum_take_symmetricBandPopulations_le (N j : ℕ) :
    ((symmetricBandPopulations N).take j).sum ≤ N := by
  have hsplit := List.sum_take_add_sum_drop (symmetricBandPopulations N) j
  rw [sum_symmetricBandPopulations] at hsplit
  omega

/-- Every cumulative boundary height is a valid spherical height. -/
theorem bandBoundaryHeight_mem {N : ℕ} (hN : 0 < N) (j : ℕ) :
    bandBoundaryHeight N j ∈ Set.Icc (-1 : ℝ) 1 := by
  have hpartial := sum_take_symmetricBandPopulations_le N j
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hpartialReal :
      (((symmetricBandPopulations N).take j).sum : ℝ) ≤ N := by
    exact_mod_cast hpartial
  have hratio0 :
      0 ≤ (((symmetricBandPopulations N).take j).sum : ℝ) / N := by
    positivity
  have hratio1 :
      (((symmetricBandPopulations N).take j).sum : ℝ) / N ≤ 1 := by
    exact (div_le_one hNreal).2 hpartialReal
  have hfactor :
      2 * (((symmetricBandPopulations N).take j).sum : ℝ) / N =
        2 * ((((symmetricBandPopulations N).take j).sum : ℝ) / N) := by
    ring
  change -1 ≤ 1 - 2 *
      (((symmetricBandPopulations N).take j).sum : ℝ) / N ∧
    1 - 2 * (((symmetricBandPopulations N).take j).sum : ℝ) / N ≤ 1
  rw [hfactor]
  constructor <;> nlinarith

@[simp] theorem bandBoundaryHeight_zero (N : ℕ) :
    bandBoundaryHeight N 0 = 1 := by
  simp [bandBoundaryHeight]

@[simp] theorem bandBoundaryHeight_final {N : ℕ} (hN : 0 < N) :
    bandBoundaryHeight N (symmetricBandPopulations N).length = -1 := by
  rw [bandBoundaryHeight, List.take_length, sum_symmetricBandPopulations]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  norm_num

/-- Height of the midpoint atom in band `j`. -/
noncomputable def bandMidpointHeight (N j : ℕ) : ℝ :=
  (bandBoundaryHeight N j + bandBoundaryHeight N (j + 1)) / 2

theorem bandMidpointHeight_mem {N : ℕ} (hN : 0 < N) (j : ℕ) :
    bandMidpointHeight N j ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases bandBoundaryHeight_mem hN j with ⟨hjLower, hjUpper⟩
  rcases bandBoundaryHeight_mem hN (j + 1) with ⟨hj1Lower, hj1Upper⟩
  constructor
  · change -1 ≤
      (bandBoundaryHeight N j + bandBoundaryHeight N (j + 1)) / 2
    linarith
  · change (bandBoundaryHeight N j + bandBoundaryHeight N (j + 1)) / 2 ≤ 1
    linarith

/-! ### Exact midpoint and shared-boundary rings -/

/-- One less than the number of bands.  Writing the band count as `n + 1`
makes the two endpoint conventions convenient in finite sums. -/
def bandTailCount (N : ℕ) : ℕ := 2 * (bandCount N - 1)

theorem length_symmetricBandPopulations_eq_tail_succ (N : ℕ) :
    (symmetricBandPopulations N).length = bandTailCount N + 1 := by
  simp [bandTailCount]

/-- Population of a band under the canonical `Fin (n+1)` indexing. -/
def finiteBandPopulation (N : ℕ) (j : Fin (bandTailCount N + 1)) : ℕ :=
  (symmetricBandPopulations N).get
    ((finCongr (length_symmetricBandPopulations_eq_tail_succ N)).symm j)

theorem sum_finiteBandPopulation (N : ℕ) :
    ∑ j, finiteBandPopulation N j = N := by
  let e : Fin (symmetricBandPopulations N).length ≃
      Fin (bandTailCount N + 1) :=
    finCongr (length_symmetricBandPopulations_eq_tail_succ N)
  change (∑ j, (symmetricBandPopulations N).get (e.symm j)) = N
  rw [e.symm.sum_comp]
  calc
    (∑ j, (symmetricBandPopulations N).get j) =
        (symmetricBandPopulations N).sum := by
      rw [← List.sum_ofFn, List.ofFn_get]
    _ = N := sum_symmetricBandPopulations N

/-- The one-sixth boundary contribution of a band.  It is forced to vanish
at the first and last bands, exactly as in the endpoint convention of the
paper. -/
def boundarySixth (N : ℕ) (j : Fin (bandTailCount N + 1)) : ℕ :=
  if j = 0 ∨ j = Fin.last (bandTailCount N) then 0
  else finiteBandPopulation N j / 6

@[simp] theorem boundarySixth_zero (N : ℕ) : boundarySixth N 0 = 0 := by
  simp [boundarySixth]

@[simp] theorem boundarySixth_last (N : ℕ) :
    boundarySixth N (Fin.last (bandTailCount N)) = 0 := by
  simp [boundarySixth]

theorem twice_boundarySixth_le (N : ℕ) (j : Fin (bandTailCount N + 1)) :
    2 * boundarySixth N j ≤ finiteBandPopulation N j := by
  unfold boundarySixth
  split_ifs
  · simp
  · have hdiv := Nat.mul_div_le (finiteBandPopulation N j) 6
    omega

/-- Population placed at the midpoint of a band.  For an interior band this
is `4 * (r/6) + r%6`, written in a subtraction form convenient for exact
cardinality accounting. -/
def midpointRingPopulation (N : ℕ) (j : Fin (bandTailCount N + 1)) : ℕ :=
  finiteBandPopulation N j - 2 * boundarySixth N j

/-- Population at the shared boundary between consecutive bands. -/
def sharedBoundaryPopulation (N : ℕ) (j : Fin (bandTailCount N)) : ℕ :=
  boundarySixth N (j.castSucc : Fin (bandTailCount N + 1)) +
    boundarySixth N (j.succ : Fin (bandTailCount N + 1))

theorem sum_sharedBoundaryPopulation (N : ℕ) :
    ∑ j, sharedBoundaryPopulation N j =
      2 * ∑ j, boundarySixth N j := by
  rw [show (∑ j, sharedBoundaryPopulation N j) =
      (∑ j : Fin (bandTailCount N),
        boundarySixth N (j.castSucc : Fin (bandTailCount N + 1))) +
        ∑ j : Fin (bandTailCount N),
          boundarySixth N (j.succ : Fin (bandTailCount N + 1)) by
    simp_rw [sharedBoundaryPopulation]
    exact Finset.sum_add_distrib]
  have hleft := Fin.sum_univ_castSucc (boundarySixth N)
  have hright := Fin.sum_univ_succ (boundarySixth N)
  rw [boundarySixth_last, add_zero] at hleft
  rw [boundarySixth_zero, zero_add] at hright
  rw [← hleft, ← hright]
  omega

theorem sum_midpointRingPopulation (N : ℕ) :
    ∑ j, midpointRingPopulation N j =
      N - 2 * ∑ j, boundarySixth N j := by
  simp_rw [midpointRingPopulation]
  rw [Finset.sum_tsub_distrib Finset.univ
      (fun j _ ↦ twice_boundarySixth_le N j),
    sum_finiteBandPopulation]
  simp [Finset.mul_sum]

/-- The midpoint and shared-boundary rings together contain exactly `N`
points. -/
theorem total_concrete_ring_population (N : ℕ) :
    (∑ j, midpointRingPopulation N j) +
      ∑ j, sharedBoundaryPopulation N j = N := by
  rw [sum_midpointRingPopulation, sum_sharedBoundaryPopulation]
  have hle : 2 * ∑ j, boundarySixth N j ≤ N := by
    calc
      2 * ∑ j, boundarySixth N j =
          ∑ j, 2 * boundarySixth N j := by simp [Finset.mul_sum]
      _ ≤ ∑ j, finiteBandPopulation N j :=
        Finset.sum_le_sum fun j _ ↦ twice_boundarySixth_le N j
      _ = N := sum_finiteBandPopulation N
  omega

/-- The actual BEMOC occupied-ring family: midpoint rings followed by the
shared-boundary rings.  The phase is set to zero; later results allow it to
be replaced independently on every ring. -/
noncomputable def bemocRingFamily (N : ℕ) :
    (Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N)) → OccupiedRing
  | Sum.inl j =>
      { population := midpointRingPopulation N j
        height := if hN : 0 < N then bandMidpointHeight N j else 0
        height_mem := by
          split_ifs with hN
          · exact bandMidpointHeight_mem hN j
          · norm_num
        phase := 0 }
  | Sum.inr j =>
      { population := sharedBoundaryPopulation N j
        height := if hN : 0 < N then bandBoundaryHeight N (j + 1) else 0
        height_mem := by
          split_ifs with hN
          · exact bandBoundaryHeight_mem hN (j + 1)
          · norm_num
        phase := 0 }

theorem sum_bemocRingFamily_population (N : ℕ) :
    ∑ k, (bemocRingFamily N k).population = N := by
  rw [Fintype.sum_sum_type]
  exact total_concrete_ring_population N

/-- A concrete `RingConstructionSequence` containing all BEMOC midpoint and
combined shared-boundary rings. -/
noncomputable def bemocRingConstructionSequence : RingConstructionSequence where
  ringCount N := Fintype.card
    (Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N))
  rings N i := bemocRingFamily N ((Fintype.equivFin _).symm i)
  totalPopulation N := by
    calc
      ∑ i, (bemocRingFamily N ((Fintype.equivFin _).symm i)).population =
          ∑ k, (bemocRingFamily N k).population :=
        (Fintype.equivFin
          (Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N))).symm.sum_comp
            (fun k ↦ (bemocRingFamily N k).population)
      _ = N := sum_bemocRingFamily_population N

/-! ## Continuous angular ring measures -/

open MeasureTheory

/-- Normalized Lebesgue measure on one full angular period. -/
noncomputable def uniformAngleMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) •
    volume.restrict (Set.Ioc 0 (2 * Real.pi))

@[simp] theorem uniformAngleMeasure_apply_univ :
    uniformAngleMeasure Set.univ = 1 := by
  rw [uniformAngleMeasure, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter, Real.volume_Ioc, sub_zero]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [show 1 / (2 * Real.pi) = (2 * Real.pi)⁻¹ by ring,
    ENNReal.ofReal_inv_of_pos hpi]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_eq_zero.not.mpr (not_le.mpr hpi)) ENNReal.ofReal_ne_top

theorem measurable_parallelPoint (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    Measurable (fun θ ↦ parallelPoint z θ hz) := by
  apply Continuous.measurable
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  fin_cases i <;> simp [parallelPoint, parallelVector] <;> fun_prop

/-- Uniform angular probability measure pushed onto an occupied parallel. -/
noncomputable def angularRingMeasure (R : OccupiedRing) : Measure Sphere :=
  Measure.map (fun θ ↦ parallelPoint R.height θ R.height_mem) uniformAngleMeasure

@[simp] theorem angularRingMeasure_apply_univ (R : OccupiedRing) :
    angularRingMeasure R Set.univ = 1 := by
  rw [angularRingMeasure,
    Measure.map_apply (measurable_parallelPoint R.height R.height_mem)
      MeasurableSet.univ]
  simp

/-- The continuous measure obtained by spreading every polygon population
uniformly around its parallel. -/
noncomputable def continuousRingMeasure {κ : Type*} [Fintype κ]
    (R : κ → OccupiedRing) : Measure Sphere :=
  ∑ k, (R k).population • angularRingMeasure (R k)

theorem continuousRingMeasure_apply_univ {κ : Type*} [Fintype κ]
    (R : κ → OccupiedRing) :
    continuousRingMeasure R Set.univ = ∑ k, ((R k).population : ENNReal) := by
  simp [continuousRingMeasure, Measure.sum_apply]

@[simp] theorem bemoc_continuousRingMeasure_apply_univ (N : ℕ) :
    continuousRingMeasure (bemocRingFamily N) Set.univ = N := by
  rw [continuousRingMeasure_apply_univ]
  exact_mod_cast sum_bemocRingFamily_population N

theorem angularRingMeasure_apply_univ_ne_top (R : OccupiedRing) :
    angularRingMeasure R Set.univ ≠ ⊤ := by
  rw [angularRingMeasure_apply_univ]
  norm_num

theorem continuousRingMeasure_apply_univ_ne_top {κ : Type*} [Fintype κ]
    (R : κ → OccupiedRing) : continuousRingMeasure R Set.univ ≠ ⊤ := by
  rw [continuousRingMeasure_apply_univ]
  rw [ENNReal.sum_ne_top]
  exact fun k _ ↦ ENNReal.coe_ne_top

/-- Integration against the combined ring measure is the population-weighted
finite sum of integrations against its angular probability measures. -/
theorem integral_continuousRingMeasure {κ : Type*} [Fintype κ]
    (R : κ → OccupiedRing) (f : Sphere → ℝ)
    (hf : ∀ k, Integrable f (angularRingMeasure (R k))) :
    ∫ x, f x ∂continuousRingMeasure R =
      ∑ k, (R k).population * ∫ x, f x ∂angularRingMeasure (R k) := by
  unfold continuousRingMeasure
  simp_rw [← Nat.cast_smul_eq_nsmul ENNReal]
  calc
    _ = ∑ k, ∫ x, f x ∂((R k).population : ENNReal) •
        angularRingMeasure (R k) := by
      exact integral_finset_sum_measure (s := Finset.univ) (fun k _ ↦
        (hf k).smul_measure ENNReal.coe_ne_top)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_smul_measure]
      simp

/-- Pair energy of two measures for a real-valued kernel. -/
noncomputable def kernelPairEnergy (K : Sphere → Sphere → ℝ)
    (μ ν : Measure Sphere) : ℝ :=
  ∫ x, ∫ y, K x y ∂ν ∂μ

/-- Distance-power energy between two finite measures. -/
noncomputable def measurePairEnergy (μ ν : Measure Sphere) (α : ℝ) : ℝ :=
  kernelPairEnergy (fun x y ↦ dist x y ^ α) μ ν

theorem continuous_distancePowerKernel {α : ℝ} (hα : 0 < α) :
    Continuous (fun p : Sphere × Sphere ↦ dist p.1 p.2 ^ α) := by
  exact continuous_dist.rpow continuous_const (fun _ ↦ Or.inr hα)

theorem integrable_distancePower_angular {α : ℝ} (hα : 0 < α)
    (x : Sphere) (R : OccupiedRing) :
    Integrable (fun y : Sphere ↦ dist x y ^ α) (angularRingMeasure R) := by
  letI : IsFiniteMeasure (angularRingMeasure R) :=
    IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr (angularRingMeasure_apply_univ_ne_top R))
  have hcont : Continuous (fun y : Sphere ↦ dist x y ^ α) :=
    (continuous_const.dist continuous_id).rpow continuous_const (fun _ ↦ Or.inr hα)
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_inner_distancePower_angular {α : ℝ} (hα : 0 < α)
    (R : OccupiedRing) :
    Continuous (fun x : Sphere ↦
      ∫ y : Sphere, dist x y ^ α ∂angularRingMeasure R) := by
  letI : IsFiniteMeasure (angularRingMeasure R) :=
    IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr (angularRingMeasure_apply_univ_ne_top R))
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      (μ := angularRingMeasure R) (continuous_distancePowerKernel hα)
      (s := Set.univ) isCompact_univ)

theorem integrable_inner_distancePower_continuousRingMeasure
    {κ : Type*} [Fintype κ] {α : ℝ} (hα : 0 < α)
    (R : κ → OccupiedRing) (Q : OccupiedRing) :
    Integrable (fun x : Sphere ↦
      ∫ y : Sphere, dist x y ^ α ∂angularRingMeasure Q)
      (continuousRingMeasure R) := by
  letI : IsFiniteMeasure (continuousRingMeasure R) :=
    IsFiniteMeasure.mk
      (lt_top_iff_ne_top.mpr (continuousRingMeasure_apply_univ_ne_top R))
  exact (continuous_inner_distancePower_angular hα Q).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrable_inner_distancePower_angular_angular
    {α : ℝ} (hα : 0 < α) (P Q : OccupiedRing) :
    Integrable (fun x : Sphere ↦
      ∫ y : Sphere, dist x y ^ α ∂angularRingMeasure Q)
      (angularRingMeasure P) := by
  letI : IsFiniteMeasure (angularRingMeasure P) :=
    IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr (angularRingMeasure_apply_univ_ne_top P))
  exact (continuous_inner_distancePower_angular hα Q).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem measurePairEnergy_smul_left (c : ENNReal) (μ ν : Measure Sphere) (α : ℝ) :
    measurePairEnergy (c • μ) ν α = c.toReal * measurePairEnergy μ ν α := by
  unfold measurePairEnergy kernelPairEnergy
  rw [integral_smul_measure]
  rfl

theorem measurePairEnergy_smul_right (c : ENNReal) (μ ν : Measure Sphere) (α : ℝ) :
    measurePairEnergy μ (c • ν) α = c.toReal * measurePairEnergy μ ν α := by
  unfold measurePairEnergy kernelPairEnergy
  simp_rw [integral_smul_measure]
  simp only [smul_eq_mul]
  rw [integral_const_mul]

/-- Symmetry of distance-power energy for finite measures. -/
theorem measurePairEnergy_comm {α : ℝ} (hα : 0 < α)
    (μ ν : Measure Sphere) (hμ : μ Set.univ ≠ ⊤) (hν : ν Set.univ ≠ ⊤) :
    measurePairEnergy μ ν α = measurePairEnergy ν μ α := by
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  have hcont : Continuous (fun p : Sphere × Sphere ↦ dist p.1 p.2 ^ α) :=
    continuous_distancePowerKernel hα
  have hint : Integrable (fun p : Sphere × Sphere ↦ dist p.1 p.2 ^ α) (μ.prod ν) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold measurePairEnergy kernelPairEnergy
  rw [integral_integral_swap hint]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with x
  rw [dist_comm]

/-- The continuously spread energy of a pair of occupied rings, including
their population weights. -/
noncomputable def continuousRingPairEnergy (P Q : OccupiedRing) (α : ℝ) : ℝ :=
  (P.population : ℝ) * (Q.population : ℝ) *
    measurePairEnergy (angularRingMeasure P) (angularRingMeasure Q) α

/-! ### Exact continuous one-ring circle formula -/

theorem parallelPoint_add_two_pi (z θ : ℝ)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    parallelPoint z (θ + 2 * Real.pi) hz = parallelPoint z θ hz := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [parallelPoint, parallelVector, Real.cos_add_two_pi,
      Real.sin_add_two_pi]

theorem dist_parallelPoint_common_add (z θ φ a : ℝ)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    dist (parallelPoint z (θ + a) hz) (parallelPoint z (φ + a) hz) =
      dist (parallelPoint z θ hz) (parallelPoint z φ hz) := by
  rw [parallelPoint_same_height_dist_eq_radius_mul_abs_sin,
    parallelPoint_same_height_dist_eq_radius_mul_abs_sin]
  have harg : ((θ + a) - (φ + a)) / 2 = (θ - φ) / 2 := by ring
  rw [harg]

theorem dist_parallelPoint_eq_difference (z θ φ : ℝ)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    dist (parallelPoint z θ hz) (parallelPoint z φ hz) =
      dist (parallelPoint z 0 hz) (parallelPoint z (φ - θ) hz) := by
  have h := dist_parallelPoint_common_add z 0 (φ - θ) θ hz
  rw [zero_add, sub_add_cancel] at h
  exact h

theorem integral_uniformAngleMeasure_eq_interval (f : ℝ → ℝ) :
    (∫ θ, f θ ∂uniformAngleMeasure) =
      (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..2 * Real.pi, f θ := by
  rw [uniformAngleMeasure, integral_smul_measure]
  have hc : 0 ≤ 1 / (2 * Real.pi) := by positivity
  rw [ENNReal.toReal_ofReal hc]
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rfl

theorem integral_angularRingMeasure_eq_uniform
    (R : OccupiedRing) (f : Sphere → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂angularRingMeasure R) =
      ∫ θ, f (parallelPoint R.height θ R.height_mem) ∂uniformAngleMeasure := by
  unfold angularRingMeasure
  rw [integral_map_of_stronglyMeasurable
    (measurable_parallelPoint R.height R.height_mem) hf.stronglyMeasurable]

theorem dist_parallelPoint_zero_eq_chord (R : OccupiedRing) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    dist
        (parallelPoint R.height 0 R.height_mem)
        (parallelPoint R.height t R.height_mem) =
      R.radius * (2 * Real.sin (t / 2)) := by
  have ht₂0 : 0 ≤ t / 2 := by linarith [ht.1]
  have ht₂pi : t / 2 ≤ Real.pi := by linarith [ht.2]
  have hsin : 0 ≤ Real.sin (t / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht₂0 ht₂pi
  rw [parallelPoint_same_height_dist_eq_radius_mul_abs_sin]
  have harg : (0 - t) / 2 = -(t / 2) := by ring
  rw [harg, Real.sin_neg, mul_neg, abs_neg,
    abs_of_nonneg (mul_nonneg (by norm_num) hsin)]
  rfl

theorem dist_parallelPoint_zero_rpow_eq_profile
    (R : OccupiedRing) {t α : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    dist
        (parallelPoint R.height 0 R.height_mem)
        (parallelPoint R.height t R.height_mem) ^ α =
      R.radius ^ α * circleProfile α (t / (2 * Real.pi)) := by
  rw [dist_parallelPoint_zero_eq_chord R ht]
  have ht₂0 : 0 ≤ t / 2 := by linarith [ht.1]
  have ht₂pi : t / 2 ≤ Real.pi := by linarith [ht.2]
  have hchord : 0 ≤ 2 * Real.sin (t / 2) :=
    mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_nonneg_of_le_pi ht₂0 ht₂pi)
  rw [Real.mul_rpow R.radius_nonneg hchord]
  unfold circleProfile
  have harg : Real.pi * (t / (2 * Real.pi)) = t / 2 := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [harg]

theorem intervalIntegral_reference_ring_eq_moment
    (R : OccupiedRing) (α : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
        dist
          (parallelPoint R.height 0 R.height_mem)
          (parallelPoint R.height t R.height_mem) ^ α) =
      (2 * Real.pi) * R.radius ^ α * circleAngularMoment α := by
  have heq :
      (∫ t in (0 : ℝ)..2 * Real.pi,
          dist
            (parallelPoint R.height 0 R.height_mem)
            (parallelPoint R.height t R.height_mem) ^ α) =
        ∫ t in (0 : ℝ)..2 * Real.pi,
          R.radius ^ α * circleProfile α (t / (2 * Real.pi)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply dist_parallelPoint_zero_rpow_eq_profile R
    simpa only [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using ht
  rw [heq, intervalIntegral.integral_const_mul]
  have hscale : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_div (circleProfile α) hscale]
  simp only [zero_div, div_self hscale]
  unfold circleAngularMoment
  simp only [smul_eq_mul]
  ring

/-- Reference-vertex chord kernel on the real angular cover. -/
noncomputable def referenceRingKernel (R : OccupiedRing) (α t : ℝ) : ℝ :=
  dist
    (parallelPoint R.height 0 R.height_mem)
    (parallelPoint R.height t R.height_mem) ^ α

theorem referenceRingKernel_periodic (R : OccupiedRing) (α : ℝ) :
    Function.Periodic (referenceRingKernel R α) (2 * Real.pi) := by
  intro t
  unfold referenceRingKernel
  rw [parallelPoint_add_two_pi]

set_option maxHeartbeats 800000 in
theorem integral_uniform_ringKernel_eq_moment
    (R : OccupiedRing) (α θ : ℝ) :
    (∫ φ,
        dist
          (parallelPoint R.height θ R.height_mem)
          (parallelPoint R.height φ R.height_mem) ^ α
        ∂uniformAngleMeasure) =
      R.radius ^ α * circleAngularMoment α := by
  let g : ℝ → ℝ := referenceRingKernel R α
  have hg : Function.Periodic g (2 * Real.pi) :=
    referenceRingKernel_periodic R α
  have hshift :
      (∫ t in -θ..2 * Real.pi - θ, g t) =
        ∫ t in (0 : ℝ)..2 * Real.pi, g t := by
    convert hg.intervalIntegral_add_eq (-θ) 0 using 1 <;> ring_nf
  calc
    (∫ φ,
        dist
          (parallelPoint R.height θ R.height_mem)
          (parallelPoint R.height φ R.height_mem) ^ α
        ∂uniformAngleMeasure) =
        (1 / (2 * Real.pi)) *
          ∫ φ in (0 : ℝ)..2 * Real.pi,
            dist
              (parallelPoint R.height θ R.height_mem)
              (parallelPoint R.height φ R.height_mem) ^ α :=
      integral_uniformAngleMeasure_eq_interval _
    _ = (1 / (2 * Real.pi)) *
          ∫ φ in (0 : ℝ)..2 * Real.pi, g (φ - θ) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro φ hφ
      unfold g referenceRingKernel
      change
        dist
            (parallelPoint R.height θ R.height_mem)
            (parallelPoint R.height φ R.height_mem) ^ α =
          dist
            (parallelPoint R.height 0 R.height_mem)
            (parallelPoint R.height (φ - θ) R.height_mem) ^ α
      rw [dist_parallelPoint_eq_difference]
    _ = (1 / (2 * Real.pi)) *
          ∫ t in -θ..2 * Real.pi - θ, g t := by
      rw [intervalIntegral.integral_comp_sub_right]
      simp only [zero_sub]
    _ = (1 / (2 * Real.pi)) *
          ∫ t in (0 : ℝ)..2 * Real.pi, g t := by rw [hshift]
    _ = R.radius ^ α * circleAngularMoment α := by
      unfold g referenceRingKernel
      rw [intervalIntegral_reference_ring_eq_moment]
      field_simp [Real.pi_ne_zero]
      ring

theorem integral_distancePower_angularRingMeasure_eq_moment
    (R : OccupiedRing) {α : ℝ} (hα : 0 < α) (θ : ℝ) :
    (∫ y : Sphere,
        dist (parallelPoint R.height θ R.height_mem) y ^ α
        ∂angularRingMeasure R) =
      R.radius ^ α * circleAngularMoment α := by
  have hf : Continuous (fun y : Sphere ↦
      dist (parallelPoint R.height θ R.height_mem) y ^ α) :=
    (continuous_const.dist continuous_id).rpow continuous_const
      (fun _ ↦ Or.inr hα)
  rw [integral_angularRingMeasure_eq_uniform R _ hf]
  exact integral_uniform_ringKernel_eq_moment R α θ

/-- Exact normalized continuous self-energy of one occupied parallel. -/
theorem measurePairEnergy_angularRingMeasure_self_eq_moment
    (R : OccupiedRing) {α : ℝ} (hα : 0 < α) :
    measurePairEnergy (angularRingMeasure R) (angularRingMeasure R) α =
      R.radius ^ α * circleAngularMoment α := by
  unfold measurePairEnergy kernelPairEnergy
  rw [integral_angularRingMeasure_eq_uniform R _
    (continuous_inner_distancePower_angular hα R)]
  simp_rw [integral_distancePower_angularRingMeasure_eq_moment R hα]
  rw [integral_const]
  simp only [smul_eq_mul, measureReal_def,
    uniformAngleMeasure_apply_univ, ENNReal.toReal_one, one_mul]

/-- Exact population-weighted continuous one-ring formula. -/
theorem continuousRingPairEnergy_self_eq_circleMoment
    (R : OccupiedRing) {α : ℝ} (hα : 0 < α) :
    continuousRingPairEnergy R R α =
      R.radius ^ α * (R.population : ℝ) ^ 2 * circleAngularMoment α := by
  rw [continuousRingPairEnergy,
    measurePairEnergy_angularRingMeasure_self_eq_moment R hα]
  ring

/-- Total continuous angular energy, expressed as a finite ring-pair sum. -/
noncomputable def continuousRingEnergy {κ : Type*} [Fintype κ]
    (R : κ → OccupiedRing) (α : ℝ) : ℝ :=
  ∑ p, ∑ q, continuousRingPairEnergy (R p) (R q) α

/-- Diagonal (same-ring) part of continuous angular energy. -/
noncomputable def continuousWithinRingEnergy {κ : Type*} [Fintype κ]
    (R : κ → OccupiedRing) (α : ℝ) : ℝ :=
  ∑ p, continuousRingPairEnergy (R p) (R p) α

/-- Scalar aggregation of all regular-polygon self-deficits.  The exact
one-ring geometric formulas identify this with the manuscript's
within-ring term. -/
noncomputable def aggregatedWithinRingDeficit {κ : Type*} [Fintype κ]
    (R : κ → OccupiedRing) (α : ℝ) : ℝ :=
  ∑ p, (R p).radius ^ α * circleSelfDeficit α (R p).population

/-- Off-diagonal (different-ring) part of continuous angular energy. -/
noncomputable def continuousCrossRingEnergy {κ : Type*} [Fintype κ]
    [DecidableEq κ] (R : κ → OccupiedRing) (α : ℝ) : ℝ :=
  ∑ p, ∑ q, if p ≠ q then continuousRingPairEnergy (R p) (R q) α else 0

/-- The finite pair-sum definition of continuous ring energy is exactly the
double integral against the combined population-weighted ring measure. -/
theorem measurePairEnergy_continuousRingMeasure {κ : Type*} [Fintype κ]
    (R : κ → OccupiedRing) {α : ℝ} (hα : 0 < α) :
    measurePairEnergy (continuousRingMeasure R) (continuousRingMeasure R) α =
      continuousRingEnergy R α := by
  unfold measurePairEnergy kernelPairEnergy
  have hinner (x : Sphere) :
      (∫ y : Sphere, dist x y ^ α ∂continuousRingMeasure R) =
        ∑ q, (R q).population *
          ∫ y : Sphere, dist x y ^ α ∂angularRingMeasure (R q) :=
    integral_continuousRingMeasure R (fun y ↦ dist x y ^ α)
      (fun q ↦ integrable_distancePower_angular hα x (R q))
  simp_rw [hinner]
  rw [integral_finset_sum Finset.univ (fun q _ ↦
    (integrable_inner_distancePower_continuousRingMeasure hα R (R q)).const_mul _)]
  simp_rw [integral_const_mul]
  have houter (q : κ) :
      (∫ x : Sphere, (∫ y : Sphere, dist x y ^ α ∂angularRingMeasure (R q))
        ∂continuousRingMeasure R) =
        ∑ p, (R p).population *
          ∫ x : Sphere, (∫ y : Sphere, dist x y ^ α ∂angularRingMeasure (R q))
            ∂angularRingMeasure (R p) :=
    integral_continuousRingMeasure R
      (fun x ↦ ∫ y : Sphere, dist x y ^ α ∂angularRingMeasure (R q))
      (fun p ↦ integrable_inner_distancePower_angular_angular hα (R p) (R q))
  simp_rw [houter]
  unfold continuousRingEnergy continuousRingPairEnergy measurePairEnergy kernelPairEnergy
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem continuous_ring_energy_eq_within_add_cross {κ : Type*} [Fintype κ]
    [DecidableEq κ] (R : κ → OccupiedRing) (α : ℝ) :
    continuousRingEnergy R α =
      continuousWithinRingEnergy R α + continuousCrossRingEnergy R α := by
  classical
  unfold continuousRingEnergy continuousWithinRingEnergy continuousCrossRingEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hoff :
      (∑ q, if p ≠ q then continuousRingPairEnergy (R p) (R q) α else 0) =
        ∑ q ∈ Finset.univ.erase p, continuousRingPairEnergy (R p) (R q) α := by
    rw [← Finset.sum_filter]
    congr 1
    ext q
    simp [ne_comm]
  rw [hoff]
  rw [← Finset.sum_erase_add Finset.univ
    (fun q ↦ continuousRingPairEnergy (R p) (R q) α) (Finset.mem_univ p)]
  ac_rfl

/-- Exact finite-sum aggregation of the continuous and discrete one-ring
circle identities for an arbitrary occupied-ring family. -/
theorem withinRingDeficit_eq_aggregated
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : κ → OccupiedRing) {α : ℝ} (hα : 0 < α) :
    continuousWithinRingEnergy R α - withinRingEnergy R α =
      aggregatedWithinRingDeficit R α := by
  rw [withinRingEnergy_eq_sum_single R hα]
  unfold continuousWithinRingEnergy aggregatedWithinRingDeficit
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [continuousRingPairEnergy_self_eq_circleMoment (R p) hα,
    singleRingDiscreteEnergy_eq_circle]
  unfold circleSelfDeficit
  ring

/-- Uniform aggregation bound retaining the exact geometric weight
`Σ ρ_p^α w_p^(1-α)`. -/
theorem exists_uniform_withinRingDeficit_bound_of_range
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {κ : Type*} [Fintype κ] [DecidableEq κ]
        (R : κ → OccupiedRing),
        |continuousWithinRingEnergy R α - withinRingEnergy R α| ≤
          C * ∑ p, (R p).radius ^ α *
            ((R p).population : ℝ) ^ (1 - α) := by
  obtain ⟨C, hC, hcircle⟩ :=
    exists_uniform_circleSelfDeficit_bound_of_range hα0 hα2
  refine ⟨C, hC, ?_⟩
  intro κ instFintype instDecidableEq R
  rw [withinRingDeficit_eq_aggregated R hα0]
  unfold aggregatedWithinRingDeficit
  calc
    |∑ p, (R p).radius ^ α *
        circleSelfDeficit α (R p).population| ≤
        ∑ p, |(R p).radius ^ α *
          circleSelfDeficit α (R p).population| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, C * (R p).radius ^ α *
          ((R p).population : ℝ) ^ (1 - α) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (R p).radius_nonneg α)]
      calc
        (R p).radius ^ α * |circleSelfDeficit α (R p).population| ≤
            (R p).radius ^ α *
              (C * ((R p).population : ℝ) ^ (1 - α)) :=
          mul_le_mul_of_nonneg_left (hcircle (R p).population)
            (Real.rpow_nonneg (R p).radius_nonneg α)
        _ = C * (R p).radius ^ α *
            ((R p).population : ℝ) ^ (1 - α) := by ring
    _ = C * ∑ p, (R p).radius ^ α *
          ((R p).population : ℝ) ^ (1 - α) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- Exact three-term decomposition for any finite occupied-ring family.  The
first term is latitude quadrature, the second within-ring discretization,
and the third cross-ring angular aliasing. -/
theorem occupied_ring_exact_decomposition {κ : Type*} [Fintype κ]
    [DecidableEq κ] (R : κ → OccupiedRing) (α I : ℝ) :
    I - finiteRieszEnergy (ringConfiguration R) α =
      (I - continuousRingEnergy R α) +
        (continuousWithinRingEnergy R α - withinRingEnergy R α) +
        (continuousCrossRingEnergy R α - crossRingEnergy R α) := by
  apply insert_continuous_ring_energy
  · exact ring_energy_eq_within_add_cross R α
  · exact continuous_ring_energy_eq_within_add_cross R α

/-- The paper's exact decomposition specialized to the concrete BEMOC rings. -/
theorem bemoc_exact_decomposition (N : ℕ) (α I : ℝ) :
    I - finiteRieszEnergy (ringConfiguration (bemocRingFamily N)) α =
      (I - continuousRingEnergy (bemocRingFamily N) α) +
        (continuousWithinRingEnergy (bemocRingFamily N) α -
          withinRingEnergy (bemocRingFamily N) α) +
        (continuousCrossRingEnergy (bemocRingFamily N) α -
          crossRingEnergy (bemocRingFamily N) α) := by
  exact occupied_ring_exact_decomposition (bemocRingFamily N) α I

/-! ### Normalized surface area on the sphere -/

theorem sphereHaarMeasure_apply_univ_ne_zero :
    volume.toSphere (E := Ambient) Set.univ ≠ 0 := by
  rw [Measure.toSphere_apply_univ]
  exact ne_of_gt (ENNReal.mul_pos (by norm_num)
    (ne_of_gt (Metric.measure_ball_pos volume 0 (by norm_num))))

/-- Normalized surface-area probability measure on `S²`, obtained from
Lebesgue Haar measure by mathlib's polar-coordinate construction. -/
noncomputable def sphereAreaProbability : Measure Sphere :=
  (volume.toSphere (E := Ambient) Set.univ)⁻¹ • volume.toSphere

@[simp] theorem sphereAreaProbability_apply_univ :
    sphereAreaProbability Set.univ = 1 := by
  rw [sphereAreaProbability, Measure.smul_apply]
  exact ENNReal.inv_mul_cancel sphereHaarMeasure_apply_univ_ne_zero
    (measure_ne_top (volume.toSphere : Measure Sphere) Set.univ)

/-- North pole used to evaluate the rotationally invariant potential. -/
noncomputable def northPole : Sphere :=
  parallelPoint 1 0 (by norm_num)

theorem northPole_dist_sq (y : Sphere) :
    dist northPole y ^ 2 = 2 * (1 - (y : Ambient) 2) := by
  change dist (parallelVector 1 0) (y : Ambient) ^ 2 = _
  rw [dist_eq_norm, norm_sub_sq_real]
  have hp : ‖parallelVector 1 0‖ = 1 := by
    simpa [northPole, parallelPoint] using norm_eq_of_mem_sphere northPole
  rw [hp, norm_eq_of_mem_sphere y]
  simp [northPole, parallelPoint, parallelVector,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  ring

/-- The elementary one-dimensional integral underlying the spherical
potential calculation. -/
theorem uniform_height_distancePower_integral {α : ℝ} (hα : 0 < α) :
    (1 / 2 : ℝ) *
        (∫ z : ℝ in (-1)..1, (2 * (1 - z)) ^ (α / 2)) =
      2 ^ (α + 1) / (α + 2) := by
  have hsub := intervalIntegral.integral_comp_sub_left
    (a := (-1 : ℝ)) (b := 1) (fun u : ℝ ↦ (2 * u) ^ (α / 2)) 1
  norm_num at hsub
  rw [hsub]
  have hscale := intervalIntegral.mul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 2) (f := fun t : ℝ ↦ t ^ (α / 2)) (2 : ℝ)
  norm_num at hscale
  have hi : (∫ u : ℝ in (0 : ℝ)..2, (2 * u) ^ (α / 2)) =
      (1 / 2 : ℝ) * (∫ t : ℝ in (0 : ℝ)..4, t ^ (α / 2)) := by
    linarith [hscale]
  rw [hi]
  rw [integral_rpow (Or.inl (by linarith : -1 < α / 2))]
  norm_num
  have hp : α / 2 + 1 = (α + 2) / 2 := by ring
  rw [hp]
  have hα2 : α + 2 ≠ 0 := by linarith
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
  ring_nf
  field_simp
  rw [show 2 + α = (1 + α) + 1 by ring,
    Real.rpow_add (by positivity : 0 < (2 : ℝ))]
  norm_num
  ring

/-- Height coordinate on the sphere. -/
def sphereHeight (x : Sphere) : ℝ := (x : Ambient) 2

theorem continuous_sphereHeight : Continuous sphereHeight := by
  exact (continuous_apply 2).comp continuous_subtype_val

/-- Uniform probability measure on the height interval `(-1,1]`. -/
noncomputable def uniformHeightMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / 2) • volume.restrict (Set.Ioc (-1) 1)

/-- The geometric height-marginal statement for normalized surface area. -/
def HasUniformHeightMarginal : Prop :=
  Measure.map sphereHeight sphereAreaProbability = uniformHeightMeasure

/-- CDF of the uniform probability measure on `[-1,1]`.  `ofReal` performs
the lower clipping at zero, while `min a 1` performs the upper clipping. -/
noncomputable def uniformHeightCDF (a : ℝ) : ENNReal :=
  ENNReal.ofReal ((min a 1 + 1) / 2)

theorem uniformHeightMeasure_Iic (a : ℝ) :
    uniformHeightMeasure (Set.Iic a) = uniformHeightCDF a := by
  rw [uniformHeightMeasure, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic a ∩ Set.Ioc (-1 : ℝ) 1 = Set.Ioc (-1) (min a 1) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨hza, hzLower, hzOne⟩
      exact ⟨hzLower, le_min hza hzOne⟩
    · rintro ⟨hzLower, hzMin⟩
      exact ⟨hzMin.trans (min_le_left a 1), hzLower,
        hzMin.trans (min_le_right a 1)⟩
  rw [hset, Real.volume_Ioc]
  unfold uniformHeightCDF
  simp only [smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

/-- Radial cone inside the unit ball whose directions have height at most
`a`. -/
def lowerHeightCone (a : ℝ) : Set Ambient :=
  Set.Ioo (0 : ℝ) 1 •
    ((fun x : Sphere ↦ (x : Ambient)) '' {x | sphereHeight x ≤ a})

theorem sphereHeight_mem_Icc (x : Sphere) : sphereHeight x ∈ Set.Icc (-1 : ℝ) 1 := by
  have hsum := x.property
  change (x : Ambient) ∈ Metric.sphere (0 : Ambient) 1 at hsum
  rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at hsum
  change (∑ i, (x : Ambient) i ^ 2) = 1 ^ 2 at hsum
  norm_num at hsum
  have hterm : (x : Ambient) 2 ^ 2 ≤ ∑ i, (x : Ambient) i ^ 2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg ((x : Ambient) i))
      (Finset.mem_univ 2)
  constructor <;> simp only [sphereHeight] <;> nlinarith

theorem lowerHeightCone_eq_empty {a : ℝ} (ha : a < -1) :
    lowerHeightCone a = ∅ := by
  have hdirections : {x : Sphere | sphereHeight x ≤ a} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.not_mem_empty, iff_false]
    exact not_le_of_gt (ha.trans_le (sphereHeight_mem_Icc x).1)
  simp [lowerHeightCone, hdirections]

theorem lowerHeightCone_eq_puncturedBall {a : ℝ} (ha : 1 ≤ a) :
    lowerHeightCone a = Metric.ball (0 : Ambient) 1 \ Metric.closedBall 0 0 := by
  have hdirections : {x : Sphere | sphereHeight x ≤ a} = Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact (sphereHeight_mem_Icc x).2.trans ha
  rw [lowerHeightCone, hdirections, Set.image_univ, Subtype.range_coe]
  simpa [Sphere] using
    (Ioo_smul_sphere_zero (E := Ambient) (a := (0 : ℝ)) (b := 1) (r := 1)
      (by norm_num) (by norm_num))

theorem uniformHeightCDF_eq_zero_of_lt_neg_one {a : ℝ} (ha : a < -1) :
    uniformHeightCDF a = 0 := by
  unfold uniformHeightCDF
  rw [min_eq_left (by linarith), ENNReal.ofReal_eq_zero]
  linarith

theorem uniformHeightCDF_eq_one_of_one_le {a : ℝ} (ha : 1 ≤ a) :
    uniformHeightCDF a = 1 := by
  unfold uniformHeightCDF
  rw [min_eq_right ha]
  norm_num

theorem lowerHeightCone_volume_of_lt_neg_one {a : ℝ} (ha : a < -1) :
    volume (lowerHeightCone a) =
      uniformHeightCDF a * volume (Metric.ball (0 : Ambient) 1) := by
  rw [lowerHeightCone_eq_empty ha, measure_empty,
    uniformHeightCDF_eq_zero_of_lt_neg_one ha]
  simp

theorem lowerHeightCone_volume_of_one_le {a : ℝ} (ha : 1 ≤ a) :
    volume (lowerHeightCone a) =
      uniformHeightCDF a * volume (Metric.ball (0 : Ambient) 1) := by
  rw [lowerHeightCone_eq_puncturedBall ha, Metric.closedBall_zero,
    measure_diff_null (measure_singleton _), uniformHeightCDF_eq_one_of_one_le ha]
  simp

/-- Cartesian description of the radial cone: away from the origin, its
directional height bound is the homogeneous inequality `v₂ ≤ a ‖v‖`. -/
def lowerHeightRegion (a : ℝ) : Set Ambient :=
  (Metric.ball (0 : Ambient) 1 \ {0}) ∩ {v | v 2 ≤ a * ‖v‖}

theorem lowerHeightCone_eq_region (a : ℝ) :
    lowerHeightCone a = lowerHeightRegion a := by
  ext v
  constructor
  · rintro ⟨t, ht, w, ⟨x, hx, rfl⟩, rfl⟩
    have hxnorm : ‖(x : Ambient)‖ = 1 := norm_eq_of_mem_sphere x
    have hvball : t • (x : Ambient) ∈ Metric.ball (0 : Ambient) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht.1, hxnorm, mul_one]
      exact ht.2
    have hxne : (x : Ambient) ≠ 0 := by
      rw [← norm_ne_zero_iff, hxnorm]
      norm_num
    have hvne : t • (x : Ambient) ≠ 0 := smul_ne_zero ht.1.ne' hxne
    refine ⟨⟨hvball, by simpa using hvne⟩, ?_⟩
    change (t • (x : Ambient)) 2 ≤ a * ‖t • (x : Ambient)‖
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, hxnorm, mul_one]
    simpa [sphereHeight, smul_eq_mul, mul_comm] using
      (mul_le_mul_of_nonneg_left hx ht.1.le)
  · rintro ⟨⟨hvball, hvzero⟩, hvheight⟩
    have hvne : v ≠ 0 := by simpa using hvzero
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    let x : Sphere := ⟨‖v‖⁻¹ • v, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hvnorm), inv_mul_cancel₀ hvnorm.ne']⟩
    have hxheight : sphereHeight x ≤ a := by
      change (‖v‖⁻¹ • v) 2 ≤ a
      rw [Pi.smul_apply]
      have hscaled := mul_le_mul_of_nonneg_left hvheight (inv_nonneg.mpr hvnorm.le)
      calc
        ‖v‖⁻¹ • v 2 ≤ ‖v‖⁻¹ * (a * ‖v‖) := hscaled
        _ = a := by field_simp
    refine ⟨‖v‖, ?_, (x : Ambient), ⟨x, hxheight, rfl⟩, ?_⟩
    · constructor
      · exact hvnorm
      · simpa [Metric.mem_ball, dist_zero_left] using hvball
    · simp [x, smul_smul, hvnorm.ne']

theorem measurableSet_lowerHeightRegion (a : ℝ) :
    MeasurableSet (lowerHeightRegion a) := by
  unfold lowerHeightRegion
  apply (Metric.isOpen_ball.measurableSet.diff
    (measurableSet_singleton (0 : Ambient))).inter
  exact measurableSet_le (continuous_apply 2).measurable
    (measurable_const.mul continuous_norm.measurable)

theorem measurableSet_lowerHeightCone (a : ℝ) :
    MeasurableSet (lowerHeightCone a) := by
  rw [lowerHeightCone_eq_region]
  exact measurableSet_lowerHeightRegion a

/-- Volume-preserving coordinates which put the height coordinate first and
leave the two horizontal coordinates in their canonical order. -/
noncomputable def ambientHeightPlaneEquiv :
    Ambient ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
  (EuclideanSpace.measurableEquiv (Fin 3)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 2)

theorem ambientHeightPlaneEquiv_apply (v : Ambient) :
    ambientHeightPlaneEquiv v = (v 2, fun j ↦ v ((2 : Fin 3).succAbove j)) := by
  rfl

theorem ambientHeightPlaneEquiv_measurePreserving :
    MeasurePreserving ambientHeightPlaneEquiv := by
  exact (EuclideanSpace.volume_preserving_measurableEquiv (Fin 3)).trans
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 2)

theorem ambient_sqNorm_split (v : Ambient) :
    ‖v‖ ^ 2 = v 2 ^ 2 + ∑ j : Fin 2, v ((2 : Fin 3).succAbove j) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  · simp only [Real.norm_eq_abs, sq_abs]
    exact (2 : Fin 3).sum_univ_succAbove (fun i ↦ v i ^ 2)
  · positivity

def horizontalSqNorm (u : Fin 2 → ℝ) : ℝ :=
  ∑ j : Fin 2, u j ^ 2

def horizontalSqBall (q : ℝ) : Set (Fin 2 → ℝ) :=
  {u | horizontalSqNorm u < q}

theorem euclideanPlane_sqNorm (u : EuclideanSpace ℝ (Fin 2)) :
    ‖u‖ ^ 2 = horizontalSqNorm u := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  · simp [horizontalSqNorm, Real.norm_eq_abs, sq_abs]
  · positivity

theorem euclideanPlane_ball_preimage_horizontalSqBall {q : ℝ} (hq : 0 ≤ q) :
    (EuclideanSpace.measurableEquiv (Fin 2)) ⁻¹' horizontalSqBall q =
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt q) := by
  ext u
  rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
  change horizontalSqNorm u < q ↔ ‖u‖ < Real.sqrt q
  have hsqrt : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
  rw [← euclideanPlane_sqNorm]
  constructor <;> intro h
  · nlinarith [norm_nonneg u]
  · nlinarith [norm_nonneg u]

theorem volume_horizontalSqBall {q : ℝ} (hq : 0 ≤ q) :
    volume (horizontalSqBall q) = ENNReal.ofReal q * ENNReal.ofReal Real.pi := by
  rw [← (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2)).measure_preimage_equiv
    (horizontalSqBall q), euclideanPlane_ball_preimage_horizontalSqBall hq,
    EuclideanSpace.volume_ball_fin_two]
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg q) 2, Real.sq_sqrt hq]

/-- Adding the origin to the punctured radial cone does not change volume. -/
def lowerHeightSolid (a : ℝ) : Set Ambient :=
  Metric.ball (0 : Ambient) 1 ∩ {v | v 2 ≤ a * ‖v‖}

theorem lowerHeightRegion_eq_solid_diff (a : ℝ) :
    lowerHeightRegion a = lowerHeightSolid a \ {0} := by
  ext v
  simp only [lowerHeightRegion, lowerHeightSolid, Set.mem_inter_iff, Set.mem_diff,
    Set.mem_setOf_eq]
  tauto

theorem lowerHeightCone_volume_eq_solid (a : ℝ) :
    volume (lowerHeightCone a) = volume (lowerHeightSolid a) := by
  rw [lowerHeightCone_eq_region, lowerHeightRegion_eq_solid_diff,
    measure_diff_null (measure_singleton _)]

theorem ambient_norm_split (v : Ambient) :
    ‖v‖ = Real.sqrt
      (v 2 ^ 2 + horizontalSqNorm (fun j ↦ v ((2 : Fin 3).succAbove j))) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [Real.norm_eq_abs, sq_abs, horizontalSqNorm]
  exact (2 : Fin 3).sum_univ_succAbove (fun i ↦ v i ^ 2)

def slicedLowerHeightSolid (a : ℝ) : Set (ℝ × (Fin 2 → ℝ)) :=
  {p | p.1 ^ 2 + horizontalSqNorm p.2 < 1 ∧
    p.1 ≤ a * Real.sqrt (p.1 ^ 2 + horizontalSqNorm p.2)}

theorem ambientHeightPlaneEquiv_preimage_slicedLowerHeightSolid (a : ℝ) :
    ambientHeightPlaneEquiv ⁻¹' slicedLowerHeightSolid a = lowerHeightSolid a := by
  ext v
  rw [Set.mem_preimage]
  simp only [slicedLowerHeightSolid, lowerHeightSolid, Set.mem_setOf_eq,
    Set.mem_inter_iff, ambientHeightPlaneEquiv_apply]
  rw [Metric.mem_ball, dist_zero_right, ambient_norm_split]
  have hq : 0 ≤ v 2 ^ 2 +
      horizontalSqNorm (fun j ↦ v ((2 : Fin 3).succAbove j)) := by
    unfold horizontalSqNorm
    positivity
  have hsqrt : 0 ≤ Real.sqrt
      (v 2 ^ 2 + horizontalSqNorm (fun j ↦ v ((2 : Fin 3).succAbove j))) :=
    Real.sqrt_nonneg _
  have hsquare : Real.sqrt
      (v 2 ^ 2 + horizontalSqNorm (fun j ↦ v ((2 : Fin 3).succAbove j))) ^ 2 =
      v 2 ^ 2 + horizontalSqNorm (fun j ↦ v ((2 : Fin 3).succAbove j)) :=
    Real.sq_sqrt hq
  constructor
  · rintro ⟨hball, hheight⟩
    exact ⟨by nlinarith, hheight⟩
  · rintro ⟨hball, hheight⟩
    exact ⟨by nlinarith, hheight⟩

theorem measurableSet_lowerHeightSolid (a : ℝ) :
    MeasurableSet (lowerHeightSolid a) := by
  unfold lowerHeightSolid
  exact Metric.isOpen_ball.measurableSet.inter <|
    measurableSet_le (continuous_apply 2).measurable
      (measurable_const.mul continuous_norm.measurable)

theorem measurableSet_slicedLowerHeightSolid (a : ℝ) :
    MeasurableSet (slicedLowerHeightSolid a) := by
  apply ambientHeightPlaneEquiv.measurableSet_preimage.mp
  rw [ambientHeightPlaneEquiv_preimage_slicedLowerHeightSolid]
  exact measurableSet_lowerHeightSolid a

theorem lowerHeightCone_volume_eq_sliced (a : ℝ) :
    volume (lowerHeightCone a) = volume (slicedLowerHeightSolid a) := by
  rw [lowerHeightCone_volume_eq_solid]
  calc
    volume (lowerHeightSolid a) =
        volume (ambientHeightPlaneEquiv ⁻¹' slicedLowerHeightSolid a) := by
          rw [ambientHeightPlaneEquiv_preimage_slicedLowerHeightSolid]
    _ = volume (slicedLowerHeightSolid a) :=
      ambientHeightPlaneEquiv_measurePreserving.measure_preimage_equiv _

def slicedUpperHeightSolid (a : ℝ) : Set (ℝ × (Fin 2 → ℝ)) :=
  {p | p.1 ^ 2 + horizontalSqNorm p.2 < 1 ∧
    a * Real.sqrt (p.1 ^ 2 + horizontalSqNorm p.2) < p.1}

noncomputable def upperConeSectionSq (a z : ℝ) : ℝ :=
  ((1 - a ^ 2) / a ^ 2) * z ^ 2

theorem slicedUpperHeightSolid_section_of_nonpos {a z : ℝ} (ha : 0 ≤ a)
    (hz : z ≤ 0) :
    Prod.mk z ⁻¹' slicedUpperHeightSolid a = ∅ := by
  ext u
  simp only [Set.mem_preimage, slicedUpperHeightSolid, Set.mem_setOf_eq,
    Set.not_mem_empty, iff_false]
  rintro ⟨_, hupper⟩
  have hsqrt : 0 ≤ Real.sqrt (z ^ 2 + horizontalSqNorm u) := Real.sqrt_nonneg _
  nlinarith

theorem slicedUpperHeightSolid_section_of_one_le {a z : ℝ} (hz : 1 ≤ z) :
    Prod.mk z ⁻¹' slicedUpperHeightSolid a = ∅ := by
  ext u
  simp only [Set.mem_preimage, slicedUpperHeightSolid, Set.mem_setOf_eq,
    Set.not_mem_empty, iff_false]
  rintro ⟨hball, _⟩
  have hq : 0 ≤ horizontalSqNorm u := by
    unfold horizontalSqNorm
    positivity
  nlinarith

theorem slicedUpperHeightSolid_section_of_lt_a {a z : ℝ}
    (ha : 0 < a) (_ha1 : a < 1) (hz0 : 0 < z) (hza : z < a) :
    Prod.mk z ⁻¹' slicedUpperHeightSolid a = horizontalSqBall (upperConeSectionSq a z) := by
  ext u
  simp only [Set.mem_preimage, slicedUpperHeightSolid, Set.mem_setOf_eq,
    horizontalSqBall, upperConeSectionSq]
  let q := horizontalSqNorm u
  have hq : 0 ≤ q := by
    dsimp [q, horizontalSqNorm]
    positivity
  have hs : 0 ≤ z ^ 2 + q := by positivity
  have hsqrt : 0 ≤ Real.sqrt (z ^ 2 + q) := Real.sqrt_nonneg _
  have hsquare : Real.sqrt (z ^ 2 + q) ^ 2 = z ^ 2 + q := Real.sq_sqrt hs
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  constructor
  · rintro ⟨hball, hupper⟩
    change q < (1 - a ^ 2) / a ^ 2 * z ^ 2
    have hsquared0 : (a * Real.sqrt (z ^ 2 + q)) ^ 2 < z ^ 2 :=
      (sq_lt_sq₀ (mul_nonneg ha.le hsqrt) hz0.le).2 hupper
    have hsquared : a ^ 2 * (z ^ 2 + q) < z ^ 2 := by
      simpa [mul_pow, hsquare] using hsquared0
    rw [div_mul_eq_mul_div]
    exact (lt_div_iff₀ ha2).2 (by nlinarith)
  · intro hqbound
    change q < (1 - a ^ 2) / a ^ 2 * z ^ 2 at hqbound
    have hsquared : a ^ 2 * (z ^ 2 + q) < z ^ 2 := by
      rw [div_mul_eq_mul_div] at hqbound
      have := (lt_div_iff₀ ha2).1 hqbound
      nlinarith
    have hball : z ^ 2 + q < 1 := by
      have hzsq : z ^ 2 < a ^ 2 := by nlinarith
      apply (mul_lt_mul_left ha2).mp
      nlinarith
    refine ⟨hball, ?_⟩
    apply (sq_lt_sq₀ (mul_nonneg ha.le hsqrt) hz0.le).mp
    simpa [mul_pow, hsquare] using hsquared

theorem slicedUpperHeightSolid_section_of_a_le {a z : ℝ}
    (ha : 0 < a) (haz : a ≤ z) (_hz1 : z < 1) :
    Prod.mk z ⁻¹' slicedUpperHeightSolid a = horizontalSqBall (1 - z ^ 2) := by
  ext u
  simp only [Set.mem_preimage, slicedUpperHeightSolid, Set.mem_setOf_eq,
    horizontalSqBall]
  let q := horizontalSqNorm u
  have hq : 0 ≤ q := by
    dsimp [q, horizontalSqNorm]
    positivity
  have hs : 0 ≤ z ^ 2 + q := by positivity
  have hsqrt : 0 ≤ Real.sqrt (z ^ 2 + q) := Real.sqrt_nonneg _
  have hsquare : Real.sqrt (z ^ 2 + q) ^ 2 = z ^ 2 + q := Real.sq_sqrt hs
  constructor
  · intro h
    nlinarith [h.1]
  · intro hball
    refine ⟨by nlinarith, ?_⟩
    have hsqrt1 : Real.sqrt (z ^ 2 + q) < 1 := by nlinarith
    nlinarith

theorem continuous_horizontalSqNorm : Continuous horizontalSqNorm := by
  unfold horizontalSqNorm
  fun_prop

theorem measurableSet_slicedUpperHeightSolid (a : ℝ) :
    MeasurableSet (slicedUpperHeightSolid a) := by
  unfold slicedUpperHeightSolid
  have hsum : Continuous (fun p : ℝ × (Fin 2 → ℝ) ↦
      p.1 ^ 2 + horizontalSqNorm p.2) :=
    (continuous_fst.pow 2).add (continuous_horizontalSqNorm.comp continuous_snd)
  exact (measurableSet_lt hsum.measurable measurable_const).inter
    (measurableSet_lt
      (measurable_const.mul (Real.continuous_sqrt.comp hsum).measurable)
      continuous_fst.measurable)

theorem volume_slicedUpperHeightSolid_eq_lintegral (a : ℝ) :
    volume (slicedUpperHeightSolid a) =
      ∫⁻ z : ℝ, volume (Prod.mk z ⁻¹' slicedUpperHeightSolid a) := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply (measurableSet_slicedUpperHeightSolid a)]

theorem upperConeSectionSq_nonneg {a z : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    0 ≤ upperConeSectionSq a z := by
  unfold upperConeSectionSq
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have ha2le : a ^ 2 ≤ 1 := by nlinarith
  exact mul_nonneg (div_nonneg (by nlinarith) (sq_nonneg a)) (sq_nonneg z)

theorem volume_slicedUpperHeightSolid_split {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    volume (slicedUpperHeightSolid a) =
      (∫⁻ z : ℝ in Set.Ioo 0 a,
        ENNReal.ofReal (upperConeSectionSq a z) * ENNReal.ofReal Real.pi) +
      (∫⁻ z : ℝ in Set.Ico a 1,
        ENNReal.ofReal (1 - z ^ 2) * ENNReal.ofReal Real.pi) := by
  rw [volume_slicedUpperHeightSolid_eq_lintegral]
  let f : ℝ → ENNReal := fun z ↦
    ENNReal.ofReal (upperConeSectionSq a z) * ENNReal.ofReal Real.pi
  let g : ℝ → ENNReal := fun z ↦
    ENNReal.ofReal (1 - z ^ 2) * ENNReal.ofReal Real.pi
  have hsections : (fun z : ℝ ↦ volume (Prod.mk z ⁻¹' slicedUpperHeightSolid a)) =
      fun z ↦ (Set.Ioo 0 a).indicator f z + (Set.Ico a 1).indicator g z := by
    funext z
    by_cases hz0 : z ≤ 0
    · rw [slicedUpperHeightSolid_section_of_nonpos ha.le hz0, measure_empty]
      rw [Set.indicator_of_not_mem (by simp [hz0])]
      rw [Set.indicator_of_not_mem (by
        intro hzmem
        exact (not_le_of_gt ha) (hzmem.1.trans hz0))]
      simp
    have hz0' : 0 < z := lt_of_not_ge hz0
    by_cases hza : z < a
    · rw [slicedUpperHeightSolid_section_of_lt_a ha ha1 hz0' hza,
        volume_horizontalSqBall (upperConeSectionSq_nonneg ha ha1)]
      simp [f, g, Set.indicator_of_mem, hz0', hza, not_le.mpr hza]
    have haz : a ≤ z := le_of_not_gt hza
    by_cases hz1 : z < 1
    · rw [slicedUpperHeightSolid_section_of_a_le ha haz hz1,
        volume_horizontalSqBall (by nlinarith [sq_nonneg z] : 0 ≤ 1 - z ^ 2)]
      simp [f, g, Set.indicator_of_mem, hz0', haz, hz1, hza]
    have hz1' : 1 ≤ z := le_of_not_gt hz1
    · rw [slicedUpperHeightSolid_section_of_one_le hz1', measure_empty]
      rw [Set.indicator_of_not_mem (by
        intro hzmem
        exact hza hzmem.2)]
      rw [Set.indicator_of_not_mem (by
        intro hzmem
        exact (not_lt_of_ge hz1') hzmem.2)]
      simp
  rw [hsections]
  have hf : Measurable f := by
    apply Measurable.mul
    · exact (ENNReal.continuous_ofReal.comp <| by
        unfold upperConeSectionSq
        fun_prop).measurable
    · exact measurable_const
  have hif : Measurable ((Set.Ioo 0 a).indicator f) :=
    hf.indicator measurableSet_Ioo
  rw [lintegral_add_left hif, lintegral_indicator measurableSet_Ioo,
    lintegral_indicator measurableSet_Ico]

theorem lintegral_ofReal_const_mul_sq_Ioo {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) :
    (∫⁻ z : ℝ in Set.Ioo 0 b, ENNReal.ofReal (c * z ^ 2)) =
      ENNReal.ofReal (c * b ^ 3 / 3) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hint : IntervalIntegrable (fun z : ℝ ↦ c * z ^ 2) volume 0 b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 b
  rw [← ofReal_integral_eq_lintegral_ofReal hint.1]
  · rw [← intervalIntegral.integral_of_le hb,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    congr 1
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    positivity

theorem lintegral_ofReal_one_sub_sq_Ico {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫⁻ z : ℝ in Set.Ico a 1, ENNReal.ofReal (1 - z ^ 2)) =
      ENNReal.ofReal (2 / 3 - a + a ^ 3 / 3) := by
  rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
  have hint : IntervalIntegrable (fun z : ℝ ↦ 1 - z ^ 2) volume a 1 :=
    (continuous_const.sub (continuous_id.pow 2)).intervalIntegrable a 1
  rw [← ofReal_integral_eq_lintegral_ofReal hint.1]
  · rw [← intervalIntegral.integral_of_le ha1,
      intervalIntegral.integral_sub, intervalIntegral.integral_const,
      integral_pow]
    norm_num
    ring_nf
    · exact continuous_const.intervalIntegrable a 1
    · exact (continuous_id.pow 2).intervalIntegrable a 1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    rcases hz with ⟨hza, hz1⟩
    have hz0 : 0 ≤ z := ha.trans hza.le
    have hzsq : z ^ 2 ≤ (1 : ℝ) ^ 2 := (sq_le_sq₀ hz0 zero_le_one).2 hz1
    change (0 : ℝ) ≤ 1 - z ^ 2
    nlinarith

theorem volume_slicedUpperHeightSolid {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    volume (slicedUpperHeightSolid a) =
      ENNReal.ofReal (2 * Real.pi / 3 * (1 - a)) := by
  rw [volume_slicedUpperHeightSolid_split ha ha1]
  have hk : 0 ≤ (1 - a ^ 2) / a ^ 2 := by
    exact div_nonneg (by nlinarith [sq_nonneg a]) (sq_nonneg a)
  have hfmeas : Measurable (fun z : ℝ ↦ ENNReal.ofReal (upperConeSectionSq a z)) :=
    (ENNReal.continuous_ofReal.comp <| by
      unfold upperConeSectionSq
      fun_prop).measurable
  have hgmeas : Measurable (fun z : ℝ ↦ ENNReal.ofReal (1 - z ^ 2)) :=
    (ENNReal.continuous_ofReal.comp <| by fun_prop).measurable
  rw [lintegral_mul_const (ENNReal.ofReal Real.pi) hfmeas,
    lintegral_mul_const (ENNReal.ofReal Real.pi) hgmeas]
  change
    (∫⁻ z : ℝ in Set.Ioo 0 a,
        ENNReal.ofReal (((1 - a ^ 2) / a ^ 2) * z ^ 2)) * ENNReal.ofReal Real.pi +
      (∫⁻ z : ℝ in Set.Ico a 1,
        ENNReal.ofReal (1 - z ^ 2)) * ENNReal.ofReal Real.pi = _
  rw [lintegral_ofReal_const_mul_sq_Ioo hk ha.le,
    lintegral_ofReal_one_sub_sq_Ico ha.le ha1.le]
  have hpoly : 0 ≤ 2 / 3 - a + a ^ 3 / 3 := by
    have hfac : 0 ≤ (a - 1) ^ 2 * (a + 2) :=
      mul_nonneg (sq_nonneg (a - 1)) (by linarith)
    nlinarith
  have hfirst : 0 ≤ (1 - a ^ 2) / a ^ 2 * a ^ 3 / 3 := by positivity
  rw [← ENNReal.ofReal_mul (q := Real.pi) hfirst,
    ← ENNReal.ofReal_mul (q := Real.pi) hpoly,
    ← ENNReal.ofReal_add
      (mul_nonneg hfirst Real.pi_pos.le)
      (mul_nonneg hpoly Real.pi_pos.le)]
  congr 1
  field_simp
  ring

def upperHeightSolid (a : ℝ) : Set Ambient :=
  Metric.ball (0 : Ambient) 1 ∩ {v | a * ‖v‖ < v 2}

theorem ambientHeightPlaneEquiv_preimage_slicedUpperHeightSolid (a : ℝ) :
    ambientHeightPlaneEquiv ⁻¹' slicedUpperHeightSolid a = upperHeightSolid a := by
  ext v
  rw [Set.mem_preimage]
  simp only [slicedUpperHeightSolid, upperHeightSolid, Set.mem_setOf_eq,
    Set.mem_inter_iff, ambientHeightPlaneEquiv_apply]
  rw [Metric.mem_ball, dist_zero_right, ambient_norm_split]
  have hq : 0 ≤ v 2 ^ 2 +
      horizontalSqNorm (fun j ↦ v ((2 : Fin 3).succAbove j)) := by
    unfold horizontalSqNorm
    positivity
  have hsqrt : 0 ≤ Real.sqrt
      (v 2 ^ 2 + horizontalSqNorm (fun j ↦ v ((2 : Fin 3).succAbove j))) :=
    Real.sqrt_nonneg _
  have hsquare : Real.sqrt
      (v 2 ^ 2 + horizontalSqNorm (fun j ↦ v ((2 : Fin 3).succAbove j))) ^ 2 =
      v 2 ^ 2 + horizontalSqNorm (fun j ↦ v ((2 : Fin 3).succAbove j)) :=
    Real.sq_sqrt hq
  constructor
  · rintro ⟨hball, hheight⟩
    exact ⟨by nlinarith, hheight⟩
  · rintro ⟨hball, hheight⟩
    exact ⟨by nlinarith, hheight⟩

theorem measurableSet_upperHeightSolid (a : ℝ) : MeasurableSet (upperHeightSolid a) := by
  unfold upperHeightSolid
  exact Metric.isOpen_ball.measurableSet.inter <|
    measurableSet_lt (measurable_const.mul continuous_norm.measurable)
      (continuous_apply 2).measurable

theorem upperHeightSolid_volume_eq_sliced (a : ℝ) :
    volume (upperHeightSolid a) = volume (slicedUpperHeightSolid a) := by
  calc
    volume (upperHeightSolid a) =
        volume (ambientHeightPlaneEquiv ⁻¹' slicedUpperHeightSolid a) := by
          rw [ambientHeightPlaneEquiv_preimage_slicedUpperHeightSolid]
    _ = volume (slicedUpperHeightSolid a) :=
      ambientHeightPlaneEquiv_measurePreserving.measure_preimage_equiv _

theorem lowerHeightSolid_union_upperHeightSolid (a : ℝ) :
    lowerHeightSolid a ∪ upperHeightSolid a = Metric.ball (0 : Ambient) 1 := by
  ext v
  simp only [lowerHeightSolid, upperHeightSolid, Set.mem_union, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro (⟨hball, _⟩ | ⟨hball, _⟩) <;> exact hball
  · intro hball
    by_cases hheight : v 2 ≤ a * ‖v‖
    · exact Or.inl ⟨hball, hheight⟩
    · exact Or.inr ⟨hball, lt_of_not_ge hheight⟩

theorem lowerHeightSolid_disjoint_upperHeightSolid (a : ℝ) :
    Disjoint (lowerHeightSolid a) (upperHeightSolid a) := by
  rw [Set.disjoint_left]
  intro v hlower hupper
  have hl : v 2 ≤ a * ‖v‖ := hlower.2
  have hu : a * ‖v‖ < v 2 := hupper.2
  exact (not_lt_of_ge hl) hu

theorem ball_volume_eq_lower_add_upper (a : ℝ) :
    volume (Metric.ball (0 : Ambient) 1) =
      volume (lowerHeightSolid a) + volume (upperHeightSolid a) := by
  rw [← lowerHeightSolid_union_upperHeightSolid a,
    measure_union (lowerHeightSolid_disjoint_upperHeightSolid a)
      (measurableSet_upperHeightSolid a)]

theorem lowerHeightCone_volume_of_pos_lt_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    volume (lowerHeightCone a) = ENNReal.ofReal (2 * Real.pi / 3 * (1 + a)) := by
  rw [lowerHeightCone_volume_eq_solid]
  have hupper : volume (upperHeightSolid a) =
      ENNReal.ofReal (2 * Real.pi / 3 * (1 - a)) := by
    rw [upperHeightSolid_volume_eq_sliced, volume_slicedUpperHeightSolid ha ha1]
  have hupperTop : volume (upperHeightSolid a) ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (Set.inter_subset_left : upperHeightSolid a ⊆
      Metric.ball (0 : Ambient) 1)).trans_lt measure_ball_lt_top
  apply (ENNReal.add_left_inj hupperTop).mp
  rw [← ball_volume_eq_lower_add_upper a, hupper,
    EuclideanSpace.volume_ball_fin_three]
  norm_num
  have hleft : 0 ≤ 2 * Real.pi / 3 * (1 + a) := by positivity
  have hright : 0 ≤ 2 * Real.pi / 3 * (1 - a) :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (by norm_num))
      (by linarith)
  rw [← ENNReal.ofReal_add hleft hright]
  congr 1
  ring

theorem slicedUpperHeightSolid_zero_section_of_pos {z : ℝ}
    (hz0 : 0 < z) (_hz1 : z < 1) :
    Prod.mk z ⁻¹' slicedUpperHeightSolid 0 = horizontalSqBall (1 - z ^ 2) := by
  ext u
  simp only [Set.mem_preimage, slicedUpperHeightSolid, Set.mem_setOf_eq,
    horizontalSqBall, zero_mul]
  constructor
  · intro h
    nlinarith [h.1]
  · intro h
    exact ⟨by nlinarith, hz0⟩

theorem volume_slicedUpperHeightSolid_zero :
    volume (slicedUpperHeightSolid 0) = ENNReal.ofReal (2 * Real.pi / 3) := by
  rw [volume_slicedUpperHeightSolid_eq_lintegral]
  let g : ℝ → ENNReal := fun z ↦
    ENNReal.ofReal (1 - z ^ 2) * ENNReal.ofReal Real.pi
  have hsections : (fun z : ℝ ↦ volume (Prod.mk z ⁻¹' slicedUpperHeightSolid 0)) =
      fun z ↦ (Set.Ioo 0 1).indicator g z := by
    funext z
    by_cases hz0 : z ≤ 0
    · rw [slicedUpperHeightSolid_section_of_nonpos (a := 0) (by norm_num) hz0,
        measure_empty, Set.indicator_of_not_mem (by simp [hz0])]
    have hz0' : 0 < z := lt_of_not_ge hz0
    by_cases hz1 : z < 1
    · rw [slicedUpperHeightSolid_zero_section_of_pos hz0' hz1,
        volume_horizontalSqBall (by nlinarith [sq_nonneg z] : 0 ≤ 1 - z ^ 2)]
      rw [Set.indicator_of_mem (by exact ⟨hz0', hz1⟩)]
    have hz1' : 1 ≤ z := le_of_not_gt hz1
    · rw [slicedUpperHeightSolid_section_of_one_le hz1', measure_empty,
        Set.indicator_of_not_mem (by
          intro hzmem
          exact (not_lt_of_ge hz1') hzmem.2)]
  rw [hsections]
  rw [lintegral_indicator measurableSet_Ioo]
  change (∫⁻ z : ℝ in Set.Ioo 0 1,
    ENNReal.ofReal (1 - z ^ 2) * ENNReal.ofReal Real.pi) = _
  have hg : Measurable (fun z : ℝ ↦ ENNReal.ofReal (1 - z ^ 2)) :=
    (ENNReal.continuous_ofReal.comp (by fun_prop)).measurable
  rw [lintegral_mul_const (ENNReal.ofReal Real.pi) hg]
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ico,
    lintegral_ofReal_one_sub_sq_Ico (by norm_num) (by norm_num)]
  norm_num
  rw [← ENNReal.ofReal_mul (q := Real.pi) (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  congr 1
  ring

theorem lowerHeightCone_volume_zero :
    volume (lowerHeightCone 0) = ENNReal.ofReal (2 * Real.pi / 3) := by
  rw [lowerHeightCone_volume_eq_solid]
  have hupper : volume (upperHeightSolid 0) = ENNReal.ofReal (2 * Real.pi / 3) := by
    rw [upperHeightSolid_volume_eq_sliced, volume_slicedUpperHeightSolid_zero]
  have hupperTop : volume (upperHeightSolid 0) ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (Set.inter_subset_left : upperHeightSolid 0 ⊆
      Metric.ball (0 : Ambient) 1)).trans_lt measure_ball_lt_top
  apply (ENNReal.add_left_inj hupperTop).mp
  rw [← ball_volume_eq_lower_add_upper 0, hupper,
    EuclideanSpace.volume_ball_fin_three]
  norm_num
  rw [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 2 * Real.pi / 3)
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi / 3)]
  congr 1
  ring

def horizontalSqLevel (q : ℝ) : Set (Fin 2 → ℝ) :=
  {u | horizontalSqNorm u = q}

theorem euclideanPlane_sphere_preimage_horizontalSqLevel {q : ℝ} (hq : 0 ≤ q) :
    (EuclideanSpace.measurableEquiv (Fin 2)) ⁻¹' horizontalSqLevel q =
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt q) := by
  ext u
  rw [Set.mem_preimage, Metric.mem_sphere, dist_zero_right]
  change horizontalSqNorm u = q ↔ ‖u‖ = Real.sqrt q
  rw [← euclideanPlane_sqNorm]
  have hu : 0 ≤ ‖u‖ := norm_nonneg u
  have hsqrt : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  constructor <;> intro h
  · nlinarith
  · nlinarith

theorem volume_horizontalSqLevel (q : ℝ) : volume (horizontalSqLevel q) = 0 := by
  by_cases hq : 0 ≤ q
  · rw [← (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2)).measure_preimage_equiv
      (horizontalSqLevel q), euclideanPlane_sphere_preimage_horizontalSqLevel hq,
      Measure.addHaar_sphere]
  · have hempty : horizontalSqLevel q = ∅ := by
      ext u
      simp only [horizontalSqLevel, Set.mem_setOf_eq, Set.not_mem_empty, iff_false]
      intro hu
      have hnonneg : 0 ≤ horizontalSqNorm u := by
        unfold horizontalSqNorm
        positivity
      linarith
    rw [hempty, measure_empty]

def slicedHeightBoundary (a : ℝ) : Set (ℝ × (Fin 2 → ℝ)) :=
  {p | p.1 ^ 2 + horizontalSqNorm p.2 < 1 ∧
    p.1 = a * Real.sqrt (p.1 ^ 2 + horizontalSqNorm p.2)}

theorem measurableSet_slicedHeightBoundary (a : ℝ) :
    MeasurableSet (slicedHeightBoundary a) := by
  unfold slicedHeightBoundary
  have hsum : Continuous (fun p : ℝ × (Fin 2 → ℝ) ↦
      p.1 ^ 2 + horizontalSqNorm p.2) :=
    (continuous_fst.pow 2).add (continuous_horizontalSqNorm.comp continuous_snd)
  exact (measurableSet_lt hsum.measurable measurable_const).inter
    (measurableSet_eq_fun continuous_fst.measurable
      (measurable_const.mul (Real.continuous_sqrt.comp hsum).measurable))

theorem slicedHeightBoundary_section_subset_level {a z : ℝ} (ha : a ≠ 0) :
    Prod.mk z ⁻¹' slicedHeightBoundary a ⊆
      horizontalSqLevel (((1 - a ^ 2) / a ^ 2) * z ^ 2) := by
  intro u hu
  rcases hu with ⟨_, heq⟩
  change horizontalSqNorm u = ((1 - a ^ 2) / a ^ 2) * z ^ 2
  have hs : 0 ≤ z ^ 2 + horizontalSqNorm u := by
    unfold horizontalSqNorm
    positivity
  have hsquare := Real.sq_sqrt hs
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  field_simp
  nlinarith [congrArg (fun t : ℝ ↦ t ^ 2) heq]

theorem volume_slicedHeightBoundary {a : ℝ} (ha : a ≠ 0) :
    volume (slicedHeightBoundary a) = 0 := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply (measurableSet_slicedHeightBoundary a)]
  apply (lintegral_eq_zero_iff
    (measurable_measure_prodMk_left (measurableSet_slicedHeightBoundary a))).2
  filter_upwards [] with z
  exact measure_mono_null (slicedHeightBoundary_section_subset_level ha)
    (volume_horizontalSqLevel _)

def heightBoundary (a : ℝ) : Set Ambient :=
  Metric.ball (0 : Ambient) 1 ∩ {v | v 2 = a * ‖v‖}

theorem ambientHeightPlaneEquiv_preimage_slicedHeightBoundary (a : ℝ) :
    ambientHeightPlaneEquiv ⁻¹' slicedHeightBoundary a = heightBoundary a := by
  ext v
  rw [Set.mem_preimage]
  simp only [slicedHeightBoundary, heightBoundary, Set.mem_setOf_eq,
    Set.mem_inter_iff, ambientHeightPlaneEquiv_apply]
  rw [Metric.mem_ball, dist_zero_right, ambient_norm_split]
  have hq : 0 ≤ v 2 ^ 2 +
      horizontalSqNorm (fun j ↦ v ((2 : Fin 3).succAbove j)) := by
    unfold horizontalSqNorm
    positivity
  have hsqrt := Real.sqrt_nonneg
    (v 2 ^ 2 + horizontalSqNorm (fun j ↦ v ((2 : Fin 3).succAbove j)))
  have hsquare := Real.sq_sqrt hq
  constructor
  · rintro ⟨hball, heq⟩
    exact ⟨by nlinarith, heq⟩
  · rintro ⟨hball, heq⟩
    exact ⟨by nlinarith, heq⟩

theorem volume_heightBoundary {a : ℝ} (ha : a ≠ 0) : volume (heightBoundary a) = 0 := by
  rw [← ambientHeightPlaneEquiv_preimage_slicedHeightBoundary]
  rw [ambientHeightPlaneEquiv_measurePreserving.measure_preimage_equiv,
    volume_slicedHeightBoundary ha]

def strictLowerHeightSolid (a : ℝ) : Set Ambient :=
  Metric.ball (0 : Ambient) 1 ∩ {v | v 2 < a * ‖v‖}

theorem measurableSet_strictLowerHeightSolid (a : ℝ) :
    MeasurableSet (strictLowerHeightSolid a) := by
  unfold strictLowerHeightSolid
  exact Metric.isOpen_ball.measurableSet.inter <|
    measurableSet_lt (continuous_apply 2).measurable
      (measurable_const.mul continuous_norm.measurable)

theorem neg_preimage_upperHeightSolid (b : ℝ) :
    (fun v : Ambient ↦ -v) ⁻¹' upperHeightSolid b = strictLowerHeightSolid (-b) := by
  ext v
  simp only [Set.mem_preimage, upperHeightSolid, strictLowerHeightSolid,
    Set.mem_inter_iff, Set.mem_setOf_eq, norm_neg, Pi.neg_apply, neg_mul]
  rw [Metric.mem_ball, Metric.mem_ball, dist_zero_right, dist_zero_right, norm_neg]
  constructor
  · rintro ⟨hball, hheight⟩
    change b * ‖v‖ < -v 2 at hheight
    exact ⟨hball, by linarith⟩
  · rintro ⟨hball, hheight⟩
    change v 2 < -(b * ‖v‖) at hheight
    refine ⟨hball, ?_⟩
    change b * ‖v‖ < -v 2
    linarith

theorem strictLowerHeightSolid_volume_eq_upper (b : ℝ) :
    volume (strictLowerHeightSolid (-b)) = volume (upperHeightSolid b) := by
  rw [← neg_preimage_upperHeightSolid]
  exact (Measure.measurePreserving_neg volume).measure_preimage
    (measurableSet_upperHeightSolid b).nullMeasurableSet

theorem strictLower_union_boundary (a : ℝ) :
    strictLowerHeightSolid a ∪ heightBoundary a = lowerHeightSolid a := by
  ext v
  simp only [strictLowerHeightSolid, heightBoundary, lowerHeightSolid, Set.mem_union,
    Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro (⟨hball, hlt⟩ | ⟨hball, heq⟩)
    · exact ⟨hball, hlt.le⟩
    · exact ⟨hball, heq.le⟩
  · rintro ⟨hball, hle⟩
    rcases hle.lt_or_eq with hlt | heq
    · exact Or.inl ⟨hball, hlt⟩
    · exact Or.inr ⟨hball, heq⟩

theorem strictLower_disjoint_boundary (a : ℝ) :
    Disjoint (strictLowerHeightSolid a) (heightBoundary a) := by
  rw [Set.disjoint_left]
  intro v hstrict hboundary
  have hlt : v 2 < a * ‖v‖ := hstrict.2
  have heq : v 2 = a * ‖v‖ := hboundary.2
  exact hlt.ne heq

theorem lowerHeightSolid_volume_eq_strictLower {a : ℝ} (ha : a ≠ 0) :
    volume (lowerHeightSolid a) = volume (strictLowerHeightSolid a) := by
  rw [← strictLower_union_boundary a,
    measure_union (strictLower_disjoint_boundary a)
      (by
        unfold heightBoundary
        exact Metric.isOpen_ball.measurableSet.inter <|
          measurableSet_eq_fun (continuous_apply 2).measurable
            (measurable_const.mul continuous_norm.measurable)),
    volume_heightBoundary ha, add_zero]

theorem upperHeightSolid_one_eq_empty : upperHeightSolid 1 = ∅ := by
  ext v
  simp only [upperHeightSolid, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.not_mem_empty, iff_false]
  rintro ⟨_, hheight⟩
  have hsplit := ambient_sqNorm_split v
  have hhorizontal : 0 ≤ ∑ j : Fin 2, v ((2 : Fin 3).succAbove j) ^ 2 := by
    positivity
  have hv2sq : v 2 ^ 2 ≤ ‖v‖ ^ 2 := by nlinarith
  have hv2 : v 2 ≤ ‖v‖ := by nlinarith [norm_nonneg v]
  norm_num at hheight
  linarith

theorem lowerHeightCone_volume_of_neg {a : ℝ} (haLower : -1 ≤ a) (ha : a < 0) :
    volume (lowerHeightCone a) = ENNReal.ofReal (2 * Real.pi / 3 * (1 + a)) := by
  rw [lowerHeightCone_volume_eq_solid, lowerHeightSolid_volume_eq_strictLower ha.ne]
  have hb : 0 < -a := neg_pos.mpr ha
  by_cases haEnd : a = -1
  · subst a
    rw [show strictLowerHeightSolid (-1) = strictLowerHeightSolid (-(1 : ℝ)) by norm_num,
      strictLowerHeightSolid_volume_eq_upper, upperHeightSolid_one_eq_empty, measure_empty]
    norm_num
  have haStrict : -1 < a := lt_of_le_of_ne haLower (Ne.symm haEnd)
  have hb1 : -a < 1 := by linarith
  rw [show strictLowerHeightSolid a = strictLowerHeightSolid (-(-a)) by simp,
    strictLowerHeightSolid_volume_eq_upper, upperHeightSolid_volume_eq_sliced,
    volume_slicedUpperHeightSolid hb hb1]
  congr 1
  ring

theorem lowerHeightCone_volume_interior_explicit {a : ℝ}
    (haLower : -1 ≤ a) (haUpper : a < 1) :
    volume (lowerHeightCone a) = ENNReal.ofReal (2 * Real.pi / 3 * (1 + a)) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · exact lowerHeightCone_volume_of_neg haLower ha
  · subst a
    simpa using lowerHeightCone_volume_zero
  · exact lowerHeightCone_volume_of_pos_lt_one ha haUpper

/-- The remaining geometric volume identity.  Its right-hand side is the
volume fraction predicted by the uniform height distribution. -/
def HasCorrectLowerHeightConeVolume : Prop :=
  ∀ a : ℝ,
    volume (lowerHeightCone a) =
      uniformHeightCDF a * volume (Metric.ball (0 : Ambient) 1)

/-- The genuinely geometric part of the cone-volume formula.  Values outside
`[-1,1)` have already been settled by the empty/full cone arguments above. -/
def HasCorrectInteriorLowerHeightConeVolume : Prop :=
  ∀ a : ℝ, -1 ≤ a → a < 1 →
    volume (lowerHeightCone a) =
      uniformHeightCDF a * volume (Metric.ball (0 : Ambient) 1)

theorem hasCorrectInteriorLowerHeightConeVolume :
    HasCorrectInteriorLowerHeightConeVolume := by
  intro a haLower haUpper
  rw [lowerHeightCone_volume_interior_explicit haLower haUpper]
  have hmin : min a 1 = a := min_eq_left haUpper.le
  rw [uniformHeightCDF, hmin, EuclideanSpace.volume_ball_fin_three]
  norm_num
  have hcdf : 0 ≤ (a + 1) / 2 := by linarith
  rw [← ENNReal.ofReal_mul hcdf]
  congr 1
  ring

theorem hasCorrectLowerHeightConeVolume_of_interior
    (hinterior : HasCorrectInteriorLowerHeightConeVolume) :
    HasCorrectLowerHeightConeVolume := by
  intro a
  by_cases hlower : a < -1
  · exact lowerHeightCone_volume_of_lt_neg_one hlower
  by_cases hupper : 1 ≤ a
  · exact lowerHeightCone_volume_of_one_le hupper
  exact hinterior a (le_of_not_gt hlower) (lt_of_not_ge hupper)

theorem hasCorrectLowerHeightConeVolume : HasCorrectLowerHeightConeVolume :=
  hasCorrectLowerHeightConeVolume_of_interior hasCorrectInteriorLowerHeightConeVolume

theorem hasUniformHeightMarginal_of_coneVolume
    (hcone : HasCorrectLowerHeightConeVolume) : HasUniformHeightMarginal := by
  unfold HasUniformHeightMarginal
  let μ := Measure.map sphereHeight sphereAreaProbability
  have hμuniv : μ Set.univ = 1 := by
    change Measure.map sphereHeight sphereAreaProbability Set.univ = 1
    rw [Measure.map_apply continuous_sphereHeight.measurable MeasurableSet.univ]
    simp
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (by rw [hμuniv]; norm_num)
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply continuous_sphereHeight.measurable measurableSet_Iic,
    uniformHeightMeasure_Iic]
  change sphereAreaProbability {x : Sphere | sphereHeight x ≤ a} = uniformHeightCDF a
  unfold sphereAreaProbability
  rw [Measure.smul_apply]
  have hs : MeasurableSet {x : Sphere | sphereHeight x ≤ a} :=
    measurableSet_le continuous_sphereHeight.measurable measurable_const
  rw [Measure.toSphere_apply' volume hs]
  change (volume.toSphere (E := Ambient) Set.univ)⁻¹ *
      (Module.finrank ℝ Ambient * volume (lowerHeightCone a)) = uniformHeightCDF a
  rw [hcone a]
  rw [Measure.toSphere_apply_univ]
  calc
    (↑(Module.finrank ℝ Ambient) * volume (Metric.ball (0 : Ambient) 1))⁻¹ *
        (↑(Module.finrank ℝ Ambient) *
          (uniformHeightCDF a * volume (Metric.ball (0 : Ambient) 1))) =
      uniformHeightCDF a *
        ((↑(Module.finrank ℝ Ambient) * volume (Metric.ball (0 : Ambient) 1))⁻¹ *
          (↑(Module.finrank ℝ Ambient) * volume (Metric.ball (0 : Ambient) 1))) := by
            ac_rfl
    _ = uniformHeightCDF a := by
      rw [ENNReal.inv_mul_cancel]
      · simp
      · rw [← Measure.toSphere_apply_univ]
        exact sphereHaarMeasure_apply_univ_ne_zero
      · rw [← Measure.toSphere_apply_univ]
        exact measure_ne_top (volume.toSphere : Measure Sphere) Set.univ

theorem hasUniformHeightMarginal : HasUniformHeightMarginal :=
  hasUniformHeightMarginal_of_coneVolume hasCorrectLowerHeightConeVolume

/-- A globally continuous version of the north-pole distance kernel.  The
clipping is inactive on spherical heights. -/
noncomputable def clippedHeightKernel (α z : ℝ) : ℝ :=
  max (2 * (1 - z)) 0 ^ (α / 2)

theorem continuous_clippedHeightKernel {α : ℝ} (hα : 0 < α) :
    Continuous (clippedHeightKernel α) := by
  unfold clippedHeightKernel
  apply (continuous_const.mul (continuous_const.sub continuous_id)).max
      continuous_const |>.rpow continuous_const
  intro z
  by_cases hz : max (2 * (1 - z)) 0 = 0
  · exact Or.inr (by linarith)
  · exact Or.inl hz

theorem northPole_distancePower_eq_clippedHeightKernel
    (α : ℝ) (y : Sphere) :
    dist northPole y ^ α = clippedHeightKernel α (sphereHeight y) := by
  have hsum := y.property
  change (y : Ambient) ∈ Metric.sphere (0 : Ambient) 1 at hsum
  rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at hsum
  change (∑ i, (y : Ambient) i ^ 2) = 1 ^ 2 at hsum
  norm_num at hsum
  have hterm : (y : Ambient) 2 ^ 2 ≤ ∑ i, (y : Ambient) i ^ 2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg ((y : Ambient) i))
      (Finset.mem_univ 2)
  have hy : (y : Ambient) 2 ≤ 1 := by nlinarith
  have hbase : 0 ≤ 2 * (1 - sphereHeight y) := by
    simp only [sphereHeight]
    linarith
  rw [clippedHeightKernel, max_eq_left hbase]
  have hd : dist northPole y ^ 2 = 2 * (1 - sphereHeight y) := by
    simpa [sphereHeight] using northPole_dist_sq y
  rw [← hd]
  rw [show α = (2 : ℝ) * (α / 2) by ring, Real.rpow_mul dist_nonneg]
  norm_num [Real.rpow_natCast]

/-- Uniformity of the height marginal gives the claimed potential value at
the north pole. -/
theorem northPole_potential_of_uniform_height
    {α : ℝ} (hα : 0 < α) (hheight : HasUniformHeightMarginal) :
    ∫ y : Sphere, dist northPole y ^ α ∂sphereAreaProbability =
      2 ^ (α + 1) / (α + 2) := by
  simp_rw [northPole_distancePower_eq_clippedHeightKernel α]
  have hmap := MeasureTheory.integral_map
    (μ := sphereAreaProbability) (continuous_sphereHeight.measurable.aemeasurable)
    (continuous_clippedHeightKernel hα).aestronglyMeasurable
  rw [← hmap, hheight, uniformHeightMeasure, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2), smul_eq_mul]
  rw [show (∫ z : ℝ, clippedHeightKernel α z ∂volume.restrict (Set.Ioc (-1) 1)) =
      ∫ z : ℝ in (-1)..1, (2 * (1 - z)) ^ (α / 2) by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    rcases hz with ⟨hzLower, hzUpper⟩
    rw [clippedHeightKernel, max_eq_left]
    linarith]
  exact uniform_height_distancePower_integral hα

/-- A linear isometry of the ambient space restricted to the unit sphere. -/
noncomputable def sphereLinearIsometryMap
    (T : Ambient ≃ₗᵢ[ℝ] Ambient) (x : Sphere) : Sphere :=
  ⟨T x, by
    rw [Metric.mem_sphere, dist_zero_right]
    simp⟩

theorem continuous_sphereLinearIsometryMap (T : Ambient ≃ₗᵢ[ℝ] Ambient) :
    Continuous (sphereLinearIsometryMap T) := by
  exact (T.continuous.comp continuous_subtype_val).subtype_mk _

noncomputable def sphereLinearIsometryEquiv
    (T : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ᵐ Sphere where
  toEquiv :=
    { toFun := sphereLinearIsometryMap T
      invFun := sphereLinearIsometryMap T.symm
      left_inv := fun x ↦ Subtype.ext (T.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (T.apply_symm_apply x) }
  measurable_toFun := (continuous_sphereLinearIsometryMap T).measurable
  measurable_invFun := (continuous_sphereLinearIsometryMap T.symm).measurable

/-- Invariance of a spherical measure under every ambient linear isometry. -/
def IsOrthogonallyInvariant (μ : Measure Sphere) : Prop :=
  ∀ T : Ambient ≃ₗᵢ[ℝ] Ambient,
    Measure.map (sphereLinearIsometryEquiv T) μ = μ

/-- The weaker invariance property actually needed for transitivity: all
Householder reflections preserve the measure. -/
def IsReflectionInvariant (μ : Measure Sphere) : Prop :=
  ∀ v : Ambient,
    Measure.map (sphereLinearIsometryEquiv ((ℝ ∙ v)ᗮ.reflection)) μ = μ

theorem sphereCone_preimage (T : Ambient ≃ₗᵢ[ℝ] Ambient) (s : Set Sphere) :
    Set.Ioo (0 : ℝ) 1 •
        ((fun x : Sphere ↦ (x : Ambient)) ''
          (sphereLinearIsometryEquiv T ⁻¹' s)) =
      T ⁻¹' (Set.Ioo (0 : ℝ) 1 •
        ((fun x : Sphere ↦ (x : Ambient)) '' s)) := by
  ext q
  rw [← Set.image2_smul, ← Set.image2_smul]
  constructor
  · intro hq
    rcases Set.mem_image2.mp hq with ⟨r, hr, a, ⟨x, hx, rfl⟩, rfl⟩
    apply Set.mem_preimage.mpr
    apply Set.mem_image2.mpr
    refine ⟨r, hr, T x, ?_, by simp⟩
    exact ⟨sphereLinearIsometryEquiv T x, hx, rfl⟩
  · intro hq
    have hTq := Set.mem_preimage.mp hq
    rcases Set.mem_image2.mp hTq with ⟨r, hr, a, ⟨y, hy, rfl⟩, hry⟩
    apply Set.mem_image2.mpr
    refine ⟨r, hr, T.symm y, ?_, ?_⟩
    · refine ⟨sphereLinearIsometryEquiv T.symm y, ?_, rfl⟩
      change sphereLinearIsometryEquiv T (sphereLinearIsometryEquiv T.symm y) ∈ s
      have hcomp : sphereLinearIsometryEquiv T
          (sphereLinearIsometryEquiv T.symm y) = y := by
        apply Subtype.ext
        exact T.apply_symm_apply y
      rw [hcomp]
      exact hy
    · apply T.injective
      simpa using hry

theorem sphereAreaProbability_reflection_invariant :
    IsReflectionInvariant sphereAreaProbability := by
  intro v
  let K : Submodule ℝ Ambient := (ℝ ∙ v)ᗮ
  let T : Ambient ≃ₗᵢ[ℝ] Ambient := K.reflection
  change Measure.map (sphereLinearIsometryEquiv T) sphereAreaProbability =
    sphereAreaProbability
  ext s hs
  rw [Measure.map_apply (sphereLinearIsometryEquiv T).measurable hs]
  unfold sphereAreaProbability
  rw [Measure.smul_apply, Measure.smul_apply]
  congr 1
  rw [Measure.toSphere_apply' volume
      ((sphereLinearIsometryEquiv T).measurable hs),
    Measure.toSphere_apply' volume hs]
  rw [sphereCone_preimage]
  change _ * volume ((T.toLinearEquiv : Ambient → Ambient) ⁻¹'
      (Set.Ioo (0 : ℝ) 1 • ((fun x : Sphere ↦ (x : Ambient)) '' s))) = _
  rw [Measure.addHaar_preimage_linearEquiv volume T.toLinearEquiv]
  have hdet :
      |LinearMap.det (T.symm.toLinearEquiv : Ambient →ₗ[ℝ] Ambient)| = 1 := by
    change |LinearMap.det (K.reflection.toLinearMap)| = 1
    rw [Submodule.det_reflection]
    simp
  change _ * (ENNReal.ofReal
      |LinearMap.det (T.symm.toLinearEquiv : Ambient →ₗ[ℝ] Ambient)| * _) = _
  rw [hdet]
  norm_num

/-- Orthogonal invariance makes a distance-power potential constant; a
Householder reflection sends any chosen point to the north pole. -/
theorem sphere_potential_eq_northPole_of_invariant
    {α : ℝ} (μ : Measure Sphere) (hinv : IsReflectionInvariant μ)
    (x : Sphere) :
    ∫ y : Sphere, dist x y ^ α ∂μ =
      ∫ y : Sphere, dist northPole y ^ α ∂μ := by
  let R : Ambient ≃ₗᵢ[ℝ] Ambient :=
    (ℝ ∙ ((x : Ambient) - (northPole : Ambient)))ᗮ.reflection
  have hnorm : ‖(x : Ambient)‖ = ‖(northPole : Ambient)‖ := by
    rw [norm_eq_of_mem_sphere x, norm_eq_of_mem_sphere northPole]
  have hRx : R (x : Ambient) = (northPole : Ambient) := by
    exact Submodule.reflection_sub hnorm
  let e := sphereLinearIsometryEquiv R
  have heX : e x = northPole := by
    apply Subtype.ext
    exact hRx
  have hmap := MeasureTheory.integral_map_equiv e
    (μ := μ) (fun y : Sphere ↦ dist northPole y ^ α)
  rw [hinv ((x : Ambient) - (northPole : Ambient))] at hmap
  rw [hmap]
  apply integral_congr_ae
  filter_upwards with y
  change dist (x : Ambient) (y : Ambient) ^ α =
    dist (northPole : Ambient) (R (y : Ambient)) ^ α
  rw [← hRx, R.isometry.dist_eq]

/-- Surface area with total mass `N`, used as the reference measure in the
conditional-negative-definiteness comparison. -/
noncomputable def sphereReferenceMeasure (N : ℕ) : Measure Sphere :=
  N • sphereAreaProbability

@[simp] theorem sphereReferenceMeasure_apply_univ (N : ℕ) :
    sphereReferenceMeasure N Set.univ = N := by
  simp [sphereReferenceMeasure, Measure.add_apply]

/-- The normalized surface measure has constant distance-power potential
`J`.  The paper later evaluates `J` as `2^(α+1)/(α+2)`. -/
def HasConstantSpherePotential (α J : ℝ) : Prop :=
  ∀ x : Sphere,
    ∫ y : Sphere, dist x y ^ α ∂sphereAreaProbability = J

/-- The constant-potential formula reduced to the height marginal of
normalized surface area.  Reflection invariance and the one-dimensional
integral evaluation are fully discharged here. -/
theorem hasConstantSpherePotential_of_uniform_height
    {α : ℝ} (hα : 0 < α) (hheight : HasUniformHeightMarginal) :
    HasConstantSpherePotential α (2 ^ (α + 1) / (α + 2)) := by
  intro x
  rw [sphere_potential_eq_northPole_of_invariant sphereAreaProbability
    sphereAreaProbability_reflection_invariant x]
  exact northPole_potential_of_uniform_height hα hheight

theorem hasConstantSpherePotential {α : ℝ} (hα : 0 < α) :
    HasConstantSpherePotential α (2 ^ (α + 1) / (α + 2)) :=
  hasConstantSpherePotential_of_uniform_height hα hasUniformHeightMarginal

theorem measurePairEnergy_measure_sphereReference
    (N : ℕ) {α J : ℝ} (hpot : HasConstantSpherePotential α J)
    (μ : Measure Sphere) (hmass : μ Set.univ = N) :
    measurePairEnergy μ (sphereReferenceMeasure N) α = J * (N : ℝ) ^ 2 := by
  rw [sphereReferenceMeasure, ← Nat.cast_smul_eq_nsmul ENNReal,
    measurePairEnergy_smul_right]
  unfold measurePairEnergy kernelPairEnergy
  unfold HasConstantSpherePotential at hpot
  simp_rw [hpot]
  rw [integral_const]
  simp [Measure.real_def, hmass]
  ring

theorem measurePairEnergy_sphereReference_measure
    (N : ℕ) {α J : ℝ} (hα : 0 < α)
    (hpot : HasConstantSpherePotential α J)
    (μ : Measure Sphere) (hμ : μ Set.univ ≠ ⊤) (hmass : μ Set.univ = N) :
    measurePairEnergy (sphereReferenceMeasure N) μ α = J * (N : ℝ) ^ 2 := by
  rw [measurePairEnergy_comm hα _ _ (by simp) hμ]
  exact measurePairEnergy_measure_sphereReference N hpot μ hmass

theorem measurePairEnergy_sphereReference_self
    (N : ℕ) {α J : ℝ} (hpot : HasConstantSpherePotential α J) :
    measurePairEnergy (sphereReferenceMeasure N) (sphereReferenceMeasure N) α =
      J * (N : ℝ) ^ 2 := by
  exact measurePairEnergy_measure_sphereReference N hpot
    (sphereReferenceMeasure N) (by simp)

/-! ### Atomic measures of finite configurations -/

/-- Counting measure of a labeled finite spherical configuration. -/
noncomputable def pointMeasure {ι : Type*} [Fintype ι]
    (X : ι → Sphere) : Measure Sphere :=
  ∑ i, Measure.dirac (X i)

@[simp] theorem pointMeasure_apply_univ {ι : Type*} [Fintype ι]
    (X : ι → Sphere) : pointMeasure X Set.univ = Fintype.card ι := by
  simp [pointMeasure, Measure.sum_apply]

/-- Integration against a finite counting measure is finite summation. -/
theorem integral_pointMeasure {ι : Type*} [Fintype ι]
    (X : ι → Sphere) (f : Sphere → ℝ) :
    ∫ x, f x ∂pointMeasure X = ∑ i, f (X i) := by
  unfold pointMeasure
  rw [integral_finset_sum_measure (s := Finset.univ)
    (fun _ _ ↦ integrable_dirac)]
  simp

theorem kernelPairEnergy_pointMeasure {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → Sphere) (Y : κ → Sphere) (K : Sphere → Sphere → ℝ) :
    kernelPairEnergy K (pointMeasure X) (pointMeasure Y) =
      ∑ i, ∑ j, K (X i) (Y j) := by
  unfold kernelPairEnergy
  simp_rw [integral_pointMeasure]

/-- For a positive exponent the diagonal of the atomic distance-power
energy vanishes, leaving exactly the ordered-pair Riesz energy. -/
theorem measurePairEnergy_pointMeasure_eq_finiteRieszEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → Sphere) {α : ℝ} (hα : 0 < α) :
    measurePairEnergy (pointMeasure X) (pointMeasure X) α =
      finiteRieszEnergy X α := by
  rw [measurePairEnergy, kernelPairEnergy_pointMeasure]
  unfold finiteRieszEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_erase_add Finset.univ
    (fun j ↦ dist (X i) (X j) ^ α) (Finset.mem_univ i)]
  simp [hα.ne']

theorem measurePairEnergy_finPointMeasure_eq_rieszEnergy
    {N : ℕ} (X : Fin N → Sphere) {α : ℝ} (hα : 0 < α) :
    measurePairEnergy (pointMeasure X) (pointMeasure X) α = rieszEnergy X α := by
  exact measurePairEnergy_pointMeasure_eq_finiteRieszEnergy X hα

/-! ## Conditional negative definiteness in measure form -/

/-- The exact positive-measure formulation of conditional negative
definiteness.  It is the expansion of the signed-measure inequality for
`η = μ - ν`, avoiding any dependence on a particular signed-measure API. -/
def MeasureConditionallyNegative (K : Sphere → Sphere → ℝ) : Prop :=
  ∀ (μ ν : Measure Sphere), μ Set.univ ≠ ⊤ → ν Set.univ ≠ ⊤ →
    μ Set.univ = ν Set.univ →
    kernelPairEnergy K μ μ + kernelPairEnergy K ν ν ≤
      kernelPairEnergy K μ ν + kernelPairEnergy K ν μ

/-- Conditional negative definiteness of the chordal distance-power kernel,
stated in the measure-theoretic form used in the paper. -/
def DistancePowerMeasureCND (α : ℝ) : Prop :=
  MeasureConditionallyNegative (fun x y ↦ dist x y ^ α)

theorem sphere_coordinate_abs_le_one (x : Sphere) (i : Fin 3) :
    |(x : Ambient) i| ≤ 1 := by
  have hsum := x.property
  change (x : Ambient) ∈ Metric.sphere (0 : Ambient) 1 at hsum
  rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at hsum
  change (∑ j, (x : Ambient) j ^ 2) = 1 ^ 2 at hsum
  norm_num at hsum
  have hterm : (x : Ambient) i ^ 2 ≤ ∑ j, (x : Ambient) j ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ((x : Ambient) j))
      (Finset.mem_univ i)
  rw [← sq_le_one_iff_abs_le_one]
  nlinarith

theorem continuous_sphereCoordinate (i : Fin 3) :
    Continuous (fun x : Sphere ↦ (x : Ambient) i) := by
  exact (continuous_apply i).comp continuous_subtype_val

theorem integrable_sphere_coordinate (μ : Measure Sphere) [IsFiniteMeasure μ]
    (i : Fin 3) : Integrable (fun x : Sphere ↦ (x : Ambient) i) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_sphereCoordinate i).measurable.aestronglyMeasurable ?_
  filter_upwards [] with x
  simpa [Real.norm_eq_abs] using sphere_coordinate_abs_le_one x i

noncomputable def sphereCoordinateMoment (μ : Measure Sphere) (i : Fin 3) : ℝ :=
  ∫ x : Sphere, (x : Ambient) i ∂μ

theorem sphere_dist_sq_coordinates (x y : Sphere) :
    dist x y ^ 2 = 2 - 2 * ∑ i : Fin 3, (x : Ambient) i * (y : Ambient) i := by
  change dist (x : Ambient) (y : Ambient) ^ 2 = _
  rw [EuclideanSpace.dist_eq]
  have hnonneg : 0 ≤ ∑ i : Fin 3,
      dist ((x : Ambient) i) ((y : Ambient) i) ^ 2 := by positivity
  rw [Real.sq_sqrt hnonneg]
  have hx := x.property
  have hy := y.property
  change (x : Ambient) ∈ Metric.sphere (0 : Ambient) 1 at hx
  change (y : Ambient) ∈ Metric.sphere (0 : Ambient) 1 at hy
  rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at hx hy
  change (∑ i, (x : Ambient) i ^ 2) = 1 ^ 2 at hx
  change (∑ i, (y : Ambient) i ^ 2) = 1 ^ 2 at hy
  simp only [Real.dist_eq, sq_abs]
  calc
    ∑ i : Fin 3, ((x : Ambient) i - (y : Ambient) i) ^ 2 =
        ∑ i : Fin 3, ((x : Ambient) i ^ 2 + (y : Ambient) i ^ 2 -
          2 * (x : Ambient) i * (y : Ambient) i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hx, hy]
      ring_nf
      rw [Finset.sum_mul]

theorem kernelPairEnergy_sq_distance
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kernelPairEnergy (fun x y : Sphere ↦ dist x y ^ 2) μ ν =
      2 * μ.real Set.univ * ν.real Set.univ -
        2 * ∑ i : Fin 3, sphereCoordinateMoment μ i * sphereCoordinateMoment ν i := by
  unfold kernelPairEnergy sphereCoordinateMoment
  simp_rw [sphere_dist_sq_coordinates]
  have hcoordμ (i : Fin 3) := integrable_sphere_coordinate μ i
  have hcoordν (i : Fin 3) := integrable_sphere_coordinate ν i
  have hinner (x : Sphere) :
      (∫ y : Sphere, (2 - 2 * ∑ i : Fin 3,
        (x : Ambient) i * (y : Ambient) i) ∂ν) =
        2 * ν.real Set.univ - 2 * ∑ i : Fin 3,
          (x : Ambient) i * (∫ y : Sphere, (y : Ambient) i ∂ν) := by
    have hsum : Integrable (fun y : Sphere ↦ ∑ i : Fin 3,
        (x : Ambient) i * (y : Ambient) i) ν :=
      integrable_finset_sum Finset.univ fun i _ ↦ (hcoordν i).const_mul _
    rw [integral_sub (integrable_const (2 : ℝ)) (hsum.const_mul 2),
      integral_const, integral_const_mul, integral_finset_sum]
    · simp_rw [integral_const_mul]
      simp only [smul_eq_mul]
      ring
    · intro i hi
      exact (hcoordν i).const_mul _
  simp_rw [hinner]
  have hsumOuter : Integrable (fun x : Sphere ↦ ∑ i : Fin 3,
      (x : Ambient) i * (∫ y : Sphere, (y : Ambient) i ∂ν)) μ :=
    integrable_finset_sum Finset.univ fun i _ ↦ (hcoordμ i).mul_const _
  rw [integral_sub (integrable_const (2 * ν.real Set.univ)) (hsumOuter.const_mul 2),
    integral_const, integral_const_mul, integral_finset_sum]
  · simp_rw [integral_mul_const]
    simp only [smul_eq_mul]
    ring
  · intro i hi
    exact (hcoordμ i).mul_const _

theorem measureConditionallyNegative_sq_distance :
    MeasureConditionallyNegative (fun x y : Sphere ↦ dist x y ^ 2) := by
  intro μ ν hμ hν hmass
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  rw [kernelPairEnergy_sq_distance, kernelPairEnergy_sq_distance,
    kernelPairEnergy_sq_distance, kernelPairEnergy_sq_distance]
  have hmassReal : μ.real Set.univ = ν.real Set.univ := by
    unfold Measure.real
    rw [hmass]
  rw [hmassReal]
  have hs : 0 ≤ ∑ i : Fin 3,
      (sphereCoordinateMoment μ i - sphereCoordinateMoment ν i) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hid :
      (∑ i : Fin 3, (sphereCoordinateMoment μ i - sphereCoordinateMoment ν i) ^ 2) =
        (∑ i : Fin 3, sphereCoordinateMoment μ i * sphereCoordinateMoment μ i) +
        (∑ i : Fin 3, sphereCoordinateMoment ν i * sphereCoordinateMoment ν i) -
        (∑ i : Fin 3, sphereCoordinateMoment μ i * sphereCoordinateMoment ν i) -
        (∑ i : Fin 3, sphereCoordinateMoment ν i * sphereCoordinateMoment μ i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hid] at hs
  nlinarith

theorem distancePowerMeasureCND_two : DistancePowerMeasureCND 2 := by
  unfold DistancePowerMeasureCND
  simpa only [Real.rpow_two] using measureConditionallyNegative_sq_distance

/-- Positive definiteness in the same finite-positive-measure formulation as
`MeasureConditionallyNegative`. -/
def MeasurePositiveDefinite (K : Sphere → Sphere → ℝ) : Prop :=
  ∀ (μ ν : Measure Sphere), μ Set.univ ≠ ⊤ → ν Set.univ ≠ ⊤ →
    kernelPairEnergy K μ ν + kernelPairEnergy K ν μ ≤
      kernelPairEnergy K μ μ + kernelPairEnergy K ν ν

def sphereInnerKernel (x y : Sphere) : ℝ :=
  ∑ i : Fin 3, (x : Ambient) i * (y : Ambient) i

theorem kernelPairEnergy_sphereInnerKernel
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kernelPairEnergy sphereInnerKernel μ ν =
      ∑ i : Fin 3, sphereCoordinateMoment μ i * sphereCoordinateMoment ν i := by
  unfold kernelPairEnergy sphereInnerKernel sphereCoordinateMoment
  have hcoordμ (i : Fin 3) := integrable_sphere_coordinate μ i
  have hcoordν (i : Fin 3) := integrable_sphere_coordinate ν i
  have hinner (x : Sphere) :
      (∫ y : Sphere, ∑ i : Fin 3, (x : Ambient) i * (y : Ambient) i ∂ν) =
        ∑ i : Fin 3, (x : Ambient) i *
          (∫ y : Sphere, (y : Ambient) i ∂ν) := by
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul]
    · intro i hi
      exact (hcoordν i).const_mul _
  simp_rw [hinner]
  rw [integral_finset_sum]
  · simp_rw [integral_mul_const]
  · intro i hi
    exact (hcoordμ i).mul_const _

theorem measurePositiveDefinite_sphereInnerKernel :
    MeasurePositiveDefinite sphereInnerKernel := by
  intro μ ν hμ hν
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  rw [kernelPairEnergy_sphereInnerKernel, kernelPairEnergy_sphereInnerKernel,
    kernelPairEnergy_sphereInnerKernel, kernelPairEnergy_sphereInnerKernel]
  have hs : 0 ≤ ∑ i : Fin 3,
      (sphereCoordinateMoment μ i - sphereCoordinateMoment ν i) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hid :
      (∑ i : Fin 3, (sphereCoordinateMoment μ i - sphereCoordinateMoment ν i) ^ 2) =
        (∑ i : Fin 3, sphereCoordinateMoment μ i * sphereCoordinateMoment μ i) +
        (∑ i : Fin 3, sphereCoordinateMoment ν i * sphereCoordinateMoment ν i) -
        (∑ i : Fin 3, sphereCoordinateMoment μ i * sphereCoordinateMoment ν i) -
        (∑ i : Fin 3, sphereCoordinateMoment ν i * sphereCoordinateMoment μ i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hid] at hs
  linarith

def sphereTensorFeature (n : ℕ) (p : Fin n → Fin 3) (x : Sphere) : ℝ :=
  ∏ k : Fin n, (x : Ambient) (p k)

theorem continuous_sphereTensorFeature (n : ℕ) (p : Fin n → Fin 3) :
    Continuous (sphereTensorFeature n p) := by
  unfold sphereTensorFeature
  exact continuous_finset_prod Finset.univ fun k hk ↦ continuous_sphereCoordinate (p k)

theorem integrable_sphereTensorFeature (μ : Measure Sphere) [IsFiniteMeasure μ]
    (n : ℕ) (p : Fin n → Fin 3) : Integrable (sphereTensorFeature n p) μ :=
  (continuous_sphereTensorFeature n p).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def sphereTensorMoment (μ : Measure Sphere)
    (n : ℕ) (p : Fin n → Fin 3) : ℝ :=
  ∫ x : Sphere, sphereTensorFeature n p x ∂μ

theorem sphereInnerKernel_pow_eq_feature_sum (n : ℕ) (x y : Sphere) :
    sphereInnerKernel x y ^ n =
      ∑ p : Fin n → Fin 3, sphereTensorFeature n p x * sphereTensorFeature n p y := by
  unfold sphereInnerKernel sphereTensorFeature
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.prod_mul_distrib]

theorem kernelPairEnergy_sphereInnerKernel_pow
    (n : ℕ) (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kernelPairEnergy (fun x y ↦ sphereInnerKernel x y ^ n) μ ν =
      ∑ p : Fin n → Fin 3, sphereTensorMoment μ n p * sphereTensorMoment ν n p := by
  unfold kernelPairEnergy sphereTensorMoment
  simp_rw [sphereInnerKernel_pow_eq_feature_sum]
  have hfeatureμ (p : Fin n → Fin 3) := integrable_sphereTensorFeature μ n p
  have hfeatureν (p : Fin n → Fin 3) := integrable_sphereTensorFeature ν n p
  have hinner (x : Sphere) :
      (∫ y : Sphere, ∑ p : Fin n → Fin 3,
        sphereTensorFeature n p x * sphereTensorFeature n p y ∂ν) =
        ∑ p : Fin n → Fin 3, sphereTensorFeature n p x *
          (∫ y : Sphere, sphereTensorFeature n p y ∂ν) := by
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul]
    · intro p hp
      exact (hfeatureν p).const_mul _
  simp_rw [hinner]
  rw [integral_finset_sum]
  · simp_rw [integral_mul_const]
  · intro p hp
    exact (hfeatureμ p).mul_const _

theorem measurePositiveDefinite_sphereInnerKernel_pow (n : ℕ) :
    MeasurePositiveDefinite (fun x y ↦ sphereInnerKernel x y ^ n) := by
  intro μ ν hμ hν
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  rw [kernelPairEnergy_sphereInnerKernel_pow, kernelPairEnergy_sphereInnerKernel_pow,
    kernelPairEnergy_sphereInnerKernel_pow, kernelPairEnergy_sphereInnerKernel_pow]
  have hs : 0 ≤ ∑ p : Fin n → Fin 3,
      (sphereTensorMoment μ n p - sphereTensorMoment ν n p) ^ 2 :=
    Finset.sum_nonneg fun p _ ↦ sq_nonneg _
  have hid :
      (∑ p : Fin n → Fin 3,
        (sphereTensorMoment μ n p - sphereTensorMoment ν n p) ^ 2) =
        (∑ p : Fin n → Fin 3, sphereTensorMoment μ n p * sphereTensorMoment μ n p) +
        (∑ p : Fin n → Fin 3, sphereTensorMoment ν n p * sphereTensorMoment ν n p) -
        (∑ p : Fin n → Fin 3, sphereTensorMoment μ n p * sphereTensorMoment ν n p) -
        (∑ p : Fin n → Fin 3, sphereTensorMoment ν n p * sphereTensorMoment μ n p) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hid] at hs
  linarith

noncomputable def innerExpCoeff (c : ℝ) (n : ℕ) : ℝ :=
  c ^ n / (Nat.factorial n : ℝ)

noncomputable def innerExpPartialKernel (c : ℝ) (N : ℕ) (x y : Sphere) : ℝ :=
  ∑ n ∈ Finset.range N, innerExpCoeff c n * sphereInnerKernel x y ^ n

theorem innerExpCoeff_nonneg {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ innerExpCoeff c n := by
  unfold innerExpCoeff
  positivity

theorem kernelPairEnergy_innerExpPartialKernel
    (c : ℝ) (N : ℕ) (μ ν : Measure Sphere)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kernelPairEnergy (innerExpPartialKernel c N) μ ν =
      ∑ n ∈ Finset.range N, innerExpCoeff c n *
        ∑ p : Fin n → Fin 3, sphereTensorMoment μ n p * sphereTensorMoment ν n p := by
  unfold kernelPairEnergy innerExpPartialKernel
  simp_rw [sphereInnerKernel_pow_eq_feature_sum]
  have hfeatureμ (n : ℕ) (p : Fin n → Fin 3) := integrable_sphereTensorFeature μ n p
  have hfeatureν (n : ℕ) (p : Fin n → Fin 3) := integrable_sphereTensorFeature ν n p
  have hinner (x : Sphere) :
      (∫ y : Sphere, ∑ n ∈ Finset.range N, innerExpCoeff c n *
        ∑ p : Fin n → Fin 3,
          sphereTensorFeature n p x * sphereTensorFeature n p y ∂ν) =
      ∑ n ∈ Finset.range N, innerExpCoeff c n *
        ∑ p : Fin n → Fin 3, sphereTensorFeature n p x *
          (∫ y : Sphere, sphereTensorFeature n p y ∂ν) := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul, integral_finset_sum]
      · simp_rw [integral_const_mul]
      · intro p hp
        exact (hfeatureν n p).const_mul _
    · intro n hn
      apply Integrable.const_mul
      exact integrable_finset_sum Finset.univ fun p _ ↦ (hfeatureν n p).const_mul _
  simp_rw [hinner]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [integral_const_mul, integral_finset_sum]
    · simp_rw [integral_mul_const]
      simp only [sphereTensorMoment]
    · intro p hp
      exact (hfeatureμ n p).mul_const _
  · intro n hn
    apply Integrable.const_mul
    exact integrable_finset_sum Finset.univ fun p _ ↦ (hfeatureμ n p).mul_const _

theorem measurePositiveDefinite_innerExpPartialKernel {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    MeasurePositiveDefinite (innerExpPartialKernel c N) := by
  intro μ ν hμ hν
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  rw [kernelPairEnergy_innerExpPartialKernel, kernelPairEnergy_innerExpPartialKernel,
    kernelPairEnergy_innerExpPartialKernel, kernelPairEnergy_innerExpPartialKernel]
  have hs : 0 ≤ ∑ n ∈ Finset.range N, innerExpCoeff c n *
      ∑ p : Fin n → Fin 3,
        (sphereTensorMoment μ n p - sphereTensorMoment ν n p) ^ 2 := by
    exact Finset.sum_nonneg fun n _ ↦ mul_nonneg (innerExpCoeff_nonneg hc n)
      (Finset.sum_nonneg fun p _ ↦ sq_nonneg _)
  have hid (n : ℕ) :
      (∑ p : Fin n → Fin 3,
        (sphereTensorMoment μ n p - sphereTensorMoment ν n p) ^ 2) =
        (∑ p : Fin n → Fin 3, sphereTensorMoment μ n p * sphereTensorMoment μ n p) +
        (∑ p : Fin n → Fin 3, sphereTensorMoment ν n p * sphereTensorMoment ν n p) -
        (∑ p : Fin n → Fin 3, sphereTensorMoment μ n p * sphereTensorMoment ν n p) -
        (∑ p : Fin n → Fin 3, sphereTensorMoment ν n p * sphereTensorMoment μ n p) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  simp_rw [hid] at hs
  simp_rw [mul_sub, mul_add] at hs
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib] at hs
  nlinarith

theorem sphereInnerKernel_abs_le_one (x y : Sphere) : |sphereInnerKernel x y| ≤ 1 := by
  have hinner := abs_real_inner_le_norm (x : Ambient) (y : Ambient)
  have hxnorm : ‖(x : Ambient)‖ = 1 := norm_eq_of_mem_sphere x
  have hynorm : ‖(y : Ambient)‖ = 1 := norm_eq_of_mem_sphere y
  rw [hxnorm, hynorm, mul_one] at hinner
  simpa [sphereInnerKernel, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, mul_comm] using hinner

theorem innerExpPartialKernel_norm_le_exp {c : ℝ} (hc : 0 ≤ c)
    (N : ℕ) (x y : Sphere) :
    ‖innerExpPartialKernel c N x y‖ ≤ Real.exp c := by
  have hcoeffSum : HasSum (innerExpCoeff c) (Real.exp c) := by
    simpa [innerExpCoeff, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ℝ c)
  rw [Real.norm_eq_abs, innerExpPartialKernel]
  calc
    |∑ n ∈ Finset.range N, innerExpCoeff c n * sphereInnerKernel x y ^ n| ≤
        ∑ n ∈ Finset.range N,
          |innerExpCoeff c n * sphereInnerKernel x y ^ n| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, innerExpCoeff c n := by
      gcongr with n hn
      rw [abs_mul, abs_of_nonneg (innerExpCoeff_nonneg hc n), abs_pow]
      exact mul_le_of_le_one_right (innerExpCoeff_nonneg hc n)
        (pow_le_one₀ (abs_nonneg _) (sphereInnerKernel_abs_le_one x y))
    _ ≤ Real.exp c := sum_le_hasSum (Finset.range N)
      (fun n hn ↦ innerExpCoeff_nonneg hc n) hcoeffSum

theorem innerExpPartialKernel_tendsto (c : ℝ) (x y : Sphere) :
    Filter.Tendsto (fun N ↦ innerExpPartialKernel c N x y) Filter.atTop
      (_root_.nhds (Real.exp (c * sphereInnerKernel x y))) := by
  have hsum := (NormedSpace.expSeries_div_hasSum_exp ℝ
    (c * sphereInnerKernel x y)).tendsto_sum_nat
  simpa [innerExpPartialKernel, innerExpCoeff, mul_pow, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm, Real.exp_eq_exp_ℝ] using hsum

noncomputable def innerExpKernel (c : ℝ) (x y : Sphere) : ℝ :=
  Real.exp (c * sphereInnerKernel x y)

theorem continuous_sphereInnerKernel_prod :
    Continuous (fun p : Sphere × Sphere ↦ sphereInnerKernel p.1 p.2) := by
  unfold sphereInnerKernel
  apply continuous_finset_sum
  intro i hi
  exact ((continuous_sphereCoordinate i).comp continuous_fst).mul
    ((continuous_sphereCoordinate i).comp continuous_snd)

theorem continuous_innerExpPartialKernel_prod (c : ℝ) (N : ℕ) :
    Continuous (fun p : Sphere × Sphere ↦ innerExpPartialKernel c N p.1 p.2) := by
  unfold innerExpPartialKernel
  apply continuous_finset_sum
  intro n hn
  exact continuous_const.mul (continuous_sphereInnerKernel_prod.pow n)

theorem continuous_innerExpKernel_prod (c : ℝ) :
    Continuous (fun p : Sphere × Sphere ↦ innerExpKernel c p.1 p.2) := by
  unfold innerExpKernel
  exact Real.continuous_exp.comp (continuous_const.mul continuous_sphereInnerKernel_prod)

theorem kernelPairEnergy_eq_integral_prod {K : Sphere → Sphere → ℝ}
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hK : Continuous (fun p : Sphere × Sphere ↦ K p.1 p.2)) :
    kernelPairEnergy K μ ν = ∫ p : Sphere × Sphere, K p.1 p.2 ∂μ.prod ν := by
  symm
  apply MeasureTheory.integral_prod
  exact hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem kernelPairEnergy_innerExpPartialKernel_tendsto {c : ℝ} (hc : 0 ≤ c)
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Filter.Tendsto (fun N ↦ kernelPairEnergy (innerExpPartialKernel c N) μ ν)
      Filter.atTop (_root_.nhds (kernelPairEnergy (innerExpKernel c) μ ν)) := by
  simp_rw [kernelPairEnergy_eq_integral_prod μ ν
    (continuous_innerExpPartialKernel_prod c _),
    kernelPairEnergy_eq_integral_prod μ ν (continuous_innerExpKernel_prod c)]
  apply MeasureTheory.tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun N ↦
      (continuous_innerExpPartialKernel_prod c N).aestronglyMeasurable
  · refine ⟨Real.exp c, Filter.Eventually.of_forall fun N ↦ ?_⟩
    exact Filter.Eventually.of_forall fun p ↦ innerExpPartialKernel_norm_le_exp hc N p.1 p.2
  · exact Filter.Eventually.of_forall fun p ↦ by
      simpa [innerExpKernel] using innerExpPartialKernel_tendsto c p.1 p.2

theorem measurePositiveDefinite_innerExpKernel {c : ℝ} (hc : 0 ≤ c) :
    MeasurePositiveDefinite (innerExpKernel c) := by
  intro μ ν hμ hν
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  have hμν := kernelPairEnergy_innerExpPartialKernel_tendsto hc μ ν
  have hνμ := kernelPairEnergy_innerExpPartialKernel_tendsto hc ν μ
  have hμμ := kernelPairEnergy_innerExpPartialKernel_tendsto hc μ μ
  have hνν := kernelPairEnergy_innerExpPartialKernel_tendsto hc ν ν
  have hlim := hμν.add hνμ
  have hrhs := hμμ.add hνν
  have hd :
      (kernelPairEnergy (innerExpKernel c) μ ν +
          kernelPairEnergy (innerExpKernel c) ν μ) -
        (kernelPairEnergy (innerExpKernel c) μ μ +
          kernelPairEnergy (innerExpKernel c) ν ν) ≤ 0 := by
    apply le_of_tendsto (hlim.sub hrhs)
    exact Filter.Eventually.of_forall fun N ↦ sub_nonpos.mpr
      (measurePositiveDefinite_innerExpPartialKernel hc N μ ν hμ hν)
  linarith

noncomputable def gaussianDistanceKernel (t : ℝ) (x y : Sphere) : ℝ :=
  Real.exp (-t * dist x y ^ 2)

theorem gaussianDistanceKernel_eq_innerExpKernel (t : ℝ) (x y : Sphere) :
    gaussianDistanceKernel t x y =
      Real.exp (-2 * t) * innerExpKernel (2 * t) x y := by
  unfold gaussianDistanceKernel
  rw [sphere_dist_sq_coordinates]
  unfold innerExpKernel sphereInnerKernel
  rw [← Real.exp_add]
  congr 1
  ring

theorem kernelPairEnergy_const_mul (a : ℝ) (K : Sphere → Sphere → ℝ)
    (μ ν : Measure Sphere) :
    kernelPairEnergy (fun x y ↦ a * K x y) μ ν = a * kernelPairEnergy K μ ν := by
  unfold kernelPairEnergy
  simp_rw [integral_const_mul]

theorem measurePositiveDefinite_const_mul {a : ℝ} (ha : 0 ≤ a)
    {K : Sphere → Sphere → ℝ} (hK : MeasurePositiveDefinite K) :
    MeasurePositiveDefinite (fun x y ↦ a * K x y) := by
  intro μ ν hμ hν
  simp_rw [kernelPairEnergy_const_mul]
  nlinarith [hK μ ν hμ hν]

theorem measurePositiveDefinite_congr {K L : Sphere → Sphere → ℝ}
    (h : ∀ x y, K x y = L x y) (hK : MeasurePositiveDefinite K) :
    MeasurePositiveDefinite L := by
  have hfun : L = K := by
    funext x y
    exact (h x y).symm
  simpa [hfun] using hK

theorem measurePositiveDefinite_gaussianDistanceKernel {t : ℝ} (ht : 0 ≤ t) :
    MeasurePositiveDefinite (gaussianDistanceKernel t) := by
  apply measurePositiveDefinite_congr fun x y ↦
    (gaussianDistanceKernel_eq_innerExpKernel t x y).symm
  exact measurePositiveDefinite_const_mul (Real.exp_pos _).le
    (measurePositiveDefinite_innerExpKernel (by positivity : 0 ≤ 2 * t))

theorem continuous_gaussianDistanceKernel_prod (t : ℝ) :
    Continuous (fun p : Sphere × Sphere ↦ gaussianDistanceKernel t p.1 p.2) := by
  unfold gaussianDistanceKernel
  exact Real.continuous_exp.comp
    (continuous_const.mul
      ((continuous_dist.comp (continuous_fst.prodMk continuous_snd)).pow 2))

theorem kernelPairEnergy_one (μ ν : Measure Sphere)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kernelPairEnergy (fun _ _ : Sphere ↦ (1 : ℝ)) μ ν =
      μ.real Set.univ * ν.real Set.univ := by
  unfold kernelPairEnergy
  simp

theorem kernelPairEnergy_sub_continuous {K L : Sphere → Sphere → ℝ}
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hK : Continuous (fun p : Sphere × Sphere ↦ K p.1 p.2))
    (hL : Continuous (fun p : Sphere × Sphere ↦ L p.1 p.2)) :
    kernelPairEnergy (fun x y ↦ K x y - L x y) μ ν =
      kernelPairEnergy K μ ν - kernelPairEnergy L μ ν := by
  rw [kernelPairEnergy_eq_integral_prod μ ν (hK.sub hL),
    kernelPairEnergy_eq_integral_prod μ ν hK,
    kernelPairEnergy_eq_integral_prod μ ν hL]
  exact MeasureTheory.integral_sub
    (hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem measureConditionallyNegative_one_sub_gaussian {t : ℝ} (ht : 0 ≤ t) :
    MeasureConditionallyNegative (fun x y ↦ 1 - gaussianDistanceKernel t x y) := by
  intro μ ν hμ hν hmass
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  have hreal : μ.real Set.univ = ν.real Set.univ := by
    simpa [Measure.real_def] using congrArg ENNReal.toReal hmass
  have hpd := measurePositiveDefinite_gaussianDistanceKernel ht μ ν hμ hν
  have hsub (ρ τ : Measure Sphere) [IsFiniteMeasure ρ] [IsFiniteMeasure τ] :=
    kernelPairEnergy_sub_continuous (K := fun _ _ ↦ (1 : ℝ))
      (L := gaussianDistanceKernel t) ρ τ
      (show Continuous (fun _ : Sphere × Sphere ↦ (1 : ℝ)) from continuous_const)
      (continuous_gaussianDistanceKernel_prod t)
  rw [hsub μ μ, hsub ν ν, hsub μ ν, hsub ν μ,
    kernelPairEnergy_one, kernelPairEnergy_one,
    kernelPairEnergy_one, kernelPairEnergy_one]
  rw [hreal]
  linarith

theorem measureConditionallyNegative_const_mul {a : ℝ} (ha : 0 ≤ a)
    {K : Sphere → Sphere → ℝ} (hK : MeasureConditionallyNegative K) :
    MeasureConditionallyNegative (fun x y ↦ a * K x y) := by
  intro μ ν hμ hν hmass
  simp_rw [kernelPairEnergy_const_mul]
  nlinarith [hK μ ν hμ hν hmass]

theorem kernelPairEnergy_add_continuous {K L : Sphere → Sphere → ℝ}
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hK : Continuous (fun p : Sphere × Sphere ↦ K p.1 p.2))
    (hL : Continuous (fun p : Sphere × Sphere ↦ L p.1 p.2)) :
    kernelPairEnergy (fun x y ↦ K x y + L x y) μ ν =
      kernelPairEnergy K μ ν + kernelPairEnergy L μ ν := by
  rw [kernelPairEnergy_eq_integral_prod μ ν (hK.add hL),
    kernelPairEnergy_eq_integral_prod μ ν hK,
    kernelPairEnergy_eq_integral_prod μ ν hL]
  exact MeasureTheory.integral_add
    (hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem measureConditionallyNegative_add_continuous
    {K L : Sphere → Sphere → ℝ}
    (hKcont : Continuous (fun p : Sphere × Sphere ↦ K p.1 p.2))
    (hLcont : Continuous (fun p : Sphere × Sphere ↦ L p.1 p.2))
    (hK : MeasureConditionallyNegative K)
    (hL : MeasureConditionallyNegative L) :
    MeasureConditionallyNegative (fun x y ↦ K x y + L x y) := by
  intro μ ν hμ hν hmass
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  simp_rw [kernelPairEnergy_add_continuous μ μ hKcont hLcont,
    kernelPairEnergy_add_continuous ν ν hKcont hLcont,
    kernelPairEnergy_add_continuous μ ν hKcont hLcont,
    kernelPairEnergy_add_continuous ν μ hKcont hLcont]
  linarith [hK μ ν hμ hν hmass, hL μ ν hμ hν hmass]

/-- Dominated convergence for pair energies on the compact sphere.  This is
the limit-passing mechanism used by Schoenberg approximations. -/
theorem kernelPairEnergy_tendsto_of_continuous_of_bound
    {K : ℕ → Sphere → Sphere → ℝ} {L : Sphere → Sphere → ℝ} {C : ℝ}
    (μ ν : Measure Sphere) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hK : ∀ n, Continuous (fun p : Sphere × Sphere ↦ K n p.1 p.2))
    (hL : Continuous (fun p : Sphere × Sphere ↦ L p.1 p.2))
    (hbound : ∀ n x y, ‖K n x y‖ ≤ C)
    (hlim : ∀ x y, Filter.Tendsto (fun n ↦ K n x y) Filter.atTop
      (_root_.nhds (L x y))) :
    Filter.Tendsto (fun n ↦ kernelPairEnergy (K n) μ ν) Filter.atTop
      (_root_.nhds (kernelPairEnergy L μ ν)) := by
  simp_rw [kernelPairEnergy_eq_integral_prod μ ν (hK _),
    kernelPairEnergy_eq_integral_prod μ ν hL]
  apply MeasureTheory.tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun n ↦ (hK n).aestronglyMeasurable
  · exact ⟨C, Filter.Eventually.of_forall fun n ↦
      Filter.Eventually.of_forall fun p ↦ hbound n p.1 p.2⟩
  · exact Filter.Eventually.of_forall fun p ↦ hlim p.1 p.2

theorem measureConditionallyNegative_of_tendsto
    {K : ℕ → Sphere → Sphere → ℝ} {L : Sphere → Sphere → ℝ} {C : ℝ}
    (hKcont : ∀ n, Continuous (fun p : Sphere × Sphere ↦ K n p.1 p.2))
    (hLcont : Continuous (fun p : Sphere × Sphere ↦ L p.1 p.2))
    (hbound : ∀ n x y, ‖K n x y‖ ≤ C)
    (hlim : ∀ x y, Filter.Tendsto (fun n ↦ K n x y) Filter.atTop
      (_root_.nhds (L x y)))
    (hCND : ∀ n, MeasureConditionallyNegative (K n)) :
    MeasureConditionallyNegative L := by
  intro μ ν hμ hν hmass
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  have hμμ := kernelPairEnergy_tendsto_of_continuous_of_bound μ μ
    hKcont hLcont hbound hlim
  have hνν := kernelPairEnergy_tendsto_of_continuous_of_bound ν ν
    hKcont hLcont hbound hlim
  have hμν := kernelPairEnergy_tendsto_of_continuous_of_bound μ ν
    hKcont hLcont hbound hlim
  have hνμ := kernelPairEnergy_tendsto_of_continuous_of_bound ν μ
    hKcont hLcont hbound hlim
  have hd :
      (kernelPairEnergy L μ μ + kernelPairEnergy L ν ν) -
        (kernelPairEnergy L μ ν + kernelPairEnergy L ν μ) ≤ 0 := by
    apply le_of_tendsto ((hμμ.add hνν).sub (hμν.add hνμ))
    exact Filter.Eventually.of_forall fun n ↦ sub_nonpos.mpr
      (hCND n μ ν hμ hν hmass)
  linarith

noncomputable def schoenbergIntegrand (p r t : ℝ) : ℝ :=
  (1 - Real.exp (-t * r)) * t ^ (-p - 1)

noncomputable def schoenbergIntegral (p r : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0, schoenbergIntegrand p r t

theorem schoenbergIntegrand_nonneg {p r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) :
    0 ≤ schoenbergIntegrand p r t := by
  unfold schoenbergIntegrand
  exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith)))
    (Real.rpow_nonneg ht.le _)

theorem continuousOn_schoenbergIntegrand {p r : ℝ} :
    ContinuousOn (schoenbergIntegrand p r) (Set.Ioi 0) := by
  unfold schoenbergIntegrand
  apply ContinuousOn.mul
  · exact continuousOn_const.sub
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_id.neg.mul continuousOn_const))
  · exact continuousOn_id.rpow continuousOn_const fun t ht ↦ Or.inl ht.ne'

theorem integrableOn_schoenbergIntegrand {p r : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hr : 0 ≤ r) :
    IntegrableOn (schoenbergIntegrand p r) (Set.Ioi 0) := by
  have hmeas (s : Set ℝ) (hs : MeasurableSet s) (hsub : s ⊆ Set.Ioi (0 : ℝ)) :
      AEStronglyMeasurable (schoenbergIntegrand p r) (volume.restrict s) :=
    (continuousOn_schoenbergIntegrand.mono hsub).aestronglyMeasurable hs
  have hzero : IntegrableOn (schoenbergIntegrand p r) (Set.Ioo 0 1) := by
    refine Integrable.mono'
      (((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr
        (by linarith : -1 < -p)).const_mul r)
      (hmeas _ measurableSet_Ioo Set.Ioo_subset_Ioi_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : 0 < t := ht.1
    have hone : 1 - Real.exp (-t * r) ≤ t * r := by
      linarith [Real.add_one_le_exp (-t * r)]
    rw [Real.norm_eq_abs, abs_of_nonneg (schoenbergIntegrand_nonneg hr ht0)]
    unfold schoenbergIntegrand
    calc
      (1 - Real.exp (-t * r)) * t ^ (-p - 1) ≤
          (t * r) * t ^ (-p - 1) :=
        mul_le_mul_of_nonneg_right hone (Real.rpow_nonneg ht0.le _)
      _ = r * (t ^ (1 : ℝ) * t ^ (-p - 1)) := by
        rw [Real.rpow_one]
        ring
      _ = r * t ^ (-p) := by
        rw [← Real.rpow_add ht0]
        congr 2
        ring
  have htop : IntegrableOn (schoenbergIntegrand p r) (Set.Ioi (1 / 2 : ℝ)) := by
    refine Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (by linarith : -p - 1 < -1)
        (by norm_num : (0 : ℝ) < 1 / 2))
      (hmeas _ measurableSet_Ioi (Set.Ioi_subset_Ioi (by norm_num))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) ht
    have hone : 1 - Real.exp (-t * r) ≤ 1 := by
      linarith [Real.exp_nonneg (-t * r)]
    rw [Real.norm_eq_abs, abs_of_nonneg (schoenbergIntegrand_nonneg hr ht0)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) hone
  exact (hzero.union htop).mono_set fun t ht ↦ by
    by_cases h : t < 1
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr (by norm_num at *; linarith)

theorem schoenbergIntegral_zero (p : ℝ) : schoenbergIntegral p 0 = 0 := by
  simp [schoenbergIntegral, schoenbergIntegrand]

theorem schoenbergIntegral_scaling {p r : ℝ} (hr : 0 < r) :
    schoenbergIntegral p r = r ^ p * schoenbergIntegral p 1 := by
  have hchange := integral_comp_mul_left_Ioi (schoenbergIntegrand p 1) 0 hr
  have hpoint : ∀ t ∈ Set.Ioi (0 : ℝ),
      schoenbergIntegrand p 1 (r * t) =
        r ^ (-p - 1) * schoenbergIntegrand p r t := by
    intro t ht
    unfold schoenbergIntegrand
    rw [Real.mul_rpow hr.le ht.le]
    have he : -(r * t) = -(t * r) := by ring
    rw [he]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul,
    mul_zero, smul_eq_mul] at hchange
  unfold schoenbergIntegral
  have hrpow : r ^ (-p - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  apply (mul_left_cancel₀ hrpow)
  rw [hchange, ← mul_assoc, ← Real.rpow_add hr, ← Real.rpow_neg_one]
  congr 2
  ring

theorem schoenbergIntegral_one_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < schoenbergIntegral p 1 := by
  unfold schoenbergIntegral
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae]
  · have hs : Function.support (schoenbergIntegrand p 1) ∩ Set.Ioi 0 = Set.Ioi 0 := by
      rw [Set.inter_eq_right]
      intro t ht
      rw [Function.mem_support]
      apply ne_of_gt
      have ht0 : 0 < t := ht
      unfold schoenbergIntegrand
      exact mul_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by simpa using neg_lt_zero.mpr ht0)))
        (Real.rpow_pos_of_pos ht0 _)
    rw [hs, Real.volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact schoenbergIntegrand_nonneg zero_le_one ht
  · exact integrableOn_schoenbergIntegrand hp0 hp1 zero_le_one

theorem schoenbergIntegral_eq_rpow_mul {p r : ℝ}
    (hp0 : 0 < p) (hr : 0 ≤ r) :
    schoenbergIntegral p r = r ^ p * schoenbergIntegral p 1 := by
  obtain rfl | hr := hr.eq_or_lt
  · simp [schoenbergIntegral_zero, Real.zero_rpow hp0.ne']
  · exact schoenbergIntegral_scaling hr

theorem sphere_dist_sq_nonneg_le_four (x y : Sphere) :
    0 ≤ dist x y ^ 2 ∧ dist x y ^ 2 ≤ 4 := by
  constructor
  · positivity
  · rw [sphere_dist_sq_coordinates]
    have hinner := sphereInnerKernel_abs_le_one x y
    unfold sphereInnerKernel at hinner
    rw [abs_le] at hinner
    linarith

theorem continuousOn_schoenberg_joint {p : ℝ} :
    ContinuousOn
      (fun z : ℝ × (Sphere × Sphere) ↦
        schoenbergIntegrand p (dist z.2.1 z.2.2 ^ 2) z.1)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  unfold schoenbergIntegrand
  have hd : Continuous (fun z : ℝ × (Sphere × Sphere) ↦ dist z.2.1 z.2.2 ^ 2) :=
    (continuous_dist.comp (continuous_snd.fst.prodMk continuous_snd.snd)).pow 2
  apply ContinuousOn.mul
  · exact continuousOn_const.sub (Real.continuous_exp.comp_continuousOn
      ((continuous_fst.neg.mul hd).continuousOn))
  · exact continuousOn_fst.rpow continuousOn_const fun z hz ↦ Or.inl hz.1.ne'

theorem integrable_schoenberg_joint {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : Measure (Sphere × Sphere)) [IsFiniteMeasure ρ] :
    Integrable
      (fun z : ℝ × (Sphere × Sphere) ↦
        schoenbergIntegrand p (dist z.2.1 z.2.2 ^ 2) z.1)
      ((volume.restrict (Set.Ioi 0)).prod ρ) := by
  have hdom : Integrable
      (fun z : ℝ × (Sphere × Sphere) ↦ schoenbergIntegrand p 4 z.1 * 1)
      ((volume.restrict (Set.Ioi 0)).prod ρ) :=
    (integrableOn_schoenbergIntegrand hp0 hp1 (by norm_num : (0 : ℝ) ≤ 4)).mul_prod
      (integrable_const (1 : ℝ))
  apply Integrable.mono' hdom
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact continuousOn_schoenberg_joint.aestronglyMeasurable
      (measurableSet_Ioi.prod MeasurableSet.univ)
  · have hzmem : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)).prod ρ,
        z ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ := by
      rw [Measure.ae_prod_mem_iff_ae_ae_mem
        (measurableSet_Ioi.prod MeasurableSet.univ)]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Filter.Eventually.of_forall fun q ↦ ⟨ht, Set.mem_univ q⟩
    filter_upwards [hzmem] with z hz
    have ht : 0 < z.1 := hz.1
    have hr := sphere_dist_sq_nonneg_le_four z.2.1 z.2.2
    rw [Real.norm_eq_abs,
      abs_of_nonneg (schoenbergIntegrand_nonneg hr.1 ht)]
    simp only [mul_one]
    unfold schoenbergIntegrand
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    exact sub_le_sub_left (Real.exp_le_exp.mpr (by nlinarith)) 1

theorem integral_schoenberg_swap {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ρ : Measure (Sphere × Sphere)) [IsFiniteMeasure ρ] :
    (∫ t : ℝ in Set.Ioi 0,
        ∫ q : Sphere × Sphere,
          schoenbergIntegrand p (dist q.1 q.2 ^ 2) t ∂ρ) =
      schoenbergIntegral p 1 *
        ∫ q : Sphere × Sphere, (dist q.1 q.2 ^ 2) ^ p ∂ρ := by
  have hswap := MeasureTheory.integral_integral_swap
    (μ := volume.restrict (Set.Ioi 0)) (ν := ρ)
    (f := fun t q ↦ schoenbergIntegrand p (dist q.1 q.2 ^ 2) t)
    (integrable_schoenberg_joint hp0 hp1 ρ)
  calc
    (∫ t : ℝ in Set.Ioi 0,
        ∫ q : Sphere × Sphere,
          schoenbergIntegrand p (dist q.1 q.2 ^ 2) t ∂ρ) =
        ∫ q : Sphere × Sphere,
          (∫ t : ℝ in Set.Ioi 0,
            schoenbergIntegrand p (dist q.1 q.2 ^ 2) t) ∂ρ := hswap
    _ = ∫ q : Sphere × Sphere,
          (dist q.1 q.2 ^ 2) ^ p * schoenbergIntegral p 1 ∂ρ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q ↦
        schoenbergIntegral_eq_rpow_mul hp0
          (sphere_dist_sq_nonneg_le_four q.1 q.2).1
    _ = _ := by
      rw [integral_mul_const]
      ring

theorem continuous_distance_sq_rpow_prod {p : ℝ} (hp : 0 < p) :
    Continuous (fun q : Sphere × Sphere ↦ (dist q.1 q.2 ^ 2) ^ p) := by
  exact ((continuous_dist.pow 2).rpow continuous_const fun _ ↦ Or.inr hp)

theorem distance_sq_rpow_half_alpha {α : ℝ} (x y : Sphere) :
    (dist x y ^ 2) ^ (α / 2) = dist x y ^ α := by
  rw [← Real.rpow_natCast (dist x y) 2, ← Real.rpow_mul (dist_nonneg : 0 ≤ dist x y)]
  congr 2
  ring

noncomputable def schoenbergKernel (p t : ℝ) (x y : Sphere) : ℝ :=
  schoenbergIntegrand p (dist x y ^ 2) t

theorem continuous_schoenbergKernel_prod (p t : ℝ) :
    Continuous (fun q : Sphere × Sphere ↦ schoenbergKernel p t q.1 q.2) := by
  unfold schoenbergKernel schoenbergIntegrand
  have hd : Continuous (fun q : Sphere × Sphere ↦ dist q.1 q.2 ^ 2) :=
    continuous_dist.pow 2
  exact (continuous_const.sub (Real.continuous_exp.comp
    (continuous_const.mul hd))).mul continuous_const

theorem measureConditionallyNegative_congr {K L : Sphere → Sphere → ℝ}
    (h : ∀ x y, K x y = L x y) (hK : MeasureConditionallyNegative K) :
    MeasureConditionallyNegative L := by
  have hfun : L = K := by
    funext x y
    exact (h x y).symm
  simpa [hfun] using hK

theorem measureConditionallyNegative_schoenbergKernel {p t : ℝ} (ht : 0 < t) :
    MeasureConditionallyNegative (schoenbergKernel p t) := by
  apply measureConditionallyNegative_congr (K := fun x y ↦
    t ^ (-p - 1) * (1 - gaussianDistanceKernel t x y))
  · intro x y
    unfold schoenbergKernel schoenbergIntegrand gaussianDistanceKernel
    ring
  · exact measureConditionallyNegative_const_mul (Real.rpow_nonneg ht.le _)
      (measureConditionallyNegative_one_sub_gaussian ht.le)

theorem measureConditionallyNegative_distance_sq_rpow {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    MeasureConditionallyNegative (fun x y : Sphere ↦ (dist x y ^ 2) ^ p) := by
  intro μ ν hμ hν hmass
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hμ)
  letI : IsFiniteMeasure ν := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hν)
  let A (ρ τ : Measure Sphere) (t : ℝ) :=
    ∫ q : Sphere × Sphere,
      schoenbergIntegrand p (dist q.1 q.2 ^ 2) t ∂ρ.prod τ
  have hAint (ρ τ : Measure Sphere) [IsFiniteMeasure ρ] [IsFiniteMeasure τ] :
      Integrable (A ρ τ) (volume.restrict (Set.Ioi 0)) :=
    (integrable_schoenberg_joint hp0 hp1 (ρ.prod τ)).integral_prod_left
  have hpoint : ∀ᵐ t ∂volume.restrict (Set.Ioi 0),
      A μ μ t + A ν ν t ≤ A μ ν t + A ν μ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hcnd := measureConditionallyNegative_schoenbergKernel (p := p) ht
      μ ν hμ hν hmass
    simpa only [A, kernelPairEnergy_eq_integral_prod μ μ
        (continuous_schoenbergKernel_prod p t),
      kernelPairEnergy_eq_integral_prod ν ν
        (continuous_schoenbergKernel_prod p t),
      kernelPairEnergy_eq_integral_prod μ ν
        (continuous_schoenbergKernel_prod p t),
      kernelPairEnergy_eq_integral_prod ν μ
        (continuous_schoenbergKernel_prod p t),
      schoenbergKernel] using hcnd
  have hint :
      (∫ t in Set.Ioi (0 : ℝ), (A μ μ t + A ν ν t)) ≤
        ∫ t in Set.Ioi (0 : ℝ), (A μ ν t + A ν μ t) :=
    MeasureTheory.integral_mono_ae (hAint μ μ |>.add (hAint ν ν))
      (hAint μ ν |>.add (hAint ν μ)) hpoint
  rw [MeasureTheory.integral_add (hAint μ μ) (hAint ν ν),
    MeasureTheory.integral_add (hAint μ ν) (hAint ν μ),
    integral_schoenberg_swap hp0 hp1 (μ.prod μ),
    integral_schoenberg_swap hp0 hp1 (ν.prod ν),
    integral_schoenberg_swap hp0 hp1 (μ.prod ν),
    integral_schoenberg_swap hp0 hp1 (ν.prod μ)] at hint
  have hbase := schoenbergIntegral_one_pos hp0 hp1
  have hprod :
      (∫ q : Sphere × Sphere, (dist q.1 q.2 ^ 2) ^ p ∂μ.prod μ) +
        (∫ q : Sphere × Sphere, (dist q.1 q.2 ^ 2) ^ p ∂ν.prod ν) ≤
      (∫ q : Sphere × Sphere, (dist q.1 q.2 ^ 2) ^ p ∂μ.prod ν) +
        (∫ q : Sphere × Sphere, (dist q.1 q.2 ^ 2) ^ p ∂ν.prod μ) := by
    apply (mul_le_mul_left hbase).mp
    nlinarith
  simpa only [kernelPairEnergy_eq_integral_prod
      (K := fun x y : Sphere ↦ (dist x y ^ 2) ^ p) μ μ
      (continuous_distance_sq_rpow_prod hp0),
    kernelPairEnergy_eq_integral_prod
      (K := fun x y : Sphere ↦ (dist x y ^ 2) ^ p) ν ν
      (continuous_distance_sq_rpow_prod hp0),
    kernelPairEnergy_eq_integral_prod
      (K := fun x y : Sphere ↦ (dist x y ^ 2) ^ p) μ ν
      (continuous_distance_sq_rpow_prod hp0),
    kernelPairEnergy_eq_integral_prod
      (K := fun x y : Sphere ↦ (dist x y ^ 2) ^ p) ν μ
      (continuous_distance_sq_rpow_prod hp0)] using hprod

theorem distancePowerMeasureCND_of_pos_of_lt_two {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) : DistancePowerMeasureCND α := by
  unfold DistancePowerMeasureCND
  have hp0 : 0 < α / 2 := by linarith
  have hp1 : α / 2 < 1 := by linarith
  simpa only [distance_sq_rpow_half_alpha] using
    measureConditionallyNegative_distance_sq_rpow hp0 hp1

/-- The algebraic consequence of conditional negative definiteness when the
reference measure has constant potential: the energy deficit is nonnegative. -/
theorem measure_energy_deficit_nonneg_of_cnd {α I : ℝ}
    (hCND : DistancePowerMeasureCND α) (μ ν : Measure Sphere)
    (hμ : μ Set.univ ≠ ⊤) (hν : ν Set.univ ≠ ⊤)
    (hmass : μ Set.univ = ν Set.univ)
    (href : measurePairEnergy ν ν α = I)
    (hcross₁ : measurePairEnergy μ ν α = I)
    (hcross₂ : measurePairEnergy ν μ α = I) :
    0 ≤ I - measurePairEnergy μ μ α := by
  have h := hCND μ ν hμ hν hmass
  unfold measurePairEnergy at href hcross₁ hcross₂ ⊢
  rw [href, hcross₁, hcross₂] at h
  linarith

/-- CND applied directly to the concrete continuous BEMOC measure and the
normalized spherical reference measure. -/
theorem bemoc_continuous_deficit_nonneg_of_cnd
    (N : ℕ) {α I : ℝ} (hα : 0 < α)
    (hCND : DistancePowerMeasureCND α)
    (href : measurePairEnergy (sphereReferenceMeasure N)
      (sphereReferenceMeasure N) α = I)
    (hcross₁ : measurePairEnergy (continuousRingMeasure (bemocRingFamily N))
      (sphereReferenceMeasure N) α = I)
    (hcross₂ : measurePairEnergy (sphereReferenceMeasure N)
      (continuousRingMeasure (bemocRingFamily N)) α = I) :
    0 ≤ I - continuousRingEnergy (bemocRingFamily N) α := by
  have hμ : continuousRingMeasure (bemocRingFamily N) Set.univ ≠ ⊤ :=
    continuousRingMeasure_apply_univ_ne_top _
  have hν : sphereReferenceMeasure N Set.univ ≠ ⊤ := by simp
  have hmass : continuousRingMeasure (bemocRingFamily N) Set.univ =
      sphereReferenceMeasure N Set.univ := by simp
  have h := measure_energy_deficit_nonneg_of_cnd hCND
    (continuousRingMeasure (bemocRingFamily N)) (sphereReferenceMeasure N)
    hμ hν hmass href hcross₁ hcross₂
  rw [measurePairEnergy_continuousRingMeasure (bemocRingFamily N) hα] at h
  exact h

/-- CND applied to an arbitrary concrete `N`-point configuration. -/
theorem configuration_deficit_nonneg_of_cnd
    {N : ℕ} (X : Fin N → Sphere) {α I : ℝ} (hα : 0 < α)
    (hCND : DistancePowerMeasureCND α)
    (href : measurePairEnergy (sphereReferenceMeasure N)
      (sphereReferenceMeasure N) α = I)
    (hcross₁ : measurePairEnergy (pointMeasure X)
      (sphereReferenceMeasure N) α = I)
    (hcross₂ : measurePairEnergy (sphereReferenceMeasure N)
      (pointMeasure X) α = I) :
    0 ≤ I - rieszEnergy X α := by
  have hμ : pointMeasure X Set.univ ≠ ⊤ := by simp
  have hν : sphereReferenceMeasure N Set.univ ≠ ⊤ := by simp
  have hmass : pointMeasure X Set.univ = sphereReferenceMeasure N Set.univ := by simp
  have h := measure_energy_deficit_nonneg_of_cnd hCND
    (pointMeasure X) (sphereReferenceMeasure N)
    hμ hν hmass href hcross₁ hcross₂
  rw [measurePairEnergy_finPointMeasure_eq_rieszEnergy X hα] at h
  exact h

/-- Once the constant surface potential is known, CND alone gives the
nonnegative continuous BEMOC deficit. -/
theorem bemoc_continuous_deficit_nonneg_of_cnd_and_potential
    (N : ℕ) {α J : ℝ} (hα : 0 < α)
    (hCND : DistancePowerMeasureCND α)
    (hpot : HasConstantSpherePotential α J) :
    0 ≤ J * (N : ℝ) ^ 2 - continuousRingEnergy (bemocRingFamily N) α := by
  apply bemoc_continuous_deficit_nonneg_of_cnd N hα hCND
  · exact measurePairEnergy_sphereReference_self N hpot
  · exact measurePairEnergy_measure_sphereReference N hpot
      (continuousRingMeasure (bemocRingFamily N)) (by simp)
  · exact measurePairEnergy_sphereReference_measure N hα hpot
      (continuousRingMeasure (bemocRingFamily N))
      (continuousRingMeasure_apply_univ_ne_top _) (by simp)

/-- Once the constant surface potential is known, CND alone gives the
nonnegative deficit for every finite spherical configuration. -/
theorem configuration_deficit_nonneg_of_cnd_and_potential
    {N : ℕ} (X : Fin N → Sphere) {α J : ℝ} (hα : 0 < α)
    (hCND : DistancePowerMeasureCND α)
    (hpot : HasConstantSpherePotential α J) :
    0 ≤ J * (N : ℝ) ^ 2 - rieszEnergy X α := by
  apply configuration_deficit_nonneg_of_cnd X hα hCND
  · exact measurePairEnergy_sphereReference_self N hpot
  · exact measurePairEnergy_measure_sphereReference N hpot (pointMeasure X) (by simp)
  · exact measurePairEnergy_sphereReference_measure N hα hpot (pointMeasure X)
      (by simp) (by simp)

/-! ## Energy-level statement -/

/-- The continuous distance-power energy of normalized area on `S²`. -/
noncomputable def continuousEnergy (α : ℝ) : ℝ :=
  2 ^ (α + 1) / (α + 2)

theorem hasConstantSpherePotential_continuousEnergy {α : ℝ} (hα : 0 < α) :
    HasConstantSpherePotential α (continuousEnergy α) := by
  simpa [continuousEnergy] using hasConstantSpherePotential hα

@[simp] theorem continuousEnergy_one : continuousEnergy 1 = 4 / 3 := by
  norm_num [continuousEnergy]

/-! ## Concrete manuscript deficit terms -/

/-- Ordered-pair energy of the explicitly indexed BEMOC ring family. -/
noncomputable def bemocFiniteEnergy (α : ℝ) (N : ℕ) : ℝ :=
  finiteRieszEnergy (ringConfiguration (bemocRingFamily N)) α

/-- Total BEMOC deficit below the continuous spherical value. -/
noncomputable def bemocEnergyDeficit (α : ℝ) (N : ℕ) : ℝ :=
  continuousEnergy α * (N : ℝ) ^ 2 - bemocFiniteEnergy α N

/-- Latitude-quadrature contribution `A_{α,N}` of the manuscript. -/
noncomputable def bemocLatitudeDeficit (α : ℝ) (N : ℕ) : ℝ :=
  continuousEnergy α * (N : ℝ) ^ 2 -
    continuousRingEnergy (bemocRingFamily N) α

/-- Within-ring discretization contribution `B_{α,N}`. -/
noncomputable def bemocWithinRingDeficit (α : ℝ) (N : ℕ) : ℝ :=
  continuousWithinRingEnergy (bemocRingFamily N) α -
    withinRingEnergy (bemocRingFamily N) α

/-- Correct population-sensitive Riemann-sum weight in the sharp
`N = 4m²` within-ring limit.  The two terms come from the asymptotic
midpoint and shared-boundary populations `8mx/3` and `4mx/3`. -/
noncomputable def withinRingAsymptoticWeight (α : ℝ) : ℝ :=
  ((8 / 3 : ℝ) ^ (1 - α) + (4 / 3 : ℝ) ^ (1 - α)) *
    (2 ^ (1 + α / 2) - 1) / (α + 2)

/-- Corrected sharp coefficient for the BEMOC within-ring contribution.
At `α = 1` its weight reduces to `2(2√2-1)/3`; for general `α` the
population powers cannot be discarded. -/
noncomputable def withinRingLimitCoefficient (α : ℝ) : ℝ :=
  -withinRingAsymptoticWeight α * (4 * Real.pi) ^ α *
    realRiemannZeta (-α)

/-- Concrete BEMOC specialization of the exact within-ring aggregation
identity. -/
theorem bemocWithinRingDeficit_eq_aggregated
    {α : ℝ} {N : ℕ} (hα : 0 < α) :
    bemocWithinRingDeficit α N =
      aggregatedWithinRingDeficit (bemocRingFamily N) α := by
  exact withinRingDeficit_eq_aggregated (bemocRingFamily N) hα

/-- The concrete within-ring term is controlled by its exact
population-radius sum.  The remaining BEMOC geometry estimate bounds this
sum by `O(N^(1-α/2))`. -/
theorem exists_bemocWithinRingDeficit_weighted_bound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      |bemocWithinRingDeficit α N| ≤
        C * ∑ p, (bemocRingFamily N p).radius ^ α *
          ((bemocRingFamily N p).population : ℝ) ^ (1 - α) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_withinRingDeficit_bound_of_range hα0 hα2
  exact ⟨C, hC, fun N ↦ hbound (bemocRingFamily N)⟩

/-- Cross-ring angular-aliasing contribution `C_{α,N}`. -/
noncomputable def bemocCrossRingDeficit (α : ℝ) (N : ℕ) : ℝ :=
  continuousCrossRingEnergy (bemocRingFamily N) α -
    crossRingEnergy (bemocRingFamily N) α

/-- Equation (2.1) of `BEMOCRieszEnergies.tex`, with all three terms
identified concretely. -/
theorem bemocEnergyDeficit_eq_three_terms (α : ℝ) (N : ℕ) :
    bemocEnergyDeficit α N =
      bemocLatitudeDeficit α N + bemocWithinRingDeficit α N +
        bemocCrossRingDeficit α N := by
  simpa [bemocEnergyDeficit, bemocFiniteEnergy, bemocLatitudeDeficit,
    bemocWithinRingDeficit, bemocCrossRingDeficit] using
    bemoc_exact_decomposition N α (continuousEnergy α * (N : ℝ) ^ 2)

/-- The total concrete BEMOC deficit is nonnegative for `0 < α < 2`. -/
theorem bemocEnergyDeficit_nonneg {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (N : ℕ) : 0 ≤ bemocEnergyDeficit α N := by
  have h := configuration_deficit_nonneg_of_cnd_and_potential
    (finRingConfiguration (bemocRingFamily N) N
      (sum_bemocRingFamily_population N)) hα0
    (distancePowerMeasureCND_of_pos_of_lt_two hα0 hα2)
    (hasConstantSpherePotential_continuousEnergy hα0)
  rw [rieszEnergy_finRingConfiguration] at h
  exact h

/-- The three explicit analytic estimates required for the manuscript's
upper bound, stated at its final `N^(1-α/2)` scale. -/
structure BemocComponentBounds (α : ℝ) where
  C : ℝ
  C_pos : 0 < C
  N₀ : ℕ
  latitude : ∀ N ≥ N₀,
    |bemocLatitudeDeficit α N| ≤ C * (N : ℝ) ^ (1 - α / 2)
  withinRing : ∀ N ≥ N₀,
    |bemocWithinRingDeficit α N| ≤ C * (N : ℝ) ^ (1 - α / 2)
  crossRing : ∀ N ≥ N₀,
    |bemocCrossRingDeficit α N| ≤ C * (N : ℝ) ^ (1 - α / 2)

/-- Formal completion of the upper-bound step from the three concrete
manuscript estimates. -/
theorem bemoc_upper_bound_of_component_bounds {α : ℝ}
    (h : BemocComponentBounds α) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      bemocEnergyDeficit α N ≤ C * (N : ℝ) ^ (1 - α / 2) := by
  refine ⟨3 * h.C, mul_pos (by norm_num) h.C_pos, h.N₀, ?_⟩
  intro N hN
  have hscale : 0 ≤ (N : ℝ) ^ (1 - α / 2) := by positivity
  have hA := h.latitude N hN
  have hB := h.withinRing N hN
  have hC := h.crossRing N hN
  rw [bemocEnergyDeficit_eq_three_terms]
  have hA' : bemocLatitudeDeficit α N ≤ h.C * (N : ℝ) ^ (1 - α / 2) :=
    le_trans (le_abs_self _) hA
  have hB' : bemocWithinRingDeficit α N ≤ h.C * (N : ℝ) ^ (1 - α / 2) :=
    le_trans (le_abs_self _) hB
  have hC' : bemocCrossRingDeficit α N ≤ h.C * (N : ℝ) ^ (1 - α / 2) :=
    le_trans (le_abs_self _) hC
  nlinarith

/-- The complete nonnegative upper estimate for the explicit BEMOC family,
conditional only on the three named analytic bounds. -/
theorem bemoc_deficit_bound_of_component_bounds {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) (h : BemocComponentBounds α) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      0 ≤ bemocEnergyDeficit α N ∧
        bemocEnergyDeficit α N ≤ C * (N : ℝ) ^ (1 - α / 2) := by
  obtain ⟨C, hC, N₀, hUpper⟩ := bemoc_upper_bound_of_component_bounds h
  exact ⟨C, hC, N₀, fun N hN ↦ ⟨bemocEnergyDeficit_nonneg hα0 hα2 N,
    hUpper N hN⟩⟩

/- An abstract ordered-pair energy for the BEMOC configuration.

The concrete geometric point set will replace this interface once the
latitude/ring construction is available in mathlib-friendly form.
-/
variable (bemocEnergy : ℝ → ℕ → ℝ)

/-- The energy deficit from the continuous spherical value. -/
noncomputable def deficit (α : ℝ) (N : ℕ) : ℝ :=
  continuousEnergy α * (N : ℝ) ^ 2 - bemocEnergy α N

/-- Schoenberg CND and the evaluated constant spherical potential discharge
the nonnegativity obligation for every configuration sequence. -/
theorem ConfigurationSequence.deficit_nonneg_of_cnd
    (X : ConfigurationSequence) {α : ℝ} (hα : 0 < α)
    (hCND : DistancePowerMeasureCND α)
    (hpot : HasConstantSpherePotential α (continuousEnergy α)) :
    ∀ N, 0 ≤ deficit X.energy α N := by
  intro N
  simpa [deficit, ConfigurationSequence.energy] using
    configuration_deficit_nonneg_of_cnd_and_potential
      (X.points N) hα hCND hpot

/-- The corresponding nonnegativity of the latitude-quadrature term for the
concrete continuously spread BEMOC rings. -/
theorem bemoc_latitude_deficit_nonneg_of_cnd
    (N : ℕ) {α : ℝ} (hα : 0 < α)
    (hCND : DistancePowerMeasureCND α)
    (hpot : HasConstantSpherePotential α (continuousEnergy α)) :
    0 ≤ continuousEnergy α * (N : ℝ) ^ 2 -
      continuousRingEnergy (bemocRingFamily N) α := by
  exact bemoc_continuous_deficit_nonneg_of_cnd_and_potential N hα hCND hpot

/-- A precise two-sided `Θ` statement with constants depending on `α`. -/
def HasRieszScale (α : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * (N : ℝ) ^ (1 - α / 2) ≤ deficit bemocEnergy α N ∧
      deficit bemocEnergy α N ≤ C * (N : ℝ) ^ (1 - α / 2)

/-! ## Explicit analytic interfaces

The paper proves the upper estimate by an exact three-term decomposition.
The following structure records exactly those obligations. -/

structure UpperBoundInputs (α : ℝ) where
  latitude : ℕ → ℝ
  withinRing : ℕ → ℝ
  crossRing : ℕ → ℝ
  decomposition : ∀ N,
    deficit bemocEnergy α N = latitude N + withinRing N + crossRing N
  latitude_nonneg : ∀ N, 0 ≤ latitude N
  within_nonneg : ∀ N, 0 ≤ withinRing N
  deficit_nonneg : ∀ N, 0 ≤ deficit bemocEnergy α N
  bound : ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |latitude N| ≤ C * (N : ℝ) ^ (1 - α / 2) ∧
    |withinRing N| ≤ C * (N : ℝ) ^ (1 - α / 2) ∧
    |crossRing N| ≤ C * (N : ℝ) ^ (1 - α / 2)

/-- Wagner's universal lower bound, in the sign and normalization used here.

Wagner writes `s = -α` and minimizes the energy with kernel
`-|x-y|^α`.  Thus his lower estimate for the second-order term says exactly
that the deficit below the continuous maximal distance-power energy is at
least a positive multiple of `N^(1-α/2)`, for every configuration.

The restriction `1 ≤ N` avoids assigning mathematical content to the empty
configuration.  The classical theorem supplies a constant depending only on
`α`, uniformly in both `N` and the configuration. -/
def HasWagnerLowerBound (α : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (X : Fin N → Sphere), 1 ≤ N →
    c * (N : ℝ) ^ (1 - α / 2) ≤
      continuousEnergy α * (N : ℝ) ^ 2 - rieszEnergy X α

/-- The sequence-level universal lower bound required by the final assembly. -/
def LowerBoundInput (α : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    c * (N : ℝ) ^ (1 - α / 2) ≤ deficit bemocEnergy α N

/-- Wagner's configuration-uniform theorem supplies the lower input for any
sequence of spherical configurations. -/
theorem ConfigurationSequence.lowerBoundInput_of_wagner
    (X : ConfigurationSequence) {α : ℝ} (hWagner : HasWagnerLowerBound α) :
    LowerBoundInput X.energy α := by
  obtain ⟨c, hc, hbound⟩ := hWagner
  refine ⟨c, hc, 1, ?_⟩
  intro N hN
  simpa [deficit, ConfigurationSequence.energy] using hbound N (X.points N) hN

/-- Direct specialization of Wagner's bound to the concrete BEMOC sequence. -/
theorem bemoc_lowerBoundInput_of_wagner {α : ℝ}
    (hWagner : HasWagnerLowerBound α) :
    LowerBoundInput bemocRingConstructionSequence.toConfigurationSequence.energy α :=
  ConfigurationSequence.lowerBoundInput_of_wagner
    bemocRingConstructionSequence.toConfigurationSequence hWagner

/-! ## Assembly of the proof -/

theorem upper_bound_of_inputs {α : ℝ}
    (h : UpperBoundInputs bemocEnergy α) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      deficit bemocEnergy α N ≤ C * (N : ℝ) ^ (1 - α / 2) := by
  obtain ⟨C, hC, N₀, hbound⟩ := h.bound
  refine ⟨3 * C, by positivity, N₀, ?_⟩
  intro N hN
  have hx : 0 ≤ (N : ℝ) ^ (1 - α / 2) := by positivity
  obtain ⟨hA, hB, hCross⟩ := hbound N hN
  have hA' : h.latitude N ≤ C * (N : ℝ) ^ (1 - α / 2) :=
    le_trans (le_abs_self _) hA
  have hB' : h.withinRing N ≤ C * (N : ℝ) ^ (1 - α / 2) :=
    le_trans (le_abs_self _) hB
  have hCross' : h.crossRing N ≤ C * (N : ℝ) ^ (1 - α / 2) :=
    le_trans (le_abs_self _) hCross
  rw [h.decomposition]
  nlinarith

/-- Formal assembly of the paper's main theorem.

All analytic content is visible in the two arguments: the three component
bounds and the universal lower bound. -/
theorem main_theorem_from_inputs {α : ℝ}
    (hUpper : UpperBoundInputs bemocEnergy α)
    (hLower : LowerBoundInput bemocEnergy α) :
    HasRieszScale bemocEnergy α := by
  obtain ⟨c, hc, NLower, hlower⟩ := hLower
  obtain ⟨C, hC, NUpper, hupper⟩ := upper_bound_of_inputs bemocEnergy hUpper
  refine ⟨c, C + c, hc, by linarith, max NLower NUpper, ?_⟩
  intro N hN
  have hNL : NLower ≤ N := le_trans (le_max_left _ _) hN
  have hNU : NUpper ≤ N := le_trans (le_max_right _ _) hN
  have hx : 0 ≤ (N : ℝ) ^ (1 - α / 2) := by positivity
  constructor
  · exact hlower N hNL
  · have hu := hupper N hNU
    nlinarith

/-- The paper's parameter-range wrapper for a concrete sequence of spherical
configurations.  The range hypotheses are recorded here because the analytic
inputs are valid precisely for `0 < α < 2`. -/
theorem negative_riesz_main_theorem
    (X : ConfigurationSequence) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hUpper : UpperBoundInputs X.energy α)
    (hLower : LowerBoundInput X.energy α) :
    HasRieszScale X.energy α := by
  have _ := hα0
  have _ := hα2
  exact main_theorem_from_inputs X.energy hUpper hLower

/-- Main-theorem wrapper using Wagner's configuration-uniform lower bound
directly, rather than a separately supplied sequence-level lower input. -/
theorem negative_riesz_main_theorem_of_wagner
    (X : ConfigurationSequence) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hUpper : UpperBoundInputs X.energy α)
    (hWagner : HasWagnerLowerBound α) :
    HasRieszScale X.energy α := by
  exact negative_riesz_main_theorem X hα0 hα2 hUpper
    (X.lowerBoundInput_of_wagner hWagner)

theorem distance_exponent : (1 : ℝ) - 1 / 2 = 1 / 2 := by
  norm_num

end BEMOC
