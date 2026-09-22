import BEMOCFormalization.NegativeType

open scoped BigOperators Pointwise
open MeasureTheory
namespace BEMOC.Definitive

/-! ### Normalized surface area on the sphere -/

theorem sphereHaarMeasure_apply_univ_ne_zero :
    volume.toSphere (E := Ambient) Set.univ ≠ 0 := by
  rw [Measure.toSphere_apply_univ]
  exact ne_of_gt (ENNReal.mul_pos (by norm_num)
    (ne_of_gt (Metric.measure_ball_pos volume 0 (by norm_num))))

@[simp] theorem sigma_apply_univ :
    sigma Set.univ = 1 := by
  rw [sigma, Measure.smul_apply]
  exact ENNReal.inv_mul_cancel sphereHaarMeasure_apply_univ_ne_zero
    (measure_ne_top (volume.toSphere : Measure Sphere) Set.univ)

/-- The normalized geometric surface measure is a probability measure. -/
instance : IsProbabilityMeasure sigma := ⟨sigma_apply_univ⟩

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
  Measure.map sphereHeight sigma = uniformHeightMeasure

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
  let μ := Measure.map sphereHeight sigma
  have hμuniv : μ Set.univ = 1 := by
    change Measure.map sphereHeight sigma Set.univ = 1
    rw [Measure.map_apply continuous_sphereHeight.measurable MeasurableSet.univ]
    simp
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (by rw [hμuniv]; norm_num)
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply continuous_sphereHeight.measurable measurableSet_Iic,
    uniformHeightMeasure_Iic]
  change sigma {x : Sphere | sphereHeight x ≤ a} = uniformHeightCDF a
  unfold sigma
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
    ∫ y : Sphere, dist northPole y ^ α ∂sigma =
      2 ^ (α + 1) / (α + 2) := by
  simp_rw [northPole_distancePower_eq_clippedHeightKernel α]
  have hmap := MeasureTheory.integral_map
    (μ := sigma) (continuous_sphereHeight.measurable.aemeasurable)
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

theorem sigma_reflection_invariant :
    IsReflectionInvariant sigma := by
  intro v
  let K : Submodule ℝ Ambient := (ℝ ∙ v)ᗮ
  let T : Ambient ≃ₗᵢ[ℝ] Ambient := K.reflection
  change Measure.map (sphereLinearIsometryEquiv T) sigma =
    sigma
  ext s hs
  rw [Measure.map_apply (sphereLinearIsometryEquiv T).measurable hs]
  unfold sigma
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
  N • sigma

@[simp] theorem sphereReferenceMeasure_apply_univ (N : ℕ) :
    sphereReferenceMeasure N Set.univ = N := by
  simp [sphereReferenceMeasure, Measure.add_apply]

/-- The normalized surface measure has constant distance-power potential
`J`.  The paper later evaluates `J` as `2^(α+1)/(α+2)`. -/
def HasConstantSpherePotential (α J : ℝ) : Prop :=
  ∀ x : Sphere,
    ∫ y : Sphere, dist x y ^ α ∂sigma = J

/-- The constant-potential formula reduced to the height marginal of
normalized surface area.  Reflection invariance and the one-dimensional
integral evaluation are fully discharged here. -/
theorem hasConstantSpherePotential_of_uniform_height
    {α : ℝ} (hα : 0 < α) (hheight : HasUniformHeightMarginal) :
    HasConstantSpherePotential α (2 ^ (α + 1) / (α + 2)) := by
  intro x
  rw [sphere_potential_eq_northPole_of_invariant sigma
    sigma_reflection_invariant x]
  exact northPole_potential_of_uniform_height hα hheight

theorem hasConstantSpherePotential {α : ℝ} (hα : 0 < α) :
    HasConstantSpherePotential α (2 ^ (α + 1) / (α + 2)) :=
  hasConstantSpherePotential_of_uniform_height hα hasUniformHeightMarginal

/-- The sphere's distance-power potential has the manuscript's exact value. -/
theorem constantPotential_of_pos {α : ℝ} (hα : 0 < α) : ConstantPotential α := by
  intro x
  exact hasConstantSpherePotential hα x


end BEMOC.Definitive
