import BEMOCFormalization.LatitudePowerJetBounds

/-!
# Graded normalized-gap bounds on comparable latitude rectangles

The common radius envelope is deliberately coarse.  The power derivative
estimate (5.5) instead needs the grading that is visible in the explicit
normalized-gap formulas.  This file proves that grading under the local
comparable-rectangle assumptions: both radii lie in `[R,40R]`, the height
separation is at most a fixed multiple of `R²`, and the normalized gap is in
the concrete fixed chart `q ≤ 3200`.
-/

open Set

namespace BEMOC

set_option maxHeartbeats 800000

/-- The six graded normalized-gap estimates used in the singular
mixed-derivative chain. -/
def LatitudeComparableGradedGapBound (s t R K : ℝ) : Prop :=
  |normalizedLatitudeGapDs s t| ≤ |s - t| * R⁻¹ ^ 4 ∧
  |normalizedLatitudeGapDst s t| ≤ 5121600 * R⁻¹ ^ 4 ∧
  |normalizedLatitudeGapDss s t| ≤ (1600 + 3 * K) * R⁻¹ ^ 4 ∧
  |normalizedLatitudeGapDsst s t| ≤ 15364801 * R⁻¹ ^ 6 ∧
  |normalizedLatitudeGapDstt s t| ≤ 15364801 * R⁻¹ ^ 6 ∧
  |normalizedLatitudeGapDsstt s t| ≤ 46094407 * R⁻¹ ^ 8

private theorem radius_product_upper
    {s t R : ℝ} (hR : 0 < R)
    (hsupper : heightRadius s ≤ 40 * R)
    (htupper : heightRadius t ≤ 40 * R) :
    heightRadius s * heightRadius t ≤ 1600 * R ^ 2 := by
  have hs0 : 0 ≤ heightRadius s := by
    unfold heightRadius
    positivity
  have ht0 : 0 ≤ heightRadius t := by
    unfold heightRadius
    positivity
  calc
    heightRadius s * heightRadius t ≤ (40 * R) * (40 * R) := by
      gcongr
    _ = 1600 * R ^ 2 := by ring

private theorem one_sub_mul_le_radius_product
    {s t R : ℝ} (hR : 0 < R)
    (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t)
    (hgap : normalizedLatitudeGap s t ≤ 3200) :
    1 - s * t ≤ 3201 * (heightRadius s * heightRadius t) := by
  have hrs : 0 < heightRadius s := hR.trans_le hsfloor
  have hrt : 0 < heightRadius t := hR.trans_le htfloor
  have hp : 0 < heightRadius s * heightRadius t := mul_pos hrs hrt
  unfold normalizedLatitudeGap at hgap
  have hmul := (div_le_iff₀ hp).mp (by linarith :
    (1 - s * t) / (heightRadius s * heightRadius t) ≤ 3201)
  nlinarith

/-- Direct proof of the graded comparable-rectangle normalized-gap jet. -/
theorem latitudeComparableGradedGapBound
    {s t R K : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1)
    (hR : 0 < R) (hK : 0 ≤ K)
    (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t)
    (hsupper : heightRadius s ≤ 40 * R)
    (htupper : heightRadius t ≤ 40 * R)
    (hsep : |s - t| ≤ K * R ^ 2)
    (hgap : normalizedLatitudeGap s t ≤ 3200) :
    LatitudeComparableGradedGapBound s t R K := by
  have hsabs : |s| ≤ 1 := abs_le.mpr hs
  have htabs : |t| ≤ 1 := abs_le.mpr ht
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
  have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
  have hrprod := radius_product_upper hR hsupper htupper
  have honeUpper :=
    one_sub_mul_le_radius_product hR hsfloor htfloor hgap
  have hstle : s * t ≤ 1 := by
    have habs : |s * t| ≤ 1 := by
      rw [abs_mul]
      calc
        |s| * |t| ≤ 1 * 1 := by gcongr
        _ = 1 := by norm_num
    exact (le_abs_self (s * t)).trans habs
  have hone0 : 0 ≤ 1 - s * t := sub_nonneg.mpr hstle
  have honeAbs :
      |1 - s * t| ≤ 5121600 * R ^ 2 := by
    rw [abs_of_nonneg hone0]
    nlinarith
  have honeAbs' :
      |s * t - 1| ≤ 5121600 * R ^ 2 := by
    rw [abs_sub_comm]
    exact honeAbs
  have hDs0 := abs_div_pow_mul_pow_le (m := 3) (n := 1)
    (z := s - t) (C := |s - t|)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (abs_nonneg _) le_rfl hR hsfloor htfloor
  have hDs :
      |normalizedLatitudeGapDs s t| ≤ |s - t| * R⁻¹ ^ 4 := by
    unfold normalizedLatitudeGapDs
    simpa using hDs0
  have hDst0 := abs_div_pow_mul_pow_le (m := 3) (n := 3)
    (z := s * t - 1) (C := 5121600 * R ^ 2)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (by positivity) honeAbs' hR hsfloor htfloor
  have hDst :
      |normalizedLatitudeGapDst s t| ≤ 5121600 * R⁻¹ ^ 4 := by
    unfold normalizedLatitudeGapDst
    calc
      |(s * t - 1) /
          (heightRadius s ^ 3 * heightRadius t ^ 3)| ≤
          (5121600 * R ^ 2) * R⁻¹ ^ 6 := hDst0
      _ = 5121600 * R⁻¹ ^ 4 := by
        field_simp [hR.ne']
        ring
  have hrsSq : heightRadius s ^ 2 ≤ 1600 * R ^ 2 := by
    calc
      heightRadius s ^ 2 ≤ (40 * R) ^ 2 := by gcongr
      _ = 1600 * R ^ 2 := by ring
  have hsdiff : |3 * s * (s - t)| ≤ 3 * K * R ^ 2 := by
    rw [abs_mul, abs_mul]
    norm_num
    calc
      3 * |s| * |s - t| ≤ 3 * 1 * (K * R ^ 2) := by gcongr
      _ = 3 * K * R ^ 2 := by ring
  have hnumDss :
      |heightRadius s ^ 2 + 3 * s * (s - t)| ≤
        (1600 + 3 * K) * R ^ 2 := by
    calc
      |_ + _| ≤ |heightRadius s ^ 2| +
          |3 * s * (s - t)| := abs_add _ _
      _ ≤ 1600 * R ^ 2 + 3 * K * R ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _)]
        gcongr
      _ = (1600 + 3 * K) * R ^ 2 := by ring
  have hDss0 := abs_div_pow_mul_pow_le (m := 5) (n := 1)
    (z := heightRadius s ^ 2 + 3 * s * (s - t))
    (C := (1600 + 3 * K) * R ^ 2)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (by positivity) hnumDss hR hsfloor htfloor
  have hDss :
      |normalizedLatitudeGapDss s t| ≤
        (1600 + 3 * K) * R⁻¹ ^ 4 := by
    unfold normalizedLatitudeGapDss
    have hDss0' :
        |(heightRadius s ^ 2 + 3 * s * (s - t)) /
          (heightRadius s ^ 5 * heightRadius t)| ≤
          ((1600 + 3 * K) * R ^ 2) * R⁻¹ ^ 6 := by
      simpa only [pow_one, Nat.reduceAdd] using hDss0
    calc
      |_ / _| ≤ ((1600 + 3 * K) * R ^ 2) * R⁻¹ ^ 6 := hDss0'
      _ = (1600 + 3 * K) * R⁻¹ ^ 4 := by
        field_simp [hR.ne']
        ring
  have htNum : |t| ≤ 1 := htabs
  have hfirstSst := abs_div_pow_mul_pow_le (m := 3) (n := 3)
    (z := t) (C := 1)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (by norm_num) htNum hR hsfloor htfloor
  have hnumSst :
      |3 * s * (1 - s * t)| ≤ 15364800 * R ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hone0]
    norm_num
    calc
      3 * |s| * (1 - s * t) ≤
          3 * 1 * (3201 * (heightRadius s * heightRadius t)) := by gcongr
      _ ≤ 15364800 * R ^ 2 := by nlinarith
  have hsecondSst := abs_div_pow_mul_pow_le (m := 5) (n := 3)
    (z := 3 * s * (1 - s * t)) (C := 15364800 * R ^ 2)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (by positivity) hnumSst hR hsfloor htfloor
  have hDsst :
      |normalizedLatitudeGapDsst s t| ≤ 15364801 * R⁻¹ ^ 6 := by
    unfold normalizedLatitudeGapDsst
    calc
      |_ - _| ≤
          |t / (heightRadius s ^ 3 * heightRadius t ^ 3)| +
          |3 * s * (1 - s * t) /
            (heightRadius s ^ 5 * heightRadius t ^ 3)| := abs_sub _ _
      _ ≤ R⁻¹ ^ 6 + (15364800 * R ^ 2) * R⁻¹ ^ 8 :=
        add_le_add (by simpa using hfirstSst) (by simpa using hsecondSst)
      _ = 15364801 * R⁻¹ ^ 6 := by
        field_simp [hR.ne']
        ring
  have hDsstSwap :
      |normalizedLatitudeGapDsst t s| ≤ 15364801 * R⁻¹ ^ 6 := by
    -- The preceding argument is symmetric; repeat it through the existing
    -- explicit `(2,1)` estimate with swapped variables.
    have hsNum : |s| ≤ 1 := hsabs
    have hfirst := abs_div_pow_mul_pow_le (m := 3) (n := 3)
      (z := s) (C := 1)
      (x := heightRadius t) (y := heightRadius s) (R := R)
      (by norm_num) hsNum hR htfloor hsfloor
    have honeComm : 1 - t * s = 1 - s * t := by ring
    have hnum :
        |3 * t * (1 - t * s)| ≤ 15364800 * R ^ 2 := by
      rw [honeComm, abs_mul, abs_mul, abs_of_nonneg hone0]
      norm_num
      calc
        3 * |t| * (1 - s * t) ≤
            3 * 1 * (3201 * (heightRadius s * heightRadius t)) := by gcongr
        _ ≤ 15364800 * R ^ 2 := by nlinarith
    have hsecond := abs_div_pow_mul_pow_le (m := 5) (n := 3)
      (z := 3 * t * (1 - t * s)) (C := 15364800 * R ^ 2)
      (x := heightRadius t) (y := heightRadius s) (R := R)
      (by positivity) hnum hR htfloor hsfloor
    unfold normalizedLatitudeGapDsst
    calc
      |_ - _| ≤
          |s / (heightRadius t ^ 3 * heightRadius s ^ 3)| +
          |3 * t * (1 - t * s) /
            (heightRadius t ^ 5 * heightRadius s ^ 3)| := abs_sub _ _
      _ ≤ R⁻¹ ^ 6 + (15364800 * R ^ 2) * R⁻¹ ^ 8 :=
        add_le_add (by simpa using hfirst) (by simpa using hsecond)
      _ = 15364801 * R⁻¹ ^ 6 := by
        field_simp [hR.ne']
        ring
  have hDstt :
      |normalizedLatitudeGapDstt s t| ≤ 15364801 * R⁻¹ ^ 6 := by
    unfold normalizedLatitudeGapDstt
    exact hDsstSwap
  have htRadiusSq := heightRadius_sq ht
  have hnum1 :
      |heightRadius t ^ 2 + 3 * t ^ 2| ≤ 4 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg t]
  have hnum2 : |3 * s ^ 2| ≤ 3 := by
    rw [abs_mul, abs_of_nonneg (by norm_num), abs_pow]
    calc
      3 * |s| ^ 2 ≤ 3 * 1 ^ 2 := by gcongr
      _ = 3 := by norm_num
  have hnum3 :
      |9 * s * t * (1 - s * t)| ≤ 46094400 * R ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hone0]
    norm_num
    calc
      9 * |s| * |t| * (1 - s * t) ≤
          9 * 1 * 1 * (3201 * (heightRadius s * heightRadius t)) := by
            gcongr
      _ ≤ 46094400 * R ^ 2 := by nlinarith
  have hh1 := abs_div_pow_mul_pow_le (m := 3) (n := 5)
    (z := heightRadius t ^ 2 + 3 * t ^ 2) (C := 4)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (by norm_num) hnum1 hR hsfloor htfloor
  have hh2 := abs_div_pow_mul_pow_le (m := 5) (n := 3)
    (z := 3 * s ^ 2) (C := 3)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (by norm_num) hnum2 hR hsfloor htfloor
  have hh3 := abs_div_pow_mul_pow_le (m := 5) (n := 5)
    (z := 9 * s * t * (1 - s * t)) (C := 46094400 * R ^ 2)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (by positivity) hnum3 hR hsfloor htfloor
  have hDsstt :
      |normalizedLatitudeGapDsstt s t| ≤ 46094407 * R⁻¹ ^ 8 := by
    unfold normalizedLatitudeGapDsstt
    calc
      |_ + _ - _| ≤
          |(heightRadius t ^ 2 + 3 * t ^ 2) /
            (heightRadius s ^ 3 * heightRadius t ^ 5)| +
          |3 * s ^ 2 /
            (heightRadius s ^ 5 * heightRadius t ^ 3)| +
          |9 * s * t * (1 - s * t) /
            (heightRadius s ^ 5 * heightRadius t ^ 5)| := by
              exact (abs_sub _ _).trans
                (add_le_add_right (abs_add _ _) _)
      _ ≤ 4 * R⁻¹ ^ 8 + 3 * R⁻¹ ^ 8 +
          (46094400 * R ^ 2) * R⁻¹ ^ 10 := by gcongr
      _ = 46094407 * R⁻¹ ^ 8 := by
        field_simp [hR.ne']
        ring
  exact ⟨hDs, hDst, hDss, hDsst, hDstt, hDsstt⟩

/-- The physical scale on the right-hand side of (5.5). -/
noncomputable def latitudePowerDerivativeScale (α R d : ℝ) : ℝ :=
  R ^ (-2 - α) * d ^ (α - 3)

/-- Generic conversion of a quadratic normalized-gap lower bound into the
negative powers used by the cusp moments.  It records, in a reusable exact
form, the exponent arithmetic behind (5.5). -/
theorem rpow_le_of_comparable_quadratic_gap
    {x c d R e : ℝ} (_hx : 0 < x) (hc : 0 < c)
    (hd : 0 < d) (hR : 0 < R) (he : e ≤ 0)
    (hlower : c * d ^ (2 : ℝ) * R ^ (-4 : ℝ) ≤ x) :
    x ^ e ≤
      c ^ e * d ^ (2 * e) * R ^ ((-4) * e) := by
  have hb : 0 < c * d ^ (2 : ℝ) * R ^ (-4 : ℝ) := by positivity
  calc
    x ^ e ≤ (c * d ^ (2 : ℝ) * R ^ (-4 : ℝ)) ^ e :=
      Real.rpow_le_rpow_of_nonpos hb hlower he
    _ = (c * d ^ (2 : ℝ)) ^ e * (R ^ (-4 : ℝ)) ^ e := by
      rw [Real.mul_rpow (mul_nonneg hc.le (Real.rpow_nonneg hd.le _))
        (Real.rpow_nonneg hR.le _)]
    _ = (c ^ e * (d ^ (2 : ℝ)) ^ e) *
        (R ^ (-4 : ℝ)) ^ e := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hd.le _)]
    _ = c ^ e * d ^ (2 * e) * R ^ ((-4) * e) := by
      rw [← Real.rpow_mul hd.le, ← Real.rpow_mul hR.le]

/-- The four exact top-level Leibniz blocks in the explicit mixed
derivative, each measured at the scale of (5.5).  This is a convenient
interface for retaining the graded powers inside each jet instead of
destroying them with a common envelope. -/
def LatitudeComparableMixedTermBound
    (α s t R C : ℝ) : Prop :=
  |latitudeJetMulD2
      (latitudePowerDss α s t) (latitudePowerDsst α s t)
        (latitudePowerDsstt α s t)
      (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
        (latitudeCusp0Dtt α s t)| ≤
      C * latitudePowerDerivativeScale α R |s - t| ∧
  |latitudeJetMul3D2
      (latitudePowerDs α s t) (latitudePowerDst α s t)
        (latitudePowerDstt α s t)
      (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
        (latitudeCusp1Dtt α s t)
      (normalizedLatitudeGapDs s t) (normalizedLatitudeGapDst s t)
        (normalizedLatitudeGapDstt s t)| ≤
      C * latitudePowerDerivativeScale α R |s - t| ∧
  |latitudeJetMul3D2
      (latitudePower α s t) (latitudePowerDt α s t)
        (latitudePowerDtt α s t)
      (latitudeCusp2 α s t) (latitudeCusp2Dt α s t)
        (latitudeCusp2Dtt α s t)
      (normalizedLatitudeGapDs s t ^ 2)
        (2 * normalizedLatitudeGapDs s t *
          normalizedLatitudeGapDst s t)
        (2 * normalizedLatitudeGapDst s t ^ 2 +
          2 * normalizedLatitudeGapDs s t *
            normalizedLatitudeGapDstt s t)| ≤
      C * latitudePowerDerivativeScale α R |s - t| ∧
  |latitudeJetMul3D2
      (latitudePower α s t) (latitudePowerDt α s t)
        (latitudePowerDtt α s t)
      (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
        (latitudeCusp1Dtt α s t)
      (normalizedLatitudeGapDss s t) (normalizedLatitudeGapDsst s t)
        (normalizedLatitudeGapDsstt s t)| ≤
      C * latitudePowerDerivativeScale α R |s - t|

/-- Exact sharp-scale assembly: once the four graded Leibniz blocks have
the natural scale, the genuine mixed derivative has the same scale with
the explicit total weight `5` (the second block occurs with coefficient
two). -/
theorem abs_variableReducedLatitudeKernelDsstt_le_of_comparableTerms
    {α s t R C : ℝ} (_hC : 0 ≤ C)
    (_hscale : 0 ≤ latitudePowerDerivativeScale α R |s - t|)
    (hterms : LatitudeComparableMixedTermBound α s t R C) :
    |variableReducedLatitudeKernelDsstt α s t| ≤
      5 * C * latitudePowerDerivativeScale α R |s - t| := by
  rcases hterms with ⟨h1, h2, h3, h4⟩
  unfold variableReducedLatitudeKernelDsstt
  calc
    |_ + 2 * _ + _ + _| ≤
        |latitudeJetMulD2
          (latitudePowerDss α s t) (latitudePowerDsst α s t)
          (latitudePowerDsstt α s t)
          (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
          (latitudeCusp0Dtt α s t)| +
        2 * |latitudeJetMul3D2
          (latitudePowerDs α s t) (latitudePowerDst α s t)
          (latitudePowerDstt α s t)
          (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
          (normalizedLatitudeGapDs s t) (normalizedLatitudeGapDst s t)
          (normalizedLatitudeGapDstt s t)| +
        |latitudeJetMul3D2
          (latitudePower α s t) (latitudePowerDt α s t)
          (latitudePowerDtt α s t)
          (latitudeCusp2 α s t) (latitudeCusp2Dt α s t)
          (latitudeCusp2Dtt α s t)
          (normalizedLatitudeGapDs s t ^ 2)
          (2 * normalizedLatitudeGapDs s t *
            normalizedLatitudeGapDst s t)
          (2 * normalizedLatitudeGapDst s t ^ 2 +
            2 * normalizedLatitudeGapDs s t *
              normalizedLatitudeGapDstt s t)| +
        |latitudeJetMul3D2
          (latitudePower α s t) (latitudePowerDt α s t)
          (latitudePowerDtt α s t)
          (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
          (normalizedLatitudeGapDss s t)
          (normalizedLatitudeGapDsst s t)
          (normalizedLatitudeGapDsstt s t)| := by
      have houter := abs_add
        (latitudeJetMulD2
          (latitudePowerDss α s t) (latitudePowerDsst α s t)
          (latitudePowerDsstt α s t)
          (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
          (latitudeCusp0Dtt α s t) +
        2 * latitudeJetMul3D2
          (latitudePowerDs α s t) (latitudePowerDst α s t)
          (latitudePowerDstt α s t)
          (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
          (normalizedLatitudeGapDs s t) (normalizedLatitudeGapDst s t)
          (normalizedLatitudeGapDstt s t) +
        latitudeJetMul3D2
          (latitudePower α s t) (latitudePowerDt α s t)
          (latitudePowerDtt α s t)
          (latitudeCusp2 α s t) (latitudeCusp2Dt α s t)
          (latitudeCusp2Dtt α s t)
          (normalizedLatitudeGapDs s t ^ 2)
          (2 * normalizedLatitudeGapDs s t *
            normalizedLatitudeGapDst s t)
          (2 * normalizedLatitudeGapDst s t ^ 2 +
            2 * normalizedLatitudeGapDs s t *
              normalizedLatitudeGapDstt s t))
        (latitudeJetMul3D2
          (latitudePower α s t) (latitudePowerDt α s t)
          (latitudePowerDtt α s t)
          (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
          (normalizedLatitudeGapDss s t)
          (normalizedLatitudeGapDsst s t)
          (normalizedLatitudeGapDsstt s t))
      have hmiddle := abs_add
        (latitudeJetMulD2
          (latitudePowerDss α s t) (latitudePowerDsst α s t)
          (latitudePowerDsstt α s t)
          (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
          (latitudeCusp0Dtt α s t) +
        2 * latitudeJetMul3D2
          (latitudePowerDs α s t) (latitudePowerDst α s t)
          (latitudePowerDstt α s t)
          (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
          (normalizedLatitudeGapDs s t) (normalizedLatitudeGapDst s t)
          (normalizedLatitudeGapDstt s t))
        (latitudeJetMul3D2
          (latitudePower α s t) (latitudePowerDt α s t)
          (latitudePowerDtt α s t)
          (latitudeCusp2 α s t) (latitudeCusp2Dt α s t)
          (latitudeCusp2Dtt α s t)
          (normalizedLatitudeGapDs s t ^ 2)
          (2 * normalizedLatitudeGapDs s t *
            normalizedLatitudeGapDst s t)
          (2 * normalizedLatitudeGapDst s t ^ 2 +
            2 * normalizedLatitudeGapDs s t *
              normalizedLatitudeGapDstt s t))
      have hinner := abs_add
        (latitudeJetMulD2
          (latitudePowerDss α s t) (latitudePowerDsst α s t)
          (latitudePowerDsstt α s t)
          (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
          (latitudeCusp0Dtt α s t))
        (2 * latitudeJetMul3D2
          (latitudePowerDs α s t) (latitudePowerDst α s t)
          (latitudePowerDstt α s t)
          (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
          (normalizedLatitudeGapDs s t) (normalizedLatitudeGapDst s t)
          (normalizedLatitudeGapDstt s t))
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hinner
      linarith
    _ ≤ C * latitudePowerDerivativeScale α R |s - t| +
        2 * (C * latitudePowerDerivativeScale α R |s - t|) +
        C * latitudePowerDerivativeScale α R |s - t| +
        C * latitudePowerDerivativeScale α R |s - t| := by gcongr
    _ = 5 * C * latitudePowerDerivativeScale α R |s - t| := by ring

end BEMOC
