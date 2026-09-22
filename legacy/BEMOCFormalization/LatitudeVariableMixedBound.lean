import BEMOCFormalization.LatitudeVariableMixedDerivative

/-!
# A quantitative envelope for the mixed latitude derivative

The preceding file identifies the genuine mixed `(2,2)` derivative of the
variable-coefficient normal form.  Here we separate the remaining estimate
from that calculus: four nonnegative envelopes control respectively the
power two-jets, the reduced-cusp two-jets, and the normalized-gap two-jets.
The numerical constant is explicit and comes only from the product rule.

This is the pointwise algebraic form of the estimate used in (5.5).  In
particular, the final theorem below turns scale bounds for the three jets
into the exact `R⁻²⁻ᵅ |s-t|ᵅ⁻³` majorant, with every derivative displayed
in the checked chain.
-/

namespace BEMOC

/-- A common absolute bound for all power-coefficient entries occurring in
the mixed `(2,2)` chain. -/
def LatitudePowerJetBound (α s t P : ℝ) : Prop :=
  0 ≤ P ∧
  |latitudePower α s t| ≤ P ∧
  |latitudePowerDt α s t| ≤ P ∧
  |latitudePowerDtt α s t| ≤ P ∧
  |latitudePowerDs α s t| ≤ P ∧
  |latitudePowerDst α s t| ≤ P ∧
  |latitudePowerDstt α s t| ≤ P ∧
  |latitudePowerDss α s t| ≤ P ∧
  |latitudePowerDsst α s t| ≤ P ∧
  |latitudePowerDsstt α s t| ≤ P

/-- A common absolute bound for the three reduced-cusp two-jets occurring
in the mixed chain. -/
def LatitudeCuspJetBound (α s t H : ℝ) : Prop :=
  0 ≤ H ∧
  |latitudeCusp0 α s t| ≤ H ∧
  |latitudeCusp0Dt α s t| ≤ H ∧
  |latitudeCusp0Dtt α s t| ≤ H ∧
  |latitudeCusp1 α s t| ≤ H ∧
  |latitudeCusp1Dt α s t| ≤ H ∧
  |latitudeCusp1Dtt α s t| ≤ H ∧
  |latitudeCusp2 α s t| ≤ H ∧
  |latitudeCusp2Dt α s t| ≤ H ∧
  |latitudeCusp2Dtt α s t| ≤ H

/-- A common absolute bound for the normalized-gap entries (including the
three composite entries) occurring in the mixed chain. -/
def LatitudeGapJetBound (s t Q : ℝ) : Prop :=
  0 ≤ Q ∧
  |normalizedLatitudeGapDs s t| ≤ Q ∧
  |normalizedLatitudeGapDst s t| ≤ Q ∧
  |normalizedLatitudeGapDstt s t| ≤ Q ∧
  |normalizedLatitudeGapDs s t ^ 2| ≤ Q ∧
  |2 * normalizedLatitudeGapDs s t *
      normalizedLatitudeGapDst s t| ≤ Q ∧
  |2 * normalizedLatitudeGapDst s t ^ 2 +
      2 * normalizedLatitudeGapDs s t *
        normalizedLatitudeGapDstt s t| ≤ Q ∧
  |normalizedLatitudeGapDss s t| ≤ Q ∧
  |normalizedLatitudeGapDsst s t| ≤ Q ∧
  |normalizedLatitudeGapDsstt s t| ≤ Q

/-- First-level normalized-gap bounds automatically control the composite
entries used by the product-rule chain.  The factor `4` is sharp enough for
the only sum of two doubled products. -/
theorem latitudeGapJetBound_of_firstLevel
    {s t G : ℝ} (hG : 1 ≤ G)
    (hDs : |normalizedLatitudeGapDs s t| ≤ G)
    (hDst : |normalizedLatitudeGapDst s t| ≤ G)
    (hDstt : |normalizedLatitudeGapDstt s t| ≤ G)
    (hDss : |normalizedLatitudeGapDss s t| ≤ G)
    (hDsst : |normalizedLatitudeGapDsst s t| ≤ G)
    (hDsstt : |normalizedLatitudeGapDsstt s t| ≤ G) :
    LatitudeGapJetBound s t (4 * G ^ 2) := by
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hGQ : G ≤ 4 * G ^ 2 := by nlinarith [sq_nonneg G]
  have hprod :
      |2 * normalizedLatitudeGapDs s t *
          normalizedLatitudeGapDst s t| ≤ 4 * G ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |normalizedLatitudeGapDs s t| *
          |normalizedLatitudeGapDst s t| ≤ 2 * G * G := by gcongr
      _ ≤ 4 * G ^ 2 := by nlinarith [sq_nonneg G]
  have hsquare :
      |normalizedLatitudeGapDs s t ^ 2| ≤ 4 * G ^ 2 := by
    rw [abs_pow]
    calc
      |normalizedLatitudeGapDs s t| ^ 2 ≤ G ^ 2 := by gcongr
      _ ≤ 4 * G ^ 2 := by nlinarith [sq_nonneg G]
  have hsecond :
      |2 * normalizedLatitudeGapDst s t ^ 2 +
          2 * normalizedLatitudeGapDs s t *
            normalizedLatitudeGapDstt s t| ≤ 4 * G ^ 2 := by
    calc
      |_ + _| ≤
          |2 * normalizedLatitudeGapDst s t ^ 2| +
          |2 * normalizedLatitudeGapDs s t *
            normalizedLatitudeGapDstt s t| := abs_add _ _
      _ ≤ 2 * G ^ 2 + 2 * G * G := by
        simp only [abs_mul, abs_pow,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        gcongr
      _ = 4 * G ^ 2 := by ring
  exact ⟨by positivity, hDs.trans hGQ, hDst.trans hGQ,
    hDstt.trans hGQ, hsquare, hprod, hsecond, hDss.trans hGQ,
    hDsst.trans hGQ, hDsstt.trans hGQ⟩

/-- Explicit common envelope for all first-level normalized-gap entries
under a common radius floor.  The summands are exactly the estimates already
proved in `LatitudeCoefficientDerivatives`; no comparison between different
powers of `R` is imposed here. -/
noncomputable def latitudeGapRadiusEnvelope (R : ℝ) : ℝ :=
  1 +
  2 * R⁻¹ ^ 4 +
  2 * R⁻¹ ^ 6 +
  (R⁻¹ ^ 6 + 6 * R⁻¹ ^ 8) +
  7 * R⁻¹ ^ 6 +
  (R⁻¹ ^ 6 + 6 * R⁻¹ ^ 8) +
  (7 * R⁻¹ ^ 8 + 18 * R⁻¹ ^ 10)

/-- The radius-floor hypotheses furnish the complete normalized-gap
envelope required by the mixed derivative estimate. -/
theorem latitudeGapJetBound_of_radiusFloor
    {s t R : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hR : 0 < R)
    (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t) :
    LatitudeGapJetBound s t
      (4 * latitudeGapRadiusEnvelope R ^ 2) := by
  let G := latitudeGapRadiusEnvelope R
  have hpow (n : ℕ) : 0 ≤ R⁻¹ ^ n := by positivity
  have h4 := hpow 4
  have h6 := hpow 6
  have h8 := hpow 8
  have h10 := hpow 10
  have hG : 1 ≤ G := by
    dsimp [G, latitudeGapRadiusEnvelope]
    linarith
  have hDs0 := abs_normalizedLatitudeGapDs_le
    hs ht hR hsfloor htfloor
  have hDss0 := abs_normalizedLatitudeGapDss_le
    hs ht hR hsfloor htfloor
  have hDsst0 := abs_normalizedLatitudeGapDsst_le
    hs ht hR hsfloor htfloor
  have hDsstt0 := abs_normalizedLatitudeGapDsstt_le
    hs ht hR hsfloor htfloor
  have hDstt0 := abs_normalizedLatitudeGapDsst_le
    ht hs hR htfloor hsfloor
  have hsabs : |s| ≤ 1 := abs_le.mpr hs
  have htabs : |t| ≤ 1 := abs_le.mpr ht
  have hst : |s * t| ≤ 1 := by
    rw [abs_mul]
    calc
      |s| * |t| ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hnum : |s * t - 1| ≤ 2 := by
    calc
      |s * t - 1| ≤ |s * t| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ 2 := by norm_num at hst ⊢; linarith
  have hDst0 := abs_div_pow_mul_pow_le (m := 3) (n := 3)
    (z := s * t - 1) (C := 2)
    (x := heightRadius s) (y := heightRadius t) (R := R)
    (by norm_num) hnum hR hsfloor htfloor
  have hDs : |normalizedLatitudeGapDs s t| ≤ G := by
    exact hDs0.trans (by
      dsimp [G, latitudeGapRadiusEnvelope]
      linarith)
  have hDst : |normalizedLatitudeGapDst s t| ≤ G := by
    unfold normalizedLatitudeGapDst
    exact hDst0.trans (by
      dsimp [G, latitudeGapRadiusEnvelope]
      linarith)
  have hDstt : |normalizedLatitudeGapDstt s t| ≤ G := by
    unfold normalizedLatitudeGapDstt
    exact hDstt0.trans (by
      dsimp [G, latitudeGapRadiusEnvelope]
      linarith)
  have hDss : |normalizedLatitudeGapDss s t| ≤ G := by
    exact hDss0.trans (by
      dsimp [G, latitudeGapRadiusEnvelope]
      linarith)
  have hDsst : |normalizedLatitudeGapDsst s t| ≤ G := by
    exact hDsst0.trans (by
      dsimp [G, latitudeGapRadiusEnvelope]
      linarith)
  have hDsstt : |normalizedLatitudeGapDsstt s t| ≤ G := by
    exact hDsstt0.trans (by
      dsimp [G, latitudeGapRadiusEnvelope]
      linarith)
  exact latitudeGapJetBound_of_firstLevel hG
    hDs hDst hDstt hDss hDsst hDsstt

/-- Bounds on the universal cusp derivatives and on the two right-height
gap derivatives give the three composed cusp two-jets.  Thus the sharp
moment estimates in `ReducedCuspDerivatives` can be inserted without
re-expanding the chain rule. -/
theorem latitudeCuspJetBound_of_valueBounds
    {α s t A G : ℝ} (hA : 0 ≤ A) (hG : 1 ≤ G)
    (h0 : |reducedLatitudeCusp α (normalizedLatitudeGap s t)| ≤ A)
    (h1 : |reducedLatitudeCuspD1Value α
      (normalizedLatitudeGap s t)| ≤ A)
    (h2 : |reducedLatitudeCuspD2Value α
      (normalizedLatitudeGap s t)| ≤ A)
    (h3 : |reducedLatitudeCuspD3Value α
      (normalizedLatitudeGap s t)| ≤ A)
    (h4 : |reducedLatitudeCuspD4Value α
      (normalizedLatitudeGap s t)| ≤ A)
    (hDt : |normalizedLatitudeGapDt s t| ≤ G)
    (hDtt : |normalizedLatitudeGapDtt s t| ≤ G) :
    LatitudeCuspJetBound α s t (2 * A * G ^ 2) := by
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hAG : A ≤ 2 * A * G ^ 2 := by
    have hh : 0 ≤ 2 * G ^ 2 - 1 := by nlinarith [sq_nonneg G]
    nlinarith [mul_nonneg hA hh]
  have hfirst {u v : ℝ} (hu : |u| ≤ A) (hv : |v| ≤ G) :
      |u * v| ≤ 2 * A * G ^ 2 := by
    rw [abs_mul]
    calc
      |u| * |v| ≤ A * G := by gcongr
      _ ≤ 2 * A * G ^ 2 := by
        have : G ≤ 2 * G ^ 2 := by nlinarith [sq_nonneg G]
        calc
          A * G ≤ A * (2 * G ^ 2) :=
            mul_le_mul_of_nonneg_left this hA
          _ = 2 * A * G ^ 2 := by ring
  have hsecond {u v w z : ℝ}
      (hu : |u| ≤ A) (hv : |v| ≤ G)
      (hw : |w| ≤ A) (hz : |z| ≤ G) :
      |u * v ^ 2 + w * z| ≤ 2 * A * G ^ 2 := by
    calc
      |_ + _| ≤ |u * v ^ 2| + |w * z| := abs_add _ _
      _ ≤ A * G ^ 2 + A * G := by
        simp only [abs_mul, abs_pow]
        gcongr
      _ ≤ 2 * A * G ^ 2 := by
        have hGG : G ≤ G ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hGG hA]
  unfold LatitudeCuspJetBound latitudeCusp0 latitudeCusp0Dt
    latitudeCusp0Dtt latitudeCusp1 latitudeCusp1Dt latitudeCusp1Dtt
    latitudeCusp2 latitudeCusp2Dt latitudeCusp2Dtt
  exact ⟨by positivity, h0.trans hAG, hfirst h1 hDt,
    hsecond h2 hDt h1 hDtt, h1.trans hAG, hfirst h2 hDt,
    hsecond h3 hDt h2 hDtt, h2.trans hAG, hfirst h3 hDt,
    hsecond h4 hDt h3 hDtt⟩

/-- An explicit common envelope for the cusp value and its first four
derivatives at a positive normalized gap.  The derivative summands are the
sharp half-power moment estimates. -/
noncomputable def latitudeCuspValueEnvelope (α x : ℝ) : ℝ :=
  1 + |reducedLatitudeCusp α x| +
  |α / 2| * x ^ (α / 2 - 1) +
  |(α / 2) * (α / 2 - 1)| *
    (Real.pi / (2 * Real.sqrt 2)) * x ^ (α / 2 - 3 / 2) +
  |(α / 2) * (α / 2 - 1) * (α / 2 - 2)| *
    (Real.pi / (2 * Real.sqrt 2)) * x ^ (α / 2 - 5 / 2) +
  |(α / 2) * (α / 2 - 1) * (α / 2 - 2) * (α / 2 - 3)| *
    (Real.pi / (2 * Real.sqrt 2)) * x ^ (α / 2 - 7 / 2)

/-- Interior off-diagonal points with a common radius floor furnish the
complete composed cusp envelope.  This theorem is the direct consumer of
the sharp moment bounds through order four. -/
theorem latitudeCuspJetBound_of_radiusFloor
    {α s t R : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (hst : s ≠ t)
    (hα : α ≤ 2) (hR : 0 < R)
    (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t) :
    LatitudeCuspJetBound α s t
      (2 * latitudeCuspValueEnvelope α (normalizedLatitudeGap s t) *
        latitudeGapRadiusEnvelope R ^ 2) := by
  let x := normalizedLatitudeGap s t
  let A := latitudeCuspValueEnvelope α x
  let G := latitudeGapRadiusEnvelope R
  have hx : 0 < x := by
    dsimp [x]
    exact normalizedLatitudeGap_pos hs ht hst
  have h1raw := abs_reducedLatitudeCuspD1Value_le hx hα
  have h2raw := abs_reducedLatitudeCuspD2Value_le_rpow hx hα
  have h3raw := abs_reducedLatitudeCuspD3Value_le_rpow hx hα
  have h4raw := abs_reducedLatitudeCuspD4Value_le_rpow hx hα
  have hterm1 : 0 ≤ |α / 2| * x ^ (α / 2 - 1) := by positivity
  have hterm2 : 0 ≤
      |(α / 2) * (α / 2 - 1)| *
        (Real.pi / (2 * Real.sqrt 2)) *
          x ^ (α / 2 - 3 / 2) := by positivity
  have hterm3 : 0 ≤
      |(α / 2) * (α / 2 - 1) * (α / 2 - 2)| *
        (Real.pi / (2 * Real.sqrt 2)) *
          x ^ (α / 2 - 5 / 2) := by positivity
  have hterm4 : 0 ≤
      |(α / 2) * (α / 2 - 1) * (α / 2 - 2) * (α / 2 - 3)| *
        (Real.pi / (2 * Real.sqrt 2)) *
          x ^ (α / 2 - 7 / 2) := by positivity
  have hA : 0 ≤ A := by
    dsimp [A, latitudeCuspValueEnvelope]
    positivity
  have h0 :
      |reducedLatitudeCusp α x| ≤ A := by
    dsimp [A, latitudeCuspValueEnvelope]
    linarith [abs_nonneg (reducedLatitudeCusp α x)]
  have h1 : |reducedLatitudeCuspD1Value α x| ≤ A := by
    apply h1raw.trans
    dsimp [A, latitudeCuspValueEnvelope]
    linarith [abs_nonneg (reducedLatitudeCusp α x)]
  have h2 : |reducedLatitudeCuspD2Value α x| ≤ A := by
    apply h2raw.trans
    dsimp [A, latitudeCuspValueEnvelope]
    linarith [abs_nonneg (reducedLatitudeCusp α x)]
  have h3 : |reducedLatitudeCuspD3Value α x| ≤ A := by
    apply h3raw.trans
    dsimp [A, latitudeCuspValueEnvelope]
    linarith [abs_nonneg (reducedLatitudeCusp α x)]
  have h4 : |reducedLatitudeCuspD4Value α x| ≤ A := by
    apply h4raw.trans
    dsimp [A, latitudeCuspValueEnvelope]
    linarith [abs_nonneg (reducedLatitudeCusp α x)]
  have hs' : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hpow (n : ℕ) : 0 ≤ R⁻¹ ^ n := by positivity
  have hG : 1 ≤ G := by
    dsimp [G, latitudeGapRadiusEnvelope]
    have h4p := hpow 4
    have h6p := hpow 6
    have h8p := hpow 8
    have h10p := hpow 10
    linarith
  have hDt0 := abs_normalizedLatitudeGapDs_le
    ht' hs' hR htfloor hsfloor
  have hDtt0 := abs_normalizedLatitudeGapDss_le
    ht' hs' hR htfloor hsfloor
  have hDt : |normalizedLatitudeGapDt s t| ≤ G := by
    unfold normalizedLatitudeGapDt
    exact hDt0.trans (by
      dsimp [G, latitudeGapRadiusEnvelope]
      have h4p := hpow 4
      have h6p := hpow 6
      have h8p := hpow 8
      have h10p := hpow 10
      linarith)
  have hDtt : |normalizedLatitudeGapDtt s t| ≤ G := by
    unfold normalizedLatitudeGapDtt
    exact hDtt0.trans (by
      dsimp [G, latitudeGapRadiusEnvelope]
      have h4p := hpow 4
      have h6p := hpow 6
      have h8p := hpow 8
      have h10p := hpow 10
      linarith)
  simpa [x, A, G] using
    latitudeCuspJetBound_of_valueBounds hA hG
      h0 h1 h2 h3 h4 hDt hDtt

private theorem abs_latitudeJetMulD2_le
    {a a₁ a₂ b b₁ b₂ P H : ℝ}
    (hP : 0 ≤ P) (_hH : 0 ≤ H)
    (ha : |a| ≤ P) (ha₁ : |a₁| ≤ P) (ha₂ : |a₂| ≤ P)
    (hb : |b| ≤ H) (hb₁ : |b₁| ≤ H) (hb₂ : |b₂| ≤ H) :
    |latitudeJetMulD2 a a₁ a₂ b b₁ b₂| ≤ 4 * P * H := by
  unfold latitudeJetMulD2
  calc
    |a₂ * b + 2 * a₁ * b₁ + a * b₂| ≤
        |a₂ * b| + |2 * a₁ * b₁| + |a * b₂| := by
      exact (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤ P * H + 2 * P * H + P * H := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
    _ = 4 * P * H := by ring

private theorem abs_latitudeJetMul3D2_le
    {a a₁ a₂ b b₁ b₂ c c₁ c₂ P H Q : ℝ}
    (hP : 0 ≤ P) (hH : 0 ≤ H) (_hQ : 0 ≤ Q)
    (ha : |a| ≤ P) (ha₁ : |a₁| ≤ P) (ha₂ : |a₂| ≤ P)
    (hb : |b| ≤ H) (hb₁ : |b₁| ≤ H) (hb₂ : |b₂| ≤ H)
    (hc : |c| ≤ Q) (hc₁ : |c₁| ≤ Q) (hc₂ : |c₂| ≤ Q) :
    |latitudeJetMul3D2 a a₁ a₂ b b₁ b₂ c c₁ c₂| ≤
      9 * P * H * Q := by
  unfold latitudeJetMul3D2
  calc
    |a₂ * b * c + a * b₂ * c + a * b * c₂ +
        2 * a₁ * b₁ * c + 2 * a₁ * b * c₁ +
        2 * a * b₁ * c₁| ≤
      |a₂ * b * c| + |a * b₂ * c| + |a * b * c₂| +
        |2 * a₁ * b₁ * c| + |2 * a₁ * b * c₁| +
        |2 * a * b₁ * c₁| := by
      calc
        |_ + _| ≤
            |a₂ * b * c + a * b₂ * c + a * b * c₂ +
              2 * a₁ * b₁ * c + 2 * a₁ * b * c₁| +
              |2 * a * b₁ * c₁| := abs_add _ _
        _ ≤
            (|a₂ * b * c + a * b₂ * c + a * b * c₂ +
              2 * a₁ * b₁ * c| + |2 * a₁ * b * c₁|) +
              |2 * a * b₁ * c₁| := by gcongr; exact abs_add _ _
        _ ≤
            ((|a₂ * b * c + a * b₂ * c + a * b * c₂| +
              |2 * a₁ * b₁ * c|) + |2 * a₁ * b * c₁|) +
              |2 * a * b₁ * c₁| := by gcongr; exact abs_add _ _
        _ ≤
            (((|a₂ * b * c + a * b₂ * c| + |a * b * c₂|) +
              |2 * a₁ * b₁ * c|) + |2 * a₁ * b * c₁|) +
              |2 * a * b₁ * c₁| := by gcongr; exact abs_add _ _
        _ ≤
            ((((|a₂ * b * c| + |a * b₂ * c|) + |a * b * c₂|) +
              |2 * a₁ * b₁ * c|) + |2 * a₁ * b * c₁|) +
              |2 * a * b₁ * c₁| := by gcongr; exact abs_add _ _
    _ ≤
      P * H * Q + P * H * Q + P * H * Q +
        2 * P * H * Q + 2 * P * H * Q + 2 * P * H * Q := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
    _ = 9 * P * H * Q := by ring

/-- The explicit product-rule estimate for the genuine mixed derivative.
The constants `4` and `36` are respectively the total Leibniz weights of
the two-factor term and the three three-factor terms. -/
theorem abs_variableReducedLatitudeKernelDsstt_le_envelopes
    {α s t P H Q : ℝ}
    (hP : LatitudePowerJetBound α s t P)
    (hH : LatitudeCuspJetBound α s t H)
    (hQ : LatitudeGapJetBound s t Q) :
    |variableReducedLatitudeKernelDsstt α s t| ≤
      4 * P * H + 36 * P * H * Q := by
  rcases hP with
    ⟨hP0, hP, hPt, hPtt, hPs, hPst, hPstt, hPss, hPsst, hPsstt⟩
  rcases hH with
    ⟨hH0, hH, hHt, hHtt, hH1, hH1t, hH1tt, hH2, hH2t, hH2tt⟩
  rcases hQ with
    ⟨hQ0, hQs, hQst, hQstt, hQs2, hQs2t, hQs2tt, hQss, hQsst, hQsstt⟩
  have h1 := abs_latitudeJetMulD2_le hP0 hH0
    hPss hPsst hPsstt hH hHt hHtt
  have h2 := abs_latitudeJetMul3D2_le hP0 hH0 hQ0
    hPs hPst hPstt hH1 hH1t hH1tt hQs hQst hQstt
  have h3 := abs_latitudeJetMul3D2_le hP0 hH0 hQ0
    hP hPt hPtt hH2 hH2t hH2tt hQs2 hQs2t hQs2tt
  have h4 := abs_latitudeJetMul3D2_le hP0 hH0 hQ0
    hP hPt hPtt hH1 hH1t hH1tt hQss hQsst hQsstt
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
          (2 * normalizedLatitudeGapDs s t * normalizedLatitudeGapDst s t)
          (2 * normalizedLatitudeGapDst s t ^ 2 +
            2 * normalizedLatitudeGapDs s t *
              normalizedLatitudeGapDstt s t)| +
        |latitudeJetMul3D2
          (latitudePower α s t) (latitudePowerDt α s t)
          (latitudePowerDtt α s t)
          (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
          (latitudeCusp1Dtt α s t)
          (normalizedLatitudeGapDss s t) (normalizedLatitudeGapDsst s t)
          (normalizedLatitudeGapDsstt s t)| := by
      calc
        |_ + _| ≤
            |latitudeJetMulD2
                (latitudePowerDss α s t) (latitudePowerDsst α s t)
                (latitudePowerDsstt α s t)
                (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
                (latitudeCusp0Dtt α s t) +
              2 * latitudeJetMul3D2
                (latitudePowerDs α s t) (latitudePowerDst α s t)
                (latitudePowerDstt α s t)
                (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
                (latitudeCusp1Dtt α s t)
                (normalizedLatitudeGapDs s t)
                (normalizedLatitudeGapDst s t)
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
                    normalizedLatitudeGapDstt s t)| +
              |latitudeJetMul3D2
                (latitudePower α s t) (latitudePowerDt α s t)
                (latitudePowerDtt α s t)
                (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
                (latitudeCusp1Dtt α s t)
                (normalizedLatitudeGapDss s t)
                (normalizedLatitudeGapDsst s t)
                (normalizedLatitudeGapDsstt s t)| := abs_add _ _
        _ ≤
            (|latitudeJetMulD2
                (latitudePowerDss α s t) (latitudePowerDsst α s t)
                (latitudePowerDsstt α s t)
                (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
                (latitudeCusp0Dtt α s t) +
              2 * latitudeJetMul3D2
                (latitudePowerDs α s t) (latitudePowerDst α s t)
                (latitudePowerDstt α s t)
                (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
                (latitudeCusp1Dtt α s t)
                (normalizedLatitudeGapDs s t)
                (normalizedLatitudeGapDst s t)
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
                    normalizedLatitudeGapDstt s t)|) +
              |latitudeJetMul3D2
                (latitudePower α s t) (latitudePowerDt α s t)
                (latitudePowerDtt α s t)
                (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
                (latitudeCusp1Dtt α s t)
                (normalizedLatitudeGapDss s t)
                (normalizedLatitudeGapDsst s t)
                (normalizedLatitudeGapDsstt s t)| := by
            gcongr
            exact abs_add _ _
        _ ≤
            ((|latitudeJetMulD2
                (latitudePowerDss α s t) (latitudePowerDsst α s t)
                (latitudePowerDsstt α s t)
                (latitudeCusp0 α s t) (latitudeCusp0Dt α s t)
                (latitudeCusp0Dtt α s t)| +
              |2 * latitudeJetMul3D2
                (latitudePowerDs α s t) (latitudePowerDst α s t)
                (latitudePowerDstt α s t)
                (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
                (latitudeCusp1Dtt α s t)
                (normalizedLatitudeGapDs s t)
                (normalizedLatitudeGapDst s t)
                (normalizedLatitudeGapDstt s t)|) +
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
                    normalizedLatitudeGapDstt s t)|) +
              |latitudeJetMul3D2
                (latitudePower α s t) (latitudePowerDt α s t)
                (latitudePowerDtt α s t)
                (latitudeCusp1 α s t) (latitudeCusp1Dt α s t)
                (latitudeCusp1Dtt α s t)
                (normalizedLatitudeGapDss s t)
                (normalizedLatitudeGapDsst s t)
                (normalizedLatitudeGapDsstt s t)| := by
            gcongr
            exact abs_add _ _
        _ = _ := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 4 * P * H + 2 * (9 * P * H * Q) +
        9 * P * H * Q + 9 * P * H * Q := by gcongr
    _ = 4 * P * H + 36 * P * H * Q := by ring

/-- Pointwise (5.5): once the coefficient/cusp/gap envelopes have their
local scale estimate, the actual mixed derivative has exactly the desired
radius and separation powers. -/
theorem abs_variableReducedLatitudeKernelDsstt_le_powerder
    {α s t R C P H Q : ℝ}
    (_hR : 0 < R) (_hst : 0 < |s - t|)
    (hP : LatitudePowerJetBound α s t P)
    (hH : LatitudeCuspJetBound α s t H)
    (hQ : LatitudeGapJetBound s t Q)
    (hscale :
      4 * P * H + 36 * P * H * Q ≤
        C * R ^ (-2 - α) * |s - t| ^ (α - 3)) :
    |variableReducedLatitudeKernelDsstt α s t| ≤
      C * R ^ (-2 - α) * |s - t| ^ (α - 3) :=
  (abs_variableReducedLatitudeKernelDsstt_le_envelopes hP hH hQ).trans hscale

end BEMOC
