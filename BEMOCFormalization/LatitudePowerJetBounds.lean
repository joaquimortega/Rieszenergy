import BEMOCFormalization.LatitudeAngularJetBounds
import BEMOCFormalization.LatitudeVariableMixedBound

/-!
# Envelope for the power-coefficient jet

This file bounds the ten entries of the mixed two-jet of
`p(s,t)^(α/2)` from three transparent inputs:

* one bound for the four scalar falling-factorial coefficients;
* one bound for the five powers `p^(α/2-m)`, `0 ≤ m ≤ 4`;
* one bound for the angular-scale derivatives through order `(2,2)`.

The explicit factor `15` is the sum of the Leibniz weights in the largest
entry.  This is intentionally an envelope theorem: geometric applications
can retain their sharp graded powers of the radius while the long algebraic
expansion is proved only once.
-/

namespace BEMOC

set_option maxHeartbeats 800000

def LatitudePowerCoefficientBound (α A : ℝ) : Prop :=
  1 ≤ A ∧
  |α / 2| ≤ A ∧
  |(α / 2) * (α / 2 - 1)| ≤ A ∧
  |(α / 2) * (α / 2 - 1) * (α / 2 - 2)| ≤ A ∧
  |(α / 2) * (α / 2 - 1) * (α / 2 - 2) *
      (α / 2 - 3)| ≤ A

def LatitudePowerRpowBound (α s t U : ℝ) : Prop :=
  0 ≤ U ∧
  |latitudeAngularScale s t ^ (α / 2)| ≤ U ∧
  |latitudeAngularScale s t ^ (α / 2 - 1)| ≤ U ∧
  |latitudeAngularScale s t ^ (α / 2 - 2)| ≤ U ∧
  |latitudeAngularScale s t ^ (α / 2 - 3)| ≤ U ∧
  |latitudeAngularScale s t ^ (α / 2 - 4)| ≤ U

def LatitudeAngularDerivativeJetBound (s t D : ℝ) : Prop :=
  1 ≤ D ∧
  |latitudeAngularScaleDs s t| ≤ D ∧
  |latitudeAngularScaleDt s t| ≤ D ∧
  |latitudeAngularScaleDss s t| ≤ D ∧
  |latitudeAngularScaleDtt s t| ≤ D ∧
  |latitudeAngularScaleDst s t| ≤ D ∧
  |latitudeAngularScaleDsst s t| ≤ D ∧
  |latitudeAngularScaleDstt s t| ≤ D ∧
  |latitudeAngularScaleDsstt s t| ≤ D

private theorem abs_mul_two_le
    {c u x y A U D : ℝ} (hA : 0 ≤ A) (hU : 0 ≤ U)
    (hD : 0 ≤ D) (hc : |c| ≤ A) (hu : |u| ≤ U)
    (hx : |x| ≤ D) (hy : |y| ≤ D) :
    |c * u * x * y| ≤ A * U * D ^ 2 := by
  simp only [abs_mul]
  calc
    |c| * |u| * |x| * |y| ≤ A * U * D * D := by gcongr
    _ = A * U * D ^ 2 := by ring

private theorem abs_mul_three_le
    {c u x y z A U D : ℝ} (hA : 0 ≤ A) (hU : 0 ≤ U)
    (hD : 0 ≤ D) (hc : |c| ≤ A) (hu : |u| ≤ U)
    (hx : |x| ≤ D) (hy : |y| ≤ D) (hz : |z| ≤ D) :
    |c * u * x * y * z| ≤ A * U * D ^ 3 := by
  simp only [abs_mul]
  calc
    |c| * |u| * |x| * |y| * |z| ≤ A * U * D * D * D := by
      gcongr
    _ = A * U * D ^ 3 := by ring

private theorem abs_mul_four_le
    {c u w x y z A U D : ℝ} (hA : 0 ≤ A) (hU : 0 ≤ U)
    (hD : 0 ≤ D) (hc : |c| ≤ A) (hu : |u| ≤ U)
    (hw : |w| ≤ D) (hx : |x| ≤ D) (hy : |y| ≤ D)
    (hz : |z| ≤ D) :
    |c * u * w * x * y * z| ≤ A * U * D ^ 4 := by
  simp only [abs_mul]
  calc
    |c| * |u| * |w| * |x| * |y| * |z| ≤
        A * U * D * D * D * D := by gcongr
    _ = A * U * D ^ 4 := by ring

/-- A checked common envelope for all ten entries of the power two-jet. -/
theorem latitudePowerJetBound_of_coefficient_rpow_angular
    {α s t A U D : ℝ}
    (hA : LatitudePowerCoefficientBound α A)
    (hU : LatitudePowerRpowBound α s t U)
    (hD : LatitudeAngularDerivativeJetBound s t D) :
    LatitudePowerJetBound α s t (15 * A * U * D ^ 4) := by
  rcases hA with ⟨hA1, ha1, ha2, ha3, ha4⟩
  rcases hU with ⟨hU0, hu0, hu1, hu2, hu3, hu4⟩
  rcases hD with
    ⟨hD1, hps, hpt, hpss, hptt, hpst, hpsst, hpstt, hpsstt⟩
  have hA0 : 0 ≤ A := zero_le_one.trans hA1
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hDpow (n : ℕ) : 1 ≤ D ^ n := by
    exact one_le_pow₀ hD1
  have hB0 : 0 ≤ A * U * D ^ 4 := by positivity
  have hbase : U ≤ 15 * A * U * D ^ 4 := by
    calc
      U = 1 * U := by ring
      _ ≤ A * U := by gcongr
      _ = A * U * 1 := by ring
      _ ≤ A * U * D ^ 4 :=
        mul_le_mul_of_nonneg_left (hDpow 4) (mul_nonneg hA0 hU0)
      _ ≤ 15 * A * U * D ^ 4 := by nlinarith
  have hone {c u x : ℝ}
      (hc : |c| ≤ A) (hu : |u| ≤ U) (hx : |x| ≤ D) :
      |c * u * x| ≤ A * U * D ^ 4 := by
    rw [abs_mul, abs_mul]
    have h : |c| * |u| * |x| ≤ A * U * D := by gcongr
    have hscale : A * U * D ≤ A * U * D ^ 4 := by
      have hD3 := hDpow 3
      have hAU : 0 ≤ A * U := mul_nonneg hA0 hU0
      calc
        A * U * D = A * U * (D * 1) := by ring
        _ ≤ A * U * (D * D ^ 3) := by
          gcongr
        _ = A * U * D ^ 4 := by ring
    exact h.trans hscale
  have htwo {c u x y : ℝ}
      (hc : |c| ≤ A) (hu : |u| ≤ U)
      (hx : |x| ≤ D) (hy : |y| ≤ D) :
      |c * u * x * y| ≤ A * U * D ^ 4 := by
    have h := abs_mul_two_le hA0 hU0 hD0 hc hu hx hy
    have hD2 := hDpow 2
    have hscale : A * U * D ^ 2 ≤ A * U * D ^ 4 := by
      have hAU : 0 ≤ A * U := mul_nonneg hA0 hU0
      have h24 : D ^ 2 ≤ D ^ 4 := by
        calc
          D ^ 2 ≤ D ^ 2 * D ^ 2 :=
            le_mul_of_one_le_right (by positivity) hD2
          _ = D ^ 4 := by ring
      gcongr
    exact h.trans hscale
  have hthree {c u x y z : ℝ}
      (hc : |c| ≤ A) (hu : |u| ≤ U)
      (hx : |x| ≤ D) (hy : |y| ≤ D) (hz : |z| ≤ D) :
      |c * u * x * y * z| ≤ A * U * D ^ 4 := by
    have h := abs_mul_three_le hA0 hU0 hD0 hc hu hx hy hz
    have hscale : A * U * D ^ 3 ≤ A * U * D ^ 4 := by
      have hnonneg : 0 ≤ A * U * D ^ 3 := by positivity
      calc
        A * U * D ^ 3 ≤ (A * U * D ^ 3) * D := by
          exact le_mul_of_one_le_right hnonneg hD1
        _ = A * U * D ^ 4 := by ring
    exact h.trans hscale
  have hfour {c u w x y z : ℝ}
      (hc : |c| ≤ A) (hu : |u| ≤ U)
      (hw : |w| ≤ D) (hx : |x| ≤ D)
      (hy : |y| ≤ D) (hz : |z| ≤ D) :
      |c * u * w * x * y * z| ≤ A * U * D ^ 4 :=
    abs_mul_four_le hA0 hU0 hD0 hc hu hw hx hy hz
  have habs9 (z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ : ℝ) :
      |z₁ + z₂ + z₃ + z₄ + z₅ + z₆ + z₇ + z₈ + z₉| ≤
        |z₁| + |z₂| + |z₃| + |z₄| + |z₅| + |z₆| + |z₇| + |z₈| + |z₉| := by
    have h₂ := abs_add z₁ z₂
    have h₃ := abs_add (z₁ + z₂) z₃
    have h₄ := abs_add (z₁ + z₂ + z₃) z₄
    have h₅ := abs_add (z₁ + z₂ + z₃ + z₄) z₅
    have h₆ := abs_add (z₁ + z₂ + z₃ + z₄ + z₅) z₆
    have h₇ := abs_add (z₁ + z₂ + z₃ + z₄ + z₅ + z₆) z₇
    have h₈ := abs_add (z₁ + z₂ + z₃ + z₄ + z₅ + z₆ + z₇) z₈
    have h₉ := abs_add (z₁ + z₂ + z₃ + z₄ + z₅ + z₆ + z₇ + z₈) z₉
    linarith
  have hzero :
      |latitudePower α s t| ≤ 15 * A * U * D ^ 4 := by
    unfold latitudePower
    exact hu0.trans hbase
  have hdt :
      |latitudePowerDt α s t| ≤ 15 * A * U * D ^ 4 := by
    unfold latitudePowerDt
    exact (hone ha1 hu1 hpt).trans (by nlinarith)
  have hds :
      |latitudePowerDs α s t| ≤ 15 * A * U * D ^ 4 := by
    unfold latitudePowerDs
    exact (hone ha1 hu1 hps).trans (by nlinarith)
  have hdtt :
      |latitudePowerDtt α s t| ≤ 15 * A * U * D ^ 4 := by
    unfold latitudePowerDtt
    calc
      |_ + _| ≤
          |(α / 2) * (α / 2 - 1) *
            latitudeAngularScale s t ^ (α / 2 - 2) *
              latitudeAngularScaleDt s t ^ 2| +
          |(α / 2) * latitudeAngularScale s t ^ (α / 2 - 1) *
              latitudeAngularScaleDtt s t| := abs_add _ _
      _ ≤ A * U * D ^ 4 + A * U * D ^ 4 := by
        exact add_le_add
          (by convert htwo ha2 hu2 hpt hpt using 1 <;> ring)
          (hone ha1 hu1 hptt)
      _ ≤ 15 * A * U * D ^ 4 := by
        have h2 := htwo ha2 hu2 hpt hpt
        have h1 := hone ha1 hu1 hptt
        nlinarith
  -- The remaining entries are bounded below using their checked explicit
  -- formulas.  Keeping the final arithmetic in one place makes later
  -- refinements of the common constant harmless.
  refine ⟨by positivity, hzero, hdt, hdtt, hds, ?_, ?_, ?_, ?_, ?_⟩
  · unfold latitudePowerDst
    let z₁ := (α / 2) * (α / 2 - 1) *
      latitudeAngularScale s t ^ (α / 2 - 2) *
        latitudeAngularScaleDt s t * latitudeAngularScaleDs s t
    let z₂ := (α / 2) *
      latitudeAngularScale s t ^ (α / 2 - 1) *
        latitudeAngularScaleDst s t
    have hz₁ : |z₁| ≤ A * U * D ^ 4 := by
      dsimp [z₁]
      exact htwo ha2 hu2 hpt hps
    have hz₂ : |z₂| ≤ A * U * D ^ 4 := by
      dsimp [z₂]
      exact hone ha1 hu1 hpst
    calc
      |_| = |z₁ + z₂| := by
        congr 1
        dsimp [z₁, z₂]
        ring
      _ ≤ |z₁| + |z₂| := abs_add _ _
      _ ≤ 15 * A * U * D ^ 4 := by linarith
  · unfold latitudePowerDstt
    let z₁ := (α / 2) * (α / 2 - 1) * (α / 2 - 2) *
      latitudeAngularScale s t ^ (α / 2 - 3) *
        latitudeAngularScaleDt s t ^ 2 * latitudeAngularScaleDs s t
    let z₂ := (α / 2) * (α / 2 - 1) *
      latitudeAngularScale s t ^ (α / 2 - 2) *
        latitudeAngularScaleDtt s t * latitudeAngularScaleDs s t
    let z₃ := 2 * ((α / 2) * (α / 2 - 1) *
      latitudeAngularScale s t ^ (α / 2 - 2) *
        latitudeAngularScaleDt s t * latitudeAngularScaleDst s t)
    let z₄ := (α / 2) *
      latitudeAngularScale s t ^ (α / 2 - 1) *
        latitudeAngularScaleDstt s t
    have hz₁ : |z₁| ≤ A * U * D ^ 4 := by
      dsimp [z₁]
      convert hthree ha3 hu3 hpt hpt hps using 1 <;> ring
    have hz₂ : |z₂| ≤ A * U * D ^ 4 := by
      dsimp [z₂]
      exact htwo ha2 hu2 hptt hps
    have hz₃ : |z₃| ≤ 2 * (A * U * D ^ 4) := by
      dsimp [z₃]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
      exact htwo ha2 hu2 hpt hpst
    have hz₄ : |z₄| ≤ A * U * D ^ 4 := by
      dsimp [z₄]
      exact hone ha1 hu1 hpstt
    calc
      |_| = |z₁ + z₂ + z₃ + z₄ + 0 + 0 + 0 + 0 + 0| := by
        congr 1
        dsimp [z₁, z₂, z₃, z₄]
        ring
      _ ≤ |z₁| + |z₂| + |z₃| + |z₄| +
          |(0 : ℝ)| + |(0 : ℝ)| + |(0 : ℝ)| + |(0 : ℝ)| + |(0 : ℝ)| :=
        habs9 _ _ _ _ _ _ _ _ _
      _ ≤ 15 * A * U * D ^ 4 := by norm_num; linarith
  · unfold latitudePowerDss
    calc
      |_ + _| ≤
          |(α / 2) * (α / 2 - 1) *
            latitudeAngularScale s t ^ (α / 2 - 2) *
              latitudeAngularScaleDs s t ^ 2| +
          |(α / 2) * latitudeAngularScale s t ^ (α / 2 - 1) *
              latitudeAngularScaleDss s t| := abs_add _ _
      _ ≤ A * U * D ^ 4 + A * U * D ^ 4 := by
        exact add_le_add
          (by convert htwo ha2 hu2 hps hps using 1 <;> ring)
          (hone ha1 hu1 hpss)
      _ ≤ 15 * A * U * D ^ 4 := by nlinarith
  · unfold latitudePowerDsst
    let z₁ := (α / 2) * (α / 2 - 1) * (α / 2 - 2) *
      latitudeAngularScale s t ^ (α / 2 - 3) *
        latitudeAngularScaleDt s t * latitudeAngularScaleDs s t ^ 2
    let z₂ := 2 * ((α / 2) * (α / 2 - 1) *
      latitudeAngularScale s t ^ (α / 2 - 2) *
        latitudeAngularScaleDs s t * latitudeAngularScaleDst s t)
    let z₃ := (α / 2) * (α / 2 - 1) *
      latitudeAngularScale s t ^ (α / 2 - 2) *
        latitudeAngularScaleDt s t * latitudeAngularScaleDss s t
    let z₄ := (α / 2) *
      latitudeAngularScale s t ^ (α / 2 - 1) *
        latitudeAngularScaleDsst s t
    have hz₁ : |z₁| ≤ A * U * D ^ 4 := by
      dsimp [z₁]
      convert hthree ha3 hu3 hpt hps hps using 1 <;> ring
    have hz₂ : |z₂| ≤ 2 * (A * U * D ^ 4) := by
      dsimp [z₂]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
      exact htwo ha2 hu2 hps hpst
    have hz₃ : |z₃| ≤ A * U * D ^ 4 := by
      dsimp [z₃]
      exact htwo ha2 hu2 hpt hpss
    have hz₄ : |z₄| ≤ A * U * D ^ 4 := by
      dsimp [z₄]
      exact hone ha1 hu1 hpsst
    calc
      |_| = |z₁ + z₂ + z₃ + z₄ + 0 + 0 + 0 + 0 + 0| := by
        congr 1
        dsimp [z₁, z₂, z₃, z₄]
        ring
      _ ≤ |z₁| + |z₂| + |z₃| + |z₄| +
          |(0 : ℝ)| + |(0 : ℝ)| + |(0 : ℝ)| + |(0 : ℝ)| + |(0 : ℝ)| :=
        habs9 _ _ _ _ _ _ _ _ _
      _ ≤ 15 * A * U * D ^ 4 := by norm_num; linarith
  · unfold latitudePowerDsstt
    let z₁ := (α / 2) * (α / 2 - 1) * (α / 2 - 2) *
      (α / 2 - 3) * latitudeAngularScale s t ^ (α / 2 - 4) *
        latitudeAngularScaleDt s t ^ 2 *
        latitudeAngularScaleDs s t ^ 2
    let z₂ := (α / 2) * (α / 2 - 1) * (α / 2 - 2) *
      latitudeAngularScale s t ^ (α / 2 - 3) *
        latitudeAngularScaleDtt s t * latitudeAngularScaleDs s t ^ 2
    let z₃ := 4 * ((α / 2) * (α / 2 - 1) * (α / 2 - 2) *
      latitudeAngularScale s t ^ (α / 2 - 3) *
        latitudeAngularScaleDt s t * latitudeAngularScaleDs s t *
          latitudeAngularScaleDst s t)
    let z₄ := 2 * ((α / 2) * (α / 2 - 1) *
      latitudeAngularScale s t ^ (α / 2 - 2) *
        latitudeAngularScaleDst s t ^ 2)
    let z₅ := 2 * ((α / 2) * (α / 2 - 1) *
      latitudeAngularScale s t ^ (α / 2 - 2) *
        latitudeAngularScaleDs s t * latitudeAngularScaleDstt s t)
    let z₆ := (α / 2) * (α / 2 - 1) * (α / 2 - 2) *
      latitudeAngularScale s t ^ (α / 2 - 3) *
        latitudeAngularScaleDt s t ^ 2 *
          latitudeAngularScaleDss s t
    let z₇ := (α / 2) * (α / 2 - 1) *
      latitudeAngularScale s t ^ (α / 2 - 2) *
        latitudeAngularScaleDtt s t * latitudeAngularScaleDss s t
    let z₈ := 2 * ((α / 2) * (α / 2 - 1) *
      latitudeAngularScale s t ^ (α / 2 - 2) *
        latitudeAngularScaleDt s t * latitudeAngularScaleDsst s t)
    let z₉ := (α / 2) * latitudeAngularScale s t ^ (α / 2 - 1) *
      latitudeAngularScaleDsstt s t
    have hz₁ : |z₁| ≤ A * U * D ^ 4 := by
      dsimp [z₁]
      convert hfour ha4 hu4 hpt hpt hps hps using 1 <;> ring
    have hz₂ : |z₂| ≤ A * U * D ^ 4 := by
      dsimp [z₂]
      convert hthree ha3 hu3 hptt hps hps using 1 <;> ring
    have hz₃ : |z₃| ≤ 4 * (A * U * D ^ 4) := by
      dsimp [z₃]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      gcongr
      exact hthree ha3 hu3 hpt hps hpst
    have hz₄ : |z₄| ≤ 2 * (A * U * D ^ 4) := by
      dsimp [z₄]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
      convert htwo ha2 hu2 hpst hpst using 1 <;> ring
    have hz₅ : |z₅| ≤ 2 * (A * U * D ^ 4) := by
      dsimp [z₅]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
      exact htwo ha2 hu2 hps hpstt
    have hz₆ : |z₆| ≤ A * U * D ^ 4 := by
      dsimp [z₆]
      convert hthree ha3 hu3 hpt hpt hpss using 1 <;> ring
    have hz₇ : |z₇| ≤ A * U * D ^ 4 := by
      dsimp [z₇]
      exact htwo ha2 hu2 hptt hpss
    have hz₈ : |z₈| ≤ 2 * (A * U * D ^ 4) := by
      dsimp [z₈]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
      exact htwo ha2 hu2 hpt hpsst
    have hz₉ : |z₉| ≤ A * U * D ^ 4 := by
      dsimp [z₉]
      exact hone ha1 hu1 hpsstt
    calc
      |_| = |z₁ + z₂ + z₃ + z₄ + z₅ + z₆ + z₇ + z₈ + z₉| := by
        congr 1
        dsimp [z₁, z₂, z₃, z₄, z₅, z₆, z₇, z₈, z₉]
        ring
      _ ≤ |z₁| + |z₂| + |z₃| + |z₄| + |z₅| + |z₆| + |z₇| +
          |z₈| + |z₉| := habs9 _ _ _ _ _ _ _ _ _
      _ ≤ 15 * A * U * D ^ 4 := by linarith

/-- Canonical coefficient envelope, useful when no sharper
parameter-dependent constant has yet been selected. -/
noncomputable def latitudePowerCoefficientEnvelope (α : ℝ) : ℝ :=
  1 + |α / 2| +
    |(α / 2) * (α / 2 - 1)| +
    |(α / 2) * (α / 2 - 1) * (α / 2 - 2)| +
    |(α / 2) * (α / 2 - 1) * (α / 2 - 2) * (α / 2 - 3)|

theorem latitudePowerCoefficientBound_envelope (α : ℝ) :
    LatitudePowerCoefficientBound α
      (latitudePowerCoefficientEnvelope α) := by
  unfold LatitudePowerCoefficientBound latitudePowerCoefficientEnvelope
  have h1 := abs_nonneg (α / 2)
  have h2 := abs_nonneg ((α / 2) * (α / 2 - 1))
  have h3 := abs_nonneg
    ((α / 2) * (α / 2 - 1) * (α / 2 - 2))
  have h4 := abs_nonneg
    ((α / 2) * (α / 2 - 1) * (α / 2 - 2) * (α / 2 - 3))
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Canonical common envelope for the five coefficient powers. -/
noncomputable def latitudePowerRpowEnvelope (α s t : ℝ) : ℝ :=
  1 +
  |latitudeAngularScale s t ^ (α / 2)| +
  |latitudeAngularScale s t ^ (α / 2 - 1)| +
  |latitudeAngularScale s t ^ (α / 2 - 2)| +
  |latitudeAngularScale s t ^ (α / 2 - 3)| +
  |latitudeAngularScale s t ^ (α / 2 - 4)|

theorem latitudePowerRpowBound_envelope (α s t : ℝ) :
    LatitudePowerRpowBound α s t
      (latitudePowerRpowEnvelope α s t) := by
  unfold LatitudePowerRpowBound latitudePowerRpowEnvelope
  have h0 := abs_nonneg (latitudeAngularScale s t ^ (α / 2))
  have h1 := abs_nonneg (latitudeAngularScale s t ^ (α / 2 - 1))
  have h2 := abs_nonneg (latitudeAngularScale s t ^ (α / 2 - 2))
  have h3 := abs_nonneg (latitudeAngularScale s t ^ (α / 2 - 3))
  have h4 := abs_nonneg (latitudeAngularScale s t ^ (α / 2 - 4))
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Canonical common envelope for the eight angular derivatives. -/
noncomputable def latitudeAngularDerivativeJetEnvelope (s t : ℝ) : ℝ :=
  1 +
  |latitudeAngularScaleDs s t| +
  |latitudeAngularScaleDt s t| +
  |latitudeAngularScaleDss s t| +
  |latitudeAngularScaleDtt s t| +
  |latitudeAngularScaleDst s t| +
  |latitudeAngularScaleDsst s t| +
  |latitudeAngularScaleDstt s t| +
  |latitudeAngularScaleDsstt s t|

theorem latitudeAngularDerivativeJetBound_envelope (s t : ℝ) :
    LatitudeAngularDerivativeJetBound s t
      (latitudeAngularDerivativeJetEnvelope s t) := by
  unfold LatitudeAngularDerivativeJetBound
    latitudeAngularDerivativeJetEnvelope
  have h1 := abs_nonneg (latitudeAngularScaleDs s t)
  have h2 := abs_nonneg (latitudeAngularScaleDt s t)
  have h3 := abs_nonneg (latitudeAngularScaleDss s t)
  have h4 := abs_nonneg (latitudeAngularScaleDtt s t)
  have h5 := abs_nonneg (latitudeAngularScaleDst s t)
  have h6 := abs_nonneg (latitudeAngularScaleDsst s t)
  have h7 := abs_nonneg (latitudeAngularScaleDstt s t)
  have h8 := abs_nonneg (latitudeAngularScaleDsstt s t)
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Fully concrete power-jet bound obtained by inserting the three
canonical self-envelopes into the checked ten-entry estimate. -/
theorem latitudePowerJetBound_selfEnvelope (α s t : ℝ) :
    LatitudePowerJetBound α s t
      (15 * latitudePowerCoefficientEnvelope α *
        latitudePowerRpowEnvelope α s t *
        latitudeAngularDerivativeJetEnvelope s t ^ 4) := by
  exact latitudePowerJetBound_of_coefficient_rpow_angular
    (latitudePowerCoefficientBound_envelope α)
    (latitudePowerRpowBound_envelope α s t)
    (latitudeAngularDerivativeJetBound_envelope s t)

/-- Fully explicit off-diagonal bound for the genuine mixed `(2,2)`
latitude derivative.  This inserts the canonical power envelope, the sharp
reduced-cusp value envelope, and the radius-floor normalized-gap envelope
into the checked `4 P H + 36 P H Q` product-rule estimate. -/
theorem abs_variableReducedLatitudeKernelDsstt_le_explicitEnvelope
    {α s t R : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (hst : s ≠ t)
    (hα : α ≤ 2) (hR : 0 < R)
    (hsfloor : R ≤ heightRadius s)
    (htfloor : R ≤ heightRadius t) :
    |variableReducedLatitudeKernelDsstt α s t| ≤
      4 *
        (15 * latitudePowerCoefficientEnvelope α *
          latitudePowerRpowEnvelope α s t *
          latitudeAngularDerivativeJetEnvelope s t ^ 4) *
        (2 * latitudeCuspValueEnvelope α (normalizedLatitudeGap s t) *
          latitudeGapRadiusEnvelope R ^ 2) +
      36 *
        (15 * latitudePowerCoefficientEnvelope α *
          latitudePowerRpowEnvelope α s t *
          latitudeAngularDerivativeJetEnvelope s t ^ 4) *
        (2 * latitudeCuspValueEnvelope α (normalizedLatitudeGap s t) *
          latitudeGapRadiusEnvelope R ^ 2) *
        (4 * latitudeGapRadiusEnvelope R ^ 2) := by
  have hP := latitudePowerJetBound_selfEnvelope α s t
  have hH := latitudeCuspJetBound_of_radiusFloor
    hs ht hst hα hR hsfloor htfloor
  have hs' : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hQ := latitudeGapJetBound_of_radiusFloor
    hs' ht' hR hsfloor htfloor
  exact abs_variableReducedLatitudeKernelDsstt_le_envelopes hP hH hQ

end BEMOC
