import BEMOCFormalization.LatitudeCentralComparableClosure
import BEMOCFormalization.LatitudeGenericSharpComparableClosure
import BEMOCFormalization.LatitudeResonantEndpointClosure
import BEMOCFormalization.LatitudeResonantOscillationClosure

/-!
# Central resonant comparable closure

The central neighboring chart has a fixed positive angular radius.  This
module specializes the scale-normalized resonant extraction at `R = 1/5`,
freezes its two dimensionless coefficients on each neighboring rectangle,
and combines the resulting local estimate with the generic separated
central closure.
-/

open MeasureTheory Set

namespace BEMOC

set_option maxHeartbeats 800000

noncomputable def centralResonantRadius : ℝ := (1 : ℝ) / 5

noncomputable def centralResonantNormalizedLength
    (N : ℕ) (j k : Fin (bandTailCount N + 1)) : ℝ :=
  neighboringBandLength N j k / centralResonantRadius ^ 2

theorem centralResonantRadius_pos : 0 < centralResonantRadius := by
  norm_num [centralResonantRadius]

theorem centralResonantNormalizedLength_nonneg
    (N : ℕ) (j k : Fin (bandTailCount N + 1)) :
    0 ≤ centralResonantNormalizedLength N j k := by
  unfold centralResonantNormalizedLength
  exact div_nonneg
    (add_nonneg (bandWidth_nonneg (N := N) j)
      (bandWidth_nonneg (N := N) k))
    (sq_nonneg centralResonantRadius)

private theorem central_resonant_radius_bounds
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧
      centralResonantRadius ≤ heightRadius s ∧
      centralResonantRadius ≤ heightRadius t ∧
      heightRadius s ≤ 40 * centralResonantRadius ∧
      heightRadius t ≤ 40 * centralResonantRadius := by
  have hchart := centralComparable_neighboring_rectangle_chart
    hM hcentral hcomp hneigh hs ht
  have habs := abs_centralComparable_neighboring_rectangle_le
    hM hcentral hcomp hneigh hs ht
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨hchart.1.1.le, hchart.1.2.le⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨hchart.2.1.1.le, hchart.2.1.2.le⟩
  have hrsq := heightRadius_sq hsSphere
  have hrtsq := heightRadius_sq htSphere
  have hrs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
  have hrt0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
  have hsSq : s ^ 2 ≤ (1 : ℝ) / 1600 := by
    have hmul := mul_self_le_mul_self (abs_nonneg s) habs.1
    norm_num at hmul ⊢
    simpa [pow_two] using hmul
  have htSq : t ^ 2 ≤ (1 : ℝ) / 1600 := by
    have hmul := mul_self_le_mul_self (abs_nonneg t) habs.2
    norm_num at hmul ⊢
    simpa [pow_two] using hmul
  have hrsLower : (1 : ℝ) / 2 ≤ heightRadius s := by nlinarith
  have hrtLower : (1 : ℝ) / 2 ≤ heightRadius t := by nlinarith
  have hrsUpper := heightRadius_le_one hsSphere
  have hrtUpper := heightRadius_le_one htSphere
  refine ⟨hchart.1, hchart.2.1, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [centralResonantRadius] at * <;> linarith

private theorem central_same_coordinate_sub_le_length
    {N : ℕ} {j k : Fin (bandTailCount N + 1)}
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |s - u| ≤ neighboringBandLength N j k ∧
      |t - v| ≤ neighboringBandLength N j k := by
  have hsu : |s - u| ≤ bandWidth N j := by
    rw [abs_le]
    unfold bandWidth
    constructor <;> linarith [hs.1, hs.2, hu.1, hu.2]
  have htv : |t - v| ≤ bandWidth N k := by
    rw [abs_le]
    unfold bandWidth
    constructor <;> linarith [ht.1, ht.2, hv.1, hv.2]
  unfold neighboringBandLength
  constructor
  · linarith [bandWidth_nonneg (N := N) k]
  · linarith [bandWidth_nonneg (N := N) j]

theorem centralComparable_resonant_normalizedRadius_oscillation
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |heightRadius s / centralResonantRadius -
        heightRadius u / centralResonantRadius| ≤
        centralResonantNormalizedLength N j k ∧
      |heightRadius t / centralResonantRadius -
        heightRadius v / centralResonantRadius| ≤
        centralResonantNormalizedLength N j k := by
  have hst := central_resonant_radius_bounds
    hM hcentral hcomp hneigh hs ht
  have huv := central_resonant_radius_bounds
    hM hcentral hcomp hneigh hu hv
  have hcoord := central_same_coordinate_sub_le_length hs hu ht hv
  constructor
  · exact (abs_normalizedHeightRadius_sub_le centralResonantRadius_pos
      hst.1 huv.1 hst.2.2.1 huv.2.2.1).trans (by
        unfold centralResonantNormalizedLength
        exact div_le_div_of_nonneg_right hcoord.1
          (sq_nonneg centralResonantRadius))
  · exact (abs_normalizedHeightRadius_sub_le centralResonantRadius_pos
      hst.2.1 huv.2.1 hst.2.2.2.1 huv.2.2.2.1).trans (by
        unfold centralResonantNormalizedLength
        exact div_le_div_of_nonneg_right hcoord.2
          (sq_nonneg centralResonantRadius))

theorem centralComparable_resonant_normalizedGap_oscillation
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |normalizedLatitudeGap s t - normalizedLatitudeGap u v| ≤
      centralResonantNormalizedLength N j k := by
  let a := neighboringBandLength N j k
  let δ := centralResonantNormalizedLength N j k
  have ha0 : 0 ≤ a := by
    dsimp [a, neighboringBandLength]
    exact add_nonneg (bandWidth_nonneg (N := N) j)
      (bandWidth_nonneg (N := N) k)
  have ha : a ≤ (1 : ℝ) / 40 := by
    have hw := centralComparable_bandWidths_le_one_eighty
      hM hcentral hcomp
    dsimp [a, neighboringBandLength]
    linarith
  have hst := abs_sub_le_neighboringBandLength j k hneigh hs ht
  have huv := abs_sub_le_neighboringBandLength j k hneigh hu hv
  have hqst := centralComparable_neighboring_normalizedLatitudeGap_le_sq
    hM hcentral hcomp hneigh hs ht
  have hquv := centralComparable_neighboring_normalizedLatitudeGap_le_sq
    hM hcentral hcomp hneigh hu hv
  have hstSq : (s - t) ^ 2 ≤ a ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [a] using hst) 2
  have huvSq : (u - v) ^ 2 ≤ a ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [a] using huv) 2
  have hδ : δ = 25 * a := by
    dsimp [δ, centralResonantNormalizedLength, centralResonantRadius]
    ring
  rw [abs_le]
  constructor <;> dsimp [δ] at * <;> rw [hδ] <;>
    nlinarith [sq_nonneg a]

theorem centralComparable_resonant_normalizedLength_le_one
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k) :
    centralResonantNormalizedLength N j k ≤ 1 := by
  have hw := centralComparable_bandWidths_le_one_eighty
    hM hcentral hcomp
  unfold centralResonantNormalizedLength neighboringBandLength
    centralResonantRadius
  norm_num
  linarith

theorem centralComparable_resonant_coefficients_bounded
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    0 < neighboringNormalizedQuadraticCoefficient
        centralResonantRadius s t ∧
      neighboringNormalizedQuadraticCoefficient
        centralResonantRadius s t ≤ (1 : ℝ) / 2 ∧
      0 < neighboringNormalizedAngularCoefficient
        centralResonantRadius s t ∧
      neighboringNormalizedAngularCoefficient
        centralResonantRadius s t ≤ 3200 := by
  have hb := central_resonant_radius_bounds
    hM hcentral hcomp hneigh hs ht
  have hq := centralComparable_neighboring_normalizedLatitudeGap_le_sq
    hM hcentral hcomp hneigh hs ht
  have hq1 := centralComparable_neighboring_rectangle_normalizedLatitudeGap_le_one
    hM hcentral hcomp hneigh hs ht
  exact neighboring_normalized_resonant_coefficients_bounded
    centralResonantRadius_pos hb.1 hb.2.1
    hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
    hq.1 hq1

theorem centralComparable_resonant_normalizedQuadraticCoefficient_oscillation
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringNormalizedQuadraticCoefficient
          centralResonantRadius s t -
        neighboringNormalizedQuadraticCoefficient
          centralResonantRadius u v| ≤
      4000000 * centralResonantNormalizedLength N j k := by
  let R := centralResonantRadius
  let δ := centralResonantNormalizedLength N j k
  have hδ : 0 ≤ δ :=
    centralResonantNormalizedLength_nonneg N j k
  have hst := central_resonant_radius_bounds
    hM hcentral hcomp hneigh hs ht
  have huv := central_resonant_radius_bounds
    hM hcentral hcomp hneigh hu hv
  have hqst := centralComparable_neighboring_normalizedLatitudeGap_le_sq
    hM hcentral hcomp hneigh hs ht
  have hquv := centralComparable_neighboring_normalizedLatitudeGap_le_sq
    hM hcentral hcomp hneigh hu hv
  have hqst1 :=
    centralComparable_neighboring_rectangle_normalizedLatitudeGap_le_one
      hM hcentral hcomp hneigh hs ht
  have hquv1 :=
    centralComparable_neighboring_rectangle_normalizedLatitudeGap_le_one
      hM hcentral hcomp hneigh hu hv
  have hrad := centralComparable_resonant_normalizedRadius_oscillation
    hM hcentral hcomp hneigh hs hu ht hv
  have hgap := centralComparable_resonant_normalizedGap_oscillation
    hM hcentral hcomp hneigh hs hu ht hv
  have radiusBounds {x : ℝ}
      (hfloor : R ≤ heightRadius x)
      (hceil : heightRadius x ≤ 40 * R) :
      1 ≤ heightRadius x / R ∧ heightRadius x / R ≤ 40 := by
    constructor
    · exact (le_div_iff₀ (by simpa [R] using centralResonantRadius_pos)).2
        (by simpa using hfloor)
    · exact (div_le_iff₀ (by simpa [R] using centralResonantRadius_pos)).2
        (by simpa using hceil)
  have hsB := radiusBounds hst.2.2.1 hst.2.2.2.2.1
  have htB := radiusBounds hst.2.2.2.1 hst.2.2.2.2.2
  have huB := radiusBounds huv.2.2.1 huv.2.2.2.2.1
  have hvB := radiusBounds huv.2.2.2.1 huv.2.2.2.2.2
  have hraw := abs_inverse_normalizedGapDenominator_sub_le
    hδ hsB.1 htB.1 huB.1 hvB.1
    hsB.2 htB.2 huB.2 hvB.2
    (by simpa [R, δ] using hrad.1)
    (by simpa [R, δ] using hrad.2)
    hqst.1 hquv.1 hqst1 hquv1
    (by simpa [δ] using hgap)
  rw [neighboringNormalizedQuadraticCoefficient_eq_inverse
      (by simpa [R] using centralResonantRadius_pos),
    neighboringNormalizedQuadraticCoefficient_eq_inverse
      (by simpa [R] using centralResonantRadius_pos)]
  simpa [R, δ] using hraw

private theorem abs_central_sqrtProductParameter_sub_le
    {a b c d p q δ : ℝ}
    (hδ : 0 ≤ δ)
    (ha0 : 1 ≤ a) (hb0 : 1 ≤ b)
    (hc0 : 1 ≤ c) (hd0 : 1 ≤ d)
    (hb1 : b ≤ 40) (hc1 : c ≤ 40)
    (hac : |a - c| ≤ δ) (hbd : |b - d| ≤ δ)
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hp : p ^ 2 = 2 * a * b)
    (hq : q ^ 2 = 2 * c * d) :
    |p - q| ≤ 80 * δ := by
  have hab :
      |a * b - c * d| ≤ 80 * δ := by
    calc
      |a * b - c * d| =
          |(a - c) * b + c * (b - d)| := by ring_nf
      _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add _ _
      _ = |a - c| * |b| + |c| * |b - d| := by
        rw [abs_mul, abs_mul]
      _ ≤ δ * 40 + 40 * δ := by
        rw [abs_of_nonneg (by linarith : 0 ≤ b),
          abs_of_nonneg (by linarith : 0 ≤ c)]
        gcongr
      _ = 80 * δ := by ring
  have hablo : 1 ≤ a * b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha0) (sub_nonneg.mpr hb0)]
  have hcdlo : 1 ≤ c * d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc0) (sub_nonneg.mpr hd0)]
  have hp1 : 1 ≤ p := by nlinarith [sq_nonneg (p - 1)]
  have hq1 : 1 ≤ q := by nlinarith [sq_nonneg (q - 1)]
  have hid :
      |p - q| * (p + q) = 2 * |a * b - c * d| := by
    calc
      |p - q| * (p + q) = |(p - q) * (p + q)| := by
        rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ p + q)]
      _ = |p ^ 2 - q ^ 2| := by ring_nf
      _ = |2 * (a * b - c * d)| := by rw [hp, hq]; ring
      _ = 2 * |a * b - c * d| := by rw [abs_mul]; norm_num
  have hmul : 2 * |p - q| ≤ 160 * δ := by
    calc
      2 * |p - q| ≤ |p - q| * (p + q) := by
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_right
            (by linarith : 2 ≤ p + q) (abs_nonneg (p - q)))
      _ = 2 * |a * b - c * d| := hid
      _ ≤ 2 * (80 * δ) := by gcongr
      _ = 160 * δ := by ring
  linarith

theorem centralComparable_resonant_normalizedAngularCoefficient_oscillation
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringNormalizedAngularCoefficient centralResonantRadius s t -
        neighboringNormalizedAngularCoefficient centralResonantRadius u v| ≤
      80 * centralResonantNormalizedLength N j k := by
  let R := centralResonantRadius
  let δ := centralResonantNormalizedLength N j k
  have hst := central_resonant_radius_bounds
    hM hcentral hcomp hneigh hs ht
  have huv := central_resonant_radius_bounds
    hM hcentral hcomp hneigh hu hv
  have hrad := centralComparable_resonant_normalizedRadius_oscillation
    hM hcentral hcomp hneigh hs hu ht hv
  have hbst := centralComparable_resonant_coefficients_bounded
    hM hcentral hcomp hneigh hs ht
  have hbuv := centralComparable_resonant_coefficients_bounded
    hM hcentral hcomp hneigh hu hv
  apply abs_central_sqrtProductParameter_sub_le
    (centralResonantNormalizedLength_nonneg N j k)
  · exact (le_div_iff₀ centralResonantRadius_pos).2
      (by simpa using hst.2.2.1)
  · exact (le_div_iff₀ centralResonantRadius_pos).2
      (by simpa using hst.2.2.2.1)
  · exact (le_div_iff₀ centralResonantRadius_pos).2
      (by simpa using huv.2.2.1)
  · exact (le_div_iff₀ centralResonantRadius_pos).2
      (by simpa using huv.2.2.2.1)
  · exact (div_le_iff₀ centralResonantRadius_pos).2 hst.2.2.2.2.2
  · exact (div_le_iff₀ centralResonantRadius_pos).2 huv.2.2.2.2.1
  · simpa [R, δ] using hrad.1
  · simpa [R, δ] using hrad.2
  · exact hbst.2.2.1.le
  · exact hbuv.2.2.1.le
  · simpa [R] using neighboringNormalizedAngularCoefficient_sq
      centralResonantRadius_pos hst.1 hst.2.1
  · simpa [R] using neighboringNormalizedAngularCoefficient_sq
      centralResonantRadius_pos huv.1 huv.2.1

theorem centralComparable_resonant_normalizedQuadraticCoefficient_lower
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 : ℝ) / 2000 ≤
      neighboringNormalizedQuadraticCoefficient
        centralResonantRadius s t := by
  have hc := centralComparable_neighboring_quadraticGapCoefficient_bounds
    hM hcentral hcomp hneigh hs ht
  unfold neighboringNormalizedQuadraticCoefficient centralResonantRadius
  norm_num
  linarith

theorem centralComparable_resonant_logQuadraticCoefficient_abs_le
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |Real.log (neighboringNormalizedQuadraticCoefficient
      centralResonantRadius s t)| ≤ 7680000 := by
  let c := neighboringNormalizedQuadraticCoefficient
    centralResonantRadius s t
  have hc := centralComparable_resonant_coefficients_bounded
    hM hcentral hcomp hneigh hs ht
  have hclower :=
    centralComparable_resonant_normalizedQuadraticCoefficient_lower
      hM hcentral hcomp hneigh hs ht
  have hcinv : c⁻¹ ≤ 2000 := by
    have hm : (0 : ℝ) < 1 / 2000 := by norm_num
    have hi : c⁻¹ ≤ ((1 : ℝ) / 2000)⁻¹ :=
      (inv_le_inv₀ hc.1 hm).2 (by simpa [c] using hclower)
    norm_num at hi ⊢
    exact hi
  have hlogInv :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr (by simpa [c] using hc.1))
  rw [Real.log_inv] at hlogInv
  have hlogLower : -2000 ≤ Real.log c := by linarith
  have hlogUpper : Real.log c ≤ 0 :=
    Real.log_nonpos (by simpa [c] using hc.1.le)
      (by simpa [c] using (hc.2.1.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)))
  rw [abs_of_nonpos hlogUpper]
  linarith

theorem centralComparable_resonant_logQuadraticCoefficient_oscillation
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |Real.log (neighboringNormalizedQuadraticCoefficient
          centralResonantRadius s t) -
        Real.log (neighboringNormalizedQuadraticCoefficient
          centralResonantRadius u v)| ≤
      neighboringResonantLogOscillationConstant *
        centralResonantNormalizedLength N j k := by
  let cs := neighboringNormalizedQuadraticCoefficient
    centralResonantRadius s t
  let cu := neighboringNormalizedQuadraticCoefficient
    centralResonantRadius u v
  let δ := centralResonantNormalizedLength N j k
  have hcs := centralComparable_resonant_normalizedQuadraticCoefficient_lower
    hM hcentral hcomp hneigh hs ht
  have hcu := centralComparable_resonant_normalizedQuadraticCoefficient_lower
    hM hcentral hcomp hneigh hu hv
  have hc :=
    centralComparable_resonant_normalizedQuadraticCoefficient_oscillation
      hM hcentral hcomp hneigh hs hu ht hv
  have hraw := abs_log_sub_le_div_of_lower
    (by norm_num : (0 : ℝ) < 1 / 2000)
    (by simpa [cs] using hcs) (by simpa [cu] using hcu)
  calc
    |Real.log cs - Real.log cu| ≤ |cs - cu| / ((1 : ℝ) / 2000) :=
      hraw
    _ ≤ (4000000 * δ) / ((1 : ℝ) / 2000) := by gcongr
    _ ≤ neighboringResonantLogOscillationConstant * δ := by
      unfold neighboringResonantLogOscillationConstant
      have hδ := centralResonantNormalizedLength_nonneg N j k
      dsimp [δ] at *
      nlinarith

theorem centralComparable_resonantAmplitude_oscillation
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringResonantAmplitude centralResonantRadius s t -
        neighboringResonantAmplitude centralResonantRadius u v| ≤
      neighboringResonantAmplitudeOscillationConstant *
        centralResonantNormalizedLength N j k := by
  let δ := centralResonantNormalizedLength N j k
  have hp := centralComparable_resonant_normalizedAngularCoefficient_oscillation
    hM hcentral hcomp hneigh hs hu ht hv
  have hc :=
    centralComparable_resonant_normalizedQuadraticCoefficient_oscillation
      hM hcentral hcomp hneigh hs hu ht hv
  have hbs := centralComparable_resonant_coefficients_bounded
    hM hcentral hcomp hneigh hs ht
  have hbu := centralComparable_resonant_coefficients_bounded
    hM hcentral hcomp hneigh hu hv
  have hδ : 0 ≤ δ :=
    centralResonantNormalizedLength_nonneg N j k
  unfold neighboringResonantAmplitude
  rw [show
    neighboringNormalizedAngularCoefficient centralResonantRadius s t *
        neighboringNormalizedQuadraticCoefficient centralResonantRadius s t -
      neighboringNormalizedAngularCoefficient centralResonantRadius u v *
        neighboringNormalizedQuadraticCoefficient centralResonantRadius u v =
      (neighboringNormalizedAngularCoefficient centralResonantRadius s t -
        neighboringNormalizedAngularCoefficient centralResonantRadius u v) *
          neighboringNormalizedQuadraticCoefficient centralResonantRadius s t +
      neighboringNormalizedAngularCoefficient centralResonantRadius u v *
        (neighboringNormalizedQuadraticCoefficient centralResonantRadius s t -
          neighboringNormalizedQuadraticCoefficient centralResonantRadius u v) by
      ring]
  calc
    |_ + _| ≤
        |(neighboringNormalizedAngularCoefficient centralResonantRadius s t -
          neighboringNormalizedAngularCoefficient centralResonantRadius u v) *
            neighboringNormalizedQuadraticCoefficient centralResonantRadius s t| +
        |neighboringNormalizedAngularCoefficient centralResonantRadius u v *
          (neighboringNormalizedQuadraticCoefficient centralResonantRadius s t -
            neighboringNormalizedQuadraticCoefficient centralResonantRadius u v)| :=
      abs_add _ _
    _ ≤ (80 * δ) * ((1 : ℝ) / 2) +
        3200 * (4000000 * δ) := by
      simp only [abs_mul]
      rw [abs_of_pos hbs.1, abs_of_pos hbu.2.2.1]
      exact add_le_add
        (mul_le_mul hp hbs.2.1 hbs.1.le (by positivity))
        (mul_le_mul hbu.2.2.2 hc (abs_nonneg _) (by positivity))
    _ = neighboringResonantAmplitudeOscillationConstant * δ := by
      unfold neighboringResonantAmplitudeOscillationConstant
      ring

theorem centralComparable_resonantLogAmplitude_oscillation
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringResonantLogAmplitude centralResonantRadius s t -
        neighboringResonantLogAmplitude centralResonantRadius u v| ≤
      neighboringResonantLogAmplitudeOscillationConstant *
        centralResonantNormalizedLength N j k := by
  let δ := centralResonantNormalizedLength N j k
  let As := neighboringResonantAmplitude centralResonantRadius s t
  let Au := neighboringResonantAmplitude centralResonantRadius u v
  let cs := neighboringNormalizedQuadraticCoefficient
    centralResonantRadius s t
  let cu := neighboringNormalizedQuadraticCoefficient
    centralResonantRadius u v
  have hδ : 0 ≤ δ :=
    centralResonantNormalizedLength_nonneg N j k
  have hA := centralComparable_resonantAmplitude_oscillation
    hM hcentral hcomp hneigh hs hu ht hv
  have hlog :=
    centralComparable_resonant_logQuadraticCoefficient_oscillation
      hM hcentral hcomp hneigh hs hu ht hv
  have hlogBound :=
    centralComparable_resonant_logQuadraticCoefficient_abs_le
      hM hcentral hcomp hneigh hs ht
  have hbu := centralComparable_resonant_coefficients_bounded
    hM hcentral hcomp hneigh hu hv
  have hAu0 : 0 ≤ Au := by
    dsimp [Au, neighboringResonantAmplitude]
    exact mul_nonneg hbu.2.2.1.le hbu.1.le
  have hAu : Au ≤ 1600 := by
    dsimp [Au, neighboringResonantAmplitude]
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hbu.2.2.2)
      (sub_nonneg.mpr hbu.2.1)]
  unfold neighboringResonantLogAmplitude
  rw [show
    As * Real.log cs - Au * Real.log cu =
      (As - Au) * Real.log cs +
        Au * (Real.log cs - Real.log cu) by ring]
  calc
    |_ + _| ≤
        |(As - Au) * Real.log cs| +
          |Au * (Real.log cs - Real.log cu)| := abs_add _ _
    _ = |As - Au| * |Real.log cs| +
          Au * |Real.log cs - Real.log cu| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hAu0]
    _ ≤
        (neighboringResonantAmplitudeOscillationConstant * δ) * 7680000 +
          1600 * (neighboringResonantLogOscillationConstant * δ) := by
      exact add_le_add
        (mul_le_mul hA (by simpa [cs] using hlogBound)
          (abs_nonneg _)
          (by
            unfold neighboringResonantAmplitudeOscillationConstant
            positivity))
        (mul_le_mul hAu (by simpa [δ, cs, cu] using hlog)
          (abs_nonneg _) (by positivity))
    _ ≤ neighboringResonantLogAmplitudeOscillationConstant * δ := by
      unfold neighboringResonantAmplitudeOscillationConstant
        neighboringResonantLogOscillationConstant
        neighboringResonantLogAmplitudeOscillationConstant
      nlinarith

theorem centralComparable_resonantNormalizedPrincipal_freezing
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringResonantNormalizedPrincipal
          centralResonantRadius s t -
        neighboringResonantFrozenNormalizedPrincipal
          centralResonantRadius u v s t| ≤
      (2 * neighboringResonantAmplitudeOscillationConstant *
          resonantUnitLinearConstant +
        neighboringResonantLogAmplitudeOscillationConstant) *
        centralResonantNormalizedLength N j k ^ 2 := by
  let R := centralResonantRadius
  let δ := centralResonantNormalizedLength N j k
  let z := (s - t) / R ^ 2
  have hδ0 : 0 ≤ δ :=
    centralResonantNormalizedLength_nonneg N j k
  have hδ1 : δ ≤ 1 :=
    centralComparable_resonant_normalizedLength_le_one hM hcentral hcomp
  have hw := abs_sub_le_neighboringBandLength j k hneigh hs ht
  have hz : |z| ≤ δ := by
    dsimp [z, δ, centralResonantNormalizedLength]
    rw [abs_div, abs_of_pos (sq_pos_of_pos centralResonantRadius_pos)]
    exact div_le_div_of_nonneg_right hw
      (sq_pos_of_pos centralResonantRadius_pos).le
  have hr :
      |resonantLatitudeBranch z| ≤ resonantUnitLinearConstant * |z| :=
    abs_resonantLatitudeBranch_le_unitLinearConstant (hz.trans hδ1)
  have hA := centralComparable_resonantAmplitude_oscillation
    hM hcentral hcomp hneigh hs hu ht hv
  have hB := centralComparable_resonantLogAmplitude_oscillation
    hM hcentral hcomp hneigh hs hu ht hv
  have hfree := abs_resonantPrincipal_freezing_remainder_le
    (LA := neighboringResonantAmplitudeOscillationConstant)
    (LB := neighboringResonantLogAmplitudeOscillationConstant)
    (L := resonantUnitLinearConstant)
    hδ0 hδ1
    (by unfold neighboringResonantAmplitudeOscillationConstant; norm_num)
    (by unfold neighboringResonantLogAmplitudeOscillationConstant; norm_num)
    resonantUnitLinearConstant_nonneg
    (by simpa [R, δ] using hA)
    (by simpa [R, δ] using hB)
    hz hr
  simpa [neighboringResonantNormalizedPrincipal,
    neighboringResonantFrozenNormalizedPrincipal, R, δ, z] using hfree

theorem centralComparable_resonantPrincipal_freezing
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringResonantPrincipalKernel s t -
        neighboringResonantFrozenPrincipalKernel
          centralResonantRadius u v s t| ≤
      centralResonantRadius *
        |reducedCuspResonantPrincipalCoefficient| *
        ((2 * neighboringResonantAmplitudeOscillationConstant *
            resonantUnitLinearConstant +
          neighboringResonantLogAmplitudeOscillationConstant) *
          centralResonantNormalizedLength N j k ^ 2) := by
  have hchart := centralComparable_neighboring_rectangle_chart
    hM hcentral hcomp hneigh hs ht
  have hfree := centralComparable_resonantNormalizedPrincipal_freezing
    hM hcentral hcomp hneigh hs hu ht hv
  rw [neighboringResonantPrincipalKernel_eq_normalized
    centralResonantRadius_pos hchart.1 hchart.2.1]
  unfold neighboringResonantFrozenPrincipalKernel
  rw [← mul_sub, abs_mul, abs_mul, abs_of_pos centralResonantRadius_pos]
  exact mul_le_mul_of_nonneg_left hfree
    (mul_nonneg centralResonantRadius_pos.le (abs_nonneg _))

noncomputable def centralResonantHigherBranchRawConstant : ℝ :=
  8 * centralResonantRadius * 3200 *
    ((4 / 3 : ℝ) * reducedCuspResonantRemainderCoefficient)

theorem centralResonantHigherBranchRawConstant_nonneg :
    0 ≤ centralResonantHigherBranchRawConstant := by
  unfold centralResonantHigherBranchRawConstant
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) centralResonantRadius_pos.le)
      (by norm_num))
    (mul_nonneg (by norm_num)
      reducedCuspResonantRemainderCoefficient_nonneg)

theorem abs_centralResonantHigherBranchKernel_le_physicalCusp_onRectangle
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringResonantHigherBranchKernel s t| ≤
      centralResonantHigherBranchRawConstant * |s - t| ^ (2 : ℝ) := by
  by_cases hst : s = t
  · subst t
    have hchart := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hs ht
    have hr : heightRadius s ≠ 0 := (heightRadius_pos hchart.1).ne'
    have hrsq := heightRadius_sq ⟨hchart.1.1.le, hchart.1.2.le⟩
    have hden : 1 - s * s ≠ 0 := by
      rw [← show heightRadius s * heightRadius s = 1 - s * s by
        nlinarith]
      exact mul_ne_zero hr hr
    have hq : normalizedLatitudeGap s s = 0 := by
      unfold normalizedLatitudeGap
      rw [show heightRadius s * heightRadius s = 1 - s * s by
        nlinarith]
      field_simp [hden]
    rw [show neighboringResonantHigherBranchKernel s s = 0 by
      unfold neighboringResonantHigherBranchKernel
      rw [hq, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
      ring]
    simp
  · have hchart := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hs ht
    have hraw := abs_neighboringResonantHigherBranchKernel_le
      hchart.1 hchart.2.1 hst hchart.2.2
    have hq :=
      centralComparable_neighboring_normalizedLatitudeGap_le_sq
        hM hcentral hcomp hneigh hs ht
    have hqpos : 0 < normalizedLatitudeGap s t :=
      normalizedLatitudeGap_pos hchart.1 hchart.2.1 hst
    have hqpow :
        normalizedLatitudeGap s t ^ ((3 : ℝ) / 2) ≤
          normalizedLatitudeGap s t := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge hqpos hchart.2.2
          (by norm_num : (1 : ℝ) ≤ 3 / 2))
    have hp := centralComparable_resonant_coefficients_bounded
      hM hcentral hcomp hneigh hs ht
    have hsqrt :
        latitudeAngularScale s t ^ (1 / 2 : ℝ) ≤
          centralResonantRadius * 3200 := by
      have hm := mul_le_mul_of_nonneg_left hp.2.2.2
        centralResonantRadius_pos.le
      unfold neighboringNormalizedAngularCoefficient at hm
      rw [mul_div_cancel₀ _ centralResonantRadius_pos.ne'] at hm
      exact hm
    have hcoef :
        0 ≤ (4 / 3 : ℝ) * reducedCuspResonantRemainderCoefficient :=
      mul_nonneg (by norm_num)
        reducedCuspResonantRemainderCoefficient_nonneg
    have hqpow' :
        normalizedLatitudeGap s t ^ ((3 : ℝ) / 2) ≤
          8 * (s - t) ^ 2 :=
      hqpow.trans hq.2
    have hfactor :
        latitudeAngularScale s t ^ ((1 : ℝ) / 2) *
            normalizedLatitudeGap s t ^ ((3 : ℝ) / 2) ≤
          (centralResonantRadius * 3200) *
            (8 * (s - t) ^ 2) :=
      mul_le_mul hsqrt hqpow'
        (Real.rpow_nonneg (by positivity) _)
        (mul_nonneg centralResonantRadius_pos.le (by norm_num))
    calc
      |neighboringResonantHigherBranchKernel s t| ≤
          (latitudeAngularScale s t ^ ((1 : ℝ) / 2) *
            normalizedLatitudeGap s t ^ ((3 : ℝ) / 2)) *
              ((4 / 3 : ℝ) *
                reducedCuspResonantRemainderCoefficient) := by
        simpa only [mul_assoc] using hraw
      _ ≤ ((centralResonantRadius * 3200) *
          (8 * (s - t) ^ 2)) *
            ((4 / 3 : ℝ) *
              reducedCuspResonantRemainderCoefficient) := by
        exact mul_le_mul_of_nonneg_right hfactor hcoef
      _ = centralResonantHigherBranchRawConstant *
          |s - t| ^ (2 : ℝ) := by
        rw [show |s - t| ^ (2 : ℝ) = (s - t) ^ 2 by
          rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast,
            sq_abs]]
        unfold centralResonantHigherBranchRawConstant
        ring

noncomputable def centralResonantFreezingConstant : ℝ :=
  2 * neighboringResonantAmplitudeOscillationConstant *
      resonantUnitLinearConstant +
    neighboringResonantLogAmplitudeOscillationConstant

noncomputable def centralResonantFrozenRawConstant : ℝ :=
  centralResonantRadius *
      (|reducedCuspResonantPrincipalCoefficient| * 3200) *
        resonantUnitBranchConstant /
    centralResonantRadius ^ 4

noncomputable def centralResonantFreezingRawConstant : ℝ :=
  centralResonantRadius *
      |reducedCuspResonantPrincipalCoefficient| *
        centralResonantFreezingConstant /
    centralResonantRadius ^ 4

noncomputable def centralResonantPrincipalRawConstant : ℝ :=
  centralResonantFrozenRawConstant +
    centralResonantFreezingRawConstant

theorem centralResonantFreezingConstant_nonneg :
    0 ≤ centralResonantFreezingConstant := by
  unfold centralResonantFreezingConstant
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (by
          unfold neighboringResonantAmplitudeOscillationConstant
          norm_num))
      resonantUnitLinearConstant_nonneg)
    (by
      unfold neighboringResonantLogAmplitudeOscillationConstant
      norm_num)

theorem centralResonantFrozenRawConstant_nonneg :
    0 ≤ centralResonantFrozenRawConstant := by
  unfold centralResonantFrozenRawConstant
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg centralResonantRadius_pos.le
        (mul_nonneg (abs_nonneg _) (by norm_num)))
      resonantUnitBranchConstant_nonneg)
    (pow_nonneg centralResonantRadius_pos.le 4)

theorem centralResonantFreezingRawConstant_nonneg :
    0 ≤ centralResonantFreezingRawConstant := by
  unfold centralResonantFreezingRawConstant
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg centralResonantRadius_pos.le (abs_nonneg _))
      centralResonantFreezingConstant_nonneg)
    (pow_nonneg centralResonantRadius_pos.le 4)

theorem centralResonantPrincipalRawConstant_nonneg :
    0 ≤ centralResonantPrincipalRawConstant := by
  unfold centralResonantPrincipalRawConstant
  exact add_nonneg centralResonantFrozenRawConstant_nonneg
    centralResonantFreezingRawConstant_nonneg

/-- On a central neighboring rectangle the logarithmic principal is
continuous, including at its removable diagonal singularity. -/
theorem continuousOn_neighboringResonantPrincipalKernel_centralRectangle
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦
        neighboringResonantPrincipalKernel p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
  let S : Set (ℝ × ℝ) :=
    Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j) ×ˢ
      Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)
  have hrcont : Continuous heightRadius := by
    unfold heightRadius
    exact (continuous_const.sub (continuous_id.pow 2)).sqrt
  have hq : ContinuousOn
      (fun p : ℝ × ℝ ↦ normalizedLatitudeGap p.1 p.2) S := by
    intro p hp
    have hchart := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hp.1 hp.2
    have hrs : heightRadius p.1 ≠ 0 :=
      (heightRadius_pos hchart.1).ne'
    have hrt : heightRadius p.2 ≠ 0 :=
      (heightRadius_pos hchart.2.1).ne'
    have hnum : ContinuousAt
        (fun q : ℝ × ℝ ↦ 1 - q.1 * q.2) p :=
      continuousAt_const.sub (continuousAt_fst.mul continuousAt_snd)
    have hden : ContinuousAt
        (fun q : ℝ × ℝ ↦ heightRadius q.1 * heightRadius q.2) p := by
      unfold heightRadius
      fun_prop
    exact ((hnum.div hden (mul_ne_zero hrs hrt)).sub
      continuousAt_const).continuousWithinAt
  have hang : Continuous
      (fun p : ℝ × ℝ ↦ latitudeAngularScale p.1 p.2) := by
    unfold latitudeAngularScale
    fun_prop
  have hangsqrt : Continuous
      (fun p : ℝ × ℝ ↦
        latitudeAngularScale p.1 p.2 ^ (1 / 2 : ℝ)) :=
    hang.rpow_const (fun _ ↦ Or.inr (by norm_num))
  have hqlog : ContinuousOn
      (fun p : ℝ × ℝ ↦
        normalizedLatitudeGap p.1 p.2 *
          Real.log (normalizedLatitudeGap p.1 p.2)) S := by
    simpa only [Function.comp_apply] using
      Real.continuous_mul_log.comp_continuousOn hq
  unfold neighboringResonantPrincipalKernel
  simpa [S, mul_assoc] using
    hangsqrt.continuousOn.mul (continuousOn_const.mul hqlog)

/-- The frozen resonant profile and the freezing error together give a
physical quadratic bound for the complete logarithmic principal. -/
theorem central_neighboring_resonantPrincipal_block_bound_raw
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k neighboringResonantPrincipalKernel| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (centralResonantPrincipalRawConstant *
            neighboringBandLength N j k ^ (2 : ℝ)) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let R := centralResonantRadius
  let u := bandBoundaryHeight N (j + 1)
  let v := bandBoundaryHeight N (k + 1)
  let A := neighboringResonantAmplitude R u v
  let B := neighboringResonantLogAmplitude R u v
  let F := neighboringResonantFrozenPrincipalProfile R A B
  let Rem : ℝ → ℝ → ℝ := fun s t ↦
    F s t - neighboringResonantPrincipalKernel s t
  have hR : 0 < R := by
    dsimp [R]
    exact centralResonantRadius_pos
  have hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j) :=
    ⟨le_rfl, bandBoundaryHeight_succ_le j⟩
  have hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k) :=
    ⟨le_rfl, bandBoundaryHeight_succ_le k⟩
  have hbuv := centralComparable_resonant_coefficients_bounded
    hM hcentral hcomp hneigh hu hv
  have hA0 : 0 ≤ A := by
    dsimp [A, neighboringResonantAmplitude]
    exact mul_nonneg hbuv.2.2.1.le hbuv.1.le
  have hA : A ≤ 1600 := by
    dsimp [A, neighboringResonantAmplitude]
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hbuv.2.2.2)
      (sub_nonneg.mpr hbuv.2.1)]
  have hcoef :
      |R * reducedCuspResonantPrincipalCoefficient * (2 * A)| ≤
        R * (|reducedCuspResonantPrincipalCoefficient| * 3200) := by
    rw [abs_mul, abs_mul, abs_of_pos hR,
      abs_of_nonneg (mul_nonneg (by norm_num) hA0)]
    nlinarith [mul_nonneg hR.le
      (mul_nonneg (abs_nonneg reducedCuspResonantPrincipalCoefficient)
        (sub_nonneg.mpr hA))]
  have hFrozenScaled :=
    abs_bandPairError_neighboringResonantFrozenPrincipalProfile_le
      hN (by omega : 3 ≤ bandCount N) j k hneigh hR
      (A := A) (B := B)
  have hFrozenRaw :
      |bandPairError N j k F| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (centralResonantFrozenRawConstant *
              neighboringBandLength N j k ^ (2 : ℝ)) := by
    calc
      |bandPairError N j k F| ≤
          |R * reducedCuspResonantPrincipalCoefficient * (2 * A)| *
            (4 * (finiteBandPopulation N j : ℝ) *
              (finiteBandPopulation N k : ℝ) *
                (((neighboringBandLength N j k / R ^ 2) ^ 2) *
                  resonantUnitBranchConstant)) := by
        simpa [F] using hFrozenScaled
      _ ≤ (R * (|reducedCuspResonantPrincipalCoefficient| * 3200)) *
            (4 * (finiteBandPopulation N j : ℝ) *
              (finiteBandPopulation N k : ℝ) *
                (((neighboringBandLength N j k / R ^ 2) ^ 2) *
                  resonantUnitBranchConstant)) := by
        exact mul_le_mul_of_nonneg_right hcoef
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
              (Nat.cast_nonneg _))
            (mul_nonneg (sq_nonneg _)
              resonantUnitBranchConstant_nonneg))
      _ = 4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (centralResonantFrozenRawConstant *
              neighboringBandLength N j k ^ (2 : ℝ)) := by
        dsimp [R, centralResonantFrozenRawConstant]
        field_simp [centralResonantRadius_pos.ne']
        ring
  have hRemRect :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          |Rem s t| ≤
            centralResonantFreezingRawConstant *
              neighboringBandLength N j k ^ (2 : ℝ) := by
    intro s hs t ht
    have hf := centralComparable_resonantPrincipal_freezing
      hM hcentral hcomp hneigh hs hu ht hv
    have hprofile :
        F s t =
          neighboringResonantFrozenPrincipalKernel R u v s t := by
      dsimp [F, A, B, neighboringResonantFrozenPrincipalProfile,
        neighboringResonantFrozenPrincipalKernel,
        neighboringResonantFrozenNormalizedPrincipal]
    dsimp [Rem]
    rw [abs_sub_comm, hprofile]
    calc
      |neighboringResonantPrincipalKernel s t -
          neighboringResonantFrozenPrincipalKernel R u v s t| ≤
        centralResonantRadius *
          |reducedCuspResonantPrincipalCoefficient| *
            (centralResonantFreezingConstant *
              centralResonantNormalizedLength N j k ^ 2) := by
        simpa [R, centralResonantFreezingConstant] using hf
      _ = centralResonantFreezingRawConstant *
          neighboringBandLength N j k ^ (2 : ℝ) := by
        unfold centralResonantFreezingRawConstant
          centralResonantNormalizedLength
        rw [show neighboringBandLength N j k ^ (2 : ℝ) =
          neighboringBandLength N j k ^ (2 : ℕ) by
            norm_num [Real.rpow_natCast]]
        field_simp [centralResonantRadius_pos.ne']
        ring
  have hRemRaw :
      |bandPairError N j k Rem| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (centralResonantFreezingRawConstant *
              neighboringBandLength N j k ^ (2 : ℝ)) := by
    apply abs_bandPairError_le_of_band_rectangle_bound hN j k Rem
      (centralResonantFreezingRawConstant *
        neighboringBandLength N j k ^ (2 : ℝ))
    · exact mul_nonneg centralResonantFreezingRawConstant_nonneg
        (Real.rpow_nonneg
          (by
            unfold neighboringBandLength
            exact add_nonneg (bandWidth_nonneg (N := N) j)
              (bandWidth_nonneg (N := N) k)) _)
    · exact hRemRect
  have hsplit :
      bandPairError N j k F =
        bandPairError N j k neighboringResonantPrincipalKernel +
          bandPairError N j k Rem := by
    exact
      bandPairError_eq_add_of_continuous_decomposition_on_literalRectangle
        j k F neighboringResonantPrincipalKernel Rem
        (continuous_neighboringResonantFrozenPrincipalProfile R A B)
        (continuousOn_neighboringResonantPrincipalKernel_centralRectangle
          hM hcentral hcomp hneigh)
        (by
          intro s hs t ht
          dsimp [Rem]
          ring)
  have htri :
      |bandPairError N j k neighboringResonantPrincipalKernel| ≤
        |bandPairError N j k F| + |bandPairError N j k Rem| := by
    calc
      |bandPairError N j k neighboringResonantPrincipalKernel| =
          |bandPairError N j k F - bandPairError N j k Rem| := by
        rw [hsplit]
        ring
      _ ≤ |bandPairError N j k F| + |bandPairError N j k Rem| :=
        abs_sub _ _
  calc
    |bandPairError N j k neighboringResonantPrincipalKernel| ≤
        |bandPairError N j k F| + |bandPairError N j k Rem| := htri
    _ ≤
        4 * (finiteBandPopulation N j : ℝ) *
            (finiteBandPopulation N k : ℝ) *
              (centralResonantFrozenRawConstant *
                neighboringBandLength N j k ^ (2 : ℝ)) +
          4 * (finiteBandPopulation N j : ℝ) *
            (finiteBandPopulation N k : ℝ) *
              (centralResonantFreezingRawConstant *
                neighboringBandLength N j k ^ (2 : ℝ)) :=
      add_le_add hFrozenRaw hRemRaw
    _ = 4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) *
          (centralResonantPrincipalRawConstant *
            neighboringBandLength N j k ^ (2 : ℝ)) := by
      unfold centralResonantPrincipalRawConstant
      ring

noncomputable def centralResonantSmoothBlockConstant : ℝ :=
  4 * (15 : ℝ) ^ 6 *
    centralAffineSmoothDssttConstant 1
      reducedCuspResonantConstantCoefficient
      reducedCuspResonantLinearCoefficient

noncomputable def centralResonantPrincipalBlockConstant : ℝ :=
  14400 * (15 : ℝ) ^ (1 + (1 : ℝ)) *
    centralResonantPrincipalRawConstant

noncomputable def centralResonantHigherBranchBlockConstant : ℝ :=
  14400 * (15 : ℝ) ^ (1 + (1 : ℝ)) *
    centralResonantHigherBranchRawConstant

noncomputable def centralResonantModelBlockConstant : ℝ :=
  centralResonantSmoothBlockConstant +
    centralResonantPrincipalBlockConstant

noncomputable def centralResonantNeighboringBlockConstant : ℝ :=
  centralResonantModelBlockConstant +
    centralResonantHigherBranchBlockConstant

theorem centralResonantSmoothBlockConstant_nonneg :
    0 ≤ centralResonantSmoothBlockConstant := by
  unfold centralResonantSmoothBlockConstant
  apply mul_nonneg (by positivity)
  unfold centralAffineSmoothDssttConstant centralPositivePowerJetConstant
    centralPositivePowerRpowBound centralPowerJetConstant
    centralNegativePowerRpowBound latitudePowerCoefficientEnvelope
    latitudeComparablePowerRpowConstant
  positivity

theorem centralResonantPrincipalBlockConstant_nonneg :
    0 ≤ centralResonantPrincipalBlockConstant := by
  unfold centralResonantPrincipalBlockConstant
  exact mul_nonneg (by positivity)
    centralResonantPrincipalRawConstant_nonneg

theorem centralResonantHigherBranchBlockConstant_nonneg :
    0 ≤ centralResonantHigherBranchBlockConstant := by
  unfold centralResonantHigherBranchBlockConstant
  exact mul_nonneg (by positivity)
    centralResonantHigherBranchRawConstant_nonneg

theorem centralResonantModelBlockConstant_nonneg :
    0 ≤ centralResonantModelBlockConstant := by
  unfold centralResonantModelBlockConstant
  exact add_nonneg centralResonantSmoothBlockConstant_nonneg
    centralResonantPrincipalBlockConstant_nonneg

theorem centralResonantNeighboringBlockConstant_nonneg :
    0 ≤ centralResonantNeighboringBlockConstant := by
  unfold centralResonantNeighboringBlockConstant
  exact add_nonneg centralResonantModelBlockConstant_nonneg
    centralResonantHigherBranchBlockConstant_nonneg

theorem central_neighboring_resonantPrincipal_block_bound
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k neighboringResonantPrincipalKernel| ≤
      comparableLatitudeBlockMajorant 1
        centralResonantPrincipalBlockConstant N j k := by
  have hraw := central_neighboring_resonantPrincipal_block_bound_raw
    hM hcentral hcomp hneigh
  have hmajor :=
    central_neighboring_cusp_raw_bound_to_majorant
      (α := (1 : ℝ)) (B := centralResonantPrincipalRawConstant)
      (by norm_num) (by norm_num)
      centralResonantPrincipalRawConstant_nonneg
      hM hcentral hcomp hneigh
      (by
        convert hraw using 1 <;> norm_num)
  simpa [centralResonantPrincipalBlockConstant] using hmajor

theorem central_neighboring_resonantModel_block_bound
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k neighboringResonantModelKernel| ≤
      comparableLatitudeBlockMajorant 1
        centralResonantModelBlockConstant N j k := by
  let S : Set (ℝ × ℝ) :=
    Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j) ×ˢ
      Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)
  let A := neighboringAffineSmoothKernel 1
    reducedCuspResonantConstantCoefficient
    reducedCuspResonantLinearCoefficient
  have hA : ContinuousOn
      (fun p : ℝ × ℝ ↦ A p.1 p.2) S := by
    intro p hp
    have hc := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hp.1 hp.2
    exact
      (continuousAt_neighboringAffineSmoothKernel_joint
        (α := (1 : ℝ))
        (H := reducedCuspResonantConstantCoefficient)
        (L := reducedCuspResonantLinearCoefficient)
        hc.1 hc.2.1).continuousWithinAt
  have hP : ContinuousOn
      (fun p : ℝ × ℝ ↦
        neighboringResonantPrincipalKernel p.1 p.2) S := by
    simpa [S] using
      continuousOn_neighboringResonantPrincipalKernel_centralRectangle
        hM hcentral hcomp hneigh
  have hdecomp :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          neighboringResonantModelKernel s t =
            A s t + neighboringResonantPrincipalKernel s t := by
    intro s hs t ht
    have hc := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hs ht
    rw [neighboringResonantModelKernel_eq_smooth_add_log
      hc.1 hc.2.1]
    rfl
  have hModel : ContinuousOn
      (fun p : ℝ × ℝ ↦ neighboringResonantModelKernel p.1 p.2) S := by
    apply (hA.add hP).congr
    intro p hp
    exact hdecomp p.1 hp.1 p.2 hp.2
  have heq :=
    bandPairError_eq_add_of_continuousOn_decomposition_on_literalRectangle
      j k neighboringResonantModelKernel A
      neighboringResonantPrincipalKernel hModel hA hdecomp
  have hsmoothRaw :=
    central_neighboring_resonantAffine_block_bound
      hM hcentral hcomp hneigh
  have hsmooth :=
    central_neighboring_smooth_raw_bound_to_majorant
      (α := (1 : ℝ))
      (S := centralAffineSmoothDssttConstant 1
        reducedCuspResonantConstantCoefficient
        reducedCuspResonantLinearCoefficient)
      (by norm_num) (by norm_num)
      (by
        unfold centralAffineSmoothDssttConstant
          centralPositivePowerJetConstant centralPositivePowerRpowBound
          centralPowerJetConstant centralNegativePowerRpowBound
          latitudePowerCoefficientEnvelope
          latitudeComparablePowerRpowConstant
        positivity)
      hM hcentral hcomp hneigh hsmoothRaw
  have hp := central_neighboring_resonantPrincipal_block_bound
    hM hcentral hcomp hneigh
  rw [heq]
  calc
    |bandPairError N j k A +
        bandPairError N j k neighboringResonantPrincipalKernel| ≤
      |bandPairError N j k A| +
        |bandPairError N j k neighboringResonantPrincipalKernel| :=
      abs_add _ _
    _ ≤ comparableLatitudeBlockMajorant 1
          centralResonantSmoothBlockConstant N j k +
        comparableLatitudeBlockMajorant 1
          centralResonantPrincipalBlockConstant N j k := by
      exact add_le_add
        (by
          simpa [A, centralResonantSmoothBlockConstant] using hsmooth)
        hp
    _ = comparableLatitudeBlockMajorant 1
        centralResonantModelBlockConstant N j k := by
      unfold comparableLatitudeBlockMajorant
        centralResonantModelBlockConstant
      ring

theorem central_neighboring_resonantHigherBranch_block_bound
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k neighboringResonantHigherBranchKernel| ≤
      comparableLatitudeBlockMajorant 1
        centralResonantHigherBranchBlockConstant N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hrect :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          |neighboringResonantHigherBranchKernel s t| ≤
            centralResonantHigherBranchRawConstant *
              neighboringBandLength N j k ^ (2 : ℝ) := by
    intro s hs t ht
    have hb :=
      abs_centralResonantHigherBranchKernel_le_physicalCusp_onRectangle
        hM hcentral hcomp hneigh hs ht
    have hw := abs_sub_le_neighboringBandLength j k hneigh hs ht
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hw (by norm_num))
      centralResonantHigherBranchRawConstant_nonneg)
  have hraw :=
    abs_bandPairError_neighboringResonantHigherBranchKernel_le_of_rectangle
      (C := centralResonantHigherBranchRawConstant *
        neighboringBandLength N j k ^ (2 : ℝ))
      (mul_nonneg centralResonantHigherBranchRawConstant_nonneg
        (Real.rpow_nonneg
          (by
            unfold neighboringBandLength
            exact add_nonneg (bandWidth_nonneg (N := N) j)
              (bandWidth_nonneg (N := N) k)) _))
      hN j k hrect
  have hmajor :=
    central_neighboring_cusp_raw_bound_to_majorant
      (α := (1 : ℝ)) (B := centralResonantHigherBranchRawConstant)
      (by norm_num) (by norm_num)
      centralResonantHigherBranchRawConstant_nonneg
      hM hcentral hcomp hneigh
      (by
        convert hraw using 1 <;> norm_num)
  simpa [centralResonantHigherBranchBlockConstant] using hmajor

/-- Complete central neighboring estimate at the resonant exponent. -/
theorem central_neighboring_resonantKernel_block_bound
    {N : ℕ} (hM : 600 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hcentral : CentralLatitudePair N j k)
    (hcomp : ComparableLatitudeScales N j k)
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1) :
    |bandPairError N j k (latitudeKernel 1)| ≤
      comparableLatitudeBlockMajorant 1
        centralResonantNeighboringBlockConstant N j k := by
  have hModel := central_neighboring_resonantModel_block_bound
    hM hcentral hcomp hneigh
  have hHigher := central_neighboring_resonantHigherBranch_block_bound
    hM hcentral hcomp hneigh
  have hA : ContinuousOn
      (fun p : ℝ × ℝ ↦ neighboringResonantModelKernel p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
    intro p hp
    have hc := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hp.1 hp.2
    have hS : ContinuousWithinAt
        (fun q : ℝ × ℝ ↦
          neighboringAffineSmoothKernel 1
            reducedCuspResonantConstantCoefficient
            reducedCuspResonantLinearCoefficient q.1 q.2)
        (Icc (bandBoundaryHeight N (j + 1))
            (bandBoundaryHeight N j) ×ˢ
          Icc (bandBoundaryHeight N (k + 1))
            (bandBoundaryHeight N k)) p :=
      (continuousAt_neighboringAffineSmoothKernel_joint
        (α := (1 : ℝ))
        (H := reducedCuspResonantConstantCoefficient)
        (L := reducedCuspResonantLinearCoefficient)
        hc.1 hc.2.1).continuousWithinAt
    have hP :=
      (continuousOn_neighboringResonantPrincipalKernel_centralRectangle
        hM hcentral hcomp hneigh) p hp
    apply (hS.add hP).congr
    · intro q hq
      have hqc := centralComparable_neighboring_rectangle_chart
        hM hcentral hcomp hneigh hq.1 hq.2
      rw [neighboringResonantModelKernel_eq_smooth_add_log
        hqc.1 hqc.2.1]
      rfl
    ·
        rw [neighboringResonantModelKernel_eq_smooth_add_log
          hc.1 hc.2.1]
        rfl
  have hdecomp :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          latitudeKernel 1 s t =
            neighboringResonantModelKernel s t +
              neighboringResonantHigherBranchKernel s t := by
    intro s hs t ht
    have hc := centralComparable_neighboring_rectangle_chart
      hM hcentral hcomp hneigh hs ht
    exact
      latitudeKernel_one_eq_neighboringResonantModel_add_branch_on_unitChart
        hc.1 hc.2.1 hc.2.2
  have heq :=
    bandPairError_eq_add_of_continuous_decomposition_on_literalRectangle
      j k (latitudeKernel 1) neighboringResonantModelKernel
      neighboringResonantHigherBranchKernel
      (continuous_latitudeKernel (by norm_num)) hA hdecomp
  rw [heq]
  calc
    |bandPairError N j k neighboringResonantModelKernel +
        bandPairError N j k neighboringResonantHigherBranchKernel| ≤
      |bandPairError N j k neighboringResonantModelKernel| +
        |bandPairError N j k neighboringResonantHigherBranchKernel| :=
      abs_add _ _
    _ ≤ comparableLatitudeBlockMajorant 1
          centralResonantModelBlockConstant N j k +
        comparableLatitudeBlockMajorant 1
          centralResonantHigherBranchBlockConstant N j k :=
      add_le_add hModel hHigher
    _ = comparableLatitudeBlockMajorant 1
        centralResonantNeighboringBlockConstant N j k := by
      unfold comparableLatitudeBlockMajorant
        centralResonantNeighboringBlockConstant
      ring

noncomputable def centralResonantSeparatedDssttConstant : ℝ :=
  comparableDerivativeScaleConversionConstant 1 *
    latitudeComparableMixedConstant 1

noncomputable def centralResonantComparableBlockConstant : ℝ :=
  centralResonantNeighboringBlockConstant +
    (15 : ℝ) ^ 6 / 2 * centralResonantSeparatedDssttConstant

theorem centralResonantSeparatedDssttConstant_nonneg :
    0 ≤ centralResonantSeparatedDssttConstant := by
  unfold centralResonantSeparatedDssttConstant
    comparableDerivativeScaleConversionConstant
  exact mul_nonneg (by positivity)
    (latitudeComparableMixedConstant_nonneg 1)

theorem centralResonantComparableBlockConstant_nonneg :
    0 ≤ centralResonantComparableBlockConstant := by
  unfold centralResonantComparableBlockConstant
  exact add_nonneg centralResonantNeighboringBlockConstant_nonneg
    (mul_nonneg (by positivity)
      centralResonantSeparatedDssttConstant_nonneg)

/-- Fixed-constant closure of every central comparable latitude rectangle
at the resonant exponent `α = 1`. -/
theorem hasCentralComparableLatitudeBlockBound_resonant
    {N : ℕ} (hM : 600 ≤ bandCount N) :
    HasCentralComparableLatitudeBlockBound 1 N
      centralResonantComparableBlockConstant := by
  exact centralComparable_block_bound_of_neighboring_and_analytic
    (by norm_num)
    centralResonantNeighboringBlockConstant_nonneg
    centralResonantSeparatedDssttConstant_nonneg
    (by omega)
    (by
      intro j k hcentral hcomp hneigh
      exact central_neighboring_resonantKernel_block_bound
        hM hcentral hcomp hneigh)
    (by
      simpa [centralResonantSeparatedDssttConstant] using
        hasCentralComparableSeparatedDssttBound_generic
          (α := (1 : ℝ)) (by norm_num) (by norm_num) (by omega))

end BEMOC
