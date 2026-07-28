import BEMOCFormalization.LatitudeNeighboringPointwiseClosure
import BEMOCFormalization.LatitudeScaledResonantBridge
import BEMOCFormalization.LatitudeCentralComparableClosure
import BEMOCFormalization.LatitudeNeighboringResonantBlockArithmetic
import BEMOCFormalization.LatitudeNeighboringSmoothPointwiseClosure
import BEMOCFormalization.LatitudeResonantEndpointClosure

/-!
# Oscillation bounds in the scale-normalized resonant chart

The logarithmic neighboring branch is harmless only after all quantities
have been divided by the common radius floor.  This file records the exact
normalized extraction and the elementary Lipschitz estimate for the
normalized radius.  The latter is the basic input for freezing both
dimensionless coefficients on a neighboring rectangle.
-/

open MeasureTheory Set

namespace BEMOC

set_option maxHeartbeats 800000

/-- Pair-error linearity when all three kernels are only known to be
continuous on the literal rectangle. -/
theorem bandPairError_eq_add_of_continuousOn_decomposition_on_literalRectangle
    {N : ℕ} (j k : Fin (bandTailCount N + 1))
    (K A B : ℝ → ℝ → ℝ)
    (hK : ContinuousOn (fun p : ℝ × ℝ ↦ K p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)))
    (hA : ContinuousOn (fun p : ℝ × ℝ ↦ A p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)))
    (hdecomp :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          K s t = A s t + B s t) :
    bandPairError N j k K =
      bandPairError N j k A + bandPairError N j k B := by
  let S : Set (ℝ × ℝ) :=
    Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j) ×ˢ
      Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)
  let fK : C(S, ℝ) :=
    ⟨fun p ↦ K p.1.1 p.1.2,
      continuousOn_iff_continuous_restrict.mp hK⟩
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq
    (isClosed_Icc.prod isClosed_Icc) fK
  have hGeq : ∀ p ∈ S, G p = K p.1 p.2 := by
    intro p hp
    exact DFunLike.congr_fun hG (⟨p, hp⟩ : S)
  have hcongr :
      bandPairError N j k K =
        bandPairError N j k (fun s t ↦ G (s, t)) := by
    apply bandPairError_congr_on_literalRectangle
    intro s hs t ht
    exact (hGeq (s, t) ⟨hs, ht⟩).symm
  have hsplit :=
    bandPairError_eq_add_of_continuous_decomposition_on_literalRectangle
      j k (fun s t ↦ G (s, t)) A B G.continuous hA (by
        intro s hs t ht
        change G (s, t) = A s t + B s t
        calc
          G (s, t) = K s t := hGeq (s, t) ⟨hs, ht⟩
          _ = A s t + B s t := hdecomp s hs t ht)
  rw [hcongr]
  exact hsplit

/-- The radius is `R⁻¹`-Lipschitz as long as both endpoints have radius at
least `R`.  This algebraic proof avoids choosing an intermediate point. -/
theorem abs_heightRadius_sub_le_div_radius
    {R x y : ℝ} (hR : 0 < R)
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1)
    (hxfloor : R ≤ heightRadius x)
    (hyfloor : R ≤ heightRadius y) :
    |heightRadius x - heightRadius y| ≤ |x - y| / R := by
  have hx' : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hy' : y ∈ Icc (-1 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
  have hrx : 0 < heightRadius x := hR.trans_le hxfloor
  have hry : 0 < heightRadius y := hR.trans_le hyfloor
  have hsum : 2 * R ≤ heightRadius x + heightRadius y := by linarith
  have hxy : |x + y| ≤ 2 := by
    calc
      |x + y| ≤ |x| + |y| := abs_add _ _
      _ ≤ 2 := by
        have hxa : |x| ≤ 1 := abs_le.mpr hx'
        have hya : |y| ≤ 1 := abs_le.mpr hy'
        linarith
  have hid :
      |heightRadius x - heightRadius y| *
          (heightRadius x + heightRadius y) =
        |x - y| * |x + y| := by
    calc
      |heightRadius x - heightRadius y| *
          (heightRadius x + heightRadius y) =
        |(heightRadius x - heightRadius y) *
          (heightRadius x + heightRadius y)| := by
            rw [abs_mul, abs_of_pos (add_pos hrx hry)]
      _ = |(y - x) * (x + y)| := by
        congr 1
        calc
          (heightRadius x - heightRadius y) *
              (heightRadius x + heightRadius y) =
            heightRadius x ^ 2 - heightRadius y ^ 2 := by ring
          _ = (1 - x ^ 2) - (1 - y ^ 2) := by
            rw [heightRadius_sq hx', heightRadius_sq hy']
          _ = (y - x) * (x + y) := by ring
      _ = |x - y| * |x + y| := by
        rw [abs_mul, abs_sub_comm y x]
  have hmul :
      |heightRadius x - heightRadius y| * (2 * R) ≤
        |x - y| * 2 := by
    calc
      |heightRadius x - heightRadius y| * (2 * R) ≤
          |heightRadius x - heightRadius y| *
            (heightRadius x + heightRadius y) := by
        gcongr
      _ = |x - y| * |x + y| := hid
      _ ≤ |x - y| * 2 := by gcongr
  apply (le_div_iff₀ hR).2
  nlinarith

/-- After division by `R`, radius oscillation is controlled by the
dimensionless physical displacement `|x-y|/R²`. -/
theorem abs_normalizedHeightRadius_sub_le
    {R x y : ℝ} (hR : 0 < R)
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1)
    (hxfloor : R ≤ heightRadius x)
    (hyfloor : R ≤ heightRadius y) :
    |heightRadius x / R - heightRadius y / R| ≤
      |x - y| / R ^ 2 := by
  rw [← sub_div, abs_div, abs_of_pos hR]
  have h := abs_heightRadius_sub_le_div_radius
    hR hx hy hxfloor hyfloor
  calc
    |heightRadius x - heightRadius y| / R ≤
        (|x - y| / R) / R := by gcongr
    _ = |x - y| / R ^ 2 := by rw [div_div, pow_two]

/-- Exact normalized resonant extraction.  In particular no `log R`
occurs: it has become a frozen quadratic coefficient, which the paired
two-moment rule annihilates. -/
theorem neighboringResonantPrincipal_eq_normalized_extraction
    {R s t : ℝ} (hR : 0 < R)
    (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    latitudeAngularScale s t ^ (1 / 2 : ℝ) *
        (reducedCuspResonantPrincipalCoefficient *
          normalizedLatitudeGap s t *
            Real.log (normalizedLatitudeGap s t)) =
      R * reducedCuspResonantPrincipalCoefficient *
        (2 *
          (neighboringNormalizedAngularCoefficient R s t *
            neighboringNormalizedQuadraticCoefficient R s t) *
          resonantLatitudeBranch ((s - t) / R ^ 2) +
        (neighboringNormalizedAngularCoefficient R s t *
          neighboringNormalizedQuadraticCoefficient R s t *
          Real.log
            (neighboringNormalizedQuadraticCoefficient R s t)) *
          ((s - t) / R ^ 2) ^ 2) := by
  let c := latitudeQuadraticGapCoefficient s t
  let ct := neighboringNormalizedQuadraticCoefficient R s t
  let pt := neighboringNormalizedAngularCoefficient R s t
  let z := (s - t) / R ^ 2
  have hc : 0 < c := latitudeQuadraticGapCoefficient_pos hs ht
  have hct : 0 < ct := by
    dsimp [ct, neighboringNormalizedQuadraticCoefficient]
    exact mul_pos (pow_pos hR 4) hc
  have hp : 0 < latitudeAngularScale s t := by
    unfold latitudeAngularScale
    exact mul_pos (mul_pos (by norm_num) (heightRadius_pos hs))
      (heightRadius_pos ht)
  have hsqrt :
      latitudeAngularScale s t ^ (1 / 2 : ℝ) = R * pt := by
    dsimp [pt, neighboringNormalizedAngularCoefficient]
    field_simp [hR.ne']
  have hq :
      normalizedLatitudeGap s t = ct * z ^ 2 := by
    rw [normalizedLatitudeGap_eq_quadraticCoefficient_mul_sq hs ht]
    dsimp [ct, z, neighboringNormalizedQuadraticCoefficient, c]
    field_simp [hR.ne']
    ring
  have hres := quadraticReducedResonantBranch_eq
    (c := ct) (w := z) hct
  unfold quadraticReducedResonantBranch at hres
  rw [hq, hsqrt]
  calc
    R * pt *
        (reducedCuspResonantPrincipalCoefficient * (ct * z ^ 2) *
          Real.log (ct * z ^ 2)) =
      R * pt * reducedCuspResonantPrincipalCoefficient *
        ((ct * z ^ 2) * Real.log (ct * z ^ 2)) := by ring
    _ = R * pt * reducedCuspResonantPrincipalCoefficient *
        (ct * Real.log ct * z ^ 2 +
          2 * ct * resonantLatitudeBranch z) := by rw [hres]
    _ = R * reducedCuspResonantPrincipalCoefficient *
        (2 * (pt * ct) * resonantLatitudeBranch z +
          (pt * ct * Real.log ct) * z ^ 2) := by ring

/-- The dimensionless neighboring length. -/
noncomputable def neighboringNormalizedLength
    (N : ℕ) (j k : Fin (bandTailCount N + 1)) : ℝ :=
  neighboringBandLength N j k /
    comparableLatitudeRadiusFloor N j ^ 2

theorem neighboringComparable_normalizedLength_pos
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1)) :
    0 < neighboringNormalizedLength N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  unfold neighboringNormalizedLength
  have hMr : (0 : ℝ) < bandCount N := by
    exact_mod_cast (show 0 < bandCount N by omega)
  have hdr : (0 : ℝ) < latitudeBandScale N j := by
    exact_mod_cast latitudeBandScale_pos N j
  exact div_pos (neighboringBandLength_pos hN hM j k)
    (sq_pos_of_pos (by
      unfold comparableLatitudeRadiusFloor
      positivity))

/-- Large depth is exactly what makes the normalized neighboring rectangle
a unit rectangle: `δ = a/R² ≤ 1`. -/
theorem neighboringComparable_normalizedLength_le_one
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j) :
    neighboringNormalizedLength N j k ≤ 1 := by
  have hlen := neighboringComparable_bandLength_le_scale
    (by omega : 1 ≤ bandCount N) hjk
  let d : ℝ := latitudeBandScale N j
  let M : ℝ := bandCount N
  have hd : 600 ≤ d := by
    dsimp [d]
    exact_mod_cast hdepth
  have hd0 : 0 ≤ d := by linarith
  have hMpos : 0 < M := by dsimp [M]; positivity
  unfold neighboringNormalizedLength comparableLatitudeRadiusFloor
  dsimp [d, M] at hd hlen ⊢
  apply (div_le_one (by positivity :
    0 < ((latitudeBandScale N j : ℝ) /
      (10 * (bandCount N : ℝ))) ^ 2)).2
  calc
    neighboringBandLength N j k ≤
        6 * (latitudeBandScale N j : ℝ) /
          (bandCount N : ℝ) ^ 2 := hlen
    _ ≤ ((latitudeBandScale N j : ℝ) /
          (10 * (bandCount N : ℝ))) ^ 2 := by
      rw [div_pow]
      have hnum : 6 * d ≤ d ^ 2 / 100 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 100)).2
        nlinarith
      calc
        6 * (latitudeBandScale N j : ℝ) /
            (bandCount N : ℝ) ^ 2 =
          (6 * d) / M ^ 2 := by rfl
        _ ≤ (d ^ 2 / 100) / M ^ 2 := by gcongr
        _ = (latitudeBandScale N j : ℝ) ^ 2 /
            (10 * (bandCount N : ℝ)) ^ 2 := by
          dsimp [d, M]
          ring

/-- Any two first-coordinate samples in the same neighboring rectangle
have normalized-radius oscillation at most `δ`; likewise for the second
coordinate. -/
theorem neighboringComparable_normalizedRadius_oscillation
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |heightRadius s / comparableLatitudeRadiusFloor N j -
        heightRadius u / comparableLatitudeRadiusFloor N j| ≤
        neighboringNormalizedLength N j k ∧
      |heightRadius t / comparableLatitudeRadiusFloor N j -
        heightRadius v / comparableLatitudeRadiusFloor N j| ≤
        neighboringNormalizedLength N j k := by
  let R := comparableLatitudeRadiusFloor N j
  have hsChart :=
    neighboringComparable_largeDepth_rectangle_chart
      (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
  have huChart :=
    neighboringComparable_largeDepth_rectangle_chart
      (by omega : 1 ≤ bandCount N) hjk hdepth hu hv
  have hsvChart :=
    neighboringComparable_largeDepth_rectangle_chart
      (by omega : 1 ≤ bandCount N) hjk hdepth hs hv
  have hutChart :=
    neighboringComparable_largeDepth_rectangle_chart
      (by omega : 1 ≤ bandCount N) hjk hdepth hu ht
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    positivity
  have hfs := (comparableSame_rectangle_geometry
    (by omega : 1 ≤ bandCount N) hjk.1 hs ht).1.1
  have hfu := (comparableSame_rectangle_geometry
    (by omega : 1 ≤ bandCount N) hjk.1 hu hv).1.1
  have hft := (comparableSame_rectangle_geometry
    (by omega : 1 ≤ bandCount N) hjk.1 hs ht).1.2
  have hfv := (comparableSame_rectangle_geometry
    (by omega : 1 ≤ bandCount N) hjk.1 hu hv).1.2
  have hsu : |s - u| ≤ neighboringBandLength N j k := by
    have hwidth : |s - u| ≤ bandWidth N j := by
      rw [abs_le]
      unfold bandWidth
      constructor <;> linarith [hs.1, hs.2, hu.1, hu.2]
    unfold neighboringBandLength
    linarith [bandWidth_nonneg (N := N) k]
  have htv : |t - v| ≤ neighboringBandLength N j k := by
    have hwidth : |t - v| ≤ bandWidth N k := by
      rw [abs_le]
      unfold bandWidth
      constructor <;> linarith [ht.1, ht.2, hv.1, hv.2]
    unfold neighboringBandLength
    linarith [bandWidth_nonneg (N := N) j]
  constructor
  · exact (abs_normalizedHeightRadius_sub_le hR
      hsChart.1 huChart.1
      (by simpa [R, comparableLatitudeRadiusFloor] using hfs)
      (by simpa [R, comparableLatitudeRadiusFloor] using hfu)).trans
      (by
        unfold neighboringNormalizedLength
        gcongr)
  · exact (abs_normalizedHeightRadius_sub_le hR
      hsChart.2.1 huChart.2.1
      (by simpa [R, comparableLatitudeRadiusFloor] using hft)
      (by simpa [R, comparableLatitudeRadiusFloor] using hfv)).trans
      (by
        unfold neighboringNormalizedLength
        gcongr)

/-- Purely algebraic coefficient-freezing lemma.  The deliberately round
constant keeps all later geometric substitutions transparent. -/
theorem abs_inverse_normalizedGapDenominator_sub_le
    {a b c d q r δ : ℝ}
    (hδ : 0 ≤ δ)
    (ha0 : 1 ≤ a) (hb0 : 1 ≤ b) (hc0 : 1 ≤ c) (hd0 : 1 ≤ d)
    (ha1 : a ≤ 40) (hb1 : b ≤ 40)
    (hc1 : c ≤ 40) (hd1 : d ≤ 40)
    (hac : |a - c| ≤ δ) (hbd : |b - d| ≤ δ)
    (hq0 : 0 ≤ q) (hr0 : 0 ≤ r)
    (hq1 : q ≤ 1) (hr1 : r ≤ 1)
    (hqr : |q - r| ≤ δ) :
    |(((a * b) ^ 2 * (q + 2))⁻¹) -
        (((c * d) ^ 2 * (r + 2))⁻¹)| ≤
      4000000 * δ := by
  let A := (a * b) ^ 2 * (q + 2)
  let B := (c * d) ^ 2 * (r + 2)
  have hab0 : 0 ≤ a * b := mul_nonneg (by linarith) (by linarith)
  have hcd0 : 0 ≤ c * d := mul_nonneg (by linarith) (by linarith)
  have hab1 : a * b ≤ 1600 := by nlinarith
  have hcd1 : c * d ≤ 1600 := by nlinarith
  have hprod :
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
  have hsq :
      |(a * b) ^ 2 - (c * d) ^ 2| ≤ 256000 * δ := by
    rw [show (a * b) ^ 2 - (c * d) ^ 2 =
      (a * b - c * d) * (a * b + c * d) by ring, abs_mul]
    calc
      |a * b - c * d| * |a * b + c * d| ≤
          (80 * δ) * 3200 := by
        gcongr
        rw [abs_of_nonneg (add_nonneg hab0 hcd0)]
        linarith
      _ = 256000 * δ := by ring
  have hAB :
      |A - B| ≤ 3328000 * δ := by
    dsimp [A, B]
    rw [show
      (a * b) ^ 2 * (q + 2) - (c * d) ^ 2 * (r + 2) =
        ((a * b) ^ 2 - (c * d) ^ 2) * (q + 2) +
          (c * d) ^ 2 * (q - r) by ring]
    calc
      |_ + _| ≤
          |((a * b) ^ 2 - (c * d) ^ 2) * (q + 2)| +
            |(c * d) ^ 2 * (q - r)| := abs_add _ _
      _ = |(a * b) ^ 2 - (c * d) ^ 2| * |q + 2| +
          |(c * d) ^ 2| * |q - r| := by rw [abs_mul, abs_mul]
      _ ≤ (256000 * δ) * 3 + 2560000 * δ := by
        rw [abs_of_nonneg (by linarith : 0 ≤ q + 2),
          abs_of_nonneg (sq_nonneg (c * d))]
        have hcdsq : (c * d) ^ 2 ≤ 2560000 := by nlinarith
        have hq3 : q + 2 ≤ 3 := by linarith
        exact add_le_add
          (mul_le_mul hsq hq3 (by linarith) (by positivity))
          (mul_le_mul hcdsq hqr (abs_nonneg _) (by positivity))
      _ = 3328000 * δ := by ring
  have hA : 2 ≤ A := by
    dsimp [A]
    have : 1 ≤ a * b := by nlinarith
    nlinarith [sq_nonneg (a * b - 1)]
  have hB : 2 ≤ B := by
    dsimp [B]
    have : 1 ≤ c * d := by nlinarith
    nlinarith [sq_nonneg (c * d - 1)]
  have hABpos : 0 < A * B := mul_pos (by linarith) (by linarith)
  rw [show A⁻¹ - B⁻¹ = (B - A) / (A * B) by
    field_simp [ne_of_gt (by linarith : 0 < A),
      ne_of_gt (by linarith : 0 < B)]]
  rw [abs_div, abs_mul, abs_of_pos (by linarith : 0 < A),
    abs_of_pos (by linarith : 0 < B), abs_sub_comm B A]
  apply (div_le_iff₀ hABpos).2
  have hden : 4 ≤ A * B := by nlinarith
  have hcoarse : |A - B| ≤ 4000000 * δ := by
    exact hAB.trans (by nlinarith)
  exact hcoarse.trans
    (le_mul_of_one_le_right (by positivity) (by linarith))

/-- The normalized gap itself oscillates by at most `δ`; in fact the proof
gives the stronger `δ²/2` bound at each endpoint. -/
theorem neighboringComparable_normalizedGap_oscillation
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
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
      neighboringNormalizedLength N j k := by
  let R := comparableLatitudeRadiusFloor N j
  let a := neighboringBandLength N j k
  let δ := neighboringNormalizedLength N j k
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    positivity
  have ha : 0 < a := by
    dsimp [a]
    exact neighboringBandLength_pos
      (by
        have hfour := four_mul_bandCount_sq_le N
        have : 0 < 4 * bandCount N ^ 2 := by positivity
        omega)
      hM j k
  have hδ0 : 0 ≤ δ := by dsimp [δ, neighboringNormalizedLength]; positivity
  have hδ1 : δ ≤ 1 := by
    simpa [δ] using
      neighboringComparable_normalizedLength_le_one hM hjk hdepth
  have hst := abs_sub_le_neighboringBandLength j k hjk.2 hs ht
  have huv := abs_sub_le_neighboringBandLength j k hjk.2 hu hv
  have hqst := neighboringComparable_normalizedGap_le_physicalSq
    (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
  have hquv := neighboringComparable_normalizedGap_le_physicalSq
    (by omega : 1 ≤ bandCount N) hjk hdepth hu hv
  have hstSq : (s - t) ^ 2 ≤ a ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [a] using hst) 2
  have huvSq : (u - v) ^ 2 ≤ a ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [a] using huv) 2
  have hqst' : normalizedLatitudeGap s t ≤ δ ^ 2 / 2 := by
    calc
      normalizedLatitudeGap s t ≤ (s - t) ^ 2 / (2 * R ^ 4) := by
        simpa [R] using hqst
      _ ≤ a ^ 2 / (2 * R ^ 4) := by gcongr
      _ = δ ^ 2 / 2 := by
        dsimp [δ, neighboringNormalizedLength, a]
        field_simp [hR.ne']
        ring
  have hquv' : normalizedLatitudeGap u v ≤ δ ^ 2 / 2 := by
    calc
      normalizedLatitudeGap u v ≤ (u - v) ^ 2 / (2 * R ^ 4) := by
        simpa [R] using hquv
      _ ≤ a ^ 2 / (2 * R ^ 4) := by gcongr
      _ = δ ^ 2 / 2 := by
        dsimp [δ, neighboringNormalizedLength, a]
        field_simp [hR.ne']
        ring
  have hcharts := neighboringComparable_largeDepth_rectangle_chart
    (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
  have hchartu := neighboringComparable_largeDepth_rectangle_chart
    (by omega : 1 ≤ bandCount N) hjk hdepth hu hv
  have hδsq : δ ^ 2 ≤ δ := by
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hδ1)]
  rw [abs_le]
  constructor <;>
    nlinarith

/-- Algebraic normal form of `c̃`: it is the reciprocal of a denominator
built only from the two normalized radii and the normalized gap. -/
theorem neighboringNormalizedQuadraticCoefficient_eq_inverse
    {R s t : ℝ} (hR : 0 < R) :
    neighboringNormalizedQuadraticCoefficient R s t =
      (((heightRadius s / R) * (heightRadius t / R)) ^ 2 *
        (normalizedLatitudeGap s t + 2))⁻¹ := by
  unfold neighboringNormalizedQuadraticCoefficient
    latitudeQuadraticGapCoefficient
  field_simp [hR.ne']
  ring

/-- Uniform `O(δ)` freezing estimate for `c̃ = R⁴c` on every large-depth
neighboring rectangle. -/
theorem neighboringComparable_normalizedQuadraticCoefficient_oscillation
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
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
          (comparableLatitudeRadiusFloor N j) s t -
        neighboringNormalizedQuadraticCoefficient
          (comparableLatitudeRadiusFloor N j) u v| ≤
      4000000 * neighboringNormalizedLength N j k := by
  let R := comparableLatitudeRadiusFloor N j
  let δ := neighboringNormalizedLength N j k
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    positivity
  have hδ : 0 ≤ δ := by
    dsimp [δ, neighboringNormalizedLength, neighboringBandLength]
    exact div_nonneg
      (add_nonneg (bandWidth_nonneg (N := N) j)
        (bandWidth_nonneg (N := N) k))
      (sq_nonneg _)
  have hstChart := neighboringComparable_largeDepth_rectangle_chart
    (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
  have huvChart := neighboringComparable_largeDepth_rectangle_chart
    (by omega : 1 ≤ bandCount N) hjk hdepth hu hv
  have hfst := (comparableSame_rectangle_geometry
    (by omega : 1 ≤ bandCount N) hjk.1 hs ht).1
  have hfuv := (comparableSame_rectangle_geometry
    (by omega : 1 ≤ bandCount N) hjk.1 hu hv).1
  have hcst := comparableSame_rectangle_common_radius_ceiling
    (by omega : 1 ≤ bandCount N) hjk.1 hs ht
  have hcuv := comparableSame_rectangle_common_radius_ceiling
    (by omega : 1 ≤ bandCount N) hjk.1 hu hv
  have radiusBounds {x : ℝ}
      (hfloor : R ≤ heightRadius x)
      (hceil : heightRadius x ≤ 40 * R) :
      1 ≤ heightRadius x / R ∧ heightRadius x / R ≤ 40 := by
    constructor
    · exact (le_div_iff₀ hR).2 (by simpa using hfloor)
    · exact (div_le_iff₀ hR).2 (by simpa using hceil)
  have hsB := radiusBounds
    (by simpa [R, comparableLatitudeRadiusFloor] using hfst.1)
    (by simpa [R, comparableLatitudeRadiusFloor] using hcst.1)
  have htB := radiusBounds
    (by simpa [R, comparableLatitudeRadiusFloor] using hfst.2)
    (by simpa [R, comparableLatitudeRadiusFloor] using hcst.2)
  have huB := radiusBounds
    (by simpa [R, comparableLatitudeRadiusFloor] using hfuv.1)
    (by simpa [R, comparableLatitudeRadiusFloor] using hcuv.1)
  have hvB := radiusBounds
    (by simpa [R, comparableLatitudeRadiusFloor] using hfuv.2)
    (by simpa [R, comparableLatitudeRadiusFloor] using hcuv.2)
  have hrad := neighboringComparable_normalizedRadius_oscillation
    hM hjk hdepth hs hu ht hv
  have hgap := neighboringComparable_normalizedGap_oscillation
    hM hjk hdepth hs hu ht hv
  have hraw := abs_inverse_normalizedGapDenominator_sub_le
    hδ hsB.1 htB.1 huB.1 hvB.1
    hsB.2 htB.2 huB.2 hvB.2
    (by simpa [R, δ] using hrad.1)
    (by simpa [R, δ] using hrad.2)
    hstChart.2.2.1 huvChart.2.2.1
    hstChart.2.2.2 huvChart.2.2.2
    (by simpa [δ] using hgap)
  rw [neighboringNormalizedQuadraticCoefficient_eq_inverse hR,
    neighboringNormalizedQuadraticCoefficient_eq_inverse hR]
  simpa [R, δ] using hraw

/-- Square of the normalized angular coefficient. -/
theorem neighboringNormalizedAngularCoefficient_sq
    {R s t : ℝ} (hR : 0 < R)
    (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    neighboringNormalizedAngularCoefficient R s t ^ 2 =
      2 * (heightRadius s / R) * (heightRadius t / R) := by
  have hp : 0 ≤ latitudeAngularScale s t := by
    unfold latitudeAngularScale
    positivity
  calc
    neighboringNormalizedAngularCoefficient R s t ^ 2 =
        (latitudeAngularScale s t ^ (1 / 2 : ℝ)) ^ 2 / R ^ 2 := by
      unfold neighboringNormalizedAngularCoefficient
      rw [div_pow]
    _ = latitudeAngularScale s t / R ^ 2 := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hp]
    _ = 2 * (heightRadius s / R) * (heightRadius t / R) := by
      change (2 * heightRadius s * heightRadius t) / R ^ 2 =
        2 * (heightRadius s / R) * (heightRadius t / R)
      field_simp only [hR.ne', pow_ne_zero]
      ring

private theorem abs_sqrtProductParameter_sub_le
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

/-- Uniform `O(δ)` freezing estimate for `p̃ = p^(1/2)/R`. -/
theorem neighboringComparable_normalizedAngularCoefficient_oscillation
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringNormalizedAngularCoefficient
          (comparableLatitudeRadiusFloor N j) s t -
        neighboringNormalizedAngularCoefficient
          (comparableLatitudeRadiusFloor N j) u v| ≤
      80 * neighboringNormalizedLength N j k := by
  let R := comparableLatitudeRadiusFloor N j
  let δ := neighboringNormalizedLength N j k
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    positivity
  have hδ : 0 ≤ δ := by
    dsimp [δ, neighboringNormalizedLength, neighboringBandLength]
    exact div_nonneg
      (add_nonneg (bandWidth_nonneg (N := N) j)
        (bandWidth_nonneg (N := N) k)) (sq_nonneg _)
  have hstChart := neighboringComparable_largeDepth_rectangle_chart
    (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
  have huvChart := neighboringComparable_largeDepth_rectangle_chart
    (by omega : 1 ≤ bandCount N) hjk hdepth hu hv
  have hfst := (comparableSame_rectangle_geometry
    (by omega : 1 ≤ bandCount N) hjk.1 hs ht).1
  have hfuv := (comparableSame_rectangle_geometry
    (by omega : 1 ≤ bandCount N) hjk.1 hu hv).1
  have hcst := comparableSame_rectangle_common_radius_ceiling
    (by omega : 1 ≤ bandCount N) hjk.1 hs ht
  have hcuv := comparableSame_rectangle_common_radius_ceiling
    (by omega : 1 ≤ bandCount N) hjk.1 hu hv
  have hrad := neighboringComparable_normalizedRadius_oscillation
    hM hjk hdepth hs hu ht hv
  apply abs_sqrtProductParameter_sub_le hδ
  · exact (le_div_iff₀ hR).2 (by simpa [R] using hfst.1)
  · exact (le_div_iff₀ hR).2 (by simpa [R] using hfst.2)
  · exact (le_div_iff₀ hR).2 (by simpa [R] using hfuv.1)
  · exact (le_div_iff₀ hR).2 (by simpa [R] using hfuv.2)
  · exact (div_le_iff₀ hR).2 (by simpa [R] using hcst.2)
  · exact (div_le_iff₀ hR).2 (by simpa [R] using hcuv.1)
  · simpa [R, δ] using hrad.1
  · simpa [R, δ] using hrad.2
  · exact (neighboringComparable_normalized_resonant_coefficients_bounded
      (by omega : 1 ≤ bandCount N) hjk hdepth hs ht).2.2.1.le
  · exact (neighboringComparable_normalized_resonant_coefficients_bounded
      (by omega : 1 ≤ bandCount N) hjk hdepth hu hv).2.2.1.le
  · simpa [R] using neighboringNormalizedAngularCoefficient_sq
      hR hstChart.1 hstChart.2.1
  · simpa [R] using neighboringNormalizedAngularCoefficient_sq
      hR huvChart.1 huvChart.2.1

/-- Uniform lower bound keeping the normalized logarithmic coefficient
away from zero. -/
theorem neighboringComparable_normalizedQuadraticCoefficient_lower
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    (1 : ℝ) / 7680000 ≤
      neighboringNormalizedQuadraticCoefficient
        (comparableLatitudeRadiusFloor N j) s t := by
  let R := comparableLatitudeRadiusFloor N j
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    positivity
  have hchart := neighboringComparable_largeDepth_rectangle_chart
    (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
  have hfloor := (comparableSame_rectangle_geometry
    (by omega : 1 ≤ bandCount N) hjk.1 hs ht).1
  have hceil := comparableSame_rectangle_common_radius_ceiling
    (by omega : 1 ≤ bandCount N) hjk.1 hs ht
  let a := heightRadius s / R
  let b := heightRadius t / R
  have ha1 : 1 ≤ a :=
    (le_div_iff₀ hR).2 (by simpa [R] using hfloor.1)
  have hb1 : 1 ≤ b :=
    (le_div_iff₀ hR).2 (by simpa [R] using hfloor.2)
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have ha : a ≤ 40 := (div_le_iff₀ hR).2 (by simpa [R] using hceil.1)
  have hb : b ≤ 40 := (div_le_iff₀ hR).2 (by simpa [R] using hceil.2)
  have hab : a * b ≤ 1600 := by nlinarith
  have hden :
      (a * b) ^ 2 * (normalizedLatitudeGap s t + 2) ≤ 7680000 := by
    have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
    have habsq : (a * b) ^ 2 ≤ 2560000 := by
      nlinarith [mul_nonneg hab0 (sub_nonneg.mpr hab)]
    have hgap0 : 0 ≤ normalizedLatitudeGap s t + 2 := by
      linarith [hchart.2.2.1]
    have hgap3 : normalizedLatitudeGap s t + 2 ≤ 3 := by
      linarith [hchart.2.2.2]
    calc
      (a * b) ^ 2 * (normalizedLatitudeGap s t + 2) ≤
          2560000 * 3 :=
        mul_le_mul habsq hgap3 hgap0 (by positivity)
      _ = 7680000 := by norm_num
  have hdenpos :
      0 < (a * b) ^ 2 * (normalizedLatitudeGap s t + 2) := by
    have habpos : 0 < a * b := mul_pos (by linarith) (by linarith)
    exact mul_pos (sq_pos_of_pos habpos) (by linarith [hchart.2.2.1])
  rw [neighboringNormalizedQuadraticCoefficient_eq_inverse hR]
  change (1 : ℝ) / 7680000 ≤
    ((a * b) ^ 2 * (normalizedLatitudeGap s t + 2))⁻¹
  rw [one_div]
  exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 7680000) hdenpos).2 hden

/-- Logarithm is Lipschitz on a positive half-line. -/
theorem abs_log_sub_le_div_of_lower
    {m x y : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / m := by
  have hx0 : 0 < x := hm.trans_le hx
  have hy0 : 0 < y := hm.trans_le hy
  rcases le_total y x with hyx | hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr
      (Real.strictMonoOn_log.monotoneOn hy0 hx0 hyx))]
    rw [← Real.log_div hx0.ne' hy0.ne']
    calc
      Real.log (x / y) ≤ x / y - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
      _ = (x - y) / y := by field_simp [hy0.ne']
      _ ≤ (x - y) / m := by
        exact div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hm hy
      _ = |x - y| / m := by rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
  · rw [abs_of_nonpos (sub_nonpos.mpr
      (Real.strictMonoOn_log.monotoneOn hx0 hy0 hxy))]
    rw [neg_sub]
    rw [← Real.log_div hy0.ne' hx0.ne']
    calc
      Real.log (y / x) ≤ y / x - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
      _ = (y - x) / x := by field_simp [hx0.ne']
      _ ≤ (y - x) / m := by
        exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hm hx
      _ = |x - y| / m := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
        ring

noncomputable def neighboringResonantAmplitude
    (R s t : ℝ) : ℝ :=
  neighboringNormalizedAngularCoefficient R s t *
    neighboringNormalizedQuadraticCoefficient R s t

noncomputable def neighboringResonantLogAmplitude
    (R s t : ℝ) : ℝ :=
  neighboringResonantAmplitude R s t *
    Real.log (neighboringNormalizedQuadraticCoefficient R s t)

def neighboringResonantAmplitudeOscillationConstant : ℝ :=
  12800000040

def neighboringResonantLogAmplitudeOscillationConstant : ℝ :=
  100000000000000000000

def neighboringResonantLogOscillationConstant : ℝ :=
  30720000000000

/-- A fixed linear majorant for the resonant unit profile. -/
noncomputable def resonantUnitLinearConstant : ℝ :=
  Classical.choose
    (exists_resonantLatitudeBranch_linear_bound 1 (by norm_num))

theorem resonantUnitLinearConstant_nonneg :
    0 ≤ resonantUnitLinearConstant :=
  (Classical.choose_spec
    (exists_resonantLatitudeBranch_linear_bound 1 (by norm_num))).1

theorem abs_resonantLatitudeBranch_le_unitLinearConstant
    {z : ℝ} (hz : |z| ≤ 1) :
    |resonantLatitudeBranch z| ≤ resonantUnitLinearConstant * |z| :=
  (Classical.choose_spec
    (exists_resonantLatitudeBranch_linear_bound 1 (by norm_num))).2 z hz

/-- Classifier-free algebraic freezing estimate.  This is intentionally
stated independently of the band geometry, so the same step can be reused
for central rectangles after their own coefficient oscillation bounds are
available. -/
theorem abs_resonantPrincipal_freezing_remainder_le
    {A A₀ B B₀ z δ LA LB L : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hLA : 0 ≤ LA) (hLB : 0 ≤ LB) (hL : 0 ≤ L)
    (hA : |A - A₀| ≤ LA * δ)
    (hB : |B - B₀| ≤ LB * δ)
    (hz : |z| ≤ δ)
    (hr : |resonantLatitudeBranch z| ≤ L * |z|) :
    |(2 * A * resonantLatitudeBranch z + B * z ^ 2) -
        (2 * A₀ * resonantLatitudeBranch z + B₀ * z ^ 2)| ≤
      (2 * LA * L + LB) * δ ^ 2 := by
  have hz2 : |z| ^ 2 ≤ δ ^ 2 := by
    exact (sq_le_sq₀ (abs_nonneg z) hδ0).2 hz
  have hδsq : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hBterm :
      (LB * δ) * δ ^ 2 ≤ LB * δ ^ 2 := by
    calc
      (LB * δ) * δ ^ 2 = (LB * δ ^ 2) * δ := by ring
      _ ≤ (LB * δ ^ 2) * 1 := by gcongr
      _ = LB * δ ^ 2 := by ring
  rw [show
    (2 * A * resonantLatitudeBranch z + B * z ^ 2) -
        (2 * A₀ * resonantLatitudeBranch z + B₀ * z ^ 2) =
      2 * (A - A₀) * resonantLatitudeBranch z +
        (B - B₀) * z ^ 2 by ring]
  calc
    |_ + _| ≤
        |2 * (A - A₀) * resonantLatitudeBranch z| +
          |(B - B₀) * z ^ 2| := abs_add _ _
    _ = 2 * |A - A₀| * |resonantLatitudeBranch z| +
          |B - B₀| * |z| ^ 2 := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow]
      norm_num
    _ ≤ 2 * (LA * δ) * (L * δ) +
          (LB * δ) * δ ^ 2 := by
      exact add_le_add
        (mul_le_mul
          (mul_le_mul_of_nonneg_left hA (by norm_num))
          (hr.trans (mul_le_mul_of_nonneg_left hz hL))
          (abs_nonneg _)
          (mul_nonneg (by norm_num) (mul_nonneg hLA hδ0)))
        (mul_le_mul hB hz2 (sq_nonneg _) (mul_nonneg hLB hδ0))
    _ ≤ (2 * LA * L + LB) * δ ^ 2 := by
      calc
        2 * (LA * δ) * (L * δ) + (LB * δ) * δ ^ 2 ≤
            2 * (LA * δ) * (L * δ) + LB * δ ^ 2 :=
          add_le_add_left hBterm _
        _ = (2 * LA * L + LB) * δ ^ 2 := by ring

/-- The normalized logarithm is uniformly bounded on every large-depth
neighboring rectangle.  The intentionally coarse rational bound avoids
putting a transcendental constant into the final majorant. -/
theorem neighboringComparable_logQuadraticCoefficient_abs_le
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |Real.log (neighboringNormalizedQuadraticCoefficient
      (comparableLatitudeRadiusFloor N j) s t)| ≤ 7680000 := by
  let c := neighboringNormalizedQuadraticCoefficient
    (comparableLatitudeRadiusFloor N j) s t
  have hc := neighboringComparable_normalized_resonant_coefficients_bounded
    (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
  have hclower :=
    neighboringComparable_normalizedQuadraticCoefficient_lower
      hM hjk hdepth hs ht
  have hcinv : c⁻¹ ≤ 7680000 := by
    have hm : (0 : ℝ) < 1 / 7680000 := by norm_num
    have hi : c⁻¹ ≤ ((1 : ℝ) / 7680000)⁻¹ :=
      (inv_le_inv₀ hc.1 hm).2 (by simpa [c] using hclower)
    norm_num at hi ⊢
    exact hi
  have hlogInv :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr (by simpa [c] using hc.1))
  rw [Real.log_inv] at hlogInv
  have hlogLower : -7680000 ≤ Real.log c := by linarith
  have hlogUpper : Real.log c ≤ 0 :=
    Real.log_nonpos (by simpa [c] using hc.1.le)
      (by simpa [c] using (hc.2.1.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)))
  rw [abs_of_nonpos hlogUpper]
  linarith

/-- The logarithm of `c̃` also freezes at `O(δ)`. -/
theorem neighboringComparable_logQuadraticCoefficient_oscillation
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
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
          (comparableLatitudeRadiusFloor N j) s t) -
        Real.log (neighboringNormalizedQuadraticCoefficient
          (comparableLatitudeRadiusFloor N j) u v)| ≤
      neighboringResonantLogOscillationConstant *
        neighboringNormalizedLength N j k := by
  let cs := neighboringNormalizedQuadraticCoefficient
    (comparableLatitudeRadiusFloor N j) s t
  let cu := neighboringNormalizedQuadraticCoefficient
    (comparableLatitudeRadiusFloor N j) u v
  let δ := neighboringNormalizedLength N j k
  have hcs := neighboringComparable_normalizedQuadraticCoefficient_lower
    hM hjk hdepth hs ht
  have hcu := neighboringComparable_normalizedQuadraticCoefficient_lower
    hM hjk hdepth hu hv
  have hc := neighboringComparable_normalizedQuadraticCoefficient_oscillation
    hM hjk hdepth hs hu ht hv
  have hraw := abs_log_sub_le_div_of_lower
    (by norm_num : (0 : ℝ) < 1 / 7680000)
    (by simpa [cs] using hcs) (by simpa [cu] using hcu)
  calc
    |Real.log cs - Real.log cu| ≤ |cs - cu| / ((1 : ℝ) / 7680000) :=
      hraw
    _ ≤ (4000000 * δ) / ((1 : ℝ) / 7680000) := by
      gcongr
    _ = neighboringResonantLogOscillationConstant * δ := by
      unfold neighboringResonantLogOscillationConstant
      ring

/-- Product coefficient `p̃c̃` has uniform `O(δ)` oscillation. -/
theorem neighboringComparable_resonantAmplitude_oscillation
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringResonantAmplitude
          (comparableLatitudeRadiusFloor N j) s t -
        neighboringResonantAmplitude
          (comparableLatitudeRadiusFloor N j) u v| ≤
      neighboringResonantAmplitudeOscillationConstant *
        neighboringNormalizedLength N j k := by
  let R := comparableLatitudeRadiusFloor N j
  let δ := neighboringNormalizedLength N j k
  let ps := neighboringNormalizedAngularCoefficient R s t
  let pu := neighboringNormalizedAngularCoefficient R u v
  let cs := neighboringNormalizedQuadraticCoefficient R s t
  let cu := neighboringNormalizedQuadraticCoefficient R u v
  have hp := neighboringComparable_normalizedAngularCoefficient_oscillation
    hM hjk hdepth hs hu ht hv
  have hc := neighboringComparable_normalizedQuadraticCoefficient_oscillation
    hM hjk hdepth hs hu ht hv
  have hbs := neighboringComparable_normalized_resonant_coefficients_bounded
    (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
  have hbu := neighboringComparable_normalized_resonant_coefficients_bounded
    (by omega : 1 ≤ bandCount N) hjk hdepth hu hv
  have hδ : 0 ≤ δ := by
    exact (neighboringComparable_normalizedLength_pos hM j k).le
  unfold neighboringResonantAmplitude
  rw [show
    neighboringNormalizedAngularCoefficient R s t *
        neighboringNormalizedQuadraticCoefficient R s t -
      neighboringNormalizedAngularCoefficient R u v *
        neighboringNormalizedQuadraticCoefficient R u v =
      (neighboringNormalizedAngularCoefficient R s t -
        neighboringNormalizedAngularCoefficient R u v) *
          neighboringNormalizedQuadraticCoefficient R s t +
      neighboringNormalizedAngularCoefficient R u v *
        (neighboringNormalizedQuadraticCoefficient R s t -
          neighboringNormalizedQuadraticCoefficient R u v) by ring]
  calc
    |_ + _| ≤
        |(neighboringNormalizedAngularCoefficient R s t -
          neighboringNormalizedAngularCoefficient R u v) *
            neighboringNormalizedQuadraticCoefficient R s t| +
        |neighboringNormalizedAngularCoefficient R u v *
          (neighboringNormalizedQuadraticCoefficient R s t -
            neighboringNormalizedQuadraticCoefficient R u v)| := abs_add _ _
    _ ≤ (80 * δ) * ((1 : ℝ) / 2) +
        3200 * (4000000 * δ) := by
      simp only [abs_mul]
      rw [abs_of_pos hbs.1, abs_of_pos hbu.2.2.1]
      exact add_le_add
        (mul_le_mul hp hbs.2.1 hbs.1.le (by nlinarith))
        (mul_le_mul hbu.2.2.2 hc (abs_nonneg _) (by nlinarith))
    _ = neighboringResonantAmplitudeOscillationConstant * δ := by
      unfold neighboringResonantAmplitudeOscillationConstant
      ring

/-- The full logarithmic coefficient `p̃ c̃ log c̃` freezes at `O(δ)`. -/
theorem neighboringComparable_resonantLogAmplitude_oscillation
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s u t v : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringResonantLogAmplitude
          (comparableLatitudeRadiusFloor N j) s t -
        neighboringResonantLogAmplitude
          (comparableLatitudeRadiusFloor N j) u v| ≤
      neighboringResonantLogAmplitudeOscillationConstant *
        neighboringNormalizedLength N j k := by
  let R := comparableLatitudeRadiusFloor N j
  let δ := neighboringNormalizedLength N j k
  let As := neighboringResonantAmplitude R s t
  let Au := neighboringResonantAmplitude R u v
  let cs := neighboringNormalizedQuadraticCoefficient R s t
  let cu := neighboringNormalizedQuadraticCoefficient R u v
  have hδ : 0 ≤ δ :=
    (neighboringComparable_normalizedLength_pos hM j k).le
  have hA := neighboringComparable_resonantAmplitude_oscillation
    hM hjk hdepth hs hu ht hv
  have hlog := neighboringComparable_logQuadraticCoefficient_oscillation
    hM hjk hdepth hs hu ht hv
  have hlogBound :=
    neighboringComparable_logQuadraticCoefficient_abs_le
      hM hjk hdepth hs ht
  have hbu := neighboringComparable_normalized_resonant_coefficients_bounded
    (by omega : 1 ≤ bandCount N) hjk hdepth hu hv
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
        (mul_le_mul hAu (by simpa [R, δ, cs, cu] using hlog)
          (abs_nonneg _) (by positivity))
    _ ≤ neighboringResonantLogAmplitudeOscillationConstant * δ := by
      unfold neighboringResonantAmplitudeOscillationConstant
        neighboringResonantLogOscillationConstant
        neighboringResonantLogAmplitudeOscillationConstant
      nlinarith

noncomputable def neighboringResonantNormalizedPrincipal
    (R s t : ℝ) : ℝ :=
  2 * neighboringResonantAmplitude R s t *
      resonantLatitudeBranch ((s - t) / R ^ 2) +
    neighboringResonantLogAmplitude R s t *
      ((s - t) / R ^ 2) ^ 2

noncomputable def neighboringResonantFrozenNormalizedPrincipal
    (R u v s t : ℝ) : ℝ :=
  2 * neighboringResonantAmplitude R u v *
      resonantLatitudeBranch ((s - t) / R ^ 2) +
    neighboringResonantLogAmplitude R u v *
      ((s - t) / R ^ 2) ^ 2

noncomputable def neighboringResonantFrozenPrincipalProfile
    (R A B s t : ℝ) : ℝ :=
  R * reducedCuspResonantPrincipalCoefficient *
    (2 * A * resonantLatitudeBranch ((s - t) / R ^ 2) +
      B * ((s - t) / R ^ 2) ^ 2)

theorem continuous_neighboringResonantFrozenPrincipalProfile
    (R A B : ℝ) :
    Continuous (fun p : ℝ × ℝ ↦
      neighboringResonantFrozenPrincipalProfile R A B p.1 p.2) := by
  have hz : Continuous
      (fun p : ℝ × ℝ ↦ (p.1 - p.2) / R ^ 2) :=
    (continuous_fst.sub continuous_snd).div_const _
  unfold neighboringResonantFrozenPrincipalProfile
  exact continuous_const.mul
    ((continuous_const.mul
      (continuous_resonantLatitudeBranch.comp hz)).add
        (continuous_const.mul (hz.pow 2)))

/-- Exact paired cancellation for a frozen resonant principal: the frozen
quadratic term disappears, leaving only the universal scaled resonant
profile. -/
theorem bandPairError_neighboringResonantFrozenPrincipalProfile
    {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    {R A B : ℝ} (hR : 0 < R) :
    bandPairError N j k
        (neighboringResonantFrozenPrincipalProfile R A B) =
      (R * reducedCuspResonantPrincipalCoefficient * (2 * A)) *
        bandPairError N j k
          (fun s t ↦ resonantLatitudeBranch ((s - t) / R ^ 2)) := by
  let P : ℝ → ℝ → ℝ :=
    neighboringResonantFrozenPrincipalProfile R A B
  let F : ℝ → ℝ → ℝ := fun s t ↦
    (R * reducedCuspResonantPrincipalCoefficient * (2 * A)) *
      resonantLatitudeBranch ((s - t) / R ^ 2)
  let Q : ℝ → ℝ → ℝ := fun s t ↦
    (R * reducedCuspResonantPrincipalCoefficient * B / R ^ 4) *
      (s - t) ^ 2
  have hz : Continuous
      (fun p : ℝ × ℝ ↦ (p.1 - p.2) / R ^ 2) :=
    (continuous_fst.sub continuous_snd).div_const _
  have hF : Continuous (fun p : ℝ × ℝ ↦ F p.1 p.2) := by
    exact continuous_const.mul
      (continuous_resonantLatitudeBranch.comp hz)
  have hQ : Continuous (fun p : ℝ × ℝ ↦ Q p.1 p.2) := by
    exact continuous_const.mul ((continuous_fst.sub continuous_snd).pow 2)
  have hP : Continuous (fun p : ℝ × ℝ ↦ P p.1 p.2) := by
    have hdecomp : (fun p : ℝ × ℝ ↦ P p.1 p.2) =
        fun p ↦ F p.1 p.2 + Q p.1 p.2 := by
      funext p
      dsimp [P, F, Q, neighboringResonantFrozenPrincipalProfile]
      field_simp [hR.ne']
      ring
    rw [hdecomp]
    exact hF.add hQ
  have hsplit :=
    bandPairError_eq_add_of_continuous_decomposition_on_literalRectangle
      j k P F Q hP hF.continuousOn (by
        intro s hs t ht
        dsimp [P, F, Q, neighboringResonantFrozenPrincipalProfile]
        field_simp [hR.ne']
        ring)
  have hQpair :
      bandPairError N j k Q = 0 := by
    dsimp [Q]
    rw [bandPairError_const_mul, bandPairError_sub_sq hN, mul_zero]
  have hFpair :
      bandPairError N j k F =
        (R * reducedCuspResonantPrincipalCoefficient * (2 * A)) *
          bandPairError N j k
            (fun s t ↦ resonantLatitudeBranch ((s - t) / R ^ 2)) := by
    dsimp [F]
    rw [bandPairError_const_mul]
  dsimp [P] at hsplit ⊢
  rw [hsplit, hQpair, add_zero, hFpair]

theorem abs_bandPairError_neighboringResonantFrozenPrincipalProfile_le
    {N : ℕ} (hN : 0 < N) (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hneigh : Nat.dist (j : ℕ) (k : ℕ) ≤ 1)
    {R A B : ℝ} (hR : 0 < R) :
    |bandPairError N j k
        (neighboringResonantFrozenPrincipalProfile R A B)| ≤
      |R * reducedCuspResonantPrincipalCoefficient * (2 * A)| *
        (4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (((neighboringBandLength N j k / R ^ 2) ^ 2) *
              resonantUnitBranchConstant)) := by
  rw [bandPairError_neighboringResonantFrozenPrincipalProfile
    hN j k hR, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_bandPairError_scaled_resonantLatitudeBranch_le_unitConstant
      hN hM j k hneigh hR)
    (abs_nonneg _)

/-- On a large-depth neighboring rectangle, freezing both dimensionless
coefficients leaves a uniform `O(δ²)` pointwise remainder. -/
theorem neighboringComparable_resonantNormalizedPrincipal_freezing
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
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
          (comparableLatitudeRadiusFloor N j) s t -
        neighboringResonantFrozenNormalizedPrincipal
          (comparableLatitudeRadiusFloor N j) u v s t| ≤
      (2 * neighboringResonantAmplitudeOscillationConstant *
          resonantUnitLinearConstant +
        neighboringResonantLogAmplitudeOscillationConstant) *
        neighboringNormalizedLength N j k ^ 2 := by
  let R := comparableLatitudeRadiusFloor N j
  let δ := neighboringNormalizedLength N j k
  let z := (s - t) / R ^ 2
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    positivity
  have hδ0 : 0 ≤ δ :=
    (neighboringComparable_normalizedLength_pos hM j k).le
  have hδ1 : δ ≤ 1 :=
    neighboringComparable_normalizedLength_le_one hM hjk hdepth
  have hw := abs_sub_le_neighboringBandLength j k hjk.2 hs ht
  have hz : |z| ≤ δ := by
    dsimp [z, δ, neighboringNormalizedLength]
    rw [abs_div, abs_of_pos (sq_pos_of_pos hR)]
    exact div_le_div_of_nonneg_right hw (sq_pos_of_pos hR).le
  have hr :
      |resonantLatitudeBranch z| ≤ resonantUnitLinearConstant * |z| :=
    abs_resonantLatitudeBranch_le_unitLinearConstant (hz.trans hδ1)
  have hA := neighboringComparable_resonantAmplitude_oscillation
    hM hjk hdepth hs hu ht hv
  have hB := neighboringComparable_resonantLogAmplitude_oscillation
    hM hjk hdepth hs hu ht hv
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

noncomputable def neighboringResonantPrincipalKernel (s t : ℝ) : ℝ :=
  latitudeAngularScale s t ^ (1 / 2 : ℝ) *
    (reducedCuspResonantPrincipalCoefficient *
      normalizedLatitudeGap s t *
        Real.log (normalizedLatitudeGap s t))

/-- The resonant principal is continuous on every literal large-depth
neighboring rectangle, including across its diagonal. -/
theorem continuousOn_neighboringResonantPrincipalKernel_rectangle
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j) :
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
    have hchart := neighboringComparable_largeDepth_rectangle_chart
      hM hjk hdepth hp.1 hp.2
    have hrs : heightRadius p.1 ≠ 0 :=
      (heightRadius_pos hchart.1).ne'
    have hrt : heightRadius p.2 ≠ 0 :=
      (heightRadius_pos hchart.2.1).ne'
    have hnum : ContinuousAt
        (fun q : ℝ × ℝ ↦ 1 - q.1 * q.2) p :=
      continuousAt_const.sub (continuousAt_fst.mul continuousAt_snd)
    have hden : ContinuousAt
        (fun q : ℝ × ℝ ↦ heightRadius q.1 * heightRadius q.2) p :=
      by
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

/-- Literal paired-error split into a frozen principal and its continuous
rectangle remainder.  The orientation is chosen so no continuity of the
remainder itself has to be established separately. -/
theorem bandPairError_frozen_eq_principal_add_remainder
    {N : ℕ} (hM : 1 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    (R A B : ℝ) :
    bandPairError N j k
        (neighboringResonantFrozenPrincipalProfile R A B) =
      bandPairError N j k neighboringResonantPrincipalKernel +
        bandPairError N j k
          (fun s t ↦
            neighboringResonantFrozenPrincipalProfile R A B s t -
              neighboringResonantPrincipalKernel s t) := by
  exact
    bandPairError_eq_add_of_continuous_decomposition_on_literalRectangle
      j k
      (neighboringResonantFrozenPrincipalProfile R A B)
      neighboringResonantPrincipalKernel
      (fun s t ↦
        neighboringResonantFrozenPrincipalProfile R A B s t -
          neighboringResonantPrincipalKernel s t)
      (continuous_neighboringResonantFrozenPrincipalProfile R A B)
      (continuousOn_neighboringResonantPrincipalKernel_rectangle
        hM hjk hdepth)
      (by
        intro s hs t ht
        ring)

noncomputable def neighboringResonantFrozenPrincipalKernel
    (R u v s t : ℝ) : ℝ :=
  R * reducedCuspResonantPrincipalCoefficient *
    neighboringResonantFrozenNormalizedPrincipal R u v s t

theorem neighboringResonantPrincipalKernel_eq_normalized
    {R s t : ℝ} (hR : 0 < R)
    (hs : s ∈ Ioo (-1 : ℝ) 1)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    neighboringResonantPrincipalKernel s t =
      R * reducedCuspResonantPrincipalCoefficient *
        neighboringResonantNormalizedPrincipal R s t := by
  unfold neighboringResonantPrincipalKernel
    neighboringResonantNormalizedPrincipal neighboringResonantAmplitude
    neighboringResonantLogAmplitude
  exact neighboringResonantPrincipal_eq_normalized_extraction hR hs ht

/-- Physical form of the freezing remainder. -/
theorem neighboringComparable_resonantPrincipal_freezing
    {N : ℕ} (hM : 3 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
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
          (comparableLatitudeRadiusFloor N j) u v s t| ≤
      comparableLatitudeRadiusFloor N j *
        |reducedCuspResonantPrincipalCoefficient| *
        ((2 * neighboringResonantAmplitudeOscillationConstant *
            resonantUnitLinearConstant +
          neighboringResonantLogAmplitudeOscillationConstant) *
          neighboringNormalizedLength N j k ^ 2) := by
  let R := comparableLatitudeRadiusFloor N j
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    positivity
  have hchart := neighboringComparable_largeDepth_rectangle_chart
    (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
  have hfree := neighboringComparable_resonantNormalizedPrincipal_freezing
    hM hjk hdepth hs hu ht hv
  rw [neighboringResonantPrincipalKernel_eq_normalized
    hR hchart.1 hchart.2.1]
  unfold neighboringResonantFrozenPrincipalKernel
  rw [← mul_sub, abs_mul, abs_mul, abs_of_pos hR]
  exact mul_le_mul_of_nonneg_left hfree
    (mul_nonneg hR.le (abs_nonneg _))

noncomputable def neighboringResonantPrincipalRawConstant : ℝ :=
  |reducedCuspResonantPrincipalCoefficient| *
    (3200 * resonantUnitBranchConstant +
      (2 * neighboringResonantAmplitudeOscillationConstant *
          resonantUnitLinearConstant +
        neighboringResonantLogAmplitudeOscillationConstant))

noncomputable def neighboringResonantPrincipalBlockConstant : ℝ :=
  1024 * neighboringResonantPrincipalRawConstant *
    (10 : ℝ) ^ 3 * (6 : ℝ) ^ 2

theorem neighboringResonantPrincipalRawConstant_nonneg :
    0 ≤ neighboringResonantPrincipalRawConstant := by
  have hL := resonantUnitLinearConstant_nonneg
  have hU := resonantUnitBranchConstant_nonneg
  unfold neighboringResonantPrincipalRawConstant
    neighboringResonantAmplitudeOscillationConstant
    neighboringResonantLogAmplitudeOscillationConstant
  positivity

/-- Complete large-depth paired bound for the logarithmic principal. -/
theorem neighboringComparable_resonantPrincipal_block_bound
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j) :
    |bandPairError N j k neighboringResonantPrincipalKernel| ≤
      comparableLatitudeBlockMajorant 1
        neighboringResonantPrincipalBlockConstant N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  let R := comparableLatitudeRadiusFloor N j
  let δ := neighboringNormalizedLength N j k
  let u := bandBoundaryHeight N (j + 1)
  let v := bandBoundaryHeight N (k + 1)
  let A := neighboringResonantAmplitude R u v
  let B := neighboringResonantLogAmplitude R u v
  let Cfree : ℝ :=
    2 * neighboringResonantAmplitudeOscillationConstant *
        resonantUnitLinearConstant +
      neighboringResonantLogAmplitudeOscillationConstant
  let Bf : ℝ :=
    |reducedCuspResonantPrincipalCoefficient| *
      (3200 * resonantUnitBranchConstant)
  let Br : ℝ :=
    |reducedCuspResonantPrincipalCoefficient| * Cfree
  have hR : 0 < R := by
    dsimp [R, comparableLatitudeRadiusFloor]
    positivity
  have hu : u ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j) :=
    ⟨le_rfl, bandBoundaryHeight_succ_le j⟩
  have hv : v ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k) :=
    ⟨le_rfl, bandBoundaryHeight_succ_le k⟩
  have hbuv := neighboringComparable_normalized_resonant_coefficients_bounded
    (by omega : 1 ≤ bandCount N) hjk hdepth hu hv
  have hA0 : 0 ≤ A := by
    dsimp [A, neighboringResonantAmplitude]
    exact mul_nonneg hbuv.2.2.1.le hbuv.1.le
  have hA : A ≤ 1600 := by
    dsimp [A, neighboringResonantAmplitude]
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hbuv.2.2.2)
      (sub_nonneg.mpr hbuv.2.1)]
  have hCfree : 0 ≤ Cfree := by
    have hL := resonantUnitLinearConstant_nonneg
    dsimp [Cfree]
    unfold neighboringResonantAmplitudeOscillationConstant
      neighboringResonantLogAmplitudeOscillationConstant
    positivity
  have hBf : 0 ≤ Bf := by
    dsimp [Bf]
    exact mul_nonneg (abs_nonneg _)
      (mul_nonneg (by norm_num) resonantUnitBranchConstant_nonneg)
  have hBr : 0 ≤ Br := by
    dsimp [Br]
    exact mul_nonneg (abs_nonneg _) hCfree
  have hcoef :
      |R * reducedCuspResonantPrincipalCoefficient * (2 * A)| ≤
        R * (|reducedCuspResonantPrincipalCoefficient| * 3200) := by
    rw [abs_mul, abs_mul, abs_of_pos hR,
      abs_of_nonneg (mul_nonneg (by norm_num) hA0)]
    calc
      R * |reducedCuspResonantPrincipalCoefficient| * (2 * A) ≤
          R * |reducedCuspResonantPrincipalCoefficient| * (2 * 1600) := by
        gcongr
      _ = R * (|reducedCuspResonantPrincipalCoefficient| * 3200) := by
        ring
  have hFrozenScaled :=
    abs_bandPairError_neighboringResonantFrozenPrincipalProfile_le
      hN hM j k hjk.2 hR (A := A) (B := B)
  have hFrozenRaw :
      |bandPairError N j k
          (neighboringResonantFrozenPrincipalProfile R A B)| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (Bf * (R * δ ^ 2)) := by
    calc
      |bandPairError N j k
          (neighboringResonantFrozenPrincipalProfile R A B)| ≤
        |R * reducedCuspResonantPrincipalCoefficient * (2 * A)| *
          (4 * (finiteBandPopulation N j : ℝ) *
            (finiteBandPopulation N k : ℝ) *
              (((neighboringBandLength N j k / R ^ 2) ^ 2) *
                resonantUnitBranchConstant)) := hFrozenScaled
      _ ≤
        (R * (|reducedCuspResonantPrincipalCoefficient| * 3200)) *
          (4 * (finiteBandPopulation N j : ℝ) *
            (finiteBandPopulation N k : ℝ) *
              (δ ^ 2 * resonantUnitBranchConstant)) := by
        have hδeq :
            neighboringBandLength N j k / R ^ 2 = δ := by
          rfl
        rw [hδeq]
        exact mul_le_mul_of_nonneg_right hcoef
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (by positivity))
              (by positivity))
            (mul_nonneg (sq_nonneg δ)
              resonantUnitBranchConstant_nonneg))
      _ = 4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (Bf * (R * δ ^ 2)) := by
        dsimp [Bf]
        ring
  have hFrozenMajor :=
    neighboringResonant_raw_bound_to_majorant hBf hM j k hjk
      (E := bandPairError N j k
        (neighboringResonantFrozenPrincipalProfile R A B))
      (by
        simpa [neighboringResonantNormalizedBandLength,
          neighboringNormalizedLength, R, δ] using hFrozenRaw)
  let Rem : ℝ → ℝ → ℝ := fun s t ↦
    neighboringResonantFrozenPrincipalProfile R A B s t -
      neighboringResonantPrincipalKernel s t
  have hRemRect :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          |Rem s t| ≤ Br * (R * δ ^ 2) := by
    intro s hs t ht
    have hf := neighboringComparable_resonantPrincipal_freezing
      hM hjk hdepth hs hu ht hv
    have hprofile :
        neighboringResonantFrozenPrincipalProfile R A B s t =
          neighboringResonantFrozenPrincipalKernel R u v s t := by
      dsimp [A, B, neighboringResonantFrozenPrincipalProfile,
        neighboringResonantFrozenPrincipalKernel,
        neighboringResonantFrozenNormalizedPrincipal]
    rw [abs_sub_comm]
    change |neighboringResonantPrincipalKernel s t -
      neighboringResonantFrozenPrincipalProfile R A B s t| ≤ _
    rw [hprofile]
    simpa [Br, Cfree, R, δ, mul_assoc, mul_left_comm, mul_comm] using hf
  have hRemRaw :
      |bandPairError N j k Rem| ≤
        4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) *
            (Br * (R * δ ^ 2)) := by
    apply abs_bandPairError_le_of_band_rectangle_bound
      hN j k Rem (Br * (R * δ ^ 2))
    · exact mul_nonneg hBr (mul_nonneg hR.le (sq_nonneg δ))
    · exact hRemRect
  have hRemMajor :=
    neighboringResonant_raw_bound_to_majorant hBr hM j k hjk
      (E := bandPairError N j k Rem)
      (by
        simpa [neighboringResonantNormalizedBandLength,
          neighboringNormalizedLength, R, δ] using hRemRaw)
  have hsplit := bandPairError_frozen_eq_principal_add_remainder
    (by omega : 1 ≤ bandCount N) j k hjk hdepth R A B
  have htri :
      |bandPairError N j k neighboringResonantPrincipalKernel| ≤
        |bandPairError N j k
          (neighboringResonantFrozenPrincipalProfile R A B)| +
        |bandPairError N j k Rem| := by
    change bandPairError N j k
        (neighboringResonantFrozenPrincipalProfile R A B) =
      bandPairError N j k neighboringResonantPrincipalKernel +
        bandPairError N j k Rem at hsplit
    calc
      |bandPairError N j k neighboringResonantPrincipalKernel| =
          |bandPairError N j k
              (neighboringResonantFrozenPrincipalProfile R A B) -
            bandPairError N j k Rem| := by
        congr 1
        linarith
      _ ≤ _ := abs_sub _ _
  calc
    |bandPairError N j k neighboringResonantPrincipalKernel| ≤
        |bandPairError N j k
          (neighboringResonantFrozenPrincipalProfile R A B)| +
        |bandPairError N j k Rem| := htri
    _ ≤ comparableLatitudeBlockMajorant 1
          (1024 * Bf * (10 : ℝ) ^ 3 * (6 : ℝ) ^ 2) N j k +
        comparableLatitudeBlockMajorant 1
          (1024 * Br * (10 : ℝ) ^ 3 * (6 : ℝ) ^ 2) N j k :=
      add_le_add hFrozenMajor hRemMajor
    _ = comparableLatitudeBlockMajorant 1
        neighboringResonantPrincipalBlockConstant N j k := by
      unfold comparableLatitudeBlockMajorant
        neighboringResonantPrincipalBlockConstant
        neighboringResonantPrincipalRawConstant
      dsimp [Bf, Br, Cfree]
      ring

/-- The resonant higher-order remainder is a physical quadratic cusp. -/
theorem abs_neighboringResonantHigherBranchKernel_le_physicalCusp
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k))
    (hst : s ≠ t) :
    |neighboringResonantHigherBranchKernel s t| ≤
      ((3200 : ℝ) ^ ((1 : ℝ) / 2) *
        ((4 / 3 : ℝ) * reducedCuspResonantRemainderCoefficient)) *
      (comparableLatitudeRadiusFloor N j ^ (-3 : ℝ) *
        |s - t| ^ (2 : ℝ)) := by
  have hchart := neighboringComparable_largeDepth_rectangle_chart
    hM hjk hdepth hs ht
  have hraw := abs_neighboringResonantHigherBranchKernel_le
    hchart.1 hchart.2.1 hst hchart.2.2.2
  have hfactor := neighboringComparable_powerFactor_le
    (α := (1 : ℝ)) (by norm_num) (by norm_num)
    hM hjk hdepth hs ht
  have hqpos : 0 < normalizedLatitudeGap s t :=
    normalizedLatitudeGap_pos hchart.1 hchart.2.1 hst
  have hqpow :
      normalizedLatitudeGap s t ^ ((3 : ℝ) / 2) ≤
        normalizedLatitudeGap s t := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hqpos hchart.2.2.2
        (by norm_num : (1 : ℝ) ≤ 3 / 2))
  have hpnonneg :
      0 ≤ latitudeAngularScale s t ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (by
      unfold latitudeAngularScale
      positivity) _
  have hfactor' :
      latitudeAngularScale s t ^ ((1 : ℝ) / 2) *
          normalizedLatitudeGap s t ^ ((3 : ℝ) / 2) ≤
        (3200 : ℝ) ^ ((1 : ℝ) / 2) *
          (comparableLatitudeRadiusFloor N j ^ (-3 : ℝ) *
            |s - t| ^ (2 : ℝ)) := by
    calc
      latitudeAngularScale s t ^ ((1 : ℝ) / 2) *
          normalizedLatitudeGap s t ^ ((3 : ℝ) / 2) ≤
        latitudeAngularScale s t ^ ((1 : ℝ) / 2) *
          normalizedLatitudeGap s t :=
        mul_le_mul_of_nonneg_left hqpow hpnonneg
      _ ≤ _ := by
        norm_num [reducedCuspUpperNu] at hfactor
        simpa [sq_abs] using hfactor
  have hcoef :
      0 ≤ (4 / 3 : ℝ) * reducedCuspResonantRemainderCoefficient :=
    mul_nonneg (by norm_num) reducedCuspResonantRemainderCoefficient_nonneg
  calc
    |neighboringResonantHigherBranchKernel s t| ≤
        (latitudeAngularScale s t ^ ((1 : ℝ) / 2) *
          normalizedLatitudeGap s t ^ ((3 : ℝ) / 2)) *
            ((4 / 3 : ℝ) *
              reducedCuspResonantRemainderCoefficient) := by
      simpa only [mul_assoc] using hraw
    _ ≤ ((3200 : ℝ) ^ ((1 : ℝ) / 2) *
          (comparableLatitudeRadiusFloor N j ^ (-3 : ℝ) *
            |s - t| ^ (2 : ℝ))) *
          ((4 / 3 : ℝ) *
            reducedCuspResonantRemainderCoefficient) :=
      mul_le_mul_of_nonneg_right hfactor' hcoef
    _ = _ := by ring

theorem abs_neighboringResonantHigherBranchKernel_le_physicalCusp_onRectangle
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    |neighboringResonantHigherBranchKernel s t| ≤
      ((3200 : ℝ) ^ ((1 : ℝ) / 2) *
        ((4 / 3 : ℝ) * reducedCuspResonantRemainderCoefficient)) *
      (comparableLatitudeRadiusFloor N j ^ (-3 : ℝ) *
        |s - t| ^ (2 : ℝ)) := by
  by_cases hst : s = t
  · subst t
    have hsI :=
      (neighboringComparable_largeDepth_rectangle_chart
        hM hjk hdepth hs ht).1
    have hr : heightRadius s ≠ 0 := (heightRadius_pos hsI).ne'
    have hrsq := heightRadius_sq ⟨hsI.1.le, hsI.2.le⟩
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
  · exact abs_neighboringResonantHigherBranchKernel_le_physicalCusp
      hM hjk hdepth hs ht hst

/-- Unconditional large-depth block bound for the higher resonant branch. -/
theorem neighboringComparable_resonantHigherBranch_block_bound
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j) :
    |bandPairError N j k neighboringResonantHigherBranchKernel| ≤
      comparableLatitudeBlockMajorant 1
        (1024 *
          ((3200 : ℝ) ^ ((1 : ℝ) / 2) *
            ((4 / 3 : ℝ) *
              reducedCuspResonantRemainderCoefficient)) *
          (10 : ℝ) ^ 3 * (6 : ℝ) ^ 2) N j k := by
  have hraw := neighboringComparable_block_bound_of_physicalCusp
    (α := (1 : ℝ))
    (B := (3200 : ℝ) ^ ((1 : ℝ) / 2) *
      ((4 / 3 : ℝ) * reducedCuspResonantRemainderCoefficient))
    (K := neighboringResonantHigherBranchKernel)
    (by norm_num) (by norm_num)
    (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3200) _)
      (mul_nonneg (by norm_num)
        reducedCuspResonantRemainderCoefficient_nonneg))
    hM j k hjk (by
      intro s hs t ht
      convert
        abs_neighboringResonantHigherBranchKernel_le_physicalCusp_onRectangle
          (by omega : 1 ≤ bandCount N) hjk hdepth hs ht using 1 <;>
        norm_num)
  norm_num at hraw ⊢
  exact hraw

noncomputable def neighboringResonantHigherBranchBlockConstant : ℝ :=
  1024 *
    ((3200 : ℝ) ^ ((1 : ℝ) / 2) *
      ((4 / 3 : ℝ) * reducedCuspResonantRemainderCoefficient)) *
    (10 : ℝ) ^ 3 * (6 : ℝ) ^ 2

noncomputable def neighboringResonantModelBlockConstant : ℝ :=
  neighboringAffineSmoothBlockConstant 1
      reducedCuspResonantConstantCoefficient
      reducedCuspResonantLinearCoefficient +
    neighboringResonantPrincipalBlockConstant

noncomputable def neighboringResonantLargeDepthBlockConstant : ℝ :=
  neighboringResonantModelBlockConstant +
    neighboringResonantHigherBranchBlockConstant

noncomputable def neighboringResonantFullBlockConstant : ℝ :=
  neighboringSmallDepthBlockConstant 1 +
    neighboringResonantLargeDepthBlockConstant

theorem neighboringResonantLargeDepthBlockConstant_nonneg :
    0 ≤ neighboringResonantLargeDepthBlockConstant := by
  unfold neighboringResonantLargeDepthBlockConstant
    neighboringResonantModelBlockConstant
    neighboringResonantHigherBranchBlockConstant
    neighboringResonantPrincipalBlockConstant
  have hraw := neighboringResonantPrincipalRawConstant_nonneg
  have hsmooth := neighboringAffineSmoothBlockConstant_nonneg
    (1 : ℝ) reducedCuspResonantConstantCoefficient
      reducedCuspResonantLinearCoefficient
  have hrem := reducedCuspResonantRemainderCoefficient_nonneg
  positivity

/-- Large-depth block bound for the constant, affine, and logarithmic
pieces of the resonant model. -/
theorem neighboringComparable_resonantModel_block_bound
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : NeighboringComparableLatitudePair N j k)
    (hdepth : 600 ≤ latitudeBandScale N j) :
    |bandPairError N j k neighboringResonantModelKernel| ≤
      comparableLatitudeBlockMajorant 1
        neighboringResonantModelBlockConstant N j k := by
  let S : Set (ℝ × ℝ) :=
    Icc (bandBoundaryHeight N (j + 1))
        (bandBoundaryHeight N j) ×ˢ
      Icc (bandBoundaryHeight N (k + 1))
        (bandBoundaryHeight N k)
  let A : ℝ → ℝ → ℝ :=
    neighboringAffineSmoothKernel 1
      reducedCuspResonantConstantCoefficient
      reducedCuspResonantLinearCoefficient
  have hA : ContinuousOn (fun p : ℝ × ℝ ↦ A p.1 p.2) S := by
    intro p hp
    have hc := neighboringComparable_largeDepth_rectangle_chart
      (by omega : 1 ≤ bandCount N) hjk hdepth hp.1 hp.2
    exact (continuousAt_neighboringAffineSmoothKernel_joint
      (α := (1 : ℝ))
      (H := reducedCuspResonantConstantCoefficient)
      (L := reducedCuspResonantLinearCoefficient)
      hc.1 hc.2.1).continuousWithinAt
  have hP : ContinuousOn
      (fun p : ℝ × ℝ ↦
        neighboringResonantPrincipalKernel p.1 p.2) S := by
    simpa [S] using
      (continuousOn_neighboringResonantPrincipalKernel_rectangle
        (by omega : 1 ≤ bandCount N) hjk hdepth)
  have hdecomp :
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          neighboringResonantModelKernel s t =
            A s t + neighboringResonantPrincipalKernel s t := by
    intro s hs t ht
    have hc := neighboringComparable_largeDepth_rectangle_chart
      (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
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
  have ha :=
    abs_bandPairError_neighboringAffineSmoothKernel_le_majorant
      (α := (1 : ℝ))
      (H := reducedCuspResonantConstantCoefficient)
      (L := reducedCuspResonantLinearCoefficient)
      (by norm_num) (by norm_num) hM hjk hdepth
  have hp :=
    neighboringComparable_resonantPrincipal_block_bound
      hM j k hjk hdepth
  rw [heq]
  calc
    |bandPairError N j k A +
        bandPairError N j k neighboringResonantPrincipalKernel| ≤
      |bandPairError N j k A| +
        |bandPairError N j k neighboringResonantPrincipalKernel| :=
      abs_add _ _
    _ ≤ comparableLatitudeBlockMajorant 1
          (neighboringAffineSmoothBlockConstant 1
            reducedCuspResonantConstantCoefficient
            reducedCuspResonantLinearCoefficient) N j k +
        comparableLatitudeBlockMajorant 1
          neighboringResonantPrincipalBlockConstant N j k :=
      add_le_add (by simpa [A] using ha) hp
    _ = comparableLatitudeBlockMajorant 1
        neighboringResonantModelBlockConstant N j k := by
      unfold comparableLatitudeBlockMajorant
        neighboringResonantModelBlockConstant
      ring

/-- Unconditional large-depth bound for the full latitude kernel at the
resonant exponent. -/
theorem hasLargeDepthNeighboringComparableLatitudeBlockBound_one
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    HasLargeDepthNeighboringComparableLatitudeBlockBound 1 N
      neighboringResonantLargeDepthBlockConstant := by
  intro j k hjk hdepth
  have hModel :=
    neighboringComparable_resonantModel_block_bound
      hM j k hjk hdepth
  have hHigher :=
    neighboringComparable_resonantHigherBranch_block_bound
      hM j k hjk hdepth
  have hA : ContinuousOn
      (fun p : ℝ × ℝ ↦ neighboringResonantModelKernel p.1 p.2)
      (Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j) ×ˢ
        Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k)) := by
    intro p hp
    have hc := neighboringComparable_largeDepth_rectangle_chart
      (by omega : 1 ≤ bandCount N) hjk hdepth hp.1 hp.2
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
      (continuousOn_neighboringResonantPrincipalKernel_rectangle
        (by omega : 1 ≤ bandCount N) hjk hdepth) p hp
    apply (hS.add hP).congr
    · intro q hq
      have hqc := neighboringComparable_largeDepth_rectangle_chart
        (by omega : 1 ≤ bandCount N) hjk hdepth hq.1 hq.2
      rw [neighboringResonantModelKernel_eq_smooth_add_log
        hqc.1 hqc.2.1]
      rfl
    · rw [neighboringResonantModelKernel_eq_smooth_add_log
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
    have hc := neighboringComparable_largeDepth_rectangle_chart
      (by omega : 1 ≤ bandCount N) hjk hdepth hs ht
    exact latitudeKernel_one_eq_neighboringResonantModel_add_branch_on_unitChart
      hc.1 hc.2.1 hc.2.2.2
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
          neighboringResonantModelBlockConstant N j k +
        comparableLatitudeBlockMajorant 1
          neighboringResonantHigherBranchBlockConstant N j k := by
      exact add_le_add hModel (by
        simpa [neighboringResonantHigherBranchBlockConstant] using hHigher)
    _ = comparableLatitudeBlockMajorant 1
        neighboringResonantLargeDepthBlockConstant N j k := by
      unfold comparableLatitudeBlockMajorant
        neighboringResonantLargeDepthBlockConstant
      ring

/-- Final unconditional neighboring comparable predicate at `α = 1`. -/
theorem hasNeighboringComparableLatitudeBlockBound_one
    {N : ℕ} (hM : 3 ≤ bandCount N) :
    HasNeighboringComparableLatitudeBlockBound 1 N
      neighboringResonantFullBlockConstant := by
  intro j k hjk
  have hfinal :=
    neighboringComparable_block_bound_of_largeDepth
      (α := (1 : ℝ))
      (C := neighboringResonantLargeDepthBlockConstant)
      (by norm_num) (by norm_num)
      (by omega : 1 ≤ bandCount N)
      neighboringResonantLargeDepthBlockConstant_nonneg
      (hasLargeDepthNeighboringComparableLatitudeBlockBound_one hM)
      j k hjk
  simpa [neighboringResonantFullBlockConstant] using hfinal

end BEMOC
