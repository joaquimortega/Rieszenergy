import BEMOCFormalization.LatitudeComparableGapGeometry
import BEMOCFormalization.LatitudeComparableSeparatedClosure

/-!
# Sharp-jet closure for separated comparable blocks

The genuine mixed derivative consists of four top-level Leibniz blocks.
This module connects their graded estimate, without any further analytic or
geometric premise, to the final separated comparable block weight.
-/

open Set

namespace BEMOC

/-- The sharp angular-scale jet on a comparable-radius rectangle.  Pure
first derivatives cost no radius power; each additional derivative in the
same variable costs `R⁻²`. -/
def LatitudeComparableAngularJetBound (s t R : ℝ) : Prop :=
  2 * R ^ 2 ≤ latitudeAngularScale s t ∧
  latitudeAngularScale s t ≤ 3200 * R ^ 2 ∧
  |latitudeAngularScaleDs s t| ≤ 80 ∧
  |latitudeAngularScaleDt s t| ≤ 80 ∧
  |latitudeAngularScaleDss s t| ≤ 80 * R⁻¹ ^ 2 ∧
  |latitudeAngularScaleDtt s t| ≤ 80 * R⁻¹ ^ 2 ∧
  |latitudeAngularScaleDst s t| ≤ 2 * R⁻¹ ^ 2 ∧
  |latitudeAngularScaleDsst s t| ≤ 2 * R⁻¹ ^ 4 ∧
  |latitudeAngularScaleDstt s t| ≤ 2 * R⁻¹ ^ 4 ∧
  |latitudeAngularScaleDsstt s t| ≤ 2 * R⁻¹ ^ 6

theorem latitudeComparableAngularJetBound
    {s t R : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) (hR : 0 < R)
    (hsfloor : R ≤ heightRadius s) (htfloor : R ≤ heightRadius t)
    (hsupper : heightRadius s ≤ 40 * R)
    (htupper : heightRadius t ≤ 40 * R) :
    LatitudeComparableAngularJetBound s t R := by
  have hpLower :=
    two_mul_radiusFloor_sq_le_latitudeAngularScale hR.le hsfloor htfloor
  have hpUpper : latitudeAngularScale s t ≤ 3200 * R ^ 2 := by
    rw [latitudeAngularScale_eq_heightRadius]
    have hs0 : 0 ≤ heightRadius s := by unfold heightRadius; positivity
    have ht0 : 0 ≤ heightRadius t := by unfold heightRadius; positivity
    calc
      2 * heightRadius s * heightRadius t ≤
          2 * (40 * R) * (40 * R) := by gcongr
      _ = 3200 * R ^ 2 := by ring
  have hps := abs_latitudeAngularScaleDs_le_of_radius_ceiling
    hs hR (by norm_num : (0 : ℝ) ≤ 40) hsfloor htupper
  have hpt := abs_latitudeAngularScaleDt_le_of_radius_ceiling
    ht hR (by norm_num : (0 : ℝ) ≤ 40) htfloor hsupper
  have hpss := abs_latitudeAngularScaleDss_le_of_radius_ceiling
    hR (by norm_num : (0 : ℝ) ≤ 40) hsfloor htupper
  have hptt := abs_latitudeAngularScaleDtt_le_of_radius_ceiling
    hR (by norm_num : (0 : ℝ) ≤ 40) htfloor hsupper
  have hpst := abs_latitudeAngularScaleDst_le
    hs ht hR hsfloor htfloor
  have hpsst := abs_latitudeAngularScaleDsst_le
    ht hR hsfloor htfloor
  have hpstt := abs_latitudeAngularScaleDstt_le
    hs hR hsfloor htfloor
  have hpsstt := abs_latitudeAngularScaleDsstt_le
    hR hsfloor htfloor
  exact ⟨hpLower, hpUpper,
    by norm_num at hps ⊢; exact hps,
    by norm_num at hpt ⊢; exact hpt,
    by convert hpss using 1 <;> norm_num [inv_pow],
    by convert hptt using 1 <;> norm_num [inv_pow],
    hpst, hpsst, hpstt, hpsstt⟩

/-- The preceding sharp angular jet holds unconditionally on every literal
classified comparable rectangle. -/
theorem comparableSame_rectangle_angularJetBound
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : ComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    LatitudeComparableAngularJetBound s t
      (comparableLatitudeRadiusFloor N j) := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hsSphere : s ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (j + 1)).1.trans hs.1,
      hs.2.trans (bandBoundaryHeight_mem hN j).2⟩
  have htSphere : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(bandBoundaryHeight_mem hN (k + 1)).1.trans ht.1,
      ht.2.trans (bandBoundaryHeight_mem hN k).2⟩
  have hfloor := (comparableSame_rectangle_geometry hM hjk hs ht).1
  have hupper :=
    comparableSame_rectangle_common_radius_ceiling hM hjk hs ht
  have hR : 0 < comparableLatitudeRadiusFloor N j := by
    unfold comparableLatitudeRadiusFloor
    have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hdr : (0 : ℝ) < latitudeBandScale N j := by
      exact_mod_cast latitudeBandScale_pos N j
    positivity
  exact latitudeComparableAngularJetBound hsSphere htSphere hR
    hfloor.1 hfloor.2 hupper.1 hupper.2

/-- The five powers of the angular scale retain their individual radius
degrees.  A common envelope would lose precisely the grading needed in
(5.5). -/
def LatitudeComparablePowerRpowGradedBound
    (α s t R A : ℝ) : Prop :=
  0 ≤ A ∧
  |latitudeAngularScale s t ^ (α / 2)| ≤
    A * R ^ α ∧
  |latitudeAngularScale s t ^ (α / 2 - 1)| ≤
    A * R ^ (α - 2) ∧
  |latitudeAngularScale s t ^ (α / 2 - 2)| ≤
    A * R ^ (α - 4) ∧
  |latitudeAngularScale s t ^ (α / 2 - 3)| ≤
    A * R ^ (α - 6) ∧
  |latitudeAngularScale s t ^ (α / 2 - 4)| ≤
    A * R ^ (α - 8)

noncomputable def latitudeComparablePowerRpowConstant (α : ℝ) : ℝ :=
  1 + (3200 : ℝ) ^ (α / 2) +
    (2 : ℝ) ^ (α / 2 - 1) +
    (2 : ℝ) ^ (α / 2 - 2) +
    (2 : ℝ) ^ (α / 2 - 3) +
    (2 : ℝ) ^ (α / 2 - 4)

private theorem abs_rpow_le_upper_radiusScale
    {p R e : ℝ} (hR : 0 < R) (he : 0 ≤ e)
    (hp0 : 0 ≤ p) (hp : p ≤ 3200 * R ^ 2) :
    |p ^ e| ≤ (3200 : ℝ) ^ e * R ^ (2 * e) := by
  rw [abs_of_nonneg (Real.rpow_nonneg hp0 _)]
  calc
    p ^ e ≤ (3200 * R ^ 2) ^ e :=
      Real.rpow_le_rpow hp0 hp he
    _ = (3200 : ℝ) ^ e * (R ^ 2) ^ e := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3200) (sq_nonneg R)]
    _ = (3200 : ℝ) ^ e * R ^ (2 * e) := by
      rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le]
      norm_num

private theorem abs_rpow_le_lower_radiusScale
    {p R e : ℝ} (hR : 0 < R) (he : e ≤ 0)
    (hp : 2 * R ^ 2 ≤ p) :
    |p ^ e| ≤ (2 : ℝ) ^ e * R ^ (2 * e) := by
  have hp0 : 0 < p := (by positivity : 0 < 2 * R ^ 2).trans_le hp
  rw [abs_of_nonneg (Real.rpow_nonneg hp0.le _)]
  calc
    p ^ e ≤ (2 * R ^ 2) ^ e :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hp he
    _ = (2 : ℝ) ^ e * (R ^ 2) ^ e := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg R)]
    _ = (2 : ℝ) ^ e * R ^ (2 * e) := by
      rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le]
      norm_num

theorem latitudeComparablePowerRpowGradedBound
    {α s t R : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hR : 0 < R)
    (hjet : LatitudeComparableAngularJetBound s t R) :
    LatitudeComparablePowerRpowGradedBound α s t R
      (latitudeComparablePowerRpowConstant α) := by
  rcases hjet with ⟨hpLower, hpUpper, _⟩
  have hp0 : 0 ≤ latitudeAngularScale s t :=
    (by positivity : 0 ≤ 2 * R ^ 2).trans hpLower
  let A := latitudeComparablePowerRpowConstant α
  have hA : 0 ≤ A := by
    dsimp [A, latitudeComparablePowerRpowConstant]
    positivity
  have hn0 : 0 ≤ (3200 : ℝ) ^ (α / 2) := by positivity
  have hn1 : 0 ≤ (2 : ℝ) ^ (α / 2 - 1) := by positivity
  have hn2 : 0 ≤ (2 : ℝ) ^ (α / 2 - 2) := by positivity
  have hn3 : 0 ≤ (2 : ℝ) ^ (α / 2 - 3) := by positivity
  have hn4 : 0 ≤ (2 : ℝ) ^ (α / 2 - 4) := by positivity
  have hc0 : (3200 : ℝ) ^ (α / 2) ≤ A := by
    dsimp [A, latitudeComparablePowerRpowConstant]
    linarith
  have hc1 : (2 : ℝ) ^ (α / 2 - 1) ≤ A := by
    dsimp [A, latitudeComparablePowerRpowConstant]
    linarith
  have hc2 : (2 : ℝ) ^ (α / 2 - 2) ≤ A := by
    dsimp [A, latitudeComparablePowerRpowConstant]
    linarith
  have hc3 : (2 : ℝ) ^ (α / 2 - 3) ≤ A := by
    dsimp [A, latitudeComparablePowerRpowConstant]
    linarith
  have hc4 : (2 : ℝ) ^ (α / 2 - 4) ≤ A := by
    dsimp [A, latitudeComparablePowerRpowConstant]
    linarith
  refine ⟨hA, ?_, ?_, ?_, ?_, ?_⟩
  · have h := abs_rpow_le_upper_radiusScale hR (by linarith : 0 ≤ α / 2)
      hp0 hpUpper
    calc
      |latitudeAngularScale s t ^ (α / 2)| ≤
          (3200 : ℝ) ^ (α / 2) * R ^ (2 * (α / 2)) := h
      _ ≤ A * R ^ (2 * (α / 2)) := by gcongr
      _ = A * R ^ α := by ring
  · have h := abs_rpow_le_lower_radiusScale hR
      (by linarith : α / 2 - 1 ≤ 0) hpLower
    calc
      |latitudeAngularScale s t ^ (α / 2 - 1)| ≤
          (2 : ℝ) ^ (α / 2 - 1) * R ^ (2 * (α / 2 - 1)) := h
      _ ≤ A * R ^ (2 * (α / 2 - 1)) := by gcongr
      _ = A * R ^ (α - 2) := by ring
  · have h := abs_rpow_le_lower_radiusScale hR
      (by linarith : α / 2 - 2 ≤ 0) hpLower
    calc
      |latitudeAngularScale s t ^ (α / 2 - 2)| ≤
          (2 : ℝ) ^ (α / 2 - 2) * R ^ (2 * (α / 2 - 2)) := h
      _ ≤ A * R ^ (2 * (α / 2 - 2)) := by gcongr
      _ = A * R ^ (α - 4) := by ring
  · have h := abs_rpow_le_lower_radiusScale hR
      (by linarith : α / 2 - 3 ≤ 0) hpLower
    calc
      |latitudeAngularScale s t ^ (α / 2 - 3)| ≤
          (2 : ℝ) ^ (α / 2 - 3) * R ^ (2 * (α / 2 - 3)) := h
      _ ≤ A * R ^ (2 * (α / 2 - 3)) := by gcongr
      _ = A * R ^ (α - 6) := by ring
  · have h := abs_rpow_le_lower_radiusScale hR
      (by linarith : α / 2 - 4 ≤ 0) hpLower
    calc
      |latitudeAngularScale s t ^ (α / 2 - 4)| ≤
          (2 : ℝ) ^ (α / 2 - 4) * R ^ (2 * (α / 2 - 4)) := h
      _ ≤ A * R ^ (2 * (α / 2 - 4)) := by gcongr
      _ = A * R ^ (α - 8) := by ring

theorem comparableSame_rectangle_powerRpowGradedBound
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : ComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    LatitudeComparablePowerRpowGradedBound α s t
      (comparableLatitudeRadiusFloor N j)
      (latitudeComparablePowerRpowConstant α) := by
  have hR : 0 < comparableLatitudeRadiusFloor N j := by
    unfold comparableLatitudeRadiusFloor
    have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
    have hdr : (0 : ℝ) < latitudeBandScale N j := by
      exact_mod_cast latitudeBandScale_pos N j
    positivity
  exact latitudeComparablePowerRpowGradedBound hα0 hα2 hR
    (comparableSame_rectangle_angularJetBound hM hjk hs ht)

/-- Pointwise control of the four graded Leibniz blocks on every separated
comparable rectangle gives the uniform derivative datum used by the Peano
bridge. -/
theorem hasSeparatedComparableLatitudeDssttBound_of_comparableTerms
    {α C : ℝ} {N : ℕ} (hM : 1 ≤ bandCount N)
    (hα2 : α < 2) (hC : 0 ≤ C)
    (hterms :
      ∀ j k : Fin (bandTailCount N + 1),
        SeparatedComparableSameLatitudePair N j k →
          ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
              (bandBoundaryHeight N j),
            ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
              (bandBoundaryHeight N k),
              LatitudeComparableMixedTermBound α s t
                (comparableLatitudeRadiusFloor N j) C) :
    HasSeparatedComparableLatitudeDssttBound α N
      (comparableDerivativeScaleConversionConstant α * C) := by
  apply hasSeparatedComparableLatitudeDssttBound_of_physicalScale
    hM hα2 hC
  intro j k hjk s hs t ht
  apply abs_variableReducedLatitudeKernelDsstt_le_of_comparableTerms hC
  · unfold latitudePowerDerivativeScale
    have hR : 0 < comparableLatitudeRadiusFloor N j := by
      unfold comparableLatitudeRadiusFloor
      have hMr : (0 : ℝ) < bandCount N := by exact_mod_cast hM
      have hdr : (0 : ℝ) < latitudeBandScale N j := by
        exact_mod_cast latitudeBandScale_pos N j
      positivity
    exact mul_nonneg (Real.rpow_nonneg hR.le _)
      (Real.rpow_nonneg (abs_nonneg _) _)
  · exact hterms j k hjk s hs t ht

/-- Fully assembled separated comparable block estimate from the four sharp
Leibniz terms.  The remaining local analysis is now exactly the proof of
`LatitudeComparableMixedTermBound`; all chart, separation, Peano, population,
and exponent arithmetic has disappeared from the conclusion. -/
theorem separatedComparableSame_block_bound_of_comparableTerms
    {α C : ℝ} {N : ℕ} (hM : 1 ≤ bandCount N)
    (hα0 : 0 < α) (hα2 : α < 2) (hC : 0 ≤ C)
    (hterms :
      ∀ j k : Fin (bandTailCount N + 1),
        SeparatedComparableSameLatitudePair N j k →
          ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
              (bandBoundaryHeight N j),
            ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
              (bandBoundaryHeight N k),
              LatitudeComparableMixedTermBound α s t
                (comparableLatitudeRadiusFloor N j) C) :
    ∀ j k, SeparatedComparableSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α
          (8192 *
            (comparableDerivativeScaleConversionConstant α * C)) N j k := by
  exact separatedComparableSame_block_bound_of_Dsstt hM hα0
    (mul_nonneg
      (by unfold comparableDerivativeScaleConversionConstant; positivity)
      hC)
    (hasSeparatedComparableLatitudeDssttBound_of_comparableTerms
      hM hα2 hC hterms)

end BEMOC
