import BEMOCFormalization.LatitudeComparableGeometry
import BEMOCFormalization.LatitudeComparableDerivativeEnvelope
import BEMOCFormalization.LatitudeComparableGradedGap
import BEMOCFormalization.LatitudeMixedTaylorSpecialization
import BEMOCFormalization.LatitudePointwiseAssembly
import BEMOCFormalization.LatitudeUnequalBlocks

/-!
# Separated comparable latitude blocks

This file closes the geometric and Peano parts of the regular comparable
same-hemisphere estimate away from neighboring bands.  The analytic input is
stated at exactly the uniform scale obtained from

`R^(-2-α) |s-t|^(α-3)`

after inserting the row radius and the lower bound for the height separation.
Thus no unit normalized-gap chart is silently assumed here.
-/

open Set

namespace BEMOC

/-- A comparable regular same-hemisphere pair with at least one intervening
band. -/
def SeparatedComparableSameLatitudePair (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : Prop :=
  ComparableSameLatitudePair N j k ∧
    2 ≤ Nat.dist (j : ℕ) (k : ℕ)

/-- The exact uniform mixed-derivative datum needed on separated comparable
rectangles.  Its powers are those of (5.5) after the physical separation
estimate is inserted. -/
def HasSeparatedComparableLatitudeDssttBound
    (α : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ j k : Fin (bandTailCount N + 1),
    SeparatedComparableSameLatitudePair N j k →
      ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
          (bandBoundaryHeight N j),
        ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
          (bandBoundaryHeight N k),
          |variableReducedLatitudeKernelDsstt α s t| ≤
            C * (bandCount N : ℝ) ^ (8 - α) *
              (latitudeBandScale N j : ℝ) ^ (-5 : ℝ) *
              (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3)

/-- The constant incurred when the physical derivative scale is converted
to the literal row radius and index separation. -/
noncomputable def comparableDerivativeScaleConversionConstant
    (α : ℝ) : ℝ :=
  5 * (10 : ℝ) ^ (2 + α) * (30 : ℝ) ^ (3 - α)

private theorem comparableDerivativeScale_identity
    {α d M D : ℝ} (hd : 0 < d) (hM : 0 < M) (hD : 0 < D) :
    (d / (10 * M)) ^ (-2 - α) *
        (d * D / (30 * M ^ 2)) ^ (α - 3) =
      (10 : ℝ) ^ (2 + α) * (30 : ℝ) ^ (3 - α) *
        M ^ (8 - α) * d ^ (-5 : ℝ) * D ^ (α - 3) := by
  rw [Real.div_rpow hd.le (by positivity : 0 ≤ 10 * M),
    Real.div_rpow (mul_nonneg hd.le hD.le)
      (by positivity : 0 ≤ 30 * M ^ 2)]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [← Real.rpow_neg (by positivity : 0 ≤ 10 * M),
    ← Real.rpow_neg (by positivity : 0 ≤ 30 * M ^ 2)]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) hM.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 30) (sq_nonneg M),
    Real.mul_rpow hd.le hD.le]
  rw [← Real.rpow_natCast M 2]
  rw [← Real.rpow_mul hM.le]
  calc
    d ^ (-2 - α) * (10 ^ (-(-2 - α)) * M ^ (-(-2 - α))) *
          (d ^ (α - 3) * D ^ (α - 3) *
            (30 ^ (-(α - 3)) * M ^ ((2 : ℝ) * -(α - 3)))) =
        (10 ^ (-(-2 - α)) * 30 ^ (-(α - 3))) *
          (M ^ (-(-2 - α)) * M ^ ((2 : ℝ) * -(α - 3))) *
          (d ^ (-2 - α) * d ^ (α - 3)) * D ^ (α - 3) := by ring
    _ = (10 ^ (-(-2 - α)) * 30 ^ (-(α - 3))) *
          M ^ (-(-2 - α) + (2 : ℝ) * -(α - 3)) *
          d ^ ((-2 - α) + (α - 3)) * D ^ (α - 3) := by
      rw [Real.rpow_add hM, Real.rpow_add hd]
    _ = _ := by ring_nf

/-- A sharp physical pointwise estimate on a separated rectangle converts
to the uniform row/index form consumed by
`HasSeparatedComparableLatitudeDssttBound`. -/
theorem hasSeparatedComparableLatitudeDssttBound_of_physicalScale
    {α C : ℝ} {N : ℕ} (hM : 1 ≤ bandCount N)
    (hα2 : α < 2) (hC : 0 ≤ C)
    (h :
      ∀ j k : Fin (bandTailCount N + 1),
        SeparatedComparableSameLatitudePair N j k →
          ∀ s ∈ Icc (bandBoundaryHeight N (j + 1))
              (bandBoundaryHeight N j),
            ∀ t ∈ Icc (bandBoundaryHeight N (k + 1))
              (bandBoundaryHeight N k),
              |variableReducedLatitudeKernelDsstt α s t| ≤
                5 * C *
                  latitudePowerDerivativeScale α
                    (comparableLatitudeRadiusFloor N j) |s - t|) :
    HasSeparatedComparableLatitudeDssttBound α N
      (comparableDerivativeScaleConversionConstant α * C) := by
  intro j k hjk s hs t ht
  have hMreal : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hdreal : (0 : ℝ) < latitudeBandScale N j := by
    exact_mod_cast latitudeBandScale_pos N j
  let d : ℝ := latitudeBandScale N j
  let M : ℝ := bandCount N
  let D : ℝ := 1 + Nat.dist (j : ℕ) (k : ℕ)
  let L : ℝ := d * D / (30 * M ^ 2)
  have hD : 0 < D := by dsimp [D]; positivity
  have hL : 0 < L := by dsimp [L, d, M]; positivity
  have hsep : L ≤ |s - t| := by
    simpa [L, d, M, D] using
      (comparableSame_rectangle_geometry hM hjk.1 hs ht).2.2 hjk.2
  have he : α - 3 ≤ 0 := by linarith
  have hpow :
      |s - t| ^ (α - 3) ≤ L ^ (α - 3) :=
    Real.rpow_le_rpow_of_nonpos hL hsep he
  have hR :
      0 < comparableLatitudeRadiusFloor N j := by
    unfold comparableLatitudeRadiusFloor
    positivity
  have hscale0 :
      0 ≤ (comparableLatitudeRadiusFloor N j) ^ (-2 - α) := by
    positivity
  have hraw := h j k hjk s hs t ht
  unfold latitudePowerDerivativeScale at hraw
  calc
    |variableReducedLatitudeKernelDsstt α s t| ≤
        5 * C *
          ((comparableLatitudeRadiusFloor N j) ^ (-2 - α) *
            |s - t| ^ (α - 3)) := by simpa [mul_assoc] using hraw
    _ ≤ 5 * C *
          ((comparableLatitudeRadiusFloor N j) ^ (-2 - α) *
            L ^ (α - 3)) := by gcongr
    _ = (comparableDerivativeScaleConversionConstant α * C) *
          (bandCount N : ℝ) ^ (8 - α) *
          (latitudeBandScale N j : ℝ) ^ (-5 : ℝ) *
          (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) ^ (α - 3) := by
      rw [show comparableLatitudeRadiusFloor N j = d / (10 * M) by
        rfl]
      rw [comparableDerivativeScale_identity
        (α := α) (d := d) (M := M) (D := D)
        (by dsimp [d]; exact hdreal)
        (by dsimp [M]; exact hMreal) hD]
      unfold comparableDerivativeScaleConversionConstant
      dsimp [d, M, D]
      ring

/-- Every separated comparable rectangle lies in the open height chart and
is disjoint from the diagonal. -/
theorem separatedComparableSame_rectangle_interior_offDiagonal
    {N : ℕ} (hM : 1 ≤ bandCount N)
    {j k : Fin (bandTailCount N + 1)}
    (hjk : SeparatedComparableSameLatitudePair N j k)
    {s t : ℝ}
    (hs : s ∈ Icc (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (ht : t ∈ Icc (bandBoundaryHeight N (k + 1))
      (bandBoundaryHeight N k)) :
    s ∈ Ioo (-1 : ℝ) 1 ∧ t ∈ Ioo (-1 : ℝ) 1 ∧ s ≠ t := by
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
  have hfloor :=
    (comparableSame_rectangle_geometry hM hjk.1 hs ht).1
  have hMpos : (0 : ℝ) < bandCount N := by exact_mod_cast hM
  have hdpos : (0 : ℝ) < latitudeBandScale N j := by
    exact_mod_cast latitudeBandScale_pos N j
  have hR :
      0 < (latitudeBandScale N j : ℝ) /
        (10 * (bandCount N : ℝ)) := by positivity
  have hsI := mem_Ioo_of_mem_Icc_heightRadius_pos hsSphere
    (hR.trans_le hfloor.1)
  have htI := mem_Ioo_of_mem_Icc_heightRadius_pos htSphere
    (hR.trans_le hfloor.2)
  have hsep := (comparableSame_rectangle_geometry hM hjk.1 hs ht).2.2
    hjk.2
  have hsepPos :
      0 < (latitudeBandScale N j : ℝ) *
          (1 + Nat.dist (j : ℕ) (k : ℕ) : ℝ) /
            (30 * (bandCount N : ℝ) ^ 2) := by positivity
  exact ⟨hsI, htI, fun hst ↦ by
    subst t
    simpa using hsepPos.trans_le hsep⟩

/-- Positive-real scale arithmetic for the separated comparable Peano
remainder.  The only loss is the explicit numerical factor `8192`,
coming from the Peano constant and the two population upper bounds. -/
theorem separatedComparable_scale_arithmetic
    {α C M N d p q D : ℝ}
    (hC : 0 ≤ C) (hM : 0 < M) (hN : 0 < N) (hd : 0 < d)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hD : 0 < D)
    (hp' : p ≤ 4 * d) (hq' : q ≤ 8 * d)
    (hMN : 4 * M ^ 2 ≤ N) :
    64 * (C * M ^ (8 - α) * d ^ (-5 : ℝ) * D ^ (α - 3)) *
          p ^ 3 * q ^ 3 / N ^ 4 ≤
      8192 * C * d * M ^ (-α) * D ^ (α - 3) := by
  have hcoef :
      0 ≤ C * M ^ (8 - α) * d ^ (-5 : ℝ) * D ^ (α - 3) := by
    positivity
  have hp3 : p ^ 3 ≤ (4 * d) ^ 3 := by gcongr
  have hq3 : q ^ 3 ≤ (8 * d) ^ 3 := by gcongr
  have hnum :
      64 * (C * M ^ (8 - α) * d ^ (-5 : ℝ) * D ^ (α - 3)) *
          p ^ 3 * q ^ 3 ≤
        64 * (C * M ^ (8 - α) * d ^ (-5 : ℝ) * D ^ (α - 3)) *
          (4 * d) ^ 3 * (8 * d) ^ 3 := by
    gcongr
  have hden : (4 * M ^ 2) ^ 4 ≤ N ^ 4 := by gcongr
  have hMcombine :
      M ^ (8 - α) * (M ^ 8)⁻¹ = M ^ (-α) := by
    rw [← Real.rpow_natCast M 8, ← Real.rpow_neg hM.le]
    rw [← Real.rpow_add hM]
    congr 1
    ring
  have hdcombine :
      d ^ (-5 : ℝ) * d ^ 6 = d := by
    rw [← Real.rpow_natCast d 6, ← Real.rpow_add hd]
    norm_num
  calc
    64 * (C * M ^ (8 - α) * d ^ (-5 : ℝ) * D ^ (α - 3)) *
          p ^ 3 * q ^ 3 / N ^ 4 ≤
        (64 * (C * M ^ (8 - α) * d ^ (-5 : ℝ) * D ^ (α - 3)) *
          (4 * d) ^ 3 * (8 * d) ^ 3) / N ^ 4 := by
      exact div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤
        (64 * (C * M ^ (8 - α) * d ^ (-5 : ℝ) * D ^ (α - 3)) *
          (4 * d) ^ 3 * (8 * d) ^ 3) / (4 * M ^ 2) ^ 4 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 8192 * C * d * M ^ (-α) * D ^ (α - 3) := by
      rw [div_eq_mul_inv]
      rw [show (4 * M ^ 2) ^ 4 = 256 * M ^ 8 by ring]
      calc
        64 * (C * M ^ (8 - α) * d ^ (-5 : ℝ) * D ^ (α - 3)) *
              (4 * d) ^ 3 * (8 * d) ^ 3 *
              (256 * M ^ 8)⁻¹ =
            8192 * C * (d ^ (-5 : ℝ) * d ^ 6) *
              (M ^ (8 - α) * (M ^ 8)⁻¹) * D ^ (α - 3) := by
                rw [mul_inv]
                norm_num
                ring
        _ = _ := by rw [hdcombine, hMcombine]

/-- The separated comparable block estimate follows from the sharp
pointwise mixed derivative scale, with all geometry, regularity, Peano
transfer, population comparison, and scale arithmetic discharged. -/
theorem separatedComparableSame_block_bound_of_Dsstt
    {α C : ℝ} {N : ℕ} (hM : 1 ≤ bandCount N)
    (hα : 0 < α) (hC : 0 ≤ C)
    (h : HasSeparatedComparableLatitudeDssttBound α N C) :
    ∀ j k, SeparatedComparableSameLatitudePair N j k →
      |bandPairError N j k (latitudeKernel α)| ≤
        comparableLatitudeBlockMajorant α (8192 * C) N j k := by
  have hN : 0 < N := by
    have hfour := four_mul_bandCount_sq_le N
    have hpos : 0 < 4 * bandCount N ^ 2 := by positivity
    omega
  have hMN :
      4 * (bandCount N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast four_mul_bandCount_sq_le N
  intro j k hjk
  let D : ℝ := 1 + Nat.dist (j : ℕ) (k : ℕ)
  let B : ℝ :=
    C * (bandCount N : ℝ) ^ (8 - α) *
      (latitudeBandScale N j : ℝ) ^ (-5 : ℝ) *
      D ^ (α - 3)
  have hB : 0 ≤ B := by dsimp [B, D]; positivity
  have hraw :=
    abs_latitudeKernel_bandPairError_le_of_Dsstt
      hN hα hB j k
      (fun s hs t ht ↦
        separatedComparableSame_rectangle_interior_offDiagonal hM hjk hs ht)
      (fun s hs t ht ↦ by
        simpa [B, D] using h j k hjk s hs t ht)
  have hpops :=
    finiteBandPopulations_le_four_scales_of_same hjk.1.2.2.1
  have hpj :
      (finiteBandPopulation N j : ℝ) ≤
        4 * (latitudeBandScale N j : ℝ) := by
    exact_mod_cast hpops.1
  have hpk0 :
      (finiteBandPopulation N k : ℝ) ≤
        4 * (latitudeBandScale N k : ℝ) := by
    exact_mod_cast hpops.2
  have hcomp :
      (latitudeBandScale N k : ℝ) ≤
        2 * (latitudeBandScale N j : ℝ) := by
    exact_mod_cast hjk.1.2.2.2.2
  have hpk :
      (finiteBandPopulation N k : ℝ) ≤
        8 * (latitudeBandScale N j : ℝ) := by linarith
  have hscale := separatedComparable_scale_arithmetic
    (α := α) (C := C) (M := (bandCount N : ℝ)) (N := (N : ℝ))
    (d := (latitudeBandScale N j : ℝ))
    (p := (finiteBandPopulation N j : ℝ))
    (q := (finiteBandPopulation N k : ℝ)) (D := D)
    hC (by exact_mod_cast hM) (by exact_mod_cast hN)
    (by exact_mod_cast latitudeBandScale_pos N j)
    (by positivity) (by positivity) (by dsimp [D]; positivity)
    hpj hpk hMN
  exact hraw.trans (by
    simpa [B, D, comparableLatitudeBlockMajorant] using hscale)

end BEMOC
