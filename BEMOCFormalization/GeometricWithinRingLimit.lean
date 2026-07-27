import BEMOCFormalization.SquareWithinRing
import BEMOCFormalization.CentralWithinRing
import BEMOCFormalization.RiemannSum

/-!
# Sharp geometric weighted-sum limit on the square subsequence

This module proves the geometric part of the sharp within-ring asymptotic:
the normalized population--radius weight on `N = 4m²` converges to the
population-sensitive midpoint and shared-boundary integral.
-/

open scoped BigOperators Topology Interval
open Filter Set MeasureTheory

namespace BEMOC

noncomputable def squareRingCoefficient (α : ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1 ^ α * z.2 ^ (1 - α)

def squareCoefficientRectangle : Set (ℝ × ℝ) :=
  Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 4

theorem continuousOn_squareRingCoefficient (α : ℝ) :
    ContinuousOn (squareRingCoefficient α) squareCoefficientRectangle := by
  intro z hz
  exact ((continuousAt_fst.rpow_const (Or.inl (by
    have : (0 : ℝ) < z.1 := lt_of_lt_of_le (by norm_num) hz.1.1
    exact this.ne'))).mul
      (continuousAt_snd.rpow_const (Or.inl (by
        have : (0 : ℝ) < z.2 := lt_of_lt_of_le (by norm_num) hz.2.1
        exact this.ne')))).continuousWithinAt

theorem isCompact_squareCoefficientRectangle :
    IsCompact squareCoefficientRectangle :=
  isCompact_Icc.prod isCompact_Icc

theorem squareLimitPair_mem_rectangle {c : ℝ}
    (hc : c ∈ Set.Icc (1 / 2 : ℝ) 4) {m : ℕ} (hm : 0 < m)
    (j : Fin (m - 1)) :
    (squareLimitRadiusFactor m ((j : ℕ) + 1), c) ∈
      squareCoefficientRectangle := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdle : ((j : ℕ) + 1 : ℕ) ≤ m := by omega
  have hx0 : (0 : ℝ) ≤ ((((j : ℕ) + 1 : ℕ) : ℝ) / m) := by positivity
  have hx1 : ((((j : ℕ) + 1 : ℕ) : ℝ) / m) ≤ 1 := by
    rw [div_le_one hmR]
    exact_mod_cast hdle
  have hbase : (1 : ℝ) ≤
      2 - (((((j : ℕ) + 1 : ℕ) : ℝ) / m) ^ 2) := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  constructor
  · constructor
    · have hs : (1 : ℝ) ≤ squareLimitRadiusFactor m ((j : ℕ) + 1) := by
        unfold squareLimitRadiusFactor
        exact Real.le_sqrt_of_sq_le (by nlinarith)
      linarith
    · unfold squareLimitRadiusFactor
      rw [Real.sqrt_le_iff]
      constructor <;> nlinarith [sq_nonneg
        (((((j : ℕ) + 1 : ℕ) : ℝ) / m))]
  · exact hc

/-- Compact-rectangle perturbation lemma for the triangular northern ring
array.  The factor `d/m` kills the finitely many polar coefficients, while
uniform continuity handles all depths `d` beyond a fixed cutoff. -/
theorem tendsto_compactCoefficient_perturbation
    {α c E : ℝ} (hc : c ∈ Set.Icc (1 / 2 : ℝ) 4) (hE : 0 ≤ E)
    (A B : (m : ℕ) → Fin (m - 1) → ℝ)
    (hrect : ∀ m, 3 ≤ m → ∀ j,
      (A m j, B m j) ∈ squareCoefficientRectangle)
    (hAerr : ∀ m, 3 ≤ m → ∀ j,
      |A m j - squareLimitRadiusFactor m ((j : ℕ) + 1)| ≤
        1 / ((((j : ℕ) + 1 : ℕ) : ℝ)))
    (hBerr : ∀ m, 3 ≤ m → ∀ j,
      |B m j - c| ≤ E / ((((j : ℕ) + 1 : ℕ) : ℝ))) :
    Tendsto
      (fun m : ℕ ↦ (1 / (m : ℝ)) * ∑ j : Fin (m - 1),
        (((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
          (squareRingCoefficient α (A m j, B m j) -
            squareRingCoefficient α
              (squareLimitRadiusFactor m ((j : ℕ) + 1), c))))
      atTop (𝓝 0) := by
  have huc : UniformContinuousOn (squareRingCoefficient α)
      squareCoefficientRectangle :=
    isCompact_squareCoefficientRectangle.uniformContinuousOn_of_continuous
      (continuousOn_squareRingCoefficient α)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨C, hC⟩ := isCompact_squareCoefficientRectangle.bddAbove_image
    (continuousOn_squareRingCoefficient α).norm
  have hone : ((1 : ℝ), (1 : ℝ)) ∈ squareCoefficientRectangle := by
    constructor <;> constructor <;> norm_num
  have hC0 : 0 ≤ C :=
    (norm_nonneg (squareRingCoefficient α (1, 1))).trans
      (hC (Set.mem_image_of_mem _ hone))
  rw [Metric.tendsto_atTop]
  intro ε hε
  let η : ℝ := ε / 2
  have hη : 0 < η := half_pos hε
  obtain ⟨δ, hδ, hmod⟩ := huc η hη
  let Q : ℝ := max 1 E
  have hQ1 : 1 ≤ Q := le_max_left _ _
  have hQE : E ≤ Q := le_max_right _ _
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  obtain ⟨D, hD⟩ := exists_nat_gt (Q / δ)
  have hDpos : 0 < D := by
    have : (0 : ℝ) < (D : ℝ) :=
      lt_of_le_of_lt (div_nonneg hQ0.le hδ.le) hD
    exact_mod_cast this
  have hQD : Q / (D : ℝ) < δ := by
    rw [div_lt_iff₀ (by exact_mod_cast hDpos : (0 : ℝ) < D)]
    simpa [mul_comm] using (div_lt_iff₀ hδ).mp hD
  have hsmall : Tendsto (fun m : ℕ ↦
      (2 * C * (D : ℝ)) * (m : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_zero.comp
      tendsto_natCast_atTop_atTop).const_mul (2 * C * (D : ℝ)))
  have hevsmall : ∀ᶠ m : ℕ in atTop,
      (2 * C * (D : ℝ)) * (m : ℝ)⁻¹ < η :=
    hsmall.eventually (gt_mem_nhds hη)
  rw [eventually_atTop] at hevsmall
  obtain ⟨M, hM⟩ := hevsmall
  refine ⟨max M 3, fun m hm ↦ ?_⟩
  have hmM : M ≤ m := le_trans (le_max_left _ _) hm
  have hm3 : 3 ≤ m := le_trans (le_max_right _ _) hm
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hprefix : (2 * C * (D : ℝ)) * (m : ℝ)⁻¹ < η := hM m hmM
  have hterm (j : Fin (m - 1)) :
      |(((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
          (squareRingCoefficient α (A m j, B m j) -
            squareRingCoefficient α
              (squareLimitRadiusFactor m ((j : ℕ) + 1), c)))| ≤
        2 * C * (D : ℝ) / (m : ℝ) + η := by
    let d : ℕ := (j : ℕ) + 1
    let x : ℝ := (d : ℝ) / m
    let z : ℝ × ℝ := (A m j, B m j)
    let z₀ : ℝ × ℝ := (squareLimitRadiusFactor m d, c)
    have hz : z ∈ squareCoefficientRectangle := hrect m hm3 j
    have hz₀ : z₀ ∈ squareCoefficientRectangle := by
      exact squareLimitPair_mem_rectangle hc hmpos j
    have hdpos : 0 < d := by dsimp [d]; omega
    have hdle : d ≤ m := by dsimp [d]; omega
    have hx0 : 0 ≤ x := by dsimp [x]; positivity
    have hx1 : x ≤ 1 := by
      dsimp [x]
      rw [div_le_one hmR]
      exact_mod_cast hdle
    by_cases hbulk : D ≤ d
    · have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
      have hratio : Q / (d : ℝ) ≤ Q / (D : ℝ) := by
        exact div_le_div_of_nonneg_left hQ0.le hDR (by exact_mod_cast hbulk)
      have hAδ : |A m j - squareLimitRadiusFactor m d| < δ := by
        calc
          |A m j - squareLimitRadiusFactor m d| ≤ 1 / (d : ℝ) :=
            hAerr m hm3 j
          _ ≤ Q / (d : ℝ) := by
            exact div_le_div_of_nonneg_right hQ1 hdR.le
          _ ≤ Q / (D : ℝ) := hratio
          _ < δ := hQD
      have hBδ : |B m j - c| < δ := by
        calc
          |B m j - c| ≤ E / (d : ℝ) := hBerr m hm3 j
          _ ≤ Q / (d : ℝ) :=
            div_le_div_of_nonneg_right hQE hdR.le
          _ ≤ Q / (D : ℝ) := hratio
          _ < δ := hQD
      have hdist : dist z z₀ < δ := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        exact max_lt hAδ hBδ
      have hg : |squareRingCoefficient α z - squareRingCoefficient α z₀| < η := by
        simpa [Real.dist_eq] using hmod z hz z₀ hz₀ hdist
      rw [abs_mul]
      have : |x| ≤ 1 := by simpa [abs_of_nonneg hx0] using hx1
      calc
        |x| * |squareRingCoefficient α z - squareRingCoefficient α z₀| ≤
            1 * η := mul_le_mul this hg.le (abs_nonneg _) (by norm_num)
        _ ≤ 2 * C * (D : ℝ) / (m : ℝ) + η := by
          have : 0 ≤ 2 * C * (D : ℝ) / (m : ℝ) := by positivity
          linarith
    · have hdD : d < D := by omega
      have hG : |squareRingCoefficient α z| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC (Set.mem_image_of_mem _ hz)
      have hG₀ : |squareRingCoefficient α z₀| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC (Set.mem_image_of_mem _ hz₀)
      have hdiff : |squareRingCoefficient α z - squareRingCoefficient α z₀| ≤
          2 * C := by
        calc
          |_ - _| ≤ |squareRingCoefficient α z| + |squareRingCoefficient α z₀| :=
            abs_sub _ _
          _ ≤ C + C := add_le_add hG hG₀
          _ = 2 * C := by ring
      have hxD : x ≤ (D : ℝ) / m := by
        dsimp [x]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hdD.le) hmR.le
      rw [abs_mul, abs_of_nonneg hx0]
      calc
        x * |squareRingCoefficient α z - squareRingCoefficient α z₀| ≤
            ((D : ℝ) / m) * (2 * C) :=
          mul_le_mul hxD hdiff (abs_nonneg _) (by positivity)
        _ ≤ 2 * C * (D : ℝ) / (m : ℝ) + η := by
          have : ((D : ℝ) / m) * (2 * C) =
              2 * C * (D : ℝ) / (m : ℝ) := by ring
          rw [this]
          linarith
  change dist _ 0 < ε
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (one_div_pos.mpr hmR)]
  calc
    (1 / (m : ℝ)) * |∑ j : Fin (m - 1),
        (((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
          (squareRingCoefficient α (A m j, B m j) -
            squareRingCoefficient α
              (squareLimitRadiusFactor m ((j : ℕ) + 1), c)))| ≤
        (1 / (m : ℝ)) * ∑ j : Fin (m - 1),
          |(((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
            (squareRingCoefficient α (A m j, B m j) -
              squareRingCoefficient α
                (squareLimitRadiusFactor m ((j : ℕ) + 1), c)))| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 / (m : ℝ)) * ∑ _j : Fin (m - 1),
        (2 * C * (D : ℝ) / (m : ℝ) + η) := by
      gcongr with j
      exact hterm j
    _ ≤ 2 * C * (D : ℝ) / (m : ℝ) + η := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hcard : (((m - 1 : ℕ) : ℝ)) ≤ m := by exact_mod_cast Nat.sub_le m 1
      calc
        (1 / (m : ℝ)) * ((m - 1 : ℕ) *
            (2 * C * (D : ℝ) / (m : ℝ) + η)) ≤
            (1 / (m : ℝ)) * ((m : ℝ) *
              (2 * C * (D : ℝ) / (m : ℝ) + η)) := by
                gcongr
        _ = 2 * C * (D : ℝ) / (m : ℝ) + η := by field_simp
    _ < ε := by
      have heq : 2 * C * (D : ℝ) / (m : ℝ) =
          (2 * C * (D : ℝ)) * (m : ℝ)⁻¹ := by field_simp
      rw [heq]
      dsimp [η] at hprefix ⊢
      linarith

/-! ## Finite reflection algebra -/

theorem sum_range_two_mul_add_one_of_reflect
    (f : ℕ → ℝ) (k : ℕ)
    (href : ∀ j < k, f (k + 1 + j) = f (k - 1 - j)) :
    (∑ j ∈ Finset.range (2 * k + 1), f j) =
      2 * (∑ j ∈ Finset.range k, f j) + f k := by
  have htail :
      (∑ j ∈ Finset.range k, f (k + 1 + j)) =
        ∑ j ∈ Finset.range k, f j := by
    calc
      (∑ j ∈ Finset.range k, f (k + 1 + j)) =
          ∑ j ∈ Finset.range k, f (k - 1 - j) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact href j (Finset.mem_range.mp hj)
      _ = ∑ j ∈ Finset.range k, f j := Finset.sum_range_reflect f k
  rw [show 2 * k + 1 = (k + 1) + k by omega,
    Finset.sum_range_add, Finset.sum_range_succ, htail]
  ring

theorem sum_fin_two_mul_add_one_of_reflect
    (f : Fin (2 * k + 1) → ℝ)
    (href : ∀ j : Fin k,
      f ⟨k + 1 + (j : ℕ), by omega⟩ = f ⟨k - 1 - (j : ℕ), by omega⟩) :
    (∑ j, f j) =
      2 * (∑ j : Fin k, f ⟨(j : ℕ), by omega⟩) + f ⟨k, by omega⟩ := by
  let e : Fin (2 * k + 1) ≃ Fin ((k + 1) + k) := finCongr (by omega)
  let g : Fin ((k + 1) + k) → ℝ := fun i ↦ f (e.symm i)
  have hall : (∑ j, f j) = ∑ i, g i := by
    simpa [g] using (Equiv.sum_comp e.symm f).symm
  have hsplit := Fin.sum_univ_add (a := k + 1) (b := k) g
  let a : Fin (k + 1) → ℝ := fun i ↦ g (Fin.castAdd k i)
  have hfirst := Fin.sum_univ_castSucc a
  have hsouth :
      (∑ i : Fin k, g (Fin.natAdd (k + 1) i)) =
        ∑ i : Fin k, a i.castSucc := by
    calc
      (∑ i : Fin k, g (Fin.natAdd (k + 1) i)) =
          ∑ i : Fin k, g (Fin.natAdd (k + 1) (Fin.rev i)) := by
            exact (Equiv.sum_comp Fin.revPerm
              (fun i : Fin k ↦ g (Fin.natAdd (k + 1) i))).symm
      _ = ∑ i : Fin k, g (Fin.castAdd k i) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [g, e]
        convert href (Fin.rev i) using 1 <;> congr 1 <;>
          apply Fin.ext <;> simp [Fin.rev] <;> omega
      _ = ∑ i : Fin k, a i.castSucc := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [a]
        congr 1
        apply Fin.ext
        simp
  have hnorthcast :
      (∑ i : Fin k, a i.castSucc) =
        ∑ j : Fin k, f ⟨(j : ℕ), by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a, g, e]
    congr 1
  have hcenter : a (Fin.last k) = f ⟨k, by omega⟩ := by
    dsimp [a, g, e]
    congr 1
  rw [hall, hsplit]
  change (∑ i, a i) + _ = _
  rw [hfirst, hsouth, hnorthcast, hcenter]
  ring

theorem sum_fin_two_mul_of_reflect
    (f : Fin (2 * k) → ℝ)
    (href : ∀ j : Fin k,
      f ⟨k + (j : ℕ), by omega⟩ = f ⟨k - 1 - (j : ℕ), by omega⟩) :
    (∑ j, f j) = 2 * (∑ j : Fin k, f ⟨(j : ℕ), by omega⟩) := by
  let e : Fin (2 * k) ≃ Fin (k + k) := finCongr (by omega)
  let g : Fin (k + k) → ℝ := fun i ↦ f (e.symm i)
  have hall : (∑ j, f j) = ∑ i, g i := by
    simpa [g] using (Equiv.sum_comp e.symm f).symm
  have hsplit := Fin.sum_univ_add (a := k) (b := k) g
  let a : Fin k → ℝ := fun i ↦ g (Fin.castAdd k i)
  have hsouth :
      (∑ i : Fin k, g (Fin.natAdd k i)) = ∑ i : Fin k, a i := by
    calc
      (∑ i : Fin k, g (Fin.natAdd k i)) =
          ∑ i : Fin k, g (Fin.natAdd k (Fin.rev i)) := by
            exact (Equiv.sum_comp Fin.revPerm
              (fun i : Fin k ↦ g (Fin.natAdd k i))).symm
      _ = ∑ i : Fin k, g (Fin.castAdd k i) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [g, e]
        convert href (Fin.rev i) using 1 <;> congr 1 <;>
          apply Fin.ext <;> simp [Fin.rev] <;> omega
      _ = ∑ i : Fin k, a i := by rfl
  have hnorth : (∑ i : Fin k, a i) =
      ∑ j : Fin k, f ⟨(j : ℕ), by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [a, g, e]
    congr 1
  rw [hall, hsplit]
  change (∑ i, a i) + _ = _
  rw [hsouth, hnorth]
  ring

/-! ## Exact square-subsequence decomposition -/

noncomputable def squareMidpointWeightedTerm (α : ℝ) (m : ℕ)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1)) : ℝ :=
  (bemocRingFamily (4 * m ^ 2) (Sum.inl j)).radius ^ α *
    (midpointRingPopulation (4 * m ^ 2) j : ℝ) ^ (1 - α)

noncomputable def squareBoundaryWeightedTerm (α : ℝ) (m : ℕ)
    (j : Fin (bandTailCount (4 * m ^ 2))) : ℝ :=
  (bemocRingFamily (4 * m ^ 2) (Sum.inr j)).radius ^ α *
    (sharedBoundaryPopulation (4 * m ^ 2) j : ℝ) ^ (1 - α)

def squareNorthMidpointIndex (m : ℕ) (j : Fin (m - 1)) :
    Fin (bandTailCount (4 * m ^ 2) + 1) :=
  ⟨(j : ℕ), by simp; omega⟩

def squareNorthBoundaryIndex (m : ℕ) (j : Fin (m - 1)) :
    Fin (bandTailCount (4 * m ^ 2)) :=
  ⟨(j : ℕ), by simp; omega⟩

@[simp] theorem squareNorthMidpointIndex_val (m : ℕ) (j : Fin (m - 1)) :
    (squareNorthMidpointIndex m j : ℕ) = j := rfl

@[simp] theorem squareNorthBoundaryIndex_val (m : ℕ) (j : Fin (m - 1)) :
    (squareNorthBoundaryIndex m j : ℕ) = j := rfl

theorem square_midpointWeightedTerm_reflect (α : ℝ) {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2) + 1)) :
    squareMidpointWeightedTerm α m (squareReflectBandIndex m j) =
      squareMidpointWeightedTerm α m j := by
  unfold squareMidpointWeightedTerm
  rw [squareReflectBandIndex,
    concrete_midpoint_radius_reflect (by positivity : 0 < 4 * m ^ 2),
    concrete_midpointRingPopulation_reflect]

theorem square_boundaryWeightedTerm_reflect (α : ℝ) {m : ℕ} (hm : 0 < m)
    (j : Fin (bandTailCount (4 * m ^ 2))) :
    squareBoundaryWeightedTerm α m
        (concreteReflectBoundaryIndex (4 * m ^ 2) j) =
      squareBoundaryWeightedTerm α m j := by
  unfold squareBoundaryWeightedTerm
  rw [concrete_shared_radius_reflect (by positivity : 0 < 4 * m ^ 2),
    concrete_sharedBoundaryPopulation_reflect]

theorem sum_squareMidpointWeightedTerm_decomposition
    (α : ℝ) {m : ℕ} (hm : 0 < m) :
    (∑ j, squareMidpointWeightedTerm α m j) =
      2 * (∑ j : Fin (m - 1),
        squareMidpointWeightedTerm α m (squareNorthMidpointIndex m j)) +
      squareMidpointWeightedTerm α m (squareCentralBandIndex m) := by
  let f : Fin (2 * (m - 1) + 1) → ℝ := fun j ↦
    squareMidpointWeightedTerm α m
      ⟨(j : ℕ), by simpa using j.isLt⟩
  have href (j : Fin (m - 1)) :
      f ⟨(m - 1) + 1 + (j : ℕ), by omega⟩ =
        f ⟨(m - 1) - 1 - (j : ℕ), by omega⟩ := by
    let js : Fin (bandTailCount (4 * m ^ 2) + 1) :=
      ⟨(m - 1) + 1 + (j : ℕ), by simp; omega⟩
    have hr : squareReflectBandIndex m js =
        ⟨(m - 1) - 1 - (j : ℕ), by simp; omega⟩ := by
      apply Fin.ext
      simp [js]
      omega
    dsimp [f, js] at hr ⊢
    rw [← hr, square_midpointWeightedTerm_reflect α hm]
  have h := sum_fin_two_mul_add_one_of_reflect f href
  let e : Fin (bandTailCount (4 * m ^ 2) + 1) ≃
      Fin (2 * (m - 1) + 1) := finCongr (by simp)
  have hall : (∑ j, squareMidpointWeightedTerm α m j) = ∑ j, f j := by
    apply Fintype.sum_equiv e
    intro j
    dsimp [f, e]
  rw [hall]
  convert h using 1
  all_goals simp [f, squareNorthMidpointIndex, squareCentralBandIndex]
  congr 1
  apply Fin.ext
  simp [squareCentralBandIndex, concreteCentralBandIndex]

theorem sum_squareBoundaryWeightedTerm_decomposition
    (α : ℝ) {m : ℕ} (hm : 0 < m) :
    (∑ j, squareBoundaryWeightedTerm α m j) =
      2 * (∑ j : Fin (m - 1),
        squareBoundaryWeightedTerm α m (squareNorthBoundaryIndex m j)) := by
  let f : Fin (2 * (m - 1)) → ℝ := fun j ↦
    squareBoundaryWeightedTerm α m
      ⟨(j : ℕ), by simpa using j.isLt⟩
  have href (j : Fin (m - 1)) :
      f ⟨(m - 1) + (j : ℕ), by omega⟩ =
        f ⟨(m - 1) - 1 - (j : ℕ), by omega⟩ := by
    let js : Fin (bandTailCount (4 * m ^ 2)) :=
      ⟨(m - 1) + (j : ℕ), by simp; omega⟩
    have hr : concreteReflectBoundaryIndex (4 * m ^ 2) js =
        ⟨(m - 1) - 1 - (j : ℕ), by simp; omega⟩ := by
      apply Fin.ext
      simp [concreteReflectBoundaryIndex, js]
      omega
    dsimp [f, js] at hr ⊢
    rw [← hr, square_boundaryWeightedTerm_reflect α hm]
  have h := sum_fin_two_mul_of_reflect f href
  let e : Fin (bandTailCount (4 * m ^ 2)) ≃ Fin (2 * (m - 1)) :=
    finCongr (by simp)
  have hall : (∑ j, squareBoundaryWeightedTerm α m j) = ∑ j, f j := by
    apply Fintype.sum_equiv e
    intro j
    dsimp [f, e]
  rw [hall]
  convert h using 1 <;> simp [f, squareNorthBoundaryIndex]

theorem bemocWeightedRadiusPopulationSum_square_decomposition
    (α : ℝ) {m : ℕ} (hm : 0 < m) :
    bemocWeightedRadiusPopulationSum α (4 * m ^ 2) =
      2 * (∑ j : Fin (m - 1),
        squareMidpointWeightedTerm α m (squareNorthMidpointIndex m j)) +
      squareMidpointWeightedTerm α m (squareCentralBandIndex m) +
      2 * (∑ j : Fin (m - 1),
        squareBoundaryWeightedTerm α m (squareNorthBoundaryIndex m j)) := by
  unfold bemocWeightedRadiusPopulationSum
  rw [Fintype.sum_sum_type]
  change (∑ j, squareMidpointWeightedTerm α m j) +
      (∑ j, squareBoundaryWeightedTerm α m j) = _
  rw [sum_squareMidpointWeightedTerm_decomposition α hm,
    sum_squareBoundaryWeightedTerm_decomposition α hm]

/-- The common limiting profile of a northern midpoint or shared-boundary
ring, after its radius and population powers are combined. -/
noncomputable def withinRingGeometricProfile (α x : ℝ) : ℝ :=
  x * (2 - x ^ 2) ^ (α / 2)

theorem continuous_withinRingGeometricProfile {α : ℝ} (hα : 0 < α) :
    Continuous (withinRingGeometricProfile α) := by
  unfold withinRingGeometricProfile
  exact continuous_id.mul
    ((continuous_const.sub (continuous_id.pow 2)).rpow_const
      (fun _ ↦ Or.inr (by positivity : 0 ≤ α / 2)))

/-- The elementary integral supplying the geometric constant. -/
theorem integral_withinRingGeometricProfile {α : ℝ} (hα0 : 0 < α) :
    (∫ x in (0 : ℝ)..1, withinRingGeometricProfile α x) =
      (2 ^ (1 + α / 2) - 1) / (α + 2) := by
  let F : ℝ → ℝ := fun x ↦ -(2 - x ^ 2) ^ (1 + α / 2) / (α + 2)
  have hden : α + 2 ≠ 0 := by linarith
  have hderiv (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt F (withinRingGeometricProfile α x) x := by
    have hbase : 0 < 2 - x ^ 2 := by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      nlinarith [hx.1, hx.2]
    have hb : HasDerivAt (fun y : ℝ ↦ 2 - y ^ 2) (-2 * x) x := by
      convert (hasDerivAt_const x 2).sub ((hasDerivAt_id x).pow 2) using 1 <;>
        simp <;> ring
    dsimp [F, withinRingGeometricProfile]
    convert ((hb.rpow_const (p := 1 + α / 2) (Or.inl hbase.ne')).neg.div_const
        (α + 2)) using 1 <;> field_simp <;> ring
  have hint : IntervalIntegrable (withinRingGeometricProfile α)
      MeasureTheory.volume 0 1 :=
    (continuous_withinRingGeometricProfile hα0).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc]
  dsimp [F]
  rw [show (2 - (1 : ℝ) ^ 2) = 1 by norm_num,
    show (2 - (0 : ℝ) ^ 2) = 2 by norm_num, Real.one_rpow]
  field_simp
  ring

/-- The unweighted profile Riemann sum, in the indexing convention `d=k+1`
used by northern BEMOC rings. -/
theorem tendsto_withinRingGeometricProfile_riemann {α : ℝ} (hα0 : 0 < α) :
    Tendsto
      (fun m : ℕ ↦
        (1 / (m : ℝ)) * ∑ k ∈ Finset.range m,
          withinRingGeometricProfile α ((k : ℝ) / (m : ℝ)))
      atTop (𝓝 ((2 ^ (1 + α / 2) - 1) / (α + 2))) := by
  simpa [integral_withinRingGeometricProfile hα0] using
    tendsto_leftEndpointRiemannSum_atTop_integral
      (continuous_withinRingGeometricProfile hα0)

noncomputable def positiveGridModelSum (α c : ℝ) (m : ℕ) : ℝ :=
  c ^ (1 - α) *
    ((1 / (m : ℝ)) * ∑ j : Fin (m - 1),
      withinRingGeometricProfile α
        (((((j : ℕ) + 1 : ℕ) : ℝ)) / (m : ℝ)))

theorem positiveGridModelSum_eq_range {α c : ℝ} {m : ℕ} (hm : 0 < m) :
    positiveGridModelSum α c m =
      c ^ (1 - α) *
        ((1 / (m : ℝ)) * ∑ k ∈ Finset.range m,
          withinRingGeometricProfile α ((k : ℝ) / (m : ℝ))) := by
  unfold positiveGridModelSum
  have hnat : m = (m - 1) + 1 := by omega
  have hfin :
      (∑ j : Fin (m - 1), withinRingGeometricProfile α
          (((((j : ℕ) + 1 : ℕ) : ℝ)) / (m : ℝ))) =
        ∑ k ∈ Finset.range (m - 1),
          withinRingGeometricProfile α ((((k + 1 : ℕ) : ℝ)) / (m : ℝ)) := by
    simpa using Fin.sum_univ_eq_sum_range
      (fun k : ℕ ↦ withinRingGeometricProfile α
        ((((k + 1 : ℕ) : ℝ)) / (m : ℝ))) (m - 1)
  rw [hfin, hnat, Finset.sum_range_succ']
  simp [withinRingGeometricProfile]

theorem tendsto_positiveGridModelSum {α c : ℝ} (hα0 : 0 < α) :
    Tendsto (positiveGridModelSum α c) atTop
      (𝓝 (c ^ (1 - α) *
        ((2 ^ (1 + α / 2) - 1) / (α + 2)))) := by
  have h := (tendsto_withinRingGeometricProfile_riemann hα0).const_mul
    (c ^ (1 - α))
  apply h.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hm ↦ hm⟩] with m hm
  exact (positiveGridModelSum_eq_range (α := α) (c := c)
    (by omega : 0 < m)).symm

/-! ## Actual northern coefficient arrays -/

noncomputable def squareMidpointRadiusCoefficient (m : ℕ) (j : Fin (m - 1)) : ℝ :=
  (bemocRingFamily (4 * m ^ 2)
      (Sum.inl (squareNorthMidpointIndex m j))).radius /
    (((((j : ℕ) + 1 : ℕ) : ℝ)) / m)

noncomputable def squareMidpointPopulationCoefficient
    (m : ℕ) (j : Fin (m - 1)) : ℝ :=
  (midpointRingPopulation (4 * m ^ 2) (squareNorthMidpointIndex m j) : ℝ) /
    ((((j : ℕ) + 1 : ℕ) : ℝ))

noncomputable def squareBoundaryRadiusCoefficient (m : ℕ) (j : Fin (m - 1)) : ℝ :=
  (bemocRingFamily (4 * m ^ 2)
      (Sum.inr (squareNorthBoundaryIndex m j))).radius /
    (((((j : ℕ) + 1 : ℕ) : ℝ)) / m)

noncomputable def squareBoundaryPopulationCoefficient
    (m : ℕ) (j : Fin (m - 1)) : ℝ :=
  (sharedBoundaryPopulation (4 * m ^ 2) (squareNorthBoundaryIndex m j) : ℝ) /
    ((((j : ℕ) + 1 : ℕ) : ℝ))

/-- The central-adjacent boundary is replaced by its limiting population
coefficient.  It is restored later as one uniformly bounded exceptional term. -/
noncomputable def squareBoundaryBulkPopulationCoefficient
    (m : ℕ) (j : Fin (m - 1)) : ℝ :=
  if (j : ℕ) < m - 2 then
    (sharedBoundaryPopulation (4 * m ^ 2)
      (squareNorthBoundaryIndex m j) : ℝ) /
        ((((j : ℕ) + 1 : ℕ) : ℝ))
  else (4 / 3 : ℝ)

theorem squareMidpointCoefficient_mem_rectangle {m : ℕ} (hm : 3 ≤ m)
    (j : Fin (m - 1)) :
    (squareMidpointRadiusCoefficient m j,
      squareMidpointPopulationCoefficient m j) ∈ squareCoefficientRectangle := by
  let ji := squareNorthMidpointIndex m j
  let d : ℕ := (j : ℕ) + 1
  have hj : (ji : ℕ) < m - 1 := by dsimp [ji]; exact j.isLt
  have hdpos : (0 : ℝ) < d := by positivity
  have hr := square_midpoint_radius_ratio_bounds (m := m) (by omega) ji hj
  have hp := square_midpointRingPopulation_north_error (m := m) ji hj
  have hpNat : 2 * d ≤ midpointRingPopulation (4 * m ^ 2) ji := by
    have := concrete_midpoint_population_two_mul_index_le ji (by simpa using hj)
    simpa [ji, d] using this
  have hpL : (1 / 2 : ℝ) ≤
      (midpointRingPopulation (4 * m ^ 2) ji : ℝ) / d := by
    rw [le_div_iff₀ hdpos]
    have hpNatR : (2 : ℝ) * d ≤
        (midpointRingPopulation (4 * m ^ 2) ji : ℝ) := by exact_mod_cast hpNat
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    nlinarith
  have hpU : (midpointRingPopulation (4 * m ^ 2) ji : ℝ) / d ≤ 4 := by
    rw [div_le_iff₀ hdpos]
    rw [abs_le] at hp
    simp [ji, d] at hp ⊢
    nlinarith
  exact ⟨by simpa [squareMidpointRadiusCoefficient, ji] using hr,
    by simpa [squareMidpointPopulationCoefficient, ji, d] using
      (show (1 / 2 : ℝ) ≤
          (midpointRingPopulation (4 * m ^ 2) ji : ℝ) / d ∧
        (midpointRingPopulation (4 * m ^ 2) ji : ℝ) / d ≤ 4 from ⟨hpL, hpU⟩)⟩

theorem squareBoundaryBulkCoefficient_mem_rectangle {m : ℕ} (hm : 3 ≤ m)
    (j : Fin (m - 1)) :
    (squareBoundaryRadiusCoefficient m j,
      squareBoundaryBulkPopulationCoefficient m j) ∈ squareCoefficientRectangle := by
  let ji := squareNorthBoundaryIndex m j
  let d : ℕ := (j : ℕ) + 1
  have hj : (ji : ℕ) < m - 1 := by dsimp [ji]; exact j.isLt
  have hdpos : (0 : ℝ) < d := by positivity
  have hr := square_boundary_radius_ratio_bounds (m := m) (by omega) ji hj
  constructor
  · exact ⟨hr.1.trans' (by norm_num), hr.2⟩
  · unfold squareBoundaryBulkPopulationCoefficient
    split_ifs with hbulk
    · have hp := square_sharedBoundaryPopulation_north_error (m := m) ji (by
        dsimp [ji] at hbulk ⊢
        exact hbulk)
      have hpNat : d ≤ sharedBoundaryPopulation (4 * m ^ 2) ji := by
        apply concrete_shared_population_index_le_ordinary ji
        simpa [ji, d] using hbulk
      constructor
      · change (1 / 2 : ℝ) ≤
            (sharedBoundaryPopulation (4 * m ^ 2) ji : ℝ) / d
        rw [le_div_iff₀ hdpos]
        have hpNatR : (d : ℝ) ≤
            (sharedBoundaryPopulation (4 * m ^ 2) ji : ℝ) := by exact_mod_cast hpNat
        linarith [show (0 : ℝ) ≤ d by positivity]
      · change (sharedBoundaryPopulation (4 * m ^ 2) ji : ℝ) / d ≤ 4
        rw [div_le_iff₀ hdpos]
        rw [abs_le] at hp
        simp [ji, d] at hp ⊢
        nlinarith
    · constructor <;> norm_num

theorem squareMidpointRadiusCoefficient_error {m : ℕ} (hm : 3 ≤ m)
    (j : Fin (m - 1)) :
    |squareMidpointRadiusCoefficient m j -
        squareLimitRadiusFactor m ((j : ℕ) + 1)| ≤
      1 / ((((j : ℕ) + 1 : ℕ) : ℝ)) := by
  exact square_midpoint_radius_factor_error (m := m) (by omega)
    (squareNorthMidpointIndex m j) (by exact j.isLt)

theorem squareBoundaryRadiusCoefficient_error {m : ℕ} (hm : 3 ≤ m)
    (j : Fin (m - 1)) :
    |squareBoundaryRadiusCoefficient m j -
        squareLimitRadiusFactor m ((j : ℕ) + 1)| ≤
      1 / ((((j : ℕ) + 1 : ℕ) : ℝ)) := by
  exact square_boundary_radius_factor_error (m := m) (by omega)
    (squareNorthBoundaryIndex m j) (by exact j.isLt)

theorem squareMidpointPopulationCoefficient_error {m : ℕ} (hm : 3 ≤ m)
    (j : Fin (m - 1)) :
    |squareMidpointPopulationCoefficient m j - (8 / 3 : ℝ)| ≤
      1 / ((((j : ℕ) + 1 : ℕ) : ℝ)) := by
  let ji := squareNorthMidpointIndex m j
  let d : ℕ := (j : ℕ) + 1
  have hdpos : (0 : ℝ) < d := by positivity
  have hp := square_midpointRingPopulation_north_error (m := m) ji (by
    dsimp [ji]
    exact j.isLt)
  unfold squareMidpointPopulationCoefficient
  change |(midpointRingPopulation (4 * m ^ 2) ji : ℝ) / d - 8 / 3| ≤ 1 / d
  rw [show (midpointRingPopulation (4 * m ^ 2) ji : ℝ) / d - 8 / 3 =
      ((midpointRingPopulation (4 * m ^ 2) ji : ℝ) - (8 / 3) * d) / d by
        field_simp; ring,
    abs_div, abs_of_pos hdpos]
  exact (div_le_div_iff_of_pos_right hdpos).2 hp

theorem squareBoundaryBulkPopulationCoefficient_error {m : ℕ} (hm : 3 ≤ m)
    (j : Fin (m - 1)) :
    |squareBoundaryBulkPopulationCoefficient m j - (4 / 3 : ℝ)| ≤
      2 / ((((j : ℕ) + 1 : ℕ) : ℝ)) := by
  let ji := squareNorthBoundaryIndex m j
  let d : ℕ := (j : ℕ) + 1
  have hdpos : (0 : ℝ) < d := by positivity
  unfold squareBoundaryBulkPopulationCoefficient
  split_ifs with hbulk
  · have hp := square_sharedBoundaryPopulation_north_error (m := m) ji (by
      dsimp [ji] at hbulk ⊢
      exact hbulk)
    change |(sharedBoundaryPopulation (4 * m ^ 2) ji : ℝ) / d - 4 / 3| ≤ 2 / d
    rw [show (sharedBoundaryPopulation (4 * m ^ 2) ji : ℝ) / d - 4 / 3 =
        ((sharedBoundaryPopulation (4 * m ^ 2) ji : ℝ) - (4 / 3) * d) / d by
          field_simp; ring,
      abs_div, abs_of_pos hdpos]
    exact (div_le_div_iff_of_pos_right hdpos).2 hp
  · simp
    positivity

theorem squareNormalizedRingWeight_midpoint_factor {α : ℝ} {m : ℕ}
    (hm : 3 ≤ m) (j : Fin (m - 1)) :
    squareNormalizedRingWeight α m (Sum.inl (squareNorthMidpointIndex m j)) =
      (((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
        squareRingCoefficient α
          (squareMidpointRadiusCoefficient m j,
            squareMidpointPopulationCoefficient m j)) := by
  let x : ℝ := ((((j : ℕ) + 1 : ℕ) : ℝ) / m)
  let a := squareMidpointRadiusCoefficient m j
  let b := squareMidpointPopulationCoefficient m j
  have hx : 0 < x := by dsimp [x]; positivity
  have hab := squareMidpointCoefficient_mem_rectangle hm j
  have ha : 0 ≤ a := by dsimp [a]; linarith [hab.1.1]
  have hb : 0 ≤ b := by dsimp [b]; linarith [hab.2.1]
  have hr : (bemocRingFamily (4 * m ^ 2)
      (Sum.inl (squareNorthMidpointIndex m j))).radius = x * a := by
    dsimp [a, x, squareMidpointRadiusCoefficient]
    rw [mul_div_cancel₀ _ hx.ne']
  have hp : ((midpointRingPopulation (4 * m ^ 2)
      (squareNorthMidpointIndex m j) : ℝ) / m) = x * b := by
    dsimp [b, x, squareMidpointPopulationCoefficient]
    field_simp
    ring
  unfold squareNormalizedRingWeight squareRingCoefficient
  change (bemocRingFamily (4 * m ^ 2)
      (Sum.inl (squareNorthMidpointIndex m j))).radius ^ α *
      ((midpointRingPopulation (4 * m ^ 2)
        (squareNorthMidpointIndex m j) : ℝ) / m) ^ (1 - α) = _
  rw [hr, hp, Real.mul_rpow hx.le ha, Real.mul_rpow hx.le hb]
  calc
    x ^ α * a ^ α * (x ^ (1 - α) * b ^ (1 - α)) =
        (x ^ α * x ^ (1 - α)) * (a ^ α * b ^ (1 - α)) := by ring
    _ = x * (a ^ α * b ^ (1 - α)) := by
      rw [← Real.rpow_add hx α (1 - α),
        show α + (1 - α) = 1 by ring, Real.rpow_one]
    _ = _ := by rfl

theorem squareNormalizedRingWeight_boundary_factor {α : ℝ} {m : ℕ}
    (hm : 3 ≤ m) (j : Fin (m - 1)) :
    squareNormalizedRingWeight α m (Sum.inr (squareNorthBoundaryIndex m j)) =
      (((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
        squareRingCoefficient α
          (squareBoundaryRadiusCoefficient m j,
            squareBoundaryPopulationCoefficient m j)) := by
  let x : ℝ := ((((j : ℕ) + 1 : ℕ) : ℝ) / m)
  let a := squareBoundaryRadiusCoefficient m j
  let b := squareBoundaryPopulationCoefficient m j
  have hx : 0 < x := by dsimp [x]; positivity
  have hrange := square_boundary_radius_ratio_bounds (m := m) (by omega)
    (squareNorthBoundaryIndex m j) (by exact j.isLt)
  have ha : 0 ≤ a := by
    dsimp [a, squareBoundaryRadiusCoefficient]
    exact le_trans (by norm_num) hrange.1
  have hpNat : (j : ℕ) + 1 ≤ sharedBoundaryPopulation (4 * m ^ 2)
      (squareNorthBoundaryIndex m j) := by
    by_cases hbulk : (j : ℕ) < m - 2
    · exact concrete_shared_population_index_le_ordinary
        (N := 4 * m ^ 2) (j := squareNorthBoundaryIndex m j) (by
          simpa using hbulk)
    · exact concrete_shared_population_index_le_centralAdjacent
        (N := 4 * m ^ 2) (j := squareNorthBoundaryIndex m j)
        (by simpa using hm) (by simp; omega)
  have hb : 0 ≤ b := by
    dsimp [b, squareBoundaryPopulationCoefficient]
    positivity
  have hr : (bemocRingFamily (4 * m ^ 2)
      (Sum.inr (squareNorthBoundaryIndex m j))).radius = x * a := by
    dsimp [a, x, squareBoundaryRadiusCoefficient]
    rw [mul_div_cancel₀ _ hx.ne']
  have hp : ((sharedBoundaryPopulation (4 * m ^ 2)
      (squareNorthBoundaryIndex m j) : ℝ) / m) = x * b := by
    dsimp [b, x, squareBoundaryPopulationCoefficient]
    field_simp
    ring
  unfold squareNormalizedRingWeight squareRingCoefficient
  change (bemocRingFamily (4 * m ^ 2)
      (Sum.inr (squareNorthBoundaryIndex m j))).radius ^ α *
      ((sharedBoundaryPopulation (4 * m ^ 2)
        (squareNorthBoundaryIndex m j) : ℝ) / m) ^ (1 - α) = _
  rw [hr, hp, Real.mul_rpow hx.le ha, Real.mul_rpow hx.le hb]
  calc
    x ^ α * a ^ α * (x ^ (1 - α) * b ^ (1 - α)) =
        (x ^ α * x ^ (1 - α)) * (a ^ α * b ^ (1 - α)) := by ring
    _ = x * (a ^ α * b ^ (1 - α)) := by
      rw [← Real.rpow_add hx α (1 - α),
        show α + (1 - α) = 1 by ring, Real.rpow_one]
    _ = _ := by rfl

noncomputable def squareNorthernMidpointNormalizedSum (α : ℝ) (m : ℕ) : ℝ :=
  (1 / (m : ℝ)) * ∑ j : Fin (m - 1),
    squareNormalizedRingWeight α m (Sum.inl (squareNorthMidpointIndex m j))

noncomputable def squareNorthernBoundaryNormalizedSum (α : ℝ) (m : ℕ) : ℝ :=
  (1 / (m : ℝ)) * ∑ j : Fin (m - 1),
    squareNormalizedRingWeight α m (Sum.inr (squareNorthBoundaryIndex m j))

theorem squareRingCoefficient_limit_profile {α c : ℝ} {m : ℕ} (hm : 0 < m)
    (j : Fin (m - 1)) :
    (((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
      squareRingCoefficient α
        (squareLimitRadiusFactor m ((j : ℕ) + 1), c)) =
      c ^ (1 - α) * withinRingGeometricProfile α
        (((((j : ℕ) + 1 : ℕ) : ℝ) / m)) := by
  let x : ℝ := ((((j : ℕ) + 1 : ℕ) : ℝ) / m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    rw [div_le_one hmR]
    exact_mod_cast (show (j : ℕ) + 1 ≤ m by omega)
  have hb : 0 ≤ 2 - x ^ 2 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  unfold squareRingCoefficient withinRingGeometricProfile squareLimitRadiusFactor
  change x * ((Real.sqrt (2 - x ^ 2)) ^ α * c ^ (1 - α)) =
    c ^ (1 - α) * (x * (2 - x ^ 2) ^ (α / 2))
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hb]
  rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
  ring

noncomputable def squareMidpointCoefficientSum (α : ℝ) (m : ℕ) : ℝ :=
  (1 / (m : ℝ)) * ∑ j : Fin (m - 1),
    (((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
      squareRingCoefficient α
        (squareMidpointRadiusCoefficient m j,
          squareMidpointPopulationCoefficient m j))

noncomputable def squareBoundaryBulkCoefficientSum (α : ℝ) (m : ℕ) : ℝ :=
  (1 / (m : ℝ)) * ∑ j : Fin (m - 1),
    (((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
      squareRingCoefficient α
        (squareBoundaryRadiusCoefficient m j,
          squareBoundaryBulkPopulationCoefficient m j))

theorem tendsto_squareMidpointCoefficientSum {α : ℝ} (hα0 : 0 < α) :
    Tendsto (squareMidpointCoefficientSum α) atTop
      (𝓝 ((8 / 3 : ℝ) ^ (1 - α) *
        ((2 ^ (1 + α / 2) - 1) / (α + 2)))) := by
  have hp := tendsto_compactCoefficient_perturbation
    (α := α) (c := (8 / 3 : ℝ)) (E := 1)
    (by constructor <;> norm_num) (by norm_num)
    squareMidpointRadiusCoefficient squareMidpointPopulationCoefficient
    (fun m hm ↦ squareMidpointCoefficient_mem_rectangle hm)
    (fun m hm ↦ squareMidpointRadiusCoefficient_error hm)
    (fun m hm ↦ squareMidpointPopulationCoefficient_error hm)
  have hmodel := tendsto_positiveGridModelSum (α := α) (c := (8 / 3 : ℝ)) hα0
  have hadd := hp.add hmodel
  simp only [zero_add] at hadd
  apply hadd.congr'
  filter_upwards [eventually_atTop.2 ⟨3, fun _ hm ↦ hm⟩] with m hm
  have hmpos : 0 < m := by omega
  unfold squareMidpointCoefficientSum
  rw [positiveGridModelSum]
  have hmodelEq :
      (8 / 3 : ℝ) ^ (1 - α) *
          ((1 / (m : ℝ)) * ∑ j : Fin (m - 1),
            withinRingGeometricProfile α (((((j : ℕ) + 1 : ℕ) : ℝ)) / m)) =
        (1 / (m : ℝ)) * ∑ j : Fin (m - 1),
          ((((((j : ℕ) + 1 : ℕ) : ℝ)) / m) * squareRingCoefficient α
            (squareLimitRadiusFactor m ((j : ℕ) + 1), (8 / 3 : ℝ))) := by
    rw [show (8 / 3 : ℝ) ^ (1 - α) *
        ((1 / (m : ℝ)) * ∑ j : Fin (m - 1),
          withinRingGeometricProfile α (((((j : ℕ) + 1 : ℕ) : ℝ)) / m)) =
      (1 / (m : ℝ)) * ((8 / 3 : ℝ) ^ (1 - α) *
        ∑ j : Fin (m - 1), withinRingGeometricProfile α
          (((((j : ℕ) + 1 : ℕ) : ℝ)) / m)) by ring,
      Finset.mul_sum]
    apply congrArg (fun t : ℝ ↦ (1 / (m : ℝ)) * t)
    apply Finset.sum_congr rfl
    intro j _
    exact (squareRingCoefficient_limit_profile (α := α) (c := (8 / 3 : ℝ))
      hmpos j).symm
  rw [hmodelEq, ← mul_add, ← Finset.sum_add_distrib]
  apply congrArg (fun t : ℝ ↦ (1 / (m : ℝ)) * t)
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tendsto_squareBoundaryBulkCoefficientSum {α : ℝ} (hα0 : 0 < α) :
    Tendsto (squareBoundaryBulkCoefficientSum α) atTop
      (𝓝 ((4 / 3 : ℝ) ^ (1 - α) *
        ((2 ^ (1 + α / 2) - 1) / (α + 2)))) := by
  have hp := tendsto_compactCoefficient_perturbation
    (α := α) (c := (4 / 3 : ℝ)) (E := 2)
    (by constructor <;> norm_num) (by norm_num)
    squareBoundaryRadiusCoefficient squareBoundaryBulkPopulationCoefficient
    (fun m hm ↦ squareBoundaryBulkCoefficient_mem_rectangle hm)
    (fun m hm ↦ squareBoundaryRadiusCoefficient_error hm)
    (fun m hm ↦ squareBoundaryBulkPopulationCoefficient_error hm)
  have hmodel := tendsto_positiveGridModelSum (α := α) (c := (4 / 3 : ℝ)) hα0
  have hadd := hp.add hmodel
  simp only [zero_add] at hadd
  apply hadd.congr'
  filter_upwards [eventually_atTop.2 ⟨3, fun _ hm ↦ hm⟩] with m hm
  have hmpos : 0 < m := by omega
  unfold squareBoundaryBulkCoefficientSum
  rw [positiveGridModelSum]
  have hmodelEq :
      (4 / 3 : ℝ) ^ (1 - α) *
          ((1 / (m : ℝ)) * ∑ j : Fin (m - 1),
            withinRingGeometricProfile α (((((j : ℕ) + 1 : ℕ) : ℝ)) / m)) =
        (1 / (m : ℝ)) * ∑ j : Fin (m - 1),
          ((((((j : ℕ) + 1 : ℕ) : ℝ)) / m) * squareRingCoefficient α
            (squareLimitRadiusFactor m ((j : ℕ) + 1), (4 / 3 : ℝ))) := by
    rw [show (4 / 3 : ℝ) ^ (1 - α) *
        ((1 / (m : ℝ)) * ∑ j : Fin (m - 1),
          withinRingGeometricProfile α (((((j : ℕ) + 1 : ℕ) : ℝ)) / m)) =
      (1 / (m : ℝ)) * ((4 / 3 : ℝ) ^ (1 - α) *
        ∑ j : Fin (m - 1), withinRingGeometricProfile α
          (((((j : ℕ) + 1 : ℕ) : ℝ)) / m)) by ring,
      Finset.mul_sum]
    apply congrArg (fun t : ℝ ↦ (1 / (m : ℝ)) * t)
    apply Finset.sum_congr rfl
    intro j _
    exact (squareRingCoefficient_limit_profile (α := α) (c := (4 / 3 : ℝ))
      hmpos j).symm
  rw [hmodelEq, ← mul_add, ← Finset.sum_add_distrib]
  apply congrArg (fun t : ℝ ↦ (1 / (m : ℝ)) * t)
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Model northern midpoint contribution. -/
noncomputable def northernMidpointModelSum (α : ℝ) (m : ℕ) : ℝ :=
  (8 / 3 : ℝ) ^ (1 - α) *
    ((1 / (m : ℝ)) * ∑ k ∈ Finset.range m,
      withinRingGeometricProfile α ((k : ℝ) / (m : ℝ)))

/-- Model northern shared-boundary contribution. -/
noncomputable def northernBoundaryModelSum (α : ℝ) (m : ℕ) : ℝ :=
  (4 / 3 : ℝ) ^ (1 - α) *
    ((1 / (m : ℝ)) * ∑ k ∈ Finset.range m,
      withinRingGeometricProfile α ((k : ℝ) / (m : ℝ)))

theorem tendsto_northernMidpointModelSum {α : ℝ} (hα0 : 0 < α) :
    Tendsto (northernMidpointModelSum α) atTop
      (𝓝 ((8 / 3 : ℝ) ^ (1 - α) *
        ((2 ^ (1 + α / 2) - 1) / (α + 2)))) := by
  exact (tendsto_const_nhds.mul
    (tendsto_withinRingGeometricProfile_riemann hα0))

theorem tendsto_northernBoundaryModelSum {α : ℝ} (hα0 : 0 < α) :
    Tendsto (northernBoundaryModelSum α) atTop
      (𝓝 ((4 / 3 : ℝ) ^ (1 - α) *
        ((2 ^ (1 + α / 2) - 1) / (α + 2)))) := by
  exact (tendsto_const_nhds.mul
    (tendsto_withinRingGeometricProfile_riemann hα0))

theorem tendsto_northernModelSum {α : ℝ} (hα0 : 0 < α) :
    Tendsto
      (fun m ↦ northernMidpointModelSum α m + northernBoundaryModelSum α m)
      atTop (𝓝 (withinRingAsymptoticWeight α)) := by
  have h := (tendsto_northernMidpointModelSum hα0).add
    (tendsto_northernBoundaryModelSum hα0)
  convert h using 1
  unfold withinRingAsymptoticWeight
  ring

/-! ## Returning from coefficient arrays to literal ring weights -/

theorem squareNorthernMidpointNormalizedSum_eq_coefficientSum
    {α : ℝ} {m : ℕ} (hm : 3 ≤ m) :
    squareNorthernMidpointNormalizedSum α m = squareMidpointCoefficientSum α m := by
  unfold squareNorthernMidpointNormalizedSum squareMidpointCoefficientSum
  apply congrArg (fun t : ℝ ↦ (1 / (m : ℝ)) * t)
  apply Finset.sum_congr rfl
  intro j _
  exact squareNormalizedRingWeight_midpoint_factor hm j

noncomputable def squareBoundaryCoefficientSum (α : ℝ) (m : ℕ) : ℝ :=
  (1 / (m : ℝ)) * ∑ j : Fin (m - 1),
    (((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
      squareRingCoefficient α
        (squareBoundaryRadiusCoefficient m j,
          squareBoundaryPopulationCoefficient m j))

theorem squareNorthernBoundaryNormalizedSum_eq_coefficientSum
    {α : ℝ} {m : ℕ} (hm : 3 ≤ m) :
    squareNorthernBoundaryNormalizedSum α m = squareBoundaryCoefficientSum α m := by
  unfold squareNorthernBoundaryNormalizedSum squareBoundaryCoefficientSum
  apply congrArg (fun t : ℝ ↦ (1 / (m : ℝ)) * t)
  apply Finset.sum_congr rfl
  intro j _
  exact squareNormalizedRingWeight_boundary_factor hm j

theorem squareBoundaryCoefficient_mem_rectangle {m : ℕ} (hm : 3 ≤ m)
    (j : Fin (m - 1)) :
    (squareBoundaryRadiusCoefficient m j,
      squareBoundaryPopulationCoefficient m j) ∈ squareCoefficientRectangle := by
  let ji := squareNorthBoundaryIndex m j
  let d : ℕ := (j : ℕ) + 1
  have hj : (ji : ℕ) < m - 1 := by dsimp [ji]; exact j.isLt
  have hdpos : (0 : ℝ) < d := by positivity
  have hr := square_boundary_radius_ratio_bounds (m := m) (by omega) ji hj
  constructor
  · exact ⟨hr.1.trans' (by norm_num), hr.2⟩
  · by_cases hbulk : (j : ℕ) < m - 2
    · have hp := square_sharedBoundaryPopulation_north_error (m := m) ji (by
        dsimp [ji] at hbulk ⊢
        exact hbulk)
      have hpNat : d ≤ sharedBoundaryPopulation (4 * m ^ 2) ji := by
        apply concrete_shared_population_index_le_ordinary ji
        simpa [ji, d] using hbulk
      constructor
      · change (1 / 2 : ℝ) ≤
            (sharedBoundaryPopulation (4 * m ^ 2) ji : ℝ) / d
        rw [le_div_iff₀ hdpos]
        have hpNatR : (d : ℝ) ≤
            (sharedBoundaryPopulation (4 * m ^ 2) ji : ℝ) := by exact_mod_cast hpNat
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
        nlinarith
      · change (sharedBoundaryPopulation (4 * m ^ 2) ji : ℝ) / d ≤ 4
        rw [div_le_iff₀ hdpos]
        rw [abs_le] at hp
        simp [ji, d] at hp ⊢
        nlinarith
    · have hjlast : (j : ℕ) = m - 2 := by omega
      have hjEq : ji = squareNorthCentralBoundaryIndex m (by omega) := by
        apply Fin.ext
        simp [ji, hjlast]
      have hpop := square_sharedBoundaryPopulation_centralAdjacent
        (m := m) (by omega)
      rw [← hjEq] at hpop
      have hlowNat : d ≤ sharedBoundaryPopulation (4 * m ^ 2) ji := by
        apply concrete_shared_population_index_le_centralAdjacent
          (N := 4 * m ^ 2) (by simp; omega) ji
        simp [ji, hjlast]
      constructor
      · change (1 / 2 : ℝ) ≤
            (sharedBoundaryPopulation (4 * m ^ 2) ji : ℝ) / d
        rw [le_div_iff₀ hdpos]
        have hlowR : (d : ℝ) ≤
            (sharedBoundaryPopulation (4 * m ^ 2) ji : ℝ) := by exact_mod_cast hlowNat
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
        nlinarith
      · change (sharedBoundaryPopulation (4 * m ^ 2) ji : ℝ) / d ≤ 4
        rw [div_le_iff₀ hdpos]
        have hdiv : (4 * m - 5) / 6 ≤ 4 * m - 5 := Nat.div_le_self _ _
        have hpopNat : sharedBoundaryPopulation (4 * m ^ 2) ji ≤ 4 * d := by
          rw [hpop]
          dsimp [d]
          omega
        exact_mod_cast hpopNat

theorem exists_squareRingCoefficient_bound (α : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ squareCoefficientRectangle,
      |squareRingCoefficient α z| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_squareCoefficientRectangle.bddAbove_image
    (continuousOn_squareRingCoefficient α).norm
  have hone : ((1 : ℝ), (1 : ℝ)) ∈ squareCoefficientRectangle := by
    constructor <;> constructor <;> norm_num
  refine ⟨C, ?_, ?_⟩
  · exact (norm_nonneg (squareRingCoefficient α (1, 1))).trans
      (hC (Set.mem_image_of_mem _ hone))
  · intro z hz
    simpa only [Real.norm_eq_abs] using hC (Set.mem_image_of_mem _ hz)

theorem squareBoundaryCoefficientSum_sub_bulk_eq_exception
    {α : ℝ} {m : ℕ} (hm : 3 ≤ m) :
    squareBoundaryCoefficientSum α m - squareBoundaryBulkCoefficientSum α m =
      (1 / (m : ℝ)) *
        (let j₀ : Fin (m - 1) := ⟨m - 2, by omega⟩
         ((((j₀ : ℕ) + 1 : ℕ) : ℝ) / m) *
           (squareRingCoefficient α
             (squareBoundaryRadiusCoefficient m j₀,
               squareBoundaryPopulationCoefficient m j₀) -
             squareRingCoefficient α
               (squareBoundaryRadiusCoefficient m j₀,
                 squareBoundaryBulkPopulationCoefficient m j₀))) := by
  let j₀ : Fin (m - 1) := ⟨m - 2, by omega⟩
  let f : Fin (m - 1) → ℝ := fun j ↦
    (((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
      squareRingCoefficient α
        (squareBoundaryRadiusCoefficient m j,
          squareBoundaryPopulationCoefficient m j))
  let g : Fin (m - 1) → ℝ := fun j ↦
    (((((j : ℕ) + 1 : ℕ) : ℝ) / m) *
      squareRingCoefficient α
        (squareBoundaryRadiusCoefficient m j,
          squareBoundaryBulkPopulationCoefficient m j))
  have hfg (j : Fin (m - 1)) (hj : j ≠ j₀) : f j = g j := by
    have hjle : (j : ℕ) ≤ m - 2 := by omega
    have hjlt : (j : ℕ) < m - 2 := by
      by_contra hnot
      have : (j : ℕ) = m - 2 := by omega
      apply hj
      apply Fin.ext
      simpa [j₀] using this
    have hcoef : squareBoundaryBulkPopulationCoefficient m j =
        squareBoundaryPopulationCoefficient m j := by
      rw [squareBoundaryBulkPopulationCoefficient, if_pos hjlt,
        squareBoundaryPopulationCoefficient]
    simp [f, g, hcoef]
  have hsum : (∑ j, f j) - ∑ j, g j = f j₀ - g j₀ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_single j₀ (fun j _ hj ↦ sub_eq_zero.mpr (hfg j hj))
      (by simp)
  unfold squareBoundaryCoefficientSum squareBoundaryBulkCoefficientSum
  change (1 / (m : ℝ)) * (∑ j, f j) -
      (1 / (m : ℝ)) * (∑ j, g j) = _
  rw [← mul_sub, hsum]
  dsimp [f, g, j₀]
  ring

theorem tendsto_squareBoundaryCoefficientSum_sub_bulk {α : ℝ} :
    Tendsto (fun m : ℕ ↦
      squareBoundaryCoefficientSum α m - squareBoundaryBulkCoefficientSum α m)
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_squareRingCoefficient_bound α
  rw [tendsto_zero_iff_norm_tendsto_zero]
  change Tendsto (fun m : ℕ ↦
    |squareBoundaryCoefficientSum α m - squareBoundaryBulkCoefficientSum α m|)
    atTop (𝓝 0)
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ abs_nonneg _
  · filter_upwards [eventually_atTop.2 ⟨3, fun m hm ↦ hm⟩] with m hm
    rw [squareBoundaryCoefficientSum_sub_bulk_eq_exception hm]
    dsimp
    let j₀ : Fin (m - 1) := ⟨m - 2, by omega⟩
    let x : ℝ := ((((j₀ : ℕ) + 1 : ℕ) : ℝ) / m)
    let za : ℝ × ℝ :=
      (squareBoundaryRadiusCoefficient m j₀,
        squareBoundaryPopulationCoefficient m j₀)
    let zb : ℝ × ℝ :=
      (squareBoundaryRadiusCoefficient m j₀,
        squareBoundaryBulkPopulationCoefficient m j₀)
    have hza : za ∈ squareCoefficientRectangle :=
      squareBoundaryCoefficient_mem_rectangle hm j₀
    have hzb : zb ∈ squareCoefficientRectangle :=
      squareBoundaryBulkCoefficient_mem_rectangle hm j₀
    have hmpos : (0 : ℝ) < m := by positivity
    have hx0 : 0 ≤ x := by dsimp [x]; positivity
    have hx1 : x ≤ 1 := by
      dsimp [x, j₀]
      rw [div_le_one hmpos]
      exact_mod_cast (show m - 2 + 1 ≤ m by omega)
    have hdiff : |squareRingCoefficient α za - squareRingCoefficient α zb| ≤
        2 * C := by
      calc
        |_ - _| ≤ |squareRingCoefficient α za| + |squareRingCoefficient α zb| :=
          abs_sub _ _
        _ ≤ C + C := add_le_add (hC za hza) (hC zb hzb)
        _ = 2 * C := by ring
    change |(1 / (m : ℝ)) * (x *
      (squareRingCoefficient α za - squareRingCoefficient α zb))| ≤
        (2 * C / m)
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hmpos), abs_mul,
      abs_of_nonneg hx0]
    calc
      (1 / (m : ℝ)) * (x * |squareRingCoefficient α za - squareRingCoefficient α zb|) ≤
          (1 / (m : ℝ)) * (1 * (2 * C)) := by gcongr
      _ = 2 * C / m := by ring
  · exact tendsto_const_div_atTop_nhds_zero_nat (2 * C)

theorem tendsto_squareNorthernMidpointNormalizedSum {α : ℝ} (hα0 : 0 < α) :
    Tendsto (squareNorthernMidpointNormalizedSum α) atTop
      (𝓝 ((8 / 3 : ℝ) ^ (1 - α) *
        ((2 ^ (1 + α / 2) - 1) / (α + 2)))) := by
  apply (tendsto_squareMidpointCoefficientSum hα0).congr'
  filter_upwards [eventually_atTop.2 ⟨3, fun m hm ↦ hm⟩] with m hm
  exact (squareNorthernMidpointNormalizedSum_eq_coefficientSum hm).symm

theorem tendsto_squareNorthernBoundaryNormalizedSum {α : ℝ} (hα0 : 0 < α) :
    Tendsto (squareNorthernBoundaryNormalizedSum α) atTop
      (𝓝 ((4 / 3 : ℝ) ^ (1 - α) *
        ((2 ^ (1 + α / 2) - 1) / (α + 2)))) := by
  have hdiff := tendsto_squareBoundaryCoefficientSum_sub_bulk (α := α)
  have hbulk := tendsto_squareBoundaryBulkCoefficientSum hα0
  have hsum := hdiff.add hbulk
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [eventually_atTop.2 ⟨3, fun m hm ↦ hm⟩] with m hm
  rw [← squareNorthernBoundaryNormalizedSum_eq_coefficientSum hm]
  ring

theorem tendsto_squareNorthernNormalizedSum {α : ℝ} (hα0 : 0 < α) :
    Tendsto
      (fun m : ℕ ↦ squareNorthernMidpointNormalizedSum α m +
        squareNorthernBoundaryNormalizedSum α m)
      atTop (𝓝 (withinRingAsymptoticWeight α)) := by
  have h := (tendsto_squareNorthernMidpointNormalizedSum hα0).add
    (tendsto_squareNorthernBoundaryNormalizedSum hα0)
  convert h using 1
  unfold withinRingAsymptoticWeight
  ring

theorem bemocWeightedRadiusPopulationSum_div_scale_square_decomposition
    {α : ℝ} {m : ℕ} (hm : 3 ≤ m) :
    bemocWeightedRadiusPopulationSum α (4 * m ^ 2) / (m : ℝ) ^ (2 - α) =
      2 * squareNorthernMidpointNormalizedSum α m +
        squareCentralMidpointWeightedTerm α m / (m : ℝ) ^ (2 - α) +
      2 * squareNorthernBoundaryNormalizedSum α m := by
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hr : (m : ℝ) ^ (1 - α) ≠ 0 :=
    (Real.rpow_pos_of_pos hmR _).ne'
  have hpow : (m : ℝ) ^ (2 - α) =
      (m : ℝ) ^ (1 - α) * (m : ℝ) := by
    rw [show (2 - α : ℝ) = (1 - α) + 1 by ring,
      Real.rpow_add hmR, Real.rpow_one]
  have hmid (j : Fin (m - 1)) :
      squareMidpointWeightedTerm α m (squareNorthMidpointIndex m j) /
          (m : ℝ) ^ (1 - α) =
        squareNormalizedRingWeight α m
          (Sum.inl (squareNorthMidpointIndex m j)) := by
    simpa [squareMidpointWeightedTerm] using
      square_ring_weight_div_scale (α := α) hm0
        (Sum.inl (squareNorthMidpointIndex m j))
  have hboundary (j : Fin (m - 1)) :
      squareBoundaryWeightedTerm α m (squareNorthBoundaryIndex m j) /
          (m : ℝ) ^ (1 - α) =
        squareNormalizedRingWeight α m
          (Sum.inr (squareNorthBoundaryIndex m j)) := by
    simpa [squareBoundaryWeightedTerm] using
      square_ring_weight_div_scale (α := α) hm0
        (Sum.inr (squareNorthBoundaryIndex m j))
  have hmidSum :
      (∑ j : Fin (m - 1),
        squareMidpointWeightedTerm α m (squareNorthMidpointIndex m j)) /
          (m : ℝ) ^ (1 - α) =
        ∑ j : Fin (m - 1), squareNormalizedRingWeight α m
          (Sum.inl (squareNorthMidpointIndex m j)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    exact hmid j
  have hboundarySum :
      (∑ j : Fin (m - 1),
        squareBoundaryWeightedTerm α m (squareNorthBoundaryIndex m j)) /
          (m : ℝ) ^ (1 - α) =
        ∑ j : Fin (m - 1), squareNormalizedRingWeight α m
          (Sum.inr (squareNorthBoundaryIndex m j)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    exact hboundary j
  have hmidRaw :
      (∑ j : Fin (m - 1),
        squareMidpointWeightedTerm α m (squareNorthMidpointIndex m j)) =
      (m : ℝ) ^ (1 - α) *
        ∑ j : Fin (m - 1), squareNormalizedRingWeight α m
          (Sum.inl (squareNorthMidpointIndex m j)) := by
    calc
      (∑ j : Fin (m - 1),
          squareMidpointWeightedTerm α m (squareNorthMidpointIndex m j)) =
          (∑ j : Fin (m - 1), squareNormalizedRingWeight α m
            (Sum.inl (squareNorthMidpointIndex m j))) * (m : ℝ) ^ (1 - α) :=
        (div_eq_iff hr).mp hmidSum
      _ = _ := by ring
  have hboundaryRaw :
      (∑ j : Fin (m - 1),
        squareBoundaryWeightedTerm α m (squareNorthBoundaryIndex m j)) =
      (m : ℝ) ^ (1 - α) *
        ∑ j : Fin (m - 1), squareNormalizedRingWeight α m
          (Sum.inr (squareNorthBoundaryIndex m j)) := by
    calc
      (∑ j : Fin (m - 1),
          squareBoundaryWeightedTerm α m (squareNorthBoundaryIndex m j)) =
          (∑ j : Fin (m - 1), squareNormalizedRingWeight α m
            (Sum.inr (squareNorthBoundaryIndex m j))) * (m : ℝ) ^ (1 - α) :=
        (div_eq_iff hr).mp hboundarySum
      _ = _ := by ring
  rw [bemocWeightedRadiusPopulationSum_square_decomposition α hm0, hpow]
  rw [show squareMidpointWeightedTerm α m (squareCentralBandIndex m) =
      squareCentralMidpointWeightedTerm α m by rfl]
  rw [hmidRaw, hboundaryRaw]
  unfold squareNorthernMidpointNormalizedSum squareNorthernBoundaryNormalizedSum
  field_simp
  ring

theorem tendsto_bemocWeightedRadiusPopulationSum_four_mul_sq
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    Tendsto
      (fun m : ℕ ↦ bemocWeightedRadiusPopulationSum α (4 * m ^ 2) /
        (m : ℝ) ^ (2 - α))
      atTop (𝓝 (2 * withinRingAsymptoticWeight α)) := by
  have hcenter := tendsto_squareCentralMidpointWeightedTerm_div_scale hα0 hα2
  have hmid := tendsto_squareNorthernMidpointNormalizedSum hα0
  have hboundary := tendsto_squareNorthernBoundaryNormalizedSum hα0
  have h := ((hmid.const_mul 2).add hcenter).add (hboundary.const_mul 2)
  have hlim : Tendsto
      (fun m : ℕ ↦ 2 * squareNorthernMidpointNormalizedSum α m +
        squareCentralMidpointWeightedTerm α m / (m : ℝ) ^ (2 - α) +
        2 * squareNorthernBoundaryNormalizedSum α m)
      atTop (𝓝 (2 * withinRingAsymptoticWeight α)) := by
    convert h using 1 <;> unfold withinRingAsymptoticWeight <;> ring
  apply hlim.congr'
  filter_upwards [eventually_atTop.2 ⟨3, fun m hm ↦ hm⟩] with m hm
  exact (bemocWeightedRadiusPopulationSum_div_scale_square_decomposition hm).symm

end BEMOC
