import BEMOCFormalization.Core

open scoped BigOperators
namespace BEMOC.Definitive

/-- Integer version of `floor(sqrt(N/4))`; division here is natural-number division. -/
def bandParameter (N : ℕ) : ℕ := Nat.sqrt (N / 4)
/-- Population of a one-based band. Only indices `1,...,2M-1` are occupied. -/
def population (N j : ℕ) : ℕ :=
  let M := bandParameter N
  if j < M then 4 * j
  else if j = M then N - 4 * M * (M - 1)
  else 4 * (2 * M - j)
/-- Boundary heights, defined from cumulative populations, including `H₀=1`. -/
noncomputable def boundary (N j : ℕ) : ℝ :=
  1 - 2 / (N : ℝ) * ∑ k ∈ Finset.Icc 1 j, (population N k : ℝ)
/-- Midpoint height, defined from the boundaries. -/
noncomputable def height (N j : ℕ) : ℝ := (boundary N (j - 1) + boundary N j) / 2
/-- Radius of an occupied parallel. -/
noncomputable def radius (N j : ℕ) : ℝ := Real.sqrt (1 - height N j ^ 2)
/-- Closed height band; endpoints have zero Lebesgue mass. -/
def band (N j : ℕ) : Set ℝ := Set.Icc (boundary N j) (boundary N (j - 1))
/-- Zero-based finite band labels; add one to recover the manuscript index. -/
abbrev RingIndex (N : ℕ) := Fin (2 * bandParameter N - 1)
/-- Every polygon vertex has its own label. -/
abbrev PointIndex (N : ℕ) := Σ j : RingIndex N, Fin (population N (j.val + 1))
/-- Independent azimuthal phases on the occupied parallels. -/
abbrev Phases (N : ℕ) := RingIndex N → ℝ

/-- Total definition. The north-pole fallback is unreachable after proving `ConstructionFacts`. -/
noncomputable def point (N : ℕ) (φ : Phases N) (i : PointIndex N) : Sphere :=
  let j := i.1.val + 1
  if h : height N j ∈ Set.Icc (-1 : ℝ) 1 then
    parallelPoint (height N j)
      (φ i.1 + 2 * Real.pi * (i.2.val : ℝ) / (population N j : ℝ)) h
  else parallelPoint 1 0 (by norm_num)

/-- The exact finite energy of the new Diamond points. -/
noncomputable def diamondEnergy (α : ℝ) (N : ℕ) (φ : Phases N) : ℝ :=
  energy (point N φ) α

/-- The integer square-root parameter has exactly the manuscript's square bounds. -/
theorem bandParameter_bounds (N : ℕ) :
    4 * (bandParameter N) ^ 2 ≤ N ∧
      N < 4 * (bandParameter N + 1) ^ 2 := by
  have hlo := Nat.sqrt_le' (N / 4)
  have hhi := Nat.lt_succ_sqrt' (N / 4)
  have hmod := Nat.mod_lt N (by omega : 0 < 4)
  have hdiv := Nat.mod_add_div N 4
  have hlo' : 4 * (Nat.sqrt (N / 4)) ^ 2 ≤ 4 * (N / 4) :=
    Nat.mul_le_mul_left 4 hlo
  have hhi' : 4 * (N / 4) < 4 * (Nat.sqrt (N / 4) + 1) ^ 2 :=
    Nat.mul_lt_mul_of_pos_left (by simpa [Nat.succ_eq_add_one] using hhi) (by omega)
  dsimp [bandParameter]
  constructor <;> omega

/-- The construction has at least one ring from `N = 4` onwards. -/
theorem bandParameter_pos {N : ℕ} (hN : 4 ≤ N) : 1 ≤ bandParameter N := by
  have h : 1 ≤ N / 4 := by omega
  exact (Nat.le_sqrt').2 (by nlinarith)

/-- The equatorial population is an ordinary natural subtraction. -/
theorem central_population (N : ℕ) :
    population N (bandParameter N) =
      N - 4 * bandParameter N * (bandParameter N - 1) := by
  simp [population]

/-- Populations above the equator are exactly `4j`. -/
theorem north_population (N j : ℕ) (hj : j < bandParameter N) :
    population N j = 4 * j := by
  simp [population, hj]

/-- Populations below the equator are reflected northern populations. -/
theorem south_population (N j : ℕ) (hj : bandParameter N < j) :
    population N j = 4 * (2 * bandParameter N - j) := by
  simp [population, Nat.not_lt.mpr (Nat.le_of_lt hj), Nat.ne_of_gt hj]

/-- The center holds between four and fifteen times the ring parameter. -/
theorem central_population_bounds {N : ℕ} (hN : 4 ≤ N) :
    4 * bandParameter N ≤ population N (bandParameter N) ∧
      population N (bandParameter N) ≤ 12 * bandParameter N + 3 := by
  let M := bandParameter N
  have hM : 1 ≤ M := bandParameter_pos hN
  have hb := bandParameter_bounds N
  have hsub : M - 1 + 1 = M := by omega
  have hprod : 4 * M * (M - 1) + 4 * M = 4 * M ^ 2 := by
    nlinarith
  have htop : 4 * (M + 1) ^ 2 = 4 * M ^ 2 + 8 * M + 4 := by ring
  rw [central_population]
  dsimp [M] at *
  constructor <;> omega

/-- Sum of the ordinary northern populations, in real coordinates. -/
theorem north_population_sum (N : ℕ) :
    ∀ j : ℕ, j < bandParameter N →
      (∑ k ∈ Finset.Icc 1 j, (population N k : ℝ)) =
        2 * (j : ℝ) * (j + 1) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      intro hj
      have hj' : j < bandParameter N := by omega
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
      rw [ih hj', north_population N (j + 1) hj]
      push_cast
      ring

/-- Closed formula for northern band boundaries. -/
theorem north_boundary {N j : ℕ} (hN : 4 ≤ N) (hj : j < bandParameter N) :
    boundary N j = 1 - 4 * (j : ℝ) * (j + 1) / N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [boundary, north_population_sum N j hj]
  field_simp
  ring

/-- Closed formula for northern midpoint heights. -/
theorem north_height {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hjM : j < bandParameter N) :
    height N j = 1 - 4 * (j : ℝ) ^ 2 / N := by
  have hprev : j - 1 < bandParameter N := by omega
  have hsub : j - 1 + 1 = j := by omega
  rw [height, north_boundary hN hprev, north_boundary hN hjM]
  have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub hj1]
    norm_num
  rw [hcast]
  ring

/-- The central population completes the two northern halves. -/
theorem central_population_eq {N : ℕ} (hN : 4 ≤ N) :
    population N (bandParameter N) +
      4 * bandParameter N * (bandParameter N - 1) = N := by
  let M := bandParameter N
  have hM : 1 ≤ M := bandParameter_pos hN
  have hb := (bandParameter_bounds N).1
  have hsub : M - 1 + 1 = M := by omega
  have hprod : 4 * M * (M - 1) + 4 * M = 4 * M ^ 2 := by nlinarith
  rw [central_population]
  dsimp [M] at *
  omega

/-- The equatorial band really has midpoint height zero. -/
theorem central_height {N : ℕ} (hN : 4 ≤ N) :
    height N (bandParameter N) = 0 := by
  let M := bandParameter N
  have hM : 1 ≤ M := bandParameter_pos hN
  have hprev : M - 1 < M := by omega
  have hs := north_population_sum N (M - 1) hprev
  have hc := central_population_eq hN
  have hsum : (∑ k ∈ Finset.Icc 1 M, (population N k : ℝ)) =
      (∑ k ∈ Finset.Icc 1 (M - 1), (population N k : ℝ)) +
        population N M := by
    have hsub : M - 1 + 1 = M := by omega
    conv_lhs => rw [← hsub]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M - 1 + 1), hsub]
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub hM]
    norm_num
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  unfold height boundary
  change (1 - 2 / (N : ℝ) *
    ∑ k ∈ Finset.Icc 1 (M - 1), (population N k : ℝ) +
    (1 - 2 / (N : ℝ) * ∑ k ∈ Finset.Icc 1 M, (population N k : ℝ))) / 2 = 0
  rw [hs, hsum, hs, hcast]
  have hcr : (population N M : ℝ) + 4 * (M : ℝ) * ((M : ℝ) - 1) = N := by
    exact_mod_cast hc
  field_simp
  nlinarith

/-- Reflection across the equator preserves every occupied population. -/
theorem population_reflect {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    population N (2 * bandParameter N - j) = population N j := by
  let M := bandParameter N
  have hM : 1 ≤ M := bandParameter_pos hN
  change population N (2 * M - j) = population N j
  rcases lt_trichotomy j M with hlt | heq | hgt
  · have href : M < 2 * M - j := by omega
    rw [south_population N (2 * M - j) href, north_population N j hlt]
    omega
  · subst j
    have href : 2 * M - M = M := by omega
    rw [href]
  · have href : 2 * M - j < M := by omega
    rw [north_population N (2 * M - j) href, south_population N j hgt]

/-- The dependent polygon labels count exactly `N` vertices. -/
theorem population_sum_eq (N : ℕ) (hN : 4 ≤ N) :
    (∑ j : RingIndex N, population N (j.val + 1)) = N := by
  let M := bandParameter N
  have hM : 1 ≤ M := bandParameter_pos hN
  have hprev : M - 1 < M := by omega
  have hsub : M - 1 + 1 = M := by omega
  have hnorth : (∑ j ∈ Finset.Ico 1 M, population N j) = 2 * (M - 1) * M := by
    rw [← Nat.Icc_pred_right 1 (by omega : 0 < M)]
    have hs := north_population_sum N (M - 1) hprev
    have hsN : (∑ j ∈ Finset.Icc 1 (M - 1), population N j) =
        2 * (M - 1) * ((M - 1) + 1) := by exact_mod_cast hs
    simpa only [hsub] using hsN
  have hsouth : (∑ j ∈ Finset.Ico (M + 1) (2 * M), population N j) =
      ∑ j ∈ Finset.Ico 1 M, population N j := by
    have hr := Finset.sum_Ico_reflect (fun j => population N j) 1
      (m := M) (n := 2 * M) (by omega : M ≤ 2 * M + 1)
    have hleft : (∑ j ∈ Finset.Ico 1 M, population N (2 * M - j)) =
        ∑ j ∈ Finset.Ico 1 M, population N j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      exact population_reflect hN hj'.1 (by omega)
    have hstart : 2 * M + 1 - M = M + 1 := by omega
    have hend : 2 * M + 1 - 1 = 2 * M := by omega
    rw [hstart, hend] at hr
    exact hr.symm.trans hleft
  have hcenter : (∑ j ∈ Finset.Ico M (M + 1), population N j) =
      population N M := by simp
  have hsplit := Finset.sum_Ico_consecutive (fun j => population N j)
    (by omega : 1 ≤ M) (by omega : M ≤ M + 1)
  have hsplit' := Finset.sum_Ico_consecutive (fun j => population N j)
    (by omega : 1 ≤ M + 1) (by omega : M + 1 ≤ 2 * M)
  have htotal : (∑ j ∈ Finset.Ico 1 (2 * M), population N j) = N := by
    calc
      (∑ j ∈ Finset.Ico 1 (2 * M), population N j) =
          (∑ j ∈ Finset.Ico 1 (M + 1), population N j) +
            (∑ j ∈ Finset.Ico (M + 1) (2 * M), population N j) := hsplit'.symm
      _ = ((∑ j ∈ Finset.Ico 1 M, population N j) +
            (∑ j ∈ Finset.Ico M (M + 1), population N j)) +
              (∑ j ∈ Finset.Ico (M + 1) (2 * M), population N j) := by rw [hsplit]
      _ = N := by
        rw [hcenter, hsouth, hnorth]
        have hc := central_population_eq hN
        dsimp [M] at *
        nlinarith
  calc
    (∑ j : RingIndex N, population N (j.val + 1)) =
        ∑ j ∈ Finset.range (2 * M - 1), population N (j + 1) := by
          simpa [RingIndex, M] using
            (Fin.sum_univ_eq_sum_range
              (fun j : ℕ => population N (j + 1)) (2 * M - 1))
    _ = N := by
      rw [Finset.sum_Ico_eq_sum_range] at htotal
      simpa [Nat.add_comm] using htotal

/-- The finite dependent index of all polygon vertices has cardinality `N`. -/
theorem card_pointIndex (N : ℕ) (hN : 4 ≤ N) :
    Fintype.card (PointIndex N) = N := by
  simpa [PointIndex, Fintype.card_sigma, Fintype.card_fin] using
    population_sum_eq N hN

/-- The height width of band `j` is exactly twice its population divided by `N`. -/
theorem boundary_width {N j : ℕ} (_hN : 4 ≤ N) (hj : 1 ≤ j) :
    boundary N (j - 1) - boundary N j =
      2 * (population N j : ℝ) / N := by
  have hsub : j - 1 + 1 = j := by omega
  have hsum : (∑ k ∈ Finset.Icc 1 j, (population N k : ℝ)) =
      (∑ k ∈ Finset.Icc 1 (j - 1), (population N k : ℝ)) +
        population N j := by
    conv_lhs => rw [← hsub]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j - 1 + 1), hsub]
  unfold boundary
  rw [hsum]
  ring

/-- Every occupied ring has a positive number of points. -/
theorem population_pos {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    0 < population N j := by
  let M := bandParameter N
  rcases lt_trichotomy j M with hlt | heq | hgt
  · rw [north_population N j hlt]
    omega
  · subst j
    exact (central_population_bounds hN).1.trans_lt' (by
      have hM := bandParameter_pos hN
      omega)
  · rw [south_population N j hgt]
    omega

/-- Cumulative population at the final occupied band. -/
theorem population_sum_Icc (N : ℕ) (hN : 4 ≤ N) :
    (∑ j ∈ Finset.Icc 1 (2 * bandParameter N - 1), population N j) = N := by
  let M := bandParameter N
  have hM : 1 ≤ M := bandParameter_pos hN
  have hfin := Fin.sum_univ_eq_sum_range
    (fun j : ℕ => population N (j + 1)) (2 * M - 1)
  have hpop := population_sum_eq N hN
  change (∑ j : Fin (2 * M - 1), population N (j.val + 1)) = N at hpop
  calc
    (∑ j ∈ Finset.Icc 1 (2 * M - 1), population N j) =
        ∑ j ∈ Finset.Ico 1 (2 * M), population N j := by
          rw [Nat.Icc_pred_right 1 (by omega : 0 < 2 * M)]
    _ = ∑ j ∈ Finset.range (2 * M - 1), population N (j + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_comm]
    _ = N := hfin.symm.trans hpop

theorem boundary_zero (N : ℕ) : boundary N 0 = 1 := by
  simp [boundary]

/-- The final boundary is the south pole height. -/
theorem boundary_last {N : ℕ} (hN : 4 ≤ N) :
    boundary N (2 * bandParameter N - 1) = -1 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hs := population_sum_Icc N hN
  have hsr : (∑ j ∈ Finset.Icc 1 (2 * bandParameter N - 1),
      (population N j : ℝ)) = N := by exact_mod_cast hs
  unfold boundary
  rw [hsr]
  field_simp
  ring

/-- Height boundaries are antisymmetric under north–south reflection. -/
theorem boundary_reflect {N j : ℕ} (hN : 4 ≤ N)
    (hj : j ≤ 2 * bandParameter N - 1) :
    boundary N (2 * bandParameter N - 1 - j) = -boundary N j := by
  let M := bandParameter N
  let L := 2 * M - 1
  change boundary N (L - j) = -boundary N j
  revert hj
  induction j with
  | zero =>
      intro _
      simp [L, M, boundary_last hN, boundary_zero]
  | succ j ih =>
      intro hj
      have hj' : j ≤ L := by omega
      have hk : 1 ≤ L - j := by omega
      have hpop : population N (L - j) = population N (j + 1) := by
        have h := population_reflect hN (j := j + 1) (by omega) (by omega)
        have heq : 2 * M - (j + 1) = L - j := by omega
        rw [heq] at h
        exact h
      have hwk := boundary_width hN hk
      have hwj := boundary_width hN (j := j + 1) (by omega)
      have hidx : L - (j + 1) = (L - j) - 1 := by omega
      have hjs : j + 1 - 1 = j := by omega
      rw [hidx]
      rw [hjs] at hwj
      rw [hpop] at hwk
      linarith [ih hj']

/-- Every midpoint height has the opposite reflected midpoint. -/
theorem height_reflect {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    height N (2 * bandParameter N - j) = -height N j := by
  let M := bandParameter N
  let L := 2 * M - 1
  have hidx1 : 2 * M - j - 1 = L - j := by omega
  have hidx2 : 2 * M - j = L - (j - 1) := by omega
  have hjL : j ≤ 2 * M - 1 := by omega
  have hpL : j - 1 ≤ 2 * M - 1 := by omega
  have hr1 := boundary_reflect hN (j := j) hjL
  have hr2 := boundary_reflect hN (j := j - 1) hpL
  change boundary N (L - j) = -boundary N j at hr1
  change boundary N (L - (j - 1)) = -boundary N (j - 1) at hr2
  unfold height
  change (boundary N (2 * M - j - 1) + boundary N (2 * M - j)) / 2 =
    -((boundary N (j - 1) + boundary N j) / 2)
  rw [hidx1, hidx2, hr1, hr2]
  ring

/-- Occupied band boundaries descend strictly. -/
theorem boundary_strict {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    boundary N j < boundary N (j - 1) := by
  have hp := population_pos hN hj1 hj2
  have hw := boundary_width hN hj1
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpr : (0 : ℝ) < population N j := by exact_mod_cast hp
  have hquot : 0 < 2 * (population N j : ℝ) / N :=
    div_pos (by positivity) hNr
  linarith

/-- A midpoint is strictly between its two band boundaries. -/
theorem height_inside_band {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    boundary N j < height N j ∧ height N j < boundary N (j - 1) := by
  have hs := boundary_strict hN hj1 hj2
  unfold height
  constructor <;> linarith

/-- The boundary sequence is weakly decreasing on its occupied range. -/
theorem boundary_antitone {N a b : ℕ} (hN : 4 ≤ N)
    (hab : a ≤ b) (hb : b < 2 * bandParameter N) :
    boundary N b ≤ boundary N a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      have hs := boundary_strict hN (j := b + 1) (by omega) hb
      have hprev : b + 1 - 1 = b := by omega
      rw [hprev] at hs
      exact (le_of_lt hs).trans (ih (by omega))

/-- Every boundary lies at or below the north-pole height. -/
theorem boundary_le_one {N j : ℕ} (hN : 4 ≤ N)
    (hj : j < 2 * bandParameter N) : boundary N j ≤ 1 := by
  have h := boundary_antitone hN (a := 0) (by omega) hj
  simpa [boundary_zero] using h

/-- Every boundary lies at or above the south-pole height. -/
theorem boundary_ge_neg_one {N j : ℕ} (hN : 4 ≤ N)
    (hj : j < 2 * bandParameter N) : -1 ≤ boundary N j := by
  have hL : j ≤ 2 * bandParameter N - 1 := by omega
  have hr := boundary_reflect hN hL
  have hother : 2 * bandParameter N - 1 - j < 2 * bandParameter N := by omega
  have htop := boundary_le_one hN hother
  linarith

/-- Every occupied midpoint lies strictly between the two poles. -/
theorem height_in_open_unit {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    height N j ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hm := height_inside_band hN hj1 hj2
  have hlo := boundary_ge_neg_one hN hj2
  have hprev : j - 1 < 2 * bandParameter N := by omega
  have hhi := boundary_le_one hN hprev
  exact ⟨lt_of_le_of_lt hlo hm.1, lt_of_lt_of_le hm.2 hhi⟩

/-- Midpoint heights strictly decrease with the one-based ring index. -/
theorem height_strict_antitone {N j k : ℕ} (hN : 4 ≤ N)
    (hj : 1 ≤ j) (hjk : j < k) (hk : k < 2 * bandParameter N) :
    height N k < height N j := by
  have hji : j < 2 * bandParameter N := by omega
  have hki : 1 ≤ k := by omega
  have hkp : k - 1 < 2 * bandParameter N := by omega
  have hmidj := height_inside_band hN hj hji
  have hmidk := height_inside_band hN hki hk
  have horder := boundary_antitone hN (a := j) (b := k - 1) (by omega) hkp
  linarith

/-- On valid inputs the total point definition uses the intended midpoint branch. -/
theorem point_eq_parallelPoint {N : ℕ} (hN : 4 ≤ N)
    (φ : Phases N) (i : PointIndex N) :
    point N φ i = parallelPoint (height N (i.1.val + 1))
      (φ i.1 + 2 * Real.pi * (i.2.val : ℝ) /
        (population N (i.1.val + 1) : ℝ))
      (Set.Ioo_subset_Icc_self (height_in_open_unit hN
        (by omega : 1 ≤ i.1.val + 1) (by
          have hi := i.1.isLt
          omega))) := by
  have hclosed : height N (i.1.val + 1) ∈ Set.Icc (-1 : ℝ) 1 :=
    Set.Ioo_subset_Icc_self (height_in_open_unit hN
      (by omega : 1 ≤ i.1.val + 1) (by
        have hi := i.1.isLt
        omega))
  unfold point
  rw [dif_pos hclosed]

/-- The third coordinate of a vertex is its ring's midpoint height. -/
theorem point_height {N : ℕ} (hN : 4 ≤ N) (φ : Phases N)
    (i : PointIndex N) :
    (point N φ i).val (2 : Fin 3) = height N (i.1.val + 1) := by
  rw [point_eq_parallelPoint hN]
  simp [parallelPoint, parallelVector]

/-- A regular polygon's distinct vertex labels have distinct angles modulo `2π`. -/
theorem polygon_angle_injective (r : ℕ) (hr : 0 < r) (φ : ℝ) :
    Function.Injective
      (fun k : Fin r => ((φ + 2 * Real.pi * (k.val : ℝ) / (r : ℝ) : ℝ) : Real.Angle)) := by
  intro k l h
  have hcong := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
  obtain ⟨m, hm⟩ := hcong
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hfactor : (2 * Real.pi) * (((k.val : ℝ) - l.val) / (r : ℝ)) =
      2 * Real.pi * (m : ℝ) := by
    calc
      (2 * Real.pi) * (((k.val : ℝ) - l.val) / (r : ℝ)) =
          (φ + 2 * Real.pi * (k.val : ℝ) / (r : ℝ)) -
            (φ + 2 * Real.pi * (l.val : ℝ) / (r : ℝ)) := by ring
      _ = 2 * Real.pi * (m : ℝ) := hm
  have hbase := mul_left_cancel₀ hpi hfactor
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hk : (k.val : ℝ) < r := by exact_mod_cast k.isLt
  have hl : (l.val : ℝ) < r := by exact_mod_cast l.isLt
  have hk0 : (0 : ℝ) ≤ k.val := by positivity
  have hl0 : (0 : ℝ) ≤ l.val := by positivity
  have hmBounds : (-1 : ℝ) < (m : ℝ) ∧ (m : ℝ) < 1 := by
    rw [← hbase]
    constructor
    · apply (lt_div_iff₀ hrr).2
      nlinarith
    · apply (div_lt_iff₀ hrr).2
      nlinarith
  have hmInt : (-1 : ℤ) < m ∧ m < 1 := by exact_mod_cast hmBounds
  have hm0 : m = 0 := by omega
  rw [hm0, Int.cast_zero] at hbase
  have hkl : (k.val : ℝ) = l.val := by
    have hzero : (k.val : ℝ) - l.val = 0 := by
      apply (div_eq_zero_iff).mp at hbase
      exact hbase.resolve_right (by positivity)
    linarith
  exact Fin.ext (by exact_mod_cast hkl)

/-- Equality of points on a nonpolar parallel forces equality of angles modulo `2π`. -/
theorem parallelPoint_angle_eq {z θ ψ : ℝ}
    (hz : z ∈ Set.Ioo (-1 : ℝ) 1)
    (hθ : z ∈ Set.Icc (-1 : ℝ) 1)
    (hψ : z ∈ Set.Icc (-1 : ℝ) 1)
    (h : parallelPoint z θ hθ = parallelPoint z ψ hψ) :
    (θ : Real.Angle) = ψ := by
  have hrad : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hrho : Real.sqrt (1 - z ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hrad)
  have hx := congrArg (fun p : Sphere => p.val (0 : Fin 3)) h
  have hy := congrArg (fun p : Sphere => p.val (1 : Fin 3)) h
  simp only [parallelPoint, parallelVector, Matrix.cons_val_zero] at hx hy
  have hcos : Real.cos θ = Real.cos ψ := mul_left_cancel₀ hrho hx
  have hsin : Real.sin θ = Real.sin ψ := mul_left_cancel₀ hrho hy
  exact Real.Angle.cos_sin_inj hcos hsin

/-- The labelled Diamond vertices are distinct for arbitrary ring phases. -/
theorem point_injective {N : ℕ} (hN : 4 ≤ N) (φ : Phases N) :
    Function.Injective (point N φ) := by
  intro i k hpoint
  have hh : height N (i.1.val + 1) = height N (k.1.val + 1) := by
    rw [← point_height hN φ i, ← point_height hN φ k]
    exact congrArg (fun p : Sphere => p.val (2 : Fin 3)) hpoint
  have hring : i.1.val = k.1.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hs := height_strict_antitone hN (j := i.1.val + 1)
        (k := k.1.val + 1) (by omega) (by omega) (by
          have hk := k.1.isLt
          omega)
      linarith
    · have hs := height_strict_antitone hN (j := k.1.val + 1)
        (k := i.1.val + 1) (by omega) (by omega) (by
          have hi := i.1.isLt
          omega)
      linarith
  have hring' : i.1 = k.1 := Fin.ext hring
  rcases i with ⟨a, x⟩
  rcases k with ⟨b, y⟩
  dsimp at hring'
  subst b
  have hpop : 0 < population N (a.val + 1) :=
    population_pos hN (by omega) (by
      have ha := a.isLt
      omega)
  have hz : height N (a.val + 1) ∈ Set.Ioo (-1 : ℝ) 1 :=
    height_in_open_unit hN (by omega) (by
      have ha := a.isLt
      omega)
  rw [point_eq_parallelPoint hN φ ⟨a, x⟩,
    point_eq_parallelPoint hN φ ⟨a, y⟩] at hpoint
  have hangle := parallelPoint_angle_eq hz _ _ hpoint
  have hxy : x = y := polygon_angle_injective (population N (a.val + 1))
    hpop (φ a) hangle
  subst y
  rfl

/-- Construction obligations, including distinctness needed to speak about an N-element set. -/
def ConstructionFacts : Prop :=
  ∀ N : ℕ, 4 ≤ N →
    1 ≤ bandParameter N ∧
    4 * bandParameter N ^ 2 ≤ N ∧
    N < 4 * (bandParameter N + 1) ^ 2 ∧
    (∑ j : RingIndex N, population N (j.val + 1)) = N ∧
    (∀ j : RingIndex N, 0 < population N (j.val + 1) ∧
      height N (j.val + 1) ∈ Set.Ioo (-1 : ℝ) 1) ∧
    (∀ φ : Phases N, Function.Injective (point N φ))

/-- All exact population, location, and distinctness facts hold for the new construction. -/
theorem constructionFacts : ConstructionFacts := by
  intro N hN
  refine ⟨bandParameter_pos hN, (bandParameter_bounds N).1,
    (bandParameter_bounds N).2, population_sum_eq N hN, ?_, ?_⟩
  · intro j
    have hj : j.val + 1 < 2 * bandParameter N := by
      have hj' := j.isLt
      omega
    exact ⟨population_pos hN (by omega) hj,
      height_in_open_unit hN (by omega) hj⟩
  · exact fun φ => point_injective hN φ

/-- The manuscript's fixed meridian convention is zero phase on every parallel. -/
def zeroPhases (N : ℕ) : Phases N := fun _ => 0

/-- The finite set of canonical deterministic Diamond points. -/
noncomputable def diamondPoints (N : ℕ) : Finset Sphere := by
  classical
  exact Finset.univ.image (point N (zeroPhases N))

/-- The named Diamond set contains exactly `N` distinct points. -/
theorem diamondPoints_card {N : ℕ} (hN : 4 ≤ N) :
    (diamondPoints N).card = N := by
  classical
  rw [diamondPoints, Finset.card_image_of_injective _ (point_injective hN _),
    Finset.card_univ, card_pointIndex N hN]

/-- The manuscript's ordered set energy equals the labelled finite energy. -/
theorem diamondPoints_energy {N : ℕ} (hN : 4 ≤ N) (α : ℝ) :
    (∑ x ∈ diamondPoints N, ∑ y ∈ diamondPoints N, dist x y ^ α) =
      diamondEnergy α N (zeroPhases N) := by
  classical
  have hinj := point_injective hN (zeroPhases N)
  have hsum (f : Sphere → ℝ) :
      (∑ x ∈ diamondPoints N, f x) =
        ∑ i : PointIndex N, f (point N (zeroPhases N) i) := by
    unfold diamondPoints
    rw [Finset.sum_image (by
      intro x _ y _ hxy
      exact hinj hxy)]
  calc
    (∑ x ∈ diamondPoints N, ∑ y ∈ diamondPoints N, dist x y ^ α) =
        ∑ i : PointIndex N,
          ∑ y ∈ diamondPoints N, dist (point N (zeroPhases N) i) y ^ α :=
      hsum _
    _ = ∑ i : PointIndex N, ∑ k : PointIndex N,
        dist (point N (zeroPhases N) i) (point N (zeroPhases N) k) ^ α := by
      apply Finset.sum_congr rfl
      intro i _
      exact hsum _
    _ = diamondEnergy α N (zeroPhases N) := rfl

/-- Closed formulas to prove from cumulative populations. -/
def BoundaryFormulas : Prop :=
  ∀ N : ℕ, 4 ≤ N →
    (∀ j : ℕ, j < bandParameter N →
      boundary N j = 1 - 4 * (j : ℝ) * (j + 1) / N) ∧
    (∀ j : ℕ, 1 ≤ j → j < bandParameter N →
      height N j = 1 - 4 * (j : ℝ) ^ 2 / N) ∧
    height N (bandParameter N) = 0 ∧
    (∀ j : ℕ, 1 ≤ j → j < 2 * bandParameter N →
      height N (2 * bandParameter N - j) = -height N j)

/-- The closed construction identities are fully proved for every `N ≥ 4`. -/
theorem boundaryFormulas : BoundaryFormulas := by
  intro N hN
  exact ⟨(fun _ hj => north_boundary hN hj),
    (fun _ hj1 hj2 => north_height hN hj1 hj2),
    central_height hN,
    (fun _ hj1 hj2 => height_reflect hN hj1 hj2)⟩

end BEMOC.Definitive
