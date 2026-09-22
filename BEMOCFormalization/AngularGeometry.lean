import BEMOCFormalization.Geometry

namespace BEMOC.Definitive

/-- Every occupied polar band lies in the usual angular interval. -/
theorem polarBand_angle_bounds {N j : ℕ} {θ : ℝ}
    (hθ : θ ∈ polarBand N j) : 0 ≤ θ ∧ θ ≤ Real.pi := by
  rcases hθ with ⟨hlo, hhi⟩
  exact ⟨(Real.arccos_nonneg _).trans hlo,
    hhi.trans (Real.arccos_le_pi _)⟩

/-- The angular width of an occupied band is positive, including the polar bands. -/
theorem polarBand_width_pos {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    0 < Real.arccos (boundary N j) - Real.arccos (boundary N (j - 1)) := by
  have hw := boundary_strict hN hj1 hj2
  have hlo := boundary_ge_neg_one hN hj2
  have hp : j - 1 < 2 * bandParameter N := by omega
  have hhi := boundary_le_one hN hp
  have ha := Real.arccos_lt_arccos hlo hw hhi
  linarith

/-- Occupied polar bands are nonempty closed intervals. -/
theorem polarBand_nonempty {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    (polarBand N j).Nonempty := by
  have hw := polarBand_width_pos hN hj1 hj2
  exact ⟨Real.arccos (boundary N (j - 1)),
    ⟨le_rfl, by linarith⟩⟩

/-- Mean value form of the cosine drop on a positive polar interval. -/
theorem cosine_drop_mean_value {a b : ℝ} (hab : a < b) :
    ∃ ξ ∈ Set.Ioo a b, (b - a) * Real.sin ξ = Real.cos a - Real.cos b := by
  obtain ⟨ξ, hξ, hderiv⟩ := exists_deriv_eq_slope Real.cos hab
    Real.continuous_cos.continuousOn
    Real.differentiable_cos.differentiableOn
  refine ⟨ξ, hξ, ?_⟩
  rw [Real.deriv_cos] at hderiv
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  apply (eq_div_iff hne).mp at hderiv
  linarith

/-- The height width of a band is an angular width times an interior sine. -/
theorem polarBand_mean_value {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    ∃ ξ ∈ Set.Ioo (Real.arccos (boundary N (j - 1)))
        (Real.arccos (boundary N j)),
      (Real.arccos (boundary N j) - Real.arccos (boundary N (j - 1))) *
        Real.sin ξ = 2 * (population N j : ℝ) / N := by
  obtain ⟨ξ, hξ, hdrop⟩ := cosine_drop_mean_value
    (sub_pos.mp (polarBand_width_pos hN hj1 hj2))
  refine ⟨ξ, hξ, ?_⟩
  rw [Real.cos_arccos (boundary_ge_neg_one hN (by omega))
    (boundary_le_one hN (by omega)),
    Real.cos_arccos (boundary_ge_neg_one hN hj2)
      (boundary_le_one hN hj2)] at hdrop
  rw [boundary_width hN hj1] at hdrop
  exact hdrop

/-- A northern boundary before the equator has nonnegative height. -/
theorem north_boundary_nonneg {N j : ℕ} (hN : 4 ≤ N)
    (hj : j < bandParameter N) : 0 ≤ boundary N j := by
  have hNlow : 4 * (bandParameter N : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hjr : (j : ℝ) + 1 ≤ bandParameter N := by
    exact_mod_cast (by omega : j + 1 ≤ bandParameter N)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [north_boundary hN hj]
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hNr).2
  nlinarith

/-- Sine throughout an ordinary northern polar band is bounded by its ring label. -/
theorem north_polar_sin_le {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hjM : j < bandParameter N)
    {θ : ℝ} (hθ : θ ∈ polarBand N j) :
    Real.sin θ ≤ 2 * (j : ℝ) / bandParameter N := by
  have hθrange := polarBand_angle_bounds hθ
  have hθupper : θ ≤ Real.arccos (boundary N j) := hθ.2
  have hcos : boundary N j ≤ Real.cos θ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hθrange.1
      (Real.arccos_le_pi _) hθupper
    rw [Real.cos_arccos (boundary_ge_neg_one hN (by omega))
      (boundary_le_one hN (by omega))] at h
    exact h
  have hB0 := north_boundary_nonneg hN hjM
  have hcos0 : 0 ≤ Real.cos θ := hB0.trans hcos
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one _
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθrange.1 hθrange.2
  have hMr : (0 : ℝ) < bandParameter N := by
    exact_mod_cast bandParameter_pos hN
  have hNlow : 4 * (bandParameter N : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hjr : (j : ℝ) + 1 ≤ bandParameter N := by
    exact_mod_cast (by omega : j + 1 ≤ bandParameter N)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcosLower : 1 - 4 * (j : ℝ) * (j + 1) / N ≤ Real.cos θ := by
    rwa [← north_boundary hN hjM]
  have hsinSq : (Real.sin θ) ^ 2 + (Real.cos θ) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hgoalSq : (Real.sin θ) ^ 2 ≤
      (2 * (j : ℝ) / bandParameter N) ^ 2 := by
    have hprod : 4 * (j : ℝ) * (j + 1) / N ≤
        2 * (j : ℝ) ^ 2 / (bandParameter N : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ hNr (by positivity : (0 : ℝ) <
        (bandParameter N : ℝ) ^ 2)).2
      have hjreal : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ j by positivity)
        (show (0 : ℝ) ≤ j - 1 by linarith)]
    have hgap : 1 - Real.cos θ ≤
        2 * (j : ℝ) ^ 2 / (bandParameter N : ℝ) ^ 2 := by linarith
    have hsinBd : (Real.sin θ) ^ 2 ≤ 2 * (1 - Real.cos θ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcos1) hcos0]
    have hid : (2 * (j : ℝ) / bandParameter N) ^ 2 =
        4 * (j : ℝ) ^ 2 / (bandParameter N : ℝ) ^ 2 := by ring
    rw [hid]
    calc
      (Real.sin θ) ^ 2 ≤ 2 * (1 - Real.cos θ) := hsinBd
      _ ≤ 2 * (2 * (j : ℝ) ^ 2 / (bandParameter N : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hgap (by norm_num)
      _ = 4 * (j : ℝ) ^ 2 / (bandParameter N : ℝ) ^ 2 := by ring
  have htarget0 : 0 ≤ 2 * (j : ℝ) / bandParameter N := by positivity
  nlinarith

/-- Every ordinary northern band has angular width at least a constant over `M`. -/
theorem north_polar_width_lower {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hjM : j < bandParameter N) :
    1 / (4 * (bandParameter N : ℝ)) ≤
      Real.arccos (boundary N j) - Real.arccos (boundary N (j - 1)) := by
  let m : ℝ := bandParameter N
  let t : ℝ := j
  let n : ℝ := N
  let w := Real.arccos (boundary N j) - Real.arccos (boundary N (j - 1))
  obtain ⟨ξ, hξ, hmean⟩ := polarBand_mean_value hN hj1 (by omega)
  have hξband : ξ ∈ polarBand N j := ⟨hξ.1.le, hξ.2.le⟩
  have hs : Real.sin ξ ≤ 2 * t / m := north_polar_sin_le hN hj1 hjM hξband
  have hmp : 0 < m := by
    change (0 : ℝ) < bandParameter N
    exact_mod_cast (by omega : 0 < bandParameter N)
  have htp : 0 < t := by
    change (0 : ℝ) < j
    exact_mod_cast (by omega : 0 < j)
  have hnp : 0 < n := by
    change (0 : ℝ) < N
    exact_mod_cast (by omega : 0 < N)
  have hwp : 0 < w := polarBand_width_pos hN hj1 (by omega)
  have hNtop : n ≤ 16 * m ^ 2 := by
    have hmreal : (1 : ℝ) ≤ m := by
      change (1 : ℝ) ≤ bandParameter N
      exact_mod_cast bandParameter_pos hN
    have htop : n < 4 * (m + 1) ^ 2 := by
      change (N : ℝ) < 4 * ((bandParameter N : ℝ) + 1) ^ 2
      exact_mod_cast (bandParameter_bounds N).2
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ m + 1 by positivity)
      (show (0 : ℝ) ≤ m - 1 by linarith)]
  have hmean' : w * Real.sin ξ = 8 * t / n := by
    rw [north_population N j hjM] at hmean
    dsimp [w, t, n]
    convert hmean using 1
    push_cast
    ring
  have hratio : t / (2 * m ^ 2) ≤ 8 * t / n := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * m ^ 2) hnp).2
    nlinarith [mul_nonneg (le_of_lt htp) (sub_nonneg.mpr hNtop)]
  change 1 / (4 * m) ≤ w
  by_contra hnot
  have hlt : w < 1 / (4 * m) := lt_of_not_ge hnot
  have hsmul := mul_le_mul_of_nonneg_left hs hwp.le
  have h2p : 0 < 2 * t / m := by positivity
  have hwmul := mul_lt_mul_of_pos_right hlt h2p
  have hid : (1 / (4 * m)) * (2 * t / m) = t / (2 * m ^ 2) := by
    field_simp
    ring
  rw [hid] at hwmul
  nlinarith

/-- North–south reflection preserves occupied angular band widths. -/
theorem polar_width_reflect {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    Real.arccos (boundary N (2 * bandParameter N - j)) -
      Real.arccos (boundary N (2 * bandParameter N - j - 1)) =
    Real.arccos (boundary N j) - Real.arccos (boundary N (j - 1)) := by
  let M := bandParameter N
  let L := 2 * M - 1
  have hjL : j ≤ L := by dsimp [L, M]; omega
  have hpL : j - 1 ≤ L := by dsimp [L, M]; omega
  have hr1 := boundary_reflect hN hjL
  have hr2 := boundary_reflect hN hpL
  have hidx1 : 2 * M - j - 1 = L - j := by dsimp [L]; omega
  have hidx2 : 2 * M - j = L - (j - 1) := by dsimp [L]; omega
  change Real.arccos (boundary N (2 * M - j)) -
      Real.arccos (boundary N (2 * M - j - 1)) =
    Real.arccos (boundary N j) - Real.arccos (boundary N (j - 1))
  rw [hidx1, hidx2]
  change boundary N (L - j) = -boundary N j at hr1
  change boundary N (L - (j - 1)) = -boundary N (j - 1) at hr2
  rw [hr1, hr2, Real.arccos_neg, Real.arccos_neg]
  ring

/-- The equatorial band has angular width at least `1/(4M)`. -/
theorem central_polar_width_lower {N : ℕ} (hN : 4 ≤ N) :
    1 / (4 * (bandParameter N : ℝ)) ≤
      Real.arccos (boundary N (bandParameter N)) -
        Real.arccos (boundary N (bandParameter N - 1)) := by
  let M := bandParameter N
  let w := Real.arccos (boundary N M) - Real.arccos (boundary N (M - 1))
  have hM : 1 ≤ M := bandParameter_pos hN
  obtain ⟨ξ, hξ, hmean⟩ := polarBand_mean_value hN hM (by omega : M < 2 * M)
  have hw : 0 < w := polarBand_width_pos hN hM (by omega : M < 2 * M)
  have hsin : Real.sin ξ ≤ 1 := Real.sin_le_one _
  have hpop : 4 * (M : ℝ) ≤ population N M := by
    exact_mod_cast (central_population_bounds hN).1
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hNtop : (N : ℝ) ≤ 16 * (M : ℝ) ^ 2 := by
    have hmreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have htop : (N : ℝ) < 4 * ((M : ℝ) + 1) ^ 2 := by
      exact_mod_cast (bandParameter_bounds N).2
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (M : ℝ) + 1 by positivity)
      (show (0 : ℝ) ≤ (M : ℝ) - 1 by linarith)]
  have hratio : 1 / (4 * (M : ℝ)) ≤
      8 * (M : ℝ) / N := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * M) hNr).2
    nlinarith
  have hmean' : w * Real.sin ξ = 2 * (population N M : ℝ) / N := hmean
  have hwidth : 8 * (M : ℝ) / N ≤ w := by
    have hpopdiv : 8 * (M : ℝ) / N ≤ 2 * (population N M : ℝ) / N := by
      apply (div_le_div_iff₀ hNr hNr).2
      nlinarith
    have hsinmul := mul_le_mul_of_nonneg_left hsin hw.le
    calc
      8 * (M : ℝ) / N ≤ 2 * (population N M : ℝ) / N := hpopdiv
      _ = w * Real.sin ξ := hmean'.symm
      _ ≤ w := by simpa using hsinmul
  exact hratio.trans hwidth

/-- Uniform lower angular width, including both polar caps and the center. -/
theorem polar_width_lower {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    1 / (4 * (bandParameter N : ℝ)) ≤
      Real.arccos (boundary N j) - Real.arccos (boundary N (j - 1)) := by
  let M := bandParameter N
  rcases lt_trichotomy j M with hlt | heq | hgt
  · exact north_polar_width_lower hN hj1 hlt
  · subst j
    exact central_polar_width_lower hN
  · let k := 2 * M - j
    have hk1 : 1 ≤ k := by dsimp [k]; omega
    have hkM : k < M := by dsimp [k]; omega
    have hlow := north_polar_width_lower hN hk1 hkM
    have href := polar_width_reflect hN hk1 (by dsimp [k]; omega : k < 2 * M)
    have hidx : 2 * M - k = j := by dsimp [k]; omega
    change Real.arccos (boundary N (2 * M - k)) -
      Real.arccos (boundary N (2 * M - k - 1)) =
        Real.arccos (boundary N k) - Real.arccos (boundary N (k - 1)) at href
    rw [hidx] at href
    rw [← href] at hlow
    exact hlow

/-- Sine stays uniformly away from zero on northern bands beyond the cap. -/
theorem north_polar_sin_lower {N j : ℕ} (hN : 4 ≤ N)
    (hj2 : 2 ≤ j) (hjM : j < bandParameter N)
    {θ : ℝ} (hθ : θ ∈ polarBand N j) :
    (j : ℝ) / (4 * bandParameter N) ≤ Real.sin θ := by
  let M := bandParameter N
  let k := j - 1
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hkM : k < M := by dsimp [k]; omega
  have hkj : k + 1 = j := by dsimp [k]; omega
  have hθrange := polarBand_angle_bounds hθ
  have hcosupper : Real.cos θ ≤ boundary N k := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (Real.arccos_nonneg _) hθrange.2 hθ.1
    rw [Real.cos_arccos (boundary_ge_neg_one hN (by omega))
      (boundary_le_one hN (by omega))] at h
    exact h
  have hcos0 : 0 ≤ Real.cos θ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hθrange.1
      (Real.arccos_le_pi _) hθ.2
    rw [Real.cos_arccos (boundary_ge_neg_one hN (by omega))
      (boundary_le_one hN (by omega))] at h
    exact (north_boundary_nonneg hN hjM).trans h
  have hB0 : 0 ≤ boundary N k := north_boundary_nonneg hN hkM
  have hB1 : boundary N k ≤ 1 := boundary_le_one hN (by dsimp [k]; omega)
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθrange.1 hθrange.2
  have hsinSq : (Real.sin θ) ^ 2 + (Real.cos θ) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsinLower : 4 * (k : ℝ) * ((k : ℝ) + 1) / N ≤ (Real.sin θ) ^ 2 := by
    have hcosSq : (Real.cos θ) ^ 2 ≤ boundary N k := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcosupper) hcos0]
    have hformula := north_boundary hN hkM
    rw [hformula] at hcosSq
    nlinarith
  have hMr : (0 : ℝ) < M := by
    exact_mod_cast (by omega : 0 < M)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hNtop : (N : ℝ) ≤ 16 * (M : ℝ) ^ 2 := by
    have hmreal : (1 : ℝ) ≤ M := by exact_mod_cast bandParameter_pos hN
    have htop : (N : ℝ) < 4 * ((M : ℝ) + 1) ^ 2 := by
      exact_mod_cast (bandParameter_bounds N).2
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (M : ℝ) + 1 by positivity)
      (show (0 : ℝ) ≤ (M : ℝ) - 1 by linarith)]
  have hratio : ((j : ℝ) / (4 * M)) ^ 2 ≤
      4 * (k : ℝ) * ((k : ℝ) + 1) / N := by
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (4 * M) ^ 2) hNr).2
    have hjreal : (j : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hkj.symm
    rw [hjreal]
    have hfactor : ((k : ℝ) + 1) ^ 2 ≤ 4 * k * ((k : ℝ) + 1) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)
        (show (0 : ℝ) ≤ 3 * k - 1 by linarith)]
    have hA := mul_le_mul_of_nonneg_left hNtop
      (sq_nonneg ((k : ℝ) + 1))
    have hB := mul_le_mul_of_nonneg_right hfactor
      (show (0 : ℝ) ≤ 16 * (M : ℝ) ^ 2 by positivity)
    nlinarith [hA, hB]
  have hgoalSq : ((j : ℝ) / (4 * M)) ^ 2 ≤ (Real.sin θ) ^ 2 :=
    hratio.trans hsinLower
  have htarget0 : (0 : ℝ) ≤ (j : ℝ) / (4 * M) := by positivity
  nlinarith

/-- Angular widths of northern bands beyond the cap are at most `8/M`. -/
theorem north_polar_width_upper {N j : ℕ} (hN : 4 ≤ N)
    (hj2 : 2 ≤ j) (hjM : j < bandParameter N) :
    Real.arccos (boundary N j) - Real.arccos (boundary N (j - 1)) ≤
      8 / bandParameter N := by
  let m : ℝ := bandParameter N
  let t : ℝ := j
  let n : ℝ := N
  let w := Real.arccos (boundary N j) - Real.arccos (boundary N (j - 1))
  obtain ⟨ξ, hξ, hmean⟩ := polarBand_mean_value hN (by omega : 1 ≤ j)
    (by omega : j < 2 * bandParameter N)
  have hξband : ξ ∈ polarBand N j := ⟨hξ.1.le, hξ.2.le⟩
  have hs : t / (4 * m) ≤ Real.sin ξ :=
    north_polar_sin_lower hN hj2 hjM hξband
  have hmp : 0 < m := by
    change (0 : ℝ) < bandParameter N
    exact_mod_cast (by omega : 0 < bandParameter N)
  have htp : 0 < t := by
    change (0 : ℝ) < j
    exact_mod_cast (by omega : 0 < j)
  have hnp : 0 < n := by
    change (0 : ℝ) < N
    exact_mod_cast (by omega : 0 < N)
  have hwp : 0 < w := polarBand_width_pos hN (by omega) (by omega)
  have hNlow : 4 * m ^ 2 ≤ n := by
    change 4 * (bandParameter N : ℝ) ^ 2 ≤ N
    exact_mod_cast (bandParameter_bounds N).1
  have hmean' : w * Real.sin ξ = 8 * t / n := by
    rw [north_population N j hjM] at hmean
    dsimp [w, t, n]
    convert hmean using 1
    push_cast
    ring
  have hratio : 8 * t / n ≤ 2 * t / m ^ 2 := by
    apply (div_le_div_iff₀ hnp (by positivity : 0 < m ^ 2)).2
    nlinarith [mul_nonneg (le_of_lt htp) (sub_nonneg.mpr hNlow)]
  have hp : 0 < t / (4 * m) := by positivity
  have hcomp : w * (t / (4 * m)) ≤ (8 / m) * (t / (4 * m)) := by
    calc
      w * (t / (4 * m)) ≤ w * Real.sin ξ :=
        mul_le_mul_of_nonneg_left hs hwp.le
      _ = 8 * t / n := hmean'
      _ ≤ 2 * t / m ^ 2 := hratio
      _ = (8 / m) * (t / (4 * m)) := by field_simp; ring
  change w ≤ 8 / m
  exact (mul_le_mul_right hp).mp hcomp

/-- The first northern band obeys the same upper width bound. -/
theorem north_cap_width_upper {N : ℕ} (hN : 4 ≤ N)
    (hM : 2 ≤ bandParameter N) :
    Real.arccos (boundary N 1) - Real.arccos (boundary N 0) ≤
      8 / bandParameter N := by
  let m : ℝ := bandParameter N
  let θ := Real.arccos (boundary N 1)
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθhalf : θ ≤ Real.pi / 2 :=
    Real.arccos_le_pi_div_two.mpr (north_boundary_nonneg hN (by omega))
  have hθband : θ ∈ polarBand N 1 := by
    change Real.arccos (boundary N 0) ≤ θ ∧ θ ≤ Real.arccos (boundary N 1)
    rw [boundary_zero, Real.arccos_one]
    exact ⟨hθ0, le_rfl⟩
  have hsin := north_polar_sin_le hN (by omega : 1 ≤ 1) (by omega) hθband
  have hjordan := Real.mul_le_sin hθ0 hθhalf
  have hmp : 0 < m := by
    change (0 : ℝ) < bandParameter N
    exact_mod_cast (by omega : 0 < bandParameter N)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hθbd : θ ≤ Real.pi / m := by
    have hmul := mul_le_mul_of_nonneg_left (hjordan.trans hsin)
      (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    have hid : (Real.pi / 2) * ((2 / Real.pi) * θ) = θ := by
      field_simp
      ring
    rw [hid] at hmul
    calc
      θ ≤ Real.pi / 2 * (2 * (1 : ℝ) / m) := by simpa [m] using hmul
      _ = Real.pi / m := by ring
  have hπ4 : Real.pi / m ≤ 4 / m :=
    div_le_div_of_nonneg_right Real.pi_le_four hmp.le
  have h48 : 4 / m ≤ 8 / m := by
    apply (div_le_div_iff₀ hmp hmp).2
    nlinarith
  simpa [boundary_zero, Real.arccos_one, m, θ] using
    hθbd.trans (hπ4.trans h48)

/-- Both central boundary heights lie within one half of the equator for `M ≥ 16`. -/
theorem central_boundary_half {N : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) :
    boundary N (bandParameter N - 1) ≤ (1 / 2 : ℝ) ∧
      (-1 / 2 : ℝ) ≤ boundary N (bandParameter N) := by
  let M := bandParameter N
  have hzero := central_height hN
  have hsum : boundary N (M - 1) + boundary N M = 0 := by
    unfold height at hzero
    dsimp [M] at *
    linarith
  have hwidth := boundary_width hN (j := M) (by omega : 1 ≤ M)
  have hp : population N M ≤ 15 * M :=
    population_le_fifteen hN (by omega) (by omega)
  have hNlow : 4 * M ^ 2 ≤ N := (bandParameter_bounds N).1
  have hnum : 2 * population N M ≤ N := by
    have hM' : 16 ≤ M := hM
    nlinarith
  have hnumr : 2 * (population N M : ℝ) ≤ N := by exact_mod_cast hnum
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hratio : (population N M : ℝ) / N ≤ 1 / 2 := by
    apply (div_le_iff₀ hNr).2
    linarith
  have hwidth' : boundary N (M - 1) - boundary N M =
      2 * ((population N M : ℝ) / N) := by
    convert hwidth using 1
    ring
  change boundary N (M - 1) ≤ (1 / 2 : ℝ) ∧
    (-1 / 2 : ℝ) ≤ boundary N M
  constructor <;> linarith [hwidth']

/-- The sine on the central band is uniformly bounded below. -/
theorem central_polar_sin_lower {N : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) {θ : ℝ}
    (hθ : θ ∈ polarBand N (bandParameter N)) :
    (1 / 2 : ℝ) ≤ Real.sin θ := by
  have hθrange := polarBand_angle_bounds hθ
  have hhalf := central_boundary_half hN hM
  have hcoslo : (-1 / 2 : ℝ) ≤ Real.cos θ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hθrange.1
      (Real.arccos_le_pi _) hθ.2
    rw [Real.cos_arccos (boundary_ge_neg_one hN (by omega))
      (boundary_le_one hN (by omega))] at h
    exact hhalf.2.trans h
  have hcoshi : Real.cos θ ≤ (1 / 2 : ℝ) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (Real.arccos_nonneg _) hθrange.2 hθ.1
    rw [Real.cos_arccos (boundary_ge_neg_one hN (by omega))
      (boundary_le_one hN (by omega))] at h
    exact h.trans hhalf.1
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθrange.1 hθrange.2
  have hsinSq := Real.sin_sq_add_cos_sq θ
  nlinarith [mul_nonneg (sub_nonneg.mpr hcoshi)
    (sub_nonneg.mpr hcoslo)]

/-- The exceptional equatorial band has angular width at most `15/M`. -/
theorem central_polar_width_upper {N : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) :
    Real.arccos (boundary N (bandParameter N)) -
      Real.arccos (boundary N (bandParameter N - 1)) ≤
      15 / bandParameter N := by
  let M := bandParameter N
  let w := Real.arccos (boundary N M) - Real.arccos (boundary N (M - 1))
  obtain ⟨ξ, hξ, hmean⟩ := polarBand_mean_value hN (by omega : 1 ≤ M)
    (by omega : M < 2 * M)
  have hξband : ξ ∈ polarBand N M := ⟨hξ.1.le, hξ.2.le⟩
  have hsin : (1 / 2 : ℝ) ≤ Real.sin ξ := central_polar_sin_lower hN hM hξband
  have hw : 0 < w := polarBand_width_pos hN (by omega) (by omega)
  have hp : population N M ≤ 15 * M :=
    population_le_fifteen hN (by omega) (by omega)
  have hpr : (population N M : ℝ) ≤ 15 * M := by exact_mod_cast hp
  have hNlow : 4 * (M : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpopratio : 2 * (population N M : ℝ) / N ≤
      15 / (2 * (M : ℝ)) := by
    apply (div_le_div_iff₀ hNr (by positivity : (0 : ℝ) < 2 * M)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hpr)
      (show (0 : ℝ) ≤ M by positivity)]
  have hcomp : w / 2 ≤ 15 / (2 * (M : ℝ)) := by
    calc
      w / 2 = w * (1 / 2 : ℝ) := by ring
      _ ≤ w * Real.sin ξ := mul_le_mul_of_nonneg_left hsin hw.le
      _ = 2 * (population N M : ℝ) / N := hmean
      _ ≤ 15 / (2 * (M : ℝ)) := hpopratio
  change w ≤ 15 / M
  calc
    w = 2 * (w / 2) := by ring
    _ ≤ 2 * (15 / (2 * (M : ℝ))) :=
      mul_le_mul_of_nonneg_left hcomp (by norm_num)
    _ = 15 / M := by ring

/-- Uniform upper angular width, including caps and the equator. -/
theorem polar_width_upper {N j : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) (hj1 : 1 ≤ j)
    (hj2 : j < 2 * bandParameter N) :
    Real.arccos (boundary N j) - Real.arccos (boundary N (j - 1)) ≤
      15 / bandParameter N := by
  let M := bandParameter N
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have h8 : 8 / (M : ℝ) ≤ 15 / M := by
    apply (div_le_div_iff₀ hMr hMr).2
    nlinarith
  rcases lt_trichotomy j M with hlt | heq | hgt
  · by_cases hj : j = 1
    · subst j
      exact (north_cap_width_upper hN (by omega)).trans h8
    · exact (north_polar_width_upper hN (by omega) hlt).trans h8
  · subst j
    exact central_polar_width_upper hN hM
  · let k := 2 * M - j
    have hk1 : 1 ≤ k := by dsimp [k]; omega
    have hkM : k < M := by dsimp [k]; omega
    have hk2 : k < 2 * M := by omega
    have hku : Real.arccos (boundary N k) -
        Real.arccos (boundary N (k - 1)) ≤ 15 / M := by
      by_cases hk : k = 1
      · rw [hk]
        exact (north_cap_width_upper hN (by omega)).trans h8
      · exact (north_polar_width_upper hN (by omega) hkM).trans h8
    have href := polar_width_reflect hN hk1 hk2
    have hidx : 2 * M - k = j := by dsimp [k]; omega
    change Real.arccos (boundary N (2 * M - k)) -
      Real.arccos (boundary N (2 * M - k - 1)) =
        Real.arccos (boundary N k) - Real.arccos (boundary N (k - 1)) at href
    rw [hidx] at href
    rw [href]
    exact hku

/-- Reflecting a polar angle across the equator reflects its occupied band. -/
theorem polarBand_reflect {N j : ℕ} {θ : ℝ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N)
    (hθ : θ ∈ polarBand N j) :
    Real.pi - θ ∈ polarBand N (2 * bandParameter N - j) := by
  let M := bandParameter N
  let L := 2 * M - 1
  have hjL : j ≤ L := by dsimp [L, M]; omega
  have hpL : j - 1 ≤ L := by dsimp [L, M]; omega
  have hr1 := boundary_reflect hN hjL
  have hr2 := boundary_reflect hN hpL
  have hidx1 : 2 * M - j - 1 = L - j := by dsimp [L]; omega
  have hidx2 : 2 * M - j = L - (j - 1) := by dsimp [L]; omega
  change boundary N (L - j) = -boundary N j at hr1
  change boundary N (L - (j - 1)) = -boundary N (j - 1) at hr2
  change Real.arccos (boundary N (2 * M - j - 1)) ≤ Real.pi - θ ∧
    Real.pi - θ ≤ Real.arccos (boundary N (2 * M - j))
  rw [hidx1, hidx2, hr1, hr2, Real.arccos_neg, Real.arccos_neg]
  exact ⟨by linarith [hθ.2], by linarith [hθ.1]⟩

/-- Sine and population are comparable on northern noncap bands and the center. -/
theorem north_central_polar_sin_comparison {N j : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) (hj2 : 2 ≤ j)
    (hjM : j ≤ bandParameter N) {θ : ℝ}
    (hθ : θ ∈ polarBand N j) :
    (1 / 30 : ℝ) * population N j / bandParameter N ≤ Real.sin θ ∧
      Real.sin θ ≤ (population N j : ℝ) / bandParameter N := by
  let M := bandParameter N
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  rcases lt_or_eq_of_le hjM with hlt | heq
  · have hlo := north_polar_sin_lower hN hj2 hlt hθ
    have hhi := north_polar_sin_le hN (by omega : 1 ≤ j) hlt hθ
    rw [north_population N j hlt]
    push_cast
    constructor
    · calc
        (1 / 30 : ℝ) * (4 * j) / M ≤ (j : ℝ) / (4 * M) := by
          apply (div_le_div_iff₀ hMr (by positivity : (0 : ℝ) < 4 * M)).2
          have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          nlinarith
        _ ≤ Real.sin θ := hlo
    · calc
        Real.sin θ ≤ 2 * (j : ℝ) / M := hhi
        _ ≤ (4 * j) / M := by
          apply (div_le_div_iff₀ hMr hMr).2
          have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          nlinarith
  · subst j
    have hlo := central_polar_sin_lower hN hM hθ
    have hhi := Real.sin_le_one θ
    have hpLo := (central_population_bounds hN).1
    have hpHi := population_le_fifteen hN (by omega : 1 ≤ M)
      (by omega : M < 2 * M)
    have hpLoR : 4 * (M : ℝ) ≤ population N M := by exact_mod_cast hpLo
    have hpHiR : (population N M : ℝ) ≤ 15 * M := by exact_mod_cast hpHi
    constructor
    · calc
        (1 / 30 : ℝ) * population N M / M ≤ 1 / 2 := by
          apply (div_le_iff₀ hMr).2
          nlinarith
        _ ≤ Real.sin θ := hlo
    · calc
        Real.sin θ ≤ 1 := hhi
        _ ≤ (population N M : ℝ) / M := by
          apply (le_div_iff₀ hMr).2
          linarith

/-- Sine and population are comparable on every occupied noncap band. -/
theorem polar_sin_comparison {N j : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) (hj2 : 2 ≤ j)
    (hjlast : j < 2 * bandParameter N - 1) {θ : ℝ}
    (hθ : θ ∈ polarBand N j) :
    (1 / 30 : ℝ) * population N j / bandParameter N ≤ Real.sin θ ∧
      Real.sin θ ≤ (population N j : ℝ) / bandParameter N := by
  let M := bandParameter N
  by_cases hjM : j ≤ M
  · exact north_central_polar_sin_comparison hN hM hj2 hjM hθ
  · let k := 2 * M - j
    have hk2 : 2 ≤ k := by dsimp [k]; omega
    have hkM : k ≤ M := by dsimp [k]; omega
    have hjmax : j < 2 * M := by omega
    have href : Real.pi - θ ∈ polarBand N k :=
      polarBand_reflect hN (by omega : 1 ≤ j) hjmax hθ
    have hcomp := north_central_polar_sin_comparison hN hM hk2 hkM href
    have hpop : population N k = population N j := by
      have h := population_reflect hN (j := k)
        (by dsimp [k]; omega : 1 ≤ k)
        (by dsimp [k]; omega : k < 2 * M)
      have hidx : 2 * M - k = j := by dsimp [k]; omega
      change population N (2 * M - k) = population N k at h
      rw [hidx] at h
      exact h.symm
    rw [hpop, Real.sin_pi_sub] at hcomp
    exact hcomp

/-- Telescoping the uniform widths controls angular boundary separation. -/
theorem polar_boundary_difference_bounds {N a b : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) (hab : a ≤ b)
    (hb : b < 2 * bandParameter N) :
    ((b : ℝ) - a) / (4 * bandParameter N) ≤
      Real.arccos (boundary N b) - Real.arccos (boundary N a) ∧
    Real.arccos (boundary N b) - Real.arccos (boundary N a) ≤
      15 * ((b : ℝ) - a) / bandParameter N := by
  revert hb
  induction b, hab using Nat.le_induction with
  | base =>
      intro _
      constructor <;> simp
  | succ b hab ih =>
      intro hb
      have hb' : b < 2 * bandParameter N := by omega
      obtain ⟨hlo, hhi⟩ := ih hb'
      have hwlo := polar_width_lower hN (j := b + 1) (by omega) (by omega)
      have hwhi := polar_width_upper hN hM (j := b + 1) (by omega) (by omega)
      constructor
      · calc
          (((b + 1 : ℕ) : ℝ) - a) / (4 * bandParameter N) =
              ((b : ℝ) - a) / (4 * bandParameter N) +
                1 / (4 * bandParameter N) := by push_cast; ring
          _ ≤ (Real.arccos (boundary N b) - Real.arccos (boundary N a)) +
                (Real.arccos (boundary N (b + 1)) -
                  Real.arccos (boundary N b)) := add_le_add hlo (by simpa using hwlo)
          _ = Real.arccos (boundary N (b + 1)) -
                Real.arccos (boundary N a) := by ring
      · calc
          Real.arccos (boundary N (b + 1)) - Real.arccos (boundary N a) =
              (Real.arccos (boundary N b) - Real.arccos (boundary N a)) +
                (Real.arccos (boundary N (b + 1)) -
                  Real.arccos (boundary N b)) := by ring
          _ ≤ 15 * ((b : ℝ) - a) / bandParameter N +
                15 / bandParameter N := add_le_add hhi (by simpa using hwhi)
          _ = 15 * ((((b + 1 : ℕ) : ℝ) - a)) /
                bandParameter N := by push_cast; ring

/-- Separated bands have an angular gap comparable to their label separation. -/
theorem ordered_polar_separation {N : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) (j k : RingIndex N)
    (hjk : j.val + 2 ≤ k.val) {θ ψ : ℝ}
    (hθ : θ ∈ polarBand N (j.val + 1))
    (hψ : ψ ∈ polarBand N (k.val + 1)) :
    ((k.val : ℝ) - j.val) / (8 * bandParameter N) ≤ ψ - θ ∧
      ψ - θ ≤ 30 * ((k.val : ℝ) - j.val) / bandParameter N := by
  let M := bandParameter N
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hgap : (2 : ℝ) ≤ (k.val : ℝ) - j.val := by
    have hcast : (j.val : ℝ) + 2 ≤ k.val := by exact_mod_cast hjk
    linarith
  have hkmax : k.val + 1 < 2 * M := by
    have hk := k.isLt
    dsimp [M] at *
    omega
  have hlow := (polar_boundary_difference_bounds hN hM
    (a := j.val + 1) (b := k.val) (by omega) (by omega)).1
  have hhigh := (polar_boundary_difference_bounds hN hM
    (a := j.val) (b := k.val + 1) (by omega) hkmax).2
  have hlow' : ((k.val : ℝ) - (j.val + 1)) / (4 * M) ≤
      Real.arccos (boundary N k.val) -
        Real.arccos (boundary N (j.val + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlow
  change Real.arccos (boundary N j.val) ≤ θ ∧
    θ ≤ Real.arccos (boundary N (j.val + 1)) at hθ
  change Real.arccos (boundary N k.val) ≤ ψ ∧
    ψ ≤ Real.arccos (boundary N (k.val + 1)) at hψ
  have hnumlo : ((k.val : ℝ) - j.val) / (8 * M) ≤
      ((k.val : ℝ) - (j.val + 1)) / (4 * M) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * M)
      (by positivity : (0 : ℝ) < 4 * M)).2
    nlinarith
  have hnumhi : 15 * (((k.val + 1 : ℕ) : ℝ) - j.val) / M ≤
      30 * ((k.val : ℝ) - j.val) / M := by
    apply (div_le_div_iff₀ hMr hMr).2
    push_cast
    nlinarith
  constructor
  · calc
      ((k.val : ℝ) - j.val) / (8 * M) ≤
          ((k.val : ℝ) - (j.val + 1)) / (4 * M) := hnumlo
      _ ≤ Real.arccos (boundary N k.val) -
          Real.arccos (boundary N (j.val + 1)) := hlow'
      _ ≤ ψ - θ := by linarith [hθ.2, hψ.1]
  · calc
      ψ - θ ≤ Real.arccos (boundary N (k.val + 1)) -
          Real.arccos (boundary N j.val) := by linarith [hθ.1, hψ.2]
      _ ≤ 15 * (((k.val + 1 : ℕ) : ℝ) - j.val) / M := hhigh
      _ ≤ 30 * ((k.val : ℝ) - j.val) / M := hnumhi

/-- Absolute angular separation for nonadjacent occupied bands. -/
theorem polar_separation {N : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) (j k : RingIndex N)
    (hjk : 2 ≤ |(j.val : ℤ) - k.val|) {θ ψ : ℝ}
    (hθ : θ ∈ polarBand N (j.val + 1))
    (hψ : ψ ∈ polarBand N (k.val + 1)) :
    (1 / 30 : ℝ) * |(j.val : ℝ) - k.val| / bandParameter N ≤ |θ - ψ| ∧
      |θ - ψ| ≤ 30 * |(j.val : ℝ) - k.val| / bandParameter N := by
  have hcase : j.val + 2 ≤ k.val ∨ k.val + 2 ≤ j.val := by
    by_cases hle : j.val ≤ k.val
    · left
      have hnon : (j.val : ℤ) - k.val ≤ 0 := by omega
      rw [abs_of_nonpos hnon] at hjk
      omega
    · right
      have hnon : 0 ≤ (j.val : ℤ) - k.val := by omega
      rw [abs_of_nonneg hnon] at hjk
      omega
  have hMr : (0 : ℝ) < bandParameter N := by
    exact_mod_cast (by omega : 0 < bandParameter N)
  rcases hcase with hforward | hback
  · obtain ⟨hlo, hhi⟩ := ordered_polar_separation hN hM j k hforward hθ hψ
    have hgap : (0 : ℝ) ≤ (k.val : ℝ) - j.val := by
      have hcast : (j.val : ℝ) ≤ k.val := by exact_mod_cast (by omega : j.val ≤ k.val)
      linarith
    have hangle : θ ≤ ψ := by
      have hdiv : 0 ≤ ((k.val : ℝ) - j.val) / (8 * bandParameter N) := by positivity
      linarith
    have habsindex : |(j.val : ℝ) - k.val| = (k.val : ℝ) - j.val := by
      rw [abs_of_nonpos (by linarith : (j.val : ℝ) - k.val ≤ 0)]
      ring
    have habsangle : |θ - ψ| = ψ - θ := by
      rw [abs_of_nonpos (by linarith : θ - ψ ≤ 0)]
      ring
    rw [habsindex, habsangle]
    constructor
    · calc
        (1 / 30 : ℝ) * ((k.val : ℝ) - j.val) / bandParameter N ≤
            ((k.val : ℝ) - j.val) / (8 * bandParameter N) := by
              apply (div_le_div_iff₀ hMr (by positivity : (0 : ℝ) <
                8 * bandParameter N)).2
              nlinarith
        _ ≤ ψ - θ := hlo
    · exact hhi
  · obtain ⟨hlo, hhi⟩ := ordered_polar_separation hN hM k j hback hψ hθ
    have hgap : (0 : ℝ) ≤ (j.val : ℝ) - k.val := by
      have hcast : (k.val : ℝ) ≤ j.val := by exact_mod_cast (by omega : k.val ≤ j.val)
      linarith
    have hangle : ψ ≤ θ := by
      have hdiv : 0 ≤ ((j.val : ℝ) - k.val) / (8 * bandParameter N) := by positivity
      linarith
    have habsindex : |(j.val : ℝ) - k.val| = (j.val : ℝ) - k.val :=
      abs_of_nonneg hgap
    have habsangle : |θ - ψ| = θ - ψ :=
      abs_of_nonneg (sub_nonneg.mpr hangle)
    rw [habsindex, habsangle]
    constructor
    · calc
        (1 / 30 : ℝ) * ((j.val : ℝ) - k.val) / bandParameter N ≤
            ((j.val : ℝ) - k.val) / (8 * bandParameter N) := by
              apply (div_le_div_iff₀ hMr (by positivity : (0 : ℝ) <
                8 * bandParameter N)).2
              nlinarith
        _ ≤ θ - ψ := hlo
    · exact hhi

/-- The full angular geometry contract for the midpoint Diamond construction. -/
theorem angular_geometry : AngularGeometry := by
  refine ⟨(1 / 30 : ℝ), 30, by norm_num, by norm_num, ?_⟩
  intro N hM
  have hN : 4 ≤ N := by
    have hlo := (bandParameter_bounds N).1
    nlinarith
  have hMr : (0 : ℝ) < bandParameter N := by
    exact_mod_cast (by omega : 0 < bandParameter N)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hj1 : 1 ≤ j.val + 1 := by omega
    have hj2 : j.val + 1 < 2 * bandParameter N := by
      have hj := j.isLt
      omega
    have hlo := polar_width_lower hN hj1 hj2
    have hhi := polar_width_upper hN hM hj1 hj2
    constructor
    · calc
        (1 / 30 : ℝ) / bandParameter N ≤
            1 / (4 * bandParameter N) := by
              apply (div_le_div_iff₀ hMr (by positivity : (0 : ℝ) <
                4 * bandParameter N)).2
              nlinarith
        _ ≤ Real.arccos (boundary N (j.val + 1)) -
            Real.arccos (boundary N j.val) := by simpa using hlo
    · calc
        Real.arccos (boundary N (j.val + 1)) -
            Real.arccos (boundary N j.val) ≤
              15 / bandParameter N := by simpa using hhi
        _ ≤ 30 / bandParameter N := by
          apply (div_le_div_iff₀ hMr hMr).2
          nlinarith
  · intro j hjfirst hjlast θ hθ
    have hj2 : 2 ≤ j.val + 1 := by omega
    have hjlast' : j.val + 1 < 2 * bandParameter N - 1 := by
      have hj := j.isLt
      omega
    have hcomp := polar_sin_comparison hN hM hj2 hjlast' hθ
    constructor
    · exact hcomp.1
    · calc
        Real.sin θ ≤ (population N (j.val + 1) : ℝ) /
            bandParameter N := hcomp.2
        _ ≤ 30 * population N (j.val + 1) / bandParameter N := by
          apply (div_le_div_iff₀ hMr hMr).2
          have hp : (0 : ℝ) ≤ population N (j.val + 1) := by positivity
          nlinarith
  · intro j k hjk θ hθ ψ hψ
    exact polar_separation hN hM j k hjk hθ hψ

end BEMOC.Definitive
