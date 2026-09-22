import BEMOCFormalization.AngularGeometry

namespace BEMOC.Definitive

/-- Squared chordal distance in polar coordinates and a longitude difference. -/
noncomputable def polarChordSquare (φ ψ θ : ℝ) : ℝ :=
  2 - 2 * (Real.cos φ * Real.cos ψ +
    Real.sin φ * Real.sin ψ * Real.cos θ)

/-- The half-angle form of the cosine drop. -/
theorem one_sub_cos_eq_two_sin_sq (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have hc := Real.cos_two_mul (x / 2)
  have hs := Real.sin_sq_add_cos_sq (x / 2)
  have htwo : 2 * (x / 2) = x := by ring
  rw [htwo] at hc
  nlinarith

/-- Exact decomposition into latitudinal and longitudinal chord terms. -/
theorem polarChordSquare_half_angle (φ ψ θ : ℝ) :
    polarChordSquare φ ψ θ =
      4 * Real.sin ((φ - ψ) / 2) ^ 2 +
      4 * Real.sin φ * Real.sin ψ * Real.sin (θ / 2) ^ 2 := by
  have hc := Real.cos_sub φ ψ
  have hlat := one_sub_cos_eq_two_sin_sq (φ - ψ)
  have hlon := one_sub_cos_eq_two_sin_sq θ
  have hlonMul := congrArg (fun u : ℝ =>
    2 * Real.sin φ * Real.sin ψ * u) hlon
  unfold polarChordSquare
  rw [hc] at hlat
  nlinarith [hlonMul]

/-- A half-angle sine square is comparable to the corresponding Euclidean square. -/
theorem half_sine_square_bounds {x : ℝ} (hx : |x| ≤ Real.pi) :
    x ^ 2 / 4 ≤ 4 * Real.sin (x / 2) ^ 2 ∧
      4 * Real.sin (x / 2) ^ 2 ≤ x ^ 2 := by
  have hxhalf : |x / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hx (by norm_num)
  have hsin := Real.mul_abs_le_abs_sin hxhalf
  have hsinhi : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcoef : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hπ).2
    nlinarith [Real.pi_le_four]
  have hhalfabs : (0 : ℝ) ≤ |x / 2| := abs_nonneg _
  have hsinlo : |x / 2| / 2 ≤ |Real.sin (x / 2)| := by
    calc
      |x / 2| / 2 = (1 / 2 : ℝ) * |x / 2| := by ring
      _ ≤ (2 / Real.pi) * |x / 2| :=
        mul_le_mul_of_nonneg_right hcoef hhalfabs
      _ ≤ |Real.sin (x / 2)| := hsin
  have hlowSq : (|x / 2| / 2) ^ 2 ≤ |Real.sin (x / 2)| ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsinlo)
      (add_nonneg (abs_nonneg (Real.sin (x / 2)))
        (by positivity : (0 : ℝ) ≤ |x / 2| / 2))]
  have hhighSq : |Real.sin (x / 2)| ^ 2 ≤ |x / 2| ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsinhi)
      (add_nonneg (abs_nonneg (x / 2)) (abs_nonneg (Real.sin (x / 2))))]
  constructor
  · calc
      x ^ 2 / 4 = 4 * (|x / 2| / 2) ^ 2 := by
        simp only [div_pow, sq_abs]
        ring
      _ ≤ 4 * |Real.sin (x / 2)| ^ 2 :=
        mul_le_mul_of_nonneg_left hlowSq (by norm_num)
      _ = 4 * Real.sin (x / 2) ^ 2 := by rw [sq_abs]
  · calc
      4 * Real.sin (x / 2) ^ 2 = 4 * |Real.sin (x / 2)| ^ 2 := by rw [sq_abs]
      _ ≤ 4 * |x / 2| ^ 2 :=
        mul_le_mul_of_nonneg_left hhighSq (by norm_num)
      _ = x ^ 2 := by rw [sq_abs]; ring

/-- The squared chord lies between fixed multiples of the polar model distance. -/
theorem polarChordSquare_comparison {φ ψ θ : ℝ}
    (hφ : φ ∈ Set.Icc (0 : ℝ) Real.pi)
    (hψ : ψ ∈ Set.Icc (0 : ℝ) Real.pi)
    (hθ : |θ| ≤ Real.pi) :
    (1 / 4 : ℝ) * ((φ - ψ) ^ 2 +
      Real.sin φ * Real.sin ψ * θ ^ 2) ≤ polarChordSquare φ ψ θ ∧
    polarChordSquare φ ψ θ ≤ (φ - ψ) ^ 2 +
      Real.sin φ * Real.sin ψ * θ ^ 2 := by
  have hdiff : |φ - ψ| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith [hφ.1, hφ.2, hψ.1, hψ.2]
  obtain ⟨hlatlo, hlathi⟩ := half_sine_square_bounds hdiff
  obtain ⟨hlonlo, hlonhi⟩ := half_sine_square_bounds hθ
  have hsinφ : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 hφ.2
  have hsinψ : 0 ≤ Real.sin ψ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hψ.1 hψ.2
  have hprod : 0 ≤ Real.sin φ * Real.sin ψ := mul_nonneg hsinφ hsinψ
  rw [polarChordSquare_half_angle]
  constructor
  · have hlon := mul_le_mul_of_nonneg_left hlonlo hprod
    nlinarith [hlatlo, hlon]
  · have hlon := mul_le_mul_of_nonneg_left hlonhi hprod
    nlinarith [hlathi, hlon]

/-- Converting polar angles to their height and radius coordinates. -/
theorem polarChordSquare_arccos {s t θ : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    polarChordSquare (Real.arccos s) (Real.arccos t) θ =
      2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
        Real.sqrt (1 - t ^ 2) * Real.cos θ := by
  rw [polarChordSquare, Real.cos_arccos hs.1 hs.2,
    Real.cos_arccos ht.1 ht.2, Real.sin_arccos, Real.sin_arccos]
  ring

/-- Chord comparison stated directly in the manuscript's height coordinates. -/
theorem heightChordSquare_comparison {s t θ : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hθ : |θ| ≤ Real.pi) :
    (1 / 4 : ℝ) * ((Real.arccos s - Real.arccos t) ^ 2 +
      Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * θ ^ 2) ≤
      2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
        Real.sqrt (1 - t ^ 2) * Real.cos θ ∧
      2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
        Real.sqrt (1 - t ^ 2) * Real.cos θ ≤
      (Real.arccos s - Real.arccos t) ^ 2 +
        Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - t ^ 2) * θ ^ 2 := by
  have hφ : Real.arccos s ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hψ : Real.arccos t ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have h := polarChordSquare_comparison hφ hψ hθ
  rw [polarChordSquare_arccos hs ht,
    Real.sin_arccos, Real.sin_arccos] at h
  exact h

/-- Angles in bands at most two labels apart differ by at most `45/M`. -/
theorem ordered_polarBand_near_angle_gap {N : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) (j k : RingIndex N)
    (hle : j.val ≤ k.val) (hnear : k.val ≤ j.val + 2)
    {φ ψ : ℝ} (hφ : φ ∈ polarBand N (j.val + 1))
    (hψ : ψ ∈ polarBand N (k.val + 1)) :
    |φ - ψ| ≤ 45 / bandParameter N := by
  have hMr : (0 : ℝ) < bandParameter N := by
    exact_mod_cast (by omega : 0 < bandParameter N)
  change Real.arccos (boundary N j.val) ≤ φ ∧
    φ ≤ Real.arccos (boundary N (j.val + 1)) at hφ
  change Real.arccos (boundary N k.val) ≤ ψ ∧
    ψ ≤ Real.arccos (boundary N (k.val + 1)) at hψ
  have hbound := (polar_boundary_difference_bounds hN hM
    (a := j.val) (b := k.val + 1) (by omega) (by
      have hk := k.isLt
      omega)).2
  have hordered := (polar_boundary_difference_bounds hN hM
    (a := j.val) (b := k.val) hle (by
      have hk := k.isLt
      omega)).1
  have hwidth := polar_width_upper hN hM
    (j := j.val + 1) (by omega) (by
      have hj := j.isLt
      omega)
  have hgapr : ((k.val + 1 : ℕ) : ℝ) - j.val ≤ 3 := by
    have hcast : (k.val : ℝ) + 1 ≤ (j.val : ℝ) + 3 := by
      exact_mod_cast (by omega : k.val + 1 ≤ j.val + 3)
    push_cast
    linarith
  have hbound45 : 15 * (((k.val + 1 : ℕ) : ℝ) - j.val) /
      bandParameter N ≤ 45 / bandParameter N := by
    apply (div_le_div_iff₀ hMr hMr).2
    nlinarith
  have hψφ : ψ - φ ≤ 45 / bandParameter N := by
    calc
      ψ - φ ≤ Real.arccos (boundary N (k.val + 1)) -
          Real.arccos (boundary N j.val) := by linarith [hφ.1, hψ.2]
      _ ≤ 15 * (((k.val + 1 : ℕ) : ℝ) - j.val) /
          bandParameter N := hbound
      _ ≤ 45 / bandParameter N := hbound45
  have hφψ : φ - ψ ≤ 45 / bandParameter N := by
    have hwidth' : Real.arccos (boundary N (j.val + 1)) -
        Real.arccos (boundary N j.val) ≤ 15 / bandParameter N := by
      simpa using hwidth
    have h15 : (15 : ℝ) / bandParameter N ≤ 45 / bandParameter N := by
      apply (div_le_div_iff₀ hMr hMr).2
      nlinarith
    have hangleOrder : Real.arccos (boundary N j.val) ≤
        Real.arccos (boundary N k.val) := by
      have hcast : (j.val : ℝ) ≤ k.val := by exact_mod_cast hle
      have hnon : 0 ≤ ((k.val : ℝ) - j.val) /
          (4 * bandParameter N) := by
        exact div_nonneg (sub_nonneg.mpr hcast) (by positivity)
      linarith [hordered]
    calc
      φ - ψ ≤ Real.arccos (boundary N (j.val + 1)) -
          Real.arccos (boundary N k.val) := by linarith [hφ.2, hψ.1]
      _ ≤ Real.arccos (boundary N (j.val + 1)) -
          Real.arccos (boundary N j.val) := by linarith [hangleOrder]
      _ ≤ 15 / bandParameter N := hwidth'
      _ ≤ 45 / bandParameter N := h15
  exact abs_le.mpr ⟨by linarith, hφψ⟩

/-- Angles in bands at most two labels apart differ by at most `45/M`. -/
theorem polarBand_near_angle_gap {N : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) (j k : RingIndex N)
    (hjk : |(j.val : ℤ) - k.val| ≤ 2)
    {φ ψ : ℝ} (hφ : φ ∈ polarBand N (j.val + 1))
    (hψ : ψ ∈ polarBand N (k.val + 1)) :
    |φ - ψ| ≤ 45 / bandParameter N := by
  rcases le_total j.val k.val with hle | hle
  · have hnear : k.val ≤ j.val + 2 := by
      have hnon : (j.val : ℤ) - k.val ≤ 0 := by omega
      rw [abs_of_nonpos hnon] at hjk
      omega
    exact ordered_polarBand_near_angle_gap hN hM j k hle hnear hφ hψ
  · have hnear : j.val ≤ k.val + 2 := by
      have hnon : 0 ≤ (j.val : ℤ) - k.val := by omega
      rw [abs_of_nonneg hnon] at hjk
      omega
    have h := ordered_polarBand_near_angle_gap hN hM k j hle hnear hψ hφ
    simpa [abs_sub_comm] using h

/-- Radius at any height in a noncap band is comparable to its population over `M`. -/
theorem band_radius_comparison {N : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) (j : RingIndex N)
    (hjfirst : j.val ≠ 0)
    (hjlast : j.val + 1 ≠ 2 * bandParameter N - 1)
    {s : ℝ} (hs : s ∈ band N (j.val + 1)) :
    (1 / 30 : ℝ) * population N (j.val + 1) / bandParameter N ≤
      Real.sqrt (1 - s ^ 2) ∧
    Real.sqrt (1 - s ^ 2) ≤
      (population N (j.val + 1) : ℝ) / bandParameter N := by
  have hj2 : 2 ≤ j.val + 1 := by omega
  have hjtop : j.val + 1 < 2 * bandParameter N - 1 := by
    have hj := j.isLt
    omega
  have hs' : boundary N (j.val + 1) ≤ s ∧
      s ≤ boundary N j.val := by
    simpa [band] using hs
  have hangle : Real.arccos s ∈ polarBand N (j.val + 1) := by
    change Real.arccos (boundary N j.val) ≤ Real.arccos s ∧
      Real.arccos s ≤ Real.arccos (boundary N (j.val + 1))
    exact ⟨Real.arccos_le_arccos hs'.2,
      Real.arccos_le_arccos hs'.1⟩
  have hcomp := polar_sin_comparison hN hM hj2 hjtop hangle
  simpa only [Real.sin_arccos] using hcomp

/-- Height membership becomes polar-angle membership under `arccos`. -/
theorem arccos_mem_polarBand_of_mem_band {N j : ℕ} {s : ℝ}
    (hs : s ∈ band N j) : Real.arccos s ∈ polarBand N j := by
  rcases hs with ⟨hlo, hhi⟩
  exact ⟨Real.arccos_le_arccos hhi,
    Real.arccos_le_arccos hlo⟩

/-- Nearby height bands have polar-angle gap at most `45/M`. -/
theorem near_band_arccos_gap {N : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) (j k : RingIndex N)
    (hjk : |(j.val : ℤ) - k.val| ≤ 2)
    {s t : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1)) :
    |Real.arccos s - Real.arccos t| ≤ 45 / bandParameter N :=
  polarBand_near_angle_gap hN hM j k hjk
    (arccos_mem_polarBand_of_mem_band hs)
    (arccos_mem_polarBand_of_mem_band ht)

/-- Separated height bands inherit the angular gap bounds. -/
theorem separated_band_arccos_gap {N : ℕ} (hN : 4 ≤ N)
    (hM : 16 ≤ bandParameter N) (j k : RingIndex N)
    (hjk : 2 ≤ |(j.val : ℤ) - k.val|)
    {s t : ℝ} (hs : s ∈ band N (j.val + 1))
    (ht : t ∈ band N (k.val + 1)) :
    (1 / 30 : ℝ) * |(j.val : ℝ) - k.val| / bandParameter N ≤
      |Real.arccos s - Real.arccos t| ∧
    |Real.arccos s - Real.arccos t| ≤
      30 * |(j.val : ℝ) - k.val| / bandParameter N :=
  polar_separation hN hM j k hjk
    (arccos_mem_polarBand_of_mem_band hs)
    (arccos_mem_polarBand_of_mem_band ht)

end BEMOC.Definitive
