import BEMOCFormalization.ConcreteWithinRing

/-!
# BEMOC latitude-band quadrature

This file records the *uncombined* three-atom rule on one BEMOC latitude
band.  When neighbouring bands are added, its endpoint atoms are exactly the
shared-boundary rings in `bemocRingFamily`.  Keeping a single-band rule here
is useful because it makes the two moment cancellations explicit before any
kernel estimates are introduced.
-/

open scoped BigOperators
open Set MeasureTheory

namespace BEMOC

/-- The atomic part of the BEMOC latitude rule on one band.  The midpoint
atom has the remainder included in its population; each endpoint gets one
sixth of the divisible part. -/
noncomputable def bandAtomicValue (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) : ℝ :=
  (midpointRingPopulation N j : ℝ) * f (bandMidpointHeight N j) +
    (boundarySixth N j : ℝ) * f (bandBoundaryHeight N j) +
      (boundarySixth N j : ℝ) * f (bandBoundaryHeight N (j + 1))

/-- The continuous height rule on the same band.  The orientation agrees
with the north-to-south ordering of `bandBoundaryHeight`. -/
noncomputable def bandContinuousValue (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) : ℝ :=
  (N / 2 : ℝ) * ∫ t in bandBoundaryHeight N (j + 1)..bandBoundaryHeight N j,
    f t

/-- The north-to-south height width of a BEMOC band. -/
noncomputable def bandWidth (N : ℕ)
    (j : Fin (bandTailCount N + 1)) : ℝ :=
  bandBoundaryHeight N j - bandBoundaryHeight N (j + 1)

/-- The signed one-band latitude quadrature error. -/
noncomputable def bandError (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) : ℝ :=
  bandAtomicValue N j f - bandContinuousValue N j f

theorem bandAtomicValue_const (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (c : ℝ) :
    bandAtomicValue N j (fun _ ↦ c) = (finiteBandPopulation N j : ℝ) * c := by
  rw [bandAtomicValue]
  have hle := twice_boundarySixth_le N j
  have hpop : midpointRingPopulation N j + 2 * boundarySixth N j =
      finiteBandPopulation N j := by
    rw [midpointRingPopulation, Nat.sub_add_cancel hle]
  have hpopR : (midpointRingPopulation N j : ℝ) +
      2 * (boundarySixth N j : ℝ) = (finiteBandPopulation N j : ℝ) := by
    exact_mod_cast hpop
  calc
    _ = ((midpointRingPopulation N j : ℝ) +
        2 * (boundarySixth N j : ℝ)) * c := by ring
    _ = _ := by rw [hpopR]

/-- The atomic rule has the stated zeroth moment. -/
theorem bandAtomicValue_one (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    bandAtomicValue N j (fun _ ↦ 1) = (finiteBandPopulation N j : ℝ) := by
  simpa using bandAtomicValue_const N j 1

/-- The midpoint/endpoints part of the atomic rule has exactly the first
moment of a mass placed at the band midpoint. -/
theorem bandAtomicValue_id (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    bandAtomicValue N j id =
      (finiteBandPopulation N j : ℝ) * bandMidpointHeight N j := by
  rw [bandAtomicValue]
  change
    (midpointRingPopulation N j : ℝ) * bandMidpointHeight N j +
        (boundarySixth N j : ℝ) * bandBoundaryHeight N j +
          (boundarySixth N j : ℝ) * bandBoundaryHeight N (j + 1) = _
  rw [bandMidpointHeight]
  have hle := twice_boundarySixth_le N j
  have hpop : midpointRingPopulation N j + 2 * boundarySixth N j =
      finiteBandPopulation N j := by
    rw [midpointRingPopulation, Nat.sub_add_cancel hle]
  have hpopR : (midpointRingPopulation N j : ℝ) +
      2 * (boundarySixth N j : ℝ) = (finiteBandPopulation N j : ℝ) := by
    exact_mod_cast hpop
  rw [← hpopR]
  ring

private theorem finiteBandPopulation_eq_list_get (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    finiteBandPopulation N j = (symmetricBandPopulations N)[j.1]'(by
      rw [length_symmetricBandPopulations_eq_tail_succ]
      exact j.2) := by
  simp [finiteBandPopulation]

/-- Consecutive BEMOC band boundaries differ by the height mass of that
band.  This is the bridge between the interval rule and its three atoms. -/
theorem bandBoundaryHeight_sub_succ (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    bandBoundaryHeight N j - bandBoundaryHeight N (j + 1) =
      2 * (finiteBandPopulation N j : ℝ) / N := by
  rw [bandBoundaryHeight, bandBoundaryHeight]
  have hj : j.1 < (symmetricBandPopulations N).length := by
    rw [length_symmetricBandPopulations_eq_tail_succ]
    exact j.2
  have htake := List.sum_take_succ (symmetricBandPopulations N) j.1 hj
  rw [finiteBandPopulation_eq_list_get]
  have htakeR :
      (((symmetricBandPopulations N).take (j.1 + 1)).sum : ℝ) =
        ((symmetricBandPopulations N).take j.1).sum +
          (symmetricBandPopulations N)[j.1]'hj := by
    exact_mod_cast htake
  rw [htakeR]
  ring

theorem bandWidth_eq_population {N : ℕ}
    (j : Fin (bandTailCount N + 1)) :
    bandWidth N j = 2 * (finiteBandPopulation N j : ℝ) / N := by
  exact bandBoundaryHeight_sub_succ N j

theorem bandWidth_nonneg {N : ℕ}
    (j : Fin (bandTailCount N + 1)) : 0 ≤ bandWidth N j := by
  rw [bandWidth_eq_population]
  positivity

/-- In a northern ordinary band the width is the explicit BEMOC scale
`2(4(j+1)-1)/N`. -/
theorem bandWidth_north {N : ℕ}
    (j : Fin (bandTailCount N + 1))
    (hj : (j : ℕ) < bandCount N - 1) :
    bandWidth N j = 2 * (ordinaryPopulation ((j : ℕ) + 1) : ℝ) / N := by
  rw [bandWidth_eq_population, concrete_finiteBandPopulation_north j hj]

/-- The defining square-root choice of `bandCount` gives the coarse but
uniform comparison needed for all northern band scales. -/
theorem four_mul_bandCount_sq_le (N : ℕ) :
    4 * bandCount N ^ 2 ≤ N := by
  have hsq := bandCount_sq_le N
  have hdiv : 4 * (N / 4) ≤ N := by omega
  exact (Nat.mul_le_mul_left 4 hsq).trans hdiv

theorem bemoc_N_le_twenty_bandCount_sq {N : ℕ}
    (hM : 1 ≤ bandCount N) : N ≤ 20 * bandCount N ^ 2 := by
  have hsqrt := Nat.lt_succ_sqrt (N / 4)
  have hdiv : N ≤ 4 * (N / 4) + 3 := by omega
  have hroot : N / 4 < (bandCount N + 1) ^ 2 := by
    simpa [bandCount, pow_two] using hsqrt
  have hstep : 4 * (N / 4) + 3 < 4 * (bandCount N + 1) ^ 2 + 3 := by
    nlinarith
  exact hdiv.trans (Nat.le_of_lt hstep) |>.trans (by nlinarith)

theorem ordinaryPopulation_between_three_and_four_mul (d : ℕ)
    (hd : 1 ≤ d) : 3 * d ≤ ordinaryPopulation d ∧ ordinaryPopulation d ≤ 4 * d := by
  simp [ordinaryPopulation]
  omega

/-- Northern BEMOC bands have height widths comparable to
`(j+1)/M²`, with deliberately loose universal constants. -/
theorem northern_bandWidth_scale {N : ℕ}
    (hM : 1 ≤ bandCount N) (j : Fin (bandTailCount N + 1))
    (hj : (j : ℕ) < bandCount N - 1) :
    (3 / 10 : ℝ) * (((j : ℕ) + 1 : ℕ) : ℝ) / (bandCount N : ℝ) ^ 2 ≤
      bandWidth N j ∧
      bandWidth N j ≤ 2 * (((j : ℕ) + 1 : ℕ) : ℝ) / (bandCount N : ℝ) ^ 2 := by
  let d : ℕ := (j : ℕ) + 1
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hpop := ordinaryPopulation_between_three_and_four_mul d hd
  have hNlo := four_mul_bandCount_sq_le N
  have hNhi := bemoc_N_le_twenty_bandCount_sq hM
  have hMpos : 0 < (bandCount N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hdR : 0 ≤ (d : ℝ) := by positivity
  have hM2 : 0 < (bandCount N : ℝ) ^ 2 := sq_pos_of_pos hMpos
  have hNloR : 4 * (bandCount N : ℝ) ^ 2 ≤ N := by exact_mod_cast hNlo
  have hNhiR : (N : ℝ) ≤ 20 * (bandCount N : ℝ) ^ 2 := by exact_mod_cast hNhi
  have hNpos : 0 < (N : ℝ) := by
    exact lt_of_lt_of_le (by positivity) hNloR
  have hpoploR : 3 * (d : ℝ) ≤ ordinaryPopulation d := by exact_mod_cast hpop.1
  have hpophiR : (ordinaryPopulation d : ℝ) ≤ 4 * (d : ℝ) := by exact_mod_cast hpop.2
  have hwidth : bandWidth N j = 2 * (ordinaryPopulation d : ℝ) / N := by
    simpa [d] using bandWidth_north j hj
  rw [hwidth]
  constructor
  · apply (div_le_div_iff₀ hM2 hNpos).2
    have hmul := mul_le_mul_of_nonneg_right hNhiR hdR
    nlinarith
  · apply (div_le_div_iff₀ hNpos hM2).2
    have hmul := mul_le_mul_of_nonneg_right hNloR hdR
    nlinarith

theorem bandContinuousValue_const {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) (c : ℝ) :
    bandContinuousValue N j (fun _ ↦ c) =
      (finiteBandPopulation N j : ℝ) * c := by
  rw [bandContinuousValue, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  rw [bandBoundaryHeight_sub_succ]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem bandContinuousValue_one {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) :
    bandContinuousValue N j (fun _ ↦ 1) = (finiteBandPopulation N j : ℝ) := by
  simpa using bandContinuousValue_const hN j 1

theorem bandContinuousValue_id {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) :
    bandContinuousValue N j id =
      (finiteBandPopulation N j : ℝ) * bandMidpointHeight N j := by
  unfold bandContinuousValue
  change (N / 2 : ℝ) *
      ∫ t in bandBoundaryHeight N (j + 1)..bandBoundaryHeight N j, t = _
  rw [integral_id]
  let a : ℝ := bandBoundaryHeight N (j + 1)
  let b : ℝ := bandBoundaryHeight N j
  change (N / 2 : ℝ) * ((b ^ 2 - a ^ 2) / 2) =
    (finiteBandPopulation N j : ℝ) * ((b + a) / 2)
  have hwidth : b - a = 2 * (finiteBandPopulation N j : ℝ) / N := by
    exact bandBoundaryHeight_sub_succ N j
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show b ^ 2 - a ^ 2 = (b - a) * (b + a) by ring, hwidth]
  field_simp
  ring

/-- The BEMOC latitude rule is exact on constants band by band. -/
theorem bandError_const {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) (c : ℝ) :
    bandError N j (fun _ ↦ c) = 0 := by
  rw [bandError, bandAtomicValue_const, bandContinuousValue_const hN]
  ring

theorem bandError_one {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) :
    bandError N j (fun _ ↦ 1) = 0 := by
  simpa using bandError_const hN j 1

/-- The BEMOC latitude rule is exact on linear functions band by band. -/
theorem bandError_id {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) : bandError N j id = 0 := by
  rw [bandError, bandAtomicValue_id, bandContinuousValue_id hN]
  ring

theorem bandAtomicValue_add (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (f g : ℝ → ℝ) :
    bandAtomicValue N j (fun t ↦ f t + g t) =
      bandAtomicValue N j f + bandAtomicValue N j g := by
  unfold bandAtomicValue
  ring

theorem bandAtomicValue_const_mul (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (c : ℝ) (f : ℝ → ℝ) :
    bandAtomicValue N j (fun t ↦ c * f t) = c * bandAtomicValue N j f := by
  unfold bandAtomicValue
  ring

theorem bandContinuousValue_add (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (f g : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hg : IntervalIntegrable g volume (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    bandContinuousValue N j (fun t ↦ f t + g t) =
      bandContinuousValue N j f + bandContinuousValue N j g := by
  unfold bandContinuousValue
  change (N / 2 : ℝ) *
      ∫ t in bandBoundaryHeight N (j + 1)..bandBoundaryHeight N j, f t + g t = _
  rw [intervalIntegral.integral_add hf hg]
  ring

theorem bandContinuousValue_const_mul (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (c : ℝ) (f : ℝ → ℝ) :
    bandContinuousValue N j (fun t ↦ c * f t) = c * bandContinuousValue N j f := by
  unfold bandContinuousValue
  rw [intervalIntegral.integral_const_mul]
  ring

theorem bandError_add (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (f g : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j))
    (hg : IntervalIntegrable g volume (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j)) :
    bandError N j (fun t ↦ f t + g t) =
      bandError N j f + bandError N j g := by
  unfold bandError
  rw [bandAtomicValue_add, bandContinuousValue_add N j f g hf hg]
  ring

theorem bandError_const_mul (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (c : ℝ) (f : ℝ → ℝ) :
    bandError N j (fun t ↦ c * f t) = c * bandError N j f := by
  unfold bandError
  rw [bandAtomicValue_const_mul, bandContinuousValue_const_mul]
  ring

/-- The local rule annihilates every affine height function. -/
theorem bandError_affine {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) (a b : ℝ) :
    bandError N j (fun t ↦ a * t + b) = 0 := by
  have hid : IntervalIntegrable id volume (bandBoundaryHeight N (j + 1))
      (bandBoundaryHeight N j) := continuous_id.intervalIntegrable _ _
  have hone : IntervalIntegrable (fun _ : ℝ ↦ b) volume
      (bandBoundaryHeight N (j + 1)) (bandBoundaryHeight N j) :=
    continuous_const.intervalIntegrable _ _
  rw [show (fun t : ℝ ↦ a * t + b) =
      fun t ↦ a * id t + (fun _ : ℝ ↦ b) t by rfl,
    bandError_add N j _ _ (hid.const_mul a) hone,
    bandError_const_mul, bandError_id hN, bandError_const hN]
  ring

theorem bandError_zero {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) :
    bandError N j (fun _ ↦ 0) = 0 := by
  simpa using bandError_const hN j 0

/-- A two-variable error functional, used for the latitude-kernel blocks. -/
noncomputable def bandPairError (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) (K : ℝ → ℝ → ℝ) : ℝ :=
  bandError N j (fun s ↦ bandError N k (fun t ↦ K s t))

/-- A bounded test function has atomic band value bounded by mass times its
supremum.  This is the elementary polar-block estimate. -/
theorem abs_bandAtomicValue_le (N : ℕ)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ t, |f t| ≤ C) :
    |bandAtomicValue N j f| ≤ (finiteBandPopulation N j : ℝ) * C := by
  unfold bandAtomicValue
  have hm : 0 ≤ (midpointRingPopulation N j : ℝ) := by positivity
  have hb : 0 ≤ (boundarySixth N j : ℝ) := by positivity
  have hmid := hbound (bandMidpointHeight N j)
  have hleft := hbound (bandBoundaryHeight N j)
  have hright := hbound (bandBoundaryHeight N (j + 1))
  have hsum : midpointRingPopulation N j + 2 * boundarySixth N j =
      finiteBandPopulation N j := by
    rw [midpointRingPopulation, Nat.sub_add_cancel (twice_boundarySixth_le N j)]
  have hsumR : (midpointRingPopulation N j : ℝ) +
      2 * (boundarySixth N j : ℝ) = (finiteBandPopulation N j : ℝ) := by
    exact_mod_cast hsum
  calc
    |(midpointRingPopulation N j : ℝ) * f (bandMidpointHeight N j) +
        (boundarySixth N j : ℝ) * f (bandBoundaryHeight N j) +
          (boundarySixth N j : ℝ) * f (bandBoundaryHeight N (j + 1))| ≤
        |(midpointRingPopulation N j : ℝ) * f (bandMidpointHeight N j)| +
          |(boundarySixth N j : ℝ) * f (bandBoundaryHeight N j)| +
            |(boundarySixth N j : ℝ) * f (bandBoundaryHeight N (j + 1))| := by
          calc
            _ ≤ |(midpointRingPopulation N j : ℝ) * f (bandMidpointHeight N j) +
                (boundarySixth N j : ℝ) * f (bandBoundaryHeight N j)| +
                |(boundarySixth N j : ℝ) * f (bandBoundaryHeight N (j + 1))| :=
              abs_add_le _ _
            _ ≤ _ := by
              exact add_le_add_right (abs_add_le _ _) _
            _ = _ := by ring
    _ ≤ (midpointRingPopulation N j : ℝ) * C +
          (boundarySixth N j : ℝ) * C + (boundarySixth N j : ℝ) * C := by
          simp only [abs_mul, abs_of_nonneg hm, abs_of_nonneg hb]
          gcongr
    _ = (finiteBandPopulation N j : ℝ) * C := by rw [← hsumR]; ring

/-- The continuous part of a band rule obeys the same bounded-kernel mass
bound. -/
theorem abs_bandContinuousValue_le {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ t, |f t| ≤ C) :
    |bandContinuousValue N j f| ≤ (finiteBandPopulation N j : ℝ) * C := by
  unfold bandContinuousValue
  have hwidth := bandBoundaryHeight_sub_succ N j
  have hle : bandBoundaryHeight N (j + 1) ≤ bandBoundaryHeight N j := by
    rw [← sub_nonneg]
    rw [hwidth]
    positivity
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := bandBoundaryHeight N (j + 1)) (b := bandBoundaryHeight N j)
    (f := f) (C := C) (fun t ht ↦ by simpa [Real.norm_eq_abs] using hbound t)
  have hscale : 0 ≤ (N / 2 : ℝ) := by positivity
  rw [abs_mul, abs_of_nonneg hscale]
  calc
    (N / 2 : ℝ) * |∫ t in bandBoundaryHeight N (j + 1)..bandBoundaryHeight N j, f t| ≤
        (N / 2 : ℝ) * (C * |bandBoundaryHeight N j - bandBoundaryHeight N (j + 1)|) :=
      mul_le_mul_of_nonneg_left hint hscale
    _ = (finiteBandPopulation N j : ℝ) * C := by
      rw [abs_of_nonneg (sub_nonneg.mpr hle), hwidth]
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
      ring

/-- One-band variation bound in terms of the literal BEMOC band mass. -/
theorem abs_bandError_le_of_uniform_bound {N : ℕ} (hN : 0 < N)
    (j : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ t, |f t| ≤ C) :
    |bandError N j f| ≤ 2 * (finiteBandPopulation N j : ℝ) * C := by
  unfold bandError
  calc
    |bandAtomicValue N j f - bandContinuousValue N j f| ≤
        |bandAtomicValue N j f| + |bandContinuousValue N j f| := by
      calc
        _ = |bandAtomicValue N j f + -bandContinuousValue N j f| := by ring
        _ ≤ _ := by simpa using
          (abs_add_le (bandAtomicValue N j f) (-bandContinuousValue N j f))
    _ ≤ (finiteBandPopulation N j : ℝ) * C +
          (finiteBandPopulation N j : ℝ) * C := by
      gcongr
      · exact abs_bandAtomicValue_le N j f C hC hbound
      · exact abs_bandContinuousValue_le hN j f C hC hbound
    _ = 2 * (finiteBandPopulation N j : ℝ) * C := by ring

/-- Uniformly bounded kernels have a uniform two-band error bound.  This is
the estimate used for the finitely many rescaled polar rectangles. -/
theorem abs_bandPairError_le_of_uniform_bound {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1)) (K : ℝ → ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ s t, |K s t| ≤ C) :
    |bandPairError N j k K| ≤
      4 * (finiteBandPopulation N j : ℝ) * (finiteBandPopulation N k : ℝ) * C := by
  unfold bandPairError
  have hinner (s : ℝ) : |bandError N k (fun t ↦ K s t)| ≤
      2 * (finiteBandPopulation N k : ℝ) * C := by
    unfold bandError
    calc
      |bandAtomicValue N k (fun t ↦ K s t) - bandContinuousValue N k (fun t ↦ K s t)| ≤
          |bandAtomicValue N k (fun t ↦ K s t)| +
            |bandContinuousValue N k (fun t ↦ K s t)| := by
              calc
                _ = |bandAtomicValue N k (fun t ↦ K s t) +
                    -bandContinuousValue N k (fun t ↦ K s t)| := by ring
                _ ≤ _ := by simpa using
                  (abs_add_le (bandAtomicValue N k (fun t ↦ K s t))
                    (-bandContinuousValue N k (fun t ↦ K s t)))
      _ ≤ (finiteBandPopulation N k : ℝ) * C +
            (finiteBandPopulation N k : ℝ) * C := by
          gcongr
          · exact abs_bandAtomicValue_le N k _ C hC (hbound s)
          · exact abs_bandContinuousValue_le hN k _ C hC (hbound s)
      _ = 2 * (finiteBandPopulation N k : ℝ) * C := by ring
  have hD : 0 ≤ 2 * (finiteBandPopulation N k : ℝ) * C := by positivity
  unfold bandError
  calc
    |bandAtomicValue N j (fun s ↦ bandError N k (fun t ↦ K s t)) -
        bandContinuousValue N j (fun s ↦ bandError N k (fun t ↦ K s t))| ≤
        |bandAtomicValue N j (fun s ↦ bandError N k (fun t ↦ K s t))| +
          |bandContinuousValue N j (fun s ↦ bandError N k (fun t ↦ K s t))| := by
            calc
              _ = |bandAtomicValue N j (fun s ↦ bandError N k (fun t ↦ K s t)) +
                  -bandContinuousValue N j (fun s ↦ bandError N k (fun t ↦ K s t))| := by ring
              _ ≤ _ := by simpa using
                (abs_add_le (bandAtomicValue N j (fun s ↦ bandError N k (fun t ↦ K s t)))
                  (-bandContinuousValue N j (fun s ↦ bandError N k (fun t ↦ K s t))))
    _ ≤ (finiteBandPopulation N j : ℝ) *
          (2 * (finiteBandPopulation N k : ℝ) * C) +
        (finiteBandPopulation N j : ℝ) *
          (2 * (finiteBandPopulation N k : ℝ) * C) := by
        gcongr
        · exact abs_bandAtomicValue_le N j _ _ hD hinner
        · exact abs_bandContinuousValue_le hN j _ _ hD hinner
    _ = 4 * (finiteBandPopulation N j : ℝ) *
          (finiteBandPopulation N k : ℝ) * C := by ring

/-- Tensor-product functions factor through the two one-band errors. -/
theorem bandPairError_product (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) (f g : ℝ → ℝ) :
    bandPairError N j k (fun s t ↦ f s * g t) =
      bandError N j f * bandError N k g := by
  unfold bandPairError
  simp_rw [bandError_const_mul]
  rw [show (fun s ↦ f s * bandError N k g) =
      fun s ↦ bandError N k g * f s by
        funext s
        ring,
    bandError_const_mul]
  ring

/-- A kernel that is affine in its second height variable is killed by the
two-moment band-pair functional. -/
theorem bandPairError_affine_right {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1)) (f : ℝ → ℝ) (a b : ℝ) :
    bandPairError N j k (fun s t ↦ f s * (a * t + b)) = 0 := by
  rw [show (fun s t ↦ f s * (a * t + b)) =
      fun s t ↦ f s * (fun t ↦ a * t + b) t by rfl,
    bandPairError_product, bandError_affine hN]
  ring

/-- Summing the uncombined three-atom rules combines their endpoint atoms
into exactly the midpoint/shared-boundary BEMOC ring family. -/
theorem sum_bandAtomicValue_eq_bemocRingFamily {N : ℕ} (hN : 0 < N)
    (f : ℝ → ℝ) :
    (∑ j : Fin (bandTailCount N + 1), bandAtomicValue N j f) =
      ∑ p : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
        (bemocRingFamily N p).population * f (bemocRingFamily N p).height := by
  rw [Fintype.sum_sum_type]
  simp only [bandAtomicValue, bemocRingFamily, dif_pos hN]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have htop := Fin.sum_univ_succ
    (fun j : Fin (bandTailCount N + 1) ↦
      (boundarySixth N j : ℝ) * f (bandBoundaryHeight N j))
  have hbottom := Fin.sum_univ_castSucc
    (fun j : Fin (bandTailCount N + 1) ↦
      (boundarySixth N j : ℝ) * f (bandBoundaryHeight N (j + 1)))
  rw [boundarySixth_zero] at htop
  simp at htop
  rw [boundarySixth_last] at hbottom
  simp at hbottom
  rw [htop, hbottom]
  have hcombine :
      (∑ x : Fin (bandTailCount N),
          (boundarySixth N x.succ : ℝ) *
            f (bandBoundaryHeight N (x + 1))) +
        ∑ x : Fin (bandTailCount N),
          (boundarySixth N x.castSucc : ℝ) *
            f (bandBoundaryHeight N (x + 1)) =
      ∑ x : Fin (bandTailCount N),
        (sharedBoundaryPopulation N x : ℝ) *
          f (bandBoundaryHeight N (x + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [sharedBoundaryPopulation, Nat.cast_add]
    ring
  rw [add_assoc, hcombine]

private theorem sum_consecutive_intervalIntegrals (f : ℝ → ℝ)
    (hf : Continuous f) (H : ℕ → ℝ) : ∀ n : ℕ,
    (∑ j ∈ Finset.range n, ∫ x in H (j + 1)..H j, f x) =
      ∫ x in H n..H 0, f x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, add_comm]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

/-- The continuous pieces of the band rules concatenate to the uniform
height integral. -/
theorem sum_bandContinuousValue_eq_heightIntegral {N : ℕ} (hN : 0 < N)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∑ j : Fin (bandTailCount N + 1), bandContinuousValue N j f) =
      (N / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, f t := by
  unfold bandContinuousValue
  calc
    _ = (N / 2 : ℝ) *
        ∑ j : Fin (bandTailCount N + 1),
          ∫ t in bandBoundaryHeight N (j + 1)..bandBoundaryHeight N j, f t := by
        rw [Finset.mul_sum]
    _ = (N / 2 : ℝ) *
        ∑ j ∈ Finset.range (bandTailCount N + 1),
          ∫ t in bandBoundaryHeight N (j + 1)..bandBoundaryHeight N j, f t := by
        congr 1
        exact Fin.sum_univ_eq_sum_range
          (fun j ↦ ∫ t in bandBoundaryHeight N (j + 1)..bandBoundaryHeight N j, f t)
          (bandTailCount N + 1)
    _ = (N / 2 : ℝ) *
        ∫ t in bandBoundaryHeight N (bandTailCount N + 1)..bandBoundaryHeight N 0, f t := by
        rw [sum_consecutive_intervalIntegrals f hf (bandBoundaryHeight N)]
    _ = _ := by
        rw [bandBoundaryHeight_zero]
        have hfinal : bandBoundaryHeight N (bandTailCount N + 1) = -1 := by
          rw [← length_symmetricBandPopulations_eq_tail_succ]
          exact bandBoundaryHeight_final hN
        rw [hfinal]

/-- Exact scalar height-quadrature identity for the BEMOC band rule. -/
theorem sum_bandError_eq_bemocHeightQuadrature {N : ℕ} (hN : 0 < N)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∑ j : Fin (bandTailCount N + 1), bandError N j f) =
      (∑ p : Fin (bandTailCount N + 1) ⊕ Fin (bandTailCount N),
        (bemocRingFamily N p).population * f (bemocRingFamily N p).height) -
        (N / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, f t := by
  simp only [bandError]
  rw [Finset.sum_sub_distrib,
    sum_bandAtomicValue_eq_bemocRingFamily hN,
    sum_bandContinuousValue_eq_heightIntegral hN f hf]

end BEMOC
