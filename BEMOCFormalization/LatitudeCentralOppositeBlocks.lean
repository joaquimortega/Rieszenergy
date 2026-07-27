import BEMOCFormalization.LatitudeSmoothOppositeBlocks

/-!
# Concrete central and opposite-hemisphere latitude blocks

The central transition consists of a single distinguished band, so the
global diameter estimate gives an unconditional block bound.  For a smooth
opposite-hemisphere pair we also give a literal instantiation of the affine
remainder interface: take the whole kernel as the remainder and use the
uniform positive lower bound for every concrete band width.  This
instantiation is intentionally coarse, but it removes the logical premise
from `HasSmoothOppositeAffineRemainders` and checks the complete passage from
the concrete kernel to the mixed-remainder block theorem.
-/

open MeasureTheory Set

namespace BEMOC

/-- The central predicate really singles out the concrete central index. -/
theorem isCentralLatitudeBand_iff_eq_concreteCentralBandIndex
    {N : ℕ} (j : Fin (bandTailCount N + 1)) :
    IsCentralLatitudeBand N j ↔ j = concreteCentralBandIndex N := by
  unfold IsCentralLatitudeBand
  constructor
  · intro hj
    apply Fin.ext
    simpa [concreteCentralBandIndex] using hj
  · rintro rfl
    simp [concreteCentralBandIndex]

/-- Hence every central transition has the distinguished concrete band in
one of its two positions. -/
theorem centralLatitudePair_has_concreteCentralBand
    {N : ℕ} {j k : Fin (bandTailCount N + 1)}
    (hjk : CentralLatitudePair N j k) :
    j = concreteCentralBandIndex N ∨
      k = concreteCentralBandIndex N := by
  rcases hjk.2 with hj | hk
  · exact Or.inl
      ((isCentralLatitudeBand_iff_eq_concreteCentralBandIndex j).mp hj)
  · exact Or.inr
      ((isCentralLatitudeBand_iff_eq_concreteCentralBandIndex k).mp hk)

/-- The central transition has an unconditional concrete diameter bound. -/
theorem centralLatitudePair_block_bound_global
    {α : ℝ} (hα : 0 ≤ α) {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (_hjk : CentralLatitudePair N j k) :
    |bandPairError N j k (latitudeKernel α)| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) * (2 : ℝ) ^ α :=
  abs_latitudeKernel_bandPairError_le_global hα hN j k

/-- The same unconditional estimate, specialized to the smooth
opposite-hemisphere case. -/
theorem smoothOppositeLatitudePair_block_bound_global
    {α : ℝ} (hα : 0 ≤ α) {N : ℕ} (hN : 0 < N)
    (j k : Fin (bandTailCount N + 1))
    (_hjk : SmoothOppositeLatitudePair N j k) :
    |bandPairError N j k (latitudeKernel α)| ≤
      4 * (finiteBandPopulation N j : ℝ) *
        (finiteBandPopulation N k : ℝ) * (2 : ℝ) ^ α :=
  abs_latitudeKernel_bandPairError_le_global hα hN j k

/-- Every concrete band has enough width that four width factors absorb
`N⁴`.  The deliberately loose constant is useful for a premise-free
instantiation of the smooth-remainder interface. -/
theorem one_le_N_pow_four_mul_bandWidths
    {N : ℕ} (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1)) :
    (1 : ℝ) ≤ (N : ℝ) ^ 4 * bandWidth N j ^ 2 * bandWidth N k ^ 2 := by
  have hN : 0 < N := by
    have hs := four_mul_bandCount_sq_le N
    nlinarith
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hj := concrete_finiteBandPopulation_three_le hM j
  have hk := concrete_finiteBandPopulation_three_le hM k
  have hjR : (3 : ℝ) ≤ finiteBandPopulation N j := by exact_mod_cast hj
  have hkR : (3 : ℝ) ≤ finiteBandPopulation N k := by exact_mod_cast hk
  have heq :
      (N : ℝ) ^ 4 * bandWidth N j ^ 2 * bandWidth N k ^ 2 =
        16 * (finiteBandPopulation N j : ℝ) ^ 2 *
          (finiteBandPopulation N k : ℝ) ^ 2 := by
    rw [bandWidth_eq_population, bandWidth_eq_population]
    field_simp [hN0]
    ring
  rw [heq]
  nlinarith [sq_nonneg ((finiteBandPopulation N j : ℝ) - 3),
    sq_nonneg ((finiteBandPopulation N k : ℝ) - 3)]

/-- A premise-free, coarse affine-remainder package for all smooth
opposite-hemisphere blocks.  It uses `R = latitudeKernel` and zero affine
part.  The sharper analytic problem is therefore isolated to replacing the
factor `N⁴` by a uniform coefficient. -/
theorem hasSmoothOppositeAffineRemainders_global
    {α : ℝ} (hα : 0 < α) {N : ℕ} (hM : 3 ≤ bandCount N) :
    HasSmoothOppositeAffineRemainders α N
      ((2 : ℝ) ^ α * (N : ℝ) ^ 4) := by
  have hN : 0 < N := by
    have hs := four_mul_bandCount_sq_le N
    nlinarith
  intro j k _hjk
  refine ⟨latitudeKernel α, (fun _ ↦ 0), (fun _ ↦ 0), ?_, ?_, ?_⟩
  · intro s
    exact ((continuous_latitudeKernel hα).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · intro s t
    ring
  · intro s hs t ht
    have hsphere : s ∈ Icc (-1 : ℝ) 1 := by
      have hlo := bandBoundaryHeight_mem hN (j + 1)
      have hhi := bandBoundaryHeight_mem hN j
      exact ⟨hlo.1.trans hs.1, hs.2.trans hhi.2⟩
    have htsphere : t ∈ Icc (-1 : ℝ) 1 := by
      have hlo := bandBoundaryHeight_mem hN (k + 1)
      have hhi := bandBoundaryHeight_mem hN k
      exact ⟨hlo.1.trans ht.1, ht.2.trans hhi.2⟩
    have hkernel :=
      abs_latitudeKernel_le_global hα.le hsphere htsphere
    have hwidth := one_le_N_pow_four_mul_bandWidths hM j k
    have hpow : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
    calc
      |latitudeKernel α s t| ≤ (2 : ℝ) ^ α := hkernel
      _ ≤ (2 : ℝ) ^ α *
          ((N : ℝ) ^ 4 * bandWidth N j ^ 2 * bandWidth N k ^ 2) :=
        (le_mul_iff_one_le_right hpow).2 hwidth
      _ = ((2 : ℝ) ^ α * (N : ℝ) ^ 4) *
          bandWidth N j ^ 2 * bandWidth N k ^ 2 := by ring

/-- Fully concrete instantiation of the mixed-remainder theorem on smooth
opposite-hemisphere blocks. -/
theorem smoothOpposite_block_bound_via_mixedRemainder
    {α : ℝ} (hα : 0 < α) {N : ℕ} (hM : 3 ≤ bandCount N)
    (j k : Fin (bandTailCount N + 1))
    (hjk : SmoothOppositeLatitudePair N j k) :
    |bandPairError N j k (latitudeKernel α)| ≤
      64 * ((2 : ℝ) ^ α * (N : ℝ) ^ 4) *
        (finiteBandPopulation N j : ℝ) ^ 3 *
        (finiteBandPopulation N k : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
  have hN : 0 < N := by
    have hs := four_mul_bandCount_sq_le N
    nlinarith
  exact smoothOpposite_block_bound_of_affineRemainders hN
    (by positivity)
    (hasSmoothOppositeAffineRemainders_global hα hM) j k hjk

end BEMOC
