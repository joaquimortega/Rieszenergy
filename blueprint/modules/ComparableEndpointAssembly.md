# Comparable endpoint assembly

The four polar corner estimates are combined into one bound for every comparable block with an endpoint index. The classification uses the explicit endpoint population and gives the first or last eight bands. The proof preserves the ordered first population and the exact power of the real label gap.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.ComparableSeparatedBlocks

namespace BEMOC.Definitive

/-- One uniform comparable bound for all endpoint blocks. -/
theorem comparable_endpoint_block_bound {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
      Comparable N (j.val + 1) (k.val + 1) →
      (j.val + 1 = 1 ∨ j.val + 1 = 2 * bandParameter N - 1 ∨
        k.val + 1 = 1 ∨ k.val + 1 = 2 * bandParameter N - 1) →
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
        C * population N (j.val + 1) / (bandParameter N : ℝ) ^ α *
          (1 + |(j.val : ℝ) - k.val|) ^ (α - 3) := by
  obtain ⟨Co, hCo, hOpp⟩ := opposite_small_bands_comparable_bound hα0 hα2
  obtain ⟨Cr, hCr, hRev⟩ := reverse_opposite_small_bands_comparable_bound hα0 hα2
  let Cn : ℝ := 65536 * (24 : ℝ) ^ α
  let C := Cn + Co + Cr
  have hCn : 0 ≤ Cn := by dsimp [Cn]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N hN j k hcomp hend
  let M := bandParameter N
  have hM : 16 ≤ M := bandParameter_ge_sixteen_of_ge_1024 hN
  have hj1 : 1 ≤ j.val + 1 := by omega
  have hj2 : j.val + 1 < 2 * M := by
    have := j.isLt
    omega
  have hk1 : 1 ≤ k.val + 1 := by omega
  have hk2 : k.val + 1 < 2 * M := by
    have := k.isLt
    omega
  obtain ⟨hj, hk⟩ := comparable_endpoint_indices_polar hN hj1 hj2 hk1 hk2 hcomp hend
  let Q : ℝ := (population N (j.val + 1) : ℝ) / (M : ℝ) ^ α *
    (1 + |(j.val : ℝ) - k.val|) ^ (α - 3)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hmajor (c : ℝ) (hc : c ≤ C)
      (h : |kernelBlock α N (j.val + 1) (k.val + 1)| ≤ c * Q) :
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤ C * Q :=
    h.trans (mul_le_mul_of_nonneg_right hc hQ)
  have hCnC : Cn ≤ C := by dsimp [C]; linarith
  have hCoC : Co ≤ C := by dsimp [C]; linarith
  have hCrC : Cr ≤ C := by dsimp [C]; linarith
  have hresult : |kernelBlock α N (j.val + 1) (k.val + 1)| ≤ C * Q := by
    rcases hj with hjnorth | hjsouth <;> rcases hk with hknorth | hksouth
    · have h := north_small_bands_comparable_bound hN hj1 hjnorth hk1 hknorth hα0 hα2
      have habs : |((j.val + 1 : ℕ) : ℝ) - ((k.val + 1 : ℕ) : ℝ)| =
          |(j.val : ℝ) - k.val| := by
        congr 1
        push_cast
        ring
      rw [habs] at h
      have h' : |kernelBlock α N (j.val + 1) (k.val + 1)| ≤ Cn * Q := by
        convert h using 1 <;> dsimp [Cn, Q, M] <;> ring
      exact hmajor Cn hCnC h'
    · have h := hOpp N hN j k hjnorth hksouth
      apply hmajor Co hCoC
      convert h using 1 <;> dsimp [Q, M] <;> ring
    · have h := hRev N hN j k hjsouth hknorth hcomp
      apply hmajor Cr hCrC
      convert h using 1 <;> dsimp [Q, M] <;> ring
    · let qj := 2 * M - (j.val + 1)
      let qk := 2 * M - (k.val + 1)
      have hqj1 : 1 ≤ qj := by dsimp [qj]; omega
      have hqk1 : 1 ≤ qk := by dsimp [qk]; omega
      have hqj : 2 * M - qj = j.val + 1 := by dsimp [qj]; omega
      have hqk : 2 * M - qk = k.val + 1 := by dsimp [qk]; omega
      have h := south_small_bands_comparable_bound hN hqj1 hjsouth hqk1 hksouth hα0 hα2
      rw [hqj, hqk] at h
      have habs : |((j.val + 1 : ℕ) : ℝ) - ((k.val + 1 : ℕ) : ℝ)| =
          |(j.val : ℝ) - k.val| := by
        congr 1
        push_cast
        ring
      rw [habs] at h
      have h' : |kernelBlock α N (j.val + 1) (k.val + 1)| ≤ Cn * Q := by
        convert h using 1 <;> dsimp [Cn, Q, M] <;> ring
      exact hmajor Cn hCnC h'
  convert hresult using 1 <;> dsimp [Q, C, M] <;> ring

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
