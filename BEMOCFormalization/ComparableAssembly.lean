import BEMOCFormalization.ComparableEndpointAssembly
import BEMOCFormalization.ComparableIntermediateClosure
import BEMOCFormalization.ComparableNearTailClosure

namespace BEMOC.Definitive

/-- All comparable regimes reduce to the near smooth-tail estimate. The
endpoint, intermediate, and far estimates here are unconditional. -/
theorem comparable_block_bound_of_near_tail {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2)
    (htail : NearTailDerivativeBound α) : ComparableBlockBound α := by
  obtain ⟨Ce, hCe, he⟩ := comparable_endpoint_block_bound hα0 hα2
  obtain ⟨Cn, hCn, hn⟩ := near_comparable_block_bound_of_tail hα0 hα2 htail
  obtain ⟨Ci, hCi, hi⟩ := intermediate_comparable_block_bound hα0 hα2
  obtain ⟨Cf, hCf, hf⟩ := far_comparable_block_bound hα0 hα2
  let C := Ce + Cn + Ci + Cf
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN j k hcomp
  let Q : ℝ := (population N (j.val + 1) : ℝ) /
    (bandParameter N : ℝ) ^ α *
      (1 + |(j.val : ℝ) - k.val|) ^ (α - 3)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hmajor (c : ℝ) (hc : c ≤ C)
      (h : |kernelBlock α N (j.val + 1) (k.val + 1)| ≤ c * Q) :
      |kernelBlock α N (j.val + 1) (k.val + 1)| ≤ C * Q :=
    h.trans (mul_le_mul_of_nonneg_right hc hQ)
  have hCeC : Ce ≤ C := by dsimp [C]; linarith
  have hCnC : Cn ≤ C := by dsimp [C]; linarith
  have hCiC : Ci ≤ C := by dsimp [C]; linarith
  have hCfC : Cf ≤ C := by dsimp [C]; linarith
  have hresult : |kernelBlock α N (j.val + 1) (k.val + 1)| ≤ C * Q := by
    by_cases hend : j.val + 1 = 1 ∨
        j.val + 1 = 2 * bandParameter N - 1 ∨
        k.val + 1 = 1 ∨
        k.val + 1 = 2 * bandParameter N - 1
    · have h := he N hN j k hcomp hend
      apply hmajor Ce hCeC
      convert h using 1 <;> dsimp [Q] <;> ring
    · have hjfirst : j.val + 1 ≠ 1 := by omega
      have hjlast : j.val + 1 ≠ 2 * bandParameter N - 1 := by omega
      have hkfirst : k.val + 1 ≠ 1 := by omega
      have hklast : k.val + 1 ≠ 2 * bandParameter N - 1 := by omega
      have hjzero : j.val ≠ 0 := by omega
      have hkzero : k.val ≠ 0 := by omega
      by_cases hnear : |(j.val : ℤ) - k.val| ≤ 1
      · have hnearR : |(j.val : ℝ) - k.val| ≤ 2 := by
          have h : |(j.val : ℝ) - k.val| ≤ 1 := by exact_mod_cast hnear
          linarith
        have h := hn N hN j k hjfirst hjlast hkfirst hklast hcomp hnearR
        apply hmajor Cn hCnC
        convert h using 1 <;> dsimp [Q] <;> ring
      · have hgap : 2 ≤ |(j.val : ℤ) - k.val| := by omega
        by_cases hmid : |(j.val : ℝ) - k.val| ≤
            2 * population N (j.val + 1)
        · have h := hi N hN j k hjzero hjlast hkzero hklast
            hcomp hgap hmid
          apply hmajor Ci hCiC
          convert h using 1 <;> dsimp [Q] <;> ring
        · have hfar : 2 * (population N (j.val + 1) : ℝ) <
            |(j.val : ℝ) - k.val| := lt_of_not_ge hmid
          have h := hf N hN j k hjzero hjlast hkzero hklast
            hcomp hgap hfar
          apply hmajor Cf hCfC
          convert h using 1 <;> dsimp [Q] <;> ring
  convert hresult using 1 <;> dsimp [Q] <;> ring

/-- The full comparable-block estimate for every `0 < α < 2`, including
polar endpoints, equal and adjacent bands, intermediate gaps, and far bands. -/
theorem comparable_block_bound {α : ℝ}
    (hα0 : 0 < α) (hα2 : α < 2) : ComparableBlockBound α :=
  comparable_block_bound_of_near_tail hα0 hα2
    (near_tail_derivative_bound hα0 hα2)

end BEMOC.Definitive
