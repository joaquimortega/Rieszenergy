import BEMOCFormalization.KernelDerivatives

namespace BEMOC.Definitive

/-- Strictly on the same side; the central index is excluded. -/
def SameSide (N j k : ℕ) : Prop :=
  (j < bandParameter N ∧ k < bandParameter N) ∨
    (bandParameter N < j ∧ bandParameter N < k)

/-- Unequal scales in one hemisphere, oriented with k the larger population. -/
def SameSideBlockBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
    8 * population N (j.val + 1) < population N (k.val + 1) →
    SameSide N (j.val + 1) (k.val + 1) →
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
      C * (population N (j.val + 1) : ℝ) ^ 3 /
        ((bandParameter N : ℝ) ^ α * (population N (k.val + 1) : ℝ) ^ (5 - α))

/-- Unequal opposite/central blocks; the central band belongs in this regime. -/
def OppositeBlockBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
    8 * population N (j.val + 1) < population N (k.val + 1) →
    ¬SameSide N (j.val + 1) (k.val + 1) →
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
      C * (population N (j.val + 1) : ℝ) ^ 3 *
        (population N (k.val + 1) : ℝ) ^ 3 / (bandParameter N : ℝ) ^ 8

end BEMOC.Definitive
