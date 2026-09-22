import BEMOCFormalization.KernelDerivatives

namespace BEMOC.Definitive

/-- Symmetric scale-comparability predicate, using real rather than truncated division. -/
def Comparable (N j k : ℕ) : Prop :=
  (population N j : ℝ) / 8 ≤ population N k ∧
    (population N k : ℝ) ≤ 8 * population N j

/-- The full comparable estimate, including equal, adjacent, polar, and opposite bands. -/
def ComparableBlockBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1024 ≤ N → ∀ j k : RingIndex N,
    Comparable N (j.val + 1) (k.val + 1) →
    |kernelBlock α N (j.val + 1) (k.val + 1)| ≤
      C * population N (j.val + 1) / (bandParameter N : ℝ) ^ α *
        (1 + |(j.val : ℝ) - k.val|) ^ (α - 3)

end BEMOC.Definitive
