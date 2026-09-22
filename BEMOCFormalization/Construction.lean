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

end BEMOC.Definitive
