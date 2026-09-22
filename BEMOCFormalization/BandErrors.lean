import BEMOCFormalization.Geometry
import BEMOCFormalization.EnergyDecomposition

open scoped BigOperators
namespace BEMOC.Definitive

/-- Integration against λ_j−ν_j, implemented as a difference of ordinary integrals. -/
noncomputable def bandError (N j : ℕ) (f : ℝ → ℝ) : ℝ :=
  (N : ℝ) / 2 * (∫ t in boundary N j..boundary N (j - 1), f t) -
    (population N j : ℝ) * f (height N j)

/-- Ordered tensor of the two band error functionals: j acts on s, k on t. -/
noncomputable def bandBlock (N j k : ℕ) (G : ℝ × ℝ → ℝ) : ℝ :=
  bandError N j (fun s => bandError N k (fun t => G (s, t)))
/-- The actual latitude kernel block. -/
noncomputable def kernelBlock (α : ℝ) (N j k : ℕ) : ℝ :=
  bandBlock N j k (fun p => latitudeKernel α p.1 p.2)

/-- Exact two-moment cancellation, derived from the midpoint and mass formulas. -/
def BandMoments : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ j : RingIndex N,
    bandError N (j.val + 1) (fun _ => 1) = 0 ∧
    bandError N (j.val + 1) id = 0

/-- Corrected variable binding for eq:latitude-decomposition. -/
def LatitudeIdentity (α : ℝ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → latitudeError α N =
    -∑ j : RingIndex N, ∑ k : RingIndex N, kernelBlock α N (j.val + 1) (k.val + 1)

/-- Exchange symmetry used when orienting unequal-scale ordered pairs. -/
def BlockSymmetry (α : ℝ) : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ j k : RingIndex N,
    kernelBlock α N (j.val + 1) (k.val + 1) =
      kernelBlock α N (k.val + 1) (j.val + 1)

end BEMOC.Definitive
