# Core proof guide

Source anchors: `definitive.tex` Theorem `thm:main` and `theo:ineq` (around lines 118–126), the sphere integration formula `eq:integralaintervalo` (around 380), the parallel kernel `eq:Falpha` (around 390), and the angular proof near lines 466–520. This module supplies the geometric and energy vocabulary. It deliberately has no construction-specific populations. The old `legacy/BEMOCFormalization/Core.lean` is a possible source of generic geometric lemmas, but no Simpson-rule definition should be imported implicitly.

`Ambient` is three-dimensional Euclidean space and `Sphere` is the metric unit sphere. `parallelVector z θ` is the usual latitude parametrization `(sqrt(1−z²) cos θ, sqrt(1−z²) sin θ, z)`. The implemented proof `parallelVector_mem_sphere` needs `z∈[-1,1]`; it uses `1−z²≥0`, the trigonometric Pythagorean identity, and norm expansion. Its reusable consequences should include the third-coordinate equation, a distance formula for two parallel points, continuity in angle and height on the valid domain, and positivity of the radius on `(-1,1)`. The distance formula should read `dist² = 2−2st−2 sqrt(1−s²)sqrt(1−t²) cos(θ−ψ)`. The downstream `Longitude` and angular-geometry proofs establish this chordal identity before using the averaged kernel. A `Sphere` subtype point carries the membership proof; `parallelPoint` is therefore convenient for the later dependent vertex type.

`sigma` is written as a normalization of mathlib's `volume.toSphere`. A definition alone does not show that this is the manuscript's normalized surface area. The proof route is to establish the total mass of `volume.toSphere` in dimension three, prove the normalizing scalar is finite and nonzero, then show the height-angle formula in `ContinuousEnergy`. If the library's `toSphere` API does not directly expose the desired disintegration, replace or bridge this definition by the pushforward of the rectangle measure under `parallelPoint`; the equivalence must be proved, not assumed. The height variable has density `dt/2`, and the angle has density `dθ/(2π)`. Check the orientation of the oriented interval integrals from `0` to `2π` and `-1` to `1`.

`continuousEnergy α` is the exact scalar `2^(α+1)/(α+2)`. It is a *definition*; `SurfaceMeasure.constantPotential_of_pos` proves the associated integral identity. Under `0<α<2`, the denominator is positive. For the first-variable potential, rotate a fixed point to the north pole, where the kernel is `(2−2t)^(α/2)`. Integrate against `dt/2`; substitution `u=2−2t` gives the stated constant. `continuousEnergy_one` is its numerical specialization, while `constantPotential_of_pos` supplies the integral formula.

`energy X α` is the full ordered sum over all labels including equal labels. This matches the paper's `Σ_{x,y∈P_N}` once the construction proves that the labelled point map is injective. For `0<α`, `dist x x ^ α=0`, and no factor of `1/2` is introduced. Two conveniences are worth proving here: invariance under a bijection of finite labels and a uniform finite-energy estimate using `dist x y≤2`. The latter will close small `N` uniformly in phases. Keep hypotheses on the exponent explicit: at `α=0`, the behavior of zero powers changes, and the theorem does not cover that endpoint.

`latitudeKernel` is an angular average. For `s,t∈[-1,1]`, let `A=2−2st` and `B=2sqrt(1−s²)sqrt(1−t²)`; Cauchy–Schwarz on the two unit meridional vectors gives `A≥B≥0`. The integrand is consequently a nonnegative base to a real power, including the singular case `A=B` at angle zero. Show kernel symmetry by swapping heights and periodic angular integration. Prove that it equals the double energy of uniform measures on the corresponding parallels; rotation invariance collapses the two-angle integral to the one-angle formula. Later modules require this identity for `ringEnergy`, the latitude height reduction, and longitude trapezoid comparison. The kernel may fail to be globally `C⁴` on the diagonal, so this module should not export an unrestricted smoothness claim.

`scale α N = N^(1−α/2)` is positive for `N≥4` and `0<α<2`; the assembly currently needs only nonnegativity. Prove `N≍M²` conversions in Construction or Geometry, then expose the useful inequalities between `M^(2−α)` and `scale α N`. Track that constants are allowed to depend on `α` but not on `N` or phases.

This foundational module proves `parallelVector_mem_sphere` and `continuousEnergy_one`. The geometric measure interpretation, chordal identity, kernel average, and energy integral are established in `SurfaceMeasure`, `AngularGeometry`, `LatitudePotential`, and `EnergyDecomposition`, rather than by this vocabulary module alone.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import Mathlib

/-! Basic geometric objects. Targets in later modules are propositions, not proofs. -/
open scoped BigOperators
open MeasureTheory
namespace BEMOC
namespace Definitive

/-- Euclidean ambient space; chordal distance is inherited from this space. -/
abbrev Ambient := EuclideanSpace ℝ (Fin 3)
/-- The unit sphere. -/
abbrev Sphere := Metric.sphere (0 : Ambient) 1

/-- Latitude parametrization, before enforcing the height domain. -/
noncomputable def parallelVector (z θ : ℝ) : Ambient :=
  !₂[Real.sqrt (1 - z ^ 2) * Real.cos θ,
     Real.sqrt (1 - z ^ 2) * Real.sin θ, z]

/-- Reused geometric argument from the previous Core, independent of its construction. -/
theorem parallelVector_mem_sphere {z θ : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    parallelVector z θ ∈ Metric.sphere (0 : Ambient) 1 := by
  rw [EuclideanSpace.sphere_zero_eq 1 (by positivity)]
  have hrad : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  simp [parallelVector, Fin.sum_univ_succ, Real.sq_sqrt hrad]
  ring_nf
  rw [Real.sq_sqrt hrad]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The exact point on a parallel, with its height condition explicit. -/
noncomputable def parallelPoint (z θ : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) : Sphere :=
  ⟨parallelVector z θ, parallelVector_mem_sphere hz⟩

/-- Normalized geometric surface measure, using mathlib's polar measure. -/
noncomputable def sigma : Measure Sphere :=
  (volume.toSphere (E := Ambient) Set.univ)⁻¹ • volume.toSphere

/-- The manuscript's continuous energy constant. -/
noncomputable def continuousEnergy (α : ℝ) : ℝ := 2 ^ (α + 1) / (α + 2)

/-- Ordered-pair energy including the diagonal, which vanishes for `0 < α`. -/
noncomputable def energy {ι : Type*} [Fintype ι] (X : ι → Sphere) (α : ℝ) : ℝ :=
  ∑ i, ∑ j, dist (X i) (X j) ^ α

/-- The target second-order scale. -/
noncomputable def scale (α : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (1 - α / 2)

/-- Average kernel for two uniform parallels; meaningful on `[-1,1]²`. -/
noncomputable def latitudeKernel (α s t : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
    (2 - 2 * s * t - 2 * Real.sqrt (1 - s ^ 2) *
      Real.sqrt (1 - t ^ 2) * Real.cos θ) ^ (α / 2)

/-- Algebraic specialization used by the discrepancy corollary. -/
theorem continuousEnergy_one : continuousEnergy 1 = 4 / 3 := by
  norm_num [continuousEnergy]

end Definitive
end BEMOC
```

<!-- END_LEAN_STATEMENTS -->
