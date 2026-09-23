# ComparableIntermediateIntegrability proof guide

`intervalIntegrable_latitudeProfile_mixedFourth` specializes the generic compact-slice C⁴ integrability theorem from `NearTailIntegralCalculus` to the actual latitude profile on the positive-chord domain. The canonical generic lemma remains in `NearTailIntegralCalculus`; this module exports the useful profile-level API.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.NearTailIntegralCalculus

open Set MeasureTheory
namespace BEMOC.Definitive

/-- The actual latitude profile has an integrable mixed fourth derivative on
any compact angular slice contained in its smooth positive-chord domain. -/
theorem intervalIntegrable_latitudeProfile_mixedFourth (α : ℝ)
    {a b : ℝ} (hab : a ≤ b) {p : ℝ × ℝ}
    (hp : p ∈ integralParameterDomain nearTailSmoothDomain a b) :
    IntervalIntegrable
      (fun θ => mixedFourth (fun q : ℝ × ℝ =>
        latitudeProfile α q.1 q.2 θ) p.1 p.2) volume a b :=
  intervalIntegrable_mixedFourth_slice isOpen_nearTailSmoothDomain
    (latitudeProfile_joint_contDiffOn α) hab hp

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
