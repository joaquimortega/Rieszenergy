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
