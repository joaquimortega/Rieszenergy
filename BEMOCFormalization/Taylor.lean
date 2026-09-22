import BEMOCFormalization.BandErrors

namespace BEMOC.Definitive

/-- Two derivatives in each height variable, in a fixed order. -/
noncomputable def mixedFourth (G : ℝ × ℝ → ℝ) (s t : ℝ) : ℝ :=
  iteratedDeriv 2 (fun u => iteratedDeriv 2 (fun v => G (u, v)) t) s

/-- The two-moment estimate for a C⁴ extension around a closed rectangle. -/
def MixedTaylorBound : Prop :=
  ∀ N : ℕ, 4 ≤ N → ∀ j k : RingIndex N,
    ∀ G : ℝ × ℝ → ℝ, ∀ W : Set (ℝ × ℝ), IsOpen W →
      (band N (j.val + 1) ×ˢ band N (k.val + 1)) ⊆ W →
      ContDiffOn ℝ 4 G W → ∀ L : ℝ, 0 ≤ L →
      (∀ p ∈ band N (j.val + 1) ×ˢ band N (k.val + 1),
        |mixedFourth G p.1 p.2| ≤ L) →
      |bandBlock N (j.val + 1) (k.val + 1) G| ≤
        (population N (j.val + 1) : ℝ) ^ 3 *
          (population N (k.val + 1) : ℝ) ^ 3 / (bandParameter N : ℝ) ^ 8 * L

end BEMOC.Definitive
