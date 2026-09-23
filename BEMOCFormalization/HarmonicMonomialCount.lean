import BEMOCFormalization.HarmonicBasis
import Mathlib.Data.Sym.Card

namespace BEMOC.Definitive

/-- Degree-`ℓ` monomials correspond to multisets of `ℓ` variables. -/
noncomputable def degreeMonomialsEquivSym (ℓ : ℕ) :
    degreeMonomials ℓ ≃ Sym (Fin 3) ℓ := by
  have h : degreeMonomials ℓ =
      {d : (Fin 3) →₀ ℕ | d.sum (fun _ => id) = ℓ} := by
    ext d
    rfl
  rw [h]
  exact (Sym.equivNatSum (Fin 3) ℓ).symm

/-- The exact three-variable homogeneous monomial count. -/
theorem degreeMonomials_card_choose (ℓ : ℕ) :
    Fintype.card (degreeMonomials ℓ) = Nat.choose (ℓ + 2) 2 := by
  classical
  rw [Fintype.card_congr (degreeMonomialsEquivSym ℓ), Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have harg : 3 + ℓ - 1 = ℓ + 2 := by omega
  rw [harg]
  rw [← Nat.choose_symm (by omega : ℓ ≤ ℓ + 2)]
  congr 1
  omega

/-- Dimension formula in the form used by the Fischer decomposition. -/
theorem degreeMonomials_card (ℓ : ℕ) :
    Fintype.card (degreeMonomials ℓ) = (ℓ + 1) * (ℓ + 2) / 2 := by
  rw [degreeMonomials_card_choose, Nat.choose_two_right]
  have h : ℓ + 2 - 1 = ℓ + 1 := by omega
  rw [h]
  ac_rfl

end BEMOC.Definitive
