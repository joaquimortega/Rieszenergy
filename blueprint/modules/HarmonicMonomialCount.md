# Harmonic monomial count

`BEMOCFormalization/HarmonicMonomialCount.lean` proves the exact dimension of the homogeneous polynomial space in three variables by counting monomials. It imports `HarmonicBasis.lean`, whose `degreeMonomials ℓ` is the set of finitely supported exponent vectors `d : Fin 3 →₀ ℕ` with total degree `d.degree = ℓ`, and Mathlib's `Data.Sym.Card`. The count is independent of harmonicity or the Laplacian; it supplies the ambient homogeneous dimension used by the Fischer decomposition in the harmonic-basis argument.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
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
```

<!-- END_LEAN_STATEMENTS -->

The first declaration, `degreeMonomialsEquivSym`, is an equivalence between `degreeMonomials ℓ` and `Sym (Fin 3) ℓ`, the type of multisets of exactly `ℓ` variables selected from three variables. Mathlib already has `Sym.equivNatSum`, which sends a multiset to its multiplicity vector in `Fin 3 →₀ ℕ`. The proof checks that the defining condition `d.degree = ℓ` is definitionally the same as `d.sum (fun _ => id) = ℓ`, then takes the inverse of `Sym.equivNatSum`. This is an actual bijection of the full exponent-vector type, not an inequality or an assumed finite-dimensionality theorem.

The second declaration, `degreeMonomials_card_choose`, transports cardinality across that equivalence with `Fintype.card_congr`. Mathlib's `Sym.card_sym_eq_choose` is the stars-and-bars count for the symmetric power. With `Fintype.card (Fin 3) = 3`, it yields `Nat.choose (3 + ℓ - 1) ℓ`. Ordinary arithmetic identifies the top index with `ℓ+2`, and `Nat.choose_symm` changes the bottom index from `ℓ` to `2`. The resulting exact statement is

\[
 \#\{d : \mathrm{Fin}(3)\to_0\mathbb N : \deg(d)=\ell\}=\binom{\ell+2}{2}.
\]

The last declaration, `degreeMonomials_card`, applies `Nat.choose_two_right` and commutativity of multiplication to express the same count as `(ℓ+1)*(ℓ+2)/2`. This is the form intended for `finrank_homogeneous_eq_degreeMonomials_card` in `HarmonicBasis.lean`. In a Fischer decomposition, subtracting the dimension of the degree-`ℓ-2` homogeneous polynomials from this number gives `2ℓ+1`; the subtraction and the Laplacian surjectivity belong in the consuming module, not here.

The module has no new axioms, opaque definitions, or placeholders. `lake build BEMOCFormalization.HarmonicMonomialCount` checks its declarations. Its direct dependencies are `HarmonicBasis.lean` for the repository definition and finite subtype instance, `Mathlib.Data.Finsupp.Multiset` through `Sym.equivNatSum`, and `Mathlib.Data.Sym.Card` for the symmetric-power cardinality formula.
