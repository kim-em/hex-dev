/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerTheory.Groebner
public import Mathlib.Tactic.Abel

public section

/-! Algebraic identities behind chain pruning. A proper pointwise LCM divisor
is strictly smaller in the selected global monomial order. Monic S-polynomials
satisfy the exact chain identity with their actual LCM multipliers. -/

namespace HexGroebnerTheory
variable {σ : Type*} {K : Type*} [Field K] (m : MonomialOrder σ)

/-- A middle monomial dividing the pair LCM gives a smaller dependency whenever
its LCM with one endpoint is a proper divisor. Equality is explicitly excluded. -/
theorem lcm_lt (a b c : σ →₀ Nat) (hc : c ≤ a ⊔ b) (hne : a ⊔ c ≠ a ⊔ b) :
    m.toSyn (a ⊔ c) < m.toSyn (a ⊔ b) := by
  apply lt_of_le_of_ne (m.toSyn_monotone (sup_le le_sup_left hc))
  exact fun h => hne (m.toSyn.injective h)

/-- The exact S-polynomial chain identity. Its two dependency LCMs divide the
original LCM; proper-divisor hypotheses can subsequently supply strict bounds. -/
theorem spoly_chain (f g h : MvPolynomial σ K)
    (hf : m.Monic f) (hg : m.Monic g) (hh : m.Monic h)
    (middle : m.degree h ≤ m.degree f ⊔ m.degree g) :
    m.sPolynomial f g =
      MvPolynomial.monomial ((m.degree f ⊔ m.degree g) - (m.degree f ⊔ m.degree h)) 1 *
        m.sPolynomial f h +
      MvPolynomial.monomial ((m.degree f ⊔ m.degree g) - (m.degree h ⊔ m.degree g)) 1 *
        m.sPolynomial h g := by
  have left : m.degree f ⊔ m.degree h ≤ m.degree f ⊔ m.degree g :=
    sup_le le_sup_left middle
  have right : m.degree h ⊔ m.degree g ≤ m.degree f ⊔ m.degree g :=
    sup_le middle le_sup_right
  simp only [MonomialOrder.sPolynomial_def, hf.leadingCoeff_eq_one,
    hg.leadingCoeff_eq_one, hh.leadingCoeff_eq_one, mul_sub, ← mul_assoc,
    MvPolynomial.monomial_mul_monomial, one_mul,
    tsub_add_tsub_cancel left le_sup_left, tsub_add_tsub_cancel left le_sup_right,
    tsub_add_tsub_cancel right le_sup_left, tsub_add_tsub_cancel right le_sup_right]
  abel

end HexGroebnerTheory
