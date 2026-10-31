/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerTheory.Upstream.Groebner
public import HexGroebnerTheory.Order

public section

/-! Gröbner bases stated by leading-monomial divisibility. The correspondence
with the upstream leading-term-ideal predicate supplies Buchberger's criterion
and unique remainders without changing the executable dependency graph. -/

namespace HexGroebnerTheory
variable {σ : Type*} {K : Type*} [Field K] (m : MonomialOrder σ)

/-- A Gröbner basis lies in its ideal and divides the leading monomial of every
nonzero ideal member. The exponent comparison is pointwise divisibility. -/
@[expose] def IsGroebnerBasis (G : Set (MvPolynomial σ K)) (I : Ideal (MvPolynomial σ K)) : Prop :=
  G ⊆ I ∧ ∀ f ∈ I, f ≠ 0 → ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree f

/-- The divisibility predicate agrees with the upstream leading-term-ideal definition. -/
theorem groebner_iff (G : Set (MvPolynomial σ K)) (I : Ideal (MvPolynomial σ K)) :
    IsGroebnerBasis m G I ↔ m.IsGroebnerBasis G I := by
  classical
  have units : ∀ g ∈ G \ {0}, IsUnit (m.leadingCoeff g) := by
    intro g hg
    exact isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr hg.2)
  have equivalence := MonomialOrder.IsGroebnerBasis.isGroebnerBasis_iff_subset_and_degree_le_eq_and_degree_le
    (m := m) (G := G \ {0}) I units
  rw [MonomialOrder.IsGroebnerBasis.isGroebnerBasis_sdiff_singleton_zero] at equivalence
  constructor
  · intro h
    apply equivalence.mpr
    refine ⟨fun g hg => h.1 hg.1, ?_⟩
    intro f hf hf0
    obtain ⟨g, hg, hg0, hd⟩ := h.2 f hf hf0
    exact ⟨g, ⟨hg, hg0⟩, hd⟩
  · intro h
    have hd := equivalence.mp h
    refine ⟨h.1, ?_⟩
    intro f hf hf0
    obtain ⟨g, hg, hdeg⟩ := hd.2 f hf hf0
    exact ⟨g, hg.1, hg.2, hdeg⟩

/-- Buchberger's criterion requires bounded division representations of all
S-polynomials. Arbitrary ideal-membership identities do not suffice. -/
theorem buchberger_iff (G : Set (MvPolynomial σ K)) :
    IsGroebnerBasis m G (Ideal.span G) ↔
      ∀ g₁ g₂ : G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0 := by
  rw [groebner_iff]
  exact MonomialOrder.IsGroebnerBasis.isGroebnerBasis_iff_isRemainder_sPolynomial_zero G

/-- Every polynomial has a unique irreducible remainder modulo a Gröbner basis. -/
theorem remainder_unique {G : Set (MvPolynomial σ K)} {I : Ideal (MvPolynomial σ K)}
    (h : IsGroebnerBasis m G I) (f : MvPolynomial σ K) :
    ∃! r, m.IsRemainder f G r := by
  apply MonomialOrder.IsGroebnerBasis.existsUnique_isRemainder₀ ((groebner_iff m G I).mp h) _ f
  intro g hg
  by_cases hz : g = 0
  · exact Or.inr hz
  · exact Or.inl (isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr hz))

end HexGroebnerTheory
