/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerTheory.Groebner

public section

/-! Uniqueness of reduced Gröbner bases, including the empty basis of the zero
ideal. Reducedness excludes zero polynomials and permits a term to be divisible
by a basis leading monomial only at its own monic leading term. -/

namespace HexGroebnerTheory
variable {σ : Type*} {K : Type*} [Field K] (m : MonomialOrder σ)

/-- A reduced basis is monic and nonzero; its tails and all other leading terms
are irreducible by the basis. The exponent comparison is pointwise divisibility. -/
@[expose] def IsReduced (G : Set (MvPolynomial σ K)) : Prop :=
  ∀ g ∈ G, g ≠ 0 ∧ m.leadingCoeff g = 1 ∧
    ∀ c ∈ g.support, ∀ h ∈ G, m.degree h ≤ c → h = g ∧ c = m.degree g

private theorem reduced_member {G H : Set (MvPolynomial σ K)} {I : Ideal (MvPolynomial σ K)}
    (hG : IsGroebnerBasis m G I) (hH : IsGroebnerBasis m H I)
    (rG : IsReduced m G) (rH : IsReduced m H) {g : MvPolynomial σ K} (hg : g ∈ G) :
    g ∈ H := by
  classical
  have rg := rG g hg
  obtain ⟨h, hh, hn, hle⟩ := hH.2 g (hG.1 hg) rg.1
  obtain ⟨g', hg', gn, gle⟩ := hG.2 h (hH.1 hh) hn
  have same := rg.2.2 (m.degree g) (m.degree_mem_support rg.1) g' hg' (gle.trans hle)
  have eqg : g' = g := same.1
  subst g'
  have degrees : m.degree g = m.degree h := le_antisymm gle hle
  have rh := rH h hh
  have lead_zero : (g - h).coeff (m.degree g) = 0 := by
    have gc := rg.2.1
    have hc := rh.2.1
    change g.coeff (m.degree g) = 1 at gc
    change h.coeff (m.degree h) = 1 at hc
    rw [← degrees] at hc
    rw [MvPolynomial.coeff_sub, gc, hc, sub_self]
  have equal : g = h := by
    apply sub_eq_zero.mp
    by_contra nonzero
    have member : g - h ∈ I := Ideal.sub_mem I (hG.1 hg) (hH.1 hh)
    obtain ⟨b, hb, bn, ble⟩ := hG.2 (g - h) member nonzero
    have term := m.degree_mem_support nonzero
    have term_bound : m.degree (g - h) = m.degree g := by
      have in_union := term
      apply MvPolynomial.support_sub at in_union
      rcases Finset.mem_union.mp in_union with term_g | term_h
      · exact (rg.2.2 _ term_g b hb ble).2
      · obtain ⟨a, ha, an, ale⟩ := hH.2 b (hG.1 hb) bn
        exact (rh.2.2 _ term_h a ha (ale.trans ble)).2.trans degrees.symm
    have coefficient := MvPolynomial.mem_support_iff.mp term
    rw [term_bound, lead_zero] at coefficient
    exact coefficient rfl
  simpa only [equal] using hh

/-- Any two reduced Gröbner bases of the same ideal are equal as sets. Sorting
and fixed coefficient representatives then determine the canonical array output. -/
theorem reduced_unique {G H : Set (MvPolynomial σ K)} {I : Ideal (MvPolynomial σ K)}
    (hG : IsGroebnerBasis m G I) (hH : IsGroebnerBasis m H I)
    (rG : IsReduced m G) (rH : IsReduced m H) : G = H := by
  apply Set.Subset.antisymm
  · exact fun _ hg => reduced_member m hG hH rG rH hg
  · exact fun _ hh => reduced_member m hH hG rH rG hh

end HexGroebnerTheory
