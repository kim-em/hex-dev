/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerTheory.CertificateOrder
public import HexGroebnerTheory.Certificate

public section

namespace HexGroebnerTheory.Certificate
open scoped HexMvPolyTheory HexModArithTheory.ZMod64
open Hex.Groebner.Certificate

/-- A maximum scan always returns one of its supplied terms. -/
theorem leadingAux_mem (order : Hex.Groebner.TermOrder) (best : List Nat × Nat)
    (terms : Polynomial) : leadingAux order best terms ∈ best :: terms := by
  induction terms generalizing best with
  | nil => simp [leadingAux]
  | cons t terms ih =>
    simp only [leadingAux]
    split
    · have h := ih t
      simp only [List.mem_cons] at h ⊢
      exact Or.inr h
    · have h := ih best
      simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- A nonzero reported leading term is a stored term. -/
theorem leading_mem {order : Hex.Groebner.TermOrder} {terms : Polynomial}
    {term : List Nat × Nat} (h : leading order terms = some term) : term ∈ terms := by
  cases terms with
  | nil => simp [leading] at h
  | cons first rest =>
    simp only [leading, Option.some.injEq] at h
    subst term
    exact leadingAux_mem order first rest

private def key (order : Hex.Groebner.TermOrder) (n : Nat) (term : List Nat × Nat) :
    HexGroebnerTheory.OrderSyn (order.cmp n) := Hex.MvPoly.Kernel.mono n term.1

private theorem compare_key (order : Hex.Groebner.TermOrder) {n : Nat}
    (a b : List Nat × Nat) (ha : a.1.length = n) (hb : b.1.length = n) :
    (compare order a.1 b.1).isLE ↔ key order n a ≤ key order n b := by
  rw [← Std.isLE_compare]
  change (compare order a.1 b.1).isLE ↔
    (order.cmp n (Hex.MvPoly.Kernel.mono n a.1) (Hex.MvPoly.Kernel.mono n b.1)).isLE
  have h := compare_eq order (Hex.MvPoly.Kernel.mono n a.1) (Hex.MvPoly.Kernel.mono n b.1)
  have h' : compare order a.1 b.1 =
      order.cmp n (Hex.MvPoly.Kernel.mono n a.1) (Hex.MvPoly.Kernel.mono n b.1) := by
    simpa only [Hex.MvPoly.Kernel.toList_mono ha, Hex.MvPoly.Kernel.toList_mono hb] using h
  rw [h']

private theorem leadingAux_max (order : Hex.Groebner.TermOrder) {n : Nat}
    (best : List Nat × Nat) (terms : Polynomial)
    (lengths : ∀ t ∈ best :: terms, t.1.length = n) :
    ∀ t ∈ best :: terms, key order n t ≤ key order n (leadingAux order best terms) := by
  induction terms generalizing best with
  | nil =>
    intro t ht
    have h : t = best := by simpa using ht
    subst t
    exact le_rfl
  | cons a terms ih =>
    have hb := lengths best (by simp)
    have ha := lengths a (by simp)
    simp only [leadingAux]
    split
    · rename_i hgt
      have hnot : ¬ key order n a ≤ key order n best := by
        intro h
        have hle := (compare_key order a best ha hb).mpr h
        have hc : compare order a.1 best.1 = .gt := by simpa using hgt
        simp [hc] at hle
      have hba : key order n best ≤ key order n a := le_of_lt (lt_of_not_ge hnot)
      have bound := ih a (fun t ht => lengths t (List.mem_cons_of_mem best ht))
      intro t ht
      rcases List.mem_cons.mp ht with h | ht
      · subst t
        exact hba.trans (bound a (by simp))
      · exact bound t ht
    · rename_i hnot
      have hab : key order n a ≤ key order n best := by
        apply (compare_key order a best ha hb).mp
        cases hc : compare order a.1 best.1 <;> simp_all
      have bound := ih best (fun t ht => by
        rcases List.mem_cons.mp ht with h | ht
        · subst t; exact hb
        · exact lengths t (by simp [ht]))
      intro t ht
      rcases List.mem_cons.mp ht with h | ht
      · subst t; exact bound best (by simp)
      · rcases List.mem_cons.mp ht with h | ht
        · subst t; exact hab.trans (bound best (by simp))
        · exact bound t (List.mem_cons_of_mem best ht)

/-- Every stored term is at most the reported leading term in the chosen order. -/
theorem leading_max {order : Hex.Groebner.TermOrder} {n : Nat} {terms : Polynomial}
    {term : List Nat × Nat} (lengths : ∀ t ∈ terms, t.1.length = n)
    (h : leading order terms = some term) :
    ∀ t ∈ terms, (compare order t.1 term.1).isLE := by
  cases terms with
  | nil => simp [leading] at h
  | cons first rest =>
    simp only [leading, Option.some.injEq] at h
    subst term
    intro t ht
    apply (compare_key order t (leadingAux order first rest) (lengths t ht)
      (lengths _ (leadingAux_mem order first rest))).mpr
    exact leadingAux_max order first rest lengths t ht

private theorem coeffAt_mem {κ : Type*} [Zero κ]
    {terms : Hex.MvPoly.Kernel.PolyList κ}
    (sorted : terms.Pairwise (fun a b => b.1 < a.1))
    {term : List Nat × κ} (h : term ∈ terms) :
    Hex.MvPoly.Kernel.coeffAt term.1 terms = term.2 := by
  induction terms with
  | nil => simp at h
  | cons first rest ih =>
    rcases List.mem_cons.mp h with h | h
    · subst term; simp [Hex.MvPoly.Kernel.coeffAt]
    · have hne : term.1 ≠ first.1 := by
        intro heq
        have hlt := (List.pairwise_cons.mp sorted).1 term h
        rw [heq] at hlt
        exact List.lt_irrefl _ hlt
      simp only [Hex.MvPoly.Kernel.coeffAt, ite_eq_right hne]
      exact ih (List.pairwise_cons.mp sorted).2 h

private theorem coeff_mod_mem {p n : Nat} [Hex.ZMod64.Bounds p]
    {cmp : Hex.Mono n → Hex.Mono n → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    {terms : Polynomial} (canonical : Hex.MvPoly.Kernel.CanonicalMod p n terms)
    {term : List Nat × Nat} (h : term ∈ terms) :
    (Hex.MvPoly.Kernel.denoteMod p (cmp := cmp) terms).coeff (Hex.MvPoly.Kernel.mono n term.1) =
      Hex.ZMod64.ofNat p term.2 := by
  have hc := Hex.MvPoly.Kernel.toResidues_canonical p canonical
  have hm : (term.1, Hex.ZMod64.ofNat p term.2) ∈ Hex.MvPoly.Kernel.toResidues p terms := by
    apply List.mem_map.mpr
    exact ⟨term, h, rfl⟩
  erw [Hex.MvPoly.Kernel.denoteMod, Hex.MvPoly.Kernel.coeff_denote (cmp := cmp)
    term.1 _ (canonical.1.1 term h) hc]
  exact coeffAt_mem hc.2.1 hm

private theorem residue_coeff {p n : Nat} [Hex.ZMod64.Bounds p]
    {cmp : Hex.Mono n → Hex.Mono n → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (terms : Polynomial) (m : Hex.Mono n) :
    (HexMvPolyTheory.Kernel.denoteMod p (cmp := cmp) terms).coeff
        (HexMvPolyTheory.monoEquiv m) =
      HexModArithTheory.ZMod64.equiv ((Hex.MvPoly.Kernel.denoteMod p (cmp := cmp) terms).coeff m) := by
  exact HexMvPolyTheory.Kernel.residueEquiv_coeff p
    (Hex.MvPoly.Kernel.denoteMod p (cmp := cmp) terms) m

private theorem support_mem {p n : Nat} [Hex.ZMod64.Bounds p]
    {cmp : Hex.Mono n → Hex.Mono n → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (terms : Polynomial) {d : Fin n →₀ Nat}
    (h : d ∈ (HexMvPolyTheory.Kernel.denoteMod p (cmp := cmp) terms).support) :
    ∃ term ∈ terms, HexMvPolyTheory.monoEquiv (Hex.MvPoly.Kernel.mono n term.1) = d := by
  induction terms with
  | nil => simp at h
  | cons term terms ih =>
    rw [HexMvPolyTheory.Kernel.denoteMod_cons] at h
    rcases Finset.mem_union.mp (MvPolynomial.support_add h) with h | h
    · have hd := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
      exact ⟨term, by simp, hd.symm⟩
    · obtain ⟨a, ha, he⟩ := ih h
      exact ⟨a, List.mem_cons_of_mem _ ha, he⟩

/-- The selected term has exactly its stored residue coefficient after denotation. -/
theorem leading_coeff {p n : Nat} [Hex.ZMod64.Bounds p]
    (order : Hex.Groebner.TermOrder) {terms : Polynomial} {term : List Nat × Nat}
    (canonical : Hex.MvPoly.Kernel.CanonicalMod p n terms)
    (h : leading order terms = some term) :
    (HexMvPolyTheory.Kernel.denoteMod p (cmp := order.cmp n) terms).coeff
        (HexMvPolyTheory.monoEquiv (Hex.MvPoly.Kernel.mono n term.1)) = (term.2 : ZMod p) := by
  rw [residue_coeff, coeff_mod_mem canonical (leading_mem h)]
  exact HexModArithTheory.ZMod64.toZMod_natCast term.2

/-- The list maximum is the actual leading exponent of the denoted polynomial. -/
theorem leading_degree {p n : Nat} [Hex.ZMod64.Bounds p]
    (order : Hex.Groebner.TermOrder) {terms : Polynomial} {term : List Nat × Nat}
    (canonical : Hex.MvPoly.Kernel.CanonicalMod p n terms)
    (h : leading order terms = some term) :
    (toMonomialOrder (order.cmp n)).degree
        (HexMvPolyTheory.Kernel.denoteMod p (cmp := order.cmp n) terms) =
      HexMvPolyTheory.monoEquiv (Hex.MvPoly.Kernel.mono n term.1) := by
  apply (toMonomialOrder (order.cmp n)).toSyn.injective
  apply le_antisymm
  · apply MonomialOrder.degree_le_iff.mpr
    intro d hd
    obtain ⟨a, ha, rfl⟩ := support_mem terms hd
    apply (compare_le (order.cmp n) _ _).mp
    have bound := leading_max canonical.1.1 h a ha
    have hc := compare_eq order (Hex.MvPoly.Kernel.mono n a.1)
      (Hex.MvPoly.Kernel.mono n term.1)
    rw [Hex.MvPoly.Kernel.toList_mono (canonical.1.1 a ha),
      Hex.MvPoly.Kernel.toList_mono (canonical.1.1 term (leading_mem h))] at hc
    rwa [← hc]
  · apply MonomialOrder.le_degree
    rw [MvPolynomial.mem_support_iff, leading_coeff order canonical h]
    intro hz
    have hc := (ZMod.natCast_eq_zero_iff term.2 p).mp hz
    have hn := canonical.1.2.2 term (leading_mem h)
    have hb := canonical.2 term (leading_mem h)
    exact hn (Nat.eq_zero_of_dvd_of_lt hc hb)

/-- The list maximum's coefficient is the Mathlib leading coefficient. -/
theorem leading_coefficient {p n : Nat} [Hex.ZMod64.Bounds p]
    (order : Hex.Groebner.TermOrder) {terms : Polynomial} {term : List Nat × Nat}
    (canonical : Hex.MvPoly.Kernel.CanonicalMod p n terms)
    (h : leading order terms = some term) :
    (toMonomialOrder (order.cmp n)).leadingCoeff
        (HexMvPolyTheory.Kernel.denoteMod p (cmp := order.cmp n) terms) = (term.2 : ZMod p) := by
  rw [MonomialOrder.leadingCoeff, leading_degree order canonical h]
  exact leading_coeff order canonical h

end HexGroebnerTheory.Certificate
