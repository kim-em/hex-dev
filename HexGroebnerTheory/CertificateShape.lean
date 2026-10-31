/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateBasis
public import HexGroebnerTheory.CertificateLeading
public import HexGroebnerTheory.Reduced
public import Mathlib.Algebra.Field.ZMod

public section

namespace HexGroebnerTheory.Certificate
open Hex.Groebner.Certificate
open scoped HexMvPolyTheory HexModArithTheory.ZMod64

private theorem shape_row (order : Hex.Groebner.TermOrder) (basis : Array Polynomial)
    (h : checkShape order basis = true) (i : Fin basis.size) :
    ∃ a, leading order basis[i.val] = some a ∧ a.2 = 1 ∧
      ∀ j : Fin basis.size, ∃ b, leading order basis[j.val] = some b ∧
        (i.val < j.val → compare order a.1 b.1 = .gt) ∧
        ∀ term ∈ basis[i.val], divides b.1 term.1 = true → i = j ∧ term.1 = a.1 := by
  simp only [checkShape, Array.getElem_map] at h
  have hi := List.all_eq_true.mp h i (by simp)
  simp only [Fin.getElem_fin] at hi
  cases ha : leading order basis[i.val] with
  | none => rw [ha] at hi; contradiction
  | some a =>
    rw [ha] at hi
    have parts := Bool.and_eq_true_iff.mp hi
    refine ⟨a, rfl, by simpa using parts.1, ?_⟩
    intro j
    have hj := List.all_eq_true.mp parts.2 j (by simp)
    cases hb : leading order basis[j.val] with
    | none => rw [hb] at hj; contradiction
    | some b =>
      rw [hb] at hj
      have conditions := Bool.and_eq_true_iff.mp hj
      refine ⟨b, rfl, ?_, ?_⟩
      · intro hij
        simpa [hij] using conditions.1
      · intro term ht hd
        have test := List.all_eq_true.mp conditions.2 term ht
        have result : i.val = j.val ∧ term.1 = a.1 := by simpa [hd] using test
        exact ⟨Fin.ext result.1, result.2⟩

/-- Shape acceptance gives nonzero monic polynomials with irreducible tails and
no leading monomial dividing a different basis polynomial's terms. -/
theorem checkShape_reduced {p n : Nat} [Hex.ZMod64.Bounds p] [Fact p.Prime]
    (order : Hex.Groebner.TermOrder) (basis : Array Polynomial)
    (canonical : ∀ a ∈ basis, Hex.MvPoly.Kernel.CanonicalMod p n a)
    (h : checkShape order basis = true) :
    IsReduced (toMonomialOrder (order.cmp n))
      (Set.range fun i : Fin basis.size =>
        HexMvPolyTheory.Kernel.denoteMod p (cmp := order.cmp n) basis[i.val]) := by
  intro g hg
  obtain ⟨i, rfl⟩ := hg
  obtain ⟨a, ha, monic, rows⟩ := shape_row order basis h i
  have ci := canonical _ (Array.getElem_mem i.isLt)
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have := (denote_eq_zero_iff ci).mp hz
    simp [this, leading] at ha
  · erw [leading_coefficient order ci ha, monic, Nat.cast_one]
  · intro c hc b hb hd
    obtain ⟨j, rfl⟩ := hb
    obtain ⟨t, ht, rfl⟩ := support_term basis[i.val] hc
    obtain ⟨d, hj, _, irreducible⟩ := rows j
    have cj := canonical _ (Array.getElem_mem j.isLt)
    erw [leading_degree order cj hj] at hd
    have divides := (divides_mono (cj.1.1 _ (leading_mem hj)) (ci.1.1 _ ht)).mpr hd
    obtain ⟨hij, hta⟩ := irreducible t ht divides
    subst j
    refine ⟨rfl, ?_⟩
    erw [hta, leading_degree order ci ha]

/-- Shape acceptance orders the actual Mathlib leading exponents decreasingly. -/
theorem checkShape_sorted {p n : Nat} [Hex.ZMod64.Bounds p]
    (order : Hex.Groebner.TermOrder) (basis : Array Polynomial)
    (canonical : ∀ a ∈ basis, Hex.MvPoly.Kernel.CanonicalMod p n a)
    (h : checkShape order basis = true) (i j : Fin basis.size) (hij : i.val < j.val) :
    (toMonomialOrder (order.cmp n)).toSyn
        ((toMonomialOrder (order.cmp n)).degree
          (HexMvPolyTheory.Kernel.denoteMod p (cmp := order.cmp n) basis[j])) <
      (toMonomialOrder (order.cmp n)).toSyn
        ((toMonomialOrder (order.cmp n)).degree
          (HexMvPolyTheory.Kernel.denoteMod p (cmp := order.cmp n) basis[i])) := by
  obtain ⟨a, ha, _, rows⟩ := shape_row order basis h i
  obtain ⟨b, hb, ordered, _⟩ := rows j
  have ci := canonical _ (Array.getElem_mem i.isLt)
  have cj := canonical _ (Array.getElem_mem j.isLt)
  simp only [Fin.getElem_fin]
  rw [leading_degree order ci ha, leading_degree order cj hb, toSyn_mono, toSyn_mono]
  apply (Std.compare_eq_gt (α := OrderSyn (order.cmp n))).mp
  have comparison := ordered hij
  rwa [compare_mono order (ci.1.1 _ (leading_mem ha)) (cj.1.1 _ (leading_mem hb))] at comparison

end HexGroebnerTheory.Certificate
