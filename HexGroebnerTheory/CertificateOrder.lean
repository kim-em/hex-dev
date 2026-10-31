/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateOrder
public import HexGroebnerTheory.Order
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Forall2

public section

namespace HexGroebnerTheory.Certificate
open Hex

private theorem degree_eq_sum {n : Nat} (m : Mono n) : Mono.degree m = m.toList.sum := by
  have mapped : (List.finRange n).map (fun i => m[i]) = m.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [Vector.getElem_toList]
  rw [← mapped, List.sum_eq_foldl_nat, List.foldl_map]
  rfl

/-- List comparison is exactly the existing lawful monomial comparison. -/
theorem compare_eq {n : Nat} (order : Hex.Groebner.TermOrder)
    (a b : Mono n) :
    Hex.Groebner.Certificate.compare order a.toList b.toList = order.cmp n a b := by
  cases order with
  | lex => simp [Hex.Groebner.Certificate.compare, Hex.Groebner.TermOrder.cmp,
      Mono.lex, Hex.MvPoly.Kernel.expCmp_eq_compare, List.compare_eq_compareLex]
  | grlex => simp [Hex.Groebner.Certificate.compare, Hex.Groebner.TermOrder.cmp,
      Mono.grlex, Mono.lex, compareLex, degree_eq_sum, Hex.MvPoly.Kernel.expCmp_eq_compare, List.compare_eq_compareLex]
  | grevlex =>
    simp [Hex.Groebner.Certificate.compare, Hex.Groebner.TermOrder.cmp,
      Mono.grevlex, Mono.revlex, compareLex, degree_eq_sum]

/-- Fixed-arity serialized exponents have the existing monomial comparison. -/
theorem compare_mono {n : Nat} (order : Hex.Groebner.TermOrder) {a b : List Nat}
    (ha : a.length = n) (hb : b.length = n) :
    Hex.Groebner.Certificate.compare order a b =
      order.cmp n (Hex.MvPoly.Kernel.mono n a) (Hex.MvPoly.Kernel.mono n b) := by
  simpa only [Hex.MvPoly.Kernel.toList_mono ha, Hex.MvPoly.Kernel.toList_mono hb] using
    compare_eq order (Hex.MvPoly.Kernel.mono n a) (Hex.MvPoly.Kernel.mono n b)

private theorem divides_forall₂ (a b : List Nat) :
    Hex.Groebner.Certificate.divides a b = true ↔ List.Forall₂ (· ≤ ·) a b := by
  induction a generalizing b with
  | nil => cases b <;> simp [Hex.Groebner.Certificate.divides]
  | cons a as ih =>
    cases b <;> simp [Hex.Groebner.Certificate.divides, List.forall₂_cons, ih]

/-- Checked list divisibility is exactly pointwise exponent divisibility. -/
theorem divides_mono {n : Nat} {a b : List Nat} (ha : a.length = n) (hb : b.length = n) :
    Hex.Groebner.Certificate.divides a b = true ↔
      HexMvPolyTheory.monoEquiv (Hex.MvPoly.Kernel.mono n a) ≤
        HexMvPolyTheory.monoEquiv (Hex.MvPoly.Kernel.mono n b) := by
  rw [divides_forall₂, Finsupp.le_def]
  simp only [HexMvPolyTheory.monoEquiv_apply, Hex.MvPoly.Kernel.get_mono]
  constructor
  · intro h i
    have hia : i.val < a.length := by omega
    have hib : i.val < b.length := by omega
    simpa [List.getD_eq_getElem?_getD, hia, hib] using h.get hia hib
  · intro h
    apply List.forall₂_of_length_eq_of_get (ha.trans hb.symm)
    intro i hi hj
    have hin : i < n := by omega
    simpa [List.getD_eq_getElem?_getD, hi, hj] using h ⟨i, hin⟩

end HexGroebnerTheory.Certificate
