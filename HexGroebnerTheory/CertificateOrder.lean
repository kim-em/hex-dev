/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.CertificateOrder
public import HexGroebnerTheory.Order
public import Mathlib.Data.List.OfFn

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

end HexGroebnerTheory.Certificate
