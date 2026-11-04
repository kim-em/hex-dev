/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.FiniteFieldCells
public import HexMvPolyTheory.Equiv
public import Mathlib.Tactic.Tauto
public section
open Hex Hex.RealFormula
open scoped HexMvPolyTheory
attribute [local instance 2500] Semiring.toGrindSemiring
namespace Hex.RCF.FiniteFieldCells

theorem meaning (a b x : ℝ) :
    formula.toProp (append (fun i : Fin 2 => if i.val = 0 then a else b) x) ↔
      (x^2-(a+b)*x+a*b < 0 → 1<x ∧ x<2) := by
  simp only [formula, RealFormula.QF.toProp, RealFormula.Atom.toProp, RealFormula.Cmp.toProp, RealFormula.Poly.eval,
    ← HexMvPolyTheory.eval₂_toMvPolynomial]
  simp only [HexMvPolyTheory.toMvPolynomial_add, HexMvPolyTheory.toMvPolynomial_sub,
    HexMvPolyTheory.toMvPolynomial_mul, HexMvPolyTheory.toMvPolynomial_X,
    HexMvPolyTheory.toMvPolynomial_C, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C]
  simp [RealFormula.append, pow_two]
  rw [← not_lt]
  tauto
end Hex.RCF.FiniteFieldCells
