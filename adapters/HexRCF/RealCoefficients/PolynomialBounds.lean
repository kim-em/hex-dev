/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealFormula
public import HexOrderedFn.Oracle
public section

namespace Hex.RCF.RealCoefficients.PolynomialBounds
open Hex.OrderedFn.Oracle

scoped instance : One Bounds := ⟨Bounds.singleton 1⟩
scoped instance : Mul Bounds := ⟨Bounds.mul⟩

open scoped Hex.RCF.RealCoefficients.PolynomialBounds

@[simp] theorem one_eq : (1 : Bounds) = Bounds.singleton 1 := rfl

@[simp] theorem mul_eq (a b : Bounds) : a * b = a.mul b := rfl

/-- Existing polynomial storage over rational coefficients. The source
formula syntax remains the shared integer schema. Rational constants in this
coefficient ring also represent every dyadic isolation endpoint exactly. -/
abbrev Poly (n : Nat) := MvPoly n Rat Mono.lex

/-- Enclose the existing polynomial representation at fixed coefficient bounds.
Monomial powers reuse the shared logarithmic exponentiation; no ring or field
laws are asserted for interval arithmetic. -/
@[expose] def enclose (bounds : Fin n → Bounds) (p : Poly n) : Bounds :=
  p.termsList.foldl (fun acc term =>
    acc.add ((Bounds.singleton term.2).mul (Mono.prod bounds term.1)))
    (Bounds.singleton 0)

/-- A fixed finite observation. An interval containing zero declines unless
it is the exact singleton zero. This function performs no refinement. -/
@[expose] def sign? (bounds : Fin n → Bounds) (p : Poly n) : Option Int :=
  (enclose bounds p).exactSign?

end Hex.RCF.RealCoefficients.PolynomialBounds
