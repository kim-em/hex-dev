/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebner.Certificate

@[expose] public section

/-! Monomial-order checks on ordinary exponent lists for certificate replay.
Term-list storage remains descending lex, while leading terms use explicit
computation order metadata. No packed/native-only operation is used here. -/

namespace Hex.Groebner.Certificate

/-- Global monomial comparison on exponent lists of the same validated arity. -/
def compare (order : TermOrder) (a b : List Nat) : Ordering :=
  match order with
  | .lex => Hex.MvPoly.Kernel.expCmp a b
  | .grlex => (Ord.compare a.sum b.sum).then (Hex.MvPoly.Kernel.expCmp a b)
  | .grevlex => (Ord.compare a.sum b.sum).then (List.compareLex (fun x y : Nat => Ord.compare y x) a.reverse b.reverse)

/-- Tail-recursive maximum scan, using constant stack space in compiled replay. -/
def leadingAux (order : TermOrder) (best : List Nat × Nat) : Polynomial → List Nat × Nat
  | [] => best
  | t :: terms => leadingAux order (if compare order t.1 best.1 == .gt then t else best) terms

/-- Largest stored term in the explicit global order, or none for zero.
Canonicality is checked separately and guarantees every stored coefficient is nonzero. -/
def leading (order : TermOrder) : Polynomial → Option (List Nat × Nat)
  | [] => none
  | t :: terms => some (leadingAux order t terms)

/-- Exact pointwise divisibility, rejecting unequal exponent lengths. -/
def divides : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => a ≤ b && divides as bs
  | _, _ => false

/-- Exact least common multiple on exponent lists of the same arity. -/
def lcm : List Nat → List Nat → Option (List Nat)
  | [], [] => some []
  | a :: as, b :: bs => (lcm as bs).map (max a b :: ·)
  | _, _ => none

end Hex.Groebner.Certificate
