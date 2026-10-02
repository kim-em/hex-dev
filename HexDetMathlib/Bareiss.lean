/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDetMathlib.Basic
public import HexBareissMathlib

public section

/-!
The exact-quotient Bareiss arm.

`HexBareissMathlib.bareissWith_eq_det` already equates fraction-free Bareiss with
the reference determinant over any Mathlib commutative ring whose supplied
quotient cancels nonzero right factors, with no nondegeneracy hypothesis. The
work here is moving that statement onto the lightweight ring instance the
executable carriers compute with, which
`HexPolyMathlib.toGrind_commRingOfGrind` does.
-/

namespace HexDetMathlib

open Hex.Det

universe u

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R] {n : Nat}

/-- Fraction-free Bareiss over an exact quotient computes the reference
determinant. -/
theorem bareissDet_eq_det (quot : R → R → R)
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a) (A : Hex.Matrix R n n) :
    bareissDet quot A = Hex.Matrix.det A := by
  let _ : CommRing R := HexPolyMathlib.commRingOfGrind
  exact HexMatrixMathlib.bareissWith_eq_det quot hquot A

omit [DecidableEq R] in
/-- The exact-quotient recipe is lawful when its stored quotient cancels nonzero
right factors. A supplied quotient without its law proves nothing. -/
theorem lawfulPolicy_bareiss (deq : DecidableEq R) (quot : R → R → R)
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a) :
    LawfulPolicy (Policy.bareiss deq quot) :=
  lawfulPolicy_of_eval_eq fun A => @bareissDet_eq_det R _ deq _ quot hquot A

/-- The exact-quotient recipe of `Hex.Det.quotientPolicy` is lawful whenever the
carrier's division is exact. This is the law behind the dense-polynomial and
multivariate carrier recipes. -/
theorem lawfulPolicy_quotientPolicy [Div R] [Hex.ExactDivLaws R] :
    LawfulPolicy (quotientPolicy (R := R)) :=
  lawfulPolicy_bareiss inferInstance Hex.exactDiv fun a _ hb => Hex.exactDiv_mul_right a hb

end HexDetMathlib
