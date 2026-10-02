/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDetMathlib.Bareiss

public section

/-!
The field arm.

A field recipe currently runs Bareiss through the division it carries, so its law
is the exact-quotient law for the guarded form of that division. The hypothesis is
the carried division's own cancellation `div (a * b) b = a` for `b ≠ 0`, over the
ambient multiplication: a second ring structure on the same type would not do.

Forward elimination is the arm this row will gain. Its correctness will relate an
accumulated pivot product and swap sign to the input determinant through the
row-operation lemmas of `HexDeterminant/RowOps.lean`, and prove that a failed
pivot column gives determinant zero. Until that operation exists below dispatch
there is nothing here to state about it.
-/

namespace HexDetMathlib

open Hex.Det

universe u

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R] {n : Nat}

/-- Guarding a division that cancels nonzero right factors yields an exact
quotient: the guard only fires on the zero denominator the law excludes. -/
theorem guardQuot_mul_right {div : R → R → R}
    (hdiv : ∀ a b : R, b ≠ 0 → div (a * b) b = a) (a b : R) (hb : b ≠ 0) :
    guardQuot div (a * b) b = a := by
  rw [guardQuot, ite_eq_right hb]
  exact hdiv a b hb

omit [DecidableEq R] in
/-- The field recipe is lawful when its carried division cancels nonzero right
factors. -/
theorem lawfulPolicy_field (deq : DecidableEq R) (div : R → R → R)
    (hdiv : ∀ a b : R, b ≠ 0 → div (a * b) b = a) :
    LawfulPolicy (Policy.field deq div FieldArm.bareiss) :=
  lawfulPolicy_of_eval_eq fun A =>
    @bareissDet_eq_det R _ deq _ (@guardQuot R _ deq div)
      (fun a _ hb => @guardQuot_mul_right R _ deq div hdiv a _ hb) A

/-- Over a field, division cancels nonzero right factors, so the shipped field
recipe is lawful. -/
theorem lawfulPolicy_fieldPolicy {F : Type u} [Lean.Grind.Field F] [DecidableEq F] :
    LawfulPolicy (fieldPolicy (F := F)) :=
  lawfulPolicy_field inferInstance (· / ·) fun a b hb =>
    Hex.ExactDivLaws.mul_div_cancel_right a b hb

end HexDetMathlib
