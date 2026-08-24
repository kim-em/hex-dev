/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.View

@[expose] public section
set_option backward.proofsInPublic true

/-!
Producer-free unit, normalization, and scalar-content operations.

None of these definitions calls the multivariate gcd producer. This is
important because certificate replay needs them before the public
`GcdOps (MvPoly ...)` instance can be assembled.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [GcdOps R]

/-- The constant unit selected from the leading coefficient, with `1` at
zero. -/
@[reducible] def polyNormUnit [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : MvPoly n R cmp :=
  match p.termsList.getLast? with
  | none => 1
  | some (_, c) => C (GcdOps.normUnit c)

/-- Canonical associate selected by the unit attached to the leading
coefficient. -/
@[reducible] def polyNormalize [IsMonomialOrder cmp]
    (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p * polyNormUnit p

/-- Recognize exactly a one-term constant polynomial whose coefficient is a
unit in the base ring. -/
@[reducible] def polyIsUnit (p : MvPoly n R cmp) : Bool :=
  match p.termsList with
  | [(m, c)] => decide (m = Mono.zero) && GcdOps.isUnit c
  | _ => false

/-- Normalized gcd fold of the distributed scalar coefficients. The empty
fold is the specified zero content; a nonempty fold starts at the first
coefficient rather than relying on an unstated `gcd 0 a` law. -/
@[reducible] def scalarContent (p : MvPoly n R cmp) : R :=
  match p.termsList with
  | [] => 0
  | (_, c) :: terms =>
      normalize (terms.foldl (fun g term => GcdOps.gcd g term.2) c)

omit [Dvd R] in
/-- The normalization unit at zero is the constant one polynomial. -/
@[simp] theorem polyNormUnit_zero [IsMonomialOrder cmp] :
    polyNormUnit (0 : MvPoly n R cmp) = 1 := by
  rfl

omit [Dvd R] in
/-- Polynomial normalization preserves zero. -/
@[simp] theorem polyNormalize_zero [IsMonomialOrder cmp] :
    polyNormalize (0 : MvPoly n R cmp) = 0 := by
  rw [polyNormalize, polyNormUnit_zero, Lean.Grind.Semiring.zero_mul]

omit [Dvd R] in
/-- Scalar content uses the explicit zero convention. -/
@[simp] theorem scalarContent_zero :
    scalarContent (0 : MvPoly n R cmp) = 0 := by
  rfl

/-- Unit recognition is sound and complete under the coefficient gcd laws. -/
theorem polyIsUnit_iff [LawfulGcdOps R] (p : MvPoly n R cmp) :
    polyIsUnit p = true ↔ ∃ q, p * q = 1 := by
  sorry

/-- The chosen normalization multiplier is a polynomial unit. -/
theorem polyNormUnit_isUnit [IsMonomialOrder cmp] [LawfulGcdOps R]
    (p : MvPoly n R cmp) :
    polyIsUnit (polyNormUnit p) = true := by
  sorry

/-- Polynomial normalization is idempotent. -/
theorem polyNormalize_idem [IsMonomialOrder cmp] [LawfulGcdOps R]
    (p : MvPoly n R cmp) :
    polyNormalize (polyNormalize p) = polyNormalize p := by
  sorry

end Hex.MvPoly
