/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Basic

public section

/-!
# Fixed-presentation semantic laws

These are the operation laws needed to transfer a field structure to
`QAdjoin`.  The executable carrier deliberately supplies only its concrete
operations; the eventual `AdjoinRoot` correspondence will package these laws
without changing those operations or their rational scalar action.
-/

namespace Hex.QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-- Fixed-presentation zero evaluates to complex zero. -/
theorem map_zero [ZPoly.CheckedIrreducible p] :
    toComplex (0 : QAdjoin p x) = 0 := by
  sorry

/-- Fixed-presentation one evaluates to complex one. -/
theorem map_one [ZPoly.CheckedIrreducible p] :
    toComplex (1 : QAdjoin p x) = 1 := by
  sorry

/-- Fixed-presentation negation agrees with complex negation. -/
theorem map_neg [ZPoly.CheckedIrreducible p] (a : QAdjoin p x) :
    toComplex (-a) = -toComplex a := by
  sorry

/-- Fixed-presentation subtraction agrees with complex subtraction. -/
theorem map_sub [ZPoly.CheckedIrreducible p] (a b : QAdjoin p x) :
    toComplex (a - b) = toComplex a - toComplex b := by
  sorry

/-- The executable rational scalar action is semantic scalar multiplication. -/
theorem map_smul [ZPoly.CheckedIrreducible p] (q : Rat) (a : QAdjoin p x) :
    toComplex (q • a) = (q : ℂ) * toComplex a := by
  sorry

/-- Fixed-presentation division agrees with complex division. -/
theorem map_div [ZPoly.CheckedIrreducible p] (a b : QAdjoin p x) :
    toComplex (a / b) = toComplex a / toComplex b := by
  sorry

/-- Equality in a checked presentation is exactly equality of interpreted
complex values. -/
theorem eq_iff_toComplex [ZPoly.CheckedIrreducible p]
    (a b : QAdjoin p x) :
    a = b ↔ toComplex a = toComplex b := by
  constructor
  · exact fun h => congrArg toComplex h
  · intro h
    exact @toComplex_injective p x _ a b h

end Hex.QAdjoin
