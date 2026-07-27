/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Approx

public section

/-!
# Canonicalization and exactification

The checked conversions in `hex-number-field` select canonical irreducible
representatives.  This module states both certificate soundness and the
completeness obligations that make their total wrappers semantically exact.
-/

namespace Hex

namespace AlgebraicNumber

/-- Forgetting minimality preserves the selected complex value. -/
theorem toRoot_toComplex (a : AlgebraicNumber) :
    a.toRoot.toComplex = a.toComplex := by
  rfl

end AlgebraicNumber

namespace AlgebraicRoot

/-- Every successful exactification denotes the original selected root. -/
theorem exact?_sound (a : AlgebraicRoot) {b : AlgebraicNumber}
    (h : a.exact? = some b) :
    b.toComplex = a.toComplex := by
  sorry

/-- Factor selection and isolation always find the canonical representative. -/
theorem exact?_isSome (a : AlgebraicRoot) :
    a.exact?.isSome := by
  sorry

/-- The total canonicalization wrapper preserves the represented value. -/
theorem exact_toComplex (a : AlgebraicRoot) :
    a.exact.toComplex = a.toComplex := by
  sorry

end AlgebraicRoot

namespace QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-- Successful conversion out of fixed coordinates preserves their value at
the selected embedding. -/
theorem toAlgebraicNumber?_sound [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) {b : AlgebraicNumber}
    (hb : a.toAlgebraicNumber? rep h = some b) :
    b.toComplex = toComplex a := by
  sorry

/-- The minimal-polynomial and isolation search for fixed coordinates always
finds a canonical representative. -/
theorem toAlgebraicNumber?_isSome [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    (a.toAlgebraicNumber? rep h).isSome := by
  sorry

/-- The total fixed-presentation conversion preserves the selected complex
value. -/
theorem toAlgebraicNumber_toComplex [ZPoly.CheckedIrreducible p]
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    (a.toAlgebraicNumber rep h).toComplex = toComplex a := by
  sorry

end QAdjoin

end Hex
