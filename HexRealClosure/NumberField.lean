/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.CompleteRoots
public import HexRealAlgebraic.FieldSign

public section

namespace Hex.RealClosure.NumberField

/-- Complete ordered roots over the coordinates of an existing selected real
number field. The generator retains its embedding and the entries retain
their coefficient field, context and exact multiplicities. -/
@[expose] def roots (generator : RealAlgebraicNumber) (context : Nat)
    (p : DensePoly (QAdjoin generator.toAlgebraic)) :
    Roots.Output generator.signField context :=
  Roots.roots generator.signField context p

/-- The checked diagnostic producer for the same number-field operation. -/
@[expose] def roots? (generator : RealAlgebraicNumber) (context : Nat)
    (p : DensePoly (QAdjoin generator.toAlgebraic)) :
    Except SignDet.BuildError (Roots.Output generator.signField context) :=
  Roots.roots? generator.signField context p

end Hex.RealClosure.NumberField
