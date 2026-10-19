/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealAlgebraic.Order
public import HexNumberField.RealSign
public section
namespace Hex.RealAlgebraicNumber
/-- Sign in the existing real generator's embedding, without canonical conversion. -/
@[expose] def signField (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) : Int :=
  value.signApprox generator.property
end Hex.RealAlgebraicNumber
