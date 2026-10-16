/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients
public section

namespace Hex.RCF.ScalarQuotePublic
open Hex Hex.RealClosure Hex.SignDet

/-- The ordinary bridge is available through the optional umbrella in a module. -/
theorem accepted {E Ctx : Type} [Zero E] [DecidableEq E]
    [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
    [DecidableEq Ctx] {sign : E → Int} {parent : Ctx}
    {context : Algebraic.Context E Ctx sign parent}
    (value : ValueCodec E) (facts : List (Algebraic.SignFact context))
    (literal : Codec.Json) (a : Algebraic.Element context)
    (checked : ((Algebraic.Element.signCodec value facts).decode literal).toOption = some a) :
    ((Algebraic.Element.codec value).decode literal).toOption = some a :=
  Hex.RCF.RealCoefficients.ScalarQuote.accepted value facts literal a checked

/-- Ordinary consumers can use the reader bridge emitted by polynomial quotation. -/
example (x : Nat) : (Except.ok x : Except String Nat).toOption = some x :=
  Hex.RCF.RealCoefficients.RootQuote.read_some (.ok x) x rfl

end Hex.RCF.ScalarQuotePublic
