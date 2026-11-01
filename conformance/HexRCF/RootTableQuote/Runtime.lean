/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RootTableQuote.Table

public section
open Hex Hex.RealClosure Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests Hex.RealClosure.Tower
namespace Hex.RCF.RootTableQuoteTests
open CellReplayTests.Algebraic

-- Emitted kernel declarations must also be compiled before compiled consumers use them.
/-- info: 3 -/
#guard_msgs in
#eval input.size

/-- info: true -/
#guard_msgs in
#eval table.isOk

/-- info: 2 -/
#guard_msgs in
#eval
  letI : One Schema.parent.Value := Algebraic.Element.cachedOne reduction reduction_eq Records.facts
  letI : Add Schema.parent.Value := Algebraic.Element.cachedAdd reduction reduction_eq Records.facts
  letI : Sub Schema.parent.Value := Algebraic.Element.cachedSub reduction reduction_eq Records.facts
  letI : Mul Schema.parent.Value := Algebraic.Element.cachedMul reduction reduction_eq Records.facts
  letI : NatCast Schema.parent.Value := Algebraic.Element.cachedNatCast reduction reduction_eq Records.facts
  restored.roots.length

-- This rejects missing scalar-decoding evidence. It is not a general assertion
-- that no native operation can run after an arbitrary arithmetic fact is omitted.
/-- info: false -/
#guard_msgs in
#eval (readTable [] input).isOk

end Hex.RCF.RootTableQuoteTests
