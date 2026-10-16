/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RootQuoteData
public section
open Hex Hex.RealClosure Hex.SignDet
namespace Hex.RCF.RationalQuoteTests
/-- Frozen constructor input, including a raw negative integer constructor. -/
@[expose] def negativeFraction : Codec.Json :=
  .array (.cons (.number (Int.ofNat 0))
    (.cons (.number (Int.negSucc 6)) (.cons (.number (Int.ofNat 3)) .nil)))

@[expose] def negativeReader : Except String Hex.RCF.RootQuoteTests.base.Value :=
  Hex.RCF.RootQuoteTests.base.codec.decode negativeFraction
end Hex.RCF.RationalQuoteTests
