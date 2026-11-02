/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.TreeQuote
public section
namespace Hex.RCF.TreeQuotePublic

theorem leaf_true : Hex.RCF.TreeQuote.leafTrue.toOption = some 7 :=
  Hex.RCF.TreeQuote.leafAccepted

theorem leaf_false : Hex.RCF.TreeQuote.leafFalse.toOption = some 29 :=
  Hex.RCF.TreeQuote.leafRefused

theorem split_true : Hex.RCF.TreeQuote.splitTrue.toOption = some 31 :=
  Hex.RCF.TreeQuote.splitAccepted

theorem split_false : Hex.RCF.TreeQuote.splitFalse.toOption = some 37 :=
  Hex.RCF.TreeQuote.splitRefused

end Hex.RCF.TreeQuotePublic
