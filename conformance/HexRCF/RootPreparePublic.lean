/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RootPreparePacket
public section

/-! Ordinary public-module consumers of the retained original packet proof. -/
open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RootPreparePublic

theorem accepted :
    (ScalarPacket.read RootHeaderPacket.model RootQuoteTests.base.codec
      RootPreparePacket.context RootHeaderPacket.polynomial 1 RootHeaderPacket.evidence).isSome = true := by
  rw [RootPreparePacket.read_checked]
  rfl

theorem sign : RootPreparePacket.fact.sign = 1 :=
  (ScalarPacket.fields RootHeaderPacket.model RootQuoteTests.base.codec RootPreparePacket.context
    RootHeaderPacket.polynomial 1 RootHeaderPacket.evidence RootPreparePacket.fact
    RootPreparePacket.read_checked).2

end Hex.RCF.RootPreparePublic
