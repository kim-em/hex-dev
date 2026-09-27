/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.Import
public import HexECPP.Fixture65
meta import HexECPP.Import
meta import HexECPP.Fixture65

public section

namespace Hex.ECPP.ImportConformance

def budget : ImportBudget :=
  ⟨4096, 100, 10, 128, 128, 256, 100⟩

def pari65 : String :=
  "[[18446744073709551629, -8423788454, 160388, 1, [10598342506117936052, 2225259013356795550]]]"

#guard match convertText budget pari65 Fixture65.child with
  | .ok cert => checkAt 18446744073709551629 cert
  | .error _ => false

end Hex.ECPP.ImportConformance
