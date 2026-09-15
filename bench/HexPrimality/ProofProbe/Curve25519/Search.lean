/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Elab
public meta import HexPrimality.Elab

public section

namespace Hex.PrimalityCurveProbe

def input : Nat := 2 ^ 255 - 19

#eval match Hex.Nat.Construction.run input (Hex.Rand.ofSeed input) with
  | .ok s => s.attempts
  | .error _ => panic! "construction exhausted"

end Hex.PrimalityCurveProbe
