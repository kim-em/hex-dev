/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Init

/-! # Shared ECPP replay policy

The process boundary and elaborators enforce the same admitted numeral ceiling.
-/

@[expose] public section

namespace Hex.ECPP

/-- Numeral ceiling admitted by the fresh-module kernel replay probes. -/
def maxBits : Nat := 512

end Hex.ECPP
