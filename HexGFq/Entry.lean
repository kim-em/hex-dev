/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexConway.Api

public section

namespace Hex.GFq

/-- A committed Conway-table entry available through instance synthesis. -/
class CommittedEntry (p n : Nat) [ZMod64.Bounds p] where
  /-- The verified lookup witness. -/
  entry : Conway.SupportedEntry p n

end Hex.GFq
