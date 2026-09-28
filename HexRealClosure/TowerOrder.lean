/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerContext

public section

namespace Hex.RealClosure.Tower
variable {registry : BaseContext.Registry}

/-- Semantic equality through the native sign of a difference. Stored
nonzero expressions may differ literally while representing the same value. -/
@[expose] def Context.equal (context : Context registry) (a b : context.Value) : Bool :=
  decide (context.sign (a - b) = 0)

/-- Compare values owned by this exact immutable context. -/
@[expose] def Context.compare (context : Context registry) (a b : context.Value) : Ordering :=
  let sign := context.sign (a - b)
  if sign < 0 then .lt else if sign = 0 then .eq else .gt

end Hex.RealClosure.Tower
