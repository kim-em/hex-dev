/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Batteries.Data.Except

/-!
# Reducible decidable equality for `Except`

Batteries derives `DecidableEq (Except ε α)` but, since it moved to targeted
`@[expose]` attributes, no longer exposes the instance's body. Elaboration-time
`decide`, which RCF reflection and the codec conformance checks use on
`Except`-valued replays, then cannot reduce it. This module derives an exposed
copy that instance resolution prefers. Remove it once Batteries exposes its
instance again.
-/

@[expose] public section

deriving instance DecidableEq for Except

end
