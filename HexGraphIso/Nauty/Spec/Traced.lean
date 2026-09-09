/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Search.Search
public import HexGraphIso.Nauty.Spec.CanonSpec

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The full key read from the structured engine's trace. -/
@[expose] def tracedKey (G : Colored n k) : Key n :=
  ⟨(runColoredTraced G).bestCodes ++ [codeSentinel],
    leafRows { g := rowsOf G } (runColoredTraced G).result.canonlab⟩

end Hex.GraphIso.Nauty
