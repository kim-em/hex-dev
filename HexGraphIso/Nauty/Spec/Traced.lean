/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

This file contains code translated from the nauty 2.9.3 sources
(https://users.cecs.anu.edu.au/~bdm/nauty/), copyright Brendan McKay and Adolfo
Piperno, released under the Apache 2.0 license.
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
