/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Search
import all HexGraphIso.Nauty.Search

public section

/-!
The traced search agrees with the production search: `run` is the
`result` projection of `runTraced`, so the two agree by definition.
This is what lets the certificate producer's key (built from the
traced run) constrain the labelling `certifyCanon?` validates (taken
from `run`).
-/

namespace Hex.GraphIso.Nauty

/-- The traced run's result is the production run's result. -/
theorem runTraced_result (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat)
    (cellEnds : List Nat) :
    (runTraced n g lab0 cellEnds).result = run n g lab0 cellEnds := by
  rw [run]

variable {n k : Nat}

/-- The traced coloured-graph run agrees with the production run. -/
theorem runColoredTraced_result (G : Colored n k) :
    (runColoredTraced G).result = runColored G := by
  rw [runColored]

end Hex.GraphIso.Nauty
