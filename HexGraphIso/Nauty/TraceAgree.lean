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
The traced search agrees with the production search: both run the
identical traversal on the identical initial state — the trace is
recorded unconditionally and merely discarded by `run` — so the
traced result is definitionally the production result. This is the
tie that lets the certificate producer's key (built from the traced
run) constrain the labelling `certifyCanon?` validates (taken from
the untraced run).
-/

namespace Hex.GraphIso.Nauty

/-- The traced run's result is the production run's result. -/
theorem runTraced_result (n : Nat) (g lab0 : Array Nat)
    (cellEnds : List Nat) :
    (runTraced n g lab0 cellEnds).result = run n g lab0 cellEnds := by
  rw [runTraced, run]
  rcases Decidable.em ((n == 0) = true) with h0 | h0
  · simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      ite_eq_left h0]
  · simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      ite_eq_right h0]

variable {n k : Nat}

/-- The traced coloured-graph run agrees with the production run. -/
theorem runColoredTraced_result (G : Colored n k) :
    (runColoredTraced G).result = runColored G := by
  rw [runColoredTraced, runColored]
  exact runTraced_result n (rowsOf G) (initialPartition G).1
    (initialPartition G).2

end Hex.GraphIso.Nauty
