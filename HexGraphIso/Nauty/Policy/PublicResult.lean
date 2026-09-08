/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Result
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The engine returns a full canonical labelling. -/
theorem canonlab_size (G : Colored n k) : (runColored G).canonlab.size = n := Engine.canonlab_size G

/-- The engine's canonical labelling fills each initial colour cell with its own vertices. -/
theorem canonlab_cellsReach (G : Colored n k) : CellsReach G (runColored G).canonlab := Engine.canonlab_cellsReach G

/-- The engine's canonical labelling respects the initial colour order. -/
theorem labelColorSorted_canonlab (G : Colored n k) :
    labelColorSorted G (runColored G).canonlab = true := Engine.labelColorSorted_canonlab G

/-- The engine's canonical labelling is a permutation of the vertices. -/
theorem canonlab_perm_range (G : Colored n k) :
    (runColored G).canonlab.toList.Perm (List.range n) := Engine.canonlab_perm_range G

/-- Finishing the engine fills every canonical row from the installed labelling. -/
theorem canong_inv (G : Colored n k) :
    CanongInv { g := rowsOf G } (runColored G).canong (runColored G).canonlab n :=
  Engine.canong_inv G

/-- The returned row array encodes the engine's returned labelling. -/
theorem canong_rows (G : Colored n k) :
    (List.range n).map ((runColored G).canong[·]!) =
      leafRows { g := rowsOf G } (runColored G).canonlab := Engine.canong_rows G

/-- Discarding the trace gives the engine's ordinary result. -/
theorem runTraced_result (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat) (cellEnds : List Nat) :
    (runTraced n g lab0 cellEnds).result = run n g lab0 cellEnds := Engine.runTraced_result n g lab0 cellEnds

/-- The traced coloured run and ordinary coloured run have the same result. -/
theorem runColoredTraced_result (G : Colored n k) :
    (runColoredTraced G).result = runColored G := Engine.runColoredTraced_result G

end Hex.GraphIso.Nauty
