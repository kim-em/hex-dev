/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Filters

public import HexGraphIso.Nauty.Policy.FirstRun
import all HexGraphIso.Nauty.Policy.FirstRun
import all HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.Orbits
import all HexGraphIso.Nauty.Policy.Colors
import all HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- The complete engine run justifies every orbit pointer by its recorded generators. -/
theorem runState_orbits (G : Colored n k) :
    OrbitsOk (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst n
    exact initial_orbits 0 (initialPartition G).1 (initialPartition G).2
  · exact (runState_safe G hn0).orbits

/-- Every generator in the completed run stabilizes the initial colour partition. -/
theorem runState_colors (G : Colored n k) :
    TraceStab G (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst n
    intro perm hp
    change perm ∈ (#[] : Array (Array Nat)) at hp
    simp at hp
  · exact (runState_safe G hn0).colors

/-- Every pair in the final workspace has checked colour-preserving realizers. -/
theorem runState_pairs (G : Colored n k) :
    PairsOk G { g := rowsOf G }
      (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst n
    exact initial_pairs G { g := rowsOf G }
  · exact (runState_safe G hn0).pairs

/-- The structured engine's reported generators preserve the ordered colour cells. -/
theorem runColoredTraced_stab (G : Colored n k) {perm : Array Nat}
    (hp : perm ∈ (runColoredTraced G).autos) : ColorStab G perm :=
  runState_colors G perm hp

/-- The engine returns a full canonical labelling. -/
theorem canonlab_size (G : Colored n k) : (runColored G).canonlab.size = n := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst n
    rfl
  · exact (runState_safe G hn0).canonical.1

/-- The engine's canonical labelling fills each initial colour cell with its own vertices. -/
theorem canonlab_cellsReach (G : Colored n k) : CellsReach G (runColored G).canonlab := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst n
    intro a len hcell
    have he : segN (initialPartition G).1 a len = segN (runColored G).canonlab a len := by
      refine segN_congr fun o ho => ?_
      rw [getElem!_neg _ _ (by rw [size_initialPartition]; omega),
        getElem!_neg _ _ (by rw [canonlab_size]; omega)]
    rw [he]
  · exact (runState_safe G hn0).canonical.2

/-- The engine's canonical labelling respects the initial colour order. -/
theorem labelColorSorted_canonlab (G : Colored n k) :
    labelColorSorted G (runColored G).canonlab = true :=
  labelColorSorted_of_cellsReach (canonlab_size G) (canonlab_cellsReach G)

/-- The engine's canonical labelling is a permutation of the vertices. -/
theorem canonlab_perm_range (G : Colored n k) :
    (runColored G).canonlab.toList.Perm (List.range n) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst n
    have hsz := canonlab_size G
    rw [List.range_zero]
    have : (runColored G).canonlab.toList.length = 0 := by rw [Array.length_toList, hsz]
    rw [List.length_eq_zero_iff.mp this]
  · exact isPerm_of_cellsReach (canonlab_size G) hn0 (canonlab_cellsReach G)

/-- Finishing the engine fills every canonical row from the installed labelling. -/
theorem canong_inv (G : Colored n k) :
    CanongInv { g := rowsOf G } (runColored G).canong (runColored G).canonlab n :=
  updatecan_inv (runState_store G)

/-- The returned row array encodes the engine's returned labelling. -/
theorem canong_rows (G : Colored n k) :
    (List.range n).map ((runColored G).canong[·]!) = leafRows { g := rowsOf G } (runColored G).canonlab :=
  rows_of_canongInv (canong_inv G)

/-- Discarding the trace gives the engine's ordinary result. -/
theorem runTraced_result (n : Nat) (g : Array (VSet n)) (lab0 : Array Nat) (cellEnds : List Nat) :
    (runTraced n g lab0 cellEnds).result = run n g lab0 cellEnds := by rw [run]

/-- The traced coloured run and ordinary coloured run have the same result. -/
theorem runColoredTraced_result (G : Colored n k) :
    (runColoredTraced G).result = runColored G := by rw [runColored]

end Hex.GraphIso.Nauty.Engine
