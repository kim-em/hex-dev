/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstNode
public import HexGraphIso.Nauty.Sparse.MaxUpperResult
public import HexGraphIso.Nauty.Sparse.Fuel
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.Search

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- For every nonempty sparse coloured graph, the literal production
search installs exactly the declarative sparse maximum. Its first-path
context is initialized from the actual colour buckets, all recursive
coverage is proved, and the existing production bound excludes exhaustion. -/
theorem runState_max (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    State.best G.graph (runState (.ofGraph G.graph) p.1 p.2).2 = some (canonSpecKey G) := by
  intro p
  have h := Max.FirstInput.initial G hn 100
  obtain ⟨last, leaf, path, _, _⟩ := initial_path G hn
  have hm := h.maximum path (by change n + 1 ≤ 1 + (n + 2); omega)
  have he := hm.root (node_noFuel G hn true 100 (n + 2) 1 p.2.length
    (initial (.ofGraph G.graph) p.1 p.2) (by omega) (NodeInv.initial G hn) (by omega))
  rw [Max.Frame.initial_key G hn] at he
  unfold runState
  rw [beq_eq_false_iff_ne.mpr (by omega : n ≠ 0)]
  exact he

/-- Finishing the pending sparse row cache retains the same exact maximum.
This is the state consumed by the total native public API. -/
theorem run_max (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    State.best G.graph (run (.ofGraph G.graph) p.1 p.2) = some (canonSpecKey G) := by
  exact runState_max G hn

end Hex.GraphIso.Nauty.Sparse
