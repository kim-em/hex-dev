/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstRef
import all HexGraphIso.Nauty.Sparse.FirstRef
public import HexGraphIso.Sparse.Run
import all HexGraphIso.Sparse.Run
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every nonempty initialized native search retains the complete selected
first-reference history, with no external path, cache or code premise. -/
theorem runState_history (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    let st := initial (.ofGraph G.graph) p.1 p.2
    ∃ href : FirstRef G.graph 100 1 (State.refined (.ofGraph G.graph) 1 p.2.length st)
      (runState (.ofGraph G.graph) p.1 p.2).2,
      1 ≤ href.last ∧ href.last ≤ n := by
  obtain ⟨last, leaf, path, hlast, hleaf⟩ := initial_path G hn
  have hb := Nat.le_trans hleaf.ok.bc (bcount_le _ _ _)
  obtain ⟨href, he⟩ := firstRef_of_path (inf := n + 2) hn path (Nat.le_refl _) (NodeInv.initial G hn)
    (by change n < (Array.replicate (n + 2) (-1 : Int)).size; simp)
    (by change n + 1 < (Array.replicate (n + 2) 0).size; simp)
  dsimp only
  rw [runState, ite_eq_right (by simpa using Nat.ne_of_gt hn)]
  exact ⟨href, by rw [he]; exact ⟨hlast, hb⟩⟩

/-- Final native row installation retains the same first-reference
history in the diagnostic result. -/
theorem runColored_history (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    let st := initial (.ofGraph G.graph) p.1 p.2
    ∃ href : FirstRef G.graph 100 1 (State.refined (.ofGraph G.graph) 1 p.2.length st) (runColored G),
      1 ≤ href.last ∧ href.last ≤ n := by
  obtain ⟨href, hb⟩ := runState_history G hn
  exact ⟨href.congr rfl, hb⟩

end Hex.GraphIso.Nauty.Sparse
