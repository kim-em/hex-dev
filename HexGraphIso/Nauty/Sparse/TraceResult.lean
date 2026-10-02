/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstTrace
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Sparse.Run
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every generator array emitted by the initialized sparse search is a
colour-preserving automorphism. All histories, references and allocation
premises are derived from initialization, including the empty graph. -/
theorem runState_trace (G : GraphIso.Sparse.Colored n k) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    TraceOk G (runState (.ofGraph G.graph) p.1 p.2).2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    dsimp only
    intro values hv
    change values ∈ (#[] : Array (Array Nat)) at hv
    simp at hv
  · obtain ⟨last, leaf, path, _, _⟩ := initial_path G hn
    dsimp only
    rw [runState, ite_eq_right (by simpa using Nat.ne_of_gt hn)]
    apply firstPath_trace hn path (by omega) (NodeInv.initial G hn)
      (FirstShape.initial G.graph _ _)
    · change n < (Array.replicate (n + 2) (-1 : Int)).size
      rw [Array.size_replicate]
      omega
    · change n + 1 < (Array.replicate (n + 2) 0).size
      rw [Array.size_replicate]
      omega
    · rfl
    · exact Array.size_replicate
    · exact TraceOk.initial G _ _

/-- Final row installation retains the sound trace literally. -/
theorem runColored_trace (G : GraphIso.Sparse.Colored n k) : TraceOk G (runColored G) :=
  (runState_trace G).congr rfl

/-- Each literal emitted array has the graph's order and is exactly the
forward map of a native colour-preserving automorphism. This soundness
theorem does not yet assert that the trace generates the entire group. -/
theorem generator_iso (G : GraphIso.Sparse.Colored n k) {values : Array Nat}
    (h : values ∈ (runColored G).genTrace) :
    ∃ p : Perm n, GraphIso.Sparse.IsIso G G p ∧ values.size = n ∧
      ∀ v : Fin n, values[v.val]! = (p.get v).val := by
  obtain ⟨hs, p, hi, hp⟩ := runColored_trace G values h
  exact ⟨p, hi, hs, hp⟩

end Hex.GraphIso.Nauty.Sparse
