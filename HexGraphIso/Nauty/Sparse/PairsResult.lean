/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstPairs
import all HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Sparse.Run
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every pair retained by the actual initialized sparse search has checked
root-colour-preserving realizers. The proof covers explicit and implicit
admissions, full workspace replacement and the empty graph. -/
theorem runState_pairs (G : GraphIso.Sparse.Colored n k) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    PairsOk G (runState (.ofGraph G.graph) p.1 p.2).2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    dsimp only
    intro pair hp
    change pair ∈ ([] : List (VSet 0 × VSet 0)) at hp
    simp at hp
  · obtain ⟨last, leaf, path, _, _⟩ := initial_path G hn
    dsimp only
    rw [runState, ite_eq_right (by simpa using Nat.ne_of_gt hn)]
    apply firstPath_pairs hn path (by omega) (NodeInv.initial G hn)
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
    · exact initial_pairs G _ _
    · exact initial_pathInv G
    · exact initial_boundary G hn
    · exact Nat.le_refl _

/-- Final native row installation preserves the validated bounded pruning
workspace literally; it adds no checks or replay to execution. -/
theorem runColored_pairs (G : GraphIso.Sparse.Colored n k) : PairsOk G (runColored G) :=
  (runState_pairs G).congr rfl

end Hex.GraphIso.Nauty.Sparse
