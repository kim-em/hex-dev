/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Depth
public import HexGraphIso.Nauty.Sparse.Result
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The completed nonempty root saves its actual first leaf, whose depth
bounds every subsequent first-code comparison. The sentinel and reference
come from execution, with all premises derived from initialization. -/
theorem runState_reference (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    let out := (runState (.ofGraph G.graph) p.1 p.2).2
    ∃ last leaf, 1 ≤ last ∧ last ≤ n ∧ Ready G last n leaf ∧
      out.reference = (firstterminal last leaf).reference ∧ Depth last out := by
  obtain ⟨last, leaf, path, hlast, hleaf⟩ := initial_path G hn
  have hb := Nat.le_trans hleaf.ok.bc (bcount_le _ _ _)
  have hs : last + 1 < (initial (.ofGraph G.graph)
      (initialPartitionWith n k G.coloring.cells.toArray Fin.val).1
      (initialPartitionWith n k G.coloring.cells.toArray Fin.val).2).firstcode.size := by
    change last + 1 < (Array.replicate (n + 2) 0).size
    rw [Array.size_replicate]
    omega
  dsimp only
  rw [runState, ite_eq_right (by simpa using Nat.ne_of_gt hn)]
  exact ⟨last, leaf, hlast, hb, hleaf, firstPath_reference path, firstPath_depth path hs⟩

theorem firstlab_size (G : GraphIso.Sparse.Colored n k) : (runColored G).firstlab.size = n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    rfl
  · obtain ⟨last, leaf, _, _, hleaf, href, _⟩ := runState_reference G hn
    have he := congrArg (fun r : Array Nat × Array Int × Array Nat => r.2.2) href
    change (runColored G).firstlab = leaf.lab at he
    rw [he]
    exact hleaf.ok.labSize

/-- The saved first label, as well as the final incumbent, respects every
original colour cell. It is suitable for a checked automorphism scatter. -/
theorem firstlab_cellsReach (G : GraphIso.Sparse.Colored n k) :
    CellsReach G.toDense (runColored G).firstlab := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    intro a len hcell
    have he : segN (Nauty.initialPartition G.toDense).1 a len =
        segN (runColored G).firstlab a len := by
      refine segN_congr fun o ho => ?_
      rw [getElem!_neg _ _ (by rw [size_initialPartition]; omega),
        getElem!_neg _ _ (by rw [firstlab_size]; omega)]
    rw [he]
  · obtain ⟨last, leaf, _, _, hleaf, href, _⟩ := runState_reference G hn
    have he := congrArg (fun r : Array Nat × Array Int × Array Nat => r.2.2) href
    change (runColored G).firstlab = leaf.lab at he
    rw [he]
    exact hleaf.ok.reach

theorem firstlab_perm (G : GraphIso.Sparse.Colored n k) :
    (runColored G).firstlab.toList.Perm (List.range n) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    have hs : (runColored G).firstlab.toList.length = 0 := by
      rw [Array.length_toList, firstlab_size]
    rw [List.length_eq_zero_iff.mp hs, List.range_zero]
  · exact isPerm_of_cellsReach (firstlab_size G) hn (firstlab_cellsReach G)

end Hex.GraphIso.Nauty.Sparse
