/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Scratch
public import HexGraphIso.Nauty.Sparse.Window

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every valid labelled partition admits a cell index, supplied by the
proved executed indexer. Used to discharge index premises of fresh selectors. -/
theorem Index.exists_valid {n level : Nat} {lab ptn : Array Nat}
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level) :
    ∃ s : Scratch, Index.Valid n lab ptn level s.cellstart s.cellend := by
  let idx := indexCells n lab ptn level (.replicate n n) (.replicate n 0)
  refine ⟨{ Scratch.fresh n with cellstart := idx.1, cellend := idx.2 }, ?_⟩
  exact indexCells_valid lab ptn (.replicate n n) (.replicate n 0) level hs hend
    (fun i hi => perm_bound hp hi) (fun i j hi hj he => perm_injective hp hi hj he)
    (by simp) (by simp)

end Hex.GraphIso.Nauty.Sparse
