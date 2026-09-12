/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Initial
public import HexGraphIso.Nauty.Sparse.RefineFuel
public import HexGraphIso.Nauty.Equitable.Root

public section

namespace Hex.GraphIso.Nauty

private theorem foldActive_card (ends : List Nat) (acc : VSet n × Nat) :
    (ends.foldl (fun (p : VSet n × Nat) e => (p.1.insert p.2, e + 1)) acc).1.card ≤
      acc.1.card + ends.length := by
  induction ends generalizing acc with
  | nil => simp
  | cons e ends ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h := ih (acc.1.insert acc.2, e + 1)
    have hi := VSet.card_insert_le acc.1 acc.2
    simp only at h
    omega

/-- Initial activation inserts at most one vertex for each listed cell. -/
theorem initActive_card (n : Nat) (ends : List Nat) :
    (initActive n ends).card ≤ ends.length := by
  simpa only [initActive, VSet.card_empty, Nat.zero_add] using
    foldActive_card ends ((VSet.empty : VSet n), 0)

namespace Sparse

/-- The actual root initializer supplies the premise of refinement's existing
loop bound, for every endpoint list including the empty graph. -/
theorem initial_saturated (g : Graph n) (lab : Array Nat) (ends : List Nat) :
    let s := initial g lab ends
    let t := refineWith g 1 s.lab s.ptn s.active ends.length s.canong.scratch
    t.queue.isEmpty = true ∨ n ≤ t.numcells :=
  refineWith_saturated _ _ _ _ _ _ _ (initActive_card n ends)

/-- Stable sparse colour buckets satisfy the shared, adjacency-independent
partition-state contract. -/
theorem initial_nodeOk (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    NodeOk n 1 p.1 (initPtn n (n + 2) p.2) (initActive n p.2) := by
  simp only [initialPartition_eq]
  exact Nauty.initial_nodeOk G.toDense hn

/-- Every initial sparse colour cell is active. The conversion here is only
the proved ordered-partition bridge; the executable uses sparse adjacency. -/
theorem initial_cells_active (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    ∀ c ∈ cells (initPtn n (n + 2) p.2) 1 n, (initActive n p.2).mem c.1 = true := by
  simp only [initialPartition_eq]
  exact Nauty.initial_cells_active G.toDense hn

/-- The cell count passed to root refinement is its actual boundary count. -/
theorem initial_count (G : GraphIso.Sparse.Colored n k) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    bcount (initPtn n (n + 2) p.2) 1 n = p.2.length := by
  simp only [initialPartition_eq]
  exact bcount_initPtn G.toDense

end Sparse
end Hex.GraphIso.Nauty
