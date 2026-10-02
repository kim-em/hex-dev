/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReachSweep
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Reach

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The executed sparse policy meets the shared mutual recursion's complete
partition, equitable-parent, colour-reachability and scratch contract. -/
theorem reachPolicy (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel : Nat) :
    Generic.SoundPolicy (.ofGraph G.graph) (n + 2) tcLevel (reachContract G) where
  node_zero := fun _ _ _ _ hin => FrameOut.refl hin.2
  node_step := by
    intro fuel next hnext first level numcells st hin
    exact reach_node G hn tcLevel hnext first level numcells st hin.1 hin.2
  sweep_none := by
    intro fuel cfuel first level numcells tc tv1 cell index st hin
    exact hin.2.1.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hin.2.1.scratch.toBounded
  sweep_zero := by
    intro fuel first level numcells tc tv1 tv cell index st hin
    exact hin.2.1.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hin.2.1.scratch.toBounded
  sweep_step := by
    intro fuel cfuel descend next hd hnext first level numcells tc tv1 tv cell index st hin
    exact reach_sweep G hn hd hnext first level numcells tc tv1 tv index cell st
      hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl)

/-- Every production node preserves its caller's partition frame, including
truncated calls and nonlocal returns. -/
theorem node_frame (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (first : Bool) (tcLevel fuel level numcells : Nat) (st : State n)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st) :
    FrameOut G (level - 1) level st
      (Generic.node first (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 :=
  Generic.node_sound (reachPolicy G hn tcLevel) first fuel level numcells st ⟨hl, h⟩

theorem sweep_frame (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (first : Bool) (tcLevel fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : State n) (hl : 1 ≤ level)
    (h : Ready G level numcells st) (ht : Generic.Target State.frame level tc cell st)
    (hv : ∀ v, cursor = some v → cell.mem v = true) :
    FrameOut G level level st
      (Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel level numcells
        tc tv1 cursor cell index st).2.2 :=
  Generic.sweep_sound (reachPolicy G hn tcLevel) first fuel cfuel level numcells tc tv1 cursor cell index st
    ⟨hl, h, ht, hv⟩

/-- The actual initialized root has the production frame guarantee, with
all entry hypotheses derived from its stable colour buckets. -/
theorem runState_frame (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    FrameOut G 0 1 (initial (.ofGraph G.graph) p.1 p.2)
      (runState (.ofGraph G.graph) p.1 p.2).2 := by
  have h := node_frame G hn true 100 (n + 2) 1 _ _ (by omega) (NodeInv.initial G hn)
  dsimp only
  rw [runState, ite_eq_right (by simpa using Nat.ne_of_gt hn)]
  exact h

/-- Final canonical-row installation preserves the whole production frame. -/
theorem run_frame (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    FrameOut G 0 1 (initial (.ofGraph G.graph) p.1 p.2)
      (run (.ofGraph G.graph) p.1 p.2) :=
  (runState_frame G hn).congr rfl rfl rfl rfl (run_bounded (.ofGraph G.graph) _ _)

end Hex.GraphIso.Nauty.Sparse
