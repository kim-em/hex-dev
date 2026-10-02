/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FixedSweep
import all HexGraphIso.Nauty.Policy.Generic.Calls
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Sparse.Run
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Actual sparse node and sweep calls restore their fixed-point bitsets.
The recursion uses the independently proved native frame effects. -/
theorem fixedPolicy (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel : Nat) :
    Generic.CallPolicy (.ofGraph G.graph) (n + 2) tcLevel (fixedContract G) where
  node_zero := fun _ _ _ _ _ => rfl
  node_step := fun _ hnext first level numcells st hin =>
    fixed_node G hn tcLevel hnext first level numcells st hin.1 hin.2.1 hin.2.2
  sweep_none := fun _ _ _ _ _ _ _ _ _ _ _ => rfl
  sweep_zero := fun _ _ _ _ _ _ _ _ _ _ _ => rfl
  sweep_step := fun _ _ hd hnext first level numcells tc tv1 tv cell index st hin =>
    fixed_sweep G hn tcLevel hd hnext first level numcells tc tv1 tv index cell st
      hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2.1 tv rfl) hin.2.2.2.2

/-- Every production node restores its incoming fixed vertices, including
operational truncation and returns that unwind past several ancestors. -/
theorem node_fixed {G : GraphIso.Sparse.Colored n k} (hn : 0 < n) (first : Bool)
    (tcLevel fuel level numcells : Nat) (st : State n)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st) (hf : FixedCells level st.frame) :
    (Generic.node first (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2.fixedpts =
      st.fixedpts :=
  Generic.node_calls (fixedPolicy G hn tcLevel) first fuel level numcells st ⟨hl, h, hf⟩

/-- Every production sweep restores its incoming fixed vertices, including
all orbit skips, short and long filters, and nonlocal exits. -/
theorem sweep_fixed {G : GraphIso.Sparse.Colored n k} (hn : 0 < n) (first : Bool)
    (tcLevel fuel cfuel level numcells tc tv1 index : Nat) (cursor : Option Nat) (cell : VSet n) (st : State n)
    (hl : 1 ≤ level) (h : Ready G level numcells st) (ht : Generic.Target State.frame level tc cell st)
    (hv : ∀ v, cursor = some v → cell.mem v = true) (hf : FixedCells level st.frame) :
    (Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel level numcells tc tv1
      cursor cell index st).2.2.fixedpts = st.fixedpts :=
  Generic.sweep_calls (fixedPolicy G hn tcLevel) first fuel cfuel level numcells tc tv1 cursor cell index st
    ⟨hl, h, ht, hv, hf⟩

/-- The completed initialized search has removed every temporary fixed
vertex. All root validity and singleton premises follow from initialization. -/
theorem runColored_fixed (G : GraphIso.Sparse.Colored n k) :
    (runColored G).fixedpts = VSet.empty := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    rfl
  · let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    have hf : FixedCells 1 (initial (.ofGraph G.graph) p.1 p.2).frame := by
      intro v hv hm
      change VSet.empty.mem v = true at hm
      simp at hm
    have hs := node_fixed hn true 100 (n + 2) 1 p.2.length _ (by omega) (NodeInv.initial G hn) hf
    change (runState (.ofGraph G.graph) p.1 p.2).2.fixedpts = VSet.empty
    rw [runState, ite_eq_right (by simpa using Nat.ne_of_gt hn)]
    exact hs

end Hex.GraphIso.Nauty.Sparse
