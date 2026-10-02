/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FuelSweep
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Fuel

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The production bounds are sufficient for the actual sparse mutual
recursion. The frame assertions also cover calls with insufficient bounds. -/
theorem fuelPolicy (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel : Nat) :
    Generic.SoundPolicy (.ofGraph G.graph) (n + 2) tcLevel (fuelContract G) where
  node_zero := by
    intro first level numcells st hin
    refine ⟨FrameOut.refl hin.2, ?_⟩
    intro hf
    have hb := Nat.le_trans hin.2.ok.bc (bcount_le _ _ _)
    omega
  node_step := by
    intro fuel next hnext first level numcells st hin
    exact ⟨reach_node G hn tcLevel (fuel_sweep_reach hnext) first level numcells st hin.1 hin.2,
      fuel_node G hn tcLevel hnext first level numcells st hin.1 hin.2⟩
  sweep_none := by
    intro fuel cfuel first level numcells tc tv1 cell index st hin
    exact ⟨hin.2.1.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hin.2.1.scratch.toBounded,
      fun _ _ => by simp⟩
  sweep_zero := by
    intro fuel first level numcells tc tv1 tv cell index st hin
    refine ⟨hin.2.1.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hin.2.1.scratch.toBounded, ?_⟩
    intro _ hcursor
    have hv := VSet.mem_lt (hin.2.2.2 tv rfl)
    have hf := hcursor tv rfl
    omega
  sweep_step := by
    intro fuel cfuel descend next hd hnext first level numcells tc tv1 tv cell index st hin
    exact ⟨reach_sweep G hn (fuel_node_reach hd) (fuel_sweep_reach hnext)
      first level numcells tc tv1 tv index cell st hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl),
      fun hf hcursor => fuel_sweep G hn hd hnext first level numcells tc tv1 tv index cell st
        hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl) hf (hcursor tv rfl)⟩

/-- A valid production node cannot exhaust the established level bound. -/
theorem node_noFuel (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (first : Bool) (tcLevel fuel level numcells : Nat) (st : State n)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st) (hf : n + 1 ≤ level + fuel) :
    (Generic.node first (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).1 ≠ .fuel :=
  (Generic.node_sound (fuelPolicy G hn tcLevel) first fuel level numcells st ⟨hl, h⟩).2 hf

theorem sweep_noFuel (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (first : Bool) (tcLevel fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : State n) (hl : 1 ≤ level)
    (h : Ready G level numcells st) (ht : Generic.Target State.frame level tc cell st)
    (hv : ∀ v, cursor = some v → cell.mem v = true) (hf : n ≤ level + fuel)
    (hc : Generic.CursorFuel n cfuel cursor) :
    (Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel level numcells
      tc tv1 cursor cell index st).1 ≠ .fuel :=
  (Generic.sweep_sound (fuelPolicy G hn tcLevel) first fuel cfuel level numcells tc tv1 cursor cell index st
    ⟨hl, h, ht, hv⟩).2 hf hc

/-- The pinned sparse production root never reports exhausted recursion,
including order zero. Its existing `n + 2` bound is sufficient unchanged. -/
theorem runState_noFuel (G : GraphIso.Sparse.Colored n k) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    (runState (.ofGraph G.graph) p.1 p.2).1 ≠ .fuel := by
  dsimp only
  by_cases hn : n = 0
  · simp only [runState, hn, beq_self_eq_true, ite_true, ne_eq, reduceCtorEq, not_false_eq_true]
  · have hpos : 0 < n := by omega
    rw [runState, ite_eq_right (by simpa using hn)]
    exact node_noFuel G hpos true 100 (n + 2) 1 _ _ (by omega) (NodeInv.initial G hpos) (by omega)

end Hex.GraphIso.Nauty.Sparse
