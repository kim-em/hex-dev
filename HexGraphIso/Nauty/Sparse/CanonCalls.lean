/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonSweep
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Reach

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Canonical-reference provenance follows the actual sparse mutual
recursion with the proved frame, equitability and scratch contracts. -/
theorem canonPolicy (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel : Nat) :
    Generic.SoundPolicy (.ofGraph G.graph) (n + 2) tcLevel (canonContract G) where
  node_zero := fun _ level _ st hin => ⟨FrameOut.refl hin.2, CanonOut.refl level st⟩
  node_step := by
    intro fuel next hnext first level numcells st hin
    have hr : (reachContract G).sweepValid fuel (n + 1) next :=
      fun first level numcells tc tv1 cursor cell index st hin =>
        (hnext first level numcells tc tv1 cursor cell index st hin).1
    exact ⟨reach_node G hn tcLevel hr first level numcells st hin.1 hin.2,
      canon_node G hn tcLevel hnext first level numcells st hin.1 hin.2⟩
  sweep_none := by
    intro fuel cfuel first level numcells tc tv1 cell index st hin
    exact ⟨hin.2.1.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hin.2.1.scratch.toBounded,
      CanonOut.refl level st⟩
  sweep_zero := by
    intro fuel first level numcells tc tv1 tv cell index st hin
    exact ⟨hin.2.1.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hin.2.1.scratch.toBounded,
      CanonOut.refl level st⟩
  sweep_step := by
    intro fuel cfuel descend next hd hnext first level numcells tc tv1 tv cell index st hin
    have hd' : (reachContract G).nodeValid fuel descend :=
      fun first level numcells st hin => (hd first level numcells st hin).1
    have hn' : (reachContract G).sweepValid fuel cfuel next :=
      fun first level numcells tc tv1 cursor cell index st hin =>
        (hnext first level numcells tc tv1 cursor cell index st hin).1
    exact ⟨reach_sweep G hn hd' hn' first level numcells tc tv1 tv index cell st
        hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl),
      canon_sweep G hn hd hnext first level numcells tc tv1 tv index cell st
        hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl)⟩

/-- Every native node couples its stored canonical label to the actual
ancestor counter, including truncated calls and returns past the caller. -/
theorem node_canon (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (first : Bool) (tcLevel fuel level numcells : Nat) (st : State n)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st) :
    CanonOut level st (Generic.node first (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 :=
  (Generic.node_sound (canonPolicy G hn tcLevel) first fuel level numcells st ⟨hl, h⟩).2

/-- Every native sibling sweep retains or installs its canonical label
within the current cells and maintains the corresponding ancestor bounds. -/
theorem sweep_canon (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (first : Bool) (tcLevel fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : State n) (hl : 1 ≤ level)
    (h : Ready G level numcells st) (ht : Generic.Target State.frame level tc cell st)
    (hv : ∀ v, cursor = some v → cell.mem v = true) :
    CanonOut level st (Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel
      level numcells tc tv1 cursor cell index st).2.2 :=
  (Generic.sweep_sound (canonPolicy G hn tcLevel) first fuel cfuel level numcells tc tv1 cursor cell index st
    ⟨hl, h, ht, hv⟩).2

end Hex.GraphIso.Nauty.Sparse
