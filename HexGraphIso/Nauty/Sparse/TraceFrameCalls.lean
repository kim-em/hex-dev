/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TraceFrameSweep
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Reach

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The native mutual recursion preserves reference containment and
generator stabilization at a fixed suspended ancestor. -/
theorem traceFramePolicy (G : GraphIso.Sparse.Colored n k) {base cells : Nat} {root : State n}
    (hp : Ready G base cells root) (hn : 0 < n) (hb : 1 ≤ base) (tcLevel : Nat) :
    Generic.SoundPolicy (.ofGraph G.graph) (n + 2) tcLevel (traceFrameContract G base root) where
  node_zero := fun _ _ _ _ hin => ⟨FrameOut.refl hin.2, fun _ h => h⟩
  node_step := by
    intro fuel next hnext first level numcells st hin
    have hr : (reachContract G).sweepValid fuel (n + 1) next :=
      fun first level numcells tc tv1 cursor cell index st hin =>
        (hnext first level numcells tc tv1 cursor cell index st hin).1
    exact ⟨reach_node G hn tcLevel hr first level numcells st hin.1 hin.2,
      traceFrame_node G hp hn hb tcLevel hnext first level numcells st hin.1 hin.2⟩
  sweep_none := by
    intro fuel cfuel first level numcells tc tv1 cell index st hin
    exact ⟨hin.2.1.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hin.2.1.scratch.toBounded,
      fun _ h => h⟩
  sweep_zero := by
    intro fuel first level numcells tc tv1 tv cell index st hin
    exact ⟨hin.2.1.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hin.2.1.scratch.toBounded,
      fun _ h => h⟩
  sweep_step := by
    intro fuel cfuel descend next hd hnext first level numcells tc tv1 tv cell index st hin
    have hd' : (reachContract G).nodeValid fuel descend :=
      fun first level numcells st hin => (hd first level numcells st hin).1
    have hn' : (reachContract G).sweepValid fuel cfuel next :=
      fun first level numcells tc tv1 cursor cell index st hin =>
        (hnext first level numcells tc tv1 cursor cell index st hin).1
    exact ⟨reach_sweep G hn hd' hn' first level numcells tc tv1 tv index cell st
        hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl),
      traceFrame_sweep G hp hn hb hd hnext first level numcells tc tv1 tv index cell st
        hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl)⟩

/-- Every complete or truncated descendant call preserves a frozen
ancestor's saved-reference cells and all accumulated generator stabilizers. -/
theorem TraceFrame.node {G : GraphIso.Sparse.Colored n k}
    {base cells level numcells : Nat} {root st : State n}
    (h : TraceFrame G base root st) (hp : Ready G base cells root)
    (hn : 0 < n) (hb : 1 ≤ base) (hlevel : base < level)
    (hi : NodeInv G level numcells st) (first : Bool) (tcLevel fuel : Nat) :
    TraceFrame G base root
      (Generic.node first (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 :=
  (Generic.node_sound (traceFramePolicy G hp hn hb tcLevel) first fuel level numcells st
    ⟨by omega, hi⟩).2 hlevel h

/-- Every complete sibling sweep retains the frozen ancestor invariant,
including filtered targets, orbit skips and returns past the current caller. -/
theorem TraceFrame.sweep {G : GraphIso.Sparse.Colored n k}
    {base cells level numcells : Nat} {root st : State n}
    (h : TraceFrame G base root st) (hp : Ready G base cells root)
    (hn : 0 < n) (hb : 1 ≤ base) (hlevel : base ≤ level)
    (hi : Ready G level numcells st) (first : Bool) (tcLevel fuel cfuel tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n)
    (ht : Generic.Target State.frame level tc cell st)
    (hv : ∀ v, cursor = some v → cell.mem v = true) :
    TraceFrame G base root
      (Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel
        level numcells tc tv1 cursor cell index st).2.2 :=
  (Generic.sweep_sound (traceFramePolicy G hp hn hb tcLevel) first fuel cfuel
    level numcells tc tv1 cursor cell index st ⟨by omega, hi, ht, hv⟩).2 hlevel h

end Hex.GraphIso.Nauty.Sparse
