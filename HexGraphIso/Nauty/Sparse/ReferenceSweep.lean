/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReferenceReturn
public import HexGraphIso.Nauty.Sparse.CanonSource
public import HexGraphIso.Nauty.Generation.Canon
import all HexGraphIso.Nauty.Generation.Canon
import all HexGraphIso.Nauty.Policy.Canon.Frame
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Ready

variable {G : GraphIso.Sparse.Colored n k} {tcLevel fuel level numcells tc tv : Nat}
  {st : State n} {cell : VSet n}

/-- The returned native child retains its individualized vertex at the
selected position before parent partition recovery. -/
theorem child_chosen (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first childFirst : Bool) (ht : Generic.Target State.frame level tc cell st)
    (hv : cell.mem tv = true) :
    (Generic.node childFirst (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      ((policy (n := n)).child first level tc tv st)).2.lab[tc]! = tv := by
  have hc := h.child hn hl first ht hv
  have hout := node_frame G hn childFirst tcLevel fuel (level + 1) (numcells + 1) _ (by omega) hc
  exact (h.child_store hn hl first ht hv ⟨hout.effect.labSize, hout.effect.perm⟩).2.2

/-- A canonical return to the receiving parent retains its earlier
canonical source, which lies strictly before the current live cursor. -/
theorem canon_earlier (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first childFirst : Bool) (ht : Generic.Target State.frame level tc cell st)
    {previous : Option Nat} (hp : Nauty.Generation.CanonPast level tc previous st)
    (hnext : cell.nextElem previous = some tv) :
    let out := (Generic.node childFirst (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    out.gcaCanon = level → out.canonlab[tc]! < tv := by
  intro out he
  have hold := child_canon_old (tcLevel := tcLevel) (fuel := fuel) h hn hl first childFirst ht
    (VSet.nextElem_mem hnext) (Nat.le_of_eq he)
  rw [hold.2]
  exact hp.before hnext (hold.1.symm.trans he)

/-- Receiving either kind of native child keeps every local canonical
source behind the next cursor, whether the child retained or installed
the reference. This includes cache invalidation during recovery. -/
theorem canon_past (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first childFirst : Bool) (ht : Generic.Target State.frame level tc cell st)
    {previous : Option Nat} (hp : Nauty.Generation.CanonPast level tc previous st)
    (hnext : cell.nextElem previous = some tv) :
    let raw := (Generic.node childFirst (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    let middle := if childFirst then afterChildFirst level tv raw else raw
    let left := (policy (n := n)).leaveChild tv middle
    Nauty.Generation.CanonPast level tc (some tv) ((policy (n := n)).recover (n + 2) level left) := by
  intro raw middle left
  have hr := child_canon (tcLevel := tcLevel) (fuel := fuel) h hn hl first childFirst ht
    (VSet.nextElem_mem hnext)
  have hg : left.gcaCanon = raw.gcaCanon := by cases childFirst <;> rfl
  have hc : left.canonlab = raw.canonlab := by cases childFirst <;> rfl
  constructor
  · change (Nauty.recover (n + 2) level left).gcaCanon ≤ level
    rw [recover_canon]
    exact Nat.min_le_left _ _
  · intro he
    change (Nauty.recover (n + 2) level left).gcaCanon = level at he
    rw [recover_canon] at he
    change min level left.gcaCanon = level at he
    rw [hg] at he
    change ¬ tv < (Nauty.recover (n + 2) level left).canonlab[tc]!
    rw [recover_ref, hc]
    rcases hr with hold | hnew
    · change raw.gcaCanon ≤ st.gcaCanon ∧ raw.canonlab = st.canonlab at hold
      have hlevel : st.gcaCanon = level := by have := hp.cap; omega
      have hh := (hp.advance (nextElem_after hnext)).source hlevel
      change ¬ tv < st.canonlab[tc]! at hh
      rw [hold.2]
      exact hh
    · rw [hnew.2.2]
      omega

end Hex.GraphIso.Nauty.Sparse.Ready
