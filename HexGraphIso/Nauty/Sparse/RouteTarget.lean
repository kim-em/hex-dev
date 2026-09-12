/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RouteAlignment
public import HexGraphIso.Nauty.Sparse.AlignedTarget
public import HexGraphIso.Nauty.Sparse.StoreNode
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Recovery
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- While first-code agreement is live, a target used by the production
sweep is either the native unhinted target or the saved first target. -/
def RouteRecorded (G : Hex.SparseGraph n) (tcLevel level tc : Nat) (st : State n) : Prop :=
  st.eqlevFirst = level →
    tc = targetcell (.ofGraph G) st.lab st.ptn level tcLevel (-1) ∨
      st.firsttc[level]! = Int.ofNat tc

/-- The hinted branch explicitly drops agreement when its returned target
differs from the saved slot. Retained agreement therefore identifies the slot. -/
theorem chooseTarget_hint_eq {g : Graph n} {tcLevel level numcells : Nat} {st : State n}
    (hl : 0 < level) (hnc : numcells < n) (he : st.eqlevFirst = level)
    (hneg : st.compCanon < 0)
    (hkeep : (chooseTarget false g tcLevel level numcells st).2.2.2.eqlevFirst = level) :
    (chooseTarget false g tcLevel level numcells st).1 = st.firsttc[level]! := by
  let pos := (maketargetCached g st.lab st.ptn level tcLevel st.firsttc[level]! st.canong.scratch).1
  by_cases hp : Int.ofNat pos = st.firsttc[level]!
  · rw [chooseTarget_pos hnc he]
    simpa only [hneg, ite_true] using hp
  · have hx : (chooseTarget false g tcLevel level numcells st).2.2.2.eqlevFirst = level - 1 := by
      simp only [pos, Int.ofNat_eq_natCast] at hp
      simp [chooseTarget, hnc, he, hneg, hp]
    omega

/-- The literal cached selector supplies the guided target condition.
All cache and partition premises concern the actual prepared state. -/
theorem route_recorded {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat} {st : State n}
    (hn : 0 < n) (hl : 0 < level) (h : Ready G level numcells st)
    (hb : st.eqlevFirst ≤ level) (hnc : numcells < n) :
    let r := chooseTarget false (.ofGraph G.graph) tcLevel level numcells st
    RouteRecorded G.graph tcLevel level r.1.toNat r.2.2.2 := by
  intro r hkeep
  have he : st.eqlevFirst = level := by
    have hm := chooseTarget_le (.ofGraph G.graph) tcLevel level numcells st
    change r.2.2.2.eqlevFirst ≤ st.eqlevFirst at hm
    omega
  obtain ⟨hlab, hptn, _, _⟩ := chooseTarget_frame false (.ofGraph G.graph) tcLevel level numcells st
  have htc := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
    (chooseTarget_reference (.ofGraph G.graph) tcLevel level numcells st)
  change r.2.2.2.firsttc = st.firsttc at htc
  change r.1.toNat = targetcell (.ofGraph G.graph) r.2.2.2.lab r.2.2.2.ptn level tcLevel (-1) ∨
    r.2.2.2.firsttc[level]! = Int.ofNat r.1.toNat
  rw [hlab, hptn, htc]
  by_cases hneg : st.compCanon < 0
  · exact Or.inr ((chooseTarget_hint_eq hl hnc he hneg hkeep).symm.trans (chooseTarget_cast hnc he).symm)
  · left
    obtain ⟨l, hlab⟩ := h.parse hn
    have hs := h.partition hn (by omega)
    have hend : st.ptn[n - 1]! ≤ level := by simpa only [hs.ptnSize] using hs.ptnEnd
    have hc : bcount st.ptn level n < n := by
      change bcount st.frame.ptn level n < n
      rw [← h.ok.count]
      exact hnc
    have ht := maketargetCached_eq G.graph st.lab st.ptn level tcLevel (-1) st.canong.scratch
      l hlab hs.ptnSize hend h.scratch (Target.nonempty hs.ptnSize hend hc)
    change (chooseTarget false (.ofGraph G.graph) tcLevel level numcells st).1.toNat = _
    rw [chooseTarget_pos hnc he, ite_eq_right hneg, (Prod.mk.inj ht).1]
    rfl

theorem RouteRecorded.congr {G : Hex.SparseGraph n} {tcLevel level tc : Nat} {st out : State n}
    (h : RouteRecorded G tcLevel level tc st) (he : out.eqlevFirst = st.eqlevFirst)
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn) (ht : out.firsttc = st.firsttc) :
    RouteRecorded G tcLevel level tc out := by
  unfold RouteRecorded at *
  rwa [he, hl, hp, ht]

theorem RouteRecorded.cheap {G : Hex.SparseGraph n} {tcLevel level tc : Nat} {st : State n}
    (h : RouteRecorded G tcLevel level tc st) (first : Bool) :
    RouteRecorded G tcLevel level tc (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h.congr rfl rfl rfl rfl

/-- Returning from a child and restoring its parent's partition preserves
the native unhinted target even when labels inside cells have changed order. -/
theorem Ready.target_recover {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat}
    {st out : State n} (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hx : FrameOut G level level st out) :
    let r := (policy (n := n)).recover (n + 2) level out
    targetcell (.ofGraph G.graph) r.lab r.ptn level tcLevel (-1) =
      targetcell (.ofGraph G.graph) st.lab st.ptn level tcLevel (-1) := by
  let r := (policy (n := n)).recover (n + 2) level out
  obtain ⟨hr, he⟩ := h.recover hn hl hx
  have hp := recover_ptn_eq h.ok hx.effect
  rw [← State.recover_frame] at hp
  change r.ptn = st.ptn at hp
  have hs := h.partition hn hl
  have hend : st.ptn[n - 1]! ≤ level := by simpa only [hs.ptnSize] using hs.ptnEnd
  have hlabel := isPerm_of_cellsReach h.ok.labSize hn h.ok.reach
  have hrlabel := isPerm_of_cellsReach hr.ok.labSize hn hr.ok.reach
  change st.lab.toList.Perm (List.range n) at hlabel
  change r.lab.toList.Perm (List.range n) at hrlabel
  obtain ⟨a, ha⟩ := Index.exists_valid hrlabel hs.ptnSize hend
  obtain ⟨b, hb⟩ := Index.exists_valid hlabel hs.ptnSize hend
  have heq : Equitable (Graph.context G.graph) level r.lab st.ptn := by
    rw [← hp]
    exact hr.equitable
  change targetcell (.ofGraph G.graph) r.lab r.ptn level tcLevel (-1) = _
  rw [hp]
  exact targetcell_perm G.graph r.lab st.lab st.ptn level tcLevel (-1) a b hrlabel hlabel
    hs.ptnSize hend ha hb heq (cellsPerm_symm he.effect.perm)

end Hex.GraphIso.Nauty.Sparse
