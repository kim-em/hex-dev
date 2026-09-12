/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReadyPerm
public import HexGraphIso.Nauty.Sparse.Preparation
import all HexGraphIso.Nauty.Policy.Recovery
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A frozen equitable witness represents the current production partition
and count, with its saved-target descent modulo within-cell label order.
Its active set belongs to the witness; child calls install their own splitter. -/
def DescentAt (G : Hex.SparseGraph n) (store : Array Int) (base : Nat) (root : RefineSt n)
    (level numcells : Nat) (st : State n) : Prop :=
  ∃ current, RefineSt.Ready G level current ∧ FollowsPerm G store base root level current ∧
    current.lab = st.lab ∧ current.ptn = st.ptn ∧ current.numcells = numcells

namespace DescentAt

variable {G : Hex.SparseGraph n} {store : Array Int} {base level numcells : Nat}
  {root : RefineSt n} {st out : State n}

theorem congr (h : DescentAt G store base root level numcells st)
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn) :
    DescentAt G store base root level numcells out := by
  obtain ⟨current, hr, hh, hcl, hcp, hcount⟩ := h
  exact ⟨current, hr, hh, hcl.trans hl.symm, hcp.trans hp.symm, hcount⟩

/-- Restoring a parent retains its descent while adopting the returned
label order, preserving the witness's complete refinement certificate. -/
theorem reorder (h : DescentAt G store base root level numcells st)
    (hl : out.lab.size = st.lab.size) (hp : out.ptn = st.ptn)
    (hc : cellsPerm st.ptn level out.lab st.lab) : DescentAt G store base root level numcells out := by
  obtain ⟨current, hr, hh, hcl, hcp, hcount⟩ := h
  have hsize : out.lab.size = current.lab.size := by rw [hcl]; exact hl
  have hcells : cellsPerm current.ptn level out.lab current.lab := by rw [hcl, hcp]; exact hc
  exact ⟨{ current with lab := out.lab }, hr.setLab out.lab hsize hcells,
    hh.setLab out.lab hcells, rfl, hcp.trans hp.symm, hcount⟩

/-- Every native individualization followed by its actual cached visit
extends the current saved-target descent. -/
theorem child (h : DescentAt G store base root level numcells st)
    (hr : RefineSt.Ready G base root) (first : Bool) {tc len o : Nat}
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
    (htc : store[level]! = Int.ofNat tc) (hs : Scratch.Bounded n st.canong.scratch) :
    let next := (policy (n := n)).child first level tc st.lab[tc + o]! st
    let r := visit (.ofGraph G) (level + 1) (numcells + 1) next
    DescentAt G store base root (level + 1) r.1 r.2.2 := by
  obtain ⟨current, hready, hh, hl, hp, hcount⟩ := h
  let next := (policy (n := n)).child first level tc st.lab[tc + o]! st
  have hscratch : Scratch.Bounded n next.canong.scratch :=
    (child_valid first level tc st.lab[tc + o]! st hs).toBounded
  have hcell : IsCell current.ptn level tc len := by rw [hp]; exact hc
  have hreadyChild := hready.child hcell hb hn ho next.canong.scratch hscratch
  have hfollow := hh.child hr hready hcell hb hn ho htc next.canong.scratch hscratch
  have he : State.refined (.ofGraph G) (level + 1) (numcells + 1) next =
      current.child (.ofGraph G) level tc current.lab[tc + o]! next.canong.scratch := by
    unfold State.refined RefineSt.child
    rw [hl, hp, hcount]
    cases first <;> rfl
  let r := State.refined (.ofGraph G) (level + 1) (numcells + 1) next
  refine ⟨r, ?_, ?_, rfl, rfl, rfl⟩
  · rw [← he] at hreadyChild
    exact hreadyChild
  · rw [← he] at hfollow
    exact hfollow

end DescentAt

/-- The established native frame effect restores the parent history
through the literal recovery and cache invalidation operation. -/
theorem DescentAt.recover {G : GraphIso.Sparse.Colored n k} {store : Array Int}
    {base level numcells : Nat} {root : RefineSt n} {st out : State n}
    (h : DescentAt G.graph store base root level numcells st)
    (hok : SearchOk G.toDense level numcells st.frame) (hout : FrameOut G level level st out) :
    DescentAt G.graph store base root level numcells ((policy (n := n)).recover (n + 2) level out) := by
  have hp := recover_ptn_eq hok hout.effect
  rw [← State.recover_frame] at hp
  have hl : ((policy (n := n)).recover (n + 2) level out).lab = out.lab := by
    change (recoverLevels level (recoverPtn (n + 2) level out)).lab = out.lab
    rw [recover_eq, recover_lab]
  apply h.reorder
  · rw [hl]
    exact hout.effect.labSize
  · exact hp
  · rw [hl]
    exact cellsPerm_symm hout.effect.perm

end Hex.GraphIso.Nauty.Sparse
