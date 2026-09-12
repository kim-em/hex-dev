/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.GuidedPerm
public import HexGraphIso.Nauty.Sparse.DescentAt
import all HexGraphIso.Nauty.Policy.Recovery
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A frozen equitable witness connects an entire guided code history
to the production labels, partition and count. Its active set is retained
with the witness; actual child calls install their own splitter. -/
def RouteAt (G : Hex.SparseGraph n) (tcLevel : Nat) (store : Array Int) (base : Nat) (root : RefineSt n)
    (level numcells : Nat) (st : State n) : Prop :=
  ∃ current, RefineSt.Ready G level current ∧ GuidedPerm G tcLevel store base root level current ∧
    current.lab = st.lab ∧ current.ptn = st.ptn ∧ current.numcells = numcells

namespace RouteAt

variable {G : Hex.SparseGraph n} {tcLevel : Nat} {store : Array Int} {base level numcells : Nat}
  {root : RefineSt n} {st out : State n}

theorem congr (h : RouteAt G tcLevel store base root level numcells st)
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn) :
    RouteAt G tcLevel store base root level numcells out := by
  obtain ⟨current, hr, hh, hcl, hcp, hcount⟩ := h
  exact ⟨current, hr, hh, hcl.trans hl.symm, hcp.trans hp.symm, hcount⟩

/-- Adopting returned label order preserves both the guided history and
the equitable certificate of the restored parent. -/
theorem reorder (h : RouteAt G tcLevel store base root level numcells st)
    (hl : out.lab.size = st.lab.size) (hp : out.ptn = st.ptn)
    (hc : cellsPerm st.ptn level out.lab st.lab) : RouteAt G tcLevel store base root level numcells out := by
  obtain ⟨current, hr, hh, hcl, hcp, hcount⟩ := h
  have hsize : out.lab.size = current.lab.size := by rw [hcl]; exact hl
  have hcells : cellsPerm current.ptn level out.lab current.lab := by rw [hcl, hcp]; exact hc
  exact ⟨{ current with lab := out.lab }, hr.setLab out.lab hsize hcells,
    hh.setLab out.lab hcells, rfl, hcp.trans hp.symm, hcount⟩

/-- Actual native individualization and the cached child visit extend
the guided code history using either an unhinted or stored target. -/
theorem child (h : RouteAt G tcLevel store base root level numcells st)
    (hr : RefineSt.Ready G base root) (first : Bool) {tc len o : Nat}
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
    (hchoice : tc = targetcell (.ofGraph G) st.lab st.ptn level tcLevel (-1) ∨
      store[level]! = Int.ofNat tc) (hs : Scratch.Bounded n st.canong.scratch) :
    let next := (policy (n := n)).child first level tc st.lab[tc + o]! st
    let r := visit (.ofGraph G) (level + 1) (numcells + 1) next
    RouteAt G tcLevel store base root (level + 1) r.1 r.2.2 := by
  obtain ⟨current, hready, hh, hl, hp, hcount⟩ := h
  let next := (policy (n := n)).child first level tc st.lab[tc + o]! st
  have hscratch : Scratch.Bounded n next.canong.scratch :=
    (child_valid first level tc st.lab[tc + o]! st hs).toBounded
  have hcell : IsCell current.ptn level tc len := by rw [hp]; exact hc
  have hchoice' : tc = targetcell (.ofGraph G) current.lab current.ptn level tcLevel (-1) ∨
      store[level]! = Int.ofNat tc := by rw [hl, hp]; exact hchoice
  have hreadyChild := hready.child hcell hb hn ho next.canong.scratch hscratch
  have hfollow := hh.child hr hready hcell hb hn ho hchoice' next.canong.scratch hscratch
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

/-- The actual guided endpoint and a native automorphism identify the
saved first sentinel and graph at a discrete production node. -/
theorem first_leaf (h : RouteAt G tcLevel st.firsttc base root level n st)
    (href : FirstRef G tcLevel base root st) (hr : RefineSt.Ready G base root)
    {f l : Label n} (hf : Label.ofArray? n st.firstlab = some f)
    (hl : Label.ofArray? n st.lab = some l) (p : Perm n)
    (hiso : ∀ i j, G.adj (p.get i) (p.get j) = G.adj i j)
    (hlabels : st.firstlab.map (renamingOf p).toFun = st.lab) :
    st.firstcode[level + 1]! = codeSentinel ∧ G.relabel l.perm = G.relabel f.perm := by
  obtain ⟨current, hc, hg, hcl, hcp, hcount⟩ := h
  have hd : discreteAt current.ptn level n = true := by
    apply (discreteAt_iff_bcount hc.spec.node.ptnSize.symm hc.spec.node.ptnEnd).mpr
    rw [← hc.spec.count, hcount]
  obtain ⟨_, hsent, hgraph⟩ := href.guided_follows hr hc hg hd hf
    (by rw [hcl]; exact hl) p hiso (by rw [hcl]; exact hlabels)
  exact ⟨hsent, hgraph⟩

end RouteAt

/-- Native partition recovery restores the guided history using the
independently proved effect of the actual child search. -/
theorem RouteAt.recover {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {store : Array Int}
    {base level numcells : Nat} {root : RefineSt n} {st out : State n}
    (h : RouteAt G.graph tcLevel store base root level numcells st)
    (hok : SearchOk G.toDense level numcells st.frame) (hout : FrameOut G level level st out) :
    RouteAt G.graph tcLevel store base root level numcells ((policy (n := n)).recover (n + 2) level out) := by
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
