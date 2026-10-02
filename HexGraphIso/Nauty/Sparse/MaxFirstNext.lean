/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstPairs
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxRecover
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.MaxTrace
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.MaxGuideReturn
import all HexGraphIso.Nauty.Sparse.MaxGuideFirst
import all HexGraphIso.Nauty.Sparse.MaxCosetState
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The actual first child's covered result establishes the complete
later-sibling context. Saved traces, references and pruning pairs come
from its executed first descent; only subtree coverage is inductive. -/
theorem FirstInput.recovered {G : GraphIso.Sparse.Colored n k} {tcLevel fuel tv last : Nat}
    {f : Frame n} {parents : Parents n} {leaf : State n} {bs fs : List Nat} {smaller : VSet n}
    (h : FirstInput G tcLevel f parents)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.nextElem none = some tv)
    (path : let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel ch.level ch.numcells ch.entry last leaf)
    (hr : let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      ReturnCodes G.graph ch.codes bs fs
        (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2)
    (resume : let p := f.firstParent G.graph tcLevel [] tv
      Resumed G tcLevel p bs fs (p.firstBack G.graph tcLevel fuel) parents)
    (hd : let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      Covers (ch.key G.graph tcLevel) (State.best G.graph
        (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2))
    (hsub : ∀ v, smaller.mem v = true →
      (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.mem v = true)
    (hc : let l : Loop n := ⟨f, true⟩
      let p := f.firstParent G.graph tcLevel [] tv
      (l.cell G.graph tcLevel).Cover G.graph tcLevel (Remaining (smaller.nextElem (some tv)) smaller)
        (State.key G.graph bs (p.firstBack G.graph tcLevel fuel))) :
    let p := f.firstParent G.graph tcLevel [] tv
    SweepInput G tcLevel ⟨f, true⟩ bs fs (smaller.nextElem (some tv)) smaller
      (p.firstBack G.graph tcLevel fuel) parents := by
  let l : Loop n := ⟨f, true⟩
  let p := f.firstParent G.graph tcLevel [] tv
  let ch := p.child G.graph tcLevel
  let raw := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  let left := (policy (n := n)).leaveChild tv (afterChildFirst f.level tv raw)
  let back := p.firstBack G.graph tcLevel fuel
  have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
  have hm := VSet.nextElem_mem htv
  have hp : p.Valid G tcLevel := h.entry.frame.first_parent h.entry.shape hi hm []
  have hch : FirstInput G tcLevel ch (parents.push p) := h.child hi htv
  have hselected := l.selected (tcLevel := tcLevel) h.entry.frame hi (by intro he; cases he)
  have hscope : Scope G tcLevel f [] p.state parents := h.scope.change
    (by intro key he; cases he) (f.firstParent_boundary G.graph tcLevel [] tv)
  have hframe := hp.returned_frame (fuel := fuel) true
  have htrace := Traces.first_node hch.scope hch.entry.frame path hch.entry.work hch.empty
  have hrest := htrace.recovered hscope hp true
  have hcounter := p.firstBack_counters path
  have hnext := resume.next p.cell (fun _ hv => hv) tv hm
  have href := f.firstParent_refs G.graph tcLevel [] tv
  have hguid : p.Guided G.graph tcLevel :=
    f.firstParent_guided (by rw [h.first]; exact h.entry.frame.positive)
      (by rw [h.canon]; exact h.entry.frame.positive) [] tv
  have hcap : back.wsCap = f.entry.wsCap := by
    have he : back.wsCap = raw.wsCap :=
      (capacityPolicy (.ofGraph G.graph) (n + 2) tcLevel raw.wsCap).recover f.level left rfl
    rw [he, node_capacity]
    change p.state.wsCap = f.entry.wsCap
    exact l.preserve (capacityPolicy (.ofGraph G.graph) (n + 2) tcLevel f.entry.wsCap) rfl
  have horbits : OrbitTrace G back :=
    (orbitPolicy G (n + 2) tcLevel).recover f.level left
      ((orbitPolicy G (n + 2) tcLevel).leave tv (afterChildFirst f.level tv raw)
        ((orbitPolicy G (n + 2) tcLevel).afterChild f.level tv raw
          (node_orbitTrace G true (n + 2) tcLevel fuel ch.level ch.numcells ch.entry hch.orbits)))
  refine ⟨h.entry.frame, hi, hselected.1, resume.codes, h.pairs_back hi htv path resume,
    resume.machine, (l.prepared h.entry.frame).2.trans hframe.2,
    (hp.target.of_out hframe.2.effect).subset hsub, ?_, fun _ hv => VSet.nextElem_mem hv,
    hp.choice.grow resume.grows, hnext.small, resume.scope,
    (h.guides.first_prepare [] tv).first_back hscope hp, Cosets.first_back hscope path,
    h.ranked, hrest.pop hscope, horbits, ?_, ?_, ?_, fun _ => hcounter.1,
    (by intro he; cases he), ?_, resume.recorded, resume.route, hc, ?_⟩
  · intro v hv
    rw [← hselected.2]
    exact hsub v hv
  · intro _
    have hs : (parents.push p) p.node.level = some p := by simp only [Parents.push, ↓reduceIte]
    exact (hrest p.node.level p hs rfl).rebase hp.ready hframe.1 hn h.entry.frame.positive
  · intro v
    have hh := hguid.first_back (cell := smaller) (tv := v) hp
      (by rw [href.2.2.2, h.canon]; exact Nat.zero_le _) path resume.grows hr hd
    simpa only [p, l, Parent.next, Frame.firstParent, Loop.parent, Loop.prepare,
      Generic.prepareFirst, policy, Generic.Policy.visit, Generic.Policy.recordFirst,
      Generic.Policy.chooseTarget, ite_true] using hh
  · rw [hcounter.1, hcounter.2]
    exact ⟨h.entry.frame.positive, Nat.le_refl _, Nat.le_refl _⟩
  · change 0 < back.wsCap
    rw [hcap]
    exact h.capacity
  · exact Or.inl (recover_nonpos ((hr.afterChild f.level tv).leave tv).nonpos (n + 2) f.level)

end Hex.GraphIso.Nauty.Sparse.Max
