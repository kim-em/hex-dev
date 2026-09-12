/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxGuides
public import HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The complete native off-path call retains every reference association
with its suspended ancestors, including truncated calls and nonlocal exits. -/
theorem Guides.node {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs : List Nat} {parents : Parents n}
    (h : Guides G.graph tcLevel f.entry parents) (hs : Scope G tcLevel f bs f.entry parents)
    (hf : f.Valid G) (fuel : Nat) :
    Guides G.graph tcLevel
      (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).2 parents := by
  have hn : 0 < n := by have := hf.positive; have := hf.depth; omega
  have hc := node_canon G hn false tcLevel fuel f.level f.numcells f.entry hf.positive hf.node
  exact h.change hs (Or.inl ⟨node_gca (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry,
    congrArg (fun r => r.2.2) (node_reference (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry)⟩)
    (fun ht => hc.old ht)

/-- A terminal native dispatch inherits the full call's reference
associations; its actual exit excludes any sibling continuation. -/
theorem Guides.emit {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs : List Nat} {parents : Parents n}
    (h : Guides G.graph tcLevel f.entry parents) (hs : Scope G tcLevel f bs f.entry parents)
    (hf : f.Valid G) (he : (f.emit G.graph tcLevel).1 ≠ .done) :
    Guides G.graph tcLevel (f.emit G.graph tcLevel).2 parents := by
  have hout := h.node hs hf 1
  rw [Generic.node, f.emit_step _ he] at hout
  exact hout

/-- The actual returned child and native recovery retain an older
canonical reference whenever the clamped ancestor still lies above this
parent. This covers both first and off-path child calls. -/
theorem Parent.Valid.recovered_canon {G : GraphIso.Sparse.Colored n k} {tcLevel fuel : Nat}
    {p : Parent n} (h : p.Valid G tcLevel) (first : Bool) :
    let ch := p.child G.graph tcLevel
    let raw := (Generic.node first (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
    let left := (policy (n := n)).leaveChild p.chosen
      (if first then afterChildFirst p.node.level p.chosen raw else raw)
    let out := (policy (n := n)).recover (n + 2) p.node.level left
    out.gcaCanon < p.node.level → out.gcaCanon = p.state.gcaCanon ∧ out.canonlab = p.state.canonlab := by
  intro ch raw left out ht
  have hn : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hg : out.gcaCanon = min p.node.level raw.gcaCanon := by
    change (Nauty.recover (n + 2) p.node.level left).gcaCanon = _
    rw [recover_canon]
    cases first <;> rfl
  have hr : out.canonlab = raw.canonlab := by
    change (Nauty.recover (n + 2) p.node.level left).canonlab = _
    rw [recover_ref]
    cases first <;> rfl
  have hb : raw.gcaCanon ≤ p.node.level := by omega
  have hold := child_canon_old (tcLevel := tcLevel) (fuel := fuel)
    h.ready hn h.node.positive p.first first h.target h.chosen hb
  exact ⟨(hg.trans (Nat.min_eq_right hb)).trans hold.1, hr.trans hold.2⟩

/-- Recovery after an actual off-path child retains every covered
reference belonging to an older suspended ancestor. -/
theorem Guides.back {G : GraphIso.Sparse.Colored n k} {tcLevel fuel : Nat}
    {p : Parent n} {parents : Parents n} (h : Guides G.graph tcLevel p.state parents)
    (hs : Scope G tcLevel p.node p.bs p.state parents) (hp : p.Valid G tcLevel) :
    Guides G.graph tcLevel (p.back G.graph tcLevel fuel) parents := by
  let ch := p.child G.graph tcLevel
  let raw := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  let left := (policy (n := n)).leaveChild p.chosen raw
  have hg : (p.back G.graph tcLevel fuel).gcaFirst = raw.gcaFirst :=
    (gcaPolicy (.ofGraph G.graph) (n + 2) tcLevel).recover p.node.level left
  have hf : (p.back G.graph tcLevel fuel).firstlab = raw.firstlab :=
    congrArg (fun r => r.2.2) ((referencePolicy (.ofGraph G.graph) (n + 2) tcLevel).recover p.node.level left)
  have hrg : raw.gcaFirst = p.state.gcaFirst := by
    rw [node_gca]
    dsimp only [ch, Parent.child]
    cases p.first <;> rfl
  have hrf : raw.firstlab = p.state.firstlab := by
    have he := congrArg (fun r => r.2.2)
      (node_reference (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry)
    exact he.trans (by dsimp only [ch, Parent.child]; cases p.first <;> rfl)
  exact h.change hs (Or.inl ⟨hg.trans hrg, hf.trans hrf⟩) (hp.recovered_canon false)

/-- The first child's bookkeeping points the first reference to this
parent. Its recovery still retains every older canonical association. -/
theorem Guides.first_back {G : GraphIso.Sparse.Colored n k} {tcLevel fuel : Nat}
    {p : Parent n} {parents : Parents n} (h : Guides G.graph tcLevel p.state parents)
    (hs : Scope G tcLevel p.node p.bs p.state parents) (hp : p.Valid G tcLevel) :
    Guides G.graph tcLevel (p.firstBack G.graph tcLevel fuel) parents := by
  apply h.change hs _ (hp.recovered_canon true)
  right
  let ch := p.child G.graph tcLevel
  let raw := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  let left := (policy (n := n)).leaveChild p.chosen (afterChildFirst p.node.level p.chosen raw)
  have he : (p.firstBack G.graph tcLevel fuel).gcaFirst = p.node.level :=
    (gcaPolicy (.ofGraph G.graph) (n + 2) tcLevel).recover p.node.level left
  exact Nat.le_of_eq he.symm

end Hex.GraphIso.Nauty.Sparse.Max
