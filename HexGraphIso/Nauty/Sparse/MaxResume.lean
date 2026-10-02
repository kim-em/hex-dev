/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxRecover
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Sparse.MaxRecover
import all HexGraphIso.Nauty.Sparse.CodeState
import all HexGraphIso.Nauty.Sparse.ReturnCodes
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The literal state after an off-path child, fixed-point cleanup and
native parent recovery. Both filters change only the target vertex set. -/
def Parent.back (G : Hex.SparseGraph n) (tcLevel fuel : Nat) (p : Parent n) : State n :=
  let ch := p.child G tcLevel
  let out := (Generic.node false (.ofGraph G) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  (policy (n := n)).recover (n + 2) p.node.level ((policy (n := n)).leaveChild p.chosen out)

/-- The native comparisons, histories and ancestor facts available to
the next sibling after receiving an off-path child. -/
structure Resumed (G : GraphIso.Sparse.Colored n k) (tcLevel : Nat) (p : Parent n)
    (ds fs : List Nat) (out : State n) (parents : Parents n) : Prop where
  machine : Comparison G.graph (p.child G.graph tcLevel).codes ds fs out
  codes : CodeReady G tcLevel p.node.level (p.node.target G.graph tcLevel).numcells out
  recorded : CheapRecorded p.node.level p.tc out
  route : RouteRecorded G.graph tcLevel p.node.level p.tc out
  scope : Scope G tcLevel p.node ds out parents
  grows : Grows (State.key G.graph p.bs p.state) (State.key G.graph ds out)
  next : ∀ cell : VSet n, (∀ v, cell.mem v = true → p.cell.mem v = true) →
    ∀ tv, cell.mem tv = true → (p.next out ds cell tv).Valid G tcLevel

/-- A complete actual child supplies the next sibling's entire native
context. The ancestor, choice and cheap-shape facts are derived from the
executed call and recovery, without assuming its maximum theorem. -/
theorem Scope.receive {G : GraphIso.Sparse.Colored n k} {tcLevel fuel : Nat}
    {p : Parent n} {fs : List Nat} {parents : Parents n}
    (h : Scope G tcLevel p.node p.bs p.state parents) (hp : p.Valid G tcLevel)
    (hi : CodeReady G tcLevel p.node.level (p.node.target G.graph tcLevel).numcells p.state)
    (hc : Comparison G.graph (p.child G.graph tcLevel).codes p.bs fs p.state)
    (hrecord : CheapRecorded p.node.level p.tc p.state)
    (hroute : RouteRecorded G.graph tcLevel p.node.level p.tc p.state)
    (hf : n ≤ p.node.level + fuel) :
    let ch := p.child G.graph tcLevel
    let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
    ∃ ds, ReturnCodes G.graph ch.codes ds fs out ∧
      Resumed G tcLevel p ds fs (p.back G.graph tcLevel fuel) parents := by
  let ch := p.child G.graph tcLevel
  let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2
  let left := (policy (n := n)).leaveChild p.chosen out
  let back := p.back G.graph tcLevel fuel
  have hn : 0 < n := by have := hp.node.positive; have := hp.node.depth; omega
  have hlen : ch.codes.length = p.node.level := by
    change (p.node.codes ++ [_]).length = p.node.level
    simp only [List.length_append, List.length_singleton, hp.node.length]
  have hlevel : ch.codes.length + 1 = ch.level := hp.child.length
  have hch := hi.child hn hp.node.positive p.first hp.target hp.chosen hrecord hroute
  have hcmp := hc.child p.first p.node.level p.tc p.chosen
  have hr := node_codes G hn tcLevel fuel ch.codes p.bs fs ch.numcells ch.entry
    (by rw [hlevel]; exact hch) (by rw [hlen]; exact hf) hcmp
  rw [hlevel] at hr
  obtain ⟨ds, hreturned, hg⟩ := hr
  have hleft : ReturnCodes G.graph ch.codes ds fs left := hreturned.leave p.chosen
  have hback := hleft.recover (n + 2)
  rw [hlen] at hback
  have hbackCodes := hi.child_return hn hp.node.positive p.first fuel hp.target hp.chosen hrecord hroute
  have hframe := node_frame G hn false tcLevel fuel ch.level ch.numcells ch.entry
    (by change 1 ≤ p.node.level + 1; omega) hch.node
  have hparent := hp.ready.child_frame hn hp.node.positive p.first hp.target hp.chosen
    (by simpa only [ch, Parent.child, Nat.add_sub_cancel] using hframe)
  have hrecovered := hp.ready.recover hn hp.node.positive (hparent.leave p.chosen)
  have hkey : State.key G.graph p.bs ch.entry = State.key G.graph p.bs p.state := by
    dsimp only [ch, Parent.child]
    cases p.first <;> rfl
  have hbackKey : State.key G.graph ds back = State.key G.graph ds out :=
    recover_key G.graph ds (n + 2) p.node.level left
  have hgrows : Grows (State.key G.graph p.bs p.state) (State.key G.graph ds back) := by
    rw [hbackKey, ← hkey]
    exact hg
  have hboundary := p.child_boundary G.graph tcLevel fuel
  refine ⟨ds, hreturned, hback, hbackCodes.1, hbackCodes.2.1, hbackCodes.2.2,
    h.change hgrows (hboundary.imp id (fun h => Nat.le_of_lt h)), hgrows, ?_⟩
  intro cell hsub tv hv
  exact hp.next hrecovered.1 hrecovered.2 hgrows hboundary
    ((hp.target.of_out hrecovered.2.effect).subset hsub) hv

end Hex.GraphIso.Nauty.Sparse.Max
