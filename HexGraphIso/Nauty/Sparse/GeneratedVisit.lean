/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.GeneratedReceipt
public import HexGraphIso.Nauty.Sparse.ReferenceComplete
import all HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxTrace
import all HexGraphIso.Nauty.Sparse.Coset
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generated.Cover
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A visited first-path sibling advances generated coverage of the
guide's true stabilizer orbit. Matching reference completion is proved
for the actual cached child; every carrier comes from its emitted trace. -/
theorem SweepInput.generated_visit {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel boundary tv : Nat} {l : Loop n} {bs fs : List Nat}
    {cell : VSet n} {st out : State n} {parents : Parents n}
    {targets : List Nat} {key : Key n} {previous : Option Nat} {short : Bool}
    {gs : List (Perm n)} {base : List (Fin n)} {guide : Fin n}
    (h : SweepInput G tcLevel l bs fs (some tv) cell st parents)
    (hf : l.first = true) (hbudget : n ≤ l.node.level + fuel)
    (hm : Generation.Matches G.graph (l.node.level + 1) st targets key)
    (heq : st.eqlevFirst = l.node.level) (hsame : boundary ≤ st.allsamelevel) :
    let c := l.cell G.graph tcLevel
    let R := State.refined (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry
    (∀ v : Fin n, Aut.Orbit G.toDense base guide v → ∀ o, o < c.len →
      R.lab[c.tc + o]! = v.val →
      Generation.ChildPath G.graph tcLevel boundary l.node.level R c.tc targets key o) →
    (∀ gamma, CellStab R.ptn l.node.level R.lab gamma → ∀ b ∈ base, gamma[b.val]! = b.val) →
    cell.nextElem previous = some tv →
    Nauty.Generation.CanonPast l.node.level c.tc previous st →
    Nauty.Generation.Cover G.toDense gs base guide cell previous →
    st.firstlab[c.tc]! = guide.val →
    Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (l.node.level + 1) (c.numcells + 1)
      ((policy (n := n)).child l.first l.node.level c.tc tv st) = (.unwind l.node.level short, out) →
    Generation.Realizes G gs out.genTrace.toList →
    Nauty.Generation.Cover G.toDense gs base guide cell (some tv) := by
  intro c R hmove hfixFrame hnext hcanon hcover hfirst hcall htrace
  classical
  have hv := h.member tv rfl
  let v : Fin n := ⟨tv, VSet.mem_lt hv⟩
  by_cases horbit : Aut.Orbit G.toDense base guide v
  · have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
    let p := l.parent G.graph tcLevel st bs cell tv
    let ch := p.child G.graph tcLevel
    have hi := h.child rfl
    obtain ⟨o, ho, hat⟩ := mem_segN_iff.mp (mem_windowSet.mp (h.subset tv hv)).2
    have hat' : R.lab[c.tc + o]! = tv := hat
    have href := h.reference_child ho hat (hmove v horbit o ho hat')
    have hmatch : Generation.Matches G.graph ch.level ch.entry targets key := hm.congr (by
      dsimp only [ch, p, Parent.child, Loop.parent]
      rw [hf]
      rfl)
    have hr := reference_complete G tcLevel fuel ch bs fs (parents.push p) boundary targets key
      hi (by change n < l.node.level + 1 + fuel; omega) href hmatch
      (by
        dsimp only [ch, p, Parent.child, Loop.parent]
        rw [hf]
        change st.eqlevFirst = l.node.level + 1 - 1
        omega)
      (by
        dsimp only [ch, p, Parent.child, Loop.parent]
        rw [hf]
        exact hsame)
      l.node.level short (congrArg Prod.fst hcall)
    change RefReturn (Graph.context G.graph) l.node.level
      (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (l.node.level + 1) (c.numcells + 1)
        ((policy (n := n)).child l.first l.node.level c.tc tv st)).2 at hr
    rw [hcall] at hr
    have hsaved := hi.codes.saved.node hn tcLevel fuel ch.level ch.numcells hi.frame.positive hi.frame.node
    have hsound := node_trace G hn tcLevel fuel ch.level ch.numcells ch.entry hi.frame.positive hi.codes.toTraceEntry
    have horbits := node_orbitTrace G false (n + 2) tcLevel fuel ch.level ch.numcells ch.entry hi.orbits
    have hc : Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry =
        (.unwind l.node.level short, out) := hcall
    rw [hc] at hsaved hsound horbits
    have hframe := (h.self hf).freeze h.effect h.selected.ready h.codes.ready hn h.frame.positive
    have hchild := hframe.child h.selected.ready h.codes.ready hn h.frame.positive
      (Nat.le_refl _) l.first h.target hv
    have hout := hchild.node h.selected.ready hn h.frame.positive
      (by change l.node.level < l.node.level + 1; omega) hi.frame.node false tcLevel fuel
    change TraceFrame G l.node.level c.entry
      (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry).2 at hout
    rw [hc] at hout
    have hfix : ∀ gamma ∈ out.genTrace, ∀ b ∈ base, gamma[b.val]! = b.val :=
      fun gamma hg => hfixFrame gamma (hout.trace gamma hg)
    apply Generation.receipt (tv := v) hcover h.codes.ready hn h.frame.positive h.target hnext hcanon
      hcall hr hsaved horbits hsound htrace hfix
    · have hh := congrArg (fun r : Array Nat × Array Int × Array Nat => r.2.2)
        (node_reference (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry)
      rw [hc] at hh
      change out.firstlab = ch.entry.firstlab at hh
      have he : ch.entry.firstlab = st.firstlab := by
        dsimp only [ch, p, Parent.child, Loop.parent]
        rw [hf]
        rfl
      rw [he] at hh
      rw [hh]
      exact hfirst
    · have hh := node_coset (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry
      rw [hc] at hh
      dsimp only [ch, p, Parent.child, Loop.parent] at hh
      rw [hf] at hh
      exact hh
  · exact hcover.advance (tv := v) hnext (fun hv => (horbit hv).elim)

end Hex.GraphIso.Nauty.Sparse.Max
