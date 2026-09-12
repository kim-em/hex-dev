/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstHistory
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.History
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A frozen native ancestor's selected descent to the saved first leaf,
including every literal cached call and its stored target and code slots. -/
structure FirstRef (G : Hex.SparseGraph n) (tcLevel base : Nat) (root : RefineSt n) (st : State n) where
  last : Nat
  leaf : RefineSt n
  path : List (Nat × Nat)
  codes : List Nat
  trace : CodePath G base root path last leaf codes
  selects : trace.Selects tcLevel
  targets : Targets st.firsttc base (path.map Prod.fst)
  lab : leaf.lab = st.firstlab
  discrete : discreteAt leaf.ptn last n = true
  sentinel : st.firstcode[last + 1]! = codeSentinel
  stored : StoredCodes st.firstcode base codes

/-- Updating unrelated bookkeeping retains the complete native history. -/
def FirstRef.congr {G : Hex.SparseGraph n} {tcLevel base : Nat} {root : RefineSt n}
    {st out : State n} (h : FirstRef G tcLevel base root st)
    (he : out.reference = st.reference) : FirstRef G tcLevel base root out := by
  have hc := congrArg (fun x : Array Nat × Array Int × Array Nat => x.1) he
  have ht := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) he
  have hl := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.2) he
  change out.firstcode = st.firstcode at hc
  change out.firsttc = st.firsttc at ht
  change out.firstlab = st.firstlab at hl
  exact ⟨h.last, h.leaf, h.path, h.codes, h.trace, h.selects,
    by rw [ht]; exact h.targets, h.lab.trans hl.symm, h.discrete,
    by rw [hc]; exact h.sentinel, by rw [hc]; exact h.stored⟩

def FirstRef.node {G : Hex.SparseGraph n} {inf tcLevel fuel base level numcells : Nat}
    {root : RefineSt n} {st : State n} (h : FirstRef G tcLevel base root st) :
    FirstRef G tcLevel base root (Generic.node false (.ofGraph G) inf tcLevel fuel level numcells st).2 :=
  h.congr (node_reference (.ofGraph G) inf tcLevel fuel level numcells st)

def FirstRef.sweep {G : Hex.SparseGraph n} {first : Bool}
    {inf tcLevel fuel cfuel base level numcells tc tv1 index : Nat}
    {cursor : Option Nat} {cell : VSet n} {root : RefineSt n} {st : State n}
    (h : FirstRef G tcLevel base root st) (hpast : Generic.Past first tv1 cursor) :
    FirstRef G tcLevel base root
      (Generic.sweep first (.ofGraph G) inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 :=
  h.congr (sweep_reference first (.ofGraph G) inf tcLevel fuel cfuel level numcells tc tv1 index cursor cell st hpast)

/-- Completing the actual first-path call supplies a frozen native
reference, retained after every later sibling and nonlocal return. -/
theorem firstRef_of_path {G : GraphIso.Sparse.Colored n k}
    {inf tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (hn : 0 < n) (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel level numcells st last leaf)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st)
    (htsize : n < st.firsttc.size) (hcsize : n + 1 < st.firstcode.size) :
    ∃ href : FirstRef G.graph tcLevel level (State.refined (.ofGraph G.graph) level numcells st)
      (Generic.node true (.ofGraph G.graph) inf tcLevel fuel level numcells st).2, href.last = last := by
  obtain ⟨xs, U, codes, trace, hsel, htargets, hcodes, hUL, _, hd⟩ :=
    firstPath_history hn path hl h htsize (by omega)
  have href := firstPath_reference (inf := inf) path
  have htc := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1) href
  have hlab := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.2) href
  have hcode := congrArg (fun x : Array Nat × Array Int × Array Nat => x.1) href
  change (Generic.node true (.ofGraph G.graph) inf tcLevel fuel level numcells st).2.firsttc =
    leaf.firsttc.set! (last + 1) (-1) at htc
  change (Generic.node true (.ofGraph G.graph) inf tcLevel fuel level numcells st).2.firstlab = leaf.lab at hlab
  change (Generic.node true (.ofGraph G.graph) inf tcLevel fuel level numcells st).2.firstcode =
    leaf.firstcode.set! (last + 1) codeSentinel at hcode
  have hlen := trace.descent.length
  have hclen := trace.length
  have hready := trace.descent.ready h.refined
  have hlast : last ≤ n := Nat.le_trans hready.spec.depth
    (by rw [hready.spec.count]; exact bcount_le _ _ _)
  refine ⟨⟨last, U, xs, codes, trace, hsel, ?_, hUL.trans hlab.symm, hd,
    firstPath_sentinel path (by omega), ?_⟩, rfl⟩
  · rw [htc]
    apply htargets.set_after
    simp only [List.length_map]
    omega
  · rw [hcode]
    exact hcodes.set_after (by omega)

end Hex.GraphIso.Nauty.Sparse
