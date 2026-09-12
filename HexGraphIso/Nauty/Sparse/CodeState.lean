/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.LeafCodes
public import HexGraphIso.Nauty.Sparse.TraceNode
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A native off-path entry carries both admission history and the
general guided history for its next cached refinement. -/
structure CodeEntry (G : GraphIso.Sparse.Colored n k) (tcLevel level numcells : Nat)
    (st : State n) : Prop extends TraceEntry G tcLevel level numcells st where
  route : let r := visit (.ofGraph G.graph) level numcells st
    RouteHistory G.graph tcLevel level (level - 1) r.1 r.2.2

/-- Prepared and recovered native partitions retain the histories needed
to interpret both code comparisons and first-reference admission. -/
structure CodeReady (G : GraphIso.Sparse.Colored n k) (tcLevel level numcells : Nat)
    (st : State n) : Prop extends TraceReady G tcLevel level numcells st where
  route : RouteHistory G.graph tcLevel level level numcells st

theorem CodeEntry.prepare {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat}
    {st : State n} (h : CodeEntry G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level) :
    let p := prepareOther (.ofGraph G.graph) tcLevel level numcells st
    CodeReady G tcLevel level p.1 p.2.2.2.2.2 :=
  ⟨h.toTraceEntry.prepare hn hl, (h.route.compare (by omega) _).target⟩

theorem CodeReady.cheap {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat}
    {st : State n} (h : CodeReady G tcLevel level numcells st) (first : Bool) :
    CodeReady G tcLevel level numcells (cheapCheck first level st) :=
  ⟨h.toTraceReady.cheap first, h.route.cheap first⟩

/-- Entering an actual child supplies the pending general and cheap
histories with the child's own invalidated cache and individualized arrays. -/
theorem CodeReady.child {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells tc tv : Nat}
    {st : State n} {cell : VSet n} (h : CodeReady G tcLevel level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level) (first : Bool)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hc : CheapRecorded level tc st) (hr : RouteRecorded G.graph tcLevel level tc st) :
    CodeEntry G tcLevel (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st) :=
  ⟨h.toTraceReady.child hn hl first ht hv hc, h.route.child first h.ready ht hv hr⟩

/-- Full native child calls preserve the parent's histories and both
target records after recovery. This uses independent frame and trace
theorems and therefore does not assume the child's code correctness. -/
theorem CodeReady.child_return {G : GraphIso.Sparse.Colored n k}
    {tcLevel level numcells tc tv : Nat} {st : State n} {cell : VSet n}
    (h : CodeReady G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first : Bool) (fuel : Nat) (ht : Generic.Target State.frame level tc cell st)
    (hv : cell.mem tv = true) (hc : CheapRecorded level tc st)
    (hr : RouteRecorded G.graph tcLevel level tc st) :
    let ch := (policy (n := n)).child first level tc tv st
    let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ch).2
    let back := (policy (n := n)).recover (n + 2) level ((policy (n := n)).leaveChild tv out)
    CodeReady G tcLevel level numcells back ∧ CheapRecorded level tc back ∧
      RouteRecorded G.graph tcLevel level tc back := by
  have hch := h.child hn hl first ht hv hc hr
  have htrace := node_trace G hn tcLevel fuel _ _ _ (by omega) hch.toTraceEntry
  have ht' := h.toTraceReady.child_return hn hl first fuel ht hv htrace
  have hr' := h.route.child_return (fuel := fuel) first hl h.ready ht hv
  exact ⟨⟨ht'.1, hr'.1⟩, ht'.2 hc, hr'.2 hr⟩

end Hex.GraphIso.Nauty.Sparse
