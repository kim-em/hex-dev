/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstLeaf
public import HexGraphIso.Nauty.Sparse.MaxPrepare
public import HexGraphIso.Nauty.Sparse.FirstTrace
import all HexGraphIso.Nauty.Sparse.MaxFirstLeaf
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Native first-path inputs retain the actual stored code prefix,
reference allocations, blank row store, workspace and inherited cheap shape. -/
structure FirstEntry (G : GraphIso.Sparse.Colored n k) (f : Frame n) : Prop where
  frame : f.Valid G
  shape : FirstShape G.graph f.level f.numcells f.entry
  targetSize : n < f.entry.firsttc.size
  firstSize : f.entry.firstcode.size = n + 2
  canonSize : f.entry.canoncode.size = n + 2
  blank : f.entry.canong.toRows = (Graph.ofGraph G.graph).blank
  work : f.entry.workperm.size = n
  trace : TraceOk G f.entry
  stored : StoredCodes f.entry.firstcode 1 f.codes
  codes_lt : ∀ code ∈ f.codes, code < codeSentinel

/-- The native root initializer establishes every first-entry field. -/
theorem FirstEntry.initial (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    FirstEntry G ⟨1, p.2.length, [], initial (.ofGraph G.graph) p.1 p.2⟩ := by
  refine ⟨⟨Nat.le_refl _, rfl, NodeInv.initial G hn⟩, FirstShape.initial _ _ _,
    ?_, ?_, ?_, rfl, ?_, TraceOk.initial _ _ _, ?_, ?_⟩
  · change n < (Array.replicate (n + 2) (-1 : Int)).size
    simp
  · change (Array.replicate (n + 2) 0).size = n + 2
    simp
  · change (Array.replicate (n + 2) 0).size = n + 2
    simp
  · change (Array.replicate n 0).size = n
    simp
  · intro i hi
    change i < 0 at hi
    omega
  · intro code hc
    cases hc

/-- First-entry storage and histories follow the literal native child,
including target scratch borrowing and child cache invalidation. -/
theorem FirstEntry.child {G : GraphIso.Sparse.Colored n k} {tcLevel tv : Nat} {f : Frame n}
    (h : FirstEntry G f)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (hm : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.mem tv = true) :
    FirstEntry G ((f.firstParent G.graph tcLevel [] tv).child G.graph tcLevel) := by
  let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  let ready := cheapCheck true f.level r.2.2.2.2
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hp := h.frame.first_parent h.shape hi hm []
  refine ⟨hp.child, h.shape.child h.frame.node hn h.frame.positive hm,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change n < ready.firsttc.size
    unfold ready cheapCheck
    split
    all_goals rw [(prepareFirst_store (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2,
      Array.size_set!]
    all_goals exact h.targetSize
  · change ready.firstcode.size = n + 2
    unfold ready cheapCheck
    split
    all_goals rw [(prepareFirst_store (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).1,
      Array.size_set!]
    all_goals exact h.firstSize
  · change ready.canoncode.size = n + 2
    unfold ready cheapCheck
    split
    all_goals rw [prepareFirst_canoncode]
    all_goals exact h.canonSize
  · change ready.canong.toRows = _
    unfold ready cheapCheck
    split <;> exact (prepareFirst_rows (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).trans h.blank
  · change ready.workperm.size = n
    unfold ready cheapCheck
    split <;> exact (prepareFirst_workSize (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).trans h.work
  · exact (((((h.trace.visit f.level f.numcells).record f.level (f.code G.graph)).target
      true tcLevel f.level (visit (.ofGraph G.graph) f.level f.numcells f.entry).1).cheap true f.level).child
      true f.level r.2.1.toNat tv)
  · have hs := h.frame.first_codes (tcLevel := tcLevel) h.stored (by rw [h.firstSize]; omega)
    change StoredCodes ready.firstcode 1 (f.codes ++ [f.code G.graph])
    unfold ready cheapCheck
    split <;> exact hs
  · intro code hc
    change code ∈ f.codes ++ [f.code G.graph] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h.codes_lt code hc
    · have he := List.mem_singleton.mp hc
      rw [he]
      exact f.code_lt G.graph

end Hex.GraphIso.Nauty.Sparse.Max
