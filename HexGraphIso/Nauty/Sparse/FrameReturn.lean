/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ChildFrame
public import HexGraphIso.Nauty.Sparse.TargetFrame
public import HexGraphIso.Nauty.Sparse.VisitFrame
import all HexGraphIso.Nauty.Search.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Sparse

namespace FrameOut

variable {G : GraphIso.Sparse.Colored n k} {base level : Nat} {st out next : State n}

theorem congr (h : FrameOut G base level st out)
    (hl : next.lab = out.lab) (hp : next.ptn = out.ptn)
    (hf : next.firstlab = out.firstlab) (hc : next.canonlab = out.canonlab)
    (hs : Scratch.Bounded n next.canong.scratch) : FrameOut G base level st next :=
  ⟨h.effect.congr hl hp hf hc, hs⟩

theorem afterChild (h : FrameOut G base level st out) (depth tv : Nat) :
    FrameOut G base level st (afterChildFirst depth tv out) :=
  h.congr rfl rfl rfl rfl h.scratch

theorem leave (h : FrameOut G base level st out) (tv : Nat) :
    FrameOut G base level st { out with fixedpts := out.fixedpts.erase tv } :=
  h.congr rfl rfl rfl rfl h.scratch

theorem afterSweep (h : FrameOut G base level st out) (first : Bool) (depth size index : Nat) :
    FrameOut G base level st ((policy (n := n)).afterSweep first depth size index out) := by
  change FrameOut G base level st
    (if first then { (Nauty.afterSweep first depth size index out) with
      order := (Nauty.afterSweep first depth size index out).order * index }
    else Nauty.afterSweep first depth size index out)
  cases first <;> simp only [ite_true, Bool.false_eq_true, ite_false]
  all_goals unfold Nauty.afterSweep; split <;> exact h.congr rfl rfl rfl rfl h.scratch

end FrameOut

namespace NodeInv

/-- Stable colour buckets establish all production entry assertions. -/
theorem initial (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    NodeInv G 1 p.2.length (Sparse.initial (.ofGraph G.graph) p.1 p.2) := by
  refine ⟨SpecNode.initial G hn, ?_, ?_⟩
  · simp only [initialPartition_eq]
    exact frame_ok (root_searchOk G.toDense hn) rfl rfl (Or.inl rfl)
  · exact (Scratch.fresh_valid n (initialPartitionWith n k G.coloring.cells.toArray Fin.val).1 (initPtn n (n + 2)
      (initialPartitionWith n k G.coloring.cells.toArray Fin.val).2) 1).toBounded

end NodeInv
end Hex.GraphIso.Nauty.Sparse
