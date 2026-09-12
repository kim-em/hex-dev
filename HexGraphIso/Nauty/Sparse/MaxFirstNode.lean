/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstLower
public import HexGraphIso.Nauty.Sparse.MaxFirstUpper
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFirstLeaf
import all HexGraphIso.Nauty.Sparse.MaxFirstSweep
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The complete executed first descent satisfies its maximum contract.
The induction supplies each first child's result, and the established
off-path theorem handles every later sibling. All contexts are derived
from the actual preparations, stored ancestors and child returns. -/
theorem FirstInput.maximum {G : GraphIso.Sparse.Colored n k} {tcLevel fuel last : Nat}
    {f : Frame n} {leaf : State n} {parents : Parents n}
    (h : FirstInput G tcLevel f parents)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel f.level f.numcells f.entry last leaf)
    (hf : n + 1 ≤ f.level + fuel) :
    let out := Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry
    MaxResult (f.key G.graph tcLevel) none (State.best G.graph out.2) (f.level - 1)
      (Max.Witness G tcLevel parents.frames) out.1 := by
  obtain ⟨level, numcells, codes, st⟩ := f
  induction fuel generalizing level numcells codes st last leaf parents with
  | zero => cases path
  | succ fuel ih =>
    let f : Frame n := ⟨level, numcells, codes, st⟩
    have hu := h.entry.upper path h.scope hf
    cases path with
    | leaf =>
      rename_i hd
      exact h.entry.frame.first_leaf h.entry.stored (by rw [h.entry.firstSize]; omega)
        h.entry.canonSize h.entry.codes_lt hd _
    | @step _ _ _ _ _ _ tv hopen htv horbit path =>
      have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
      have hi : (visit (.ofGraph G.graph) level numcells st).1 < n := by
        have hr := h.entry.frame.node.visit_ready hn h.entry.frame.positive
        have hc : (visit (.ofGraph G.graph) level numcells st).1 =
            bcount (visit (.ofGraph G.graph) level numcells st).2.2.ptn level n := hr.ok.count
        have hb := bcount_le (visit (.ofGraph G.graph) level numcells st).2.2.ptn level n
        change (visit (.ofGraph G.graph) level numcells st).1 ≠ n at hopen
        omega
      let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      have hch : FirstInput G tcLevel ch (parents.push p) := h.child hi htv
      have hchild := ih (level := ch.level) (numcells := ch.numcells) (codes := ch.codes) (st := ch.entry)
        hch path (by change n + 1 ≤ (level + 1) + fuel; change n + 1 ≤ level + (fuel + 1) at hf; omega)
      have hlower := h.sweep_lower hi htv horbit path
        (by change n ≤ level + fuel; change n + 1 ≤ level + (fuel + 1) at hf; omega) hchild
      refine ⟨hu, ?_⟩
      rw [Generic.node, Frame.first_sweep_step _ hopen]
      dsimp only
      rw [htv]
      simp only [Option.getD_some]
      let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      let swept := Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 (cheapCheck true level r.2.2.2.2)
      have hbound : ∀ target short, swept.1 = .unwind target short → target < level :=
        Generic.sweep_bound true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
          level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 (cheapCheck true level r.2.2.2.2)
      change ExitCover (f.key G.graph tcLevel) (State.best G.graph swept.2.2) level
        (Max.Witness G tcLevel (parents.frames.insert f)) swept.1 at hlower
      change ExitCover (f.key G.graph tcLevel)
        (State.best G.graph (match swept.1 with
          | .done => (Generic.Exit.unwind (level - 1) false,
              (policy (n := n)).afterSweep true level r.2.2.2.1 swept.2.1 swept.2.2)
          | _ => (swept.1, swept.2.2)).2) (level - 1)
        (Max.Witness G tcLevel parents.frames)
        (match swept.1 with
          | .done => (Generic.Exit.unwind (level - 1) false,
              (policy (n := n)).afterSweep true level r.2.2.2.1 swept.2.1 swept.2.2)
          | _ => (swept.1, swept.2.2)).1
      generalize hx : swept = result at hlower hbound ⊢
      obtain ⟨exit, index, out⟩ := result
      cases exit with
      | fuel => trivial
      | done =>
        change (level - 1 ≤ level - 1) ∧ _
        refine ⟨Nat.le_refl _, ?_⟩
        simp only [↓reduceIte, afterSweep_best]
        exact hlower
      | unwind target short =>
        have ht := hbound target short rfl
        have hw : Max.Witness G tcLevel (parents.frames.insert f) target (State.best G.graph out) := by
          simpa only [ExitCover, ite_eq_right (by omega : target ≠ level)] using hlower.2
        change target ≤ level - 1 ∧ _
        refine ⟨by omega, ?_⟩
        split
        · rename_i heq
          subst target
          exact Max.Witness.resolve hw
        · exact (Max.Witness.below (by omega : target < level - 1)).mp hw

end Hex.GraphIso.Nauty.Sparse.Max
