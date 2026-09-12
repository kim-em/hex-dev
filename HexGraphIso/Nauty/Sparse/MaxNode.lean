/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxSweep
public import HexGraphIso.Nauty.Sparse.MaxStart
public import HexGraphIso.Nauty.Sparse.MaxTerminal
public import HexGraphIso.Nauty.Sparse.MaxUpperNode
import all HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxUpperSweep
import all HexGraphIso.Nauty.Sparse.ComparisonOps
import all HexGraphIso.Nauty.Sparse.Maximum
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The actual off-path search satisfies its complete maximum contract.
The induction assembles local native state invariants at preparation,
child entry and recovery; its only recursive premise is the smaller
executed call. No production-maximum theorem is assumed. -/
theorem node_max (G : GraphIso.Sparse.Colored n k) (tcLevel fuel : Nat) : NodeMax G tcLevel fuel := by
  induction fuel with
  | zero =>
    intro f bs fs parents h hf
    have hl := h.frame.length
    have hd := h.frame.depth
    omega
  | succ fuel ih =>
    intro f bs fs parents h hf
    have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
    have hlen := h.frame.length
    have hdepth := h.frame.depth
    refine ⟨node_upper G tcLevel (fuel + 1) f bs fs parents
      h.frame h.codes h.machine h.scope hf, ?_⟩
    by_cases he : (f.emit G.graph tcLevel).1 = .done
    · let l : Loop n := ⟨f, false⟩
      let p := l.prepare G.graph tcLevel
      let prepared := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
      have hi : (classify (.ofGraph G.graph) f.level prepared.1 prepared.2.2.2.2.2).1 = .internal :=
        (leafExit_done _ _ _).mp he
      have hstate : (f.emit G.graph tcLevel).2 = prepared.2.2.2.2.2 := by
        change (leafExit (classify (.ofGraph G.graph) f.level prepared.1 prepared.2.2.2.2.2).1 f.level
          (classify (.ofGraph G.graph) f.level prepared.1 prepared.2.2.2.2.2).2).2 = _
        rw [classify_internal_state hi]
        rfl
      have hs := h.prepare hi
      have hlower := lower_sweep G tcLevel fuel ih (n + 1) l bs fs
        ((p.2.2.1.nextElem none).getD 0) 0 (p.2.2.1.nextElem none) p.2.2.1 p.2.2.2.2 parents hs
        (by change n ≤ f.level + fuel; omega) (fun _ _ => by omega) (by intro hh; cases hh)
      let swept := Generic.sweep false (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1) f.level
        prepared.1 prepared.2.2.1.toNat ((prepared.2.2.2.1.nextElem none).getD 0)
        (prepared.2.2.2.1.nextElem none) prepared.2.2.2.1 0 (cheapCheck false f.level prepared.2.2.2.2.2)
      have hbound : ∀ target short, swept.1 = .unwind target short → target < f.level :=
        Generic.sweep_bound false (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1) f.level
          prepared.1 prepared.2.2.1.toNat ((prepared.2.2.2.1.nextElem none).getD 0)
          (prepared.2.2.2.1.nextElem none) prepared.2.2.2.1 0 (cheapCheck false f.level prepared.2.2.2.2.2)
      have hcover : ExitCover (f.key G.graph tcLevel) (State.best G.graph swept.2.2) f.level
          (Max.Witness G tcLevel (parents.frames.insert f)) swept.1 := by
        simpa only [l, p, swept, prepared, Loop.cell, Loop.prepare, prepareOther, Bool.false_eq_true, ite_false]
          using hlower
      rw [Generic.node, f.sweep_step _ he]
      dsimp only
      rw [hstate]
      change ExitCover (f.key G.graph tcLevel)
        (State.best G.graph (match swept.1 with
          | .done => (Generic.Exit.unwind (f.level - 1) false,
              (policy (n := n)).afterSweep false f.level prepared.2.2.2.2.1 swept.2.1 swept.2.2)
          | _ => (swept.1, swept.2.2)).2) (f.level - 1)
        (Max.Witness G tcLevel parents.frames)
        (match swept.1 with
          | .done => (Generic.Exit.unwind (f.level - 1) false,
              (policy (n := n)).afterSweep false f.level prepared.2.2.2.2.1 swept.2.1 swept.2.2)
          | _ => (swept.1, swept.2.2)).1
      generalize hx : swept = result at hcover hbound ⊢
      obtain ⟨exit, index, out⟩ := result
      cases exit with
      | fuel => trivial
      | done =>
        change (f.level - 1 ≤ f.level - 1) ∧ _
        refine ⟨Nat.le_refl _, ?_⟩
        simp only [↓reduceIte, afterSweep_best]
        exact hcover
      | unwind target short =>
        have ht := hbound target short rfl
        have hw : Max.Witness G tcLevel (parents.frames.insert f) target (State.best G.graph out) := by
          simpa only [ExitCover, ite_eq_right (by omega : target ≠ f.level)] using hcover.2
        change target ≤ f.level - 1 ∧ _
        refine ⟨by omega, ?_⟩
        split
        · rename_i heq
          subst target
          exact Max.Witness.resolve hw
        · exact (Max.Witness.below (by omega : target < f.level - 1)).mp hw
    · rw [Generic.node, f.emit_step _ he]
      exact (h.emit he).coverage

end Hex.GraphIso.Nauty.Sparse.Max
