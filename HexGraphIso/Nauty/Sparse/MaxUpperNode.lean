/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxUpperSweep
public import HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxDescent
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.MaxUpperSweep
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Every actual terminal dispatch respects the full node upper bound,
whether it compares discrete rows or rejects a nondiscrete code prefix. -/
theorem Frame.Valid.emit_bound {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs fs : List Nat} (h : f.Valid G)
    (hi : CodeEntry G tcLevel f.level f.numcells f.entry)
    (hc : Comparison G.graph f.codes bs fs f.entry)
    (he : (f.emit G.graph tcLevel).1 ≠ .done) :
    Bounded (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
      (State.best G.graph (f.emit G.graph tcLevel).2) := by
  let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  by_cases hd : p.1 = n
  · exact (h.leaf_bound hi hc hd).choose_spec.2.1
  · have hbad : (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .bad := by
      have hn : (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 ≠ .internal := by
        intro hh
        exact he ((leafExit_done _ _ _).mpr hh)
      rw [classify_eq] at hn ⊢
      split
      · rfl
      · rename_i hguard
        simp only [hguard, bne_iff_ne.mpr hd, ite_true] at hn
        exact (hn rfl).elim
    exact (h.prune_bound hc hd hbad).2.1

theorem afterSweep_best (G : Hex.SparseGraph n) (first : Bool)
    (level size index : Nat) (st : State n) :
    State.best G ((policy (n := n)).afterSweep first level size index st) = State.best G st := by
  change State.best G (if first then { Nauty.afterSweep first level size index st with
    order := (Nauty.afterSweep first level size index st).order * index }
    else Nauty.afterSweep first level size index st) = _
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals unfold Nauty.afterSweep; split <;> rfl

/-- The executed native off-path node and sibling recursion never install
a key above the incoming incumbent and complete frozen subtree. This is
the unconditional upper half of the production maximum induction. -/
theorem node_upper (G : GraphIso.Sparse.Colored n k) (tcLevel fuel : Nat) :
    NodeUpper G tcLevel fuel := by
  induction fuel with
  | zero =>
    intro f bs fs parents hv hi hc hs hf
    have hl := hv.length
    have hd := hv.depth
    omega
  | succ fuel ih =>
    intro f bs fs parents hv hi hc hs hf
    have hn : 0 < n := by have := hv.positive; have := hv.depth; omega
    have hlen := hv.length
    have hdepth := hv.depth
    by_cases he : (f.emit G.graph tcLevel).1 = .done
    · let v := visit (.ofGraph G.graph) f.level f.numcells f.entry
      let compared := compareCodes f.level v.2.1 v.2.2
      let t := chooseTarget false (.ofGraph G.graph) tcLevel f.level v.1 compared
      let acted := f.emit G.graph tcLevel
      let ready := cheapCheck false f.level t.2.2.2
      have ht : CodeReady G tcLevel f.level v.1 t.2.2.2 := hi.prepare hn hv.positive
      have hcomp := (hv.node.visit_ready hn hv.positive).compare v.2.1
      have hinternal : (classify (.ofGraph G.graph) f.level v.1 t.2.2.2).1 = .internal :=
        (leafExit_done _ _ _).mp he
      have hstate : acted.2 = t.2.2.2 := by
        change (leafExit (classify (.ofGraph G.graph) f.level v.1 t.2.2.2).1 f.level
          (classify (.ofGraph G.graph) f.level v.1 t.2.2.2).2).2 = _
        rw [classify_internal_state hinternal]
        rfl
      have hopen : v.1 < n := by
        have hcount : v.1 = bcount t.2.2.2.ptn f.level n := ht.ready.ok.count
        have hb := bcount_le t.2.2.2.ptn f.level n
        have hne := classify_open hinternal
        omega
      have hm := hc.prepare tcLevel f.numcells (by omega)
      rw [hlen] at hm
      obtain ⟨hrecord, hroute⟩ := hi.recorded hn hv.positive hopen
      change CheapRecorded f.level t.1.toNat t.2.2.2 at hrecord
      change RouteRecorded G.graph tcLevel f.level t.1.toNat t.2.2.2 at hroute
      have hphase := hcomp.ready.target_phase (tcLevel := tcLevel) hn hv.positive hopen
      have hphase' : ready.compCanon ≤ 0 ∨ false = false ∧ (t.2.1.nextElem none).isSome := by
        rcases hphase with hp | hp
        · left
          unfold ready cheapCheck
          split <;> exact hp
        · exact Or.inr ⟨rfl, hp⟩
      have hkey : State.key G.graph bs ready = State.key G.graph bs f.entry :=
        f.otherParent_key G.graph tcLevel bs 0
      have hscope : Scope G tcLevel f bs ready parents := hs.change
        (by rw [hkey]; exact Grows.refl _) (f.otherParent_boundary G.graph tcLevel bs 0)
      have hparents : ∀ tv, t.2.1.mem tv = true →
          (⟨f, false, ready, t.1.toNat, t.2.1, tv, bs⟩ : Parent n).Valid G tcLevel := by
        intro tv hmem
        exact hv.other_parent hc hopen hmem
      have hready : CodeReady G tcLevel f.level v.1 ready := ht.cheap false
      have hrecord' : CheapRecorded f.level t.1.toNat ready := hrecord.cheap false ht.ancestor
      have hroute' : RouteRecorded G.graph tcLevel f.level t.1.toNat ready := hroute.cheap false
      have hcomparison : Comparison G.graph (f.codes ++ [f.code G.graph]) bs fs ready :=
        hm.1.cheap false f.level
      have hupper := upper_sweep G hn tcLevel fuel ih (n + 1) false f bs fs t.1.toNat
        ((t.2.1.nextElem none).getD 0) 0 (t.2.1.nextElem none) t.2.1 ready parents hv
        hready hparents hscope
        (fun _ hv => VSet.nextElem_mem hv) (by intro hh; cases hh)
        hrecord' hroute' (by omega) (fun _ _ => by omega) hcomparison hphase'
      rw [hkey] at hupper
      rw [Generic.node, f.sweep_step _ he]
      dsimp only
      rw [show (f.emit G.graph tcLevel).2 = t.2.2.2 from hstate]
      let swept := Generic.sweep false (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        f.level v.1 t.1.toNat ((t.2.1.nextElem none).getD 0) (t.2.1.nextElem none) t.2.1 0 ready
      change Bounded (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
        (State.best G.graph swept.2.2) at hupper
      change Bounded (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
        (State.best G.graph (match swept.1 with
          | .done => (Generic.Exit.unwind (f.level - 1) false,
              (policy (n := n)).afterSweep false f.level t.2.2.1 swept.2.1 swept.2.2)
          | _ => (swept.1, swept.2.2)).2)
      generalize hx : swept = result at hupper ⊢
      obtain ⟨exit, index, out⟩ := result
      cases exit with
      | fuel => exact hupper
      | unwind => exact hupper
      | done =>
        change Bounded _ _ (State.best G.graph ((policy (n := n)).afterSweep false f.level t.2.2.1 index out))
        rw [afterSweep_best]
        exact hupper
    · rw [Generic.node, f.emit_step _ he]
      exact hv.emit_bound hi hc he

end Hex.GraphIso.Nauty.Sparse.Max
