/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FrameReturn
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Actual sparse call invariants and frame effects, including arbitrary
truncation and nonlocal exits. Parent equitability is restored between siblings. -/
@[expose] def reachContract (G : GraphIso.Sparse.Colored n k) : Generic.Contract (State n) n where
  nodePre _ _ level numcells st := 1 ≤ level ∧ NodeInv G level numcells st
  nodePost _ _ level _ st out := FrameOut G (level - 1) level st out.2
  sweepPre _ _ _ level numcells tc _ cursor cell _ st :=
    1 ≤ level ∧ Ready G level numcells st ∧ Generic.Target State.frame level tc cell st ∧
      ∀ v, cursor = some v → cell.mem v = true
  sweepPost _ _ _ level _ _ _ _ _ _ st out := FrameOut G level level st out.2.2

/-- The production node's local work preserves its caller frame when its
child sweep does. Refinement establishes all target and equitability premises. -/
theorem reach_node (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel : Nat)
    {fuel : Nat} {next : Generic.SweepFn (State n) n}
    (hnext : (reachContract G).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells : Nat) (st : State n)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st) :
    FrameOut G (level - 1) level st
      (Generic.nodeStep (.ofGraph G.graph) tcLevel next first level numcells st).2 := by
  have hv := h.visit_ready hn hl
  have compose : ∀ out, FrameOut G level level
      (visit (.ofGraph G.graph) level numcells st).2.2 out →
      FrameOut G (level - 1) level st out := fun _ hx => h.visit_frame hl hx
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst, Generic.Policy.compareCodes,
    Generic.Policy.chooseTarget, Generic.Policy.firstterminal, Generic.Policy.classify,
    Generic.Policy.leafExit, Generic.Policy.cheapCheck]
  generalize he : visit (.ofGraph G.graph) level numcells st = r at hv compose ⊢
  obtain ⟨nc, code, refined⟩ := r
  let compared := if first then recordFirst (n := n) level code refined
    else compareCodes (n := n) level code refined
  have hc : Local G level nc refined compared := by
    cases first
    · exact hv.compare code
    · exact hv.record code
  have ht := hc.ready.target_frame first tcLevel
  have htarget := hc.ready.target hn hl first tcLevel
  dsimp only
  generalize he : chooseTarget first (.ofGraph G.graph) tcLevel level nc compared = r at ht htarget ⊢
  obtain ⟨tc, cell, size, targeted⟩ := r
  have hfinish : ∀ prepared, Local G level nc refined prepared →
      Generic.Target State.frame level tc.toNat cell prepared →
      FrameOut G (level - 1) level st (Id.run (do
        let ready := cheapCheck (n := n) first level prepared
        let tv := cell.nextElem none
        let (exit, index, out) := next first level nc tc.toNat (tv.getD 0) tv cell 0 ready
        match exit with
        | .done => return (Generic.Exit.unwind (level - 1) false,
            Generic.Policy.afterSweep (n := n) first level size index out)
        | _ => return (exit, out))).2 := by
    intro prepared hp htarg
    have hcheap := hp.ready.cheap first
    have hout := hnext first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 _
      ⟨hl, hcheap.ready, htarg.of_out hcheap.frame.effect, fun _ hv => VSet.nextElem_mem hv⟩
    dsimp only
    generalize he : next first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (cheapCheck (n := n) first level prepared) = r at hout ⊢
    obtain ⟨exit, index, out⟩ := r
    have hall : FrameOut G level level refined out := (hp.frame.trans hcheap.frame).trans hout
    cases exit
    · exact compose _ (hall.afterSweep first level size index)
    · exact compose _ hall
    · exact compose _ hall
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact compose _ ((hc.trans ht).trans ht.ready.terminal).frame
    · exact hfinish targeted (hc.trans ht) htarget
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hc' := ht.ready.classify
    generalize he : classify (.ofGraph G.graph) level nc targeted = r at hc' ⊢
    obtain ⟨leaf, classified⟩ := r
    have he' := hc'.ready.leaf leaf
    generalize he : leafExit (n := n) leaf level classified = r at he' ⊢
    obtain ⟨exit, out⟩ := r
    have hall := ((hc.trans ht).trans hc').trans he'
    cases exit
    · exact hfinish out hall ((htarget.of_out hc'.frame.effect).of_out he'.frame.effect)
    · exact compose _ hall.frame
    · exact compose _ hall.frame

end Hex.GraphIso.Nauty.Sparse
