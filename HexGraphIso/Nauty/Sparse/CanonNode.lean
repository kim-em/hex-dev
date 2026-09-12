/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonControl
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Actual native frame and canonical-reference effects have the same
entry conditions, including truncated calls and arbitrary return targets. -/
@[expose] def canonContract (G : GraphIso.Sparse.Colored n k) : Generic.Contract (State n) n :=
  { reachContract G with
    nodePost := fun _ _ level _ st result =>
      FrameOut G (level - 1) level st result.2 ∧ CanonOut level st result.2
    sweepPost := fun _ _ _ level _ _ _ _ _ _ st result =>
      FrameOut G level level st result.2.2 ∧ CanonOut level st result.2.2 }

/-- Native node preparation and leaf actions preserve canonical provenance;
an installed reference belongs to this node's actual cached refinement. -/
theorem canon_node (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel : Nat)
    {fuel : Nat} {next : Generic.SweepFn (State n) n}
    (hnext : (canonContract G).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells : Nat) (st : State n)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st) :
    CanonOut level st (Generic.nodeStep (.ofGraph G.graph) tcLevel next first level numcells st).2 := by
  have hv := h.visit_ready hn hl
  have compose : ∀ out, CanonOut level (visit (.ofGraph G.graph) level numcells st).2.2 out →
      CanonOut level st out := fun _ hx => CanonOut.visit h hx
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
  have hcc : compared.canonlab = refined.canonlab := by
    cases first
    · exact (compareCodes_frame level code refined).2.2.2
    · rfl
  have hcg : compared.gcaCanon = refined.gcaCanon := by
    cases first
    · exact compare_canon level code refined
    · rfl
  have hcanon : CanonOut level refined compared := CanonOut.fields (CanonOut.refl level refined) hcc hcg
  have ht := hc.ready.target_frame first tcLevel
  have htarget := hc.ready.target hn hl first tcLevel
  have htc := (chooseTarget_frame first (.ofGraph G.graph) tcLevel level nc compared).2.2.2
  have htg := chooseTarget_ancestor first (.ofGraph G.graph) tcLevel level nc compared
  dsimp only
  generalize he : chooseTarget first (.ofGraph G.graph) tcLevel level nc compared = r at ht htarget htc htg ⊢
  obtain ⟨tc, cell, size, targeted⟩ := r
  have hprepared := hc.trans ht
  have hcanPrepared : CanonOut level refined targeted := CanonOut.fields hcanon htc htg
  have hfinish : ∀ prepared, Local G level nc refined prepared → CanonOut level refined prepared →
      Generic.Target State.frame level tc.toNat cell prepared →
      CanonOut level st (Id.run (do
        let ready := cheapCheck first level prepared
        let tv := cell.nextElem none
        let (exit, index, out) := next first level nc tc.toNat (tv.getD 0) tv cell 0 ready
        match exit with
        | .done => return (Generic.Exit.unwind (level - 1) false,
            Generic.Policy.afterSweep (n := n) first level size index out)
        | _ => return (exit, out))).2 := by
    intro prepared hp hcan htarg
    have hcheap := hp.ready.cheap first
    have hcc : CanonOut level refined (cheapCheck first level prepared) := by
      unfold cheapCheck
      split <;> exact CanonOut.fields hcan rfl rfl
    have hout := (hnext first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 _
      ⟨hl, hcheap.ready, htarg.of_out hcheap.frame.effect, fun _ hv => VSet.nextElem_mem hv⟩).2
    dsimp only
    generalize he : next first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (cheapCheck first level prepared) = r at hout ⊢
    obtain ⟨exit, index, out⟩ := r
    have hall : CanonOut level refined out := CanonOut.trans hcc hout (hp.frame.trans hcheap.frame)
    cases exit
    · exact compose _ (CanonOut.afterSweep hall first size index)
    · exact compose _ hall
    · exact compose _ hall
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · apply compose
      apply CanonOut.trans hcanPrepared _ hprepared.frame
      exact ⟨Nat.min_le_left _ _, Or.inr ⟨Nat.le_refl _, rfl, cellsPerm_refl _ _ _⟩⟩
    · exact hfinish targeted hprepared hcanPrepared htarget
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hc' := ht.ready.classify
    have hcanonClass : CanonOut level refined (classify (.ofGraph G.graph) level nc targeted).2 :=
      CanonOut.fields hcanPrepared (classify_frame (.ofGraph G.graph) level nc targeted).2.2.2
        (classify_ancestor (.ofGraph G.graph) level nc targeted)
    generalize he : classify (.ofGraph G.graph) level nc targeted = r at hc' hcanonClass ⊢
    obtain ⟨leaf, classified⟩ := r
    have he' := hc'.ready.leaf leaf
    have hcanonLeaf := CanonOut.trans hcanonClass (canon_leaf leaf level classified) (hprepared.trans hc').frame
    generalize he : leafExit leaf level classified = r at he' hcanonLeaf ⊢
    obtain ⟨exit, out⟩ := r
    have hall := (hprepared.trans hc').trans he'
    cases exit
    · exact hfinish out hall hcanonLeaf ((htarget.of_out hc'.frame.effect).of_out he'.frame.effect)
    · exact compose _ hcanonLeaf
    · exact compose _ hcanonLeaf

end Hex.GraphIso.Nauty.Sparse
