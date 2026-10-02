/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.PairsSweep
import all HexGraphIso.Nauty.Sparse.CheapHistory
import all HexGraphIso.Nauty.Policy.Effect
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every complete or truncated off-path call preserves the root pruning
workspace. Native boundary, path and trace invariants justify each admission
before the node/sibling induction proceeds through the actual filters. -/
theorem node_pairs (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel fuel : Nat) :
    ∀ level numcells st, 1 ≤ level → PairsEntry G tcLevel level numcells st →
      PairsOk G (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 := by
  induction fuel with
  | zero =>
    intro level numcells st hl h
    rw [Generic.node]
    exact h.pairs
  | succ fuel ih =>
    intro level numcells st hl h
    let v := visit (.ofGraph G.graph) level numcells st
    let compared := compareCodes level v.2.1 v.2.2
    let target := chooseTarget false (.ofGraph G.graph) tcLevel level v.1 compared
    let classified := classify (.ofGraph G.graph) level v.1 target.2.2.2
    let acted := leafExit classified.1 level classified.2
    have hcomp := (h.node.visit_ready hn hl).compare v.2.1
    have htarget : Generic.Target State.frame level target.1.toNat target.2.1 target.2.2.2 :=
      hcomp.ready.target hn hl false tcLevel
    have prepared := h.prepare hn hl
    have ht : TraceReady G tcLevel level v.1 target.2.2.2 := prepared.1
    have hpath : PathInv G level target.2.2.2 := prepared.2.1
    have hbound : target.2.2.2.noncheaplevel ≤ level := prepared.2.2.2.2
    have hb : CheapBoundary G level target.2.2.2 := prepared.2.2.2.1
    have hp : PairsOk G target.2.2.2 := prepared.2.2.1
    have ha : TraceReady G tcLevel level v.1 acted.2 := ht.classified hn
    have hclass := ht.ready.classify
    have hleaf := hclass.ready.leaf classified.1
    have hpa : PairsOk G acted.2 := classified_pairs ht hn hp hb hbound
    have hba : CheapBoundary G level acted.2 := (hb.classify v.1).leaf classified.1
    have hpatha : PathInv G level acted.2 := (hpath.classify v.1).leaf classified.1
    have hbounda : acted.2.noncheaplevel ≤ level := by
      rw [leafExit_noncheap, (classify_controls (.ofGraph G.graph) level v.1 target.2.2.2).2]
      exact hbound
    have hfinish : acted.1 = .done →
        PairsOk G (Generic.sweep false (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
          level v.1 target.1.toNat ((target.2.1.nextElem none).getD 0) (target.2.1.nextElem none)
          target.2.1 0 (cheapCheck false level acted.2)).2.2 := by
      intro hdone
      have hi : classified.1 = .internal := (leafExit_done classified.1 level classified.2).mp hdone
      have hopen : v.1 ≠ n := classify_open hi
      have hnc : v.1 < n := by
        have hc : v.1 = bcount target.2.2.2.ptn level n := ht.ready.ok.count
        have hb := bcount_le target.2.2.2.ptn level n
        omega
      have hcode := refineWith_code_lt (.ofGraph G.graph) level st.lab st.ptn st.active numcells st.canong.scratch
      have hh := h.history.compare (by omega) hcode
      have hrecord : CheapRecorded level target.1.toNat target.2.2.2 := hh.recorded hnc hcomp.ready.scratch
      have hrecord' : CheapRecorded level target.1.toNat acted.2 := hrecord.classified
      have hcheap := ha.ready.cheap false
      exact pairs_sweep G hn tcLevel fuel ih (n + 1) false level v.1 target.1.toNat
        ((target.2.1.nextElem none).getD 0) 0 (target.2.1.nextElem none) target.2.1 _ hl
        (show PairsReady G tcLevel level v.1 (cheapCheck false level acted.2) from
          ⟨ha.cheap false, hpatha.cheap false, hpa.cheap false level,
            hba.cheap hn hl ha.ready false, cheap_bound false hbounda⟩)
        (((htarget.of_out hclass.frame.effect).of_out hleaf.frame.effect).of_out hcheap.frame.effect)
        (fun _ hv => VSet.nextElem_mem hv) (by intro he; cases he)
        (hrecord'.cheap false ha.ancestor)
    rw [Generic.node]
    unfold Generic.nodeStep
    change PairsOk G (Id.run (do
      let (exit, prepared) := acted
      match exit with
      | .done => pure ()
      | _ => return (exit, prepared)
      let ready := cheapCheck false level prepared
      let s := Generic.sweep false (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        level v.1 target.1.toNat ((target.2.1.nextElem none).getD 0) (target.2.1.nextElem none)
        target.2.1 0 ready
      match s.1 with
      | .done => return (.unwind (level - 1) false,
          (policy (n := n)).afterSweep false level target.2.2.1 s.2.1 s.2.2)
      | _ => return (s.1, s.2.2))).2
    generalize he : acted = result at hpa hfinish ⊢
    obtain ⟨exit, prepared⟩ := result
    cases exit with
    | fuel => exact hpa
    | unwind => exact hpa
    | done =>
      have hs := hfinish rfl
      dsimp only
      generalize he : Generic.sweep false (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        level v.1 target.1.toNat ((target.2.1.nextElem none).getD 0) (target.2.1.nextElem none)
        target.2.1 0 (cheapCheck false level prepared) = result at hs ⊢
      obtain ⟨exit, index, out⟩ := result
      cases exit with
      | fuel => exact hs
      | unwind => exact hs
      | done => exact hs.afterSweep false level target.2.2.1 index

end Hex.GraphIso.Nauty.Sparse
