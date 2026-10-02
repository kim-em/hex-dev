/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TraceSweep
import all HexGraphIso.Nauty.Sparse.CheapHistory
import all HexGraphIso.Nauty.Policy.Effect
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

theorem classify_open {g : Graph n} {level numcells : Nat} {st : State n}
    (h : (classify g level numcells st).1 = .internal) : numcells ≠ n := by
  intro he
  subst numcells
  unfold classify at h
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst,
    bne_self_eq_false, Bool.false_eq_true, ite_false] at h
  repeat' split at h
  all_goals cases h

/-- Classification and leaf bookkeeping retain a recorded sweep target;
only the later cheap guard can make that recording irrelevant. -/
theorem CheapRecorded.classified {g : Graph n} {level numcells tc : Nat} {st : State n}
    (h : CheapRecorded level tc st) :
    let c := classify g level numcells st
    CheapRecorded level tc (leafExit c.1 level c.2).2 := by
  let c := classify g level numcells st
  have ht := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.1)
    ((leafExit_reference c.1 level c.2).trans (classify_reference g level numcells st))
  change (leafExit c.1 level c.2).2.firsttc = st.firsttc at ht
  change (leafExit c.1 level c.2).2.noncheaplevel ≤ (leafExit c.1 level c.2).2.gcaFirst →
    (leafExit c.1 level c.2).2.eqlevFirst = level → (leafExit c.1 level c.2).2.firsttc[level]! = Int.ofNat tc
  rw [leafExit_noncheap, leafExit_gca, leafExit_eqlev, ht,
    (classify_controls g level numcells st).1, (classify_controls g level numcells st).2, classify_eqlev]
  exact h

/-- Every complete or truncated off-path call preserves soundness of the
literal emitted trace. The mutual node/sibling induction establishes all
admission histories from the entry's pending native visit. -/
theorem node_trace (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel fuel : Nat) :
    ∀ level numcells st, 1 ≤ level → TraceEntry G tcLevel level numcells st →
      TraceOk G (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 := by
  induction fuel with
  | zero =>
    intro level numcells st hl h
    rw [Generic.node]
    exact h.trace
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
    have ht : TraceReady G tcLevel level v.1 target.2.2.2 := h.prepare hn hl
    have ha : TraceReady G tcLevel level v.1 acted.2 := ht.classified hn
    have hclass := ht.ready.classify
    have hleaf := hclass.ready.leaf classified.1
    have hfinish : acted.1 = .done →
        TraceOk G (Generic.sweep false (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
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
      exact trace_sweep G hn tcLevel fuel ih (n + 1) false level v.1 target.1.toNat
        ((target.2.1.nextElem none).getD 0) 0 (target.2.1.nextElem none) target.2.1 _ hl
        (ha.cheap false)
        (((htarget.of_out hclass.frame.effect).of_out hleaf.frame.effect).of_out hcheap.frame.effect)
        (fun _ hv => VSet.nextElem_mem hv) (by intro he; cases he)
        (hrecord'.cheap false ha.ancestor)
    rw [Generic.node]
    unfold Generic.nodeStep
    change TraceOk G (Id.run (do
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
    generalize he : acted = result at ha hfinish ⊢
    obtain ⟨exit, prepared⟩ := result
    cases exit with
    | fuel => exact ha.trace
    | unwind => exact ha.trace
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
