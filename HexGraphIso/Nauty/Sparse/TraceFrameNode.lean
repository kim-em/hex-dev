/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TraceFrameOps
public import HexGraphIso.Nauty.Sparse.Reach
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The ordinary native frame contract together with preservation of any
fixed suspended ancestor. The latter implication is proved by the policy
induction; it is not an assumption about a completed production call. -/
@[expose] def traceFrameContract (G : GraphIso.Sparse.Colored n k) (base : Nat) (root : State n) :
    Generic.Contract (State n) n :=
  { reachContract G with
    nodePost := fun _ _ level _ st out => FrameOut G (level - 1) level st out.2 ∧
      (base < level → TraceFrame G base root st → TraceFrame G base root out.2)
    sweepPost := fun _ _ _ level _ _ _ _ _ _ st out => FrameOut G level level st out.2.2 ∧
      (base ≤ level → TraceFrame G base root st → TraceFrame G base root out.2.2) }

/-- Actual node preparation, either terminal action, and the returned
sweep preserve the frozen reference and generator frame. -/
theorem traceFrame_node (G : GraphIso.Sparse.Colored n k) {base cells : Nat} {root : State n}
    (hp : Ready G base cells root) (hn : 0 < n) (hb : 1 ≤ base) (tcLevel : Nat)
    {fuel : Nat} {next : Generic.SweepFn (State n) n}
    (hnext : (traceFrameContract G base root).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells : Nat) (st : State n)
    (hl : 1 ≤ level) (hi : NodeInv G level numcells st)
    (hlevel : base < level) (h : TraceFrame G base root st) :
    TraceFrame G base root (Generic.nodeStep (.ofGraph G.graph) tcLevel next first level numcells st).2 := by
  have hv := hi.visit_ready hn hl
  have hvisit := h.visit hp hi hn hb hlevel
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst, Generic.Policy.compareCodes,
    Generic.Policy.chooseTarget, Generic.Policy.firstterminal, Generic.Policy.classify,
    Generic.Policy.leafExit, Generic.Policy.cheapCheck]
  generalize he : visit (.ofGraph G.graph) level numcells st = r at hv hvisit ⊢
  obtain ⟨nc, code, refined⟩ := r
  let compared := if first then recordFirst (n := n) level code refined
    else compareCodes (n := n) level code refined
  have hc : Local G level nc refined compared := by
    cases first
    · exact hv.compare code
    · exact hv.record code
  have hcomp : TraceFrame G base root compared := by
    cases first
    · exact hvisit.compare level code
    · exact hvisit.record level code
  have ht := hc.ready.target_frame first tcLevel
  have htarget := hc.ready.target hn hl first tcLevel
  have htf := hcomp.target first tcLevel level nc
  dsimp only
  generalize he : chooseTarget first (.ofGraph G.graph) tcLevel level nc compared = r at ht htarget htf ⊢
  obtain ⟨tc, cell, size, targeted⟩ := r
  have hfinish : ∀ prepared, Ready G level nc prepared → TraceFrame G base root prepared →
      Generic.Target State.frame level tc.toNat cell prepared →
      TraceFrame G base root (Id.run (do
        let ready := cheapCheck first level prepared
        let tv := cell.nextElem none
        let (exit, index, out) := next first level nc tc.toNat (tv.getD 0) tv cell 0 ready
        match exit with
        | .done => return (Generic.Exit.unwind (level - 1) false,
            Generic.Policy.afterSweep (n := n) first level size index out)
        | _ => return (exit, out))).2 := by
    intro prepared hr hf htarg
    have hcheap := hr.cheap first
    have hout := (hnext first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 _
      ⟨hl, hcheap.ready, htarg.of_out hcheap.frame.effect, fun _ hv => VSet.nextElem_mem hv⟩).2
      (by omega) (hf.cheap first level)
    dsimp only
    generalize he : next first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (cheapCheck first level prepared) = r at hout ⊢
    obtain ⟨exit, index, out⟩ := r
    cases exit
    · exact hout.afterSweep first level size index
    · exact hout
    · exact hout
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact htf.terminal hp ht.ready hn hb (by omega)
    · exact hfinish targeted ht.ready htf htarget
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hclass := ht.ready.classify
    have hleafFrame := htf.classified hp ht.ready hn hb (by omega)
    dsimp only at hleafFrame
    generalize he : classify (.ofGraph G.graph) level nc targeted = r at hclass hleafFrame ⊢
    obtain ⟨leaf, classified⟩ := r
    have hleaf := hclass.ready.leaf leaf
    generalize he : leafExit leaf level classified = r at hleaf hleafFrame ⊢
    obtain ⟨exit, out⟩ := r
    cases exit
    · exact hfinish out hleaf.ready hleafFrame
        ((htarget.of_out hclass.frame.effect).of_out hleaf.frame.effect)
    · exact hleafFrame
    · exact hleafFrame

end Hex.GraphIso.Nauty.Sparse
