/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FixedState
public import HexGraphIso.Nauty.Policy.Generic.Calls
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every call restores its incoming fixed-point set. Entry singletons
make each temporary child vertex fresh; recovered parents remain equitable. -/
@[expose] def fixedContract (G : GraphIso.Sparse.Colored n k) : Generic.Contract (State n) n where
  nodePre _ _ level numcells st :=
    1 ≤ level ∧ NodeInv G level numcells st ∧ FixedCells level st.frame
  nodePost _ _ _ _ st out := out.2.fixedpts = st.fixedpts
  sweepPre _ _ _ level numcells tc _ cursor cell _ st :=
    1 ≤ level ∧ Ready G level numcells st ∧ Generic.Target State.frame level tc cell st ∧
      (∀ v, cursor = some v → cell.mem v = true) ∧ FixedCells level st.frame
  sweepPost _ _ _ _ _ _ _ _ _ _ st out := out.2.2.fixedpts = st.fixedpts

/-- Native node preparation preserves the fixed singletons and their
bitset; all exit arms inherit exact restoration from the child sweep. -/
theorem fixed_node (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel : Nat)
    {fuel : Nat} {next : Generic.SweepFn (State n) n}
    (hnext : (fixedContract G).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells : Nat) (st : State n)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st) (hf : FixedCells level st.frame) :
    (Generic.nodeStep (.ofGraph G.graph) tcLevel next first level numcells st).2.fixedpts = st.fixedpts := by
  have hv := h.visit_ready hn hl
  have hvf := fixed_visit h hf
  have hve : (visit (.ofGraph G.graph) level numcells st).2.2.fixedpts = st.fixedpts := rfl
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst, Generic.Policy.compareCodes,
    Generic.Policy.chooseTarget, Generic.Policy.firstterminal, Generic.Policy.classify,
    Generic.Policy.leafExit, Generic.Policy.cheapCheck]
  generalize he : visit (.ofGraph G.graph) level numcells st = r at hv hvf hve ⊢
  obtain ⟨nc, code, refined⟩ := r
  let compared := if first then recordFirst (n := n) level code refined
    else compareCodes (n := n) level code refined
  have hc : Local G level nc refined compared := by
    cases first
    · exact hv.compare code
    · exact hv.record code
  have hce : compared.fixedpts = refined.fixedpts := by
    cases first
    · exact compare_fixed level code refined
    · rfl
  have hcf := hvf.ofEffect hce hc.frame.effect
  have ht := hc.ready.target_frame first tcLevel
  have htarget := hc.ready.target hn hl first tcLevel
  have hte := target_fixed first (.ofGraph G.graph) tcLevel level nc compared
  dsimp only
  generalize he : chooseTarget first (.ofGraph G.graph) tcLevel level nc compared = r at ht htarget hte ⊢
  obtain ⟨tc, cell, size, targeted⟩ := r
  have htf := hcf.ofEffect hte ht.frame.effect
  have heq := hte.trans (hce.trans hve)
  have hfinish : ∀ prepared, Ready G level nc prepared →
      Generic.Target State.frame level tc.toNat cell prepared → FixedCells level prepared.frame →
      prepared.fixedpts = st.fixedpts →
      (Id.run (do
        let ready := cheapCheck (n := n) first level prepared
        let tv := cell.nextElem none
        let (exit, index, out) := next first level nc tc.toNat (tv.getD 0) tv cell 0 ready
        match exit with
        | .done => return (Generic.Exit.unwind (level - 1) false,
            Generic.Policy.afterSweep (n := n) first level size index out)
        | _ => return (exit, out))).2.fixedpts = st.fixedpts := by
    intro prepared hp htarg hf he
    have hcheap := hp.cheap first
    have hche := cheap_fixed first level prepared
    have hout := hnext first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 _
      ⟨hl, hcheap.ready, htarg.of_out hcheap.frame.effect,
        (fun _ hv => VSet.nextElem_mem hv), hf.ofEffect hche hcheap.frame.effect⟩
    dsimp only
    generalize hcall : next first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (cheapCheck (n := n) first level prepared) = r at hout ⊢
    obtain ⟨exit, index, out⟩ := r
    have hall := hout.trans (hche.trans he)
    cases exit
    · exact (afterSweep_fixed first level size index out).trans hall
    · exact hall
    · exact hall
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact heq
    · exact hfinish targeted ht.ready htarget htf heq
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hcl := ht.ready.classify
    have hcle := classify_fixed (.ofGraph G.graph) level nc targeted
    generalize he : classify (.ofGraph G.graph) level nc targeted = r at hcl hcle ⊢
    obtain ⟨leaf, classified⟩ := r
    have hclf := htf.ofEffect hcle hcl.frame.effect
    have hleaf := hcl.ready.leaf leaf
    have hle := leaf_fixed leaf level classified
    generalize he : leafExit (n := n) leaf level classified = r at hleaf hle ⊢
    obtain ⟨exit, out⟩ := r
    have hall := hle.trans (hcle.trans heq)
    cases exit
    · exact hfinish out hleaf.ready ((htarget.of_out hcl.frame.effect).of_out hleaf.frame.effect)
        (hclf.ofEffect hle hleaf.frame.effect) hall
    · exact hall
    · exact hall

end Hex.GraphIso.Nauty.Sparse
