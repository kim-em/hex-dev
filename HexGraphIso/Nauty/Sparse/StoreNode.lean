/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.StoreOps
public import HexGraphIso.Nauty.Sparse.Reach
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every well-formed call preserves its partition frame and any installed
native canonical store. The implication permits the independent first-descent
argument to seed that store at the actual first leaf. -/
@[expose] def storeContract (G : GraphIso.Sparse.Colored n k) : Generic.Contract (State n) n where
  nodePre := (reachContract G).nodePre
  nodePost fuel first level numcells st out :=
    (reachContract G).nodePost fuel first level numcells st out ∧ (Store G.graph st → Store G.graph out.2)
  sweepPre := (reachContract G).sweepPre
  sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st out :=
    (reachContract G).sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st out ∧
      (Store G.graph st → Store G.graph out.2.2)

theorem store_node_reach {G : GraphIso.Sparse.Colored n k} {fuel : Nat} {descend : Generic.NodeFn (State n)}
    (h : (storeContract G).nodeValid fuel descend) : (reachContract G).nodeValid fuel descend :=
  fun first level numcells st hin => (h first level numcells st hin).1

theorem store_sweep_reach {G : GraphIso.Sparse.Colored n k} {fuel cfuel : Nat}
    {next : Generic.SweepFn (State n) n} (h : (storeContract G).sweepValid fuel cfuel next) :
    (reachContract G).sweepValid fuel cfuel next :=
  fun first level numcells tc tv1 cursor cell index st hin =>
    (h first level numcells tc tv1 cursor cell index st hin).1

theorem Ready.parse {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}
    (h : Ready G level numcells st) (hn : 0 < n) : ∃ l, Label.ofArray? n st.lab = some l :=
  Label.ofArray?_exists (isPerm_of_cellsReach h.ok.labSize hn h.ok.reach)

/-- Actual node preparation, classification and leaf installation preserve
the native canonical prefix, before passing it to the child continuation. -/
theorem store_node (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel : Nat)
    {fuel : Nat} {next : Generic.SweepFn (State n) n}
    (hnext : (storeContract G).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells : Nat) (st : State n)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st) (hs : Store G.graph st) :
    Store G.graph (Generic.nodeStep (.ofGraph G.graph) tcLevel next first level numcells st).2 := by
  have hv := h.visit_ready hn hl
  have hvs := hs.visit level numcells
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst, Generic.Policy.compareCodes,
    Generic.Policy.chooseTarget, Generic.Policy.firstterminal, Generic.Policy.classify,
    Generic.Policy.leafExit, Generic.Policy.cheapCheck]
  generalize he : visit (.ofGraph G.graph) level numcells st = r at hv hvs ⊢
  obtain ⟨nc, code, refined⟩ := r
  let compared := if first then recordFirst (n := n) level code refined else compareCodes (n := n) level code refined
  have hc : Local G level nc refined compared := by
    cases first
    · exact hv.compare code
    · exact hv.record code
  have hcs : Store G.graph compared := by
    cases first
    · exact hvs.compare level code
    · exact hvs.record level code
  have ht := hc.ready.target_frame first tcLevel
  have htarget := hc.ready.target hn hl first tcLevel
  have hts := hcs.target first tcLevel level nc
  dsimp only
  generalize he : chooseTarget first (.ofGraph G.graph) tcLevel level nc compared = r at ht htarget hts ⊢
  obtain ⟨tc, cell, size, targeted⟩ := r
  have hfinish : ∀ prepared, Ready G level nc prepared →
      Generic.Target State.frame level tc.toNat cell prepared → Store G.graph prepared →
      Store G.graph (Id.run (do
        let ready := cheapCheck (n := n) first level prepared
        let tv := cell.nextElem none
        let (exit, index, out) := next first level nc tc.toNat (tv.getD 0) tv cell 0 ready
        match exit with
        | .done => return (Generic.Exit.unwind (level - 1) false,
            Generic.Policy.afterSweep (n := n) first level size index out)
        | _ => return (exit, out))).2 := by
    intro prepared hp htarg hstore
    have hcheap := hp.cheap first
    have hout := (hnext first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 _
      ⟨hl, hcheap.ready, htarg.of_out hcheap.frame.effect, fun _ hv => VSet.nextElem_mem hv⟩).2
      (hstore.cheap first level)
    dsimp only
    generalize he : next first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (cheapCheck (n := n) first level prepared) = r at hout ⊢
    obtain ⟨exit, index, out⟩ := r
    cases exit
    · exact hout.afterSweep first level size index
    · exact hout
    · exact hout
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · obtain ⟨l, hlab⟩ := ht.ready.parse hn
      exact hts.terminal level l hlab
    · exact hfinish targeted ht.ready htarget hts
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    obtain ⟨l, hlab⟩ := ht.ready.parse hn
    have hc' := ht.ready.classify
    have hsc := hts.classify level nc l hlab
    generalize he : classify (.ofGraph G.graph) level nc targeted = r at hc' hsc ⊢
    obtain ⟨leaf, classified⟩ := r
    have he' := hc'.ready.leaf leaf
    have hsl := hsc.1.leaf leaf level hsc.2
    generalize he : leafExit (n := n) leaf level classified = r at he' hsl ⊢
    obtain ⟨exit, out⟩ := r
    cases exit
    · exact hfinish out he'.ready ((htarget.of_out hc'.frame.effect).of_out he'.frame.effect) hsl
    · exact hsl
    · exact hsl

end Hex.GraphIso.Nauty.Sparse
