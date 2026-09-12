/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.StoreSearch
public import HexGraphIso.Nauty.Sparse.FirstPath
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

theorem chooseTarget_rows (first : Bool) (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (chooseTarget first g tcLevel level numcells st).2.2.2.canong.toRows = st.canong.toRows := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n => out.2.2.2.canong.toRows = st.canong.toRows)
  mvcgen
  all_goals simp_all +zetaDelta

theorem prepareFirst_rows (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2.canong.toRows = st.canong.toRows := by
  unfold Generic.prepareFirst
  change (chooseTarget true g tcLevel level _ _).2.2.2.canong.toRows = _
  rw [chooseTarget_rows]
  rfl

/-- Before the first leaf, the actual first descent retains the literal
canonical row allocation while refinement continues to reuse its scratch. -/
theorem firstPath_rows {g : Graph n} {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf) :
    leaf.canong.toRows = st.canong.toRows := by
  induction path with
  | leaf fuel level numcells st hdisc => exact prepareFirst_rows g tcLevel level numcells st
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    rw [ih]
    change (cheapCheck true level (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2).canong.toRows = _
    unfold cheapCheck
    split <;> exact prepareFirst_rows g tcLevel level numcells st

/-- The native initial allocation is a valid empty prefix for every label
of its input graph. Its capacity equals the graph's directed edge count. -/
theorem blank_prefix (G : Hex.SparseGraph n) (l : Label n) :
    (Graph.ofGraph G).blank.Prefix (G.relabel l.perm) 0 := by
  refine ⟨Nat.zero_le _, by simp [Graph.blank], ?_, ?_, fun _ hi => by omega⟩
  · simp [Graph.blank, Graph.ofGraph]
  · intro i hi
    have he : i = 0 := by omega
    subst i
    rw [(G.relabel l.perm).offset_zero]
    simp [Graph.blank]

/-- The first terminal installs its checked current label with an empty
prefix in the retained initial allocation. -/
theorem firstterminal_store (G : Hex.SparseGraph n) (level : Nat) (st : State n) (l : Label n)
    (hl : Label.ofArray? n st.lab = some l) (hb : st.canong.toRows = (Graph.ofGraph G).blank) :
    Store G (firstterminal level st) := by
  refine ⟨l, ?_, ?_⟩
  · unfold firstterminal
    exact hl
  · unfold firstterminal
    change st.canong.toRows.Prefix (G.relabel l.perm) 0
    rw [hb]
    exact blank_prefix G l

/-- The first descent initializes the native store at its first leaf;
the already-proved recursive store contract covers every later sibling. -/
theorem firstPath_store {G : GraphIso.Sparse.Colored n k} (hn : 0 < n)
    {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel level numcells st last leaf)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st)
    (hb : st.canong.toRows = (Graph.ofGraph G.graph).blank) :
    Store G.graph (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    let prepared : State n := (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).2.2.2.2
    have hp : Ready G level (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).1 prepared :=
      (h.prepare (tcLevel := tcLevel) hn hl).1
    obtain ⟨l, hlab⟩ := hp.parse hn
    have ht := firstterminal_store G.graph level prepared l hlab
      ((prepareFirst_rows (.ofGraph G.graph) tcLevel level numcells st).trans hb)
    dsimp only [prepared] at ht
    unfold Generic.prepareFirst at hdisc ht
    dsimp only at hdisc
    rw [Generic.node]
    unfold Generic.nodeStep
    dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
      Generic.Policy.chooseTarget, Generic.Policy.firstterminal] at hdisc ht ⊢
    simpa only [ite_true, hdisc, beq_self_eq_true, Id.run_pure] using ht
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    obtain ⟨hr, ht⟩ := h.prepare (tcLevel := tcLevel) hn hl
    have hcheap := hr.cheap true
    have htarget := ht.of_out hcheap.frame.effect
    have hmem := VSet.nextElem_mem htv
    have hchild := hcheap.ready.child hn hl true htarget hmem
    have hblank : ((policy (n := n)).child true level r.2.1.toNat tv
        (cheapCheck true level r.2.2.2.2)).canong.toRows = (Graph.ofGraph G.graph).blank := by
      change (cheapCheck true level r.2.2.2.2).canong.toRows = _
      unfold cheapCheck
      split <;> exact (prepareFirst_rows (.ofGraph G.graph) tcLevel level numcells st).trans hb
    have hc := ih (by omega) hchild hblank
    have hs := sweep_first_store G hn tcLevel fuel n level r.1 r.2.1.toNat tv 0
      r.2.2.1 _ hl hcheap.ready htarget hmem horbit hc
    rw [Generic.node]
    unfold Generic.nodeStep
    change Store G.graph (Id.run do
      let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      if r.1 == n then
        return (.unwind (level - 1) false, Generic.Policy.firstterminal (n := n) level r.2.2.2.2)
      let s := Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        level r.1 r.2.1.toNat ((r.2.2.1.nextElem none).getD 0)
        (r.2.2.1.nextElem none) r.2.2.1 0
        (Generic.Policy.cheapCheck (n := n) true level r.2.2.2.2)
      match s.1 with
      | .done => return (.unwind (level - 1) false,
          Generic.Policy.afterSweep (n := n) true level r.2.2.2.1 s.2.1 s.2.2)
      | _ => return (s.1, s.2.2)).2
    simp only [beq_eq_false_iff_ne.mpr hopen, Bool.false_eq_true, ite_false, htv, Option.getD_some]
    generalize he : Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
      level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0
      (Generic.Policy.cheapCheck (n := n) true level r.2.2.2.2) = result at hs ⊢
    obtain ⟨exit, index, out⟩ := result
    cases exit with
    | fuel => exact hs
    | unwind => exact hs
    | done => exact hs.afterSweep true level r.2.2.2.1 index

end Hex.GraphIso.Nauty.Sparse
