/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CanonLabel
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The first leaf installs a valid incumbent, and all ancestor sweeps
retain its validity throughout the actual remaining production search. -/
theorem firstPath_canonical {G : GraphIso.Sparse.Colored n k} (hn : 0 < n)
    {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel level numcells st last leaf)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st) :
    CanonLabel G (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    have ht := (h.prepare (tcLevel := tcLevel) hn hl).1.canonical
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
    have hc := ih (by omega) hchild
    have hs := sweep_first_canonical G hn tcLevel fuel n level r.1 r.2.1.toNat tv 0
      r.2.2.1 _ hl hcheap.ready htarget hmem horbit hc
    rw [Generic.node]
    unfold Generic.nodeStep
    change CanonLabel G (Id.run do
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
    simp only [beq_eq_false_iff_ne.mpr hopen, Bool.false_eq_true, ite_false,
      htv, Option.getD_some]
    generalize he : Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
      level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0
      (Generic.Policy.cheapCheck (n := n) true level r.2.2.2.2) = result at hs ⊢
    obtain ⟨exit, index, out⟩ := result
    cases exit with
    | fuel => exact hs
    | unwind => exact hs
    | done =>
      apply hs.congr
      change (Nauty.afterSweep true level r.2.2.2.1 index out).canonlab = out.canonlab
      unfold Nauty.afterSweep
      split <;> rfl

/-- The nonempty production root returns an installed, colour-respecting
canonical label. The initializer supplies all first-descent premises. -/
theorem runState_canonical (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    CanonLabel G (runState (.ofGraph G.graph) p.1 p.2).2 := by
  obtain ⟨last, leaf, path, _, _⟩ := initial_path G hn
  dsimp only
  rw [runState, ite_eq_right (by simpa using Nat.ne_of_gt hn)]
  exact firstPath_canonical hn path (by omega) (NodeInv.initial G hn)

end Hex.GraphIso.Nauty.Sparse
