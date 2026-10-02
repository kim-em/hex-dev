/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.StoreSweep
import all HexGraphIso.Nauty.Policy.Generic.Sound

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The complete production recursion preserves native canonical prefixes
and its partition frames, independently of any maximality claim. -/
theorem storePolicy (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel : Nat) :
    Generic.SoundPolicy (.ofGraph G.graph) (n + 2) tcLevel (storeContract G) where
  node_zero := fun _ _ _ _ hin => ⟨FrameOut.refl hin.2, fun hs => hs⟩
  node_step := by
    intro fuel next hnext first level numcells st hin
    exact ⟨reach_node G hn tcLevel (store_sweep_reach hnext) first level numcells st hin.1 hin.2,
      store_node G hn tcLevel hnext first level numcells st hin.1 hin.2⟩
  sweep_none := by
    intro fuel cfuel first level numcells tc tv1 cell index st hin
    exact ⟨hin.2.1.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hin.2.1.scratch.toBounded, fun hs => hs⟩
  sweep_zero := by
    intro fuel first level numcells tc tv1 tv cell index st hin
    exact ⟨hin.2.1.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hin.2.1.scratch.toBounded, fun hs => hs⟩
  sweep_step := by
    intro fuel cfuel descend next hd hnext first level numcells tc tv1 tv cell index st hin
    exact ⟨reach_sweep G hn (store_node_reach hd) (store_sweep_reach hnext)
      first level numcells tc tv1 tv index cell st hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl),
      store_sweep G hn hd hnext first level numcells tc tv1 tv index cell st
        hin.1 hin.2.1 hin.2.2.1 (hin.2.2.2 tv rfl)⟩

theorem node_store (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (first : Bool) (tcLevel fuel level numcells : Nat) (st : State n)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st) (hs : Store G.graph st) :
    Store G.graph (Generic.node first (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 :=
  (Generic.node_sound (storePolicy G hn tcLevel) first fuel level numcells st ⟨hl, h⟩).2 hs

theorem sweep_store (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (first : Bool) (tcLevel fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : State n) (hl : 1 ≤ level)
    (h : Ready G level numcells st) (ht : Generic.Target State.frame level tc cell st)
    (hv : ∀ v, cursor = some v → cell.mem v = true) (hs : Store G.graph st) :
    Store G.graph (Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel
      level numcells tc tv1 cursor cell index st).2.2 :=
  (Generic.sweep_sound (storePolicy G hn tcLevel) first fuel cfuel level numcells tc tv1 cursor cell index st
    ⟨hl, h, ht, hv⟩).2 hs

/-- A store established by the first child survives its entire receiving
sweep, even though the parent had no installed label before that child. -/
theorem sweep_first_store (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (tcLevel fuel cfuel level numcells tc tv index : Nat) (cell : VSet n) (st : State n)
    (hl : 1 ≤ level) (h : Ready G level numcells st)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (horbit : Generic.Policy.orbit (n := n) st tv = tv)
    (hs : Store G.graph (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child true level tc tv st)).2) :
    Store G.graph (Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (cfuel + 1)
      level numcells tc tv (some tv) cell index st).2.2 := by
  have hd := node_frame G hn true tcLevel fuel (level + 1) (numcells + 1) _
    (by omega) (h.child hn hl true ht hv)
  rw [Generic.sweep]
  unfold Generic.sweepStep
  simp only [Bool.not_true, horbit, beq_self_eq_true, Bool.or_true, Bool.and_self, ite_true]
  generalize he : Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel
    (level + 1) (numcells + 1) ((policy (n := n)).child true level tc tv st) = r at hd hs ⊢
  obtain ⟨exit, out⟩ := r
  have hp := h.child_frame hn hl true ht hv hd
  apply store_advance G hn (fun first level numcells tc tv1 cursor cell index st hin =>
    Generic.sweep_sound (storePolicy G hn tcLevel) first fuel cfuel level numcells tc tv1 cursor cell index st hin)
    true level numcells tc tv tv index cell st _ exit hl h ht
    ((hp.afterChild level tv).leave tv)
  exact (hs.afterChild level tv).leave tv

end Hex.GraphIso.Nauty.Sparse
