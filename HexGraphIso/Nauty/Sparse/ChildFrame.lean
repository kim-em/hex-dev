/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReadyFrame
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Ready

variable {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}

/-- Every surviving target member establishes the complete production child
entry invariant. The certificate is derived from parent equitability. -/
theorem child (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first : Bool) {tc tv : Nat} {cell : VSet n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    NodeInv G (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st) := by
  obtain ⟨len, ht, hm⟩ := ht
  obtain ⟨hc, hlen, hb⟩ := ht (mem_ne_empty hv)
  obtain ⟨o, ho, he⟩ := mem_segN_iff.mp (hm tv hv)
  change st.lab[tc + o]! = tv at he
  have hp := isPerm_of_cellsReach h.ok.labSize hn h.ok.reach
  let base : State n := { st with active := VSet.empty }
  have hsame : (policy (n := n)).child first level tc tv base =
      (policy (n := n)).child first level tc tv st := by cases first <;> rfl
  have hentry := child_entry G.graph first level numcells tc len o base hp
    (h.partition hn hl) h.scratch.toBounded (Nat.le_trans h.ok.bc (bcount_le _ _ _))
    h.ok.count h.equitable hc hb (by omega) ho
  change st.lab[tc + o]! = tv at he
  dsimp only [base] at hentry
  rw [he] at hentry
  change _ ∧ _ ∧ _ ∧ _ ∧ _ at hentry
  change (policy (n := n)).child first level tc tv { st with active := VSet.empty } = _ at hsame
  rw [hsame] at hentry
  let out := (policy (n := n)).child first level tc tv st
  have hf := child_fields first level tc tv st
  have hcanon : out.canonlab = st.canonlab := by cases first <;> rfl
  refine ⟨⟨hentry.1, hentry.2.1, hentry.2.2.2.1, ?_, hentry.2.2.2.2⟩, ?_, hentry.2.2.1.toBounded⟩
  · have hh := h.ok.bc
    have hc := h.ok.count
    omega
  · exact breakout_searchOk hn h.ok hl hc hlen hb ho
      (by simpa only [State.frame, he] using hf.1) hf.2.1 hcanon

/-- A child's return composes with individualization to preserve the parent
frame, including references installed anywhere below the child. -/
theorem child_frame (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first : Bool) {tc tv : Nat} {cell : VSet n} {out : State n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hx : FrameOut G level (level + 1) ((policy (n := n)).child first level tc tv st) out) :
    FrameOut G level level st out := by
  obtain ⟨len, ht, hm⟩ := ht
  obtain ⟨hc, hlen, hb⟩ := ht (mem_ne_empty hv)
  obtain ⟨o, ho, he⟩ := mem_segN_iff.mp (hm tv hv)
  change st.lab[tc + o]! = tv at he
  have hf := child_fields first level tc tv st
  refine ⟨breakout_child_out hn h.ok hl hc hlen hb ho hx.effect ?_ hf.2.1 ?_ ?_, hx.scratch⟩
  · change ((policy (n := n)).child first level tc tv st).lab = _
    simpa only [State.frame, he] using hf.1
  · cases first <;> rfl
  · cases first <;> rfl

end Hex.GraphIso.Nauty.Sparse.Ready
