/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReadyFrame
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Local bookkeeping preserves the equitable parent and its call frame. -/
structure Local (G : GraphIso.Sparse.Colored n k) (level numcells : Nat) (st out : State n) : Prop where
  ready : Ready G level numcells out
  frame : FrameOut G level level st out

namespace Local

theorem trans {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st mid out : State n}
    (h : Local G level numcells st mid) (h' : Local G level numcells mid out) :
    Local G level numcells st out := ⟨h'.ready, h.frame.trans h'.frame⟩

end Local

namespace Ready

variable {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}

theorem step (h : Ready G level numcells st) {out : State n}
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (hf : out.firstlab = st.firstlab ∨ out.firstlab = st.lab)
    (hc : out.canonlab = st.canonlab ∨ out.canonlab = st.lab)
    (hs : Scratch.Valid n out.lab out.ptn level out.canong.scratch) : Local G level numcells st out :=
  ⟨h.of_frame hl hp hc hs, h.frame hl hp hf hc hs.toBounded⟩

theorem record (h : Ready G level numcells st) (code : Nat) :
    Local G level numcells st (recordFirst level code st) :=
  h.step rfl rfl (Or.inl rfl) (Or.inl rfl) h.scratch

theorem compare (h : Ready G level numcells st) (code : Nat) :
    Local G level numcells st (compareCodes level code st) := by
  obtain ⟨hl, hp, hf, hc⟩ := compareCodes_frame level code st
  apply h.step hl hp (Or.inl hf) (Or.inl hc)
  rw [hl, hp, SearchState.compare_storage]
  exact h.scratch

theorem terminal (h : Ready G level numcells st) :
    Local G level numcells st (firstterminal level st) := by
  have hl : (firstterminal level st).lab = st.lab := by unfold firstterminal; rfl
  have hp : (firstterminal level st).ptn = st.ptn := by unfold firstterminal; rfl
  have hf : (firstterminal level st).firstlab = st.lab := by unfold firstterminal; rfl
  have hc : (firstterminal level st).canonlab = st.lab := by unfold firstterminal; rfl
  apply h.step hl hp (Or.inr hf) (Or.inr hc)
  rw [hl, hp, SearchState.terminal_storage]
  exact h.scratch

theorem leaf (h : Ready G level numcells st) (leaf : Leaf) :
    Local G level numcells st (leafExit leaf level st).2 := by
  obtain ⟨hl, hp, hf, hc⟩ := leafExit_frame leaf level st
  apply h.step hl hp (Or.inl hf) hc
  rw [hl, hp, SearchState.leaf_storage]
  exact h.scratch

theorem cheap (h : Ready G level numcells st) (first : Bool) :
    Local G level numcells st (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h.step rfl rfl (Or.inl rfl) (Or.inl rfl) h.scratch

end Ready
end Hex.GraphIso.Nauty.Sparse
