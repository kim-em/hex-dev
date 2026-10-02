/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FrameOps
public import HexGraphIso.Nauty.Policy.EquitableState
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Ready

variable {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}

/-- Bookkeeping with an unchanged partition preserves the equitable parent
invariant, including optional installation of the current canonical label. -/
theorem of_frame (h : Ready G level numcells st) {out : State n}
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (hc : out.canonlab = st.canonlab ∨ out.canonlab = st.lab)
    (hs : Scratch.Valid n out.lab out.ptn level out.canong.scratch) :
    Ready G level numcells out := by
  refine ⟨frame_ok h.ok hl hp hc, ?_, hs⟩
  rw [hl, hp]
  exact h.equitable

theorem frame (h : Ready G level numcells st) {out : State n}
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (hf : out.firstlab = st.firstlab ∨ out.firstlab = st.lab)
    (hc : out.canonlab = st.canonlab ∨ out.canonlab = st.lab)
    (hs : Scratch.Bounded n out.canong.scratch) : FrameOut G level level st out :=
  ⟨frame_out h.ok hl hp hf hc, hs⟩

/-- The parent's structural partition facts do not depend on the stale
active set left by a completed descendant. -/
theorem partition (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level) :
    NodeOk n level st.lab st.ptn VSet.empty := by
  refine ⟨h.ok.labSize, ?_, h.ok.ptnSize, searchOk_end hn h.ok hl, ?_, ?_⟩
  · intro i hi
    exact cellsReach_lt h.ok.reach i (by have := h.ok.labSize; change st.lab.size = n at this; omega)
  · intro v hv
    simp at hv
  · intro q
    by_cases hq : q < n
    · exact h.ok.vals q hq
    · left
      have hs : st.ptn.size ≤ q := by have := h.ok.ptnSize; change st.ptn.size = n at this; omega
      rw [getElem!_neg st.ptn q (by omega)]
      exact Nat.zero_le _

/-- A returned child is recovered to the exact parent partition. Reordering
within its cells preserves equitability; the real policy invalidates indices. -/
theorem recover (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    {out : State n} (hx : FrameOut G level level st out) :
    let r := (policy (n := n)).recover (n + 2) level out
    Ready G level numcells r ∧ FrameOut G level level st r := by
  have hbound : level + 1 < n + 2 := by
    have hb := Nat.le_trans h.ok.bc (bcount_le _ _ _)
    omega
  have hr := hx.effect.trans (recover_out hbound hx.effect.reach)
  rw [← State.recover_frame] at hr
  have hv := recover_valid (n + 2) level out hx.scratch
  refine ⟨⟨?_, ?_, hv⟩, ⟨hr, hv.toBounded⟩⟩
  · apply searchOk_of_out h.ok hl hr
    intro q hq
    rw [State.recover_frame, recover_ptn]
    split
    · exact Or.inr rfl
    · exact Or.inl (by omega)
  · change Equitable (Graph.context G.graph) level
      ((policy (n := n)).recover (n + 2) level out).frame.lab
      ((policy (n := n)).recover (n + 2) level out).frame.ptn
    rw [State.recover_frame]
    exact recover_equitable hn hl h.ok h.equitable hx.effect

end Hex.GraphIso.Nauty.Sparse.Ready
