/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.AncestorStab
public import HexGraphIso.Nauty.Sparse.FrameReturn
public import HexGraphIso.Nauty.Sparse.CanonScatter
import all HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A suspended first-path partition contains the current and saved labels,
and is stabilized by every emitted generator. The workspace bound justifies
the literal reference scatters used to extend the trace. -/
structure TraceFrame (G : GraphIso.Sparse.Colored n k) (base : Nat) (root st : State n) : Prop where
  frame : FrameOut G base base root st
  first : st.firstlab.size = n ∧ cellsPerm root.ptn base root.lab st.firstlab
  canon : st.canonlab.size = n ∧ cellsPerm root.ptn base root.lab st.canonlab
  trace : ∀ gamma ∈ st.genTrace, CellStab root.ptn base root.lab gamma
  work : st.workperm.size = n

namespace TraceFrame

variable {G : GraphIso.Sparse.Colored n k} {base numcells : Nat} {root st out : State n}

/-- Cell membership in the frozen partition makes either saved reference
a full permutation, supplying the precondition of the executed scatter. -/
theorem label_perm (hroot : Ready G base numcells root) (hn : 0 < n) (hb : 1 ≤ base)
    {lab : Array Nat} (hs : lab.size = n) (hp : cellsPerm root.ptn base root.lab lab) :
    lab.toList.Perm (List.range n) := by
  have hsize : root.ptn.size = n := hroot.ok.ptnSize
  have hend : root.ptn[root.ptn.size - 1]! ≤ base := searchOk_end hn hroot.ok hb
  have hc := cellsPerm_segN_perm hp (Nat.le_of_eq hsize.symm) hend
    (by rwa [hsize] at hend)
  rw [segN_eq_toList (show root.lab.size = n from hroot.ok.labSize), segN_eq_toList hs] at hc
  exact hc.symm.trans (isPerm_of_cellsReach hroot.ok.labSize hn hroot.ok.reach)

/-- An effect at the frozen level transports both reference-store
alternatives. Only new trace entries require a separate stabilization proof. -/
theorem of_effect (h : TraceFrame G base root st) (hp : Ready G base numcells root)
    (he : FrameOut G base base st out)
    (ht : ∀ gamma ∈ out.genTrace, CellStab root.ptn base root.lab gamma)
    (hw : out.workperm.size = n) : TraceFrame G base root out := by
  have carry {lab : Array Nat} (hs : lab.size = st.lab.size)
      (hc : cellsPerm st.ptn base st.lab lab) :
      lab.size = n ∧ cellsPerm root.ptn base root.lab lab := by
    refine ⟨hs.trans (h.frame.effect.labSize.trans hp.ok.labSize), ?_⟩
    apply cellsPerm_trans h.frame.effect.perm
    intro a len hcell
    exact hc a len (isCell_of_low h.frame.effect.low hcell)
  refine ⟨h.frame.trans he, ?_, ?_, ht, hw⟩
  · rcases he.effect.firstStore with heq | ⟨hs, hc⟩
    · change out.firstlab = st.firstlab at heq
      rw [heq]
      exact h.first
    · exact carry hs hc
  · rcases he.effect.canonStore with heq | ⟨hs, hc⟩
    · change out.canonlab = st.canonlab at heq
      rw [heq]
      exact h.canon
    · exact carry hs hc

/-- Effects below a suspended ancestor preserve its references as well
as its frame, including complete calls and nonlocal returns. -/
theorem extend (h : TraceFrame G base root st) (hp : Ready G base numcells root)
    (hn : 0 < n) (hpos : 1 ≤ base) {bound level : Nat}
    (he : FrameOut G bound level st out) (hb : base ≤ bound) (hl : base ≤ level)
    (ht : ∀ gamma ∈ out.genTrace, CellStab root.ptn base root.lab gamma)
    (hw : out.workperm.size = n) : TraceFrame G base root out := by
  have hsize : st.lab.size = n := h.frame.effect.labSize.trans hp.ok.labSize
  have hptn : st.ptn.size = n := h.frame.effect.ptnSize.trans hp.ok.ptnSize
  have hps : st.ptn.size = root.ptn.size := h.frame.effect.ptnSize
  have hpEnd : root.ptn[root.ptn.size - 1]! ≤ base := searchOk_end hn hp.ok hpos
  have hclosed : st.ptn[root.ptn.size - 1]! = root.ptn[root.ptn.size - 1]! :=
    h.frame.effect.low _ (Or.inl hpEnd)
  have hend : st.ptn[st.ptn.size - 1]! ≤ base := by rw [hps, hclosed]; exact hpEnd
  exact h.of_effect hp (he.coarsen hb hl hsize hptn hend) ht hw

/-- Bookkeeping retaining labels, partition, trace and workspace transports
the entire frozen-ancestor invariant. Scratch validity is supplied by its
native operation contract. -/
theorem fields (h : TraceFrame G base root st)
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (hf : out.firstlab = st.firstlab) (hc : out.canonlab = st.canonlab)
    (ht : out.genTrace = st.genTrace) (hw : out.workperm.size = st.workperm.size)
    (hs : Scratch.Bounded n out.canong.scratch) : TraceFrame G base root out := by
  refine ⟨h.frame.congr hl hp hf hc hs, ?_, ?_, ?_, hw.trans h.work⟩
  · rw [hf]; exact h.first
  · rw [hc]; exact h.canon
  · rw [ht]; exact h.trace

end TraceFrame
end Hex.GraphIso.Nauty.Sparse
