/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.StateFrame
public import HexGraphIso.Nauty.Sparse.RefineFrame

public section

namespace Hex.GraphIso.Nauty.Sparse.NodeInv

variable {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}

/-- A production visit establishes the equitable parent invariant and a
valid cache, retaining exact counts and original colour-cell boundaries. -/
theorem visit_ready (h : NodeInv G level numcells st) (hn : 0 < n) (hl : 1 ≤ level) :
    let r := visit (.ofGraph G.graph) level numcells st
    Ready G level r.1 r.2.2 := by
  let r := refineWith (.ofGraph G.graph) level st.lab st.ptn st.active numcells st.canong.scratch
  have hend : st.ptn[n - 1]! ≤ level := by simpa only [h.spec.node.ptnSize] using h.spec.node.ptnEnd
  have hr := refineWith_state G.graph level st.lab st.ptn st.active numcells st.canong.scratch
    h.spec.label h.spec.node.ptnSize hend h.spec.node.starts h.scratch
  have hb := refineWith_boundary (.ofGraph G.graph) level st.lab st.ptn st.active numcells st.canong.scratch
  have hcount : r.numcells = bcount r.ptn level n := refineWith_count G.graph level st.lab st.ptn
    st.active numcells st.canong.scratch h.spec.label h.spec.node.ptnSize hend h.spec.node.starts h.scratch h.spec.count
  have hmono : numcells ≤ r.numcells := by
    have hb := bcount_mono (fun q hq => hb.closed hq) (nn := n)
    change bcount st.ptn level n ≤ bcount r.ptn level n at hb
    rw [← hcount, ← h.spec.count] at hb
    exact hb
  refine ⟨?_, ?_, hr.2.2.2.2.2⟩
  · refine ⟨?_, hr.2.1, ?_, ?_, ?_, hcount, ?_, h.ok.canon⟩
    · change r.lab.size = n
      have hp : r.lab.toList.Perm (List.range n) := hr.1
      simpa only [Array.length_toList, List.length_range] using hp.length_eq
    · exact visit_cellsReach G hn level numcells st h.spec.label h.spec.node h.scratch h.ok.reach
        (fun q hq => Nat.le_trans (h.ok.init1 q hq) hl)
    · intro q hq
      have hh := h.ok.init1 q hq
      change st.ptn[q]! ≤ 1 at hh
      change r.ptn[q]! ≤ 1
      rw [hr.2.2.1.closed q (by omega)]
      exact hh
    · intro q hq
      change r.ptn[q]! ≤ level ∨ r.ptn[q]! = n + 2
      rcases hb.values q with he | he
      · rw [he]
        exact h.ok.vals q hq
      · exact Or.inl (by rw [he]; exact Nat.le_refl _)
    · change level ≤ bcount r.ptn level n
      rw [← hcount]
      exact Nat.le_trans h.spec.depth hmono
  · exact refineWith_equitable G.graph level st.lab st.ptn st.active numcells st.canong.scratch
      h.spec.label h.spec.node.ptnSize hend h.spec.node.starts h.scratch h.spec.count h.spec.cert

/-- Compose an executed refinement with the rest of its node. New cuts are
below the receiving ancestor, while labels and stored references stay within
the caller's cells. This follows the sparse operation's actual write sites. -/
theorem visit_frame (h : NodeInv G level numcells st) (hl : 1 ≤ level) {out : State n}
    (hx : FrameOut G level level (visit (.ofGraph G.graph) level numcells st).2.2 out) :
    FrameOut G (level - 1) level st out := by
  let r := (visit (.ofGraph G.graph) level numcells st).2.2
  have hend : st.ptn[n - 1]! ≤ level := by simpa only [h.spec.node.ptnSize] using h.spec.node.ptnEnd
  have ht := refineWith_state G.graph level st.lab st.ptn st.active numcells st.canong.scratch
    h.spec.label h.spec.node.ptnSize hend h.spec.node.starts h.scratch
  have hb := refineWith_boundary (.ofGraph G.graph) level st.lab st.ptn st.active numcells st.canong.scratch
  have hrs : r.lab.size = n := by
    have hp : r.lab.toList.Perm (List.range n) := ht.1
    simpa only [Array.length_toList, List.length_range] using hp.length_eq
  have hps : r.ptn.size = n := ht.2.1
  have hclosed : ∀ q, st.ptn[q]! ≤ level → r.ptn[q]! = st.ptn[q]! := ht.2.2.1.closed
  have hlast : r.ptn[r.ptn.size - 1]! ≤ level := by rw [hps, hclosed _ hend]; exact hend
  have hp : cellsPerm st.ptn level st.lab r.lab := cellsPerm_symm ht.2.2.2.1
  have liftPerm : ∀ {lab : Array Nat}, lab.size = r.lab.size → cellsPerm r.ptn level r.lab lab →
      cellsPerm st.ptn level r.lab lab := by
    intro lab hsize hperm
    exact cellsPerm_coarsen (h.spec.node.ptnSize.trans hps.symm) (hrs.trans hps.symm)
      (hsize.trans (hrs.trans hps.symm)) hperm hlast h.spec.node.ptnEnd
      (fun q hq => by rw [hclosed q hq]; exact hq)
  refine ⟨⟨?_, ?_, hx.effect.reach, ?_, ?_, ?_, ?_, hx.effect.canon⟩, hx.scratch⟩
  · exact hx.effect.labSize.trans (hrs.trans h.spec.node.labSize.symm)
  · exact hx.effect.ptnSize.trans (hps.trans h.spec.node.ptnSize.symm)
  · intro q hq
    change st.ptn[q]! ≤ level - 1 ∨ out.ptn[q]! ≤ level - 1 at hq
    change out.ptn[q]! = st.ptn[q]!
    rcases hq with hq | hq
    · have he := hclosed q (by omega)
      exact (hx.effect.low q (Or.inl (by change r.ptn[q]! ≤ level; rw [he]; omega))).trans he
    · have he := hx.effect.low q (Or.inr (by change out.ptn[q]! ≤ level; omega))
      change out.ptn[q]! = r.ptn[q]! at he
      rw [he] at hq ⊢
      rcases hb.values q with hv | hv
      · exact hv
      · change r.ptn[q]! = level at hv
        omega
  · exact cellsPerm_trans hp (liftPerm hx.effect.labSize hx.effect.perm)
  · rcases hx.effect.firstStore with he | he
    · exact Or.inl he
    · exact Or.inr ⟨he.1.trans (hrs.trans h.spec.node.labSize.symm), cellsPerm_trans hp (liftPerm he.1 he.2)⟩
  · rcases hx.effect.canonStore with he | he
    · exact Or.inl he
    · exact Or.inr ⟨he.1.trans (hrs.trans h.spec.node.labSize.symm), cellsPerm_trans hp (liftPerm he.1 he.2)⟩

end Hex.GraphIso.Nauty.Sparse.NodeInv
