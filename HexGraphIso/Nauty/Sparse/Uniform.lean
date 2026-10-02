/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.LeafPath
import all HexGraphIso.Nauty.Sparse.LeafPath

public section

namespace Hex.GraphIso.Nauty.Sparse.Generation

/-- Every selected native descent has the same target sequence and full
leaf key, allowing arbitrary bounded scratch at every literal child call. -/
def Uniform (G : Hex.SparseGraph n) (tcLevel level : Nat) (st : RefineSt n)
    (targets : List Nat) (key : Key n) : Prop :=
  ∀ targets' key', HasLeaf G tcLevel level st targets' key' → targets' = targets ∧ key' = key

private theorem cell_nondiscrete {G : Hex.SparseGraph n} {level tc len : Nat} {st : RefineSt n}
    (hr : RefineSt.Ready G level st) (hc : IsCell st.ptn level tc len)
    (hb : tc + len ≤ n) (hn : 1 < len) : discreteAt st.ptn level n ≠ true := by
  intro hd
  have hm := mem_cells_of_isCell (nn := n) (Nat.le_of_eq hr.spec.node.ptnSize.symm)
    hr.spec.node.ptnEnd hc (by omega) (by rw [hr.spec.node.ptnSize]; exact hb)
  have he := cells_eq_of_discreteAt hd _ hm
  simp only [beq_iff_eq] at he
  omega

namespace Uniform

variable {G : Hex.SparseGraph n} {tcLevel level : Nat} {st : RefineSt n}
  {targets : List Nat} {key : Key n}

theorem leaf {label : Label n} (hr : RefineSt.Ready G level st)
    (hd : discreteAt st.ptn level n = true) (hp : Label.ofArray? n st.lab = some label) :
    Uniform G tcLevel level st [] ⟨[st.longcode, codeSentinel], G.relabel label.perm⟩ := by
  intro targets key h
  rcases h.cases with ⟨other, _, ho, rfl, rfl⟩ |
    ⟨tc, len, o, scratch, rest, tail, hc, hb, hn, _⟩
  · rw [hp] at ho
    cases ho
    exact ⟨rfl, rfl⟩
  · exact (cell_nondiscrete hr hc hb hn hd).elim

/-- Uniformity of every literal target child gives parent uniformity.
The target and code are those of the executed sparse refinement. -/
theorem node {tc len : Nat} (hr : RefineSt.Ready G level st)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len)
    (ht : tc = targetcell (.ofGraph G) st.lab st.ptn level tcLevel (-1))
    (hchildren : ∀ o, o < len → ∀ scratch, Scratch.Bounded n scratch →
      Uniform G tcLevel (level + 1) (st.child (.ofGraph G) level tc st.lab[tc + o]! scratch) targets key) :
    Uniform G tcLevel level st (tc :: targets) ⟨st.longcode :: key.codes, key.graph⟩ := by
  intro targets' key' h
  rcases h.cases with ⟨label, hd, _⟩ |
    ⟨tc', len', o, scratch, rest, tail, hc', hb', hn', ho, hs, ht', hchild, rfl, rfl⟩
  · exact (cell_nondiscrete hr hc hb hn hd).elim
  · have he : tc' = tc := ht'.trans ht.symm
    cases he
    have he : len' = len := by
      rcases isCell_disjoint_or_eq hc' hc with he | he | he
      · omega
      · omega
      · exact he.2
    cases he
    obtain ⟨rfl, rfl⟩ := hchildren o ho scratch hs rest tail hchild
    exact ⟨rfl, rfl⟩

/-- Every literal target child inherits a uniform parent's suffix. -/
theorem child {tc len o : Nat} {scratch : Scratch}
    (h : Uniform G tcLevel level st (tc :: targets) ⟨st.longcode :: key.codes, key.graph⟩)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
    (hs : Scratch.Bounded n scratch)
    (ht : tc = targetcell (.ofGraph G) st.lab st.ptn level tcLevel (-1)) :
    Uniform G tcLevel (level + 1) (st.child (.ofGraph G) level tc st.lab[tc + o]! scratch) targets key := by
  intro targets' key' hleaf
  obtain ⟨htargets, hkey⟩ := h _ _ (hleaf.step hc hb hn ho hs ht)
  refine ⟨(List.cons.inj htargets).2, ?_⟩
  have hcodes := (List.cons.inj (congrArg Key.codes hkey)).2
  have hgraph := congrArg Key.graph hkey
  cases key
  cases key'
  congr

/-- Counted checked carriers transport every child's leaves to the
guiding child. They need not belong to a group already proved complete. -/
theorem carriers {tc len guide : Nat} {scratch : Scratch}
    (hr : RefineSt.Ready G level st)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (hg : guide < len)
    (hs : Scratch.Bounded n scratch)
    (ht : tc = targetcell (.ofGraph G) st.lab st.ptn level tcLevel (-1))
    (hcarriers : ∀ o, o < len → ∃ gamma, checkAutom (Graph.context G).g gamma = true ∧
      CellStab st.ptn level st.lab gamma ∧ gamma[st.lab[tc + o]!]! = st.lab[tc + guide]!)
    (hguide : Uniform G tcLevel (level + 1)
      (st.child (.ofGraph G) level tc st.lab[tc + guide]! scratch) targets key) :
    Uniform G tcLevel level st (tc :: targets) ⟨st.longcode :: key.codes, key.graph⟩ := by
  apply node hr hc hb hn ht
  intro o ho other hother targets' key' hleaf
  obtain ⟨gamma, hcheck, hstab, hmove⟩ := hcarriers o ho
  exact hguide targets' key' (hleaf.carried hr hc hb hn ho hg hother hs hcheck hstab hmove)

/-- Native state equivalence transports uniformity because its inverse
preserves every individual leaf key and selected target sequence. -/
theorem map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j)
    {tcLevel level : Nat} {s t : RefineSt n} {targets : List Nat} {key : Key n}
    (hs : RefineSt.Ready G level s) (ht : RefineSt.Ready H level t)
    (he : RefineSt.Equiv (renamingOf p) level s t)
    (h : Uniform G tcLevel level s targets key) : Uniform H tcLevel level t targets key := by
  intro targets' key' hleaf
  exact h targets' key' ((HasLeaf.map_iff G H p hiso hs ht he).mpr hleaf)

end Uniform
end Hex.GraphIso.Nauty.Sparse.Generation
