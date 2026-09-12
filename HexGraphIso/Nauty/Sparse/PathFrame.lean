/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Path
public import HexGraphIso.Nauty.Invariant.Singleton

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Cached native refinement retains both boundaries and the literal
vertex of every incoming singleton. -/
theorem SpecNode.refine_singleton {G : Hex.SparseGraph n} {level numcells a : Nat}
    {lab ptn : Array Nat} {active : VSet n}
    (h : SpecNode G level lab ptn active numcells) (scratch : Scratch)
    (hs : Scratch.Bounded n scratch) (ha : IsCell ptn level a 1) :
    let out := Sparse.refineWith (.ofGraph G) level lab ptn active numcells scratch
    IsCell out.ptn level a 1 ∧ out.lab[a]! = lab[a]! := by
  have hr := refineWith_state G level lab ptn active numcells scratch
    h.label h.node.ptnSize (by simpa only [h.node.ptnSize] using h.node.ptnEnd) h.node.starts hs
  refine ⟨?_, cellsPerm_singleton hr.2.2.2.1 ha⟩
  obtain ⟨hpos, hstart, _, hend⟩ := ha
  refine ⟨hpos, ?_, ?_, ?_⟩
  · rcases hstart with he | he
    · exact Or.inl he
    · right
      rw [hr.2.2.1.closed _ he]
      exact he
  · intro i hi hj
    omega
  · rw [hr.2.2.1.closed _ hend]
    exact hend

/-- An actual cached child preserves its parent's ordered cell contents
and every boundary already closed at that parent. -/
theorem RefineSt.Ready.child_frame {G : Hex.SparseGraph n} {level : Nat} {s : RefineSt n}
    (h : RefineSt.Ready G level s) {tc len o : Nat}
    (hc : IsCell s.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
    (scratch : Scratch) (hs : Scratch.Bounded n scratch) :
    let out := s.child (.ofGraph G) level tc s.lab[tc + o]! scratch
    cellsPerm s.ptn level s.lab out.lab ∧
      ∀ q : Nat, s.ptn[q]! ≤ level → out.ptn[q]! = s.ptn[q]! := by
  let b := breakout n s.lab s.ptn (level + 1) tc s.lab[tc + o]!
  have hraw := h.spec.child h.equitable hc hb hn ho
  have hr := refineWith_state G (level + 1) b.1 b.2.1 b.2.2 (s.numcells + 1) scratch
    hraw.label hraw.node.ptnSize (by simpa only [hraw.node.ptnSize] using hraw.node.ptnEnd)
    hraw.node.starts hs
  have hout := h.child hc hb hn ho scratch hs
  have hopen := hc.2.2.1 tc (Nat.le_refl _) (by omega)
  have hclosed : ∀ q : Nat, s.ptn[q]! ≤ level → b.2.1[q]! = s.ptn[q]! := by
    intro q hq
    exact Array.getElem!_set!_ne _ _ _ _ (by intro he; subst q; omega)
  have hbreak := breakout_cellsPerm (n := n) hc (by rw [h.spec.node.ptnSize]; exact hb)
    (by rw [h.spec.node.labSize, h.spec.node.ptnSize]) ho
  refine ⟨cellsPerm_trans hbreak ?_, ?_⟩
  · exact cellsPerm_coarsen (h.spec.node.ptnSize.trans hraw.node.ptnSize.symm)
      (hraw.node.labSize.trans hraw.node.ptnSize.symm)
      (hout.spec.node.labSize.trans hraw.node.ptnSize.symm)
      (cellsPerm_symm hr.2.2.2.1) hraw.node.ptnEnd h.spec.node.ptnEnd
      (fun q hq => by rw [hclosed q hq]; omega)
  · intro q hq
    exact (hr.2.2.1.closed q (by rw [hclosed q hq]; omega)).trans (hclosed q hq)

/-- Every literal native descent retains its frozen ancestor's cell
contents and closed boundaries, independently of scratch contents. -/
theorem DescPath.frame {G : Hex.SparseGraph n} {base last : Nat} {root leaf : RefineSt n}
    {path : List (Nat × Nat)} (h : DescPath G base root path last leaf)
    (hr : RefineSt.Ready G base root) :
    cellsPerm root.ptn base root.lab leaf.lab ∧
      ∀ q : Nat, root.ptn[q]! ≤ base → leaf.ptn[q]! = root.ptn[q]! := by
  induction h with
  | refl => exact ⟨cellsPerm_refl _ _ _, fun _ _ => rfl⟩
  | step tc len o scratch hc hb hn ho hs tail ih =>
    have hchild := hr.child hc hb hn ho scratch hs
    have hleaf := tail.ready hchild
    obtain ⟨hstep, hclosed⟩ := hr.child_frame hc hb hn ho scratch hs
    obtain ⟨htail, hlast⟩ := ih hchild
    refine ⟨?_, ?_⟩
    · exact cellsPerm_trans hstep (cellsPerm_coarsen
        (hr.spec.node.ptnSize.trans hchild.spec.node.ptnSize.symm)
        (hchild.spec.node.labSize.trans hchild.spec.node.ptnSize.symm)
        (hleaf.spec.node.labSize.trans hchild.spec.node.ptnSize.symm)
        htail hchild.spec.node.ptnEnd hr.spec.node.ptnEnd
        (fun q hq => by rw [hclosed q hq]; omega))
    · intro q hq
      rw [hlast q (by rw [hclosed q hq]; omega), hclosed q hq]

end Hex.GraphIso.Nauty.Sparse
