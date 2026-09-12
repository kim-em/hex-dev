/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefinedSmall

public section

namespace Hex.GraphIso.Nauty.Sparse.RefineSt.Ready

variable {G : Hex.SparseGraph n} {level : Nat} {s : RefineSt n}

/-- Any two actual cached children of the same cell below a cheap-shaped
node correspond under a graph automorphism, including equal choices with
different incoming scratch. -/
theorem children (h : RefineSt.Ready G level s) (hshape : NodeShape n level s.ptn)
    {tc len a b : Nat} (hc : IsCell s.ptn level tc len) (hb : tc + len ≤ n)
    (hn : 1 < len) (ha : a < len) (hb' : b < len)
    (scratch other : Scratch) (hs : Scratch.Bounded n scratch) (ht : Scratch.Bounded n other) :
    ∃ p : Perm n, (∀ i j, G.adj (p.get i) (p.get j) = G.adj i j) ∧
      RefineSt.Equiv (renamingOf p) (level + 1)
        (s.child (.ofGraph G) level tc s.lab[tc + a]! scratch)
        (s.child (.ofGraph G) level tc s.lab[tc + b]! other) := by
  have hp : ∃ p : Perm n, (∀ i j, G.adj (p.get i) (p.get j) = G.adj i j) ∧
      cellsPerm s.ptn level s.lab (s.lab.map (renamingOf p).toFun) ∧
      s.lab[tc + b]! = renamingOf p s.lab[tc + a]! := by
    by_cases he : a = b
    · subst b
      refine ⟨Perm.id n, by simp, ?_, ?_⟩
      · have hm : s.lab.map (renamingOf (Perm.id n)).toFun = s.lab := by
          have hid : (renamingOf (Perm.id n)).toFun = id := by
            funext v
            simp [renamingOf]
          rw [hid]
          exact Array.map_id _
        rw [hm]
        exact cellsPerm_refl _ _ _
      · simp [renamingOf]
    · exact h.automorphism hshape hc hb hn ha hb' he
  obtain ⟨p, hiso, hcell, hmove⟩ := hp
  obtain ⟨j, hj, hm, he⟩ := child_match G G p hiso h h rfl rfl hcell
    hc hb hn ha scratch other hs ht
  have hjb : tc + j = tc + b := perm_injective h.spec.label (by omega) (by omega)
    (hm.trans hmove.symm)
  have hjb : j = b := by omega
  subst j
  exact ⟨p, hiso, he⟩

end Hex.GraphIso.Nauty.Sparse.RefineSt.Ready
