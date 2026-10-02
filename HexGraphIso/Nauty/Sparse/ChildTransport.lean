/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Path
public import HexGraphIso.Nauty.Sparse.SpecChildMap
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Corresponding members of a cell give equivalent literal cached child
calls. Both scratch arguments remain independent; tied label order may
change the selected offset but not the refined partition or code. -/
theorem child_match (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j)
    {level : Nat} {s t : RefineSt n}
    (hs : RefineSt.Ready G level s) (ht : RefineSt.Ready H level t)
    (hp : t.ptn = s.ptn) (hnc : t.numcells = s.numcells)
    (he : cellsPerm s.ptn level t.lab (s.lab.map (renamingOf p).toFun))
    {tc len o : Nat} (hc : IsCell s.ptn level tc len)
    (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
    (a b : Scratch) (ha : Scratch.Bounded n a) (hb' : Scratch.Bounded n b) :
    ∃ j, j < len ∧ t.lab[tc + j]! = renamingOf p s.lab[tc + o]! ∧
      RefineSt.Equiv (renamingOf p) (level + 1)
        (s.child (.ofGraph G) level tc s.lab[tc + o]! a)
        (t.child (.ofGraph H) level tc t.lab[tc + j]! b) := by
  have hend : s.ptn[n - 1]! ≤ level := by
    simpa only [hs.spec.node.ptnSize] using hs.spec.node.ptnEnd
  have hweak : ∀ q, q < n → s.ptn[q]! ≤ level ∨ level + 1 < s.ptn[q]! := by
    intro q _
    rcases hs.spec.node.vals q with hh | hh
    · exact Or.inl hh
    · have hd := hs.spec.depth
      have hn := hs.spec.count
      have hb := bcount_le s.ptn level n
      exact Or.inr (by omega)
  obtain ⟨j, hj, hm, hchild⟩ := breakout_match (renamingOf p) level tc len o s.lab t.lab s.ptn
    hs.spec.node.labSize ht.spec.node.labSize hs.spec.node.ptnSize hend hweak hc hb hn ho he
  have ht' : SpecNode H level t.lab s.ptn t.active s.numcells := by
    simpa only [hp, hnc] using ht.spec
  have heq : Equitable (Graph.context H) level t.lab s.ptn := by
    simpa only [hp] using ht.equitable
  have hsrc := hs.spec.child hs.equitable hc hb hn ho
  have htgt := ht'.child heq hc hb hn hj
  let u := breakout n s.lab s.ptn (level + 1) tc s.lab[tc + o]!
  let v := breakout n t.lab s.ptn (level + 1) tc t.lab[tc + j]!
  have hclosed : u.2.1[n - 1]! ≤ level + 1 := by
    simpa only [hsrc.node.ptnSize] using hsrc.node.ptnEnd
  have hr := refineWith_equiv G H p hiso (level + 1) u.1 v.1 u.2.1 u.2.2 (s.numcells + 1)
    a b hsrc.label htgt.label hsrc.node.ptnSize hclosed hsrc.node.starts ha hb' hchild
  refine ⟨j, hj, hm, ?_⟩
  simpa only [RefineSt.child, hp, hnc, u, v, breakout] using hr

/-- Specifying both corresponding vertices identifies the exact pair of
native cached child calls, independently of their offsets and scratch. -/
theorem child_equiv (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j)
    {level : Nat} {s t : RefineSt n}
    (hs : RefineSt.Ready G level s) (ht : RefineSt.Ready H level t)
    (hp : t.ptn = s.ptn) (hnc : t.numcells = s.numcells)
    (he : cellsPerm s.ptn level t.lab (s.lab.map (renamingOf p).toFun))
    {tc len a b : Nat} (hc : IsCell s.ptn level tc len)
    (hb : tc + len ≤ n) (hn : 1 < len) (ha : a < len) (hb' : b < len)
    (scratch other : Scratch) (hsc : Scratch.Bounded n scratch) (hoc : Scratch.Bounded n other)
    (hmove : t.lab[tc + b]! = renamingOf p s.lab[tc + a]!) :
    RefineSt.Equiv (renamingOf p) (level + 1)
      (s.child (.ofGraph G) level tc s.lab[tc + a]! scratch)
      (t.child (.ofGraph H) level tc t.lab[tc + b]! other) := by
  obtain ⟨j, hj, hm, hchild⟩ := child_match G H p hiso hs ht hp hnc he hc hb hn ha scratch other hsc hoc
  have hij : tc + j = tc + b := perm_injective ht.spec.label (by omega) (by omega)
    (hm.trans hmove.symm)
  have hsame : j = b := by omega
  subst j
  exact hchild

end Hex.GraphIso.Nauty.Sparse
