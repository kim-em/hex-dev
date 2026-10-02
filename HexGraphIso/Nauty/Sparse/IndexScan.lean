/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexStart

public section

namespace Hex.GraphIso.Nauty.Sparse.Index.Tail

/-- The scan's existing range bound and break condition supply a maximal
run. Its writes preserve the other fields of the current working state. -/
theorem scanned (h : Tail n first last upto oldlab hits oldstarts oldends s)
    (r : RefineSt n) (hp : oldlab.toList.Perm (List.range n))
    (hu : upto < last) (hbn : last < n) (ha : upto + 1 ≤ b) (hb : b ≤ last)
    (hk : hits[s.lab[b]!]! = hits[s.lab[upto + 1]!]!)
    (hn : b = upto + 1 + (last - (upto + 1)) ∨
      hits[s.lab[b + 1]!]! ≠ hits[s.lab[upto + 1]!]!)
    (hs : Scatter n s.lab s.cellstart r.cellstart (upto + 1 + 1) (b + 1) (upto + 1)) :
    Tail n first last b oldlab hits oldstarts oldends
      { r with
        lab := s.lab
        hits := hits
        cellstart := r.cellstart.setIfInBounds s.lab[upto + 1]!
          (if b - (upto + 1) = 0 then n else upto + 1)
        cellend := s.cellend.setIfInBounds (upto + 1) b } := by
  have hnext : b = last ∨ hits[s.lab[b]!]! ≠ hits[s.lab[b + 1]!]! := by
    rcases hn with hn | hn
    · exact Or.inl (by omega)
    · exact Or.inr (fun he => hn (he.symm.trans hk))
  have hx := h.extend hp hu hbn ha hb hk hnext hs
  apply hx.transfer
  · rfl
  · have heq : b - (upto + 1) = 0 ↔ upto + 1 = b := by omega
    simp only [heq]
  · rfl
  · exact h.hits_eq.symm

end Hex.GraphIso.Nauty.Sparse.Index.Tail
