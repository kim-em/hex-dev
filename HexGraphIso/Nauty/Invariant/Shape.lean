/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Domination
public import HexGraphIso.Nauty.SmallCell.Transitive

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A reached search partition supplies the geometric descent invariant
for any refinement state with those same partition arrays. -/
theorem SearchOk.iter {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st : Search n} {r : RefineSt n} (h : SearchOk G level numcells st)
    (hn0 : 0 < n) (hlevel : 1 ≤ level) (hl : r.lab = st.lab) (hp : r.ptn = st.ptn) :
    IterOk ctx level r := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hl]; exact h.labSize
  · rw [hl]; exact labOk_of_reach h.labSize h.reach
  · rw [hp]; exact h.ptnSize
  · rw [hp]; exact searchOk_end hn0 h hlevel
  · rw [hl]; exact labInj_of_reach h.labSize hn0 h.reach
  · intro q hq
    rw [hp]
    exact h.vals q hq
  · exact Nat.le_trans h.bc (bcount_le _ _ _)

/-- Small-cell shape together with the existing reach, count, and
equitability facts gives the complete subtree invariant. -/
theorem SearchOk.subtree {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st : Search n} {r : RefineSt n} (h : SearchOk G level numcells st)
    (hn0 : 0 < n) (hlevel : 1 ≤ level) (hl : r.lab = st.lab) (hp : r.ptn = st.ptn)
    (hc : r.numcells = numcells) (he : Equitable ctx level st.lab st.ptn)
    (hs : NodeShape n level st.ptn) : SubtreeOk ctx level r := by
  refine ⟨h.iter hn0 hlevel hl hp, ?_, ?_, ?_⟩
  · rw [hl, hp]; exact he
  · rw [hp, hc]; exact h.count.symm
  · rw [hp]; exact hs

end Hex.GraphIso.Nauty
