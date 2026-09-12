/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstResult
public import HexGraphIso.Sparse.Run

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Finishing native canonical rows retains the complete installed label. -/
theorem canonlab_size (G : GraphIso.Sparse.Colored n k) : (runColored G).canonlab.size = n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    rfl
  · exact (runState_canonical G hn).1

/-- The returned canonical label retains every original ordered colour
cell's vertices, including the empty input. -/
theorem canonlab_cellsReach (G : GraphIso.Sparse.Colored n k) :
    CellsReach G.toDense (runColored G).canonlab := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    intro a len hcell
    have he : segN (Nauty.initialPartition G.toDense).1 a len =
        segN (runColored G).canonlab a len := by
      refine segN_congr fun o ho => ?_
      rw [getElem!_neg _ _ (by rw [size_initialPartition]; omega),
        getElem!_neg _ _ (by rw [canonlab_size]; omega)]
    rw [he]
  · exact (runState_canonical G hn).2

/-- The actual output array is a permutation, so its checked parser always
succeeds. This theorem does not depend on certificate replay. -/
theorem canonlab_perm (G : GraphIso.Sparse.Colored n k) :
    (runColored G).canonlab.toList.Perm (List.range n) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    have hs : (runColored G).canonlab.toList.length = 0 := by
      rw [Array.length_toList, canonlab_size]
    rw [List.length_eq_zero_iff.mp hs, List.range_zero]
  · exact isPerm_of_cellsReach (canonlab_size G) hn (canonlab_cellsReach G)

theorem canonlab_parse (G : GraphIso.Sparse.Colored n k) :
    ∃ l, Label.ofArray? n (runColored G).canonlab = some l :=
  Label.ofArray?_exists (canonlab_perm G)

/-- The diagnostic result succeeds unconditionally for every native sparse
coloured graph. No default label or alternate search is needed. -/
theorem searchResult?_isSome (G : GraphIso.Sparse.Colored n k) : (searchResult? G).isSome := by
  obtain ⟨l, hl⟩ := canonlab_parse G
  simp [searchResult?, hl]

end Hex.GraphIso.Nauty.Sparse
