/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Control
import all HexGraphIso.Nauty.Invariant.Domination

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

/-- A non-generator prune cannot cross an ancestor that lies strictly
above both saved subtree boundaries, regardless of the canonical comparison. -/
theorem prune_floor {level noncheaplevel allsamelevel : Nat} {eqlevCanon : Int}
    (hcheap : level < noncheaplevel) (hsame : level < allsamelevel) :
    Int.ofNat level ≤ pruneReturn noncheaplevel allsamelevel eqlevCanon := by
  unfold pruneReturn
  split <;> dsimp only <;> split <;> simp only [Int.ofNat_eq_natCast] at * <;> omega

/-- Agreement with the canonical prefix also prevents a non-generator
prune from crossing this level, independently of the all-same boundary. -/
theorem prune_floor_canon {level noncheaplevel allsamelevel : Nat} {eqlevCanon : Int}
    (hcheap : level < noncheaplevel) (hcanon : Int.ofNat level ≤ eqlevCanon) :
    Int.ofNat level ≤ pruneReturn noncheaplevel allsamelevel eqlevCanon := by
  unfold pruneReturn
  split <;> dsimp only <;> split <;> simp only [Int.ofNat_eq_natCast] at * <;> omega

/-- A non-generator return crossing an ancestor must use one of the two
saved subtree boundaries. A comparison-code argument alone is insufficient. -/
theorem prune_early {level noncheaplevel allsamelevel : Nat} {eqlevCanon : Int}
    (h : pruneReturn noncheaplevel allsamelevel eqlevCanon < Int.ofNat level) :
    noncheaplevel ≤ level ∨ allsamelevel ≤ level := by
  by_cases hc : noncheaplevel ≤ level
  · exact Or.inl hc
  · right
    by_cases hs : allsamelevel ≤ level
    · exact hs
    exfalso
    have hf := prune_floor (eqlevCanon := eqlevCanon) (by omega : level < noncheaplevel)
      (by omega : level < allsamelevel)
    omega

/-- The final all-same adjustment never moves the boundary above the
first-path frame being completed. -/
theorem finish_floor {level size index : Nat} {st : SearchSt n}
    (h : level ≤ st.allsamelevel) : level ≤ (firstFinish level size index st).allsamelevel := by
  unfold firstFinish
  split
  · next hif =>
    have he : st.allsamelevel = level + 1 := beq_iff_eq.mp hif.2
    change level ≤ st.allsamelevel - 1
    omega
  · exact h

/-- Lowering the all-same boundary to the completed frame requires both
a uniform child boundary and a counter equal to the original cell size. -/
theorem finish_drop {level size index : Nat} {st : SearchSt n}
    (hbefore : level < st.allsamelevel)
    (hafter : (firstFinish level size index st).allsamelevel ≤ level) :
    size = index ∧ st.allsamelevel = level + 1 := by
  unfold firstFinish at hafter
  split at hafter
  · next hif => exact ⟨beq_iff_eq.mp hif.1, beq_iff_eq.mp hif.2⟩
  · exact (Nat.not_le_of_gt hbefore hafter).elim

end Hex.GraphIso.Nauty.Generation
