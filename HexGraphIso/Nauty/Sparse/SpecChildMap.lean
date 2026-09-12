/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecLeafMap
public import HexGraphIso.Nauty.Spec.Descent

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every enumerated member of a target cell has a corresponding member
after renaming. The actual individualization rotations preserve cell
equivalence on the new partition, despite different offsets and tie orders. -/
theorem breakout_match (σ : Renaming n) (level first len o : Nat) (lab out ptn : Array Nat)
    (hp : lab.size = n) (hq : out.size = n) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level)
    (hvals : ∀ q, q < n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
    (hc : IsCell ptn level first len) (hb : first + len ≤ n) (hn : 1 < len) (ho : o < len)
    (hperm : cellsPerm ptn level out (lab.map σ.toFun)) :
    ∃ j, j < len ∧ out[first + j]! = σ lab[first + o]! ∧
      cellsPerm (ptn.set! first (level + 1)) (level + 1)
        (breakout n out ptn (level + 1) first out[first + j]!).1
        ((breakout n lab ptn (level + 1) first lab[first + o]!).1.map σ.toFun) := by
  have hmem : σ lab[first + o]! ∈ segN out first len := by
    apply (hperm first len hc).mem_iff.mpr
    rw [segN_map_of_le _ _ _ _ (by omega)]
    exact List.mem_map.mpr ⟨lab[first + o]!, mem_segN_iff.mpr ⟨o, ho, rfl⟩, rfl⟩
  obtain ⟨j, hj, he⟩ := mem_segN_iff.mp hmem
  have hend' : ptn[ptn.size - 1]! ≤ level := by simpa only [hs] using hend
  have hcell := mem_cells_of_isCell (nn := n) (Nat.le_of_eq hs.symm) hend' hc (by omega)
    (by rw [hs]; exact hb)
  exact ⟨j, hj, he, breakout_cellsPerm_map hs hq hp hend' hvals hperm hcell
    (by omega) (by omega) (by omega) he⟩

end Hex.GraphIso.Nauty.Sparse
