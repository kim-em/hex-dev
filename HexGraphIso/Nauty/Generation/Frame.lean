/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Generation.Stabilizer

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k} {base : List (Fin n)}

/-- A cell-stabilizing array fixes every vertex in a singleton cell. -/
theorem cellStab_fixes {ptn lab γ : Array Nat} {level pos : Nat}
    (hpos : pos < lab.size) (hcell : IsCell ptn level pos 1)
    (h : CellStab ptn level lab γ) : γ[lab[pos]!]! = lab[pos]! := by
  have he := cellsPerm_singleton h hcell
  rw [getElem!_map_of_lt (fun v => γ[v]!) lab hpos] at he
  exact he.symm

/-- Stabilizing a reached frame fixes the individualized base because
those vertices are singleton cells in that frame. -/
theorem frame_fixes {level : Nat} {st : Search n} {γ : Array Nat}
    (hfixed : FixedCells level st) (hsize : st.lab.size = n)
    (hbase : ∀ b ∈ base, st.fixedpts.mem b.val = true)
    (hstab : CellStab st.ptn level st.lab γ) :
    ∀ b ∈ base, γ[b.val]! = b.val := by
  intro b hb
  obtain ⟨pos, hpos, hat, hcell⟩ := hfixed b.val b.isLt (hbase b hb)
  have hf := cellStab_fixes (by omega : pos < st.lab.size) hcell hstab
  rwa [hat] at hf

end Hex.GraphIso.Nauty.Generation
