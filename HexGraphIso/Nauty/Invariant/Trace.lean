/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Store
public import HexGraphIso.Nauty.Invariant.Refine
import all HexGraphIso.Nauty.Invariant.Store

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A raw permutation array preserves the ordered initial colours. -/
def ColorMap (G : Colored n k) (γ : Array Nat) : Prop :=
  ∀ v : Fin n, ∃ hv : γ[v.val]! < n,
    G.coloring.cells.get ⟨γ[v.val]!, hv⟩ = G.coloring.cells.get v

/-- Scattering between reached labellings preserves colours because the
colour at each position is fixed by the initial ordered partition. -/
theorem ColorMap.scatter {G : Colored n k} {γ ref cur : Array Nat}
    (hn : 0 < n) (hrefSize : ref.size = n)
    (href : CellsReach G ref) (hcur : CellsReach G cur)
    (hmap : ∀ i, i < n → γ[ref[i]!]! = cur[i]!) : ColorMap G γ := by
  intro v
  have hm := (isPerm_of_cellsReach hrefSize hn href).mem_iff.mpr
    (List.mem_range.mpr v.isLt)
  obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp hm
  have hin : i < n := by simpa [hrefSize] using hi
  have hv : ref[i]! = v.val := by
    rw [getElem!_pos ref i (by omega)]
    exact hiv
  obtain ⟨hr, hrc⟩ := achieved_position_colors href i hin
  obtain ⟨hc, hcc⟩ := achieved_position_colors hcur i hin
  have hγ : γ[v.val]! = cur[i]! := by rw [← hv, hmap i hin]
  refine ⟨by omega, ?_⟩
  have hv' : (⟨ref[i]!, hr⟩ : Fin n) = v := Fin.ext hv
  have hγ' : (⟨γ[v.val]!, by omega⟩ : Fin n) = ⟨cur[i]!, hc⟩ := Fin.ext hγ
  rw [hγ', ← hv']
  exact Fin.ext (hcc.trans hrc.symm)

end Hex.GraphIso.Nauty
