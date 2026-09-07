/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Uniform
import all HexGraphIso.Nauty.Correct.Generation.Uniform

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

/-- Cell equivalence can be reversed through an inverse vertex renaming.
Only inverses on the vertex range are needed. -/
theorem reverse_cells {σ τ : Renaming n} {level : Nat} {U V : RefineSt n}
    (hU : IterOk ctx level U) (hsp : StPerm level V (mapSt σ U))
    (hinv : ∀ v, v < n → τ (σ v) = v) : StPerm level U (mapSt τ V) := by
  have hV := iterOk_of_stPerm hU hsp
  have hmap : (U.lab.map σ.toFun).map τ.toFun = U.lab := by
    rw [Array.map_map]
    calc
      U.lab.map (τ.toFun ∘ σ.toFun) = U.lab.map id :=
        map_congr_of_labOk hU.ok.labOk hinv
      _ = U.lab := by simp
  refine ⟨hsp.ptn.symm, hsp.active.symm, hsp.numcells.symm, hsp.hint.symm,
    hsp.maxpos.symm, hsp.longcode.symm, ?_, ?_⟩
  · change (V.lab.map τ.toFun).size = U.lab.size
    rw [Array.size_map, hV.ok.labSize, hU.ok.labSize]
  · change cellsPerm U.ptn level U.lab (V.lab.map τ.toFun)
    apply cellsPerm_of_forall_cells hU.ok.ptnSize hU.ok.labSize
      (by rw [Array.size_map, hV.ok.labSize]) hU.ok.ptnEnd
    intro p hp
    have hb := cells_bound (Nat.le_of_eq hU.ok.ptnSize.symm) hU.ok.ptnEnd p hp
    rw [hU.ok.ptnSize] at hb
    have hle := cells_le p hp
    have hc := cells_isCell (Nat.le_of_eq hU.ok.ptnSize.symm) hU.ok.ptnEnd p hp
    have hcV : IsCell V.ptn level p.1 (p.2 + 1 - p.1) := by
      rw [← hsp.ptn]
      exact hc
    have hm := (hsp.cells _ _ hcV).map τ.toFun
    change ((segN V.lab p.1 (p.2 + 1 - p.1)).map τ.toFun).Perm
      ((segN (U.lab.map σ.toFun) p.1 (p.2 + 1 - p.1)).map τ.toFun) at hm
    rw [← segN_map (by rw [hV.ok.labSize]; omega),
      ← segN_map (by rw [Array.size_map, hU.ok.labSize]; omega), hmap] at hm
    exact hm.symm

/-- Uniformity transports through the same graph and cell isomorphisms
as a reference occurrence. The inverse transports arbitrary destination
leaves back to the uniform source. -/
theorem Uniform.transport {σ τ : Renaming n} {tcLevel level : Nat}
    {U V : RefineSt n} {targets : List Nat} {key : Key n}
    (h : Uniform ctx tcLevel level U targets key)
    (hU : IterOk ctx level U) (hsp : StPerm level V (mapSt σ U))
    (hrows : RowsMap τ ctx.g ctx.g) (hinv : ∀ v, v < n → τ (σ v) = v) :
    Uniform ctx tcLevel level V targets key := by
  intro targets' key' hleaf
  exact h targets' key' (hleaf.transport hrows (iterOk_of_stPerm hU hsp) (reverse_cells hU hsp hinv))

end Hex.GraphIso.Nauty.Generation
