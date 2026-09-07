/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Guided
import all HexGraphIso.Nauty.Policy.Guided
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Equitable.Basic

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat} {ctx : Ctx n}

/-- Renaming and reordering within cells transports a canonically selected
descent, retaining both its target positions and the canonical choices. -/
theorem DescPath.selected {σ : Renaming n} (hg : RowsMap σ ctx.g ctx.g) (tcLevel : Nat) :
    ∀ {level last : Nat} {path : List (Nat × Nat)} {U leaf V : RefineSt n},
      DescPath ctx level U path last leaf → Selects ctx tcLevel level U path →
      IterOk ctx level U → StPerm level V (mapSt σ U) →
      ∃ out path', DescPath ctx level V path' last out ∧
        Selects ctx tcLevel level V path' ∧ path'.map Prod.fst = path.map Prod.fst ∧
        StPerm last out (mapSt σ leaf)
  | _, _, _, _, _, V, .refl _ _, _, _, hsp =>
    ⟨V, [], .refl _ _, trivial, rfl, hsp⟩
  | level, last, _, U, leaf, V, .step tc e o hlvl hcell hne ho htail, hs, hU, hsp => by
    have hV := iterOk_of_stPerm hU hsp
    have hcellV : (tc, e) ∈ cells V.ptn level n := by
      rw [← hsp.ptn]
      exact hcell
    have hen := target_end_lt hV.ok.ptnSize hV.ok.ptnEnd hcellV
    have hcellIsV := cells_isCell (Nat.le_of_eq hV.ok.ptnSize.symm) hV.ok.ptnEnd _ hcellV
    have hmemU : σ.toFun U.lab[tc + o]! ∈ segN (U.lab.map σ.toFun) tc (e + 1 - tc) := by
      rw [segN_map (by rw [hU.ok.labSize]; omega)]
      exact List.mem_map.mpr ⟨U.lab[tc + o]!, mem_segN_iff.mpr ⟨o, by omega, rfl⟩, rfl⟩
    have hmemV : σ.toFun U.lab[tc + o]! ∈ segN V.lab tc (e + 1 - tc) :=
      (hsp.cells tc (e + 1 - tc) hcellIsV).mem_iff.mpr hmemU
    obtain ⟨oV, hoV, hval⟩ := mem_segN_iff.mp hmemV
    have hchild := stPerm_child hg hsp hU hcell hne (by omega) ho hval
    obtain ⟨out, path', hd, hselect, ht, hleaf⟩ :=
      htail.selected hg tcLevel hs.2 (iterOk_child hU hlvl hcell hne ho) hchild
    refine ⟨out, (tc, oV) :: path', .step tc e oV hlvl hcellV hne (by omega) hd,
      ⟨(stPerm_target hg hU hsp).trans hs.1, hselect⟩, ?_, hleaf⟩
    simp only [List.map_cons, ht]

namespace Engine

/-- A checked row-preserving renaming relating the final labellings
identifies descent depths whenever it stabilizes the common ancestor. -/
theorem Guided.depth_map {σ : Renaming n} {tcLevel base last₁ last₂ : Nat}
    {store : Array Int} {root first current : RefineSt n} {p₁ p₂ : List (Nat × Nat)}
    (hg : RowsMap σ ctx.g ctx.g)
    (hfirst : DescPath ctx base root p₁ last₁ first)
    (hok : IterOk ctx base root) (hselect : Selects ctx tcLevel base root p₁)
    (htarget : Targets store base (p₁.map Prod.fst))
    (hcurrent : DescPath ctx base root p₂ last₂ current)
    (hguided : Guided ctx tcLevel store base root p₂)
    (hstab : StPerm base root (mapSt σ root))
    (hdisc₁ : ∀ q, q < n → first.ptn[q]! ≤ last₁)
    (hdisc₂ : ∀ q, q < n → current.ptn[q]! ≤ last₂)
    (hlab : first.lab.map σ.toFun = current.lab) : last₂ = last₁ := by
  obtain ⟨mapped, path, hd, hs, ht, hp⟩ := hfirst.selected hg tcLevel hselect hok hstab
  have hfirstOk := descends_iterOk hfirst.descends hok
  have hmapped := iterOk_of_stPerm hfirstOk hp
  have hdisc : ∀ q, q < n → mapped.ptn[q]! ≤ last₁ := by
    intro q hq
    rw [← hp.ptn]
    exact hdisc₁ q hq
  have hlabels : mapped.lab = current.lab := by
    have he := stPerm_lab_eq hp (by simpa only [hmapped.ok.ptnSize] using hdisc)
      (by rw [hmapped.ok.labSize, hmapped.ok.ptnSize])
    exact he.symm.trans hlab
  exact Guided.depth hd hok hs (ht ▸ htarget) hcurrent hguided hdisc hdisc₂ hlabels

end Engine

end Hex.GraphIso.Nauty
