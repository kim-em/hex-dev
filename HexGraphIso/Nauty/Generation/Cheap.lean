/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Generation.RefPath
public import HexGraphIso.Nauty.SmallCell.Transitive
import all HexGraphIso.Nauty.Invariant.Refine
import all HexGraphIso.Nauty.Invariant.Domination
import all HexGraphIso.Nauty.Invariant.Codes
import all HexGraphIso.Nauty.Search.State
import all HexGraphIso.Nauty.Invariant.Frame

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

/-- At a small-cell node, a matching reference in one target child occurs
in every target child. The geometric carrier supplies occurrence only;
no membership in the emitted generator group is assumed. -/
theorem HasLeaf.smallChild {st : RefineSt n} {tcLevel level tc e oU oV : Nat}
    {targets : List Nat} {key : Key n}
    (hS : SubtreeOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (h : HasLeaf ctx tcLevel (level + 1)
      (childSt ctx level st tc st.lab[tc + oU]!) targets key) :
    HasLeaf ctx tcLevel (level + 1)
      (childSt ctx level st tc st.lab[tc + oV]!) targets key := by
  by_cases ho : oU = oV
  · simpa only [ho] using h
  obtain ⟨σ, hrows, hsp, hmap⟩ := stabilizer_transitive hS hgsz hsymm hloop hcell hne hoU hoV ho
  exact h.transport hrows (iterOk_child hS.it hlvl hcell hne hoU)
    (stPerm_child hrows hsp hS.it hcell hne hoV hoU hmap)

/-- Small-cell transitivity transports the saved reference path,
including its uniformity guarantees, to every target child. -/
theorem RefPath.smallChild {st : RefineSt n} {tcLevel boundary level tc e oU oV : Nat}
    {targets : List Nat} {key : Key n}
    (hS : SubtreeOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (h : RefPath ctx tcLevel boundary (level + 1)
      (childSt ctx level st tc st.lab[tc + oU]!) targets key) :
    RefPath ctx tcLevel boundary (level + 1)
      (childSt ctx level st tc st.lab[tc + oV]!) targets key := by
  by_cases ho : oU = oV
  · simpa only [ho] using h
  obtain ⟨σ, hrows, hsp, hmap⟩ := stabilizer_transitive hS hgsz hsymm hloop hcell hne hoU hoV ho
  have hraw : st.lab.map (fun v => (renamingArray σ)[v]!) = st.lab.map σ.toFun :=
    map_congr_of_labOk hS.it.ok.labOk (fun v hv => renamingArray_get σ hv)
  refine h.carried hS.it hlvl hgsz (checkAutom_renaming σ hrows) ?_ hcell hne hoU hoV ?_
  · change cellsPerm st.ptn level st.lab (st.lab.map (fun v => (renamingArray σ)[v]!))
    rw [hraw]
    exact hsp.cells
  · have he := target_end_lt hS.it.ok.ptnSize hS.it.ok.ptnEnd hcell
    rw [renamingArray_get σ (hS.it.ok.labOk _ (by rw [hS.it.ok.labSize]; omega))]
    exact hmap.symm

end Hex.GraphIso.Nauty.Generation
