/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Descent
public import HexGraphIso.Nauty.Correct.Generation.Uniform
public import HexGraphIso.Nauty.Correct.Generation.Tree
import all HexGraphIso.Nauty.Correct.Generation.Uniform

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

/-- A valid uniform subtree whose key matches the first reference emits
a carrier on its first descent. Leaf existence is derived from validity,
so uniformity is never used vacuously. -/
theorem uniform_reference {inf tcLevel fuel level numcells : Nat} {st : SearchSt n}
    {targets : List Nat} {key : Key n}
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hT : TreeOk ctx level (refine ctx level st.lab st.ptn st.active numcells))
    (hU : Uniform ctx tcLevel level (refine ctx level st.lab st.ptn st.active numcells) targets key)
    (hsize : st.firstlab.size = n) (hperm : st.firstlab.toList.Perm (List.range n))
    (hm : Matches ctx level st targets key)
    (hlevel : st.eqlevFirst = level - 1) (hclear : st.needshortprune = false)
    (hguide : st.gcaFirst < level) (hfuel : n < level + fuel) :
    let result := otherNode ctx inf tcLevel fuel level numcells st
    result.1 = Int.ofNat st.gcaFirst ∧ LabelCarrier ctx st.firstlab result.2.lab result.2.genTrace := by
  have hpos : 1 ≤ level := by omega
  obtain ⟨targets', key', hleaf⟩ := hT.nonempty hpos hsymm
  have hocc : HasLeaf ctx tcLevel level (refine ctx level st.lab st.ptn st.active numcells) targets key := by
    obtain ⟨rfl, rfl⟩ := hU targets' key' hleaf
    exact hleaf
  apply descent_reference inf tcLevel hgsz
    (fun level rs targets key => TreeOk ctx level rs ∧ Uniform ctx tcLevel level rs targets key)
    (fun h => ⟨h.1.it, h.1.eqt, h.1.acc⟩) ?_
    fuel level numcells st targets key ⟨hT, hU⟩ hsize hperm hm hocc hlevel hclear hguide hT.it.lvl hfuel
  intro level rs tc e o targets key h hlvl hcell hne htarget ho _ o' ho'
  have hT' := h.1.child hlvl hsymm hcell hne ho'
  have hU' := h.2.child hlvl hcell hne htarget ho'
  obtain ⟨targets', key', hleaf⟩ := hT'.nonempty (by omega) hsymm
  obtain ⟨rfl, rfl⟩ := hU' targets' key' hleaf
  exact ⟨⟨hT', hU'⟩, hleaf⟩

end Hex.GraphIso.Nauty.Generation
