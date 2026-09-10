/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Scatter
public import HexGraphIso.Nauty.SmallCell.Prefix
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

/-!
The cheap code-one admission uses two discrete descents from a common
small-cell ancestor. The current target-position path must be a prefix
of the first one. The
run invariant supplies this history at the first greatest common
ancestor, independently of the finite refinement codes.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- Compatible descents below a cheap ancestor validate the search's
first-reference scatter without an automorphism scan. -/
theorem scatter_of_descPaths {ctx : Ctx n} {st : Search n}
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    {ancestor : RefineSt n} (hsmall : SubtreeOk ctx st.gcaFirst ancestor)
    {p₁ p₂ : List (Nat × Nat)} {level₁ level₂ : Nat} {U V : RefineSt n}
    (hU : DescPath ctx st.gcaFirst ancestor p₁ level₁ U)
    (hV : DescPath ctx st.gcaFirst ancestor p₂ level₂ V)
    (htargets : p₂.map Prod.fst <+: p₁.map Prod.fst)
    (hUd : ∀ i, i < n → U.ptn[i]! ≤ level₁)
    (hVd : ∀ i, i < n → V.ptn[i]! ≤ level₂)
    (hfirst : st.firstlab = U.lab) (hcurrent : st.lab = V.lab)
    (hwork : st.workperm.size = n) :
    checkAutom ctx.g (scatter st.firstlab st).workperm = true := by
  have hUok := descends_iterOk hU.descends hsmall.it
  have hVok := descends_iterOk hV.descends hsmall.it
  apply scatter_checked hwork
  · rw [hfirst]
    exact hUok.ok.labSize
  · rw [hfirst]
    exact labInj_perm_range hUok.ok.labSize hUok.ok.labOk hUok.inj
  · rw [hcurrent]
    exact hVok.ok.labSize
  · rw [hcurrent]
    exact labInj_perm_range hVok.ok.labSize hVok.ok.labOk hVok.inj
  · rw [hfirst, hcurrent]
    exact (descPath_prefix hgsz hsymm hloop (p₁.map Prod.fst)
      hsmall hU rfl hUd hV htargets hVd).2.symm

end Hex.GraphIso.Nauty
