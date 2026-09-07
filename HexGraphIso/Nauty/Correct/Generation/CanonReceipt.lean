/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.PathCover
public import HexGraphIso.Nauty.Correct.Generation.Canon

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

/-- A canonical unwind to this sweep consumes the current child using
its earlier reference source. Cell stabilization is proved for the actual
carrier from the two reached labellings, rather than imposed on the whole
trace of an off-path search. -/
theorem PathCover.canon {tcLevel specFuel boundary level tc len e tv : Nat}
    {rs : RefineSt n} {targets codes : List Nat} {key : Key n}
    {tcell : VSet n} {cursor : Option Nat} {parent child out : SearchSt n} {best : Option (Key n)}
    (h : PathCover ctx tcLevel boundary level rs tc len targets key tcell cursor)
    (hnext : tcell.nextElem cursor = some tv)
    (hok : IterOk ctx level rs) (hlvl : level < n) (hgsz : ctx.g.size = n)
    (hcell : (tc, e) ∈ cells rs.ptn level n) (hne : tc < e) (hlen : len = e + 1 - tc)
    (hpast : CanonPast level tc cursor parent)
    (hrefs : FrameRefs ctx tcLevel specFuel level codes rs.lab rs.ptn tc len rs.numcells parent best)
    (hgca : child.gcaCanon = parent.gcaCanon) (hlab : child.canonlab = parent.canonlab)
    (hguide : GuideRel (level + 1) child out) (hatCanon : level = out.gcaCanon)
    (hcarrier : LabelCarrier ctx out.canonlab out.lab out.genTrace)
    (hsize : out.canonlab.size = n) (hcurrent : cellsPerm rs.ptn level rs.lab out.lab)
    (hatCur : out.lab[tc]! = tv) :
    PathCover ctx tcLevel boundary level rs tc len targets key tcell (some tv) := by
  obtain ⟨oRef, href, hatRef, hearlier, hrefReach⟩ := hpast.locate hnext hrefs hgca hlab hguide hatCanon.symm
  have hc : CellCarrier ctx rs.ptn level rs.lab out.canonlab out.lab out.genTrace := by
    obtain ⟨γ, hmem, hcheck, hmap⟩ := hcarrier
    exact ⟨γ, hmem, hcheck, hmap,
      cellStab_of_scatter hok.ok.ptnSize hok.ok.labSize hsize hok.ok.ptnEnd hrefReach hcurrent hmap⟩
  exact h.reference hnext hok hlvl hgsz hcell hne hlen href hearlier hc hatRef hatCur

end Hex.GraphIso.Nauty.Generation
