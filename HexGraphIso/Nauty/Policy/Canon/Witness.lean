/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.ShortPair
import all HexGraphIso.Nauty.Policy.Canon.Frame
import all HexGraphIso.Nauty.Policy.Canon.Ref
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The guide and its vertex keys transfer together from the frozen sweep
frame to the current ordering, including references removed by a filter. -/
theorem CanonGuide.frame {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc len : Nat} {cs : List Nat}
    {base st : Search n} {best : Option (Key n)}
    (h : CanonGuide level tc base
      (fun v => prefixKey cs (vertexKey ctx tcLevel fuel level base.lab base.ptn tc numcells v)) best st)
    (hf : SearchOut G level level base st)
    (hbase : SearchOk G level numcells base) (hst : SearchOk G level numcells st)
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hc : IsCell base.ptn level tc len) (hlen : 2 ≤ len) (hr : tc + len ≤ n)
    (hfuel : level + 1 + fuel ≤ n + 1) :
    CanonGuide level tc st
      (fun v => prefixKey cs (vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v)) best st := by
  intro he
  obtain ⟨v, hv, hat, hp⟩ := h.rebase hf he
  have hm : (windowSet n base.lab tc len).mem v = true := by
    obtain ⟨w, _, hw, hm⟩ := h.mem (labOk_of_reach hbase.labSize hbase.reach) hc
      (by change tc + len ≤ base.lab.size; rw [hbase.labSize]; exact hr) he
    have hwv : w = v := hw.symm.trans hat
    rwa [hwv] at hm
  refine ⟨v, ?_, hat, hp⟩
  have hk := hf.vertex_key (ctx := ctx) (tcLevel := tcLevel)
    hbase hst hn0 hlevel hc hlen hr hm hfuel
  change vertexKey ctx tcLevel fuel level base.lab base.ptn tc numcells v =
    vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v at hk
  dsimp only at hv ⊢
  rwa [← hk]

/-- A canonical scatter returning from an actual child identifies that
whole child's specification key with an already covered reference child.
The emitting leaf may lie below arbitrarily many intermediate sweeps. -/
theorem child_canon_cover {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel runFuel level numcells tc tv len : Nat} {first childFirst : Bool}
    {cell : VSet n} {st : Search n} {cs : List Nat} {best : Option (Key n)}
    (h : SearchOk G level numcells st) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hpath : FixedCells level st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true)
    (hgsz : ctx.g.size = n) (hc : IsCell st.ptn level tc len) (hr : tc + len ≤ n)
    (hfuel : level + 1 + fuel ≤ n + 1)
    (hguide : CanonGuide level tc st
      (fun v => prefixKey cs (vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v)) best st) :
    let out := (node childFirst ctx (n + 2) tcLevel runFuel (level + 1) (numcells + 1)
      (Nauty.child first level tc tv st)).2
    out.gcaCanon = level → out.canonlab.size = n → checkAutom ctx.g out.workperm = true →
      (∀ i, i < n → out.workperm[out.canonlab[i]!]! = out.lab[i]!) →
      Generic.Covers (prefixKey cs (vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells tv)) best := by
  intro out hg hs hcheck hmap
  have hold := child_canon_old (ctx := ctx) (tcLevel := tcLevel) (fuel := runFuel)
    (first := first) h hn0 hlevel htarget htv childFirst (Nat.le_of_eq hg)
  have hparent : st.gcaCanon = level := hold.1.symm.trans hg
  obtain ⟨v, hv, hat, href⟩ := hguide hparent
  obtain ⟨v', _, hat', hmem⟩ := hguide.mem (labOk_of_reach h.labSize h.reach) hc
    (by change tc + len ≤ st.lab.size; rw [h.labSize]; exact hr) hparent
  have hvv : v' = v := hat'.symm.trans hat
  rw [hvv] at hmem
  rw [← hold.2] at hat href
  have hcframe := child_frame (ctx := ctx) (tcLevel := tcLevel) (fuel := runFuel) (first := first)
    h hn0 hlevel hpath htarget htv childFirst
  have hout : SearchOut G level level st out := hcframe.1.congr rfl rfl rfl rfl
  have hend := searchOk_end hn0 h hlevel
  have hstab := cellStab_of_scatter h.ptnSize h.labSize hs hend href hout.perm hmap
  have hchild := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hlevel h htarget htv
  have hnode := node_out (ctx := ctx) (tcLevel := tcLevel) (fuel := runFuel)
    childFirst hn0 (by omega) hchild.1
  have hstore := child_store (ctx := ctx) first hn0 hlevel h htarget htv
    ⟨hnode.labSize, hnode.perm⟩
  have hcarry : out.workperm[v]! = tv := by
    rw [← hat]
    exact (hmap tc (by have := hc.1; omega)).trans hstore.2.2
  have hkey := h.vertex_key hn0 hlevel hgsz hcheck hstab hc hr hmem hfuel tcLevel
  rw [hcarry] at hkey
  change vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells v =
    vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells tv at hkey
  rw [← hkey]
  exact hv

/-- An actual received short return either covers the entire current child
through its canonical-reference automorphism, or carries the cheap boundary.
Classifier provenance and the scatter survive all intervening sweeps. -/
theorem SweepPre.short_witness {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel runFuel level numcells tc tv1 tv target len : Nat} {first : Bool}
    {cell : VSet n} {base st : Search n} {cs : List Nat} {best : Option (Key n)}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (he : (node false ctx (n + 2) tcLevel runFuel (level + 1) (numcells + 1)
      (Nauty.child first level tc tv st)).1 = .unwind target true)
    (hi : RunInv G ctx (node false ctx (n + 2) tcLevel runFuel (level + 1) (numcells + 1)
      (Nauty.child first level tc tv st)).2)
    (hreceive : level ≤ target)
    (hbase : SearchOk G level numcells base)
    (hframe : SearchOut G level level base st)
    (hc : IsCell base.ptn level tc len) (hlen : 2 ≤ len) (hr : tc + len ≤ n)
    (hfuel : level + 1 + fuel ≤ n + 1)
    (hguide : CanonGuide level tc base
      (fun v => prefixKey cs (vertexKey ctx tcLevel fuel level base.lab base.ptn tc numcells v)) best st) :
    let out := (node false ctx (n + 2) tcLevel runFuel (level + 1) (numcells + 1)
      (Nauty.child first level tc tv st)).2
    Generic.Covers (prefixKey cs (vertexKey ctx tcLevel fuel level st.lab st.ptn tc numcells tv)) best ∨
      target ≤ out.noncheaplevel - 1 := by
  intro out
  have ht := h.child_target hn0 hgsz hsymm he hreceive
  have horigin := node_origin false ctx (n + 2) tcLevel runFuel (level + 1) (numcells + 1)
    (Nauty.child first level tc tv st) he
  rcases horigin.admission hi.workspace.1 with ⟨_, hg, htrace, hmap⟩ | ⟨_, hcheap⟩
  · left
    apply child_canon_cover h.partition hn0 h.positive h.path.fixed h.target (h.cursor_mem tv rfl)
      hgsz (isCell_of_low hframe.low hc) hr hfuel
      (hguide.frame hframe hbase h.partition hn0 h.positive hc hlen hr hfuel)
      (hg.symm.trans ht) hi.canonical.1 (hi.trace _ htrace)
    exact hmap hi.scratch hi.canonical.1 (isPerm_of_cellsReach hi.canonical.1 hn0 hi.canonical.2)
  · exact Or.inr hcheap

end Hex.GraphIso.Nauty
