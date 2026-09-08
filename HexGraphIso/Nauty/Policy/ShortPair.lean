/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.ReturnOrigin
public import HexGraphIso.Nauty.Policy.FilterPair
public import HexGraphIso.Nauty.Policy.CanonPair
import all HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- A short return received from a child targets exactly this sweep.
The node bound rules out a target strictly between adjacent levels. -/
theorem SweepPre.child_target {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv target : Nat} {first : Bool}
    {cell : VSet n} {st : Search n}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (he : (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).1 = .unwind target true)
    (hreceive : level ≤ target) : target = level := by
  have hb := (h.child hn0 hgsz hsymm).node_bound (n + 2) target true he
  omega

/-- The actual short-return pair is valid at its receiving parent.
Canonical scatters use the parent's covered reference; implicit pairs
fix the parent path and use its root-stabilization invariant. -/
theorem return_pair {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv target : Nat} {first childFirst : Bool}
    {cell : VSet n} {st : Search n} {key : Nat → Key n} {best : Option (Key n)}
    (h : SearchOk G level numcells st.view)
    (hn0 : 0 < n) (hlevel : 1 ≤ level) (hpath : PathInv G ctx level st)
    (htarget : Generic.Target Search.view level tc cell st) (htv : cell.mem tv = true)
    (hbound : target < level + 1)
    (he : (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).1 = .unwind target true)
    (hi : RunInv G ctx (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).2)
    (hreceive : level ≤ target) (hguide : CanonGuide level tc st key best st) :
    let raw := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).2
    let out := { raw with fixedpts := raw.fixedpts.erase tv }
    ∀ pair, out.autos.back? = some pair → PairOk ctx.g st.ptn st.lab level pair.1 pair.2 := by
  intro raw out pair hpair
  have ht : target = level := by omega
  have horigin : LeafReturn target out := shortPolicy.leave tv target raw
    (node_origin childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st) he)
  rcases horigin.admission hi.workspace.1 with ⟨hb, hg, htrace, hmap⟩ | ⟨hb, hcheap⟩
  · have hp : pair = fmperm out.workperm n := Option.some.inj (hpair.symm.trans hb)
    subst pair
    apply child_pair h hn0 hlevel hpath.fixed htarget htv childFirst h
      (SearchOut.refl G level level h.reach)
      hguide (hg.symm.trans ht) hi.canonical.1 (hi.trace _ htrace)
    exact hmap hi.scratch hi.canonical.1 (isPerm_of_cellsReach hi.canonical.1 hn0 hi.canonical.2)
  · have hp : pair = fmptn out.lab out.ptn out.noncheaplevel n :=
      Option.some.inj (hpair.symm.trans hb)
    have hf := child_frame (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) (first := first)
      h hn0 hlevel hpath.fixed htarget htv childFirst
    have hfix := short_implicit_fix (out := out) hn0 hlevel h hpath.fixed hf.1 hf.2 (by omega)
    have hm : pair ∈ raw.autos := by simpa using Array.mem_of_back? hpair
    intro v hv hmcr
    obtain ⟨γ, hc, hfixed, hroot, hlt⟩ := hi.pairs pair (by simpa only [Array.mem_toList_iff] using hm) v hv hmcr
    refine ⟨γ, hc, hfixed, ?_, hlt⟩
    apply hpath.stab γ hc hroot
    intro u hu hmem
    apply hfixed u hu
    rw [hp]
    apply VSet.subset_iff.mp hfix
    change out.fixedpts.mem u = true
    rw [hf.2]
    exact hmem

/-- Later siblings obtain the target bound from their actual node precondition. -/
theorem SweepPre.return_pair {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv target : Nat} {first : Bool}
    {cell : VSet n} {st : Search n} {key : Nat → Key n} {best : Option (Key n)}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (he : (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).1 = .unwind target true)
    (hi : RunInv G ctx (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).2)
    (hreceive : level ≤ target) (hguide : CanonGuide level tc st key best st) :
    let raw := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).2
    let out := { raw with fixedpts := raw.fixedpts.erase tv }
    ∀ pair, out.autos.back? = some pair → PairOk ctx.g st.ptn st.lab level pair.1 pair.2 :=
  Engine.return_pair h.partition hn0 h.positive h.path h.target (h.cursor_mem tv rfl)
    ((h.child hn0 hgsz hsymm).node_bound (n + 2) target true he) he hi hreceive hguide

/-- The leftmost first-path child has the same local pair guarantee after
its first-path controls and fixed points are cleaned up. No later-sibling
precondition is needed at this first entry. -/
theorem first_return_pair {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv target : Nat}
    {cell : VSet n} {st : Search n} {key : Nat → Key n} {best : Option (Key n)}
    (h : SearchOk G level numcells st.view)
    (hn0 : 0 < n) (hlevel : 1 ≤ level) (hpath : PathInv G ctx level st)
    (htarget : Generic.Target Search.view level tc cell st) (htv : cell.mem tv = true)
    (he : (node true ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child true level tc tv st)).1 = .unwind target true)
    (hi : RunInv G ctx (node true ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child true level tc tv st)).2)
    (hreceive : level ≤ target) (hguide : CanonGuide level tc st key best st) :
    let raw := (node true ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child true level tc tv st)).2
    let out := { afterChildFirst level tv raw with fixedpts := raw.fixedpts.erase tv }
    ∀ pair, out.autos.back? = some pair → PairOk ctx.g st.ptn st.lab level pair.1 pair.2 :=
  return_pair h hn0 hlevel hpath htarget htv
    (first_node_bound ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child true level tc tv st) (by omega) target true he) he hi hreceive hguide

/-- Applying a received short return preserves coverage of the parent's
original target cell, using the pair justified by that actual child call. -/
theorem SweepPre.return_cover {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel specFuel level numcells tc tv1 tv target len : Nat} {first : Bool}
    {cell : VSet n} {st : Search n} {key : Nat → Key n} {best : Option (Key n)}
    {cs : List Nat} {live : Nat → Prop}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (he : (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).1 = .unwind target true)
    (hi : RunInv G ctx (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).2)
    (hreceive : level ≤ target) (hguide : CanonGuide level tc st key best st)
    (hc : IsCell st.ptn level tc len) (hr : tc + len ≤ n)
    (hfuel : level + 1 + specFuel ≤ n + 1)
    (hcover : CellCover ctx tcLevel specFuel level numcells tc len cs st live best)
    (hsub : ∀ v, live v → (windowSet n st.lab tc len).mem v = true)
    (hmem : ∀ v, live v → cell.mem v = true) :
    let raw := (node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (Engine.child first level tc tv st)).2
    let out := { raw with fixedpts := raw.fixedpts.erase tv }
    CellCover ctx tcLevel specFuel level numcells tc len cs st
      (fun v => live v ∧ (shortprune cell out).mem v = true) best := by
  intro raw out
  apply filter_pair h.partition hn0 h.positive hgsz hc hr hfuel hcover hsub hmem
  intro fix mcr hp
  exact h.return_pair hn0 hgsz hsymm he hi hreceive hguide (fix, mcr) hp

end Hex.GraphIso.Nauty.Engine
