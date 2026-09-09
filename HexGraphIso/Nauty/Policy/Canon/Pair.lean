/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Canon.Ref
public import HexGraphIso.Nauty.Policy.ChildFrame
public import HexGraphIso.Nauty.Invariant.Autos
import all HexGraphIso.Nauty.Policy.Canon.Ref
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The canonical scatter of an actual child returning to this loop
stabilizes the frozen parent cells. Its workspace pair is therefore valid
at that parent, independently of the current ordering of labels. -/
theorem child_pair {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv : Nat} {first : Bool}
    {cell : VSet n} {base st : Search n} {key : Nat → Key n} {best : Option (Key n)}
    (h : SearchOk G level numcells st)
    (hn0 : 0 < n) (hlevel : 1 ≤ level) (hpath : FixedCells level st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (ht : cell.mem tv = true)
    (childFirst : Bool)
    (hbase : SearchOk G level numcells base)
    (hframe : SearchOut G level level base st)
    (hguide : CanonGuide level tc base key best st) :
    let out := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    out.gcaCanon = level → out.canonlab.size = n → checkAutom ctx.g out.workperm = true →
      (∀ i, i < n → out.workperm[out.canonlab[i]!]! = out.lab[i]!) →
      PairOk ctx.g base.ptn base.lab level (fmperm out.workperm n).1 (fmperm out.workperm n).2 := by
  intro out he hs hcheck hmap
  have hold := child_canon_old (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel)
    (first := first) h hn0 hlevel htarget ht childFirst (Nat.le_of_eq he)
  obtain ⟨_, _, _, href⟩ := hguide (hold.1.symm.trans he)
  rw [← hold.2] at href
  have hc := child_frame (ctx := ctx) (tcLevel := tcLevel) (fuel := fuel) (first := first)
    h hn0 hlevel hpath htarget ht childFirst
  have hp : SearchOut G level level base out :=
    hframe.trans (hc.1.congr rfl rfl rfl rfl)
  have hend := searchOk_end hn0 hbase hlevel
  apply pairOk_fmperm (labOk_of_reach hbase.labSize hbase.reach)
    hbase.labSize hbase.ptnSize hend hcheck
  exact cellStab_of_scatter hbase.ptnSize hbase.labSize hs hend href hp.perm hmap

/-- A later sibling's canonical scatter yields a valid pair at its frozen parent. -/
theorem SweepPre.canon_pair {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells tc tv1 tv : Nat} {first : Bool}
    {cell : VSet n} {base st : Search n} {key : Nat → Key n} {best : Option (Key n)}
    (h : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hn0 : 0 < n) (childFirst : Bool)
    (hbase : SearchOk G level numcells base)
    (hframe : SearchOut G level level base st)
    (hguide : CanonGuide level tc base key best st) :
    let out := (node childFirst ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st)).2
    out.gcaCanon = level → out.canonlab.size = n → checkAutom ctx.g out.workperm = true →
      (∀ i, i < n → out.workperm[out.canonlab[i]!]! = out.lab[i]!) →
      PairOk ctx.g base.ptn base.lab level (fmperm out.workperm n).1 (fmperm out.workperm n).2 :=
  child_pair h.partition hn0 h.positive h.path.fixed h.target (h.cursor_mem tv rfl)
    childFirst hbase hframe hguide

end Hex.GraphIso.Nauty
