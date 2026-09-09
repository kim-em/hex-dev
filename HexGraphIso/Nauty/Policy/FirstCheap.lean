/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstBounded
public import HexGraphIso.Nauty.Policy.Safety
import all HexGraphIso.Nauty.Policy.FirstBounded
import all HexGraphIso.Nauty.Policy.Leftmost
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Preparing the first path does not move the cheap boundary. -/
theorem prepareFirst_noncheap (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.noncheaplevel = st.noncheaplevel := by
  unfold Generic.prepareFirst
  change (chooseTarget true ctx tcLevel level _ _).2.2.2.noncheaplevel = _
  rw [chooseFirst_fields]
  rfl

/-- The initial descent keeps every earlier failed guard below its frozen ancestor. -/
theorem firstLeaf_noncheap {ctx : Ctx n} {tcLevel fuel level numcells last bound : Nat}
    {st leaf : Search n} (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hlevel : bound < level) (hin : bound < st.noncheaplevel) : bound < leaf.noncheaplevel := by
  induction hpath with
  | leaf fuel level numcells st hdisc =>
    rw [prepareFirst_noncheap]
    exact hin
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    apply ih (by omega)
    change bound < (cheapCheck true level
      (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2).noncheaplevel
    unfold cheapCheck
    split
    · change bound < level + 1
      omega
    · rw [prepareFirst_noncheap]
      exact hin

/-- A full first-path call also preserves failed guards at its ancestors. -/
theorem firstPath_noncheap {ctx : Ctx n} {inf tcLevel fuel level numcells last bound : Nat}
    {st leaf : Search n} (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hlevel : bound < level) (hin : bound < st.noncheaplevel) :
    bound < (node true ctx inf tcLevel fuel level numcells st).2.noncheaplevel := by
  rw [node_eq_generic]
  apply hpath.bounded (noncheapPolicy ctx inf tcLevel bound) (fun _ _ _ h => h) (Nat.le_of_lt hlevel)
  change bound < leaf.noncheaplevel
  exact firstLeaf_noncheap hpath hlevel hin

/-- A first-path node that is cheap after the guard supplies the small-cell ancestor invariant. -/
theorem firstCheap_small {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : Search n} (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st)
    (heq : Equitable ctx level (st.refined ctx level numcells).lab (st.refined ctx level numcells).ptn)
    (hsmall : st.noncheaplevel < level → SubtreeOk ctx level (st.refined ctx level numcells))
    (hcheap : (cheapCheck true level
      (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2).noncheaplevel ≤ level) :
    SubtreeOk ctx level (st.refined ctx level numcells) := by
  by_cases hbefore : st.noncheaplevel < level
  · exact hsmall hbefore
  have hp := (prepareFirst_fields ctx tcLevel level numcells st).2.1
  have hc : cheapautom (st.refined ctx level numcells).ptn level n = true := by
    unfold cheapCheck at hcheap
    rw [prepareFirst_noncheap, hp] at hcheap
    have hb : st.noncheaplevel ≥ level := by omega
    cases hguard : cheapautom (st.refined ctx level numcells).ptn level n with
    | true => rfl
    | false => simp only [Bool.not_true, hb, decide_true, Bool.or_true, hguard, Bool.not_false,
        Bool.and_self, ite_true] at hcheap
               omega
  have hr := (prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 hlevel hok).1
  have hacc := hr.count
  change (st.refined ctx level numcells).numcells =
    bcount (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.ptn level n at hacc
  rw [hp] at hacc
  exact subtreeOk_of_cheapautom (refined_iter hn0 hlevel hok) heq hacc.symm hc

end Hex.GraphIso.Nauty
