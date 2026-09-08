/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxPrepare
import all HexGraphIso.Nauty.Policy.MaxPosition
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.FirstPath
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.Partition
import all HexGraphIso.Nauty.Policy.Reach
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- The actual first descent moves the first leaf only within its entry
cells, with the same boundary convention as a complete node call. -/
theorem firstPath_frame {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells last : Nat} {st leaf : Search n}
    (path : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hn0 : 0 < n) (hl : 1 ≤ level) (hok : SearchOk G level numcells st.view) :
    SearchOut G (level - 1) level st.view leaf.view := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    let h := reachPolicy G ctx tcLevel hn0
    have hv := h.visit level numcells st hl hok
    have hr := h.record level (visit ctx level numcells st).2.1 _ _ hv.1
    have ht := h.target true level _ _ hl hr.ok
    exact hv.2 _ (hr.effect.trans ht.1.effect)
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    let h := reachPolicy G ctx tcLevel hn0
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    have hv := h.visit level numcells st hl hok
    have hr := h.record level (visit ctx level numcells st).2.1 _ _ hv.1
    have ht := h.target true level _ _ hl hr.ok
    have hc := h.cheap true level r.1 r.2.2.2.2 ht.1.ok
    have hd := h.child true level r.1 r.2.1.toNat tv r.2.2.1
      (cheapCheck true level r.2.2.2.2) hl hc.ok (ht.2.of_out hc.effect) (VSet.nextElem_mem htv)
    have hi := ih (by omega) hd.1
    have ho := hd.2 leaf (by simpa only [Nat.add_sub_cancel, policy, Generic.Policy.cheapCheck] using hi)
    exact hv.2 _ (hr.effect.trans (ht.1.effect.trans (hc.effect.trans ho)))

/-- A received first child introduces its saved reference from its actual
first descent. Later children preserve the already covered reference. -/
theorem SweepInput.first_reference {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let raw := (Engine.node (first && tv == tv1) ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Engine.child first level tc tv st)).2
    let middle := if first && tv == tv1 then afterChildFirst level tv1 raw else raw
    let left := { middle with fixedpts := middle.fixedpts.erase tv }
    let ready := recoverLevels level (recoverPtn (n + 2) level left)
    Generic.Grows (st.key ctx bs) (ready.best ctx) →
    Generic.Covers (l.key ctx tcLevel tv) (ready.best ctx) →
    ready.gcaFirst = level →
      Generic.Covers (l.key ctx tcLevel ready.firstlab[tc]!) (ready.best ctx) ∧
        cellsPerm (l.prepare ctx tcLevel).2.2.2.2.ptn level
          (l.prepare ctx tcLevel).2.2.2.2.lab ready.firstlab := by
  intro raw middle left ready hg hc hlevel
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have href : ready.firstlab = raw.firstlab := by
    have he := congrArg (fun r => r.2.2)
      ((referencePolicy ctx (n + 2) tcLevel).recover level left)
    change ready.firstlab = left.firstlab at he
    rw [he]
    dsimp only [left, middle]
    split <;> rfl
  by_cases hcf : (first && tv == tv1) = true
  · have hi := h.push hgsz hsymm hloop
    rw [hcf] at hi
    have hp := hi.entry.1
    have htrace := hi.entry.2.2.2.2.1
    obtain ⟨last, leaf, path⟩ := firstPath_exists (ctx := ctx) (tcLevel := tcLevel)
      hn0 hi.frame.positive hi.frame.partition (empty_orbits hp.orbits htrace) hi.fuel
    have he := firstPath_frame path hn0 hi.frame.positive hi.frame.partition
    have hr := congrArg (fun r => r.2.2) (firstPath_reference (inf := n + 2) path)
    change (Engine.node true ctx (n + 2) tcLevel fuel _ _ _).2.firstlab = leaf.lab at hr
    dsimp only [Parent.child] at he hr
    rw [← h.first_eq, ← h.level_eq, ← h.tc_eq] at he hr
    rw [← h.numcells_eq] at hr
    have hraw : raw.firstlab = leaf.lab := by
      dsimp only [raw]
      rw [hcf]
      exact hr
    let p : Parent n := ⟨l, st, tv, bs, fs⟩
    have hpick := p.picked h.suspend
    dsimp only [Parent.child] at hpick
    rw [← h.first_eq, ← h.level_eq, ← h.tc_eq] at hpick
    have htv : leaf.lab[tc]! = tv := (he.atSingleton hpick.1).trans hpick.2
    have hd := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
      hl h.partition h.target (h.cursor_mem tv rfl)
    have ho := hd.2 leaf (by simpa only [Nat.add_sub_cancel, policy, Generic.Policy.child] using he)
    rw [href, hraw]
    have hperm := ho.perm
    change cellsPerm st.ptn level st.lab leaf.lab at hperm
    have hptn := h.effect.ptn_eq h.base h.partition
    change st.ptn = (l.prepare ctx tcLevel).2.2.2.2.ptn at hptn
    rw [hptn] at hperm
    exact ⟨htv ▸ hc, cellsPerm_trans h.effect.perm hperm⟩
  · have hfalse : (first && tv == tv1) = false := Bool.eq_false_iff.mpr hcf
    have hr : raw.firstlab = st.firstlab := by
      dsimp only [raw]
      rw [hfalse]
      have hh := congrArg (fun r => r.2.2)
        (node_reference ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
          (Engine.child first level tc tv st))
      cases first <;> exact hh
    have hgc : ready.gcaFirst = st.gcaFirst := by
      have hh := (gcaPolicy ctx (n + 2) tcLevel).recover level left
      change ready.gcaFirst = left.gcaFirst at hh
      rw [hh]
      dsimp only [left, middle, raw]
      rw [ite_eq_right hcf, hfalse, node_gca]
      cases first <;> rfl
    have hp := h.first_ref (hgc ▸ hlevel)
    rw [href, hr]
    exact ⟨hp.1.grow hg, hp.2⟩

end Hex.GraphIso.Nauty.Engine.Max
