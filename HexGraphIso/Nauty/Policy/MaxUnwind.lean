/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxFrame
import all HexGraphIso.Nauty.Policy.MaxSuspend
import all HexGraphIso.Nauty.Policy.Maximum
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- An actual sweep propagates a child's nonlocal witness through first-child
cleanup, with the same incumbent and the full chosen-cell upper bound. -/
theorem SweepInput.unwind {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel inf : Nat}
    {first short : Bool} {level numcells tc tv1 tv index target : Nat} {cell : VSet n}
    {st out : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    {descend : Generic.NodeFn (Search n)} {next : Generic.SweepFn (Search n) n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents)
    (hvisit : (!first || st.orbits[tv]! == tv) = true)
    (hcall : descend (first && tv == tv1) (level + 1) (numcells + 1)
      (Nauty.child first level tc tv st) = (.unwind target short, out))
    (ht : target < level)
    (hr : let p : Parent n := ⟨l, st, tv, bs, fs⟩
      Generic.Result ((p.child ctx tcLevel).key ctx tcLevel)
        ((p.child ctx tcLevel).entry.key ctx bs) (out.best ctx) level
        (Witness ctx tcLevel ((parents.push p).frames ctx tcLevel)) (.unwind target short)) :
    let result := Generic.sweepStep inf descend next first level numcells tc tv1 tv cell index st
    Generic.Result (l.bound ctx tcLevel) (st.key ctx bs) (result.2.2.best ctx) level
      (Witness ctx tcLevel ((parents.frames ctx tcLevel).insert l.node)) result.1 := by
  let p : Parent n := ⟨l, st, tv, bs, fs⟩
  let middle := if first && tv == tv1 then afterChildFirst level tv1 out else out
  let cleaned := { middle with fixedpts := middle.fixedpts.erase tv }
  have hstep : Generic.sweepStep inf descend next first level numcells tc tv1 tv cell index st =
      (.unwind target short, index, cleaned) := by
    unfold Generic.sweepStep
    dsimp only [policy, Generic.Policy.orbit, Generic.Policy.child,
      Generic.Policy.afterChildFirst, Generic.Policy.leaveChild]
    simp only [hvisit, ↓reduceIte, hcall, Generic.advance, ht, Id.run_pure,
      apply_ite Id.run]
    dsimp only [cleaned, middle]
    split <;> rfl
  have hkey : cleaned.best ctx = out.best ctx := by
    dsimp only [cleaned, middle]
    split <;> rfl
  have hbefore : (p.child ctx tcLevel).entry.key ctx bs = st.key ctx bs := by
    dsimp only [p, Parent.child]
    cases hf : l.first <;> rfl
  have hbound := hr.bounded.mono (p.key_le h.suspend)
  rw [hbefore] at hbound
  have hw : Witness ctx tcLevel ((parents.push p).frames ctx tcLevel) target (out.best ctx) := by
    simpa only [Generic.ExitCover, ite_eq_right (by omega : target ≠ level)] using hr.coverage.2
  have hframes := Parents.push_frames (p := p) (parents := parents) (target := target)
    (ctx := ctx) (tcLevel := tcLevel) h.node.positive
    (by change target < l.node.level; have := h.level_eq; omega)
    (by simpa only [p, h.level_eq] using h.parent)
  obtain ⟨f, hf, hd, hw⟩ := hw
  rw [hstep]
  change Generic.Result _ _ (cleaned.best ctx) level _ (.unwind target short)
  rw [hkey]
  refine ⟨hbound, by omega, ?_⟩
  simp only [ite_eq_right (by omega : target ≠ level)]
  exact ⟨f, hframes ▸ hf, hd, hw⟩

/-- At the cheap boundary's node, the returning sweep's witness becomes
coverage of the node's full specification, independent of target hints. -/
theorem Loop.receive {ctx : Ctx n} {tcLevel : Nat} {l : Loop n} {parents : Parents n}
    {before after : Option (Key n)} {short : Bool}
    (hl : 1 ≤ l.node.level)
    (h : Generic.Result (l.bound ctx tcLevel) before after l.node.level
      (Witness ctx tcLevel ((parents.frames ctx tcLevel).insert l.node))
      (.unwind (l.node.level - 1) short)) :
    Generic.Covers (l.node.key ctx tcLevel) after := by
  apply Witness.resolve
  simpa only [Generic.ExitCover,
      ite_eq_right (by omega : l.node.level - 1 ≠ l.node.level)] using h.coverage.2

/-- Constructing the complete child input specializes the smaller-call
contract to this sweep's actual descent and frozen ancestor table. -/
theorem SweepInput.child_result {G : Colored n k} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G { g := rowsOf G } tcLevel fuel cfuel first level numcells tc tv1 (some tv)
      cell index st l bs fs parents)
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel)) :
    let ctx : Ctx n := { g := rowsOf G }
    let p : Parent n := ⟨l, st, tv, bs, fs⟩
    let result := Nauty.node (first && tv == tv1) ctx (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st)
    Generic.Result ((p.child ctx tcLevel).key ctx tcLevel)
      ((p.child ctx tcLevel).entry.key ctx bs) (result.2.best ctx) level
      (Witness ctx tcLevel ((parents.push p).frames ctx tcLevel)) result.1 := by
  intro ctx p result
  have hp := h.push (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
  change NodeInput G ctx tcLevel fuel (first && tv == tv1)
    (p.child ctx tcLevel) bs fs (parents.push p) at hp
  have he : p.child ctx tcLevel =
      ⟨level + 1, numcells + 1, l.codes ctx, Nauty.child first level tc tv st⟩ := by
    simp only [p, ctx, Parent.child, h.first_eq, h.level_eq, h.numcells_eq, h.tc_eq]
  rw [he] at hp ⊢
  have hr := (hn (first && tv == tv1) (level + 1) (numcells + 1)
    (Nauty.child first level tc tv st) trivial).1 (l.codes ctx) bs fs (parents.push p) hp
  simpa only [result, Generic.nodeCall, ← node_eq_generic, Nat.add_sub_cancel] using hr

/-- An actual visited child returning past this sweep supplies the
maximum contract directly from its smaller-call induction hypothesis. -/
theorem visit_unwind (G : Colored n k) (tcLevel fuel cfuel : Nat)
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel))
    (first short : Bool) (level numcells tc tv1 tv index target : Nat)
    (cell : VSet n) (st out : Search n)
    (hvisit : (!first || st.orbits[tv]! == tv) = true)
    (hcall : node (first && tv == tv1) { g := rowsOf G } (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st) = (.unwind target short, out))
    (ht : target < level) :
    (keyContract G tcLevel).sweepPost fuel (cfuel + 1) first level numcells tc tv1 (some tv) cell index st
      (Generic.sweepStep (n + 2)
        (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel)
        (Generic.sweepCall { g := rowsOf G } (n + 2) tcLevel fuel cfuel)
        first level numcells tc tv1 tv cell index st) := by
  intro l bs fs parents h
  let ctx : Ctx n := { g := rowsOf G }
  let p : Parent n := ⟨l, st, tv, bs, fs⟩
  have hc : Generic.nodeCall ctx (n + 2) tcLevel fuel (first && tv == tv1)
      (level + 1) (numcells + 1) (Nauty.child first level tc tv st) =
        (.unwind target short, out) := by
    simpa only [Generic.nodeCall, ← node_eq_generic] using hcall
  have hr := h.child_result hn
  dsimp only at hr
  rw [hcall] at hr
  exact h.unwind hvisit hc ht hr

end Hex.GraphIso.Nauty.Max
