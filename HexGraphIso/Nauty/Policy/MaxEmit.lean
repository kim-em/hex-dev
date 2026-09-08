/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxCheap
public import HexGraphIso.Nauty.Policy.MaxRules
import all HexGraphIso.Nauty.Policy.MaxCheap
import all HexGraphIso.Nauty.Policy.MaxRules
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Prune
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- A nonlocal emission is the actual node step, with no sweep invoked. -/
theorem Frame.emit_step {ctx : Ctx n} {tcLevel : Nat} {f : Frame n}
    (next : Generic.SweepFn (Search n) n) (h : (f.emit ctx tcLevel).1 ≠ .done) :
    Generic.nodeStep ctx tcLevel next false f.level f.numcells f.entry = f.emit ctx tcLevel := by
  unfold Frame.emit at h ⊢
  dsimp only [prepareOther] at h ⊢
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
    Generic.Policy.compareCodes, Generic.Policy.chooseTarget, Generic.Policy.classify,
    Generic.Policy.leafExit, Generic.Policy.cheapCheck, Generic.Policy.afterSweep]
  generalize hv : visit ctx f.level f.numcells f.entry = v at h ⊢
  obtain ⟨nc, code, st⟩ := v
  simp only [Bool.false_eq_true, ite_false]
  generalize ht : chooseTarget false ctx tcLevel f.level nc (compareCodes f.level code st) = t at h ⊢
  obtain ⟨tc, cell, len, out⟩ := t
  generalize hc : leafExit (classify ctx f.level nc out).1 f.level
    (classify ctx f.level nc out).2 = c at h ⊢
  obtain ⟨exit, result⟩ := c
  cases exit with
  | done => exact (h rfl).elim
  | fuel => rfl
  | unwind target short => rfl

/-- A better classification occurs only at a discrete node. -/
theorem better_discrete {ctx : Ctx n} {level numcells sr : Nat} {st : Search n}
    (h : (classify ctx level numcells st).1 = .better sr) : numcells = n := by
  by_cases hn : numcells = n
  · exact hn
  rw [classify_eq] at h
  split at h
  · cases h
  · simp only [bne_iff_ne.mpr hn, ite_true] at h
    cases h

/-- Installation sets the equal-code level to the leaf level, so every
strict-ancestor return from a better leaf uses the cheap boundary. -/
theorem better_target {level sr target : Nat} {short : Bool} {st : Search n}
    (he : (leafExit (.better sr) level st).1 = .unwind target short)
    (ht : target < level) : target = st.noncheaplevel - 1 := by
  unfold leafExit at he
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at he
  split at he
  all_goals
    obtain ⟨t, s, hx, hbound⟩ := pruneReturn_target level (install level sr _)
    rw [he] at hx
    cases hx
    change level ≤ target ∨ target = st.noncheaplevel - 1 at hbound
    exact hbound.resolve_left (by omega)

/-- The better-leaf rule discharges its complete local maximum obligation,
including every nonlocal cheap return. -/
theorem better_rule (G : Colored n k) (tcLevel sr : Nat) :
    NodeRule G tcLevel false (fun level numcells st => verdict G tcLevel level numcells st = .better sr) := by
  intro fuel _ level numcells st hbetter cs bs fs parents h
  let ctx : Ctx n := { g := rowsOf G }
  let f : Frame n := ⟨level, numcells, cs, st⟩
  let p := prepareOther ctx tcLevel level numcells st
  let c := classify ctx level p.1 p.2.2.2.2.2
  have hclass : c.1 = .better sr := hbetter
  have hd : p.1 = n := better_discrete hclass
  have hdone : (f.emit ctx tcLevel).1 ≠ .done := by
    change (leafExit c.1 level c.2).1 ≠ .done
    intro he
    have hi := (leafExit_done c.1 level c.2).mp he
    rw [hclass] at hi
    cases hi
  have hnf := leafExit_noFuel c.1 level c.2
  obtain ⟨target, short, hexit⟩ : ∃ target short, (f.emit ctx tcLevel).1 = .unwind target short := by
    cases he : (f.emit ctx tcLevel).1 with
    | done => exact (hdone he).elim
    | fuel => exact (hnf he).elim
    | unwind target short => exact ⟨target, short, rfl⟩
  have hin : Engine.NodePre G ctx tcLevel level numcells st := h.entry.1
  have ht := hin.leaf_bound hexit
  have hcheap : target = (f.emit ctx tcLevel).2.noncheaplevel - 1 := by
    change target = (leafExit c.1 level c.2).2.noncheaplevel - 1
    rw [leafExit_noncheap]
    apply better_target (ht := ht)
    change (leafExit c.1 level c.2).1 = .unwind target short at hexit
    rwa [hclass] at hexit
  have hr := h.cheap_leaf hd hexit hcheap
    (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
  rw [f.emit_step _ hdone]
  exact hr

end Hex.GraphIso.Nauty.Engine.Max
